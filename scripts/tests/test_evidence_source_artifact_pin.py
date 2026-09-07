#!/usr/bin/env python3
"""Regression tests for byte-verified source-artifact pins."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.source_record_integrity import (  # noqa: E402
    stamp_source_record_audit_integrity,
    stamp_source_record_audit_receipts,
)
from scripts import audit_evidence_integrity as GATE  # noqa: E402
from scripts import source_manifest_validation as source_manifest  # noqa: E402
from scripts import source_named_result_index  # noqa: E402


def complete_v10_source_record_scan_fixture(
    payload: dict[str, object], *, paper: str = "FixturePaper"
) -> None:
    """Add the generator-owned full-scan fields to synthetic v10 records.

    Tests that exercise a later gate should not accidentally pass because the
    raw record omitted the mandatory no-Lean/Lean/recursion scan contract.
    Individual tests can still override any field after this helper to model a
    failing generated scan.
    """

    sections = (
        "boundary_input_items",
        "conclusion_dependency_items",
        "type_valued_certificate_result_items",
        "recursive_field_items",
        "semantic_model_items",
        "source_premise_consistency_items",
    )
    expected_lists = (
        "expected_input_judgment_keys",
        "expected_field_judgment_keys",
        "expected_semantic_model_judgment_keys",
    )
    has_surface = any(bool(payload.get(key)) for key in (*sections, *expected_lists))
    source_path = f"papers/{paper}/PaperInterface.lean"
    source_sha256 = hashlib.sha256(
        f"fixture-v10-source:{paper}".encode("utf-8")
    ).hexdigest()
    payload.setdefault(
        "source_record_input_fingerprint", {"max_depth": 4, "no_lean": False}
    )
    payload.setdefault("missing_configured_review_rows", [])
    payload.setdefault("recursion_failures", [])
    payload.setdefault("recursion_failure_count", 0)
    payload.setdefault("constructor_result_type_check_error", "")
    payload.setdefault("source_premise_consistency_schema", 1)
    payload.setdefault("source_premise_consistency_error", "")
    payload.setdefault("source_premise_consistency_items", [])
    payload.setdefault("source_premise_consistency_item_count", 0)
    payload.setdefault("review_row_count", 1 if has_surface else 0)
    payload.setdefault("recursive_field_count", 0)
    payload.setdefault("configured_review_rows", [{}] if has_surface else [])
    payload.setdefault("configured_review_rows_count", 1 if has_surface else 0)
    payload.setdefault("configured_review_row_count", 1 if has_surface else 0)
    payload.setdefault(
        "review_interface_source", {"path": source_path, "sha256": source_sha256}
    )
    if has_surface:
        fresh = {
            "mode": "isolated_temp_overlay",
            "returncode": 0,
            "source_file": source_path,
            "source_sha256": source_sha256,
        }
        payload.setdefault(
            "lean_check",
            {
                "returncode": 0,
                "requested_checked_rows": [
                    {
                        "row": "fixture_selected_review_row",
                        "qualified_declaration": f"{paper}.PaperInterface.fixture_selected_review_row",
                    }
                ],
                "checked_rows": [
                    {
                        "row": "fixture_selected_review_row",
                        "qualified_declaration": f"{paper}.PaperInterface.fixture_selected_review_row",
                    }
                ],
                "fresh_source_elaboration": dict(fresh),
            },
        )
        payload.setdefault("fresh_source_elaboration", dict(fresh))
    else:
        payload.setdefault(
            "lean_check",
            {
                "command": "skipped Lean check: no source-record rows or fields",
                "returncode": 0,
                "requested_checked_rows": [],
                "checked_rows": [],
            },
        )
        payload.setdefault(
            "fresh_source_elaboration",
            {
                "mode": "not_run_without_lean",
                "source_file": source_path,
                "source_sha256": source_sha256,
            },
        )


class SourceArtifactPinTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.paper.mkdir(parents=True)
        self.manifest = self.paper / "audit" / "paper_statement_map.json"
        self.artifact = self.paper / "source.txt"
        self.artifact.write_bytes(b"source theorem bytes\n")
        self.digest = hashlib.sha256(self.artifact.read_bytes()).hexdigest()

    def findings(self, payload: dict[str, object]) -> list[object]:
        return source_manifest.source_artifact_pin_findings(
            self.paper, "formalized", self.manifest, payload
        )

    def test_matching_paper_local_artifact_bytes_pass(self) -> None:
        self.assertEqual(
            self.findings(
                {
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": self.digest,
                }
            ),
            [],
        )

    def test_current_v11_lane_ignores_superseded_legacy_name_reason(self) -> None:
        self.manifest.parent.mkdir(parents=True, exist_ok=True)
        (self.manifest.parent / "paper_coverage_llm.json").write_text(
            json.dumps({"items": {"old": {"reason": "matched by name"}}}),
            encoding="utf-8",
        )

        legacy_findings = GATE.check_placeholder_evidence(
            self.paper, "formalized"
        )
        selected_context = SimpleNamespace(v11_lean_claim_graph_selected=True)
        with patch.object(
            GATE, "AUDIT_SIDECARS", ("paper_coverage_llm.json",)
        ):
            current_findings = GATE.check_placeholder_evidence(
                self.paper,
                "formalized",
                context=selected_context,
            )

        self.assertTrue(
            any("name matching as semantic evidence" in f.message for f in legacy_findings)
        )
        self.assertEqual(current_findings, [])

    def test_matching_repository_relative_artifact_path_passes(self) -> None:
        self.assertEqual(
            self.findings(
                {
                    "source_artifact_path": "papers/FixturePaper/source.txt",
                    "source_artifact_sha256": self.digest,
                }
            ),
            [],
        )

    def test_digest_mismatch_reports_expected_and_actual_hashes(self) -> None:
        findings = self.findings(
            {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": "0" * 64,
            }
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("SHA-256 mismatch", findings[0].message)
        self.assertIn(self.digest, findings[0].message)

    def test_missing_path_does_not_accept_canonical_digest_alone(self) -> None:
        findings = self.findings({"source_artifact_sha256": self.digest})
        self.assertEqual(len(findings), 1)
        self.assertIn("missing source_artifact_path", findings[0].message)

    def test_legacy_digest_is_explicitly_unverifiable(self) -> None:
        findings = self.findings({"source_pdf_sha256": self.digest})
        self.assertEqual(len(findings), 1)
        self.assertIn("legacy/unscoped digest", findings[0].message)
        self.assertIn("source_pdf_sha256", findings[0].message)

    def test_path_escape_is_rejected_even_when_target_exists(self) -> None:
        outside = self.root / "outside.txt"
        outside.write_bytes(self.artifact.read_bytes())
        findings = self.findings(
            {
                "source_artifact_path": "../outside.txt",
                "source_artifact_sha256": self.digest,
            }
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("escapes the paper folder", findings[0].message)

    def test_missing_and_non_regular_artifacts_are_rejected(self) -> None:
        missing = self.findings(
            {
                "source_artifact_path": "missing.pdf",
                "source_artifact_sha256": self.digest,
            }
        )
        self.assertIn("does not exist", missing[0].message)

        directory = self.paper / "source-directory"
        directory.mkdir()
        non_regular = self.findings(
            {
                "source_artifact_path": "source-directory",
                "source_artifact_sha256": self.digest,
            }
        )
        self.assertIn("not a regular file", non_regular[0].message)

    def test_structural_public_mode_warns_when_pinned_bytes_are_not_provisioned(self) -> None:
        findings = source_manifest.source_artifact_pin_findings(
            self.paper,
            "formalized",
            self.manifest,
            {
                "source_artifact_path": "licensed-source.pdf",
                "source_artifact_sha256": self.digest,
            },
            require_source_bytes=False,
        )
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "WARN")
        self.assertIn("not release certification", findings[0].message)

    def test_malformed_digest_is_rejected_before_hashing(self) -> None:
        findings = self.findings(
            {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": "not-a-sha256",
            }
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("64 hexadecimal characters", findings[0].message)

    def test_missing_statement_map_does_not_pass_source_manifest_check(self) -> None:
        findings = source_manifest.check_source_manifest(self.paper, "formalized")
        self.assertEqual(len(findings), 1)
        self.assertIn("source statement inventory is missing", findings[0].message)


class SourceAnchorEvidenceTests(unittest.TestCase):
    """Regression tests for content-verified source statement-map anchors."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.manifest = self.audit / "paper_statement_map.json"
        self.artifact = self.paper / "source.txt"
        self.artifact.write_bytes(b"alpha theorem\nbeta assumption\ngamma conclusion\n")

    def quote(self, line_start: int, line_end: int | None = None) -> dict[str, object]:
        line_end = line_start if line_end is None else line_end
        lines = source_manifest.normalized_source_lines(
            source_manifest.normalized_source_text(self.artifact.read_bytes())
        )
        excerpt = source_manifest.normalized_source_line_excerpt(lines, line_start, line_end)
        assert excerpt is not None
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": excerpt,
            "quoted_text_sha256": hashlib.sha256(excerpt.encode("utf-8")).hexdigest(),
        }

    def payload(
        self,
        location: str = "source.txt:1-2",
        evidence: object | None = None,
        *,
        required: object = True,
    ) -> dict[str, object]:
        digest = hashlib.sha256(self.artifact.read_bytes()).hexdigest()
        row: dict[str, object] = {
            "source_kind": "theorem",
            "source_location": location,
        }
        if evidence is not None:
            row["source_anchor_evidence"] = evidence
        return {
            "source_coverage_mode": "named_theoretical_statements",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": digest,
            "source_anchor_evidence_required": required,
            "items": {"source_row": row},
        }

    def findings(self, payload: dict[str, object]) -> list[object]:
        return source_manifest.source_anchor_evidence_findings(
            self.paper, "formalized", self.manifest, payload
        )

    def named_result_inventory_review(
        self, payload: dict[str, object]
    ) -> dict[str, object]:
        source_digest = payload["source_artifact_sha256"]
        assert isinstance(source_digest, str)
        source_text = source_manifest.normalized_source_text(self.artifact.read_bytes())
        presentations = source_named_result_index.extract_named_result_presentations(
            source_text, source_format="text"
        )
        return {
            "schema": 1,
            "complete": True,
            "validator": "fixture-reviewer",
            "validated_at": "2026-07-26",
            "method": "fixture named-result source scan",
            "source_artifact_sha256": source_digest,
            "discovered_named_result_sha256": (
                source_named_result_index.named_result_presentations_sha256(
                    presentations
                )
            ),
            "prose_definition_presentations": [],
            "discovered_prose_definition_sha256": hashlib.sha256(
                b"[]"
            ).hexdigest(),
        }

    def test_exact_quote_from_pinned_source_passes(self) -> None:
        payload = self.payload(evidence=[self.quote(1, 2)])
        self.assertEqual(self.findings(payload), [])

    def test_raw_inventory_and_visual_semantic_anchor_have_distinct_pins(self) -> None:
        visual = self.paper / "visual-review.md"
        visual_scan = self.paper / "visual-source.pdf"
        ocr_input = self.paper / "ocr-input.pdf"
        visual_text = "Alpha theorem in visually checked mathematical notation.\n"
        visual.write_text(visual_text, encoding="utf-8")
        visual_scan.write_bytes(b"%PDF-fixture-visual\n")
        ocr_input.write_bytes(b"%PDF-fixture-ocr\n")
        quote = visual_text.rstrip("\n")
        payload = self.payload(
            "source.txt:1-2",
            [
                {
                    "path": "visual-review.md",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
                }
            ],
        )
        payload["source_text_companion"] = {
            "schema": 1,
            "canonical_text": {
                "path": "source.txt",
                "sha256": hashlib.sha256(self.artifact.read_bytes()).hexdigest(),
            },
            "visual_primary_scan": {
                "path": "visual-source.pdf",
                "sha256": hashlib.sha256(visual_scan.read_bytes()).hexdigest(),
            },
            "transcript_input_scan": {
                "path": "ocr-input.pdf",
                "sha256": hashlib.sha256(ocr_input.read_bytes()).hexdigest(),
            },
            "extraction": {"tool": "pdftotext", "options": ["-layout"]},
            "page_map": [
                {"line_start": 1, "line_end": 3, "pdf_page": 1, "printed_page": 1}
            ],
            "visual_comparison_attestation": {
                "complete": True,
                "method": "Checked the visual source against the canonical transcript.",
            },
            "semantic_review_transcription": {
                "schema": 1,
                "path": "visual-review.md",
                "sha256": hashlib.sha256(visual.read_bytes()).hexdigest(),
                "controlling_visual_source": {
                    "path": "visual-source.pdf",
                    "sha256": hashlib.sha256(visual_scan.read_bytes()).hexdigest(),
                },
                "complete_for_selected_semantic_surface": True,
                "method": "Visually transcribed the selected theorem passage.",
            },
        }
        self.assertEqual(self.findings(payload), [])

    def test_multiple_declared_anchors_each_need_matching_quote(self) -> None:
        payload = self.payload(
            "source.txt:1; source.txt:3",
            [self.quote(1), self.quote(3)],
        )
        self.assertEqual(self.findings(payload), [])

    def test_missing_quote_is_blocking_for_an_opted_in_paper(self) -> None:
        findings = self.findings(self.payload())
        self.assertEqual(len(findings), 1)
        self.assertIn("source_anchor_evidence must be a nonempty list", findings[0].message)

    def test_in_range_but_wrong_quote_is_rejected(self) -> None:
        bad_quote = "beta assumption"
        evidence = {
            "path": "source.txt",
            "line_start": 1,
            "line_end": 1,
            "quoted_text": bad_quote,
            "quoted_text_sha256": hashlib.sha256(bad_quote.encode("utf-8")).hexdigest(),
        }
        findings = self.findings(self.payload("source.txt:1", [evidence]))
        self.assertTrue(
            any("does not equal the exact normalized source line slice" in finding.message for finding in findings)
        )

    def test_out_of_range_declared_anchor_is_rejected(self) -> None:
        evidence = {
            "path": "source.txt",
            "line_start": 4,
            "line_end": 4,
            "quoted_text": "not a source line",
            "quoted_text_sha256": hashlib.sha256(b"not a source line").hexdigest(),
        }
        findings = self.findings(self.payload("source.txt:4", [evidence]))
        self.assertTrue(any("outside the 3-line canonical source artifact" in finding.message for finding in findings))

    def test_changed_source_bytes_invalidate_anchor_evidence_through_the_pin(self) -> None:
        payload = self.payload(evidence=[self.quote(1)])
        self.artifact.write_bytes(b"different source bytes\n")
        findings = self.findings(payload)
        self.assertEqual(len(findings), 1)
        self.assertIn("source artifact SHA-256 mismatch", findings[0].message)

    def test_evidence_cannot_point_at_a_same_content_unpinned_file(self) -> None:
        alternate = self.paper / "alternate.txt"
        alternate.write_bytes(self.artifact.read_bytes())
        evidence = self.quote(1)
        evidence["path"] = "alternate.txt"
        findings = self.findings(self.payload("source.txt:1", [evidence]))
        self.assertTrue(
            any("must identify the canonical pinned source artifact" in finding.message for finding in findings)
        )

    def test_line_endings_are_normalized_after_the_raw_artifact_is_pinned(self) -> None:
        self.artifact.write_bytes(b"alpha theorem\r\nbeta assumption\r\n")
        payload = self.payload("source.txt:1-2", [self.quote(1, 2)])
        self.assertEqual(self.findings(payload), [])

    def test_quote_digest_must_match_the_normalized_quote_bytes(self) -> None:
        evidence = self.quote(1)
        evidence["quoted_text_sha256"] = "0" * 64
        findings = self.findings(self.payload("source.txt:1", [evidence]))
        self.assertTrue(any("does not match the normalized quoted_text bytes" in finding.message for finding in findings))

    def test_opt_in_is_explicit_and_non_opted_maps_remain_compatible(self) -> None:
        payload = self.payload(required=False)
        self.assertEqual(self.findings(payload), [])

    def test_computational_scope_exception_requires_quotes_without_global_opt_in(self) -> None:
        payload = self.payload("source.txt:1", required=False)
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        row["source_scope_classification"] = "non_named_computational_illustration"

        findings = self.findings(payload)
        self.assertEqual(len(findings), 1)
        self.assertIn("source_anchor_evidence must be a nonempty list", findings[0].message)

        row["source_anchor_evidence"] = [self.quote(1)]
        self.assertEqual(self.findings(payload), [])

    def test_user_approved_scope_exclusion_requires_structured_pinned_metadata(self) -> None:
        payload = self.payload("source.txt:1", [self.quote(1)])
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        row["source_kind"] = "prose_assertion"
        row["claim_bearing"] = True
        quote = self.quote(1)["quoted_text"]
        assert isinstance(quote, str)
        row["user_approved_scope_exclusion"] = {
            "schema": 1,
            "approval_kind": "explicit_user_instruction",
            "approval_reference": "User instruction for this review pass.",
            "approved_at": "2026-07-25",
            "reason": "The user expressly excluded this source-visible claim from required formalization scope.",
            "source_locator": "source.txt:1",
            "source_evidence": "The exact source line remains byte-pinned in the inventory.",
            "source_anchor_quote_sha256": hashlib.sha256(
                quote.encode("utf-8")
            ).hexdigest(),
        }
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")
        self.assertEqual(source_manifest.check_source_manifest(self.paper, "formalized"), [])

        row["user_approved_scope_exclusion"]["approval_kind"] = "curator_note"
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")
        findings = source_manifest.check_source_manifest(self.paper, "formalized")
        self.assertTrue(
            any("approval_kind" in finding.message for finding in findings)
        )

    def test_user_scope_exclusion_may_explicitly_exclude_a_named_formal_kind(self) -> None:
        payload = self.payload("source.txt:1", [self.quote(1)])
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        quote = self.quote(1)["quoted_text"]
        assert isinstance(quote, str)
        row.update(
            {
                "source_kind": "theorem",
                "claim_bearing": True,
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "User instruction for this review pass.",
                    "approved_at": "2026-07-25",
                    "reason": "The user expressly excluded this named theorem from this proof pass.",
                    "source_locator": "source.txt:1",
                    "source_evidence": "The exact source line remains byte-pinned in the inventory.",
                    "source_anchor_quote_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                },
            }
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(source_manifest.check_source_manifest(self.paper, "formalized"), [])

    def test_user_scope_exclusion_keeps_a_named_theorem_quote_visible(self) -> None:
        self.artifact.write_bytes(b"Theorem 1 states the exact audited property.\n")
        payload = self.payload("source.txt:1", [self.quote(1)])
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        quote = self.quote(1)["quoted_text"]
        assert isinstance(quote, str)
        row.update(
            {
                "source_kind": "remark",
                "claim_bearing": True,
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "User instruction for this review pass.",
                    "approved_at": "2026-07-25",
                    "reason": "The user expressly excluded this named theorem from this proof pass.",
                    "source_locator": "source.txt:1",
                    "source_evidence": "The exact source line remains byte-pinned in the inventory.",
                    "source_anchor_quote_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                },
            }
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(source_manifest.check_source_manifest(self.paper, "formalized"), [])

    def test_user_scope_exclusion_cannot_remove_registered_proof_support(self) -> None:
        self.artifact.write_bytes(b"An unnumbered supporting assertion is used below.\n")
        payload = self.payload("source.txt:1", [self.quote(1)], required=False)
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        quote = self.quote(1)["quoted_text"]
        assert isinstance(quote, str)
        row.update(
            {
                "source_kind": "prose_assertion",
                "claim_bearing": True,
                "inventory_role": "proof_support",
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "User instruction for this review pass.",
                    "approved_at": "2026-07-25",
                    "reason": "The user excluded this unnumbered prose assertion from this proof pass.",
                    "source_locator": "source.txt:1",
                    "source_evidence": "The exact source line remains byte-pinned in the inventory.",
                    "source_anchor_quote_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                },
            }
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")

        findings = source_manifest.check_source_manifest(self.paper, "formalized")

        self.assertTrue(
            any("cannot remove an assertion marked as proof_support" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_user_scope_exclusion_allows_unnumbered_remark_with_result_reference(self) -> None:
        self.artifact.write_bytes(
            b"For finite support, some conditions discussed after Theorem 1 may be weakened.\n"
        )
        payload = self.payload("source.txt:1", [self.quote(1)])
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        quote = self.quote(1)["quoted_text"]
        assert isinstance(quote, str)
        row.update(
            {
                "source_kind": "remark",
                "claim_bearing": True,
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "User instruction for this review pass.",
                    "approved_at": "2026-07-25",
                    "reason": "The user excluded this unnumbered remark from this proof pass.",
                    "source_locator": "source.txt:1",
                    "source_evidence": "The exact source line remains byte-pinned in the inventory.",
                    "source_anchor_quote_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                },
            }
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(source_manifest.check_source_manifest(self.paper, "formalized"), [])

    def test_manifest_gate_runs_the_opted_in_anchor_check(self) -> None:
        payload = self.payload()
        row = payload["items"]["source_row"]
        assert isinstance(row, dict)
        # Keep the fixture in ordinary named-theory scope so the manifest
        # reaches the opted-in missing-anchor diagnostic below.
        row["statement"] = "Theorem: fixture source claim."
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")
        findings = source_manifest.check_source_manifest(self.paper, "formalized")
        self.assertEqual(len(findings), 1)
        self.assertIn("source_anchor_evidence must be a nonempty list", findings[0].message)

    def test_structural_public_mode_does_not_mark_a_pinned_source_review_stale(self) -> None:
        """Licensed source absence is a warning, not a private-review reissue trigger."""

        payload = self.payload("source.txt:1", [self.quote(1)])
        payload["source_named_result_inventory_review"] = (
            self.named_result_inventory_review(payload)
        )
        self.manifest.write_text(json.dumps(payload), encoding="utf-8")
        self.artifact.unlink()

        findings = source_manifest.check_source_manifest(
            self.paper, "formalized", require_source_bytes=False
        )

        self.assertTrue(findings)
        self.assertTrue(all(finding.severity == "WARN" for finding in findings))
        self.assertTrue(
            any("not provisioned in this structural checkout" in finding.message for finding in findings)
        )


class CorrectedSourceTargetMapTests(unittest.TestCase):
    """Corrected targets must remain source-anchored and authorization-pinned."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.source = self.paper / "source.txt"
        self.source.write_text(
            "The archival theorem claims an unrestricted result.\n"
            "The displayed proof uses an omitted three-point condition.\n",
            encoding="utf-8",
        )
        self.approval = self.paper / "docs" / "approval.md"
        self.approval.parent.mkdir()
        self.approval.write_text(
            "The repaired target is approved only with its explicit condition.\n",
            encoding="utf-8",
        )

    def payload(self) -> dict[str, object]:
        source_lines = source_manifest.normalized_source_lines(
            source_manifest.normalized_source_text(self.source.read_bytes())
        )
        excerpt = source_manifest.normalized_source_line_excerpt(source_lines, 1, 2)
        assert excerpt is not None
        archival = "The archival theorem claims the unrestricted result."
        corrected = "With the explicit three-point condition, the repaired result holds."
        target: dict[str, object] = {
            "schema": 1,
            "statement": corrected,
            "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": "source.txt:1-2",
            "archival_source_quote_sha256": hashlib.sha256(
                excerpt.encode("utf-8")
            ).hexdigest(),
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-07-25",
                "reference": "The user approved the visible repaired target, not archival equivalence.",
                "target_statement_sha256": hashlib.sha256(
                    corrected.encode("utf-8")
                ).hexdigest(),
                "artifact_path": "docs/approval.md",
                "artifact_sha256": hashlib.sha256(self.approval.read_bytes()).hexdigest(),
            },
        }
        target["corrected_target_sha256"] = source_manifest.corrected_target_record_digest(
            target
        )
        return {
            "items": {
                "opaque_source_key": {
                    "statement": archival,
                    "source_kind": "theorem",
                    "source_location": "source.txt:1-2",
                    "coverage_status": "corrected_source_statement",
                    "source_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
                    "lean_declarations": ["opaque_complete_endpoint"],
                    "corrected_target": target,
                }
            }
        }

    def write_ledger(self, *, resolution: str = "corrected_source_statement") -> None:
        (self.audit / "source_proof_fidelity.json").write_text(
            json.dumps(
                {
                    "defects": [
                        {
                            "id": "FIXTURE-SOURCE-DEFECT",
                            "statement_impact": "source_statement",
                            "resolution": resolution,
                        }
                    ]
                }
            ),
            encoding="utf-8",
        )
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "audit/source_proof_fidelity.json"
                        }
                    }
                }
            ),
            encoding="utf-8",
        )

    def findings(self, payload: dict[str, object]) -> list[object]:
        return source_manifest.corrected_source_statement_map_findings(
            self.paper, "formalized", payload
        )

    def current_excerpt_payload(self) -> dict[str, object]:
        payload = self.payload()
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        target = item["corrected_target"]
        assert isinstance(target, dict)
        approval = target["approval"]
        assert isinstance(approval, dict)
        excerpt = (
            "The repaired target is approved only with its explicit condition."
        )
        approval.pop("artifact_sha256")
        approval.update(
            {
                "artifact_protocol": GATE.CORRECTED_TARGET_APPROVAL_PROTOCOL,
                "artifact_excerpt": excerpt,
                "artifact_excerpt_sha256": hashlib.sha256(
                    excerpt.encode("utf-8")
                ).hexdigest(),
            }
        )
        target["corrected_target_sha256"] = source_manifest.corrected_target_record_digest(
            target
        )
        return payload

    def test_valid_corrected_target_is_anchored_to_its_archival_source(self) -> None:
        self.write_ledger()
        self.assertEqual(self.findings(self.payload()), [])

    def excluded_payload(self) -> dict[str, object]:
        payload = self.payload()
        item = payload["items"]["opaque_source_key"]
        quote = self.source.read_text().rstrip("\n")
        digest = hashlib.sha256(quote.encode()).hexdigest()
        item.pop("lean_declarations")
        item.update(
            claim_bearing=True,
            inventory_role="source_scope_exclusion",
            scope_disposition="user_approved_scope_exclusion",
            coverage_status="user_approved_scope_exclusion",
            source_anchor_evidence=[{
                "path": "source.txt", "line_start": 1, "line_end": 2,
                "quoted_text": quote, "quoted_text_sha256": digest,
            }],
            user_approved_scope_exclusion={
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "The maintainer explicitly deferred this result for the release.",
                "approved_at": "2026-09-06",
                "reason": "The original result remains uncredited pending a feasible-domain proof.",
                "source_locator": "source.txt:1-2",
                "source_evidence": "The theorem claims an unrestricted conclusion beyond the current proof domain.",
                "source_anchor_quote_sha256": digest,
            },
        )
        return payload

    def test_excluded_corrected_target_preserves_validated_provenance_without_endpoint(self) -> None:
        self.write_ledger()
        self.assertEqual(self.findings(self.excluded_payload()), [])

    def test_excluded_corrected_target_still_rejects_stale_approval(self) -> None:
        self.write_ledger()
        payload = self.excluded_payload()
        self.approval.write_text("This artifact no longer contains the approved target.\n")
        self.assertTrue(any("artifact_sha256" in f.message for f in self.findings(payload)))

    def test_excluded_corrected_target_cannot_retain_an_active_route(self) -> None:
        self.write_ledger()
        payload = self.excluded_payload()
        payload["items"]["opaque_source_key"]["lean_declarations"] = ["active_endpoint"]
        self.assertTrue(self.findings(payload))

    def subsumed_payload(self) -> dict[str, object]:
        payload = self.payload()
        payload["source_coverage_mode"] = "named_theoretical_statements"
        payload["semantic_contract_schema"] = 1
        items = payload["items"]
        assert isinstance(items, dict)
        support = items["opaque_source_key"]
        assert isinstance(support, dict)
        support.pop("lean_declarations")
        support.update(
            claim_bearing=True,
            coverage_status="subsumed_by_selected_result",
            inventory_role="subsumed_by_selected_result",
            protocol_role="subsumed_by_selected_result",
            source_status="subsumed_by_selected_result",
            source_scope_classification="source_resolved_within_paper_observation",
            scope_disposition="supporting_context_for_selected_result",
            subsumed_by_source_item="canonical_result",
        )
        items["canonical_result"] = {
            "claim_bearing": True,
            "source_kind": "theorem",
            "title": "Theorem 1. Canonical repaired result",
            "statement": "Theorem 1 gives the selected repaired result.",
            "lean_declarations": ["canonical_complete_endpoint"],
            "semantic_contract": {
                "spec_declaration": "Fixture.CanonicalSpec",
                "evidence_declaration": "Fixture.CanonicalProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        return payload

    def test_subsumed_corrected_target_retains_validated_provenance_without_endpoint(
        self,
    ) -> None:
        self.write_ledger()
        self.assertEqual(self.findings(self.subsumed_payload()), [])

    def test_subsumed_corrected_target_still_rejects_stale_approval(self) -> None:
        self.write_ledger()
        payload = self.subsumed_payload()
        self.approval.write_text("This artifact no longer contains the approved target.\n")
        self.assertTrue(
            any("artifact_sha256" in finding.message for finding in self.findings(payload))
        )

    def test_invalid_subsumption_does_not_exempt_a_corrected_target_endpoint(
        self,
    ) -> None:
        self.write_ledger()
        payload = self.subsumed_payload()
        support = payload["items"]["opaque_source_key"]
        assert isinstance(support, dict)
        support["lean_declarations"] = ["duplicate_active_endpoint"]
        messages = [finding.message for finding in self.findings(payload)]
        self.assertTrue(
            any(
                "corrected_target without coverage_status corrected_source_statement"
                in message
                for message in messages
            ),
            messages,
        )

    def test_exclusion_requires_every_source_slice_in_its_recorded_order(self) -> None:
        payload = self.excluded_payload()
        approval = payload["items"]["opaque_source_key"]["user_approved_scope_exclusion"]
        approval["source_locator"] = "source.txt:1; source.txt:2"
        validate = lambda: source_manifest.user_approved_scope_exclusion_errors(self.paper, approval)
        self.assertEqual(validate(), [])
        approval["source_locator"] = "source.txt:2; source.txt:1"
        self.assertTrue(any("exact source quote" in error for error in validate()))
        approval["source_locator"] = "source.txt:1; source.txt:2"
        self.source.write_text(self.source.read_text().replace("three-point", "four-point"))
        self.assertTrue(any("exact source quote" in error for error in validate()))

    def test_excluded_corrected_target_rejects_malformed_retained_target(self) -> None:
        self.write_ledger()
        payload = self.excluded_payload()
        payload["items"]["opaque_source_key"]["corrected_target"] = "not a target record"
        self.assertTrue(any("structured corrected_target" in f.message for f in self.findings(payload)))

    def test_quarantined_false_source_claim_needs_no_fictitious_corrected_target(self) -> None:
        """A documented false claim is distinct from an approved replacement."""

        self.write_ledger(resolution="quarantined_source_defect")
        payload = self.payload()
        items = payload["items"]
        assert isinstance(items, dict)
        item = items["opaque_source_key"]
        assert isinstance(item, dict)
        item.pop("corrected_target")
        item["coverage_status"] = "not_credited_source_defect"
        item["source_status"] = "quarantined_source_defect"

        self.assertEqual(self.findings(payload), [])

    def test_corrected_source_semantic_bundle_needs_no_single_theorem_endpoint(self) -> None:
        """One corrected algorithm may govern a bounded prerequisite bundle."""

        self.write_ledger()
        payload = self.payload()
        items = payload["items"]
        assert isinstance(items, dict)
        item = items["opaque_source_key"]
        assert isinstance(item, dict)
        item["inventory_role"] = "source_semantic_declaration"
        item["lean_declarations"] = [
            "Fixture.correctedTransition",
            "Fixture.correctedOutput",
        ]

        self.assertEqual(self.findings(payload), [])

    def test_current_approval_ignores_unrelated_artifact_prose_only(self) -> None:
        self.write_ledger()
        payload = self.current_excerpt_payload()
        self.assertEqual(self.findings(payload), [])

        self.approval.write_text(
            "The repaired target is approved only with its explicit condition.\n"
            "This unrelated implementation note was added later.\n",
            encoding="utf-8",
        )
        self.assertEqual(self.findings(payload), [])

        self.approval.write_text(
            "The repaired target is no longer approved with that condition.\n",
            encoding="utf-8",
        )
        findings = self.findings(payload)
        self.assertTrue(
            any("occur exactly once" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_current_approval_rejects_an_ambiguous_repeated_excerpt(self) -> None:
        self.write_ledger()
        payload = self.current_excerpt_payload()
        excerpt = "The repaired target is approved only with its explicit condition."
        self.approval.write_text(excerpt + "\n" + excerpt + "\n", encoding="utf-8")
        findings = self.findings(payload)
        self.assertTrue(
            any("found 2" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_original_locator_never_replaces_the_current_excerpt_check(self) -> None:
        self.write_ledger()
        payload = self.current_excerpt_payload()
        target = payload["items"]["opaque_source_key"]["corrected_target"]
        approval = target["approval"]
        approval["original_artifact_path"] = "docs/retired-approval.md"
        target["corrected_target_sha256"] = (
            source_manifest.corrected_target_record_digest(target)
        )

        # The historical file is intentionally absent. Only its canonical
        # locator is needed; the current file still carries the authority.
        self.assertEqual(self.findings(payload), [])

        self.approval.unlink()
        findings = self.findings(payload)
        self.assertTrue(
            any("artifact_path" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

        self.approval.write_text(
            "This current artifact omits the approved corrected-target excerpt.\n",
            encoding="utf-8",
        )
        findings = self.findings(payload)
        self.assertTrue(
            any("found 0" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_malformed_original_locator_is_rejected_even_with_fresh_digest(
        self,
    ) -> None:
        self.write_ledger()
        payload = self.current_excerpt_payload()
        target = payload["items"]["opaque_source_key"]["corrected_target"]
        approval = target["approval"]
        approval["original_artifact_path"] = "../docs/approval.md"
        target["corrected_target_sha256"] = (
            source_manifest.corrected_target_record_digest(target)
        )
        findings = self.findings(payload)
        self.assertTrue(
            any("original_artifact_path" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_repeated_corrected_presentation_inherits_canonical_endpoint(self) -> None:
        """An alias cannot be forced to recreate its canonical proof route."""

        self.write_ledger()
        payload = self.payload()
        items = payload["items"]
        assert isinstance(items, dict)
        canonical = items["opaque_source_key"]
        assert isinstance(canonical, dict)
        alias = deepcopy(canonical)
        alias.pop("lean_declarations")
        alias["claim_bearing"] = False
        alias["inventory_role"] = "source_presentation_alias"
        alias["source_presentation_alias"] = {
            "schema": 1,
            "canonical_source_item": "opaque_source_key",
            "relation": "repeated_source_presentation",
            "semantic_basis": "The second source presentation has the same corrected target.",
            "validator": "independent source-presentation reviewer",
            "validated_at": "2026-08-19T00:00:00Z",
        }
        items["repeated_presentation"] = alias

        self.assertEqual(self.findings(payload), [])

        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        target = canonical["corrected_target"]
        assert isinstance(target, dict)
        coverage = {
            "coverage": "covered_corrected_target",
            "target_kind": "approved_corrected_target",
            "review_rows": ["opaque_complete_endpoint"],
            "statement_sha256": target["approval"]["target_statement_sha256"],
            "archival_statement_sha256": hashlib.sha256(
                str(canonical["statement"]).encode("utf-8")
            ).hexdigest(),
            "corrected_target_sha256": target["corrected_target_sha256"],
            "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
            "archival_equivalence_claimed": False,
        }
        (self.audit / "paper_coverage_llm.json").write_text(
            json.dumps(
                {
                    "items": {
                        "opaque_source_key": coverage,
                        "repeated_presentation": deepcopy(coverage),
                    }
                }
            ),
            encoding="utf-8",
        )
        self.assertEqual(
            GATE.corrected_target_coverage_findings(self.paper, "formalized"), []
        )

    def test_corrected_target_has_one_primary_endpoint_and_no_proof_helper(self) -> None:
        """A repaired target cannot be routed through a collection of helpers."""

        self.write_ledger()
        for declarations in ([], ["opaque_complete_endpoint", "second_endpoint"], "endpoint"):
            with self.subTest(lean_declarations=declarations):
                payload = self.payload()
                item = payload["items"]["opaque_source_key"]
                assert isinstance(item, dict)
                item["lean_declarations"] = declarations
                findings = self.findings(payload)
                self.assertTrue(
                    any("lean_declarations" in finding.message for finding in findings),
                    [finding.message for finding in findings],
                )

        payload = self.payload()
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        item["proof_lean_declarations"] = ["opaque_partial_proof"]
        findings = self.findings(payload)
        self.assertTrue(
            any("proof_lean_declarations" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_target_cannot_claim_archival_equivalence(self) -> None:
        self.write_ledger()
        payload = self.payload()
        target = payload["items"]["opaque_source_key"]["corrected_target"]
        assert isinstance(target, dict)
        target["archival_equivalence_claimed"] = True
        target["corrected_target_sha256"] = source_manifest.corrected_target_record_digest(target)
        findings = self.findings(payload)
        self.assertTrue(
            any("archival_equivalence_claimed" in finding.message for finding in findings)
        )

    def test_governing_defect_must_be_a_source_statement_correction(self) -> None:
        self.write_ledger(resolution="repaired_in_lean")
        findings = self.findings(self.payload())
        self.assertTrue(
            any("not resolved as corrected_source_statement" in finding.message for finding in findings)
        )

    def test_stale_target_record_is_rejected(self) -> None:
        self.write_ledger()
        payload = self.payload()
        target = payload["items"]["opaque_source_key"]["corrected_target"]
        assert isinstance(target, dict)
        target["corrected_target_sha256"] = "0" * 64
        findings = self.findings(payload)
        self.assertTrue(any("corrected_target_sha256 is stale" in finding.message for finding in findings))

    def test_coverage_fast_lane_rejects_ordinary_credit_for_a_corrected_target(self) -> None:
        payload = self.payload()
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        target = item["corrected_target"]
        assert isinstance(target, dict)
        coverage = {
            "items": {
                "opaque_source_key": {
                    "coverage": "covered_corrected_target",
                    "target_kind": "approved_corrected_target",
                    "review_rows": ["opaque_complete_endpoint"],
                    "statement_sha256": target["approval"][
                        "target_statement_sha256"
                    ],
                    "archival_statement_sha256": hashlib.sha256(
                        item["statement"].encode("utf-8")
                    ).hexdigest(),
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
                    "archival_equivalence_claimed": False,
                }
            }
        }
        coverage_path = self.audit / "paper_coverage_llm.json"
        coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
        self.assertEqual(
            GATE.corrected_target_coverage_findings(self.paper, "formalized"), []
        )

        coverage["items"]["opaque_source_key"]["coverage"] = "covered"
        coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
        findings = GATE.corrected_target_coverage_findings(self.paper, "formalized")
        self.assertTrue(any("uses `covered`" in finding.message for finding in findings))
        self.assertEqual(
            GATE.corrected_target_coverage_findings(
                self.paper,
                "formalized",
                context=SimpleNamespace(v11_lean_claim_graph_selected=True),
            ),
            [],
        )

    def test_coverage_fast_lane_accepts_unique_paper_interface_short_row(self) -> None:
        """Dashboard-local row names may bind one unique configured endpoint."""

        payload = self.payload()
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        endpoint = f"{self.paper.name}.PaperInterface.opaque_complete_endpoint"
        item["lean_declarations"] = [endpoint]
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        target = item["corrected_target"]
        assert isinstance(target, dict)
        coverage = {
            "items": {
                "opaque_source_key": {
                    "coverage": "covered_corrected_target",
                    "target_kind": "approved_corrected_target",
                    "review_rows": [endpoint],
                    "statement_sha256": target["approval"][
                        "target_statement_sha256"
                    ],
                    "archival_statement_sha256": hashlib.sha256(
                        str(item["statement"]).encode("utf-8")
                    ).hexdigest(),
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
                    "archival_equivalence_claimed": False,
                }
            }
        }
        coverage_path = self.audit / "paper_coverage_llm.json"
        coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
        self.assertEqual(
            GATE.corrected_target_coverage_findings(self.paper, "formalized"), []
        )

        coverage["items"]["opaque_source_key"]["review_rows"] = [
            "opaque_complete_endpoint"
        ]
        coverage_path.write_text(json.dumps(coverage), encoding="utf-8")
        self.assertEqual(
            GATE.corrected_target_coverage_findings(self.paper, "formalized"), []
        )

    def test_coverage_fast_lane_accepts_exact_contract_backed_spec(self) -> None:
        """A v11 source card may own a corrected endpoint through its Spec."""

        payload = self.payload()
        payload["semantic_contract_schema"] = 1
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        endpoint = f"{self.paper.name}.PaperInterface.complete_endpoint"
        spec = f"{self.paper.name}.PaperInterface.complete_endpointSpec"
        item["lean_declarations"] = [endpoint]
        item["semantic_contract"] = {
            "spec_declaration": spec,
            "evidence_declaration": endpoint,
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        target = item["corrected_target"]
        assert isinstance(target, dict)
        coverage = {
            "items": {
                "opaque_source_key": {
                    "coverage": "covered_corrected_target",
                    "target_kind": "approved_corrected_target",
                    "review_rows": [spec],
                    "statement_sha256": target["approval"][
                        "target_statement_sha256"
                    ],
                    "archival_statement_sha256": hashlib.sha256(
                        str(item["statement"]).encode("utf-8")
                    ).hexdigest(),
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
                    "archival_equivalence_claimed": False,
                }
            }
        }
        (self.audit / "paper_coverage_llm.json").write_text(
            json.dumps(coverage), encoding="utf-8"
        )

        self.assertEqual(
            GATE.corrected_target_coverage_findings(self.paper, "formalized"), []
        )

    def test_coverage_fast_lane_rejects_ambiguous_paper_interface_short_row(self) -> None:
        """A final component cannot identify a repaired route when ambiguous."""

        payload = self.payload()
        item = payload["items"]["opaque_source_key"]
        assert isinstance(item, dict)
        item["lean_declarations"] = [
            f"{self.paper.name}.PaperInterface.opaque_complete_endpoint"
        ]
        payload["items"]["other_source_key"] = {
            "lean_declarations": [
                f"{self.paper.name}.PaperInterface.Nested.opaque_complete_endpoint"
            ]
        }
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        target = item["corrected_target"]
        assert isinstance(target, dict)
        coverage = {
            "items": {
                "opaque_source_key": {
                    "coverage": "covered_corrected_target",
                    "target_kind": "approved_corrected_target",
                    "review_rows": ["opaque_complete_endpoint"],
                    "statement_sha256": target["approval"][
                        "target_statement_sha256"
                    ],
                    "archival_statement_sha256": hashlib.sha256(
                        str(item["statement"]).encode("utf-8")
                    ).hexdigest(),
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["FIXTURE-SOURCE-DEFECT"],
                    "archival_equivalence_claimed": False,
                }
            }
        }
        (self.audit / "paper_coverage_llm.json").write_text(
            json.dumps(coverage), encoding="utf-8"
        )
        findings = GATE.corrected_target_coverage_findings(self.paper, "formalized")
        self.assertTrue(
            any(
                "must link exactly the sole corrected-target endpoint"
                in finding.message
                for finding in findings
            )
        )


class SourcePremiseConsistencyGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)

    def write_consistency(self, item: dict[str, object]) -> None:
        (self.audit / "source_record_audit.json").write_text(
            json.dumps(
                {
                    "source_premise_consistency_schema": 1,
                    "source_premise_consistency_items": [item],
                }
            ),
            encoding="utf-8",
        )

    def test_direct_eliminator_blocks_full_closeout_but_only_warns_partial(self) -> None:
        self.write_consistency(
            {
                "reviewed_input_type": "Fixture.SourceModel",
                "direct_eliminators": [
                    {
                        "candidate": "Fixture.SourceModel.false",
                        "direct_eliminator": True,
                    }
                ],
                "candidate_data_dependent_eliminators": [],
            }
        )

        full = GATE.check_source_premise_consistency(self.paper, "formalized")
        partial = GATE.check_source_premise_consistency(
            self.paper, "partially formalized"
        )

        self.assertEqual(len(full), 1)
        self.assertEqual(full[0].severity, "ERROR")
        self.assertIn("direct route", full[0].message)
        self.assertEqual(len(partial), 1)
        self.assertEqual(partial[0].severity, "WARN")

    def test_data_dependent_candidate_remains_visible_without_false_closeout_claim(self) -> None:
        self.write_consistency(
            {
                "reviewed_input_type": "Fixture.SourceModel",
                "direct_eliminators": [],
                "candidate_data_dependent_eliminators": [
                    {
                        "candidate": "Fixture.needsExtraData",
                        "direct_eliminator": False,
                    }
                ],
            }
        )

        findings = GATE.check_source_premise_consistency(self.paper, "formalized")

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "WARN")
        self.assertIn("extra non-proposition data", findings[0].message)


class CorrectedModelScopeContractTests(unittest.TestCase):
    """Keep the corrected-target exception narrow and evidence-backed."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        # Synthetic corrected-scope fixtures do not install the source-record
        # helper. Exercise the real identity subprocess path explicitly in
        # its regression test below; ordinary contract fixtures only need a
        # current identity result.
        self._identity_error_impl = GATE.source_record_current_input_fingerprint_error
        identity_patch = patch.object(
            GATE, "source_record_current_input_fingerprint_error", return_value=""
        )
        identity_patch.start()
        self.addCleanup(identity_patch.stop)
        self.identity_helper = (
            self.root
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        )
        self.identity_helper.parent.mkdir(parents=True)
        self.identity_helper.write_text("# fixture identity helper\n", encoding="utf-8")
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.paper_statement_map = self.audit / "paper_statement_map.json"
        self.paper_statement_map.write_text("{}\n", encoding="utf-8")
        self.paper_statement_map_digest = hashlib.sha256(
            self.paper_statement_map.read_bytes()
        ).hexdigest()
        self.approval = self.paper / "docs" / "GOVERNING_CORRECTED_MODEL.md"
        self.approval.parent.mkdir()
        self.approval.write_text(
            "Author-approved corrected model for FixturePaper.\n",
            encoding="utf-8",
        )
        self.archive = self.paper / "source.tar.gz"
        self.archive.write_bytes(b"archived source bytes\n")
        self.approval_digest = hashlib.sha256(self.approval.read_bytes()).hexdigest()
        self.archive_digest = hashlib.sha256(self.archive.read_bytes()).hexdigest()
        self.scope_id = "FixturePaper-corrected-model"
        self.correction_id = "FIXTURE-CORRECTION"
        self.model_spec = "FixturePaper.ClarifiedSourceModel"
        self.target = "FixturePaper.PaperInterface.corrected_main_result"
        self.semantic_key = "semantic-model::corrected_main_result"
        self.semantic_digest = self._sha("corrected-main-result-expanded-surface")
        self.assumption_row = "positive_rate"
        self.assumption = "FixturePaper.PaperInterface.positive_rate"
        self.assumption_key = "semantic-model::positive_rate"
        self.assumption_digest = self._sha("positive-rate-expanded-surface")
        self.field_key = "FixturePaper.ClarifiedSourceModel.seller_type_count_pos"
        self.audit_digest = self._sha("current-source-record-audit")
        self.raw_integrity_digest = self._sha("current-source-record-raw-integrity")
        self.scope_digest = self._sha("current-formalization-scope")
        self.field_digest = self._sha("current-expanded-field")
        self.governing_correction = {
            "id": self.correction_id,
            "clause": "Use the approved finite corrected state model.",
            "source_anchor": "docs/GOVERNING_CORRECTED_MODEL.md:1",
            "relation": "author_approved_correction",
            "model_evidence": self.model_spec,
            "does_not_claim_archive_derivation": True,
        }
        self.governing_digest = GATE.governing_corrections_sha256(
            {"governing_corrections": [self.governing_correction]}
        )
        assert self.governing_digest is not None

    @staticmethod
    def _sha(value: str) -> str:
        return hashlib.sha256(value.encode("utf-8")).hexdigest()

    def _approval_fields(self) -> dict[str, str]:
        return {
            "approval_artifact_path": "docs/GOVERNING_CORRECTED_MODEL.md",
            "approval_artifact_sha256": self.approval_digest,
        }

    def _source_anchor(self) -> str:
        return "docs/GOVERNING_CORRECTED_MODEL.md:1"

    def _semantic_item(
        self,
        row: str,
        declaration: str,
        key: str,
        digest: str,
        *,
        consumes_model: bool,
    ) -> dict[str, object]:
        return {
            "row": row,
            "qualified_declaration": declaration,
            "judgment_key": key,
            "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            "source_record_item_semantic_id": self._sha(key + "-semantic-id"),
            "source_record_item_context_sha256": self._sha(
                key + "-context"
            ),
            "source_record_item_sha256": digest,
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": declaration,
                    "elaborated_signature_sha256": self._sha(
                        key + "-elaborated-signature"
                    ),
                }
            ],
            "source_record_item_reuse_eligibility": {
                "eligible": True,
                "blockers": [],
            },
            "expanded_lean_surface": {
                "record_roots": [self.model_spec] if consumes_model else [],
                "record_field_types": (
                    [
                        {
                            "path": (
                                f"{self.model_spec} -> {self.field_key}"
                            )
                        }
                    ]
                    if consumes_model
                    else []
                ),
            },
            "record_input_bindings": (
                [
                    {
                        "binder_names": ["model"],
                        "record_roots": [self.model_spec],
                    }
                ]
                if consumes_model
                else []
            ),
            "dimensions": [
                {
                    "id": "expanded_binders_and_domain",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": False,
                }
            ],
        }

    def _semantic_items(self) -> list[dict[str, object]]:
        return [
            self._semantic_item(
                "corrected_main_result",
                self.target,
                self.semantic_key,
                self.semantic_digest,
                consumes_model=True,
            ),
            self._semantic_item(
                self.assumption_row,
                self.assumption,
                self.assumption_key,
                self.assumption_digest,
                consumes_model=False,
            ),
        ]

    def _semantic_mapping(
        self, item: dict[str, object], *, disposition: str
    ) -> dict[str, object]:
        return {
            "source_record_item_key": item["judgment_key"],
            "source_record_item_sha256": item["source_record_item_sha256"],
            "qualified_declaration": item["qualified_declaration"],
            "disposition": disposition,
            "correction_ids": [self.correction_id],
            "source_anchor": self._source_anchor(),
            "semantic_comparison": "The approved corrected target is compared directly to its governing model.",
            "lean_evidence": self.model_spec,
            "dimensions": {
                "expanded_binders_and_domain": {
                    "verdict": "author_approved_correction",
                    "source_locator": self._source_anchor(),
                    "semantic_comparison": "The expanded domain is part of the author-approved corrected target.",
                    "lean_evidence": self.model_spec,
                }
            },
            **self._approval_fields(),
        }

    @staticmethod
    def _mark_raw_item_aggregate_only(item: dict[str, object]) -> None:
        for key in (
            "source_record_item_digest_schema",
            "source_record_item_semantic_id",
            "source_record_item_context_sha256",
            "source_record_item_sha256",
            "reviewed_elaborated_signature_identities",
        ):
            item.pop(key, None)
        item["source_record_item_reuse_eligibility"] = {
            "eligible": False,
            "blockers": ["no source-content semantic identity"],
        }

    @staticmethod
    def _mark_mapping_aggregate_only(mapping: dict[str, object]) -> None:
        mapping.pop("source_record_item_sha256", None)
        mapping["aggregate_audit_freshness_only"] = True

    def _status_payload(self, contract_digest: str) -> dict[str, object]:
        return {
            "id": "FixturePaper",
            "status": "formalized",
            "review_surface": {
                "include_names": ["corrected_main_result"],
                "assumption_names": [self.assumption_row],
            },
            "formalization_scope": {
                "kind": GATE.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                "scope_id": self.scope_id,
                "scope_role": GATE.WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
                "whole_paper_closeout_claimed": True,
                "approval": {
                    "recorded_at": "2026-07-24T00:00:00Z",
                    "statement": "The author approved this corrected finite model as the formalization target.",
                    "artifact_path": "docs/GOVERNING_CORRECTED_MODEL.md",
                    "artifact_sha256": self.approval_digest,
                },
                "base_archive": {
                    "path": "source.tar.gz",
                    "sha256": self.archive_digest,
                },
                "model_spec_declaration": self.model_spec,
                "target_result_declarations": [self.target],
                "correction_ids": [self.correction_id],
                "archival_equivalence_claimed": False,
                "semantic_contract": {
                    "path": "audit/corrected_model_semantic_contract.json",
                    "sha256": contract_digest,
                },
            },
            "governing_corrections": [dict(self.governing_correction)],
        }

    def _contract_payload(self) -> dict[str, object]:
        dimensions = {
            dimension: {
                "disposition": "reviewed",
                "rationale": "The corrected target records this semantic dimension explicitly.",
                "lean_evidence": self.model_spec,
            }
            for dimension in sorted(GATE.CORRECTED_MODEL_SEMANTIC_DIMENSIONS)
        }
        return {
            "schema": GATE.CORRECTED_MODEL_CONTRACT_SCHEMA,
            "scope_id": self.scope_id,
            "approval_artifact_sha256": self.approval_digest,
            "base_archive_sha256": self.archive_digest,
            "model_spec_declaration": self.model_spec,
            "target_result_declarations": [self.target],
            "correction_ids": [self.correction_id],
            "governing_corrections_sha256": self.governing_digest,
            "archival_equivalence_claimed": False,
            "semantic_dimensions": sorted(GATE.CORRECTED_MODEL_SEMANTIC_DIMENSIONS),
            "source_record_audit_sha256": self.audit_digest,
            "source_record_audit_integrity_sha256": self.raw_integrity_digest,
            "source_record_scope_sha256": self.scope_digest,
            "semantic_item_keys": [self.semantic_key, self.assumption_key],
            "semantic_item_mappings": [
                self._semantic_mapping(
                    self._semantic_items()[0],
                    disposition="author_approved_correction",
                ),
                self._semantic_mapping(
                    self._semantic_items()[1],
                    disposition="author_approved_additional_assumption",
                ),
            ],
            "target_result_mappings": [
                {
                    "target_declaration": self.target,
                    "source_record_item_key": self.semantic_key,
                    "source_record_item_sha256": self.semantic_digest,
                    "model_spec_declaration": self.model_spec,
                    "correction_ids": [self.correction_id],
                    "source_anchor": self._source_anchor(),
                    "semantic_comparison": "The target consumes the governing corrected model record.",
                    "lean_evidence": self.model_spec,
                    **self._approval_fields(),
                }
            ],
            "assumption_mappings": [
                {
                    "assumption_declaration": self.assumption,
                    "source_record_item_key": self.assumption_key,
                    "source_record_item_sha256": self.assumption_digest,
                    "disposition": "author_approved_additional_assumption",
                    "correction_ids": [self.correction_id],
                    "source_anchor": self._source_anchor(),
                    "semantic_comparison": "The positive-rate premise is explicit in the approved corrected model.",
                    "lean_evidence": self.model_spec,
                    **self._approval_fields(),
                }
            ],
            "semantic_review_groups": [
                {
                    "item_keys": [self.semantic_key, self.assumption_key],
                    "correction_ids": [self.correction_id],
                    "dimensions": dimensions,
                }
            ],
            "model_field_mappings": [
                {
                    "source_record_item_key": self.field_key,
                    "source_record_item_sha256": self.field_digest,
                    "correction_id": self.correction_id,
                    "semantic_role": "finite seller carrier",
                    "rationale": "The direct record field is part of the approved corrected target.",
                    "lean_evidence": self.model_spec,
                }
            ],
        }

    def _write_valid_scope(self) -> dict[str, object]:
        self._write_raw_audit(
            {
                    "source_record_audit_sha256": self.audit_digest,
                    "paper_statement_map_sha256": self.paper_statement_map_digest,
                    "source_record_input_fingerprint": {
                        "max_depth": 4,
                        "no_lean": False,
                        "engine_identities": [
                            {
                                "path": "scripts/source_record_audit.py",
                                "sha256": self._sha("fixture-engine-input"),
                            }
                        ],
                    },
                    "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                    "import_module": "FixturePaper.PaperInterface",
                    "formalization_scope": {
                        "kind": GATE.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                        "scope_id": self.scope_id,
                        "approval_artifact_sha256": self.approval_digest,
                        "base_archive_sha256": self.archive_digest,
                        "model_spec_declaration": self.model_spec,
                        "target_result_declarations": [self.target],
                        "correction_ids": [self.correction_id],
                        "governing_corrections_sha256": self.governing_digest,
                        "archival_equivalence_claimed": False,
                        "scope_sha256": self.scope_digest,
                    },
                    "expected_semantic_model_judgment_keys": [
                        self.semantic_key,
                        self.assumption_key,
                    ],
                    "semantic_model_items": self._semantic_items(),
                    "available_local_lean_declarations": [self.model_spec],
                    "recursive_field_items": [
                        {
                            "judgment_key": self.field_key,
                            "structure": self.model_spec,
                            "path": f"{self.model_spec} -> {self.model_spec}.seller_type_count_pos",
                            "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                            "source_record_item_semantic_id": self._sha(
                                self.field_key + "-semantic-id"
                            ),
                            "source_record_item_context_sha256": self._sha(
                                self.field_key + "-context"
                            ),
                            "source_record_item_sha256": self.field_digest,
                            "reviewed_elaborated_signature_identities": [
                                {
                                    "qualified_declaration": self.target,
                                    "elaborated_signature_sha256": self._sha(
                                        self.field_key + "-elaborated-signature"
                                    ),
                                }
                            ],
                            "source_record_item_reuse_eligibility": {
                                "eligible": True,
                                "blockers": [],
                            },
                        }
                    ],
            }
        )
        raw_audit = json.loads(
            (self.audit / "source_record_audit.json").read_text(encoding="utf-8")
        )
        self.audit_digest = str(raw_audit["source_record_audit_sha256"])
        self.raw_integrity_digest = str(
            raw_audit["source_record_audit_integrity_sha256"]
        )
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = self._contract_payload()
        contract_path.write_text(
            json.dumps(contract, sort_keys=True), encoding="utf-8"
        )
        contract_digest = hashlib.sha256(contract_path.read_bytes()).hexdigest()
        status = self._status_payload(contract_digest)
        (self.paper / "status.json").write_text(
            json.dumps(status, sort_keys=True), encoding="utf-8"
        )
        return status

    def _write_raw_audit(self, payload: dict[str, object]) -> None:
        complete_v10_source_record_scan_fixture(payload, paper=self.paper.name)
        stamp_source_record_audit_receipts(payload)
        (self.audit / "source_record_audit.json").write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )

    def _write_status(self, status: dict[str, object]) -> None:
        (self.paper / "status.json").write_text(
            json.dumps(status, sort_keys=True), encoding="utf-8"
        )

    def _rewrite_contract(
        self, status: dict[str, object], contract: dict[str, object]
    ) -> None:
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract_path.write_text(
            json.dumps(contract, sort_keys=True), encoding="utf-8"
        )
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        contract_ref = scope["semantic_contract"]
        assert isinstance(contract_ref, dict)
        contract_ref["sha256"] = hashlib.sha256(contract_path.read_bytes()).hexdigest()
        self._write_status(status)

    def test_complete_pinned_contract_is_the_only_corrected_scope_that_bypasses_legacy_judgments(self) -> None:
        status = self._write_valid_scope()

        self.assertEqual(
            GATE.corrected_model_scope_contract_findings(
                self.paper, "formalized", status
            ),
            [],
        )
        self.assertTrue(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )
        # There is deliberately no legacy source_record_match_llm.json fixture.
        self.assertEqual(
            GATE.check_source_record_judgments(self.paper, "formalized"), []
        )

    def test_corrected_scope_without_explicit_authority_never_bypasses_audit(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        scope.pop("scope_role")
        scope.pop("whole_paper_closeout_claimed")
        self._write_status(status)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any("explicitly declare scope_role" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )

    def test_legacy_scalar_scope_derives_an_omitted_target_mapping_model(self) -> None:
        status = self._write_valid_scope()
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        contract["target_result_mappings"][0].pop("model_spec_declaration")
        self._rewrite_contract(status, contract)

        self.assertEqual(
            GATE.corrected_model_scope_contract_findings(
                self.paper, "formalized", status
            ),
            [],
        )

    def test_component_scope_is_valid_evidence_but_never_a_waiver(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        scope["scope_role"] = GATE.COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE
        scope["whole_paper_closeout_claimed"] = False
        status["status"] = "partially formalized"
        self._write_status(status)

        self.assertEqual(
            GATE.corrected_model_scope_contract_findings(
                self.paper, "partially formalized", status
            ),
            [],
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )

    def test_component_scope_cannot_promote_a_paper_to_full_closeout(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        scope["scope_role"] = GATE.COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE
        scope["whole_paper_closeout_claimed"] = False
        status["status"] = "formalized"
        self._write_status(status)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any("cannot support full-closeout status" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )

    def test_component_scope_rejects_a_whole_paper_claim(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        scope["scope_role"] = GATE.COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE
        scope["whole_paper_closeout_claimed"] = True
        status["status"] = "partially formalized"
        self._write_status(status)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "partially formalized", status
        )
        self.assertTrue(
            any("conflicts with whole_paper_closeout_claimed=true" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_current_corrected_scope_exposes_only_exact_transitive_model_fields(self) -> None:
        status = self._write_valid_scope()

        fields = GATE.current_author_approved_corrected_model_field_items(
            self.paper, status
        )

        self.assertIsNotNone(fields)
        assert fields is not None
        self.assertEqual(set(fields), {self.field_key})

    def test_raw_surface_mutation_with_old_receipt_cannot_support_corrected_scope(self) -> None:
        """A shape-valid aggregate digest cannot authenticate edited raw items."""

        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        receipt = audit["source_record_audit_integrity_sha256"]
        audit["semantic_model_items"][0]["dimensions"][0][
            "requires_checked_bridge_when_detected"
        ] = True
        # Deliberately retain the old raw receipt and input/aggregate identities.
        self.assertEqual(receipt, audit["source_record_audit_integrity_sha256"])
        audit_path.write_text(json.dumps(audit, sort_keys=True), encoding="utf-8")

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "compact raw-evidence digest is stale"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_restamped_raw_surface_mutation_cannot_support_corrected_scope(self) -> None:
        """Recomputing only the transport receipt cannot bless a raw edit."""

        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        aggregate_digest = audit["source_record_audit_sha256"]
        old_receipt = audit["source_record_audit_integrity_sha256"]
        audit["semantic_model_items"][0]["dimensions"][0][
            "requires_checked_bridge_when_detected"
        ] = True
        stamp_source_record_audit_integrity(audit)
        self.assertEqual(audit["source_record_audit_sha256"], aggregate_digest)
        self.assertNotEqual(
            audit["source_record_audit_integrity_sha256"], old_receipt
        )
        audit_path.write_text(json.dumps(audit, sort_keys=True), encoding="utf-8")

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "compact raw-evidence digest is stale"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_changed_engine_identity_invalidates_current_input_fingerprint(self) -> None:
        """Evidence gates replay identity-only mode against current engine inputs."""

        status = self._write_valid_scope()
        audit = json.loads(
            (self.audit / "source_record_audit.json").read_text(encoding="utf-8")
        )
        current_fingerprint = json.loads(
            json.dumps(audit["source_record_input_fingerprint"])
        )
        current_fingerprint["engine_identities"][0]["sha256"] = self._sha(
            "changed-engine-input"
        )
        helper_output = {
            "schema": 1,
            "paper": self.paper.name,
            "paper_statement_map_sha256": self.paper_statement_map_digest,
            "source_record_input_fingerprint": current_fingerprint,
        }
        proc = SimpleNamespace(
            returncode=0,
            stdout=json.dumps(helper_output),
            stderr="",
        )
        with (
            patch.object(
                GATE,
                "source_record_current_input_fingerprint_error",
                side_effect=self._identity_error_impl,
            ),
            patch.object(GATE.subprocess, "run", return_value=proc) as run,
        ):
            findings = GATE.corrected_model_scope_contract_findings(
                self.paper, "formalized", status
            )

        self.assertTrue(
            any(
                "source_record_input_fingerprint is stale" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )
        command = run.call_args.args[0]
        self.assertIn("--identity-only", command)
        self.assertIn("--max-depth", command)
        self.assertIn("4", command)
        self.assertNotIn("--no-lean", command)

    def test_explicit_aggregate_freshness_covers_nonreusable_items(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        for item in audit["semantic_model_items"]:
            self._mark_raw_item_aggregate_only(item)
        self._mark_raw_item_aggregate_only(audit["recursive_field_items"][0])
        self._write_raw_audit(audit)

        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        contract["source_record_audit_sha256"] = audit["source_record_audit_sha256"]
        contract["source_record_audit_integrity_sha256"] = audit[
            "source_record_audit_integrity_sha256"
        ]
        for mapping in contract["semantic_item_mappings"]:
            self._mark_mapping_aggregate_only(mapping)
        self._mark_mapping_aggregate_only(contract["target_result_mappings"][0])
        self._mark_mapping_aggregate_only(contract["assumption_mappings"][0])
        self._mark_mapping_aggregate_only(contract["model_field_mappings"][0])
        self._rewrite_contract(status, contract)

        self.assertEqual(
            GATE.corrected_model_scope_contract_findings(
                self.paper, "formalized", status
            ),
            [],
        )

    def test_nonreusable_items_cannot_implicitly_or_synthetically_use_item_freshness(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        target_item = audit["semantic_model_items"][0]
        self._mark_raw_item_aggregate_only(target_item)
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "must set aggregate_audit_freshness_only" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        self._mark_mapping_aggregate_only(contract["semantic_item_mappings"][0])
        self._mark_mapping_aggregate_only(contract["target_result_mappings"][0])
        contract["semantic_item_mappings"][0]["source_record_item_sha256"] = self.semantic_digest
        self._rewrite_contract(status, contract)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "must not retain an item digest for aggregate-only freshness"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_reusable_items_cannot_claim_aggregate_freshness(self) -> None:
        status = self._write_valid_scope()
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        contract["semantic_item_mappings"][0][
            "aggregate_audit_freshness_only"
        ] = True
        self._rewrite_contract(status, contract)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "claims aggregate-only freshness for a reusable raw item"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_raw_item_freshness_metadata_is_fail_closed(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        target_item = audit["semantic_model_items"][0]
        target_item.pop("source_record_item_reuse_eligibility")
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "requires generated source_record_item_reuse_eligibility"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

        self._mark_raw_item_aggregate_only(target_item)
        target_item["source_record_item_sha256"] = self.semantic_digest
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "aggregate-only freshness while retaining item-level metadata"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_corrected_contract_requires_current_source_map_for_aggregate_freshness(self) -> None:
        status = self._write_valid_scope()
        self.paper_statement_map.write_text('{"changed": true}\n', encoding="utf-8")

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )
        self.assertTrue(
            any(
                "paper_statement_map_sha256 is stale" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_missing_contract_never_bypasses_legacy_source_record_requirements(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        assert isinstance(scope, dict)
        scope.pop("semantic_contract")
        self._write_status(status)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any("requires semantic_contract metadata" in finding.message for finding in findings)
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )
        self.assertTrue(
            GATE.check_source_record_judgments(self.paper, "formalized")
        )

    def test_corrected_target_must_have_a_current_expanded_semantic_row(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        audit["expected_semantic_model_judgment_keys"] = []
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "must expose exactly one current semantic item"
                in finding.message
                for finding in findings
            )
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )

    def test_corrected_contract_covers_nested_fields_reachable_from_model_record(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        audit["recursive_field_items"].extend(
            [
                {
                    "judgment_key": "FixturePaper.ClarifiedSourceModel.ordinal_model",
                    "structure": "FixturePaper.ClarifiedSourceModel",
                    "path": (
                        "FixturePaper.ClarifiedSourceModel -> "
                        "FixturePaper.ClarifiedSourceModel.ordinal_model"
                    ),
                    "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                    "source_record_item_semantic_id": self._sha(
                        "nested-record-field-semantic-id"
                    ),
                    "source_record_item_context_sha256": self._sha(
                        "nested-record-field-context"
                    ),
                    "source_record_item_sha256": self._sha("nested-record-field"),
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": self.target,
                            "elaborated_signature_sha256": self._sha(
                                "nested-record-field-elaborated-signature"
                            ),
                        }
                    ],
                    "source_record_item_reuse_eligibility": {
                        "eligible": True,
                        "blockers": [],
                    },
                },
                {
                    "judgment_key": "FixturePaper.OrdinalModel.strict_tail",
                    "structure": "FixturePaper.OrdinalModel",
                    "path": (
                        "FixturePaper.OrdinalModel -> "
                        "FixturePaper.OrdinalModel.strict_tail"
                    ),
                    "source_record_item_digest_schema": GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                    "source_record_item_semantic_id": self._sha(
                        "nested-expanded-field-semantic-id"
                    ),
                    "source_record_item_context_sha256": self._sha(
                        "nested-expanded-field-context"
                    ),
                    "source_record_item_sha256": self._sha("nested-expanded-field"),
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": self.target,
                            "elaborated_signature_sha256": self._sha(
                                "nested-expanded-field-elaborated-signature"
                            ),
                        }
                    ],
                    "source_record_item_reuse_eligibility": {
                        "eligible": True,
                        "blockers": [],
                    },
                },
            ]
        )
        target_item = audit["semantic_model_items"][0]
        assert isinstance(target_item, dict)
        surface = target_item["expanded_lean_surface"]
        assert isinstance(surface, dict)
        record_fields = surface["record_field_types"]
        assert isinstance(record_fields, list)
        record_fields.extend(
            [
                {
                    "path": (
                        "FixturePaper.ClarifiedSourceModel -> "
                        "FixturePaper.ClarifiedSourceModel.ordinal_model"
                    )
                },
                {
                    "path": (
                        "FixturePaper.ClarifiedSourceModel -> "
                        "FixturePaper.ClarifiedSourceModel.ordinal_model -> "
                        "FixturePaper.OrdinalModel.strict_tail"
                    )
                },
            ]
        )
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "cover exactly every expanded corrected-model field reachable"
                in finding.message
                for finding in findings
            )
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )
        self.assertIsNone(
            GATE.current_author_approved_corrected_model_field_items(
                self.paper, status
            )
        )

    def test_semantically_incomplete_but_rehashed_contract_never_bypasses_legacy_judgments(self) -> None:
        status = self._write_valid_scope()
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        group = contract["semantic_review_groups"][0]
        group["dimensions"].pop("extended_rate_codomain")
        self._rewrite_contract(status, contract)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any("must cover every semantic dimension" in finding.message for finding in findings)
        )
        self.assertFalse(
            GATE.author_approved_corrected_scope_contract_is_current(
                self.paper, status
            )
        )
        self.assertTrue(
            GATE.check_source_record_judgments(self.paper, "formalized")
        )

    def test_governing_correction_content_is_pinned_not_only_its_id(self) -> None:
        status = self._write_valid_scope()
        corrections = status["governing_corrections"]
        assert isinstance(corrections, list)
        correction = corrections[0]
        assert isinstance(correction, dict)
        correction["clause"] = "Use a different corrected finite state model."
        self._write_status(status)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "complete current correction content" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_target_mapping_requires_the_exact_fully_qualified_declaration(self) -> None:
        status = self._write_valid_scope()
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        target_mapping = contract["target_result_mappings"][0]
        target_mapping["target_declaration"] = (
            "Other.PaperInterface.corrected_main_result"
        )
        self._rewrite_contract(status, contract)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "does not match a generated fully qualified PaperInterface semantic item"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_target_mapping_requires_the_governing_model_record_in_expanded_surface(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        target_item = audit["semantic_model_items"][0]
        target_item["expanded_lean_surface"]["record_roots"] = [
            "Other.ClarifiedSourceModel"
        ]
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "target does not consume the exact governing model record"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_detected_bridge_boundary_requires_a_current_local_declaration(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        target_dimension = audit["semantic_model_items"][0]["dimensions"][0]
        target_dimension["requires_checked_bridge_when_detected"] = True
        self._write_raw_audit(audit)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "needs fully qualified checked_bridge_declarations"
                in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_explicit_assumptions_require_per_item_contract_mappings(self) -> None:
        status = self._write_valid_scope()
        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        contract["assumption_mappings"] = []
        self._rewrite_contract(status, contract)

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "requires assumption_mappings" in finding.message
                or "assumption_mappings must cover exactly" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_current_corrected_scope_accepts_only_exact_approved_assumption_rows(self) -> None:
        status = self._write_valid_scope()
        (self.audit / "assumption_match_llm.json").write_text(
            json.dumps(
                {
                    "items": {
                        self.assumption_row: {
                            "judgment": "documented_additional_assumption"
                        }
                    }
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )

        self.assertEqual(GATE.check_status_alignment(self.paper, "formalized"), [])

        contract_path = self.audit / "corrected_model_semantic_contract.json"
        contract = json.loads(contract_path.read_text(encoding="utf-8"))
        contract["assumption_mappings"][0]["disposition"] = "literal_source_condition"
        self._rewrite_contract(status, contract)
        self.assertEqual(GATE.check_status_alignment(self.paper, "formalized"), [])

        contract["assumption_mappings"] = []
        self._rewrite_contract(status, contract)
        findings = GATE.check_status_alignment(self.paper, "formalized")
        self.assertEqual(len(findings), 1)
        self.assertIn("non-source/caveat assumption", findings[0].message)

    def test_v11_corrected_scope_rows_require_exact_scope_and_approval_pins(self) -> None:
        status = self._write_valid_scope()
        scope = status["formalization_scope"]
        approval = scope["approval"]
        assumptions = {
            "items": {
                self.assumption_row: {
                    "judgment": "documented_additional_assumption",
                    "author_approved_corrected_scope": {
                        "scope_id": scope["scope_id"],
                        "approval_artifact_path": approval["artifact_path"],
                        "approval_artifact_sha256": approval["artifact_sha256"],
                        "correction_ids": [self.correction_id],
                    },
                }
            }
        }

        self.assertEqual(
            GATE.current_v11_author_approved_assumption_rows(status, assumptions),
            {self.assumption_row},
        )

        assumptions["items"][self.assumption_row][
            "author_approved_corrected_scope"
        ]["approval_artifact_sha256"] = "0" * 64
        self.assertEqual(
            GATE.current_v11_author_approved_assumption_rows(status, assumptions),
            set(),
        )

        self._write_valid_scope()
        (self.audit / "assumption_match_llm.json").write_text(
            json.dumps(
                {"items": {self.assumption_row: {"judgment": "partial_boundary"}}},
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        findings = GATE.check_status_alignment(self.paper, "formalized")
        self.assertEqual(len(findings), 1)
        self.assertIn("non-source/caveat assumption", findings[0].message)

    def test_corrected_scope_rejects_non_sha_source_record_digests(self) -> None:
        status = self._write_valid_scope()
        audit_path = self.audit / "source_record_audit.json"
        audit = json.loads(audit_path.read_text(encoding="utf-8"))
        audit["source_record_audit_sha256"] = "not-a-sha256"
        audit_path.write_text(json.dumps(audit, sort_keys=True), encoding="utf-8")

        findings = GATE.corrected_model_scope_contract_findings(
            self.paper, "formalized", status
        )

        self.assertTrue(
            any(
                "requires a SHA-256 audit digest" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )


class SemanticContractInventoryTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper = Path(self.temporary.name) / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        (self.audit / "source_proof_fidelity.json").write_text(
            json.dumps(
                {
                    "defects": [
                        {
                            "id": "FIX-1",
                            "resolution": "repaired_in_lean",
                        }
                    ]
                }
            ),
            encoding="utf-8",
        )

    def findings(self, payload: dict[str, object]) -> list[object]:
        # These fixtures exercise source-claim contracts.  Make their normal
        # closeout scope explicit and give only claim/contract fixtures a
        # source presentation category; catalogue/prose fixtures remain
        # outside ordinary named-theory selection by construction.
        payload = json.loads(json.dumps(payload))
        payload.setdefault("source_coverage_mode", "named_theoretical_statements")
        raw_items = payload.get("items")
        if isinstance(raw_items, dict):
            for item in raw_items.values():
                if not isinstance(item, dict):
                    continue
                if (
                    item.get("claim_bearing") is True
                    or "semantic_contract" in item
                    or "source_defect_ids" in item
                    or "source_core_projection" in item
                ):
                    item.setdefault("source_kind", "theorem")
                    # Ordinary coverage follows a source-visible result
                    # presentation, not curator metadata alone. These
                    # contract fixtures deliberately model such a theorem.
                    item.setdefault("statement", "Theorem: fixture source claim.")
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        return GATE.semantic_contract_inventory_findings(
            self.paper, "formalized"
        )

    def test_claim_bearing_and_repaired_items_require_contract_routing(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "claim_bearing": True,
                        "source_defect_ids": ["FIX-1"],
                    }
                },
            }
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(any("lacks semantic_contract" in message for message in messages))
        self.assertTrue(any("repaired_in_lean" in message for message in messages))

    def test_claim_bearing_vocabulary_uses_translation_lane_without_contract(self) -> None:
        for source_kind, statement in (
            ("definition", "Definition 2. A policy is fair exactly when its laws agree."),
            (
                "predicate_vocabulary",
                "Definition. Distributional equality means equality of the displayed laws.",
            ),
        ):
            with self.subTest(source_kind=source_kind):
                findings = self.findings(
                    {
                        "semantic_contract_schema": 1,
                        "items": {
                            "source_vocabulary": {
                                "claim_bearing": True,
                                "source_kind": source_kind,
                                "statement": statement,
                            }
                        },
                    }
                )
                self.assertFalse(
                    any(
                        "lacks semantic_contract" in finding.message
                        for finding in findings
                    ),
                    [finding.message for finding in findings],
                )

    def test_schema_two_typed_prerequisites_do_not_require_legacy_contracts(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "semantic_route_schema": 2,
                "items": {
                    "source_formula": {
                        "claim_bearing": True,
                        "source_kind": "formula",
                        "statement": "The source defines a formula used by the result.",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Fixture.sourceFormula"],
                    },
                    "typed_support": {
                        "claim_bearing": True,
                        "source_kind": "prose_assertion",
                        "statement": "The source proof uses this intermediate support.",
                        "inventory_role": "proof_support",
                        "scope_disposition": "explicit_proof_support",
                    },
                },
            }
        )
        self.assertFalse(
            any("lacks semantic_contract" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_claim_bearing_result_still_requires_contract(self) -> None:
        for source_kind in ("theorem", "proposition", "lemma", "corollary"):
            with self.subTest(source_kind=source_kind):
                findings = self.findings(
                    {
                        "semantic_contract_schema": 1,
                        "items": {
                            "source_result": {
                                "claim_bearing": True,
                                "source_kind": source_kind,
                                "statement": f"{source_kind.title()} 1. Fixture result.",
                            }
                        },
                    }
                )
                self.assertTrue(
                    any(
                        "lacks semantic_contract" in finding.message
                        for finding in findings
                    ),
                    [finding.message for finding in findings],
                )

    def test_quarantined_false_result_uses_defect_support_not_positive_contract(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "false_source_result": {
                        "claim_bearing": True,
                        "source_kind": "lemma",
                        "statement": "Lemma 1. The printed inequality holds.",
                        "source_status": "quarantined_source_defect",
                        "inventory_role": "quarantined_source_defect",
                        "source_defect_ids": ["FIX-1"],
                        "support_lean_declarations": [
                            "Fixture.printedInequalityCounterexample"
                        ],
                    }
                },
            }
        )
        self.assertFalse(
            any("lacks semantic_contract" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )

    def test_nonnamed_defect_support_may_remain_nonclaim_context(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "named_result": {
                        "claim_bearing": True,
                        "source_kind": "theorem",
                        "statement": "Theorem 1. Fixture result.",
                        "source_defect_ids": ["FIX-1"],
                        "semantic_contract": {
                            "spec_declaration": "Fixture.checkedStatement",
                            "evidence_declaration": "Fixture.checkedProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    },
                    "proof_support": {
                        "claim_bearing": False,
                        "source_kind": "formula",
                        "statement": "Equation (1) is the intermediate rearrangement used in the proof.",
                        "source_defect_ids": ["FIX-1"],
                    },
                },
            }
        )
        self.assertEqual(findings, [])

    def test_named_presentations_cannot_be_marked_nonclaim(self) -> None:
        for source_kind in (
            "theorem",
            "proposition",
            "lemma",
            "corollary",
            "definition",
        ):
            with self.subTest(source_kind=source_kind):
                findings = self.findings(
                    {
                        "semantic_contract_schema": 1,
                        "items": {
                            "named_source_item": {
                                "claim_bearing": False,
                                "source_kind": source_kind,
                                "statement": f"{source_kind.title()} 1. Fixture statement.",
                            }
                        },
                    }
                )
                self.assertTrue(
                    any(
                        "cannot set claim_bearing: false" in finding.message
                        or "claim_bearing: false is permitted only" in finding.message
                        for finding in findings
                    ),
                    [finding.message for finding in findings],
                )

    def test_non_claim_bearing_catalogue_item_does_not_opt_into_contract_schema(self) -> None:
        findings = self.findings(
            {
                "items": {
                    "nonformal_figure": {
                        "claim_bearing": False,
                    }
                }
            }
        )
        self.assertEqual(findings, [])

    def test_well_formed_linked_contract_passes_fast_schema_lane(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "claim_bearing": True,
                        "source_defect_ids": ["FIX-1"],
                        "semantic_contract": {
                            "spec_declaration": "Renamed.checkedShape",
                            "evidence_declaration": "Renamed.unrelatedProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    }
                },
            }
        )
        self.assertEqual(findings, [])

    def test_schema_requires_explicit_claim_bearing_classification(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "unclassified_source_row": {
                        "source_defect_ids": [],
                    }
                },
            }
        )
        self.assertTrue(
            any(
                "claim_bearing must be explicitly Boolean" in finding.message
                for finding in findings
            )
        )

    def test_unknown_semantic_shape_fails_closed(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "semantic_contract": {
                            "spec_declaration": "A",
                            "evidence_declaration": "B",
                            "evidence_mode": "proves",
                            "semantic_shape": "runtime_by_function_name",
                        }
                    }
                },
            }
        )
        self.assertTrue(
            any("semantic_shape must be `plain`" in finding.message for finding in findings)
        )

    def test_specialized_shapes_fail_closed_until_meta_roles_exist(self) -> None:
        for shape in (
            "instrumented_execution_bound",
            "initial_transform_commutation",
            "pointwise_refinement",
        ):
            with self.subTest(shape=shape):
                findings = self.findings(
                    {
                        "semantic_contract_schema": 1,
                        "items": {
                            "source_claim": {
                                "claim_bearing": True,
                                "semantic_contract": {
                                    "spec_declaration": "Audited.spec",
                                    "evidence_declaration": "Audited.proof",
                                    "evidence_mode": "proves",
                                    "semantic_shape": shape,
                                },
                            }
                        },
                    }
                )
                self.assertTrue(
                    any(
                        "unsupported until they have role-bearing Lean Meta checks"
                        in finding.message
                        for finding in findings
                    )
                )

    def test_schema_rejects_non_object_items(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {"source_claim": "not an object"},
            }
        )
        self.assertTrue(
            any(
                "items.source_claim: source inventory item is not an object"
                in finding.message
                for finding in findings
            )
        )

        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": [],
            }
        )
        self.assertTrue(
            any("source map `items` must be an object" in finding.message for finding in findings)
        )

    def test_item_opt_in_requires_schema_marker_and_well_formed_defect_ids(self) -> None:
        findings = self.findings(
            {
                "items": {
                    "source_claim": {
                        "claim_bearing": True,
                        "source_defect_ids": ["FIX-1", "FIX-1"],
                    }
                }
            }
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(any("semantic_contract_schema is required" in message for message in messages))
        self.assertTrue(any("unique nonempty strings" in message for message in messages))

    def test_source_defect_ids_must_resolve_in_configured_ledger(self) -> None:
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "claim_bearing": False,
                        "source_defect_ids": ["TYPO-1"],
                    }
                },
            }
        )
        self.assertTrue(
            any("absent from the configured" in finding.message for finding in findings)
        )

    def test_repaired_defect_routing_uses_configured_custom_ledger(self) -> None:
        custom_ledger = self.paper / "proof-ledger.json"
        custom_ledger.write_text(
            json.dumps(
                {
                    "defects": [
                        {"id": "CUSTOM-2", "resolution": "repaired_in_lean"}
                    ]
                }
            ),
            encoding="utf-8",
        )
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "proof-ledger.json"
                        }
                    }
                }
            ),
            encoding="utf-8",
        )
        findings = self.findings(
            {
                "semantic_contract_schema": 1,
                "items": {
                    "source_claim": {
                        "claim_bearing": True,
                        "source_defect_ids": ["CUSTOM-2"],
                        "semantic_contract": {
                            "spec_declaration": "Renamed.checkedShape",
                            "evidence_declaration": "Renamed.unrelatedProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    }
                },
            }
        )
        self.assertEqual(findings, [])


class SemanticContractScopeDispositionTests(unittest.TestCase):
    """Regression tests for the source-only non-claim contract lanes."""

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper = Path(self.temporary.name) / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.source = self.paper / "source.txt"

    def findings(
        self,
        source_quote: str,
        item: dict[str, object],
        *,
        provision_source: bool = True,
        require_source_bytes: bool = True,
    ) -> list[object]:
        self.source.write_text(source_quote + "\n", encoding="utf-8")
        digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        quote_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
        item = {
            **item,
            "source_location": "source.txt:1",
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": source_quote,
                    "quoted_text_sha256": quote_digest,
                }
            ],
        }
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "semantic_contract_schema": 1,
                    "source_coverage_mode": "named_theoretical_statements",
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": digest,
                    "items": {"arbitrary_navigation_key": item},
                }
            ),
            encoding="utf-8",
        )
        if not provision_source:
            self.source.unlink()
        return GATE.semantic_contract_inventory_findings(
            self.paper,
            "formalized",
            require_source_bytes=require_source_bytes,
        )

    def test_false_cannot_hide_named_mathematical_or_formula_claims(self) -> None:
        cases = (
            (
                "Theorem 7 proves that the allocation is optimal.",
                {
                    "statement": "A source theorem establishes optimality.",
                    "source_kind": "example",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "scope_reason": "The source passage is allegedly a local observation.",
                    "source_evidence": "The exact source quote is the claimed observation.",
                },
                "cannot label a named formal statement",
            ),
            (
                "For every input, an optimal allocation exists.",
                {
                    "statement": "The source makes a general existence claim.",
                    "source_kind": "remark",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "scope_reason": "The source passage is allegedly a local observation.",
                    "source_evidence": "The exact source quote is the claimed observation.",
                },
                "general correctness, existence, optimality, or mathematical assertion",
            ),
            (
                "For every x, f(x) = x^2.",
                {
                    "statement": "The source gives a displayed formula.",
                    "source_kind": "remark",
                    "claim_bearing": False,
                    "source_scope_classification": "non_named_computational_illustration",
                    "scope_reason": "The source passage is allegedly a local observation.",
                    "source_evidence": "The exact source quote is the claimed observation.",
                },
                "requires a literal finite observation/report",
            ),
        )
        for source_quote, item, expected in cases:
            with self.subTest(source_quote=source_quote):
                messages = [finding.message for finding in self.findings(source_quote, item)]
                self.assertTrue(any(expected in message for message in messages), messages)

    def test_byte_valid_finite_observation_is_source_only_nonclaim_exemption(self) -> None:
        findings = self.findings(
            "Figure 1 reports a finite simulated welfare estimate for 3 candidate settings.",
            {
                "statement": "Figure 1 reports a finite simulated welfare estimate.",
                "source_kind": "example",
                "claim_bearing": False,
                "source_scope_classification": "non_named_computational_illustration",
                "scope_reason": "The exact source caption reports one finite numerical observation.",
                "source_evidence": "The byte-pinned source caption is the scope evidence.",
                # These are intentionally theorem-like navigation strings. They
                # must not affect a source-semantic scope determination.
                "lean_declarations": ["Fixture.TheoremNamedPlotHelper"],
            },
        )
        self.assertEqual(findings, [])

    def test_byte_valid_open_nonresult_observation_is_nonclaim_exemption(self) -> None:
        findings = self.findings(
            "We leave the multi-firm characterization open.",
            {
                "statement": "The source explicitly leaves the multi-firm case open.",
                "source_kind": "remark",
                "claim_bearing": False,
                "source_scope_classification": (
                    "source_declared_open_nonresult_observation"
                ),
                "coverage_status": "source_declared_open",
                "protocol_role": "source_declared_open",
                "scope_reason": "The exact source remark explicitly reports an unresolved issue.",
                "source_evidence": "The byte-pinned source remark is the scope evidence.",
            },
        )
        self.assertEqual(findings, [])

    def test_ocr_spaced_conjecture_heading_is_open_nonresult_evidence(self) -> None:
        findings = self.findings(
            "C ONJECTURE 1. The displayed limit is zero.",
            {
                "statement": "The source labels the displayed limit as a conjecture.",
                "source_kind": "open_problem",
                "claim_bearing": False,
                "source_scope_classification": (
                    "source_declared_open_nonresult_observation"
                ),
                "coverage_status": "source_declared_open",
                "protocol_role": "source_declared_open",
                "scope_reason": "The exact source heading explicitly marks the statement as a conjecture.",
                "source_evidence": "The byte-pinned OCR source heading is the scope evidence.",
            },
        )
        self.assertEqual(findings, [])

    def test_structural_mode_preserves_open_observation_without_source_bytes(self) -> None:
        item = {
            "statement": "The source explicitly leaves the multi-firm case open.",
            "source_kind": "remark",
            "claim_bearing": False,
            "source_scope_classification": "source_declared_open_nonresult_observation",
            "coverage_status": "source_declared_open",
            "protocol_role": "source_declared_open",
            "scope_reason": "The exact source remark explicitly reports an unresolved issue.",
            "source_evidence": "The byte-pinned source remark is the scope evidence.",
        }
        structural = self.findings(
            "We leave the multi-firm characterization open.",
            item,
            provision_source=False,
            require_source_bytes=False,
        )
        self.assertFalse(
            any(finding.severity == "ERROR" for finding in structural), structural
        )
        strict = GATE.semantic_contract_inventory_findings(
            self.paper, "formalized", require_source_bytes=True
        )
        self.assertTrue(
            any("source_artifact_path does not exist" in finding.message for finding in strict),
            strict,
        )

    def test_structural_open_observation_still_rejects_unsafe_or_malformed_evidence(self) -> None:
        item = {
            "statement": "The source explicitly leaves the multi-firm case open.",
            "source_kind": "remark",
            "claim_bearing": False,
            "source_scope_classification": "source_declared_open_nonresult_observation",
            "coverage_status": "source_declared_open",
            "protocol_role": "source_declared_open",
            "scope_reason": "The exact source remark explicitly reports an unresolved issue.",
            "source_evidence": "The byte-pinned source remark is the scope evidence.",
        }
        self.findings(
            "We leave the multi-firm characterization open.",
            item,
            provision_source=False,
            require_source_bytes=False,
        )
        payload = json.loads((self.audit / "paper_statement_map.json").read_text())
        row = payload["items"]["arbitrary_navigation_key"]
        row["source_location"] = "../outside.txt:1"
        row["source_anchor_evidence"][0]["path"] = "../outside.txt"
        row["source_anchor_evidence"][0]["quoted_text_sha256"] = "0" * 64
        (self.audit / "paper_statement_map.json").write_text(json.dumps(payload))
        findings = GATE.semantic_contract_inventory_findings(
            self.paper, "formalized", require_source_bytes=False
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(
            any(
                "source_location must name the pinned source artifact" in message
                for message in messages
            ),
            messages,
        )

        row["source_location"] = "source.txt:1"
        row["source_anchor_evidence"][0]["path"] = "source.txt"
        (self.audit / "paper_statement_map.json").write_text(json.dumps(payload))
        findings = GATE.semantic_contract_inventory_findings(
            self.paper, "formalized", require_source_bytes=False
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(any("quoted_text_sha256" in message for message in messages), messages)

    def test_user_approved_scope_exclusion_remains_claim_bearing_without_contract(self) -> None:
        source_quote = "The simulation-efficiency issue remains outside this proof campaign."
        quote_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
        findings = self.findings(
            source_quote,
            {
                "statement": "The source-visible simulation issue is excluded by an explicit user scope decision.",
                "source_kind": "remark",
                "claim_bearing": True,
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "The user explicitly excluded this issue from the current proof campaign.",
                    "approved_at": "2026-07-25",
                    "reason": "This standalone simulation issue is intentionally outside the requested proof scope.",
                    "source_evidence": "The exact quoted source passage identifies the excluded issue.",
                    "source_locator": "source.txt:1",
                    "source_anchor_quote_sha256": quote_digest,
                },
            },
        )
        self.assertEqual(findings, [])

    def test_structural_user_scope_exclusion_keeps_shape_and_digest_checks(self) -> None:
        source_quote = "The simulation-efficiency issue remains outside this proof campaign."
        quote_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
        item = {
            "statement": "The source-visible simulation issue is excluded by an explicit user scope decision.",
            "source_kind": "remark",
            "claim_bearing": True,
            "user_approved_scope_exclusion": {
                "schema": 1,
                "approval_kind": "explicit_user_instruction",
                "approval_reference": "The user explicitly excluded this issue from the current proof campaign.",
                "approved_at": "2026-07-25",
                "reason": "This standalone simulation issue is intentionally outside the requested proof scope.",
                "source_evidence": "The exact quoted source passage identifies the excluded issue.",
                "source_locator": "source.txt:1",
                "source_anchor_quote_sha256": quote_digest,
            },
        }
        structural = self.findings(
            source_quote,
            item,
            provision_source=False,
            require_source_bytes=False,
        )
        self.assertFalse(
            any(finding.severity == "ERROR" for finding in structural), structural
        )
        payload = json.loads((self.audit / "paper_statement_map.json").read_text())
        row = payload["items"]["arbitrary_navigation_key"]
        self.assertEqual(
            GATE._semantic_contract_user_scope_exclusion_error(
                self.paper,
                "formalized",
                self.audit / "paper_statement_map.json",
                payload,
                row,
                require_source_bytes=False,
            ),
            "",
        )

        approval = payload["items"]["arbitrary_navigation_key"][
            "user_approved_scope_exclusion"
        ]
        approval["source_anchor_quote_sha256"] = "0" * 64
        (self.audit / "paper_statement_map.json").write_text(json.dumps(payload))
        malformed = GATE._semantic_contract_user_scope_exclusion_error(
            self.paper,
            "formalized",
            self.audit / "paper_statement_map.json",
            payload,
            row,
            require_source_bytes=False,
        )
        self.assertIn("source_anchor_quote_sha256", malformed)

    def test_user_approved_scope_exclusion_cannot_reclassify_a_claim_as_false(self) -> None:
        source_quote = "The simulation-efficiency issue remains outside this proof campaign."
        quote_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
        findings = self.findings(
            source_quote,
            {
                "statement": "A source-visible issue is not a finite observational exemption.",
                "source_kind": "remark",
                "claim_bearing": False,
                "user_approved_scope_exclusion": {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                    "approval_reference": "The user explicitly excluded this issue from the current proof campaign.",
                    "approved_at": "2026-07-25",
                    "reason": "This standalone simulation issue is intentionally outside the requested proof scope.",
                    "source_evidence": "The exact quoted source passage identifies the excluded issue.",
                    "source_locator": "source.txt:1",
                    "source_anchor_quote_sha256": quote_digest,
                },
            },
        )
        messages = [finding.message for finding in findings]
        self.assertTrue(
            any("claim_bearing: false is permitted only" in message for message in messages),
            messages,
        )

class SemanticSurfaceInventoryTests(unittest.TestCase):
    def test_surface_contract_requires_structural_tokens_and_rejects_unknown_fields(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = Path(temp_dir) / "FixturePaper"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {
                            "source_claim": {
                                "source_kind": "theorem",
                                "statement": "Theorem: fixture source claim.",
                                "semantic_surface": {
                                    "schema": 1,
                                    "required_terms": ["SomePrimitive"],
                                    "forbidden_opaque_terms": ["OpaqueBundle"],
                                    "typoed_structural_requirement": ["∀"],
                                }
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            findings = source_manifest.semantic_surface_inventory_findings(paper, "formalized")

        messages = [finding.message for finding in findings]
        self.assertTrue(any("unknown field" in message for message in messages), messages)
        self.assertTrue(
            any("required_structural_tokens must be a nonempty" in message for message in messages),
            messages,
        )

    def test_schema_three_semantic_prerequisite_uses_its_explicit_root_not_a_contract(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = Path(temp_dir) / "FixturePaper"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_coverage_mode": "named_theoretical_statements",
                        "semantic_contract_schema": 1,
                        "semantic_route_schema": 2,
                        "items": {
                            "source_definition": {
                                "source_kind": "definition",
                                "claim_bearing": True,
                                "inventory_role": "source_semantic_declaration",
                                "lean_declarations": ["FixturePaper.SourceDefinition"],
                                "semantic_surface": {
                                    "schema": 3,
                                    "outer_binder_sha256": "0" * 64,
                                    "required_result_patterns": [
                                        {
                                            "id": "definition_shape",
                                            "relation": "iff",
                                            "all_features": ["finite"],
                                            "quantifier_shape": {"forall": 0, "exists": 0},
                                        }
                                    ],
                                },
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            findings = source_manifest.semantic_surface_inventory_findings(paper, "formalized")

        messages = [finding.message for finding in findings]
        self.assertFalse(
            any("needs an exact semantic_contract" in message for message in messages),
            messages,
        )


class ProducerIndependenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)

    def write(self, basename: str, payload: dict[str, object]) -> None:
        if (
            basename == "source_record_audit.json"
            and str(payload.get("prompt_version") or "").strip()
            == GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        ):
            complete_v10_source_record_scan_fixture(payload, paper=self.paper.name)
            stamp_source_record_audit_receipts(payload)
        (self.paper / "audit" / basename).write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def test_translator_and_producer_are_collected_as_identities(self) -> None:
        self.assertEqual(
            GATE.validators({"translator": "translator-a", "producer": "producer-b"}),
            {"translator-a", "producer-b"},
        )

    def test_translator_must_be_distinct_from_statement_judge(self) -> None:
        self.write(
            "lean_to_tex_llm.json",
            {"translator": "same-agent", "items": {"row": {}}},
        )
        self.write(
            "statement_match_llm.json",
            {"validator": "same-agent", "items": {"row": {}}},
        )
        findings = GATE.check_validator_independence(self.paper, "formalized")
        self.assertTrue(
            any("Lean translator and statement judge" in finding.message for finding in findings)
        )

        self.write(
            "statement_match_llm.json",
            {"validator": "different-agent", "items": {"row": {}}},
        )
        self.assertEqual(
            GATE.check_validator_independence(self.paper, "formalized"), []
        )

    def test_shared_identity_is_release_blocking_but_not_closeout_math_debt(self) -> None:
        self.write(
            "lean_to_tex_llm.json",
            {"translator": "same-agent", "items": {"row": {}}},
        )
        self.write(
            "statement_match_llm.json",
            {"validator": "same-agent", "items": {"row": {}}},
        )

        normal = GATE.check_validator_independence(self.paper, "formalized")
        release = GATE.check_validator_independence(
            self.paper, "formalized", release=True
        )

        self.assertEqual([finding.severity for finding in normal], ["WARN"])
        self.assertEqual([finding.severity for finding in release], ["ERROR"])
        self.assertIn("single-agent review evidence", normal[0].message)

    def test_source_curator_and_formalizer_are_pairwise_checked_when_recorded(self) -> None:
        self.write(
            "statement_match_llm.json",
            {"validator": "judge", "items": {"row": {}}},
        )
        self.write(
            "paper_coverage_llm.json",
            {"validator": "curator", "items": {"row": {}}},
        )
        self.write(
            "paper_statement_map.json",
            {"source_curator": "curator", "items": {"row": {}}},
        )
        (self.paper / "status.json").write_text(
            json.dumps({"formalizer": "judge"}), encoding="utf-8"
        )
        messages = [
            finding.message
            for finding in GATE.check_validator_independence(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any("source curator and coverage judge" in message for message in messages)
        )
        self.assertTrue(
            any("formalizer and statement judge" in message for message in messages)
        )

    def test_defect_support_judge_is_independent_from_coverage_judge(self) -> None:
        self.write(
            "paper_coverage_llm.json",
            {"validator": "same-agent", "items": {"row": {}}},
        )
        self.write(
            "defect_support_match_llm.json",
            {"validator": "same-agent", "items": {"judgment": {}}},
        )
        findings = GATE.check_validator_independence(self.paper, "formalized")
        self.assertTrue(
            any(
                "coverage judge and defect-support judge" in finding.message
                for finding in findings
            )
        )

    def test_all_five_recorded_roles_are_pairwise_disjoint(self) -> None:
        self.write(
            "lean_to_tex_llm.json",
            {"translator": "same", "items": {"row": {}}},
        )
        self.write(
            "statement_match_llm.json",
            {"validator": "same", "items": {"row": {}}},
        )
        self.write(
            "paper_coverage_llm.json",
            {"validator": "same", "items": {"row": {}}},
        )
        self.write(
            "paper_statement_map.json",
            {"source_curator": "same", "items": {"row": {}}},
        )
        (self.paper / "status.json").write_text(
            json.dumps({"formalizer": "same"}), encoding="utf-8"
        )
        findings = GATE.check_validator_independence(self.paper, "formalized")
        self.assertEqual(len(findings), 10)


class CoverageRowSignaturePinTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper = Path(self.temporary.name) / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)

    def write_coverage(self, pins: object) -> None:
        (self.paper / "audit" / "paper_coverage_llm.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": self.paper.name,
                    "prompt_version": GATE.PAPER_COVERAGE_ROW_SIGNATURE_PROMPT_VERSION,
                    "items": {
                        "source_claim": {
                            "coverage": "covered",
                            "review_rows": ["reviewed_row"],
                            "review_row_signature_sha256": pins,
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

    def test_v5_direct_coverage_requires_well_formed_exact_row_pin_map(self) -> None:
        self.write_coverage({})
        findings = GATE.coverage_row_signature_pin_findings(
            self.paper, "formalized"
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("keys do not exactly match review_rows", findings[0].message)
        self.assertIn("reviewed_row", findings[0].message)

        self.write_coverage({"reviewed_row": "a" * 64})
        self.assertEqual(
            GATE.coverage_row_signature_pin_findings(self.paper, "formalized"),
            [],
        )

    def test_selected_v11_lane_never_validates_legacy_coverage_pins(self) -> None:
        self.write_coverage({})

        findings = GATE.coverage_row_signature_pin_findings(
            self.paper,
            "formalized",
            context=SimpleNamespace(v11_lean_claim_graph_selected=True),
        )

        self.assertEqual(findings, [])


class SourceRecordJudgmentTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous_root = GATE.ROOT
        GATE.ROOT = self.root
        source_root_patch = patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, GATE, "ROOT", previous_root)
        identity_patch = patch.object(
            GATE, "source_record_current_input_fingerprint_error", return_value=""
        )
        identity_patch.start()
        self.addCleanup(identity_patch.stop)
        self.paper = self.root / "papers" / "FixturePaper"
        audit_dir = self.paper / "audit"
        audit_dir.mkdir(parents=True)
        statement_map_path = audit_dir / "paper_statement_map.json"
        statement_map_path.write_text("{}\n", encoding="utf-8")
        self.statement_map_digest = hashlib.sha256(
            statement_map_path.read_bytes()
        ).hexdigest()

    def write(self, basename: str, payload: dict[str, object]) -> None:
        if (
            basename == "source_record_audit.json"
            and str(payload.get("prompt_version") or "").strip()
            == GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        ):
            complete_v10_source_record_scan_fixture(payload, paper=self.paper.name)
            stamp_source_record_audit_receipts(payload)
        (self.paper / "audit" / basename).write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def source_record_item_digest(self, kind: str, key: str) -> str:
        return hashlib.sha256(f"{kind}:{key}".encode("utf-8")).hexdigest()

    def v10_source_record_audit(
        self,
        *,
        input_keys: tuple[str, ...] = (),
        field_keys: tuple[str, ...] = (),
        audit_digest: str = "current-digest",
    ) -> dict[str, object]:
        def item(kind: str, key: str) -> dict[str, object]:
            return {
                "judgment_key": key,
                "kind": kind,
                "source_record_item_digest_schema": (
                    GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                ),
                "source_record_item_semantic_id": self.source_record_item_digest(
                    kind + ":semantic", key
                ),
                "source_record_item_context_sha256": self.source_record_item_digest(
                    kind + ":context", key
                ),
                "source_record_item_sha256": self.source_record_item_digest(
                    kind, key
                ),
                "reviewed_elaborated_signature_identities": [
                    {
                        "qualified_declaration": "FixturePaper.PaperInterface.fixture_row",
                        "elaborated_signature_sha256": self.source_record_item_digest(
                            kind + ":elaborated", key
                        ),
                    }
                ],
                "source_record_item_reuse_eligibility": {
                    "eligible": True,
                    "blockers": [],
                },
            }

        return {
            "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
            "source_record_policy_version": (
                GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
            ),
            "source_record_audit_sha256": audit_digest,
            "paper_statement_map_sha256": self.statement_map_digest,
            "expected_input_judgment_keys": list(input_keys),
            "expected_field_judgment_keys": list(field_keys),
            "expected_semantic_model_judgment_keys": [],
            "boundary_input_items": [
                item("semantic_proposition_premise", key) for key in input_keys
            ],
            "conclusion_dependency_items": [],
            "recursive_field_items": [
                item("recursive_record_field", key) for key in field_keys
            ],
            "semantic_model_items": [],
        }

    def test_missing_configured_source_record_rows_are_errors_for_every_status(self) -> None:
        self.write(
            "source_record_audit.json",
            {
                "missing_configured_review_rows": [
                    "paper_source_statement",
                    "paper_algorithm_contract",
                ]
            },
        )

        findings = GATE.check_source_record_configured_rows(
            self.paper
        )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("audit coverage is incomplete", findings[0].message)
        self.assertIn("paper_algorithm_contract", findings[0].message)

    def test_plain_formalized_rejects_untagged_visible_premise_boundary(self) -> None:
        self.write(
            "paper_coverage_llm.json",
            {
                "items": {
                    "paper_row": {
                        "coverage": "conditional_boundary"
                    }
                }
            },
        )

        findings = GATE.check_status_alignment(self.paper, "formalized")

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("visible-premise/partial coverage row", findings[0].message)

    def test_plain_formalized_rejects_unpinned_formalized_note_boundary(self) -> None:
        self.write(
            "paper_coverage_llm.json",
            {
                "formalized_note_rows": ["paper_row"],
                "items": {
                    "paper_row": {
                        "coverage": "conditional_boundary"
                    }
                },
            },
        )
        self.write(
            "statement_match_llm.json",
            {
                "items": {
                    "paper_row": {
                        "judgment": "mismatch",
                        "resolution": "conditional_boundary",
                        "status_impact": "formalized_note",
                    }
                }
            },
        )

        findings = GATE.check_status_alignment(self.paper, "formalized")
        self.assertGreaterEqual(len(findings), 2)
        self.assertTrue(
            any("current approved source-convention receipt" in finding.message for finding in findings)
        )

    def test_plain_formalized_accepts_current_pinned_source_convention_note(self) -> None:
        source_item = {
            "source_kind": "theorem",
            "source_location": "source.txt:10-12",
            "statement": "The source theorem has the displayed conclusion.",
        }
        convention = {
            "id": "FIXTURE-SOURCE-CONVENTION-01",
            "source_locator": "source.txt:13-15",
            "classification": "human_verified_source_implicit",
            "formal_meaning": "The source model requires the displayed regularity for the endpoint variation.",
            "why_needed": "The Lean proof exposes that regularity as an input rather than inferring a result.",
            "checked_scope": "The review records only the model regularity and no theorem conclusion.",
        }
        source_semantic_sha256 = GATE.source_item_coverage_sha256(source_item, "")
        convention_id = convention["id"]
        receipt = {
            "source_target_disposition": "approved_source_convention",
            "source_statement_semantic_sha256": source_semantic_sha256,
            "source_statement_locator": source_item["source_location"],
            "model_convention_ids": [convention_id],
            "model_convention_sha256_by_id": {
                convention_id: GATE.model_convention_semantic_digest(convention)
            },
            "model_convention_source_locators": {
                convention_id: convention["source_locator"]
            },
        }
        self.write("paper_statement_map.json", {"items": {"source_row": source_item}})
        self.write("source_proof_fidelity.json", {"model_conventions": [convention]})
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "papers/FixturePaper/audit/source_proof_fidelity.json"
                        }
                    }
                }
            ),
            encoding="utf-8",
        )
        self.write(
            "paper_coverage_llm.json",
            {
                "formalized_note_rows": ["paper_row"],
                "items": {
                    "paper_row": {
                        "coverage": "covered_with_boundary",
                        "status_impact": "formalized_note",
                        **receipt,
                    }
                },
            },
        )
        self.write(
            "statement_match_llm.json",
            {
                "formalized_note_rows": ["paper_row"],
                "items": {
                    "paper_row": {
                        "judgment": "mismatch",
                        "resolution": "conditional_boundary",
                        "status_impact": "formalized_note",
                        "obligation_ledger_error": "",
                        "unmatched_source_conclusions": [],
                        "unmatched_source_inputs": [],
                        "unmatched_lean_conclusions": [],
                        "unjustified_lean_inputs": ["l_extra_premise"],
                        "obligation_alignment": [{"relation": "equivalent"}],
                        **receipt,
                    }
                },
            },
        )

        self.assertEqual(GATE.check_status_alignment(self.paper, "formalized"), [])

    def test_pinned_source_convention_note_cannot_waive_weakened_conclusion(self) -> None:
        source_item = {
            "source_kind": "theorem",
            "source_location": "source.txt:10-12",
            "statement": "The source theorem has the displayed conclusion.",
        }
        convention = {
            "id": "FIXTURE-SOURCE-CONVENTION-01",
            "source_locator": "source.txt:13-15",
            "classification": "human_verified_source_implicit",
            "formal_meaning": "The source model requires the displayed regularity for the endpoint variation.",
            "why_needed": "The Lean proof exposes that regularity as an input rather than inferring a result.",
            "checked_scope": "The review records only the model regularity and no theorem conclusion.",
        }
        convention_id = convention["id"]
        receipt = {
            "source_target_disposition": "approved_source_convention",
            "source_statement_semantic_sha256": GATE.source_item_coverage_sha256(source_item, ""),
            "source_statement_locator": source_item["source_location"],
            "model_convention_ids": [convention_id],
            "model_convention_sha256_by_id": {
                convention_id: GATE.model_convention_semantic_digest(convention)
            },
            "model_convention_source_locators": {
                convention_id: convention["source_locator"]
            },
        }
        self.write("paper_statement_map.json", {"items": {"source_row": source_item}})
        self.write("source_proof_fidelity.json", {"model_conventions": [convention]})
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "papers/FixturePaper/audit/source_proof_fidelity.json"
                        }
                    }
                }
            ),
            encoding="utf-8",
        )
        self.write(
            "statement_match_llm.json",
            {
                "formalized_note_rows": ["paper_row"],
                "items": {
                    "paper_row": {
                        "judgment": "mismatch",
                        "resolution": "conditional_boundary",
                        "status_impact": "formalized_note",
                        "obligation_ledger_error": "",
                        "unmatched_source_conclusions": ["s_result"],
                        "unmatched_source_inputs": [],
                        "unmatched_lean_conclusions": [],
                        "unjustified_lean_inputs": ["l_extra_premise"],
                        "obligation_alignment": [{"relation": "equivalent"}],
                        **receipt,
                    }
                },
            },
        )

        findings = GATE.check_status_alignment(self.paper, "formalized")
        self.assertTrue(
            any("non-premise semantic gap" in finding.message for finding in findings)
        )

    def test_formalized_note_cannot_waive_non_source_or_partial_assumption(self) -> None:
        for judgment in (
            "documented_additional_assumption",
            "partial_boundary",
            "not_paper_assumption",
        ):
            for status in ("formalized", "formalized with caveat"):
                with self.subTest(judgment=judgment, status=status):
                    self.write(
                        "assumption_match_llm.json",
                        {
                            "formalized_note_rows": ["assumption_row"],
                            "items": {
                                "assumption_row": {
                                    "judgment": judgment,
                                    "status_impact": "formalized_note",
                                }
                            },
                        },
                    )

                    findings = GATE.check_status_alignment(self.paper, status)

                    self.assertEqual(len(findings), 1)
                    self.assertIn("non-source/caveat assumption", findings[0].message)

        self.write(
            "assumption_match_llm.json",
            {
                "formalized_note_rows": ["source_convention"],
                "items": {
                    "source_convention": {
                        "judgment": "documented_caveat",
                        "status_impact": "formalized_note",
                    }
                },
            },
        )
        for status in ("formalized", "formalized with caveat"):
            with self.subTest(source_convention_status=status):
                self.assertEqual(GATE.check_status_alignment(self.paper, status), [])

    def test_retired_assumption_sidecar_rows_do_not_affect_current_closeout(self) -> None:
        """A canonical sidecar is current evidence, not historical premise debt."""

        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "assumption_names": ["active_source_condition"]
                    }
                }
            ),
            encoding="utf-8",
        )
        self.write(
            "assumption_match_llm.json",
            {
                "items": {
                    "retired_external_tail_boundary": {
                        "judgment": "partial_boundary"
                    },
                    "active_source_condition": {
                        "judgment": "paper_condition"
                    },
                }
            },
        )

        self.assertEqual(GATE.check_status_alignment(self.paper, "formalized"), [])

        sidecar_path = self.paper / "audit" / "assumption_match_llm.json"
        sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
        sidecar["items"]["active_source_condition"]["judgment"] = "partial_boundary"
        sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
        findings = GATE.check_status_alignment(self.paper, "formalized")
        self.assertEqual(len(findings), 1)
        self.assertIn("non-source/caveat assumption", findings[0].message)

    def test_explicitly_empty_assumption_surface_ignores_retired_sidecar_rows(self) -> None:
        (self.paper / "status.json").write_text(
            json.dumps({"review_surface": {"assumption_names": []}}),
            encoding="utf-8",
        )
        self.write(
            "assumption_match_llm.json",
            {
                "items": {
                    "retired_external_tail_boundary": {
                        "judgment": "partial_boundary"
                    }
                }
            },
        )

        self.assertEqual(GATE.check_status_alignment(self.paper, "formalized"), [])

    def test_explicit_source_routes_require_current_schema_two_semantic_model_evidence(self) -> None:
        status = {
            "review_surface": {
                "llm_statement_review": {
                    "require_explicit_source_routes": True
                }
            }
        }

        missing_config = GATE.explicit_source_route_semantic_model_findings(
            self.paper, "formalized", status
        )
        self.assertEqual(len(missing_config), 1)
        self.assertIn("semantic_model_review schema 2", missing_config[0].message)

        dimensions = sorted(GATE.SEMANTIC_MODEL_REVIEW_DIMENSIONS)
        status["review_surface"]["semantic_model_review"] = {
            "schema": 2,
            "required_dimensions": dimensions,
        }
        missing_audit = GATE.explicit_source_route_semantic_model_findings(
            self.paper, "formalized", status
        )
        self.assertEqual(len(missing_audit), 1)
        self.assertIn("requires a current generated", missing_audit[0].message)

        key = "semantic-model::paper_row"
        semantic_dimensions = [
            {
                "id": dimension,
                "detected_from_expanded_surface": (
                    dimension == "expanded_binders_and_domain"
                ),
            }
            for dimension in dimensions
        ]
        semantic_responses = {
            dimension: {
                "verdict": (
                    "matches_source_model"
                    if dimension == "expanded_binders_and_domain"
                    else "not_applicable"
                ),
                "source_locator": "source.tex:1-2",
                "semantic_comparison": "The source and expanded Lean surface preserve the recorded semantic domain.",
                "lean_evidence": "The generated expanded source-record surface was reviewed against the displayed source semantics.",
            }
            for dimension in dimensions
        }
        audit_payload = {
            "prompt_version": "source-record-v7-semantic-world-refinement",
            "source_record_audit_sha256": "current-digest",
            "expected_semantic_model_judgment_keys": [key],
            "semantic_model_items": [
                {
                    "judgment_key": key,
                    "dimensions": semantic_dimensions,
                }
            ],
        }
        match_payload = {
            "prompt_version": "source-record-v7-semantic-world-refinement",
            "source_record_audit_sha256": "current-digest",
            "validator": "judge",
            "validated_at": "2026-07-24T00:00:00Z",
            "items": {
                key: {
                    "classification": "semantic_model_review",
                    "semantic_model_dimensions": semantic_responses,
                }
            },
        }
        self.write("source_record_audit.json", audit_payload)
        self.write("source_record_match_llm.json", match_payload)

        stale_prompt = GATE.explicit_source_route_semantic_model_findings(
            self.paper, "formalized", status
        )
        self.assertEqual(len(stale_prompt), 1)
        self.assertIn("requires source-record prompt", stale_prompt[0].message)

        audit_payload["prompt_version"] = GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        audit_payload["paper_statement_map_sha256"] = self.statement_map_digest
        match_payload["prompt_version"] = GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        self.write("source_record_audit.json", audit_payload)
        match_payload["source_record_audit_sha256"] = audit_payload[
            "source_record_audit_sha256"
        ]
        self.write("source_record_match_llm.json", match_payload)

        self.assertEqual(
            GATE.explicit_source_route_semantic_model_findings(
                self.paper, "formalized", status
            ),
            [],
        )

        malformed_cases = {
            "duplicate_expected": (
                lambda payload: payload.update(
                    {"expected_semantic_model_judgment_keys": [key, key]}
                ),
                "nonempty unique expected",
            ),
            "blank_generated": (
                lambda payload: payload["semantic_model_items"].append(  # type: ignore[index]
                    {"judgment_key": "", "dimensions": semantic_dimensions}
                ),
                "semantic_model_items with nonempty unique",
            ),
            "duplicate_generated": (
                lambda payload: payload["semantic_model_items"].append(  # type: ignore[index]
                    {
                        "judgment_key": key,
                        "dimensions": semantic_dimensions,
                    }
                ),
                "semantic_model_items with nonempty unique",
            ),
        }
        for label, (mutate, expected_message) in malformed_cases.items():
            with self.subTest(label=label):
                malformed = json.loads(json.dumps(audit_payload))
                mutate(malformed)
                self.write("source_record_audit.json", malformed)
                findings = GATE.explicit_source_route_semantic_model_findings(
                    self.paper, "formalized", status
                )
                self.assertEqual(len(findings), 1)
                self.assertIn(expected_message, findings[0].message)

    def test_strict_v11_source_spec_contract_replaces_legacy_semantic_lane(self) -> None:
        """The v11 occurrence gate, not v10 aggregate coverage, is authoritative."""

        status = {
            "review_surface": {
                "llm_statement_review": {
                    "require_explicit_source_routes": True
                },
                "require_source_spec_correspondence": True,
            }
        }

        self.assertEqual(
            GATE.explicit_source_route_semantic_model_findings(
                self.paper, "formalized", status
            ),
            [],
        )

    def test_explicit_source_routes_honor_configured_source_record_paths(self) -> None:
        key = "semantic-model::paper_row"
        dimensions = sorted(GATE.SEMANTIC_MODEL_REVIEW_DIMENSIONS)
        semantic_dimensions = [
            {
                "id": dimension,
                "detected_from_expanded_surface": (
                    dimension == "expanded_binders_and_domain"
                ),
            }
            for dimension in dimensions
        ]
        semantic_responses = {
            dimension: {
                "verdict": (
                    "matches_source_model"
                    if dimension == "expanded_binders_and_domain"
                    else "not_applicable"
                ),
                "source_locator": "source.tex:1-2",
                "semantic_comparison": "The source and expanded Lean surface preserve the recorded semantic domain.",
                "lean_evidence": "The generated expanded source-record surface was reviewed against the displayed source semantics.",
            }
            for dimension in dimensions
        }
        status = {
            "review_surface": {
                "llm_statement_review": {
                    "require_explicit_source_routes": True
                },
                "semantic_model_review": {
                    "schema": 2,
                    "required_dimensions": dimensions,
                },
                "llm_source_record_review": {
                    "source_record_audit_file": "papers/FixturePaper/custom/source_record_audit.json",
                    "source_record_judgment_file": "papers/FixturePaper/custom/source_record_match_llm.json",
                },
            }
        }
        # A stale canonical copy must not substitute for the status-configured
        # source-record review artifacts.
        self.write(
            "source_record_audit.json",
            {"prompt_version": "source-record-v7-semantic-world-refinement"},
        )
        custom = self.paper / "custom"
        custom.mkdir()
        audit_payload = {
            "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
            "source_record_audit_sha256": "current-digest",
            "paper_statement_map_sha256": self.statement_map_digest,
            "expected_semantic_model_judgment_keys": [key],
            "semantic_model_items": [
                {
                    "judgment_key": key,
                    "dimensions": semantic_dimensions,
                }
            ],
        }
        match_payload = {
            "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
            "source_record_audit_sha256": "current-digest",
            "validator": "judge",
            "validated_at": "2026-07-24T00:00:00Z",
            "items": {
                key: {
                    "classification": "semantic_model_review",
                    "semantic_model_dimensions": semantic_responses,
                }
            },
        }
        complete_v10_source_record_scan_fixture(
            audit_payload, paper=self.paper.name
        )
        stamp_source_record_audit_receipts(audit_payload)
        match_payload["source_record_audit_sha256"] = audit_payload[
            "source_record_audit_sha256"
        ]
        (custom / "source_record_audit.json").write_text(
            json.dumps(audit_payload), encoding="utf-8"
        )
        (custom / "source_record_match_llm.json").write_text(
            json.dumps(match_payload), encoding="utf-8"
        )

        self.assertEqual(
            GATE.explicit_source_route_semantic_model_findings(
                self.paper, "formalized", status
            ),
            [],
        )

    def test_source_record_boundary_items_require_current_match_judgments(self) -> None:
        input_key = "row.h : SourceAssumption"
        field_key = "Model.hidden_field"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(
                input_keys=(input_key,), field_keys=(field_key,)
            ),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "old-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    input_key: {
                        "classification": "validated_source_assumption"
                    },
                    field_key: {
                        "classification": "validated_source_assumption"
                    }
                },
            },
        )

        findings = GATE.check_source_record_judgments(self.paper, "formalized")

        self.assertEqual(len(findings), 1)
        self.assertIn("2 required boundary/field/semantic-model item", findings[0].message)
        self.assertIn("2 lack current validated judgments", findings[0].message)
        self.assertEqual(findings[0].severity, "ERROR")

    def test_source_record_stale_judgments_are_warnings_for_partial_papers(self) -> None:
        input_key = "row.h : SourceAssumption"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(input_keys=(input_key,)),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "old-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {},
            },
        )

        findings = GATE.check_source_record_judgments(
            self.paper, "partially formalized"
        )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "WARN")

    def test_source_record_accepts_current_row_level_prompt_and_digest(self) -> None:
        input_key = "row.h : SourceAssumption"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(input_keys=(input_key,)),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "old-digest",
                "items": {
                    input_key: {
                        "classification": "validated_source_assumption",
                        "prompt_version": (
                            GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                        ),
                        "source_record_audit_sha256": "current-digest",
                        "validator": "judge",
                        "validated_at": "2026-07-10T00:00:00Z",
                        "source_record_item_digest_schema": (
                            GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                        ),
                        "source_record_item_sha256": self.source_record_item_digest(
                            "semantic_proposition_premise", input_key
                        ),
                    }
                },
            },
        )

        self.assertEqual(
            GATE.check_source_record_judgments(self.paper, "formalized"), []
        )

    def test_source_record_accepts_inputs_covered_by_current_statement_ledger(self) -> None:
        self.write(
            "source_record_audit.json",
            {
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "expected_input_judgment_keys": [
                    "row.hCovered : SourceAssumption",
                    "row.hSeparate : ModelAssumption",
                ],
                "expected_field_judgment_keys": ["Model.hidden_field"],
                "statement_ledger_covered_boundary_input_keys": [
                    "row.hCovered : SourceAssumption"
                ],
                "boundary_input_items": [
                    {"judgment_key": "row.hCovered : SourceAssumption"},
                    {"judgment_key": "row.hSeparate : ModelAssumption"},
                ],
                "recursive_field_items": [
                    {"judgment_key": "Model.hidden_field"}
                ],
            },
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-16T00:00:00Z",
                "items": {
                    "row.hCovered : SourceAssumption": {
                        "classification": "validated_source_assumption"
                    },
                    "row.hSeparate : ModelAssumption": {
                        "classification": "validated_source_assumption"
                    },
                    "Model.hidden_field": {
                        "classification": "validated_source_assumption"
                    },
                },
            },
        )

        self.assertEqual(
            GATE.check_source_record_judgments(self.paper, "formalized"), []
        )

    def test_source_record_accepts_current_item_digest_after_audit_digest_change(self) -> None:
        input_key = "row.h : SourceAssumption"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(
                input_keys=(input_key,), audit_digest="new-aggregate-digest"
            ),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "old-aggregate-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    input_key: {
                        "classification": "validated_source_assumption",
                        "source_record_item_digest_schema": (
                            GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                        ),
                        "source_record_item_sha256": self.source_record_item_digest(
                            "semantic_proposition_premise", input_key
                        ),
                    }
                },
            },
        )

        self.assertEqual(
            GATE.check_source_record_judgments(self.paper, "formalized"), []
        )

    def test_fast_gate_rejects_incomplete_semantic_model_judgment(self) -> None:
        key = "semantic-model::paper_row"
        self.write(
            "source_record_audit.json",
            {
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "expected_semantic_model_judgment_keys": [key],
                "semantic_model_items": [
                    {
                        "judgment_key": key,
                        "dimensions": [
                            {
                                "id": "joint_law_and_state_evolution",
                                "detected_from_expanded_surface": True,
                            }
                        ],
                    }
                ],
            },
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-24T00:00:00Z",
                "items": {key: {"classification": "validated_source_assumption"}},
            },
        )

        rejected = GATE.check_source_record_judgments(self.paper, "formalized")

        self.assertEqual(len(rejected), 1)
        self.assertIn(key, rejected[0].message)
        self.assertFalse(
            GATE.semantic_model_judgment_is_complete(
                {
                    "dimensions": [
                        {
                            "id": "carrier_and_domain",
                            "detected_from_expanded_surface": True,
                            "requires_checked_bridge_when_detected": True,
                        }
                    ]
                },
                {
                    "classification": "semantic_model_review",
                    "semantic_model_dimensions": {
                        "carrier_and_domain": {
                            "verdict": "matches_source_model",
                            "source_locator": "source.tex:12-18",
                            "semantic_comparison": "The opaque carrier is compared with the source carrier.",
                            "lean_evidence": "The local opaque type is visible in the review surface.",
                        }
                    },
                },
            )
        )

        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-24T00:00:00Z",
                "items": {
                    key: {
                        "classification": "semantic_model_review",
                        "semantic_model_dimensions": {
                            "joint_law_and_state_evolution": {
                                "verdict": "matches_source_model",
                                "source_locator": "source.tex:12-18",
                                "semantic_comparison": "The source state law is related to the reviewed joint law.",
                                "lean_evidence": "The generated expanded PMF surface is reviewed.",
                                "lean_bridge": "Fixture.source_state_to_joint_law",
                            }
                        },
                    }
                },
            },
        )

        self.assertEqual(
            GATE.check_source_record_judgments(self.paper, "formalized"), []
        )

        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": "source-record-v7-semantic-world-refinement",
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-24T00:00:00Z",
                "items": {
                    key: {
                        "classification": "semantic_model_review",
                        "semantic_model_dimensions": {
                            "joint_law_and_state_evolution": {
                                "verdict": "mismatch_or_open",
                                "source_locator": "source.tex:12-18",
                                "semantic_comparison": "The source state law has no proved bridge to the reviewed joint law.",
                                "lean_evidence": "The generated expanded PMF surface is reviewed.",
                                "lean_bridge": "Fixture.unresolved_state_to_joint_law",
                            }
                        },
                    }
                },
            },
        )

        open_findings = GATE.check_full_closeout_open_semantic_model_dimensions(
            self.paper, "formalized with caveat"
        )

        self.assertEqual(len(open_findings), 1)
        self.assertIn("mismatch_or_open", open_findings[0].message)

    def test_fast_gate_rejects_name_only_schema_two_probability_review(self) -> None:
        item = {
            "dimensions": [
                {
                    "id": "null_cell_totalization_and_partition_scope",
                    "detected_from_expanded_surface": True,
                    "expanded_shape_basis": ["expanded probability-law type surface"],
                    "requires_checked_bridge_when_detected": True,
                }
            ]
        }
        name_only_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {
                "null_cell_totalization_and_partition_scope": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.tex:20-27",
                    "semantic_comparison": "The exact source-key matches the partition name.",
                    "lean_evidence": "A matching function name provides the convention.",
                    "lean_bridge": "Fixture.partition_formula",
                }
            },
        }
        missing_basis_item = {
            "dimensions": [
                {
                    "id": "expectation_definedness",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": True,
                }
            ]
        }
        otherwise_complete_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {
                "expectation_definedness": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.tex:30-33",
                    "semantic_comparison": "The source and Lean compare the law, integrand, and integrability convention.",
                    "lean_evidence": "The expanded probability-law surface has an integrability proof.",
                    "lean_bridge": "Fixture.integrable_payoff",
                }
            },
        }

        self.assertFalse(
            GATE.semantic_model_judgment_is_complete(item, name_only_judgment)
        )
        self.assertFalse(
            GATE.semantic_model_judgment_is_complete(
                missing_basis_item, otherwise_complete_judgment
            )
        )

        parameter_translation_item = {
            "dimensions": [
                {
                    "id": "carrier_and_domain",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": True,
                    "requires_parameter_translation_when_detected": True,
                }
            ]
        }
        parameter_translation_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {
                "carrier_and_domain": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.tex:34-39",
                    "semantic_comparison": "The source has N candidates while the Lean carrier encodes the same finite domain.",
                    "lean_evidence": "The expanded carrier is Fin (n + 2).",
                    "lean_bridge": "Fixture.source_candidate_count_representation",
                }
            },
        }
        self.assertFalse(
            GATE.semantic_model_judgment_is_complete(
                parameter_translation_item, parameter_translation_judgment
            )
        )
        parameter_translation_judgment["semantic_model_dimensions"][
            "carrier_and_domain"
        ]["parameter_translation"] = (
            "The source parameter N is represented by Lean index n = N - 2, "
            "and the checked cardinality equality proves card (Fin (n + 2)) = N."
        )
        self.assertTrue(
            GATE.semantic_model_judgment_is_complete(
                parameter_translation_item, parameter_translation_judgment
            )
        )

    def test_fast_gate_requires_cardinality_and_transformed_law_subanalyses(self) -> None:
        item = {
            "dimensions": [
                {
                    "id": "carrier_and_domain",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": True,
                    "requires_cardinality_boundary_analysis_when_detected": True,
                },
                {
                    "id": "joint_law_and_state_evolution",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": True,
                    "requires_transformed_law_analysis_when_detected": True,
                    "requires_distribution_parameterization_analysis_when_detected": True,
                },
            ]
        }
        judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {
                "carrier_and_domain": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.tex:40-45",
                    "semantic_comparison": "The source and Lean carriers have the same finite domain.",
                    "lean_evidence": "The expanded Lean type is Fin (n + 2).",
                    "lean_bridge": "Fixture.finite_carrier_bridge",
                },
                "joint_law_and_state_evolution": {
                    "verdict": "matches_source_model",
                    "source_locator": "source.tex:46-54",
                    "semantic_comparison": "The source process is compared with the full joint law.",
                    "lean_evidence": "The expanded PMF model supplies the consumed probability law.",
                    "lean_bridge": "Fixture.source_to_joint_law",
                },
            },
        }
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))

        judgment["semantic_model_dimensions"]["carrier_and_domain"][
            "cardinality_boundary_analysis"
        ] = {
            "verdict": "threshold_checked",
            "source_cardinality_domain": "The source strict result assumes at least three candidates.",
            "lean_cardinality_domain": "Fin (n + 2) is used with n positive.",
            "boundary_cases_checked": "Two candidates are inspected as the excluded endpoint; three is the first case.",
            "strictness_witness_or_reason": "A distinct interior candidate witnesses the strict comparison at the stated threshold.",
            "lean_boundary_evidence": "The checked cardinality bridge converts n positive into the source lower bound.",
        }
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))

        judgment["semantic_model_dimensions"]["joint_law_and_state_evolution"][
            "transformed_law_analysis"
        ] = {
            "verdict": "transformed_law_checked",
            "source_operation": "The source scales independent noise before ranking it.",
            "lean_operation": "The Lean construction maps the product law through the same scaling map.",
            "parameter_domain_and_endpoints": "Positive scale is required; zero and negative scales are outside the probability-law statement.",
            "law_normalization_or_pushforward_evidence": "A checked change-of-variables/pushforward theorem supplies normalization and the transformed law.",
            "outcome_equivariance_or_no_relabeling_evidence": "Ranking cells are carried through the map, so the outcome event is preserved.",
            "lean_semantic_bridge": "The checked transport theorem relates the source operation and Lean outcome law.",
        }
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))

        parameterization = {
            "verdict": "proved_outcome_equivalence_after_translation",
            "source_parameterization": "The source draws unit-variance Laplace noise epsilon and uses epsilon / theta for theta positive.",
            "source_scale_or_variance": "The base Laplace noise has variance 1, so dividing by theta gives standard deviation 1 / theta.",
            "unit_normalization_evidence": "A checked second-moment theorem proves that the selected centered Laplace base law has variance 1.",
            "lean_parameterization": "The Lean distribution is parameterized by its Laplace rate r.",
            "lean_scale_or_variance": "A Laplace law with rate r has variance 2 / r^2, so its standard deviation is sqrt(2) / r.",
            "parameter_translation": "r = sqrt(2) * theta for every theta > 0.",
            "family_coupling_scope": "Both compared positive theta values arise from one shared unit-variance base noise law before scaling.",
            "family_coupling_evidence": "A checked density family equality transports the common base noise distribution to every Lean rate-r law.",
            "law_equivalence_evidence": "Positive reparameterization preserves the intended ranking conclusion.",
            "outcome_preservation_evidence": "The ranking event is unchanged after the translated score law is used.",
            "lean_semantic_bridge": "A checked density calculation and ranking-event transport identify the translated source law with the Lean PMF.",
        }
        judgment["semantic_model_dimensions"]["joint_law_and_state_evolution"][
            "distribution_parameterization_analysis"
        ] = parameterization
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))

        parameterization["law_equivalence_evidence"] = (
            "For r = sqrt(2) * theta, a checked density equality gives equality of "
            "the source scaled-noise law and the Lean rate-r law before ranking."
        )
        missing_coupling_evidence = parameterization.pop("family_coupling_evidence")
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))
        parameterization["family_coupling_evidence"] = missing_coupling_evidence
        missing_normalization_evidence = parameterization.pop("unit_normalization_evidence")
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))
        parameterization["unit_normalization_evidence"] = missing_normalization_evidence
        self.assertTrue(GATE.semantic_model_judgment_is_complete(item, judgment))

        parameterization["verdict"] = "mismatch_or_open"
        self.assertFalse(GATE.semantic_model_judgment_is_complete(item, judgment))

    def test_plain_formalized_rejects_current_unresolved_math_judgment(self) -> None:
        input_key = "row.local_interval_event_clauses"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(input_keys=(input_key,)),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    input_key: {
                        "classification": "unresolved_assumed_math",
                        "source_record_item_digest_schema": (
                            GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                        ),
                        "source_record_item_sha256": self.source_record_item_digest(
                            "semantic_proposition_premise", input_key
                        ),
                    }
                },
            },
        )

        findings = GATE.check_plain_formalized_unresolved_source_record_math(
            self.paper, "formalized"
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("plain `formalized` status conflicts", findings[0].message)
        self.assertIn("row.local_interval_event_clauses", findings[0].message)

    def test_non_plain_formalized_allows_visible_unresolved_math_judgment(self) -> None:
        self.write(
            "source_record_audit.json",
            {
                "prompt_version": "source-record-v4-name-invariant-signature-closure",
                "source_record_audit_sha256": "current-digest",
                "boundary_input_items": [
                    {"judgment_key": "row.local_interval_event_clauses"}
                ],
            },
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": "source-record-v4-name-invariant-signature-closure",
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    "row.local_interval_event_clauses": {
                        "classification": "unresolved_assumed_math"
                    }
                },
            },
        )

        self.assertEqual(
            GATE.check_plain_formalized_unresolved_source_record_math(
                self.paper, "paper draft"
            ),
            [],
        )

    def test_opt_in_source_obligation_tracker_reports_current_unresolved_math(self) -> None:
        input_key = "row.local_interval_event_clauses"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(input_keys=(input_key,)),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "current-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    input_key: {
                        "classification": "unresolved_assumed_math",
                        "source_record_item_digest_schema": (
                            GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                        ),
                        "source_record_item_sha256": self.source_record_item_digest(
                            "semantic_proposition_premise", input_key
                        ),
                    }
                },
            },
        )

        findings = GATE.check_current_unresolved_source_record_math(
            self.paper, "paper draft"
        )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "WARN")
        self.assertIn("row.local_interval_event_clauses", findings[0].message)

    def test_opt_in_source_obligation_tracker_ignores_stale_unresolved_math(self) -> None:
        input_key = "row.local_interval_event_clauses"
        self.write(
            "source_record_audit.json",
            self.v10_source_record_audit(input_keys=(input_key,)),
        )
        self.write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": "FixturePaper",
                "prompt_version": GATE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "old-digest",
                "validator": "judge",
                "validated_at": "2026-07-10T00:00:00Z",
                "items": {
                    input_key: {
                        "classification": "unresolved_assumed_math",
                        "source_record_item_digest_schema": (
                            GATE.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                        ),
                        "source_record_item_sha256": hashlib.sha256(
                            b"stale semantic item"
                        ).hexdigest(),
                    }
                },
            },
        )

        self.assertEqual(
            GATE.check_current_unresolved_source_record_math(
                self.paper, "paper draft"
            ),
            [],
        )

class CorrectedModelMultiScopeBindingsTests(unittest.TestCase):
    optional_model = "Fixture.OptionalModel"
    report_model = "Fixture.ReportRequiredModel"
    optional_target = "Fixture.PaperInterface.optional_result"
    report_target = "Fixture.PaperInterface.report_required_result"

    @classmethod
    def _field_item(cls, model: str, field: str) -> dict[str, object]:
        return {
            "judgment_key": field,
            "path": f"{model} -> {field}",
        }

    @classmethod
    def _target_item(cls, target: str, model: str, field: str) -> dict[str, object]:
        return {
            "qualified_declaration": target,
            "expanded_lean_surface": {
                "record_field_types": [{"path": f"{model} -> {field}"}]
            },
        }

    @classmethod
    def _two_model_audit(cls) -> dict[str, object]:
        optional_field = f"{cls.optional_model}.optional_condition"
        report_field = f"{cls.report_model}.report_condition"
        return {
            "recursive_field_items": [
                cls._field_item(cls.optional_model, optional_field),
                cls._field_item(cls.report_model, report_field),
            ],
            "semantic_model_items": [
                cls._target_item(
                    cls.optional_target, cls.optional_model, optional_field
                ),
                cls._target_item(
                    cls.report_target, cls.report_model, report_field
                ),
            ],
        }

    def test_multi_model_scope_unions_disjoint_target_roots(self) -> None:
        fields, errors = GATE.corrected_model_transitively_reachable_field_items(
            self._two_model_audit(),
            model_spec_declarations=[self.optional_model, self.report_model],
            target_model_spec_declarations={
                self.optional_target: self.optional_model,
                self.report_target: self.report_model,
            },
            target_result_declarations=[self.optional_target, self.report_target],
        )

        self.assertEqual(errors, [])
        self.assertEqual(
            set(fields),
            {
                f"{self.optional_model}.optional_condition",
                f"{self.report_model}.report_condition",
            },
        )

    def test_multi_model_scope_rejects_cross_mapped_target_root(self) -> None:
        _fields, errors = GATE.corrected_model_transitively_reachable_field_items(
            self._two_model_audit(),
            model_spec_declarations=[self.optional_model, self.report_model],
            target_model_spec_declarations={
                self.optional_target: self.report_model,
                self.report_target: self.optional_model,
            },
            target_result_declarations=[self.optional_target, self.report_target],
        )

        self.assertTrue(
            any("mapped governing model" in error for error in errors), errors
        )

    def test_multi_model_scope_requires_an_exact_target_map(self) -> None:
        bindings, errors = GATE.corrected_model_scope_model_bindings(
            {
                "model_spec_declarations": [
                    self.optional_model,
                    self.report_model,
                ],
                "target_model_spec_declarations": {
                    self.optional_target: self.optional_model,
                },
            },
            target_result_declarations=[
                self.optional_target,
                self.report_target,
            ],
        )

        self.assertIsNone(bindings)
        self.assertTrue(
            any("map exactly every target_result_declaration" in error for error in errors),
            errors,
        )

    def test_legacy_scalar_model_scope_remains_accepted(self) -> None:
        field = f"{self.optional_model}.optional_condition"
        fields, errors = GATE.corrected_model_transitively_reachable_field_items(
            {
                "recursive_field_items": [
                    self._field_item(self.optional_model, field)
                ],
                "semantic_model_items": [
                    self._target_item(
                        self.optional_target, self.optional_model, field
                    )
                ],
            },
            model_spec_declaration=self.optional_model,
            target_result_declarations=[self.optional_target],
        )

        self.assertEqual(errors, [])
        self.assertEqual(set(fields), {field})


if __name__ == "__main__":
    unittest.main()
