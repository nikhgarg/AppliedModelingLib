#!/usr/bin/env python3
"""Regression tests for normal/deep source-map integrity boundaries."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

import audit_evidence_integrity as integrity  # noqa: E402
from scripts import source_manifest_validation as source_manifest  # noqa: E402
import source_named_result_index  # noqa: E402


class EvidenceIntegrityScopeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.previous_root = integrity.ROOT
        integrity.ROOT = self.root
        source_root_patch = mock.patch.object(source_manifest, "ROOT", self.root)
        source_root_patch.start()
        self.addCleanup(source_root_patch.stop)
        self.addCleanup(setattr, integrity, "ROOT", self.previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.source = self.paper / "source.txt"
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "\n"
            "Figure 1 reports a numerical illustration.\n",
            encoding="utf-8",
        )

    def quote(self, line: int, end_line: int | None = None) -> dict[str, object]:
        final_line = end_line or line
        text = "\n".join(
            self.source.read_text(encoding="utf-8").splitlines()[
                line - 1 : final_line
            ]
        )
        return {
            "path": self.source.name,
            "line_start": line,
            "line_end": final_line,
            "quoted_text": text,
            "quoted_text_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        }

    def test_repaired_defect_route_preflight_is_json_only_and_exact(self) -> None:
        (self.paper / "status.json").write_text(
            json.dumps({"status": "formalized"}), encoding="utf-8"
        )
        source_map = {
            "semantic_contract_schema": 1,
            "items": {
                "theorem1": {
                    "semantic_contract": {
                        "spec_declaration": "FixturePaper.theorem1Spec",
                        "evidence_declaration": "FixturePaper.theorem1",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    }
                }
            },
        }
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(source_map), encoding="utf-8"
        )
        (self.audit / "source_proof_fidelity.json").write_text(
            json.dumps(
                {
                    "schema": 2,
                    "paper": "FixturePaper",
                    "defects": [
                        {"id": "FIX-1", "resolution": "repaired_in_lean"}
                    ],
                }
            ),
            encoding="utf-8",
        )

        missing = integrity.repaired_source_defect_route_preflight_findings(
            self.paper, "formalized"
        )
        self.assertEqual(len(missing), 1)
        self.assertIn("FIX-1", missing[0].message)

        source_map["items"]["theorem1"]["source_defect_ids"] = ["FIX-1"]
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(source_map), encoding="utf-8"
        )
        self.assertEqual(
            integrity.repaired_source_defect_route_preflight_findings(
                self.paper, "formalized"
            ),
            [],
        )

    def write_map(
        self,
        items: dict[str, object],
        *,
        mode: str | None = "named_theoretical_statements",
        semantic_contract_schema: bool = False,
        named_result_review_overrides: dict[str, object] | None = None,
    ) -> None:
        digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        effective_mode = mode or "named_theoretical_statements"
        presentations = source_named_result_index.extract_named_result_presentations(
            self.source.read_text(encoding="utf-8"),
            source_format="text",
        )
        receipt_presentations = [
            presentation
            for presentation in presentations
            if integrity.source_named_presentation_in_coverage_scope(
                presentation.kind, effective_mode
            )
        ]
        payload: dict[str, object] = {
            "source_artifact_path": self.source.name,
            "source_artifact_sha256": digest,
            "source_anchor_evidence_required": True,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "fixture-reviewer",
                "validated_at": "2026-07-26",
                "method": "fixture named-result source scan",
                "source_artifact_sha256": digest,
                "discovered_named_result_sha256": (
                    integrity.named_result_presentations_sha256(receipt_presentations)
                ),
                "prose_definition_presentations": [],
                "discovered_prose_definition_sha256": hashlib.sha256(
                    b"[]"
                ).hexdigest(),
            },
            "items": items,
        }
        if mode is not None:
            payload["source_coverage_mode"] = mode
        if named_result_review_overrides:
            review = payload["source_named_result_inventory_review"]
            assert isinstance(review, dict)
            review.update(named_result_review_overrides)
        if mode == "deep_paper_with_all_prose_claims":
            payload["source_prose_inventory_review"] = {
                "complete": True,
                "validator": "fixture-reviewer",
                "validated_at": "2026-07-26",
                "method": "fixture source screened in full",
                "source_artifact_sha256": digest,
            }
        if semantic_contract_schema:
            payload["semantic_contract_schema"] = 1
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def named_contract_item(self) -> dict[str, object]:
        return {
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:1",
            "source_anchor_evidence": [self.quote(1)],
            "semantic_contract": {
                "spec_declaration": "Fixture.sourceSpec",
                "evidence_declaration": "Fixture.sourceProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }

    def test_claim_atom_allows_canonical_text_beside_visual_transcription(self) -> None:
        """A raw atom remains valid when a visual transcript aids semantic review."""

        visual = self.paper / "visual-review.md"
        visual.write_text("Theorem 1. Gives the named result.\n", encoding="utf-8")
        raw_quote = "Theorem 1. Gives the named result."
        atom = {
            "id": "theorem1.result",
            "source_locator": "source.txt:1",
            "source_quote_sha256": hashlib.sha256(raw_quote.encode("utf-8")).hexdigest(),
            "semantic_claim": "The named result holds.",
            "reviewed_lean_route": "FixturePaper.theorem1",
            "identity_schema": 2,
        }
        self.assertEqual(
            integrity._source_claim_atoms_current_quote_binding_errors(
                self.paper,
                [atom],
                source_artifact_path=visual.name,
                source_artifact_sha256=hashlib.sha256(visual.read_bytes()).hexdigest(),
                alternate_source_artifact_path=self.source.name,
                alternate_source_artifact_sha256=hashlib.sha256(
                    self.source.read_bytes()
                ).hexdigest(),
            ),
            [],
        )

    def test_normal_scope_skips_deep_only_anchor_and_contract_obligations(self) -> None:
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "renamable_figure_item": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                    # Deliberately no anchor or semantic contract: a normal
                    # named-theory closeout must not become all-prose review.
                },
            },
            semantic_contract_schema=True,
        )

        self.assertEqual(
            source_manifest.check_source_manifest(self.paper, "formalized"), []
        )
        self.assertEqual(
            integrity.semantic_contract_inventory_findings(self.paper, "formalized"),
            [],
        )

    def test_repaired_defect_route_is_validated_without_expanding_paper_coverage(self) -> None:
        """A repair route cannot disappear behind normal presentation scope."""

        supporting_display = {
            "source_kind": "figure",
            "claim_bearing": True,
            "source_location": "source.txt:3",
            "source_anchor_evidence": [self.quote(3)],
            "source_defect_ids": ["FIX-REPAIR-1"],
            "semantic_contract": {
                "spec_declaration": "Fixture.repairSpec",
                "evidence_declaration": "Fixture.repairProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        self.write_map(
            {"non_named_repair_support": supporting_display},
            semantic_contract_schema=True,
        )
        (self.audit / "source_proof_fidelity.json").write_text(
            json.dumps(
                {
                    "defects": [
                        {
                            "id": "FIX-REPAIR-1",
                            "resolution": "repaired_in_lean",
                        }
                    ]
                }
            ),
            encoding="utf-8",
        )

        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        ordinary = integrity.filter_source_map_items_for_coverage(
            payload["items"], "named_theoretical_statements"
        )
        _scoped, integrity_items = source_manifest.scoped_source_map_payload(
            payload,
            "named_theoretical_statements",
            folder=self.paper,
            repository_root=integrity.ROOT,
        )

        self.assertNotIn("non_named_repair_support", ordinary)
        self.assertIn("non_named_repair_support", integrity_items)
        self.assertEqual(
            integrity.semantic_contract_inventory_findings(self.paper, "formalized"),
            [],
        )

    def test_approved_scope_exclusion_is_not_a_direct_route_obligation(self) -> None:
        """Its dedicated source validator remains responsible for the exclusion."""

        excluded_quote = self.quote(3)
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "approved_nonproof_item": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [excluded_quote],
                    "user_approved_scope_exclusion": {
                        "schema": 1,
                        "approval_kind": "explicit_user_instruction",
                        "approval_reference": "fixture scope decision",
                        "approved_at": "2026-08-14",
                        "reason": "The finite illustration is outside the requested theorem proofs.",
                        "source_locator": "source.txt:3",
                        "source_evidence": "The exact caption remains source-pinned.",
                        "source_anchor_quote_sha256": excluded_quote[
                            "quoted_text_sha256"
                        ],
                    },
                },
            },
            semantic_contract_schema=True,
        )
        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )

        _scoped, integrity_items = source_manifest.scoped_source_map_payload(
            payload,
            "named_theoretical_statements",
            folder=self.paper,
            repository_root=integrity.ROOT,
        )

        self.assertEqual(set(integrity_items), {"renamable_named_item"})
        self.assertEqual(
            source_manifest.user_approved_scope_exclusion_map_findings(
                self.paper,
                "formalized",
                self.audit / "paper_statement_map.json",
                payload,
            ),
            [],
        )

    def test_deep_scope_applies_anchor_and_contract_obligations_to_figure(self) -> None:
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "renamable_figure_item": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                },
            },
            mode="deep_paper_with_all_prose_claims",
            semantic_contract_schema=True,
        )

        anchor_messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        contract_messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any("source_anchor_evidence must be a nonempty list" in message for message in anchor_messages),
            anchor_messages,
        )
        self.assertTrue(
            any("lacks semantic_contract" in message for message in contract_messages),
            contract_messages,
        )

    def test_raw_nonobject_is_never_filtered_out(self) -> None:
        self.write_map({"renamable_bad_item": "not an object"})

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(any("not an object" in message for message in messages), messages)

    def test_source_presentation_conflict_is_never_filtered_out(self) -> None:
        self.write_map(
            {
                "renamable_conflict": {
                    "source_kind": "figure",
                    "claim_bearing": False,
                    "statement": "Theorem 1 gives the named result.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.quote(1)],
                }
            }
        )

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("conflicts with a named theoretical source presentation" in message for message in messages),
            messages,
        )

    def test_independent_named_result_index_rejects_an_omitted_theorem(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Figure 1 reports a numerical illustration.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # A source location on an out-of-scope presentation is not
                # allowed to make a discovered theorem disappear. Map/Lean
                # names are intentionally irrelevant to this assertion.
                "misleading_theorem_navigation": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:1",
                }
            }
        )

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]

        self.assertTrue(
            any("independent source named-result index found an uncovered theorem" in message for message in messages),
            messages,
        )

    def test_reviewed_material_candidate_is_a_normal_coverage_obligation(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Remark 4. The witness is unique under strict preferences.\n"
            "Note 5. This paragraph gives historical motivation only.\n",
            encoding="utf-8",
        )
        candidates = [
            {
                "schema": 1,
                "id": "remark4",
                "presentation_label": "Remark 4",
                "visible_kind": "remark",
                "scope_disposition": "material_named_claim",
                "semantic_basis": "This is a distinct mathematical conclusion.",
                "discovery_basis": "mechanical_labelled_heading",
                "source_anchor": self.quote(2),
            },
            {
                "schema": 1,
                "id": "note5",
                "presentation_label": "Note 5",
                "visible_kind": "note",
                "scope_disposition": "deep_audit_material",
                "semantic_basis": "This is historical motivation, not a paper claim.",
                "discovery_basis": "mechanical_labelled_heading",
                "source_anchor": self.quote(3),
            },
        ]
        inventory = integrity.reviewed_source_presentation_inventory(
            self.source.read_text(encoding="utf-8"),
            source_path=self.source.name,
            source_format="text",
            candidate_dispositions=candidates,
        )
        digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        review = {
            "schema": 1,
            "complete": True,
            "validator": "fixture-reviewer",
            "validated_at": "2026-08-28T12:00:00Z",
            "method": "source-only mechanical and holistic candidate review",
            "source_artifact_sha256": digest,
            "discovered_named_result_sha256": integrity.named_result_presentations_sha256(
                inventory.classified
            ),
            "candidate_presentations": candidates,
            "discovered_candidate_presentation_sha256": inventory.candidate_sha256,
            "prose_definition_presentations": [],
            "discovered_prose_definition_sha256": hashlib.sha256(b"[]").hexdigest(),
        }
        payload = {
            "source_artifact_path": self.source.name,
            "source_artifact_sha256": digest,
            "source_anchor_evidence_required": True,
            "source_coverage_mode": "named_theoretical_statements",
            "source_named_result_inventory_review": review,
            "items": {
                "theorem1": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.quote(1)],
                },
                "remark4": {
                    "source_kind": "claim",
                    "claim_bearing": True,
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [self.quote(2)],
                },
            },
        }
        map_path = self.audit / "paper_statement_map.json"
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        payload["items"].pop("remark4")
        messages = [
            finding.message
            for finding in source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            )
        ]
        self.assertTrue(
            any("uncovered claim presentation `Remark 4`" in message for message in messages),
            messages,
        )
        self.assertFalse(any("Note 5" in message for message in messages), messages)

    def test_source_index_anchor_selection_ignores_map_metadata_and_location(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 2. Every witness has the stated property.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # The map key, source kind, prose summary, and Lean route are
                # all deliberately non-theorem-like. Only the current exact
                # anchor may select this row for Theorem 1.
                "figure_navigation_key": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "statement": "Every admissible input has a witness.",
                    "lean_declarations": ["Fixture.figureCaption"],
                    "source_location": "source.txt:1-2",
                    "source_anchor_evidence": [self.quote(1)],
                }
            }
        )

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]

        self.assertFalse(
            any("uncovered theorem presentation `Theorem 1`" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("uncovered theorem presentation `Theorem 2`" in message for message in messages),
            messages,
        )

    def test_named_result_core_reconciliation_is_byte_pinned_and_source_only(self) -> None:
        self.source.write_text(
            "Theorem 1. Assume every input is admissible.\n"
            "Then every input has a witness.\n"
            "This paragraph gives intuition for the theorem.\n"
            "Theorem 2. Every witness is unique.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # Map key and Lean route deliberately conflict with the
                # presentation. The core's current source bytes decide it.
                "figure_navigation": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "source_location": "source.txt:1-3",
                    "source_anchor_evidence": [self.quote(1, 3)],
                    "lean_declarations": ["Fixture.unrelatedFigureRoute"],
                    "source_presentation_reconciliation": {
                        "schema": 1,
                        "relation": "conservative_text_span_core",
                        "presentation_kind": "theorem",
                        "presentation_label": "Theorem 1",
                        "core_anchor": self.quote(1, 2),
                        "boundary_reason": "completed_statement_then_explanation",
                        "semantic_basis": (
                            "The pinned multiline core contains the displayed "
                            "hypothesis and conclusion; line 3 is explanation."
                        ),
                        "validator": "fixture source-only reviewer",
                        "validated_at": "2026-07-28T12:00:00Z",
                    },
                },
                "second_navigation": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_location": "source.txt:4",
                    "source_anchor_evidence": [self.quote(4)],
                },
            }
        )
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        invalid = json.loads(json.dumps(payload))
        invalid["items"]["figure_navigation"][
            "source_presentation_reconciliation"
        ]["core_anchor"] = self.quote(1)
        messages = [
            finding.message
            for finding in source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, invalid
            )
        ]
        self.assertTrue(
            any("continuation" in message for message in messages),
            messages,
        )

    def test_normal_receipt_skips_standalone_display_but_reports_unclassified_named_presentation(
        self,
    ) -> None:
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "Formula 2. Gives a standalone display identity.\n"
            "Algorithm 3. Gives a standalone update procedure.\n"
            "Property 3. Requires source-specific presentation classification.\n",
            encoding="utf-8",
        )
        self.write_map({"named": self.named_contract_item()})

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]

        self.assertFalse(
            any("discovered_named_result_sha256 does not match" in message for message in messages),
            messages,
        )
        self.assertFalse(
            any("uncovered formula presentation" in message for message in messages),
            messages,
        )
        self.assertFalse(
            any("uncovered algorithm presentation" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("unclassified named presentation `Property 3`" in message for message in messages),
            messages,
        )

    def test_deep_receipt_reconciles_standalone_formula(self) -> None:
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "Formula 2. Gives a standalone display identity.\n",
            encoding="utf-8",
        )
        self.write_map(
            {"named": self.named_contract_item()},
            mode="deep_paper_with_all_prose_claims",
        )

        uncovered_messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("uncovered formula presentation" in message for message in uncovered_messages),
            uncovered_messages,
        )

        self.write_map(
            {
                "named": self.named_contract_item(),
                "formula": {
                    "source_kind": "formula",
                    "claim_bearing": True,
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [self.quote(2)],
                },
            },
            mode="deep_paper_with_all_prose_claims",
        )
        reconciled_messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertFalse(
            any("uncovered formula presentation" in message for message in reconciled_messages),
            reconciled_messages,
        )

    def test_explicit_corrected_target_remains_anchor_mandatory_in_normal_scope(self) -> None:
        self.write_map(
            {
                "renamable_correction": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "coverage_status": "corrected_source_statement",
                    "source_location": "source.txt:3",
                    "corrected_target": {},
                }
            }
        )

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("source_anchor_evidence must be a nonempty list" in message for message in messages),
            messages,
        )

    def test_closeout_requires_explicit_coverage_mode(self) -> None:
        self.write_map(
            {"renamable_named_item": self.named_contract_item()}, mode=None
        )

        closeout_messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        draft_messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "paper draft")
        ]
        self.assertTrue(
            any("must explicitly set source_coverage_mode" in message for message in closeout_messages),
            closeout_messages,
        )
        self.assertFalse(
            any("must explicitly set source_coverage_mode" in message for message in draft_messages),
            draft_messages,
        )

    def test_named_result_receipt_error_is_not_reported_twice(self) -> None:
        self.write_map({"renamable_named_item": self.named_contract_item()})
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload.pop("source_named_result_inventory_review")
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        receipt_messages = [
            message
            for message in messages
            if "source_named_result_inventory_review" in message
        ]
        self.assertEqual(len(receipt_messages), 1, messages)

    def test_partial_or_conditional_status_can_defer_named_result_receipt(self) -> None:
        """Only a full closeout claims a complete named-result inventory."""

        self.write_map({"renamable_named_item": self.named_contract_item()})
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload.pop("source_named_result_inventory_review")
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        for status in ("partially formalized", "conditional"):
            with self.subTest(status=status):
                self.assertEqual(
                    source_manifest.source_named_result_inventory_findings(
                        self.paper,
                        status,
                        map_path,
                        payload,
                    ),
                    [],
                )

        full_messages = [
            finding.message
            for finding in source_manifest.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            )
        ]
        self.assertTrue(
            any("source_named_result_inventory_review" in message for message in full_messages),
            full_messages,
        )

    def test_receipt_environment_alias_is_source_pinned_and_parser_validated(self) -> None:
        self.source = self.paper / "source.tex"
        self.source.write_text(
            "\\begin{customresult}\\label{custom:main}\n"
            "Every admissible input has a witness.\n"
            "\\end{customresult}\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                "opaque_navigation_key": {
                    "source_kind": "claim",
                    "claim_bearing": True,
                    "source_location": "source.tex:1-3",
                    "source_anchor_evidence": [self.quote(1, 3)],
                }
            },
            named_result_review_overrides={
                "environment_kinds": {"customresult": "claim"},
            },
        )
        # Updating the alias table changes the source-only index, so refresh
        # the receipt with the resulting presentation digest.
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        review["discovered_named_result_sha256"] = (
            integrity.named_result_presentations_sha256(
                source_named_result_index.extract_named_result_presentations(
                    self.source.read_text(encoding="utf-8"),
                    source_format="tex",
                    environment_kinds={"customresult": "claim"},
                )
            )
        )
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            ),
            [],
        )

        review["environment_kinds"] = {"customresult": "not_a_source_kind"}
        map_path.write_text(json.dumps(payload), encoding="utf-8")
        messages = [
            finding.message
            for finding in source_manifest.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            )
        ]
        self.assertEqual(
            len(
                [
                    message
                    for message in messages
                    if "presentation classification is invalid" in message
                ]
            ),
            1,
            messages,
        )

    def test_repeated_presentation_alias_requires_distinct_matching_source_pins(
        self,
    ) -> None:
        """Aliases reconcile source presentations, but cannot hide a new claim."""

        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 2. Every admissible input has two witnesses.\n",
            encoding="utf-8",
        )
        alias = {
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:2",
            "source_anchor_evidence": [self.quote(2)],
            "source_presentation_alias": {
                "schema": 1,
                "relation": "repeated_source_presentation",
                "canonical_source_item": "canonical_theorem_one",
                "semantic_basis": (
                    "The two pinned presentations have the same displayed "
                    "hypotheses, scope, and conclusion."
                ),
                "validator": "fixture source-only reconciliation",
                "validated_at": "2026-07-27T12:00:00Z",
            },
        }
        items = {
            "canonical_theorem_one": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:1",
                "source_anchor_evidence": [self.quote(1)],
            },
            "theorem_two": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:3",
                "source_anchor_evidence": [self.quote(3)],
            },
            "appendix_restatement": alias,
        }
        self.write_map(items)
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        with self.subTest("same_source_span_is_not_a_repeated_presentation"):
            invalid = json.loads(json.dumps(payload))
            invalid["items"]["appendix_restatement"]["source_anchor_evidence"] = [
                self.quote(1)
            ]
            messages = [
                finding.message
                for finding in source_manifest.source_named_result_inventory_findings(
                    self.paper, "formalized", map_path, invalid
                )
            ]
            self.assertTrue(
                any("must anchor a distinct source presentation" in message for message in messages),
                messages,
            )

        with self.subTest("cross_result_canonical_pin_is_rejected"):
            invalid = json.loads(json.dumps(payload))
            invalid["items"]["appendix_restatement"]["source_presentation_alias"][
                "canonical_source_item"
            ] = "theorem_two"
            messages = [
                finding.message
                for finding in source_manifest.source_named_result_inventory_findings(
                    self.paper, "formalized", map_path, invalid
                )
            ]
            self.assertTrue(
                any("does not preserve the canonical visible source result label" in message for message in messages),
                messages,
            )

    def test_explicitly_renumbered_restatement_requires_source_relation_evidence(
        self,
    ) -> None:
        """A different visible label is reusable only when source text says so."""

        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "We restate Theorem 1 formally as Theorem 2.\n"
            "Theorem 2. Every admissible input has a witness.\n",
            encoding="utf-8",
        )
        items = {
            "canonical_result": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:3",
                "source_anchor_evidence": [self.quote(3)],
            },
            "renumbered_restatement": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:1-2",
                "source_anchor_evidence": [self.quote(1, 2)],
                "source_presentation_alias": {
                    "schema": 1,
                    "relation": "repeated_source_presentation",
                    "canonical_source_item": "canonical_result",
                    "label_relation": "source_explicit_renumbered_restatement",
                    "source_restatement_evidence": self.quote(2),
                    "semantic_basis": (
                        "The source itself says that Theorem 2 restates Theorem 1."
                    ),
                    "validator": "fixture source-only reconciliation",
                    "validated_at": "2026-07-27T12:00:00Z",
                },
            },
        }
        self.write_map(items)
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        invalid = json.loads(json.dumps(payload))
        invalid["items"]["renumbered_restatement"][
            "source_presentation_alias"
        ]["source_restatement_evidence"] = self.quote(1)
        messages = [
            finding.message
            for finding in source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, invalid
            )
        ]
        self.assertTrue(
            any("does not materially state a restatement" in message for message in messages),
            messages,
        )

    def test_source_resolved_conjecture_requires_selected_named_result(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has two witnesses.\n"
            "Conjecture 1. Every admissible input has a witness.\n"
            "Theorem 1 proves this conjecture through a stronger result.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                "selected_result": self.named_contract_item(),
                "resolved_conjecture": {
                    "source_kind": "open_problem",
                    "claim_bearing": False,
                    "source_location": "source.txt:2-3",
                    "source_anchor_evidence": [self.quote(2, 3)],
                    "source_scope_classification": (
                        "source_resolved_within_paper_observation"
                    ),
                    "coverage_status": "subsumed_by_selected_result",
                    "protocol_role": "subsumed_by_selected_result",
                    "subsumed_by_source_item": "selected_result",
                    "scope_reason": (
                        "The paper proves the conjecture through its stronger theorem."
                    ),
                    "source_evidence": (
                        "Source lines 2-3 state the conjecture and its resolution by Theorem 1."
                    ),
                },
            },
            semantic_contract_schema=True,
        )
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        self.assertEqual(
            source_manifest.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )
        self.assertEqual(source_manifest.check_source_manifest(self.paper, "formalized"), [])
        self.assertEqual(
            integrity.semantic_contract_inventory_findings(self.paper, "formalized"),
            [],
        )
        self.assertEqual(
            integrity._semantic_contract_nonclaim_scope_error(
                self.paper,
                "formalized",
                map_path,
                payload,
                payload["items"]["resolved_conjecture"],
            ),
            "",
        )

        invalid_cases = (
            "missing_target",
            "unselected_target",
            "self_target",
            "cyclic_target",
            "support_only_target",
            "nonclaim_target",
            "unanchored_target",
            "unanchored_conjecture",
            "missing_reason",
            "missing_evidence",
            "unrelated_source_anchor",
            "duplicate_invalid_disposition",
            "malformed_resolved_policy",
        )
        for case in invalid_cases:
            with self.subTest(case):
                invalid = json.loads(json.dumps(payload))
                conjecture = invalid["items"]["resolved_conjecture"]
                target = invalid["items"]["selected_result"]
                if case == "missing_target":
                    conjecture["subsumed_by_source_item"] = "nonexistent_result"
                elif case == "unselected_target":
                    target.pop("semantic_contract")
                elif case == "self_target":
                    conjecture["subsumed_by_source_item"] = "resolved_conjecture"
                elif case == "cyclic_target":
                    target["subsumed_by_source_item"] = "resolved_conjecture"
                elif case == "support_only_target":
                    target["source_status"] = "support_only"
                elif case == "nonclaim_target":
                    target["claim_bearing"] = False
                elif case == "unanchored_target":
                    target.pop("source_anchor_evidence")
                elif case == "unanchored_conjecture":
                    conjecture.pop("source_anchor_evidence")
                elif case == "missing_reason":
                    conjecture.pop("scope_reason")
                elif case == "missing_evidence":
                    conjecture.pop("source_evidence")
                elif case == "unrelated_source_anchor":
                    conjecture["source_location"] = "source.txt:1"
                    conjecture["source_anchor_evidence"] = [self.quote(1)]
                elif case == "duplicate_invalid_disposition":
                    invalid["items"]["duplicate_disposition"] = dict(conjecture)
                    invalid["items"]["duplicate_disposition"][
                        "subsumed_by_source_item"
                    ] = "nonexistent_result"
                elif case == "malformed_resolved_policy":
                    conjecture["protocol_role"] = "source_declared_open"
                messages = [
                    finding.message
                    for finding in source_manifest.source_named_result_inventory_findings(
                        self.paper, "formalized", map_path, invalid
                    )
                ]
                self.assertTrue(
                    any(
                        "named open presentation" in message
                        or "source-resolved item" in message
                        for message in messages
                    ),
                    messages,
                )
                self.assertTrue(
                    integrity._semantic_contract_nonclaim_scope_error(
                        self.paper,
                        "formalized",
                        map_path,
                        invalid,
                        conjecture,
                    ),
                    case,
                )

        with self.subTest("partial_status_cannot_skip_resolved_validation"):
            invalid = json.loads(json.dumps(payload))
            invalid.pop("source_named_result_inventory_review")
            conjecture = invalid["items"]["resolved_conjecture"]
            conjecture["subsumed_by_source_item"] = "nonexistent_result"
            self.assertTrue(
                integrity._semantic_contract_nonclaim_scope_error(
                    self.paper, "partial", map_path, invalid, conjecture
                )
            )

    def test_named_open_problem_requires_explicit_nonproof_disposition(self) -> None:
        self.source.write_text(
            "Conjecture 1. Every admissible input has a witness.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                "opaque_source_navigation": {
                    "source_kind": "open_problem",
                    "claim_bearing": False,
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.quote(1)],
                    "source_scope_classification": (
                        "source_declared_open_nonresult_observation"
                    ),
                    "coverage_status": "source_declared_open",
                    "protocol_role": "source_declared_open",
                    "scope_reason": "The paper presents this as an open conjecture.",
                    "source_evidence": "Conjecture 1 in the source text.",
                }
            }
        )

        self.assertEqual(
            source_manifest.check_source_manifest(self.paper, "formalized"), []
        )

        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        item = payload["items"]["opaque_source_navigation"]
        assert isinstance(item, dict)
        item["claim_bearing"] = True
        map_path.write_text(json.dumps(payload), encoding="utf-8")
        messages = [
            finding.message
            for finding in source_manifest.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("named open presentation" in message for message in messages),
            messages,
        )


class HumanReviewMetadataTests(unittest.TestCase):
    def test_missing_or_malformed_claimed_counts_fail_closed(self) -> None:
        folder = Path("/tmp/Fixture")
        missing = integrity.check_human_review(
            folder,
            "formalized",
            {},
            False,
            review_log_present=False,
        )
        self.assertEqual(len(missing), 1)
        self.assertEqual(missing[0].severity, "ERROR")

        malformed = integrity.check_human_review(
            folder,
            "formalized",
            {
                "human_review": {
                    "reviewed_rows": True,
                    "total_rows": 1,
                    "stale_rows": 2,
                    "mismatch_rows": 0,
                }
            },
            False,
            review_log_present=False,
        )
        self.assertTrue(any("reviewed_rows" in item.message for item in malformed))

    def test_incomplete_human_review_remains_nonblocking(self) -> None:
        findings = integrity.check_human_review(
            Path("/tmp/Fixture"),
            "formalized",
            {
                "human_review": {
                    "reviewed_rows": 0,
                    "total_rows": 2,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                }
            },
            False,
            review_log_present=False,
        )
        self.assertEqual([item.severity for item in findings], ["WARN"])


class EvidenceIntegrityReceiptOrderingTests(unittest.TestCase):
    CURRENT_PREFIX_CHECKS = (
        "check_duplicate_sidecars",
        "check_placeholder_evidence",
        "check_full_closeout_assumption_alignment",
        "check_source_manifest",
        "semantic_contract_inventory_findings",
        "current_v11_source_route_findings",
        "source_proof_fidelity_findings",
    )
    LEGACY_PREFIX_CHECKS = tuple(
        name
        for name in CURRENT_PREFIX_CHECKS
        if name
        not in {
            "check_full_closeout_assumption_alignment",
            "current_v11_source_route_findings",
        }
    )
    LEGACY_ONLY_CHECKS = (
        "historical_statement_manifest_replay_evidence_findings",
        "coverage_row_signature_pin_findings",
        "corrected_target_coverage_findings",
        "check_status_alignment",
        "check_source_record_configured_rows",
        "check_source_premise_consistency",
        "check_source_record_judgments",
        "source_record_legacy_semantic_complement_findings",
        "explicit_source_route_semantic_model_findings",
        "check_plain_formalized_unresolved_source_record_math",
        "check_full_closeout_open_semantic_model_dimensions",
        "check_current_unresolved_source_record_math",
    )
    CURRENT_SUFFIX_CHECKS = (
        "check_validator_independence",
        "check_human_review",
        "check_vacuous_assumptions",
        "check_active_status",
        "check_build_coverage",
    )
    RUNNER_CHECKS = (
        *CURRENT_PREFIX_CHECKS,
        *LEGACY_ONLY_CHECKS,
        *CURRENT_SUFFIX_CHECKS,
    )

    def run_selected_context(
        self, context_type: type[integrity.EvidenceRunContext]
    ) -> list[str]:
        folder = Path("/tmp/Fixture").resolve()
        context = mock.Mock(spec=context_type)
        context.issued_by_builder = True
        context.folder = folder
        context.status = "formalized"
        context.status_payload = {}
        context.audit_config_snapshot = mock.Mock(payload={})
        context.json_snapshot.return_value = None
        context.corrected_scope_findings = ()
        called: list[str] = []

        def recorder(name: str) -> mock.Mock:
            return mock.Mock(
                side_effect=lambda *_args, **_kwargs: called.append(name) or []
            )

        with (
            mock.patch.object(integrity, "paper_dirs", return_value=[folder]),
            mock.patch.object(integrity, "check_report_generator", return_value=[]),
            mock.patch.object(
                integrity, "lake_targets", return_value=(set(), {"Fixture"})
            ),
            mock.patch.object(
                source_manifest,
                "source_proof_fidelity_findings",
                recorder("source_proof_fidelity_findings"),
            ),
            mock.patch.multiple(
                integrity,
                **{name: recorder(name) for name in self.RUNNER_CHECKS},
            ),
        ):
            findings = integrity._run_evidence_integrity(
                "Fixture",
                False,
                include_source_obligations=True,
                context=context,
                finalize_context=False,
                require_current_final_closure_receipt=False,
            )

        self.assertEqual(findings, [])
        return called

    def test_current_v11_runner_invokes_no_legacy_only_checks(self) -> None:
        self.assertEqual(
            self.run_selected_context(integrity.V11EvidenceRunContext),
            [*self.CURRENT_PREFIX_CHECKS, *self.CURRENT_SUFFIX_CHECKS],
        )

    def test_current_v11_evidence_conjunction_rejects_each_family(self) -> None:
        folder = Path("/tmp/Fixture").resolve()
        context = mock.Mock(spec=integrity.V11EvidenceRunContext)
        context.folder = folder
        context.status = "formalized"
        context.status_payload = {}
        context.json_snapshot.return_value = None
        checks = (*self.CURRENT_PREFIX_CHECKS, *self.CURRENT_SUFFIX_CHECKS)

        for failing_name in checks:
            with self.subTest(failing_name=failing_name):
                error = integrity.Finding(
                    "ERROR",
                    "Fixture",
                    f"audit/{failing_name}",
                    f"negative control for {failing_name}",
                )

                with mock.patch.multiple(
                    integrity,
                    **{
                        name: mock.Mock(
                            return_value=[error] if name == failing_name else []
                        )
                        for name in checks
                    },
                ), mock.patch.object(
                    source_manifest,
                    "source_proof_fidelity_findings",
                    return_value=(
                        [error]
                        if failing_name == "source_proof_fidelity_findings"
                        else []
                    ),
                ):
                    findings = integrity.current_v11_evidence_integrity_findings(
                        folder,
                        context,
                        release=False,
                        require_source_bytes=True,
                        active=set(),
                        defaults=set(),
                        libraries={"Fixture"},
                    )

                self.assertEqual(findings, [error])

    def test_legacy_runner_retains_all_historical_checks(self) -> None:
        self.assertEqual(
            self.run_selected_context(integrity.LegacyEvidenceRunContext),
            [
                *self.LEGACY_PREFIX_CHECKS,
                *self.LEGACY_ONLY_CHECKS,
                *self.CURRENT_SUFFIX_CHECKS,
            ],
        )

    def test_current_v11_skips_all_legacy_raw_semantic_complements(self) -> None:
        folder = Path("/tmp/Fixture")
        context = mock.Mock(spec=integrity.EvidenceRunContext)
        context.v11_lean_claim_graph_selected = True
        raw_validators = (
            "source_record_semantic_target_disposition_findings",
            "source_record_input_target_disposition_findings",
            "source_record_recursive_field_target_disposition_findings",
        )
        with mock.patch.multiple(
            integrity,
            **{
                name: mock.Mock(
                    side_effect=AssertionError(
                        "current v11 must not run legacy raw semantic complements"
                    )
                )
                for name in raw_validators
            },
        ):
            findings = integrity.source_record_legacy_semantic_complement_findings(
                folder,
                "formalized",
                context=context,
            )

        self.assertEqual(findings, [])

    def test_legacy_lane_runs_every_raw_semantic_complement(self) -> None:
        folder = Path("/tmp/Fixture")
        context = mock.Mock(spec=integrity.EvidenceRunContext)
        context.v11_lean_claim_graph_selected = False
        expected = [
            integrity.Finding("WARN", "Fixture", "target", "target"),
            integrity.Finding("WARN", "Fixture", "input", "input"),
            integrity.Finding("WARN", "Fixture", "field", "field"),
        ]
        with (
            mock.patch.object(
                integrity,
                "source_record_semantic_target_disposition_findings",
                return_value=[expected[0]],
            ) as target,
            mock.patch.object(
                integrity,
                "source_record_input_target_disposition_findings",
                return_value=[expected[1]],
            ) as input_route,
            mock.patch.object(
                integrity,
                "source_record_recursive_field_target_disposition_findings",
                return_value=[expected[2]],
            ) as recursive,
        ):
            findings = integrity.source_record_legacy_semantic_complement_findings(
                folder,
                "formalized",
                context=context,
            )

        self.assertEqual(findings, expected)
        target.assert_called_once_with(folder, "formalized", context=context)
        input_route.assert_called_once_with(folder, "formalized", context=context)
        recursive.assert_called_once_with(folder, "formalized", context=context)

    def test_standalone_audit_requires_current_canonical_receipt(self) -> None:
        with mock.patch.object(
            integrity, "_run_evidence_integrity", return_value=[]
        ) as internal:
            integrity.run("Fixture", False)

        self.assertTrue(
            internal.call_args.kwargs["require_current_final_closure_receipt"]
        )
        self.assertTrue(internal.call_args.kwargs["finalize_context"])

    def test_selected_v11_context_never_enters_legacy_raw_helpers(self) -> None:
        folder = Path("/tmp/Fixture")
        context = mock.Mock(spec=integrity.EvidenceRunContext)
        context.v11_lean_claim_graph_selected = True
        with (
            mock.patch.object(
                integrity,
                "load_json",
                side_effect=AssertionError("selected v11 reopened a legacy JSON path"),
            ),
            mock.patch.object(
                integrity,
                "v11_direct_semantic_review_state",
                side_effect=AssertionError("selected v11 re-ran lane success"),
            ),
        ):
            findings = [
                *integrity.check_source_record_configured_rows(
                    folder, context=context
                ),
                *integrity.check_source_premise_consistency(
                    folder, "formalized", context=context
                ),
                *integrity.check_source_record_judgments(
                    folder, "formalized", context=context
                ),
                *integrity.source_record_semantic_target_disposition_findings(
                    folder, "formalized", context=context
                ),
                *integrity.explicit_source_route_semantic_model_findings(
                    folder, "formalized", {}, context=context
                ),
                *integrity.check_plain_formalized_unresolved_source_record_math(
                    folder, "formalized", context=context
                ),
                *integrity.check_full_closeout_open_semantic_model_dimensions(
                    folder, "formalized", context=context
                ),
                *integrity.check_current_unresolved_source_record_math(
                    folder, "formalized with caveat", context=context
                ),
            ]

        self.assertEqual(findings, [])

    def test_selected_v11_duplicate_scan_ignores_legacy_carriers(self) -> None:
        folder = Path("/tmp/Fixture")
        context = mock.Mock(spec=integrity.EvidenceRunContext)
        context.v11_lean_claim_graph_selected = True

        def frozen_snapshot(path: Path) -> None:
            if path.name in integrity.V11_NONAUTHORITATIVE_LEGACY_SIDECARS:
                raise AssertionError("selected v11 inspected a legacy duplicate")
            return None

        context.json_snapshot.side_effect = frozen_snapshot

        self.assertEqual(
            integrity.check_duplicate_sidecars(
                folder, "formalized", context=context
            ),
            [],
        )

    def test_consolidated_closeout_defers_receipt_check_to_finalizer(self) -> None:
        context = mock.Mock(spec=integrity.EvidenceRunContext)
        with mock.patch.object(
            integrity, "_run_evidence_integrity", return_value=[]
        ) as internal:
            integrity.run_for_consolidated_closeout_transaction(
                "Fixture", False, context=context
            )

        self.assertFalse(
            internal.call_args.kwargs["require_current_final_closure_receipt"]
        )
        self.assertFalse(internal.call_args.kwargs["finalize_context"])

    def test_deferred_v11_evidence_rejects_missing_primary_gate_capability(
        self,
    ) -> None:
        context = mock.Mock(spec=integrity.V11EvidenceRunContext)
        context.folder = Path("/tmp/Fixture").resolve()
        error = integrity.Finding(
            "ERROR",
            "Fixture",
            "papers/Fixture/status.json",
            "current evidence gate requires the primary acceptance",
        )
        with mock.patch(
            "scripts.current_closeout.evidence_gate.run_current_evidence_gate",
            return_value=[error],
        ) as current_gate:
            findings = integrity.run_for_consolidated_closeout_transaction(
                "Fixture", False, context=context
            )

        self.assertEqual(findings, [error])
        current_gate.assert_called_once()

    def test_deferred_v11_evidence_accepts_primary_gate_capability(self) -> None:
        context = mock.Mock(spec=integrity.V11EvidenceRunContext)
        context.folder = Path("/tmp/Fixture").resolve()
        with mock.patch(
            "scripts.current_closeout.evidence_gate.run_current_evidence_gate",
            return_value=[],
        ) as current_gate:
            findings = integrity.run_for_consolidated_closeout_transaction(
                "Fixture", False, context=context
            )

        self.assertEqual(findings, [])
        current_gate.assert_called_once_with(
            repository_root=integrity.ROOT,
            paper_id="Fixture",
            release=False,
            require_source_bytes=True,
            diagnostics=None,
            context=context,
        )

    def test_deferred_v11_evidence_error_cannot_issue_capability(self) -> None:
        context = mock.Mock(spec=integrity.V11EvidenceRunContext)
        context.folder = Path("/tmp/Fixture").resolve()
        error = integrity.Finding(
            "ERROR",
            "Fixture",
            "papers/Fixture/audit/paper_statement_map.json",
            "source route is incomplete",
        )
        with mock.patch(
            "scripts.current_closeout.evidence_gate.run_current_evidence_gate",
            return_value=[error],
        ) as current_gate:
            findings = integrity.run_for_consolidated_closeout_transaction(
                "Fixture", False, context=context
            )

        self.assertEqual(findings, [error])
        current_gate.assert_called_once()

    def test_standalone_graph_credential_skips_legacy_evidence_replay(self) -> None:
        folder = Path("/tmp/Fixture")
        warning = integrity.Finding(
            "WARN",
            "Fixture",
            "papers/Fixture/status.json",
            "review remains pending",
        )
        with (
            mock.patch.object(integrity, "paper_dirs", return_value=[folder]),
            mock.patch.object(integrity, "check_report_generator", return_value=[]),
            mock.patch.object(integrity, "lake_targets", return_value=(set(), set())),
            mock.patch.object(
                integrity,
                "graph_native_closure_fast_path_findings",
                return_value=[warning],
            ) as graph_fast_path,
            mock.patch.object(integrity, "build_evidence_run_context") as build_context,
        ):
            findings = integrity._run_evidence_integrity(
                "Fixture",
                False,
                finalize_context=True,
                require_current_final_closure_receipt=True,
            )

        self.assertEqual(findings, [warning])
        graph_fast_path.assert_called_once_with(
            folder,
            release=False,
            require_source_bytes=True,
        )
        build_context.assert_not_called()

    def test_graph_credential_is_not_replaced_by_legacy_fallback_when_invalid(
        self,
    ) -> None:
        folder = Path("/tmp/Fixture")
        invalid = integrity.Finding(
            "ERROR",
            "Fixture",
            "papers/Fixture/FINAL_CLOSURE_RECEIPT.md",
            "canonical obligation-graph credential is invalid: stale source",
        )
        with (
            mock.patch.object(integrity, "paper_dirs", return_value=[folder]),
            mock.patch.object(integrity, "check_report_generator", return_value=[]),
            mock.patch.object(integrity, "lake_targets", return_value=(set(), set())),
            mock.patch.object(
                integrity,
                "graph_native_closure_fast_path_findings",
                return_value=[invalid],
            ),
            mock.patch.object(integrity, "build_evidence_run_context") as build_context,
        ):
            findings = integrity._run_evidence_integrity(
                "Fixture",
                False,
                finalize_context=True,
                require_current_final_closure_receipt=True,
            )

        self.assertEqual(findings, [invalid])
        build_context.assert_not_called()


if __name__ == "__main__":
    unittest.main()
