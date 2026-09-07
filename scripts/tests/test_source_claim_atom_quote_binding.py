#!/usr/bin/env python3
"""Regressions for byte-pinned strict source-claim atom receipts."""

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

from scripts import audit_evidence_integrity as integrity  # noqa: E402


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


class SourceClaimAtomQuoteBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        legacy_transition = mock.patch(
            "scripts.theorem_realization_transition.theorem_realization_reissue_requirement",
            return_value=mock.Mock(
                required=False,
                reason="unchanged legacy fixture",
            ),
        )
        legacy_transition.start()
        self.addCleanup(legacy_transition.stop)
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.paper = Path(self.temporary.name) / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.source_text = (
            "Theorem A states the complete source-facing equality.\n"
            "Its stated boundary condition is part of the same result.\n"
        )
        self.source = self.paper / "source.txt"
        self.source.write_text(self.source_text, encoding="utf-8")
        self.write_status("formalized")

    def write_status(
        self,
        status: str,
        *,
        requirement: object | None = None,
    ) -> None:
        review_surface: dict[str, object] = {}
        if requirement is not None:
            review_surface["require_source_spec_correspondence"] = requirement
        (self.paper / "status.json").write_text(
            json.dumps({"status": status, "review_surface": review_surface}),
            encoding="utf-8",
        )

    def atom(
        self,
        *,
        atom_id: str = "source-clause",
        route: str = "Fixture.Proof",
        locator: str = "source.txt:1-2",
        quote: str | None = None,
    ) -> dict[str, str]:
        if quote is None:
            quote = self.source_text.rstrip("\n")
        return {
            "id": atom_id,
            "source_locator": locator,
            "semantic_claim": (
                "For every admissible input, the complete displayed equality and "
                "its stated boundary condition hold."
            ),
            "reviewed_lean_route": route,
            "source_quote_sha256": sha256_text(quote),
        }

    def strict_payload(self, atom: dict[str, str] | None = None) -> dict[str, object]:
        raw_atom = atom or self.atom()
        atoms: list[dict[str, str]] = [raw_atom]
        contract: dict[str, str] = {
            "spec_declaration": "Fixture.SourceSpec",
            "evidence_declaration": "Fixture.Proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        component = sha256_text("fixture spec component")
        correspondence: dict[str, object] = {
            "schema": 1,
            "source_atoms_sha256": integrity.source_claim_atoms_semantic_sha256(atoms),
            "spec_closure_sha256": sha256_text("fixture closure"),
            "spec_surface_sha256": component,
            "closure_environment_sha256": sha256_text("fixture environment"),
            "source_atom_bindings": [
                {
                    "source_atom_sha256": integrity.source_claim_atom_semantic_sha256(
                        raw_atom
                    ),
                    "spec_component_sha256s": [component],
                    "semantic_bridge": (
                        "The complete source equality and stated boundary are "
                        "represented by the canonical Spec component."
                    ),
                }
            ],
            "closure_node_dispositions": [],
        }
        correspondence["item_identity_sha256"] = (
            integrity.source_spec_correspondence_item_identity_sha256(
                contract, correspondence
            )
        )
        return {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": sha256_bytes(self.source.read_bytes()),
            "source_claim_atoms_schema": 1,
            "source_spec_correspondence_schema": 1,
            "items": {
                "navigation_only_row_key": {
                    "claim_bearing": True,
                    "source_kind": "theorem",
                    "title": "Theorem A. Complete source-facing equality",
                    "statement": "Theorem A states the complete source-facing equality.",
                    "semantic_contract": contract,
                    "source_claim_atoms": atoms,
                    "source_spec_correspondence": correspondence,
                }
            },
        }

    def write_map(self, payload: object) -> None:
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def strict_messages(self) -> list[str]:
        return [
            finding.message
            for finding in integrity.source_spec_correspondence_inventory_findings(
                self.paper, "formalized"
            )
        ]

    def install_canonical_source_semantic_basis(
        self,
        payload: dict[str, object],
        *,
        artifact_path: str = "source.txt",
        source_locator: str = "source.txt:1-2",
    ) -> None:
        item = payload["items"]["navigation_only_row_key"]
        assert isinstance(item, dict)
        contract = item["semantic_contract"]
        correspondence = item["source_spec_correspondence"]
        assert isinstance(contract, dict)
        assert isinstance(correspondence, dict)
        correspondence["closure_node_dispositions"] = [
            {
                "closure_component_sha256": sha256_text(
                    "fixture supplemental closure component"
                ),
                "semantic_basis": {
                    "artifact_path": artifact_path,
                    "artifact_sha256": payload["source_artifact_sha256"],
                    "source_locator": source_locator,
                    "semantic_statement": (
                        "The canonical source theorem supplies the complete "
                        "supplemental mathematical basis for this closure node."
                    ),
                },
                "pinned_declaration_identity_sha256": sha256_text(
                    "fixture external declaration"
                ),
            }
        ]
        correspondence["item_identity_sha256"] = (
            integrity.source_spec_correspondence_item_identity_sha256(
                contract, correspondence
            )
        )

    def test_strict_atom_quote_is_accepted_only_for_the_current_canonical_slice(self) -> None:
        self.write_map(self.strict_payload())
        self.assertEqual(self.strict_messages(), [])

    def test_strict_atom_quote_uses_the_authenticated_visual_transcription(self) -> None:
        visual_text = "Theorem A states the visually checked equality.\n"
        visual = self.paper / "visual-review.md"
        primary_scan = self.paper / "visual-source.pdf"
        ocr_input = self.paper / "ocr-input.pdf"
        visual.write_text(visual_text, encoding="utf-8")
        primary_scan.write_bytes(b"%PDF-fixture-primary\n")
        ocr_input.write_bytes(b"%PDF-fixture-ocr\n")
        payload = self.strict_payload(
            self.atom(locator="visual-review.md:1", quote=visual_text.rstrip("\n"))
        )
        payload["source_text_companion"] = {
            "schema": 1,
            "canonical_text": {
                "path": "source.txt",
                "sha256": sha256_bytes(self.source.read_bytes()),
            },
            "visual_primary_scan": {
                "path": "visual-source.pdf",
                "sha256": sha256_bytes(primary_scan.read_bytes()),
            },
            "transcript_input_scan": {
                "path": "ocr-input.pdf",
                "sha256": sha256_bytes(ocr_input.read_bytes()),
            },
            "extraction": {"tool": "pdftotext", "options": ["-layout"]},
            "page_map": [
                {"line_start": 1, "line_end": 2, "pdf_page": 1, "printed_page": 1}
            ],
            "visual_comparison_attestation": {
                "complete": True,
                "method": "Checked the semantic transcription against the primary scan.",
            },
            "semantic_review_transcription": {
                "schema": 1,
                "path": "visual-review.md",
                "sha256": sha256_bytes(visual.read_bytes()),
                "controlling_visual_source": {
                    "path": "visual-source.pdf",
                    "sha256": sha256_bytes(primary_scan.read_bytes()),
                },
                "complete_for_selected_semantic_surface": True,
                "method": "Visually transcribed the selected theorem passage.",
            },
        }
        self.write_map(payload)
        self.assertEqual(self.strict_messages(), [])

    def test_strict_atom_quote_mismatch_is_rejected_even_with_a_fresh_correspondence_digest(
        self,
    ) -> None:
        stale = self.atom(quote="different source prose")
        self.write_map(self.strict_payload(stale))

        messages = self.strict_messages()
        self.assertTrue(
            any(
                "source_quote_sha256 does not match the exact current canonical source line slice"
                in message
                for message in messages
            ),
            messages,
        )

    def test_exact_clause_is_accepted_only_when_unique_in_current_quote(self) -> None:
        exact_clause = self.atom()
        exact_clause.update(
            {
                "identity_schema": 3,
                "verbatim_source_clause": (
                    "Its stated boundary condition is part of the same result."
                ),
            }
        )
        self.write_map(self.strict_payload(exact_clause))
        self.assertEqual(self.strict_messages(), [])

        absent_clause = dict(exact_clause)
        absent_clause["verbatim_source_clause"] = "A clause absent from the source."
        self.write_map(self.strict_payload(absent_clause))
        absent_messages = self.strict_messages()
        self.assertTrue(
            any(
                "verbatim_source_clause must occur exactly once" in message
                and "found 0 occurrence(s)" in message
                for message in absent_messages
            ),
            absent_messages,
        )

        repeated_clause = dict(exact_clause)
        repeated_clause["verbatim_source_clause"] = "the"
        self.write_map(self.strict_payload(repeated_clause))
        repeated_messages = self.strict_messages()
        self.assertTrue(
            any(
                "verbatim_source_clause must occur exactly once" in message
                and "found 2 occurrence(s)" in message
                for message in repeated_messages
            ),
            repeated_messages,
        )

    def test_strict_atom_quote_cannot_bind_a_different_paper_local_file(self) -> None:
        other = self.paper / "other.txt"
        other_quote = "A different local source file says something else."
        other.write_text(other_quote + "\n", encoding="utf-8")
        self.write_map(
            self.strict_payload(
                self.atom(locator="other.txt:1", quote=other_quote)
            )
        )

        messages = self.strict_messages()
        self.assertTrue(
            any(
                "must identify the canonical pinned source artifact" in message
                for message in messages
            ),
            messages,
        )

    def test_strict_inventory_rejects_missing_quote_and_stale_canonical_pin(self) -> None:
        missing_quote = self.atom()
        missing_quote.pop("source_quote_sha256")
        self.write_map(self.strict_payload(missing_quote))
        messages = self.strict_messages()
        self.assertTrue(
            any("source_quote_sha256 is required" in message for message in messages),
            messages,
        )

        missing_pin = self.strict_payload()
        missing_pin.pop("source_artifact_sha256")
        self.write_map(missing_pin)
        messages = self.strict_messages()
        self.assertTrue(
            any("lacks the top-level canonical source pin" in message for message in messages),
            messages,
        )

        payload = self.strict_payload()
        payload["source_artifact_sha256"] = "0" * 64
        self.write_map(payload)
        messages = self.strict_messages()
        self.assertTrue(
            any("source artifact SHA-256 mismatch" in message for message in messages),
            messages,
        )

    def test_structural_mode_warns_for_every_reference_to_absent_canonical_source(
        self,
    ) -> None:
        payload = self.strict_payload()
        self.install_canonical_source_semantic_basis(payload)
        self.write_map(payload)
        self.source.unlink()

        strict_messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any("does not name a local source file" in message for message in strict_messages),
            strict_messages,
        )
        self.assertTrue(
            any("must name an existing paper-local artifact" in message for message in strict_messages),
            strict_messages,
        )

        structural_findings = integrity.semantic_contract_inventory_findings(
            self.paper,
            "formalized",
            require_source_bytes=False,
        )
        structural_messages = [finding.message for finding in structural_findings]
        self.assertTrue(
            any(
                finding.severity == "WARN"
                and "source bytes are not provisioned" in finding.message
                for finding in structural_findings
            ),
            structural_messages,
        )
        self.assertFalse(
            any("does not name a local source file" in message for message in structural_messages),
            structural_messages,
        )
        self.assertFalse(
            any("source_artifact_path does not exist" in message for message in structural_messages),
            structural_messages,
        )
        self.assertFalse(
            any("must name an existing paper-local artifact" in message for message in structural_messages),
            structural_messages,
        )

    def test_structural_mode_warns_for_supplemental_source_but_rejects_unsafe_paths(
        self,
    ) -> None:
        payload = self.strict_payload()
        self.install_canonical_source_semantic_basis(
            payload,
            artifact_path="missing-supplement.txt",
            source_locator="missing-supplement.txt:1",
        )
        self.write_map(payload)
        self.source.unlink()

        messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper,
                "formalized",
                require_source_bytes=False,
            )
        ]
        self.assertTrue(
            any("semantic-basis source bytes are not provisioned" in message for message in messages),
            messages,
        )
        self.assertFalse(
            any("must name an existing paper-local artifact" in message for message in messages),
            messages,
        )

        self.source.write_text(self.source_text, encoding="utf-8")
        unsafe = self.strict_payload(
            self.atom(locator="../outside.txt:1", quote="outside source text")
        )
        self.write_map(unsafe)
        self.source.unlink()
        unsafe_messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper,
                "formalized",
                require_source_bytes=False,
            )
        ]
        self.assertTrue(
            any("escapes the paper folder" in message for message in unsafe_messages),
            unsafe_messages,
        )

    def test_structural_mode_still_rejects_present_mismatched_canonical_bytes(self) -> None:
        payload = self.strict_payload()
        payload["source_artifact_sha256"] = "0" * 64
        self.write_map(payload)

        messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper,
                "formalized",
                require_source_bytes=False,
            )
        ]
        self.assertTrue(
            any("source artifact SHA-256 mismatch" in message for message in messages),
            messages,
        )

    def test_quote_receipt_identity_is_independent_of_navigation_names(self) -> None:
        first = self.atom(atom_id="old-source-id", route="Old.Namespace.Proof")
        second = self.atom(atom_id="new-source-id", route="New.Namespace.Proof")
        self.assertEqual(
            integrity.source_claim_atom_semantic_sha256(first),
            integrity.source_claim_atom_semantic_sha256(second),
        )

    def test_legacy_atom_inventory_does_not_require_quote_data(self) -> None:
        legacy = self.atom()
        legacy.pop("source_quote_sha256")
        payload = self.strict_payload(legacy)
        payload.pop("source_spec_correspondence_schema")
        item = payload["items"]["navigation_only_row_key"]
        assert isinstance(item, dict)
        item.pop("source_spec_correspondence")
        self.write_map(payload)

        self.assertEqual(
            integrity.source_claim_atom_inventory_findings(self.paper, "formalized"),
            [],
        )
        self.assertEqual(self.strict_messages(), [])

    def test_future_requirement_is_quiet_before_closeout_but_missing_map_fails_at_closeout(
        self,
    ) -> None:
        self.write_status("not started", requirement=True)
        self.assertEqual(
            integrity.source_spec_correspondence_inventory_findings(
                self.paper, "not started"
            ),
            [],
        )

        self.write_status("formalized", requirement=True)
        messages = self.strict_messages()
        self.assertTrue(
            any(
                "requires source_spec_correspondence_schema" in message
                and "missing or invalid" in message
                for message in messages
            ),
            messages,
        )

    def test_malformed_requirement_switch_is_reported_even_before_closeout(self) -> None:
        self.write_status("not started", requirement="yes")
        messages = [
            finding.message
            for finding in integrity.source_spec_correspondence_inventory_findings(
                self.paper, "not started"
            )
        ]
        self.assertTrue(
            any("must be Boolean when declared" in message for message in messages),
            messages,
        )

    def test_closeout_requirement_reports_a_non_object_canonical_map(self) -> None:
        self.write_status("formalized", requirement=True)
        self.write_map(["not", "a", "source-map-object"])

        messages = self.strict_messages()
        self.assertTrue(
            any(
                "requires source_spec_correspondence_schema" in message
                and "missing or invalid" in message
                for message in messages
            ),
            messages,
        )


if __name__ == "__main__":
    unittest.main()
