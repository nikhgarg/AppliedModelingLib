"""Frozen route preflight has one current owner and no legacy acquisition."""

from __future__ import annotations

import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import source_manifest_validation as source
from scripts.current_closeout import primary_gate_transaction as gate
from scripts.current_closeout import runtime_api
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    EvidenceJSONSnapshot,
    Finding,
)


class CurrentRoutePreflightTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.folder = self.root / "papers" / "Fixture"
        self.folder.mkdir(parents=True)
        self.item = {"claim_bearing": True, "source_claim_atoms": []}
        self.map = {"items": {"claim": self.item}}
        self.context = CommonEvidenceRunContextInputs(
            folder=self.folder,
            status="formalized",
            audit_config_snapshot=EvidenceJSONSnapshot(
                self.root / "papers" / "audit_config.json", "a" * 64, {}, b"{}"
            ),
            status_snapshot=EvidenceJSONSnapshot(
                self.folder / "status.json", "b" * 64,
                {"status": "formalized"}, b"{}",
            ),
            statement_map_snapshot=EvidenceJSONSnapshot(
                self.folder / "audit" / "paper_statement_map.json", "c" * 64,
                self.map, b"{}",
            ),
            source_proof_fidelity_snapshot=None,
            sidecar_snapshots=(),
            source_proof_fidelity_path_error="",
        ).issue_v11(None)

    def test_runtime_has_no_route_preflight_forwarder(self) -> None:
        self.assertFalse(hasattr(runtime_api, "paper_closeout_fast_route_schema_findings"))

    def test_foreign_or_copied_context_stops_before_all_checks(self) -> None:
        for context, folder in (
            (object(), self.folder),
            (replace(self.context), self.folder),
            (self.context, self.folder.with_name("Other")),
        ):
            with self.subTest(context=type(context), folder=folder), mock.patch.object(
                gate, "current_source_spec_correspondence_inventory_findings",
                side_effect=AssertionError("invalid context reached source checks"),
            ):
                findings = gate.current_route_schema_preflight_findings(
                    self.root, folder, context=context
                )
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].severity, "ERROR")
            self.assertIn("exact builder-issued", findings[0].message)

    def test_complete_preflight_preserves_source_and_configuration_conjunction(self) -> None:
        duplicate = Finding("ERROR", "Fixture", "audit/source.json", "source defect")
        primary = SimpleNamespace(
            configuration_errors=("configuration defect",),
            structure_errors=("structure defect",),
            semantic_errors=("later semantic acceptance",),
            proof_errors=("later proof acceptance",),
            axiom_errors=("later axiom acceptance",),
        )
        with (
            mock.patch.object(gate, "current_source_spec_correspondence_inventory_findings",
                              return_value=[duplicate]) as correspondence,
            mock.patch.object(source, "repaired_source_defect_route_preflight_findings",
                              return_value=[duplicate]) as repaired,
            mock.patch.object(source, "source_proof_fidelity_findings",
                              return_value=[Finding("ERROR", "Fixture", "audit/fidelity.json",
                                                    "fidelity defect")]) as fidelity,
            mock.patch.object(gate, "current_v11_primary_gate_result", return_value=primary),
        ):
            findings = gate.current_route_schema_preflight_findings(
                self.root, self.folder, context=self.context
            )
        self.assertEqual(len(findings), 4)
        self.assertTrue(all(Path(finding.path).is_absolute() for finding in findings))
        self.assertFalse(any("later" in finding.message for finding in findings))
        correspondence.assert_called_once_with(
            self.root, self.folder, context=self.context, require_source_bytes=False
        )
        repaired.assert_called_once_with(self.folder, "formalized", context=self.context)
        fidelity.assert_called_once_with(
            self.folder, "formalized", self.context.status_payload,
            require_source_bytes=False, context=self.context,
        )

    def _correspondence(self, *, receipts=None, errors=(), source_current=False,
                        quote_errors=(), retained_error=None):
        surface = SimpleNamespace(
            declaration_inventory={"typed": "Lean-owned inventory"},
            paper_semantic_targets={}, library_semantic_targets={},
        )
        semantic = SimpleNamespace(
            semantic_review_current=True, surface=surface, findings=(), selection_error=""
        )
        with (
            mock.patch.object(source, "source_spec_correspondence_inventory_inputs",
                              return_value=([], self.map, [("claim", self.item)], source_current)),
            mock.patch.object(source, "source_claim_atoms_validation_errors", return_value=[]),
            mock.patch.object(source, "_source_claim_atoms_current_quote_binding_errors",
                              return_value=list(quote_errors)) as quotes,
            mock.patch.object(gate, "current_v11_semantic_review_result", return_value=semantic),
            mock.patch.object(gate, "builder_issued_v11_lean_review_surface",
                              return_value=surface, side_effect=retained_error),
            mock.patch.object(gate, "graph_context_input_sha256", return_value="d" * 64),
            mock.patch.object(gate, "graph_native_realization_receipts_from_inventory",
                              return_value=(receipts or {}, list(errors))) as realization,
        ):
            findings = gate.current_source_spec_correspondence_inventory_findings(
                self.root, self.folder, context=self.context, require_source_bytes=False
            )
        if retained_error is not None:
            realization.assert_not_called()
        else:
            self.assertEqual(realization.call_args.kwargs["inventory"], surface.declaration_inventory)
        return findings, quotes

    def test_retained_graph_cannot_omit_selected_realization(self) -> None:
        findings, _ = self._correspondence()
        self.assertEqual(len(findings), 1)
        self.assertIn("different realization surface: claim", findings[0].message)

    def test_retained_graph_errors_are_not_replaced_by_missing_receipt_noise(self) -> None:
        findings, _ = self._correspondence(errors=("proof endpoint is not its Spec",))
        self.assertEqual([f.message for f in findings], ["proof endpoint is not its Spec"])

    def test_retained_graph_validator_remains_mandatory(self) -> None:
        findings, _ = self._correspondence(
            retained_error=ValueError("retained v11 Lean review surface has no build provider")
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("realization graph is unavailable", findings[0].message)
        self.assertIn("no build provider", findings[0].message)

    def test_exact_source_atom_quotes_remain_required(self) -> None:
        findings, quotes = self._correspondence(
            receipts={"claim": {}}, source_current=True,
            quote_errors=("source-claim atom quote is stale",),
        )
        quotes.assert_called_once()
        self.assertEqual([f.message for f in findings],
                         ["items.claim: source-claim atom quote is stale"])

    def test_unavailable_source_pin_does_not_claim_quote_certification(self) -> None:
        findings, quotes = self._correspondence(receipts={"claim": {}})
        quotes.assert_not_called()
        self.assertEqual(findings, [])

    def test_source_correspondence_rejects_unissued_context_before_graph_work(self) -> None:
        with mock.patch.object(gate, "current_v11_semantic_review_result",
                               side_effect=AssertionError("unissued context reached graph")):
            findings = gate.current_source_spec_correspondence_inventory_findings(
                self.root, self.folder, context=replace(self.context)
            )
        self.assertEqual(len(findings), 1)
        self.assertIn("exact builder-issued", findings[0].message)

    def test_current_graph_requires_a_readable_map_without_legacy_switch(self) -> None:
        with (
            mock.patch.object(source, "transaction_json", return_value=None),
            mock.patch.object(gate, "current_v11_semantic_review_result",
                              side_effect=AssertionError("missing map reached graph")),
        ):
            findings = gate.current_source_spec_correspondence_inventory_findings(
                self.root, self.folder, context=self.context
            )
        self.assertEqual(len(findings), 1)
        self.assertIn("canonical source map is missing or invalid", findings[0].message)

    def test_historical_correction_reader_is_lazy(self) -> None:
        corrections = mock.Mock(side_effect=AssertionError("absent ledger acquired corrections"))
        with (
            mock.patch.object(source, "source_proof_fidelity_config", return_value=None),
            mock.patch.object(source, "source_proof_fidelity_requirement_reasons", return_value=()),
        ):
            findings = source.source_proof_fidelity_ledger_findings(
                self.folder, "formalized", {}, corrected_scope_findings=corrections
            )
        self.assertEqual(findings, [])
        corrections.assert_not_called()


if __name__ == "__main__":
    unittest.main()
