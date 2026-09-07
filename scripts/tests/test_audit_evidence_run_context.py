#!/usr/bin/env python3
"""Tests for run-scoped evidence reuse and exact mutation detection."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import fields, replace
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as evidence
from scripts import source_manifest_validation as source_manifest
from scripts import audit_repository
from scripts import source_record_differential_revalidation as differential
from scripts.configured_assumption_formalization_regularities import (
    CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD,
)
from scripts.current_closeout import (
    evidence_acceptance,
    evidence_transaction,
    graph_preparation,
    review_surface,
)
from scripts.current_closeout import lean_review_graph as graph_contract


class EvidenceRunContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "Fixture"
        self.audit_dir = self.paper / "audit"
        self.audit_dir.mkdir(parents=True)
        self._write_json(self.paper / "status.json", {"status": "formalized"})
        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "a" * 64,
                "nested": {"rows": ["content-addressed-obligation"]},
            },
        )
        self._write_json(
            self.audit_dir / "source_record_match_llm.json", {"items": {}}
        )
        self._write_json(
            self.audit_dir / "paper_statement_map.json", {"items": {}}
        )

    @staticmethod
    def _write_json(path: Path, payload: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

    def test_foundation_frontier_failure_names_bounded_unknown_roots(self) -> None:
        occurrences = [
            {
                "declaration": f"External.Package.declaration{index:02d}",
                "module": "External.Package.Module",
                "package_root": "",
                "declaration_kind": "definition",
            }
            for index in range(10)
        ]
        preview = {
            "specifications": [
                {
                    "specification": "Fixture.claimSpec",
                    "unregistered_external_occurrences": occurrences,
                },
                {
                    "specification": "Fixture.otherSpec",
                    "unregistered_external_occurrences": occurrences[:1],
                },
            ]
        }

        diagnostic = graph_contract.foundation_frontier_unregistered_diagnostic(
            preview,
            expected_count=10,
        )

        self.assertIn("found 10 material declaration(s)", diagnostic)
        self.assertIn("External.Package.declaration00", diagnostic)
        self.assertIn("External.Package.declaration07", diagnostic)
        self.assertNotIn("External.Package.declaration08", diagnostic)
        self.assertIn("... 2 more", diagnostic)
        self.assertRegex(diagnostic, r"diagnostic_sha256=[0-9a-f]{64}$")

    def test_foundation_frontier_failure_rejects_inconsistent_detail(self) -> None:
        diagnostic = graph_contract.foundation_frontier_unregistered_diagnostic(
            {"specifications": []},
            expected_count=1,
        )
        self.assertEqual(
            diagnostic,
            "Lean foundation-frontier preview has inconsistent unregistered "
            "root detail (summary=1, rows=0)",
        )

    def _build_context(
        self,
        diagnostics: dict[str, int] | None = None,
        *,
        identity_error: str = "",
    ) -> tuple[evidence.EvidenceRunContext, tuple[mock.Mock, ...]]:
        identity = mock.Mock(return_value=identity_error)
        corrected = mock.Mock(return_value=[])
        judgments = mock.Mock(
            return_value={
                "content-addressed-obligation": {
                    "classification": "paper_matches",
                }
            }
        )
        watch = mock.Mock(return_value="stable-watch")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                return_value="",
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", identity
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", corrected
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", judgments
            ),
            mock.patch.object(
                evidence, "_source_record_identity_process_watch_digest", watch
            ),
        ):
            context = evidence.build_evidence_run_context(
                self.paper, diagnostics=diagnostics
            )
        return context, (identity, corrected, judgments, watch)

    def _write_strict_receipt_only_source_record(self) -> None:
        """Create one required key omitted from the ordinary sidecar snapshot."""

        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": (
                    evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                ),
                "source_record_audit_sha256": "a" * 64,
                "expected_field_judgment_keys": ["strict-receipt-only"],
            },
        )

    def _select_v11(self) -> None:
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "require_source_spec_correspondence": True,
                },
            },
        )

    def test_common_snapshot_root_cannot_carry_legacy_authority(self) -> None:
        root_fields = {
            field.name
            for field in fields(evidence._EvidenceRunContextSnapshotRoot)
        }
        self.assertFalse(
            root_fields
            & {
                "audit_snapshot",
                "match_snapshot",
                "legacy_state",
                "semantic_reuse_authority",
                "source_record_identity_context",
            }
        )

    def test_current_repository_import_does_not_load_historical_raw_authorities(self) -> None:
        """Current-v11 startup is outside the historical receipt implementation."""

        repository_root = Path(__file__).resolve().parents[2]
        script = """
import sys
from scripts import audit_repository
forbidden = {
    'scripts.legacy_source_record_authorities',
    'scripts.source_record_archived_transports',
    'scripts.source_record_assumption_association',
    'scripts.source_record_auxiliary_routing_supplement',
    'scripts.source_record_freshness',
    'scripts.source_record_integrity',
    'scripts.source_record_obligation_groups',
    'scripts.source_record_overlay_protocol',
    'scripts.source_record_projection_contract',
    'scripts.source_record_semantic_reuse',
    'scripts.source_record_target_disposition',
    'scripts.review_surface_structure',
}
loaded = sorted(forbidden.intersection(sys.modules))
if loaded:
    raise SystemExit('historical raw authorities loaded: ' + ', '.join(loaded))
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=repository_root,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_public_selector_dispatches_to_only_the_selected_builder(self) -> None:
        v11_context = mock.Mock()
        v11_root = mock.Mock(v11_selected=True)
        v11_root.build_v11.return_value = v11_context
        with mock.patch.object(
            evidence._EvidenceRunContextSnapshotRoot,
            "acquire",
            return_value=v11_root,
        ):
            self.assertIs(
                evidence.build_evidence_run_context(self.paper),
                v11_context,
            )
        v11_root.build_v11.assert_called_once_with(None)
        v11_root.build_legacy.assert_not_called()

        legacy_context = mock.Mock()
        legacy_root = mock.Mock(v11_selected=False)
        legacy_root.build_legacy.return_value = legacy_context
        with mock.patch.object(
            evidence._EvidenceRunContextSnapshotRoot,
            "acquire",
            return_value=legacy_root,
        ):
            self.assertIs(
                evidence.build_evidence_run_context(self.paper),
                legacy_context,
            )
        legacy_root.build_legacy.assert_called_once_with(diagnostics=None)
        legacy_root.build_v11.assert_not_called()

    def test_v11_context_never_reads_or_validates_legacy_raw_source_record(self) -> None:
        """The selected Lean graph is one lane, not a raw-parser fallback."""

        self.assertTrue(evidence.EvidenceRunContext.__abstractmethods__)
        self.assertNotIn(
            "legacy_state",
            {field.name for field in fields(evidence.V11EvidenceRunContext)},
        )
        self.assertNotIn(
            "lean_review_graph_snapshot",
            {field.name for field in fields(evidence.LegacyEvidenceRunContext)},
        )
        self._select_v11()
        packet_cache = self.audit_dir / "human_review_packet_lean_cache.json"
        self._write_json(packet_cache, {"derived": "before"})
        identity = mock.Mock(side_effect=AssertionError("legacy identity ran"))
        fingerprint = mock.Mock(
            side_effect=AssertionError("legacy fingerprint ran")
        )
        watch = mock.Mock(side_effect=AssertionError("legacy watch ran"))
        diagnostics: dict[str, int] = {}
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", identity
            ),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence, "_source_record_identity_process_watch_digest", watch
            ),
            mock.patch.object(
                evidence,
                "_corrected_model_scope_contract_findings",
                side_effect=AssertionError("v11 ran legacy corrected-scope replay"),
            ),
            mock.patch.object(
                evidence,
                "_build_legacy_evidence_run_context",
                side_effect=AssertionError("v11 dispatched to legacy builder"),
            ),
        ):
            context = evidence.build_evidence_run_context(
                self.paper, diagnostics=diagnostics
            )
            self.assertIsInstance(context, evidence.V11EvidenceRunContext)
            self.assertNotIsInstance(context, evidence.LegacyEvidenceRunContext)
            self.assertEqual(
                context.source_semantic_lane,
                evidence.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
            )
            self.assertIsNone(context.legacy_source_record_state)
            self.assertFalse(context.corrected_scope_current)
            with self.assertRaisesRegex(
                ValueError, "has no legacy source-record state"
            ):
                context.require_legacy_source_record_state()
            self.assertIsNone(
                context.json_snapshot(
                    self.audit_dir / "source_record_audit.json"
                )
            )
            self.assertIsNone(context.json_snapshot(packet_cache))

            # Historical raw bytes can change during a v11 transaction because
            # they are not an input to it; every actual v11 source/map/Lean
            # input remains mutation-watched independently.
            self._write_json(
                self.audit_dir / "source_record_audit.json",
                {"historical": "changed but nonauthoritative"},
            )
            self._write_json(packet_cache, {"derived": "after"})
            self.assertEqual(
                evidence.evidence_run_context_mutation_findings(context), []
            )

        identity.assert_not_called()
        fingerprint.assert_not_called()
        watch.assert_not_called()
        self.assertNotIn(
            evidence.EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE,
            diagnostics,
        )

    def test_call_shaped_primary_receipt_is_legacy_only(self) -> None:
        self._select_v11()
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertFalse(
            evidence.has_current_v11_primary_closeout_semantic_graph_receipt(
                context, folder=self.paper
            )
        )
        self.assertFalse(
            evidence._issue_primary_closeout_source_record_judgment_receipt(
                context
            )
        )
        self.assertFalse(
            evidence.has_current_v11_primary_closeout_semantic_graph_receipt(
                context, folder=self.root / "papers" / "Other"
            )
        )

        self._write_json(self.paper / "status.json", {"status": "formalized"})
        legacy, _calls = self._build_context()
        self.assertTrue(
            evidence._issue_primary_closeout_source_record_judgment_receipt(legacy)
        )
        self.assertFalse(
            evidence.has_current_v11_primary_closeout_semantic_graph_receipt(
                legacy, folder=self.paper
            )
        )

    def test_call_shaped_evidence_receipt_cannot_be_minted(self) -> None:
        self._select_v11()
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertFalse(
            evidence.has_current_v11_evidence_integrity_receipt(context)
        )
        self.assertIsNone(
            evidence_acceptance._issue_current_v11_evidence_integrity(
                context,
                (),
                release=False,
                require_source_bytes=True,
            )
        )

        copied_context = replace(context)
        self.assertFalse(
            evidence.has_current_v11_evidence_integrity_receipt(copied_context)
        )

        self._write_json(self.paper / "status.json", {"status": "formalized"})
        legacy, _calls = self._build_context()
        self.assertTrue(
            evidence._issue_primary_closeout_source_record_judgment_receipt(legacy)
        )
        self.assertFalse(
            evidence.has_current_v11_evidence_integrity_receipt(legacy)
        )

    def test_v11_watches_only_the_selected_canonical_sidecar(self) -> None:
        self._select_v11()
        canonical = self.audit_dir / "paper_statement_map.json"
        root_alias = self.paper / "paper_statement_map.json"
        self._write_json(root_alias, {"historical_alias": True})
        with mock.patch.object(evidence, "ROOT", self.root):
            context = evidence.build_evidence_run_context(self.paper)

            self.assertIsNotNone(context.json_snapshot(canonical))
            self.assertIsNone(context.json_snapshot(root_alias))
            self._write_json(root_alias, {"historical_alias": "changed"})
            self.assertEqual(
                evidence.evidence_run_context_mutation_findings(context), []
            )

            self._write_json(canonical, {"items": {"changed": {}}})
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("paper_statement_map.json", findings[0].message)

    def test_v11_does_not_select_root_only_statement_map_alias(self) -> None:
        self._select_v11()
        canonical = self.audit_dir / "paper_statement_map.json"
        canonical.unlink()
        root_alias = self.paper / "paper_statement_map.json"
        self._write_json(root_alias, {"items": {"historical": {}}})

        with mock.patch.object(evidence, "ROOT", self.root):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertEqual(context.statement_map_snapshot.path, canonical)
        self.assertIsNone(context.statement_map_snapshot.sha256)
        self.assertIsNone(context.json_snapshot(root_alias))

    def test_future_legacy_sidecar_cannot_enter_v11_by_negative_list_omission(
        self,
    ) -> None:
        self._select_v11()
        future_name = "future_legacy_transport.json"
        future_path = self.audit_dir / future_name
        self._write_json(future_path, {"historical": True})
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "AUDIT_SIDECARS",
                (*evidence.AUDIT_SIDECARS, future_name),
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)
            self.assertIsNone(context.json_snapshot(future_path))
            self._write_json(future_path, {"historical": "changed"})
            self.assertEqual(
                evidence.evidence_run_context_mutation_findings(context), []
            )

    def test_v11_omits_inactive_assumption_and_defect_judgment_lanes(self) -> None:
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "require_source_spec_correspondence": True,
                    "assumption_names": [],
                },
            },
        )
        assumption_path = self.audit_dir / "assumption_match_llm.json"
        defect_path = self.audit_dir / "defect_support_match_llm.json"
        self._write_json(assumption_path, {"items": {"historical": {}}})
        self._write_json(defect_path, {"items": {"historical": {}}})

        with mock.patch.object(evidence, "ROOT", self.root):
            context = evidence.build_evidence_run_context(self.paper)
            self.assertIsNone(context.json_snapshot(assumption_path))
            self.assertIsNone(context.json_snapshot(defect_path))

            self._write_json(assumption_path, {"items": {"changed": {}}})
            self._write_json(defect_path, {"items": {"changed": {}}})
            self.assertEqual(
                evidence.evidence_run_context_mutation_findings(context), []
            )

    def test_v11_input_selection_does_not_import_dashboard_module(self) -> None:
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "require_source_spec_correspondence": True,
                    "assumption_names": [],
                },
            },
        )
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.dict(sys.modules, {"scripts.review_dashboard": None}),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertIsInstance(context, evidence.V11EvidenceRunContext)

    def test_v11_watches_selected_assumptions_not_legacy_defect_support(
        self,
    ) -> None:
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "require_source_spec_correspondence": True,
                    "assumption_names": ["Fixture.sourceBoundary"],
                },
            },
        )
        self._write_json(
            self.audit_dir / "paper_statement_map.json",
            {
                "items": {
                    "result": {"source_defect_ids": ["source-typo"]}
                }
            },
        )
        assumption_path = self.audit_dir / "assumption_match_llm.json"
        defect_path = self.audit_dir / "defect_support_match_llm.json"
        self._write_json(assumption_path, {"items": {}})
        self._write_json(defect_path, {"items": {}})

        with mock.patch.object(evidence, "ROOT", self.root):
            context = evidence.build_evidence_run_context(self.paper)
            self.assertIsNotNone(context.json_snapshot(assumption_path))
            self.assertIsNone(context.json_snapshot(defect_path))

            self._write_json(assumption_path, {"items": {"changed": {}}})
            self._write_json(defect_path, {"items": {"changed": {}}})
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("assumption_match_llm.json", findings[0].message)
        self.assertNotIn("defect_support_match_llm.json", findings[0].message)

    def test_legacy_context_still_watches_both_sidecar_locations(self) -> None:
        canonical = self.audit_dir / "paper_statement_map.json"
        root_alias = self.paper / "paper_statement_map.json"
        self._write_json(root_alias, {"historical_alias": True})
        context, _calls = self._build_context()

        self.assertIsNotNone(context.json_snapshot(canonical))
        self.assertIsNotNone(context.json_snapshot(root_alias))

    def test_v11_watches_configured_source_not_conventional_source_guesses(
        self,
    ) -> None:
        self._select_v11()
        status = json.loads(
            (self.paper / "status.json").read_text(encoding="utf-8")
        )
        status["review_entrypoint"] = "FINAL_VALIDATION_REPORT.md"
        self._write_json(self.paper / "status.json", status)
        configured_source = self.paper / "sources" / "canonical.txt"
        configured_source.parent.mkdir(parents=True)
        configured_source.write_text("selected source\n", encoding="utf-8")
        self._write_json(
            self.audit_dir / "paper_statement_map.json",
            {
                "source_artifact_path": "sources/canonical.txt",
                "items": {
                    "result": {
                        "source_anchor_evidence": [
                            {"path": "sources/canonical.txt"}
                        ]
                    }
                },
            },
        )
        conventional_source = self.paper / "paper.tex"
        conventional_source.write_text("unselected source\n", encoding="utf-8")
        report = self.paper / "FINAL_VALIDATION_REPORT.md"
        report.write_text("derived report\n", encoding="utf-8")

        with mock.patch.object(evidence, "ROOT", self.root):
            context = evidence.build_evidence_run_context(self.paper)
            snapshotted_paths = {
                snapshot.path.resolve() for snapshot in context.input_snapshots
            }
            self.assertIn(configured_source.resolve(), snapshotted_paths)
            self.assertNotIn(conventional_source.resolve(), snapshotted_paths)
            self.assertNotIn(report.resolve(), snapshotted_paths)
            self.assertNotIn((self.paper / "source.txt").resolve(), snapshotted_paths)
            self.assertNotIn(
                (
                    self.paper
                    / ".review_traces"
                    / "paper_theorem_validations.jsonl"
                ).resolve(),
                snapshotted_paths,
            )

            conventional_source.write_text(
                "changed but still unselected\n", encoding="utf-8"
            )
            report.write_text("changed derived report\n", encoding="utf-8")
            self.assertEqual(
                evidence.evidence_run_context_mutation_findings(context), []
            )

            configured_source.write_text("changed selected source\n", encoding="utf-8")
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("sources/canonical.txt", findings[0].message)

    def test_context_fingerprint_reuses_typed_semantic_reconciliation(self) -> None:
        """The frozen fingerprint and final identity gate use one route projection."""

        projection = object()
        replay = mock.Mock()
        replay.semantic_contract_revalidation_projection.return_value = (
            projection,
            "",
        )
        fingerprint = mock.Mock(return_value="")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_semantic_contract_revalidation_module",
                return_value=replay,
            ),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", return_value=""
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", return_value={}
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            evidence.build_evidence_run_context(self.paper)

        self.assertEqual(fingerprint.call_count, 1)
        self.assertIs(
            fingerprint.call_args.kwargs["semantic_contract_revalidation"],
            projection,
        )

    def _write_current_source_record_with_map_pin(self) -> None:
        """Make the fixture sufficient for the optional structural replay."""

        map_bytes = (self.audit_dir / "paper_statement_map.json").read_bytes()
        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": (
                    evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                ),
                "source_record_audit_sha256": "a" * 64,
                "source_record_audit_integrity_sha256": "b" * 64,
                "paper_statement_map_sha256": hashlib.sha256(map_bytes).hexdigest(),
            },
        )

    def test_one_materialization_per_unchanged_transaction(self) -> None:
        diagnostics: dict[str, int] = {}
        context, calls = self._build_context(diagnostics)
        identity, corrected, judgments, watch = calls

        identity.assert_called_once()
        corrected.assert_called_once()
        judgments.assert_called_once()
        watch.assert_called_once()
        self.assertEqual(
            diagnostics,
            {
                evidence.EVIDENCE_DIAGNOSTIC_CONTEXTS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE: 1,
                evidence.EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS: 1,
            },
        )
        self.assertEqual(
            set(
                context.require_legacy_source_record_state().current_source_record_judgments
            ),
            {"content-addressed-obligation"},
        )

    def test_v11_semantic_gates_run_once_per_exact_transaction(self) -> None:
        """Primary/evidence consumers share strict findings, not authority flags."""

        context, _calls = self._build_context()
        raw_finding = evidence.Finding(
            "ERROR", "Fixture", "audit/raw.json", "raw semantic mismatch"
        )
        library_finding = evidence.Finding(
            "ERROR", "Fixture", "audit/library.json", "library mismatch"
        )
        raw_gate = mock.Mock(return_value=[raw_finding])
        library_gate = mock.Mock(return_value=[library_finding])
        with (
            mock.patch.object(
                evidence,
                "_v11_raw_source_spec_screening_findings_uncached",
                raw_gate,
            ),
            mock.patch.object(
                evidence,
                "_material_library_semantic_review_findings_uncached",
                library_gate,
            ),
        ):
            first_raw = evidence.v11_raw_source_spec_screening_findings(
                self.paper, "formalized", context=context
            )
            first_library = evidence.material_library_semantic_review_findings(
                self.paper, "formalized", context=context
            )
            # A legacy caller may mutate its local list.  That must not alter
            # the transaction-owned immutable tuple returned to later lanes.
            first_raw.clear()
            first_library.clear()
            self.assertEqual(
                evidence.v11_raw_source_spec_screening_findings(
                    self.paper, "formalized", context=context
                ),
                [raw_finding],
            )
            self.assertEqual(
                evidence.material_library_semantic_review_findings(
                    self.paper, "formalized", context=context
                ),
                [library_finding],
            )

        raw_gate.assert_called_once()
        library_gate.assert_called_once()
        self.assertEqual(
            dict(context.runtime_cache_diagnostics()),
            {
                "validation_cache_hits": 2,
                "validation_cache_misses": 2,
                "validation_cache_entries": 2,
                "v11_graph_carrier_reuses": 0,
            },
        )

    def test_semantic_contract_inventory_runs_once_per_exact_transaction(self) -> None:
        """Nested contract and bridge consumers share one structural verdict."""

        context, _calls = self._build_context()
        finding = evidence.Finding(
            "ERROR", "Fixture", "audit/map.json", "contract mismatch"
        )
        validator = mock.Mock(return_value=[finding])
        with mock.patch.object(
            evidence,
            "_semantic_contract_inventory_findings_uncached",
            validator,
        ):
            first = evidence.semantic_contract_inventory_findings(
                self.paper, "formalized", context=context
            )
            first.clear()
            self.assertEqual(
                evidence.semantic_contract_inventory_findings(
                    self.paper, "formalized", context=context
                ),
                [finding],
            )

        validator.assert_called_once()

    def test_source_spec_inventory_runs_once_per_exact_transaction(self) -> None:
        """Preflight and evidence stages share one frozen source/Spec verdict."""

        context, _calls = self._build_context()
        finding = evidence.Finding(
            "ERROR", "Fixture", "audit/map.json", "source/Spec mismatch"
        )
        validator = mock.Mock(return_value=[finding])
        with mock.patch.object(
            evidence,
            "_source_spec_correspondence_inventory_findings_uncached",
            validator,
        ):
            first = evidence.source_spec_correspondence_inventory_findings(
                self.paper,
                "formalized",
                context=context,
            )
            first.clear()
            self.assertEqual(
                evidence.source_spec_correspondence_inventory_findings(
                    self.paper,
                    "formalized",
                    context=context,
                ),
                [finding],
            )

        validator.assert_called_once()

    def test_repaired_defect_route_runs_once_per_exact_transaction(self) -> None:
        """Early route preflight and evidence inventory share one route verdict."""

        context, _calls = self._build_context()
        finding = evidence.Finding(
            "ERROR", "Fixture", "audit/map.json", "repaired defect is unrouted"
        )
        validator = mock.Mock(return_value=[finding])
        with mock.patch.object(
            source_manifest,
            "_repaired_source_defect_route_preflight_findings_uncached",
            validator,
        ):
            first = evidence.repaired_source_defect_route_preflight_findings(
                self.paper,
                "formalized",
                context=context,
            )
            first.clear()
            self.assertEqual(
                evidence.repaired_source_defect_route_preflight_findings(
                    self.paper,
                    "formalized",
                    context=context,
                ),
                [finding],
            )

        validator.assert_called_once()

    def test_source_proof_fidelity_runs_once_per_exact_transaction(self) -> None:
        """Primary and deferred evidence gates share the complete fidelity verdict."""

        context, _calls = self._build_context()
        finding = evidence.Finding(
            "ERROR", "Fixture", "audit/fidelity.json", "proof route mismatch"
        )
        validator = mock.Mock(return_value=[finding])
        with mock.patch.object(
            evidence,
            "_source_proof_fidelity_findings_uncached",
            validator,
        ):
            primary = audit_repository.check_source_proof_fidelity(
                self.paper,
                "formalized",
                context.status_payload,
                run_context=mock.Mock(evidence_context=context),
            )
            self.assertEqual(len(primary), 1)
            primary.clear()
            self.assertEqual(
                evidence.source_proof_fidelity_findings(
                    self.paper,
                    "formalized",
                    context.status_payload,
                    context=context,
                ),
                [finding],
            )
            validator.assert_called_once()

            copied = replace(context)
            self.assertFalse(copied.issued_by_builder)
            evidence.source_proof_fidelity_findings(
                self.paper,
                "formalized",
                copied.status_payload,
                context=copied,
            )
            evidence.source_proof_fidelity_findings(
                self.paper,
                "formalized",
                copied.status_payload,
                context=copied,
            )
            self.assertEqual(validator.call_count, 3)

            evidence.source_proof_fidelity_findings(
                self.paper,
                "formalized",
                context.status_payload,
                context=context,
                file_bytes_override={},
            )
            self.assertEqual(validator.call_count, 4)

            evidence.source_proof_fidelity_findings(
                self.paper,
                "formalized",
                {**context.status_payload, "status": "partially formalized"},
                context=context,
            )
            self.assertEqual(validator.call_count, 5)

    def test_v11_semantic_gate_cache_is_mode_bound_and_not_copyable(self) -> None:
        context, _calls = self._build_context()
        uncached = mock.Mock(return_value=[])
        with mock.patch.object(
            evidence,
            "_v11_raw_source_spec_screening_findings_uncached",
            uncached,
        ):
            evidence.v11_raw_source_spec_screening_findings(
                self.paper, "formalized", context=context
            )
            evidence.v11_raw_source_spec_screening_findings(
                self.paper,
                "formalized",
                require_source_bytes=False,
                context=context,
            )
            copied = replace(context)
            self.assertFalse(copied.issued_by_builder)
            evidence.v11_raw_source_spec_screening_findings(
                self.paper, "formalized", context=copied
            )
            evidence.v11_raw_source_spec_screening_findings(
                self.paper, "formalized", context=copied
            )

        self.assertEqual(uncached.call_count, 4)
        self.assertEqual(
            dict(context.runtime_cache_diagnostics()),
            {
                "validation_cache_hits": 0,
                "validation_cache_misses": 2,
                "validation_cache_entries": 2,
                "v11_graph_carrier_reuses": 0,
            },
        )

    def test_v11_lean_review_surface_is_shared_only_inside_exact_context(self) -> None:
        self._select_v11()
        context, _calls = self._build_context()
        surface = evidence._V11LeanReviewSurface(
            semantic_targets={},
            paper_prerequisites=(),
            library_prerequisites=(),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={},
            module_sources={},
            build_input_provider=object(),
        )
        builder = mock.Mock(return_value=surface)
        with mock.patch.object(
            review_surface, "build_v11_review_surface_material", builder
        ):
            first = review_surface.build_accepting_v11_review_surface(
                evidence.ROOT,
                self.paper,
                ["Fixture.SecondSpec", "Fixture.FirstSpec"],
                context=context,
            )
            second = review_surface.build_accepting_v11_review_surface(
                evidence.ROOT,
                self.paper,
                ["Fixture.FirstSpec", "Fixture.SecondSpec"],
                context=context,
            )
            self.assertIs(first, second)
            builder.assert_called_once_with(
                evidence.ROOT,
                self.paper,
                ("Fixture.FirstSpec", "Fixture.SecondSpec"),
                context=context,
            )

            copied = replace(context)
            self.assertFalse(copied.issued_by_builder)
            with self.assertRaisesRegex(
                ValueError,
                "requires its exact issued transaction",
            ):
                review_surface.build_accepting_v11_review_surface(
                    evidence.ROOT,
                    self.paper,
                    ["Fixture.FirstSpec", "Fixture.SecondSpec"],
                    context=copied,
                )

            builder.return_value = replace(surface, graph_request={"schema": 2})
            with self.assertRaisesRegex(
                ValueError,
                "cannot retain multiple v11 Lean graphs",
            ):
                review_surface.build_accepting_v11_review_surface(
                    evidence.ROOT,
                    self.paper,
                    ["Fixture.ThirdSpec"],
                    context=context,
                )

        self.assertEqual(builder.call_count, 3)
        diagnostics = dict(context.runtime_cache_diagnostics())
        self.assertEqual(diagnostics["validation_cache_misses"], 2)
        self.assertEqual(diagnostics["validation_cache_hits"], 1)
        self.assertEqual(diagnostics["validation_cache_entries"], 2)

    def test_diagnostic_surface_never_prepares_a_missing_or_stale_graph(self) -> None:
        self._select_v11()
        context, _calls = self._build_context()
        with (
            mock.patch.object(
                review_surface, "build_accepting_v11_review_surface",
                side_effect=AssertionError("diagnostic entered accepting builder"),
            ),
            mock.patch(
                "scripts.lean_signature_manifest.run_lean_declaration_inventory",
                side_effect=AssertionError("diagnostic launched Lean"),
            ),
            mock.patch.object(
                review_surface, "build_v11_review_surface_material",
                side_effect=ValueError("stale saved Lean inventory"),
            ) as material,
        ):
            with self.assertRaisesRegex(ValueError, "explicit Lean graph preparation required"):
                evidence._v11_lean_review_surface(self.paper, ["Fixture.Spec"], context=context)
            material.assert_not_called()
            with mock.patch.object(
                type(context), "v11_lean_review_graph_payload",
                new_callable=mock.PropertyMock, return_value={},
            ):
                with self.assertRaisesRegex(ValueError, "preparation required: stale"):
                    evidence._v11_lean_review_surface(self.paper, ["Fixture.Spec"], context=context)
            material.assert_called_once_with(
                evidence.ROOT, self.paper, ("Fixture.Spec",), context=context,
                require_graph_checkpoint=True,
            )
        self.assertIsNone(context.retained_v11_review_surface())

    def test_diagnostic_checkpoint_projection_does_not_grant_accepting_reuse(self) -> None:
        self._select_v11()
        context, _calls = self._build_context()
        surface = evidence._V11LeanReviewSurface(
            semantic_targets={"Fixture.Spec": {}}, paper_prerequisites=(),
            library_prerequisites=(), source_declarations={},
            library_source_declarations={}, semantic_contracts={},
            declaration_inventory={}, module_sources={}, build_input_provider=None,
        )
        with (
            mock.patch.object(type(context), "v11_lean_review_graph_payload",
                              new_callable=mock.PropertyMock, return_value={}),
            mock.patch.object(review_surface, "build_v11_review_surface_material",
                              return_value=surface) as material,
            mock.patch("scripts.lean_signature_manifest.run_lean_declaration_inventory",
                       side_effect=AssertionError("diagnostic launched Lean")),
        ):
            first = evidence._v11_lean_review_surface(self.paper, ["Fixture.Spec"], context=context)
            self.assertIs(first, evidence._v11_lean_review_surface(
                self.paper, ["Fixture.Spec"], context=context,
            ))
            material.assert_called_once()
        self.assertIsNone(context.retained_v11_review_surface())
        self.assertIsNone(first.build_input_provider)

        # A strict worker's already-prepared surface is reused directly.
        prepared = replace(surface, build_input_provider=object())
        context.retain_v11_review_surface(prepared)
        with mock.patch.object(review_surface, "build_v11_review_surface_material",
                               side_effect=AssertionError("retained surface rebuilt")):
            self.assertIs(prepared, evidence._v11_lean_review_surface(
                self.paper, ["Fixture.Spec"], context=context,
            ))

    def test_diagnostic_full_projection_uses_only_checkpoint_graph_material(self) -> None:
        self._select_v11()
        context, _calls = self._build_context()
        projection = mock.Mock(**{name: {} for name in (
            "semantic_targets", "paper_semantic_targets", "library_semantic_targets",
            "paper_declaration_sources", "library_declaration_sources",
            "source_declarations", "library_source_declarations",
            "semantic_contracts", "review_claim_manifests",
        )})
        material = mock.Mock(
            acquisition=mock.Mock(projection=projection, inventory={}),
            build_input_provider=None, module_sources={}, graph_request={},
            carrier_reused=True,
        )
        with (
            mock.patch.object(graph_contract, "build_v11_lean_review_graph_material",
                              return_value=material) as graph,
            mock.patch.object(review_surface, "project_paper_semantic_prerequisites",
                              return_value=[]),
            mock.patch.object(review_surface, "project_library_semantic_prerequisites",
                              return_value=[]),
            mock.patch("scripts.lean_signature_manifest.run_lean_declaration_inventory",
                       side_effect=AssertionError("diagnostic launched Lean")),
        ):
            result = review_surface.build_v11_review_surface_material(
                self.root, self.paper, ["Fixture.Spec"], context=context,
                require_graph_checkpoint=True,
            )
        graph.assert_called_once_with(
            self.root, self.paper, ["Fixture.Spec"], context=context,
            checkpoint_projection_only=True,
        )
        self.assertIsNone(result.build_input_provider)
        self.assertIsNone(context.retained_v11_review_surface())

    def test_plan_bound_v11_graph_reuses_inventory_and_watches_carrier(self) -> None:
        self._select_v11()
        audit_config = self.root / "papers" / "audit_config.json"
        lakefile = self.root / "lakefile.toml"
        self._write_json(audit_config, {"schema": 1})
        lakefile.write_text("name = \"fixture\"\n", encoding="utf-8")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(evidence, "AUDIT_CONFIG", audit_config),
            mock.patch.object(evidence, "LAKEFILE", lakefile),
            mock.patch.object(
                graph_contract,
                "graph_engine_projection",
                return_value={"schema": 1, "sources": [], "semantic_hash_tool_identity": {}},
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
        ):
            planner_context = evidence.build_evidence_run_context(self.paper)
            request = {
                "schema": 1,
                "entry_module": "Fixture.ProofInterface",
                "specification_names": ["Fixture.SourceSpec"],
            }
            inventory = {"schema": 1, "declarations": []}
            surface = evidence._V11LeanReviewSurface(
                semantic_targets={},
                paper_prerequisites=(),
                library_prerequisites=(),
                source_declarations={},
                library_source_declarations={},
                semantic_contracts={},
                declaration_inventory=inventory,
                module_sources={},
                build_input_provider=object(),
                graph_request=request,
            )
            binding = planner_context._issuer_token
            self.assertIsInstance(binding, evidence._EvidenceRunContextIssuerBinding)
            binding.v11_review_surface = surface
            carrier = graph_contract.builder_issued_v11_lean_review_graph_carrier(
                self.paper,
                planner_context,
                repository_root=self.root,
            )
            self.assertIsNotNone(carrier)
            reference = graph_contract.checkpoint_builder_issued_v11_lean_review_graph(
                self.paper,
                planner_context,
                repository_root=self.root,
            )
            self.assertIsNotNone(reference)
            # Independent semantic judgments and generated display counts are
            # still checked by their own current gates, but cannot alter the
            # Lean declaration graph or force Lean discovery to repeat.
            self._write_json(
                self.audit_dir / "v11_raw_source_spec_screening.json",
                {"schema": 3, "items": {}},
            )
            status_payload = json.loads(
                (self.paper / "status.json").read_text(encoding="utf-8")
            )
            status_payload["paper_interface"] = {
                "line_count": 999,
                "declaration_rows": 999,
                "review_rows": 999,
            }
            self._write_json(self.paper / "status.json", status_payload)
            statement_map = json.loads(
                (self.audit_dir / "paper_statement_map.json").read_text(
                    encoding="utf-8"
                )
            )
            statement_map["non_graph_bookkeeping_note"] = "reviewed"
            self._write_json(
                self.audit_dir / "paper_statement_map.json",
                statement_map,
            )
            # Reviewer issuance is downstream of Lean discovery. Adding both
            # ledgers must not change the graph request or reacquire Lean.
            self._write_json(
                self.audit_dir / "paper_semantic_prerequisites.json",
                {"schema": 1, "items": {}},
            )
            self._write_json(
                self.audit_dir / "library_semantic_review.json",
                {"schema": 1, "items": {}},
            )
            worker_context = (
                evidence.build_evidence_run_context_with_v11_graph_checkpoint(
                    self.paper
                )
            )
            self.assertEqual(
                graph_contract.validated_graph_carrier_inventory(
                    self.paper,
                    worker_context,
                    graph_request=request,
                    repository_root=self.root,
                ),
                inventory,
            )
            # The portable carrier contract grants no runtime authority and
            # therefore does not mutate evidence diagnostics.  The accepting
            # graph consumer records reuse only after this check succeeds.
            self.assertEqual(
                worker_context.runtime_cache_diagnostics()[
                    "v11_graph_carrier_reuses"
                ],
                0,
            )
            with mock.patch.object(
                graph_contract,
                "graph_engine_projection",
                return_value={
                    "schema": 1,
                    "sources": [{"path": "changed", "sha256": "a" * 64}],
                    "semantic_hash_tool_identity": {},
                },
            ):
                self.assertIsNone(
                    graph_contract.current_v11_lean_review_graph_checkpoint_reference(
                        self.paper,
                        worker_context,
                        repository_root=self.root,
                    )
                )
            with self.assertRaisesRegex(ValueError, "current frozen inputs"):
                graph_contract.validated_graph_carrier_inventory(
                    self.paper,
                    worker_context,
                    graph_request={**request, "specification_names": ["Fixture.OtherSpec"]},
                    repository_root=self.root,
                )

            carrier_path = self.root / str(reference["path"])
            carrier_path.write_text("{}\n", encoding="utf-8")
            mutation_findings = evidence.evidence_run_context_mutation_findings(
                worker_context
            )
            self.assertTrue(
                any(
                    "changed during the paper audit transaction" in item.message
                    for item in mutation_findings
                )
            )

    def test_diagnostic_context_reuses_checkpoint_owner_without_second_snapshot(self) -> None:
        snapshot_root = mock.Mock(v11_selected=True)
        with mock.patch.object(
            evidence._EvidenceRunContextSnapshotRoot, "acquire",
            return_value=snapshot_root,
        ) as acquire:
            context = evidence.build_evidence_run_context(
                self.paper, reuse_v11_graph_checkpoint=True,
            )
        acquire.assert_called_once_with(self.paper)
        snapshot_root.build_v11_with_graph_checkpoint.assert_called_once_with()
        snapshot_root.build_v11.assert_not_called()
        self.assertIs(context, snapshot_root.build_v11_with_graph_checkpoint.return_value)

    def test_checkpoint_context_reuses_one_input_snapshot_transaction(self) -> None:
        base_context = object()
        graph_context = object()
        reference = {"path": ".lake/closeout-objects/graph.json"}
        snapshot_root = mock.Mock(
            v11_selected=True,
            folder=self.paper,
            repository_root=evidence.ROOT,
        )
        snapshot_root.build_v11.side_effect = (base_context, graph_context)
        snapshot_root.build_v11_with_graph_checkpoint.side_effect = lambda: (
            evidence_transaction.CurrentV11EvidenceSnapshotRoot.build_v11_with_graph_checkpoint(snapshot_root)
        )

        with (
            mock.patch.object(
                evidence_transaction.CurrentV11EvidenceSnapshotRoot,
                "acquire",
                return_value=snapshot_root,
            ) as acquire,
            mock.patch.object(
                graph_contract,
                "current_v11_lean_review_graph_checkpoint_reference",
                return_value=reference,
            ) as checkpoint,
            mock.patch.object(
                evidence,
                "build_evidence_run_context",
                side_effect=AssertionError("a second snapshot transaction started"),
            ),
        ):
            actual = evidence.build_evidence_run_context_with_v11_graph_checkpoint(
                self.paper
            )

        self.assertIs(actual, graph_context)
        acquire.assert_called_once_with(
            self.paper,
            repository_root=evidence.ROOT,
        )
        checkpoint.assert_called_once_with(
            self.paper,
            base_context,
            repository_root=evidence.ROOT,
        )
        self.assertEqual(
            snapshot_root.build_v11.call_args_list,
            [mock.call(None), mock.call(reference)],
        )

    def test_stale_checkpoint_is_a_cache_miss_not_a_current_graph_blocker(self) -> None:
        base_context = object()
        snapshot_root = mock.Mock(
            v11_selected=True,
            folder=self.paper,
            repository_root=self.root,
        )
        snapshot_root.build_v11.return_value = base_context
        snapshot_root.build_v11_with_graph_checkpoint.side_effect = lambda: (
            evidence_transaction.CurrentV11EvidenceSnapshotRoot.build_v11_with_graph_checkpoint(snapshot_root)
        )

        with (
            mock.patch.object(
                evidence_transaction.CurrentV11EvidenceSnapshotRoot,
                "acquire",
                return_value=snapshot_root,
            ),
            mock.patch.object(
                graph_contract,
                "current_v11_lean_review_graph_checkpoint_reference",
                side_effect=ValueError("Lean import-closure source bytes changed"),
            ),
        ):
            actual = evidence_transaction.build_current_v11_context_with_graph_checkpoint(
                self.paper,
                repository_root=self.root,
            )

        self.assertIs(actual, base_context)
        self.assertEqual(snapshot_root.build_v11.call_args_list, [mock.call(None)])

    def test_v11_checkpoint_loader_never_builds_a_legacy_context(self) -> None:
        snapshot_root = mock.Mock(v11_selected=False)
        with mock.patch.object(
            evidence_transaction.CurrentV11EvidenceSnapshotRoot,
            "acquire",
            return_value=snapshot_root,
        ):
            with self.assertRaisesRegex(ValueError, "does not select the v11"):
                evidence.build_evidence_run_context_with_v11_graph_checkpoint(
                    self.paper
                )

        snapshot_root.build_v11.assert_not_called()
        snapshot_root.build_legacy.assert_not_called()

    def test_current_review_projection_uses_graph_targets_without_packet(self) -> None:
        specification = "Fixture.SourceSpec"
        context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            v11_lean_review_graph_payload={"schema": 3},
            statement_map={"items": {}},
        )
        route_set = mock.Mock()
        route_set.result_specifications.return_value = (specification,)
        projection_surface = evidence.CurrentV11ReviewGraphProjection(
            context=context,
            specifications=(specification,),
            semantic_targets={specification: {"display": "Prop"}},
            paper_prerequisite_targets={"Fixture.Model": {"display": "Model"}},
            library_semantic_targets={
                "AppliedModelingLib.Model": {"display": "Library model"}
            },
            library_semantic_target_errors={},
            paper_declaration_sources={
                specification: {
                    "paper_declaration_source": "def SourceSpec : Prop := True",
                }
            },
            library_declaration_sources={
                "AppliedModelingLib.Model": {
                    "library_definition": "def Model : Prop := True",
                }
            },
        )

        with (
            mock.patch.object(
                evidence_transaction,
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ),
            mock.patch.object(
                review_surface,
                "build_current_v11_review_graph_projection",
                return_value=projection_surface,
            ) as project_surface,
            mock.patch.object(
                review_surface.EvidenceRouteSet,
                "from_source_map",
                return_value=route_set,
            ),
        ):
            projection = evidence.current_v11_review_graph_projection(self.paper)

        self.assertIsNotNone(projection)
        assert projection is not None
        project_surface.assert_called_once_with(
            evidence.ROOT,
            self.paper,
            (specification,),
            context=context,
        )
        self.assertIs(projection.context, context)
        self.assertEqual(projection.specifications, (specification,))
        material = projection.target_material()
        self.assertEqual(material["specifications"], [specification])
        self.assertIs(material["semantic_targets"], projection_surface.semantic_targets)
        self.assertIs(
            material["paper_prerequisite_targets"],
            projection_surface.paper_prerequisite_targets,
        )
        self.assertIs(
            material["library_semantic_targets"],
            projection_surface.library_semantic_targets,
        )
        self.assertIs(
            material["paper_declaration_sources"],
            projection_surface.paper_declaration_sources,
        )
        self.assertIs(
            material["library_declaration_sources"],
            projection_surface.library_declaration_sources,
        )

    def test_current_review_projection_without_checkpoint_is_a_cache_miss(
        self,
    ) -> None:
        context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            v11_lean_review_graph_payload=None,
        )
        with (
            mock.patch.object(
                evidence_transaction,
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ),
            mock.patch.object(
                review_surface,
                "build_current_v11_review_graph_projection",
                side_effect=AssertionError("a cache probe launched graph work"),
            ) as build_surface,
        ):
            self.assertIsNone(
                evidence.current_v11_review_graph_projection(self.paper)
            )
        build_surface.assert_not_called()

    def test_current_review_projection_owns_nonrendering_ledger_projection(
        self,
    ) -> None:
        target = {
            "display": "True",
            "display_sha256": hashlib.sha256(b"True").hexdigest(),
        }
        declaration = "def Model := True"
        declaration_digest = hashlib.sha256(declaration.encode()).hexdigest()
        frozen_bytes = {self.paper / "PaperInterface.lean": b"def Model := True\n"}
        context = mock.Mock(
            folder=self.paper.resolve(),
            statement_map={"paper": "Fixture", "items": {}},
        )
        context.file_bytes_override.return_value = frozen_bytes
        projection = evidence.CurrentV11ReviewGraphProjection(
            context=context,
            specifications=("Fixture.SourceSpec",),
            semantic_targets={"Fixture.SourceSpec": dict(target)},
            paper_prerequisite_targets={"Fixture.Model": dict(target)},
            library_semantic_targets={"Library.Model": dict(target)},
            library_semantic_target_errors={},
            paper_declaration_sources={"Fixture.Model": {
                "paper_declaration_source": declaration,
                "paper_declaration_sha256": declaration_digest,
            }},
            library_declaration_sources={"Library.Model": {
                "library_definition": declaration,
                "library_definition_sha256": declaration_digest,
            }},
        )
        paper_rows = ({"lean_name": "Fixture.Model"},)
        library_rows = ({"lean_name": "Library.Model"},)
        with (
            mock.patch.object(
                review_surface,
                "project_paper_semantic_prerequisites",
                return_value=list(paper_rows),
            ) as project_paper,
            mock.patch.object(
                review_surface,
                "project_library_semantic_prerequisites",
                return_value=list(library_rows),
            ) as project_library,
        ):
            self.assertEqual(
                projection.project_paper_prerequisites(
                    self.paper,
                    ledger={"items": {}},
                ),
                paper_rows,
            )
            self.assertEqual(
                projection.project_library_prerequisites(
                    self.paper,
                    ledger={"items": {}},
                ),
                library_rows,
            )

        self.assertEqual(
            project_paper.call_args.kwargs["file_bytes_override"], frozen_bytes
        )
        self.assertEqual(
            project_library.call_args.kwargs["file_bytes_override"], frozen_bytes
        )
        self.assertIs(
            project_paper.call_args.kwargs["declaration_sources"],
            projection.paper_declaration_sources,
        )
        self.assertIs(
            project_library.call_args.kwargs["declaration_sources"],
            projection.library_declaration_sources,
        )
        self.assertEqual(
            set(project_paper.call_args.kwargs["supporting_declarations_sha256_by_name"]),
            {"Fixture.Model"},
        )

    def test_one_pre_review_graph_materializes_checkpoint_without_packet(self) -> None:
        spec = "Fixture.SourceSpec"
        context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            statement_map={"items": {}},
        )
        context.changed_input_paths.return_value = ()
        context.runtime_cache_diagnostics.return_value = {
            "v11_graph_carrier_reuses": 0,
        }
        route_set = mock.Mock()
        route_set.result_specifications.return_value = (spec,)
        provider = mock.Mock()
        provider.finalize_unchanged.return_value = True
        surface = graph_preparation.V11LeanReviewSurface(
            semantic_targets={spec: {"display": "Prop"}},
            paper_prerequisites=(),
            library_prerequisites=(),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={(spec, "Fixture.SourceProof", "proves"): {}},
            declaration_inventory={"schema": 1},
            module_sources={},
            build_input_provider=provider,
            graph_request={"schema": 4, "specification_names": [spec]},
            paper_semantic_targets={"Fixture.Model": {"display": "Model"}},
            library_semantic_targets={"Library.Primitive": {"display": "Primitive"}},
        )
        reference = {
            "schema": 1,
            "kind": "v11_lean_review_graph",
            "path": ".lake/closeout-objects/graph.json",
            "sha256": "a" * 64,
        }
        with (
            mock.patch.object(
                graph_preparation,
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ),
            mock.patch.object(
                graph_preparation.EvidenceRouteSet,
                "from_source_map",
                return_value=route_set,
            ),
            mock.patch.object(
                graph_preparation,
                "build_accepting_v11_review_surface",
                return_value=surface,
            ) as acquire,
            mock.patch.object(
                graph_preparation,
                "checkpoint_builder_issued_v11_lean_review_graph",
                return_value=reference,
            ) as checkpoint,
        ):
            prepared = dict(
                graph_preparation.prepare_v11_lean_review_graph(
                    self.root, self.paper
                )
            )

        acquire.assert_called_once_with(
            self.root, self.paper, (spec,), context=context
        )
        checkpoint.assert_called_once_with(
            self.paper,
            context,
            repository_root=self.root,
        )
        provider.finalize_unchanged.assert_called_once_with()
        self.assertFalse(prepared["acceptance_credential"])
        self.assertFalse(prepared["semantic_judgments_issued"])
        self.assertFalse(prepared["presentation_materialized"])
        self.assertFalse(prepared["checkpoint_reused"])
        self.assertEqual(prepared["specification_count"], 1)
        self.assertEqual(prepared["paper_prerequisite_count"], 1)
        self.assertEqual(prepared["library_prerequisite_count"], 1)
        self.assertEqual(prepared["proof_contract_count"], 1)

    def test_legacy_graph_preparation_export_delegates_to_current_owner(self) -> None:
        prepared = {"schema": 1, "paper": self.paper.name}
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                graph_preparation,
                "prepare_v11_lean_review_graph",
                return_value=prepared,
            ) as current_prepare,
        ):
            observed = evidence.prepare_v11_lean_review_graph(self.paper)

        self.assertIs(observed, prepared)
        current_prepare.assert_called_once_with(self.root, self.paper)

    def test_pre_review_graph_publishes_no_cache_when_inputs_changed(self) -> None:
        spec = "Fixture.SourceSpec"
        context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            statement_map={"items": {}},
        )
        context.changed_input_paths.return_value = ()
        route_set = mock.Mock()
        route_set.result_specifications.return_value = (spec,)
        provider = mock.Mock()
        provider.finalize_unchanged.return_value = False
        surface = graph_preparation.V11LeanReviewSurface(
            semantic_targets={spec: {"display": "Prop"}},
            paper_prerequisites=(),
            library_prerequisites=(),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={"schema": 1},
            module_sources={},
            build_input_provider=provider,
            graph_request={"schema": 4, "specification_names": [spec]},
        )

        with (
            mock.patch.object(
                graph_preparation,
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ),
            mock.patch.object(
                graph_preparation.EvidenceRouteSet,
                "from_source_map",
                return_value=route_set,
            ),
            mock.patch.object(
                graph_preparation,
                "build_accepting_v11_review_surface",
                return_value=surface,
            ),
            mock.patch.object(
                graph_preparation,
                "checkpoint_builder_issued_v11_lean_review_graph",
            ) as checkpoint,
        ):
            with self.assertRaisesRegex(ValueError, "changed during graph preparation"):
                graph_preparation.prepare_v11_lean_review_graph(
                    self.root, self.paper
                )

        checkpoint.assert_not_called()

    def test_pre_review_graph_reacquires_once_after_stale_carrier(self) -> None:
        spec = "Fixture.SourceSpec"
        cached_context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            statement_map={"items": {}},
        )
        cached_context.changed_input_paths.return_value = ()
        fresh_context = mock.Mock(
            v11_lean_claim_graph_selected=True,
            statement_map={"items": {}},
        )
        fresh_context.changed_input_paths.return_value = ()
        fresh_context.runtime_cache_diagnostics.return_value = {
            "v11_graph_carrier_reuses": 0,
        }
        route_set = mock.Mock()
        route_set.result_specifications.return_value = (spec,)
        provider = mock.Mock()
        provider.finalize_unchanged.return_value = True
        surface = graph_preparation.V11LeanReviewSurface(
            semantic_targets={spec: {"display": "Prop"}},
            paper_prerequisites=(),
            library_prerequisites=(),
            source_declarations={},
            library_source_declarations={},
            semantic_contracts={},
            declaration_inventory={"schema": 1},
            module_sources={},
            build_input_provider=provider,
            graph_request={"schema": 4, "specification_names": [spec]},
        )
        reference = {
            "schema": 1,
            "kind": "v11_lean_review_graph",
            "path": ".lake/closeout-objects/graph.json",
            "sha256": "a" * 64,
        }
        with (
            mock.patch.object(
                graph_preparation,
                "build_current_v11_context_with_graph_checkpoint",
                return_value=cached_context,
            ),
            mock.patch.object(
                graph_preparation,
                "build_current_v11_evidence_run_context",
                return_value=fresh_context,
            ) as reacquire,
            mock.patch.object(
                graph_preparation.EvidenceRouteSet,
                "from_source_map",
                return_value=route_set,
            ),
            mock.patch.object(
                graph_preparation,
                "build_accepting_v11_review_surface",
                side_effect=(
                    graph_preparation.V11LeanReviewGraphCarrierMismatch(
                        "stale carrier"
                    ),
                    surface,
                ),
            ) as acquire,
            mock.patch.object(
                graph_preparation,
                "checkpoint_builder_issued_v11_lean_review_graph",
                return_value=reference,
            ) as checkpoint,
        ):
            prepared = dict(
                graph_preparation.prepare_v11_lean_review_graph(
                    self.root, self.paper
                )
            )

        reacquire.assert_called_once_with(
            self.paper, repository_root=self.root
        )
        self.assertEqual(acquire.call_count, 2)
        acquire.assert_has_calls(
            [
                mock.call(
                    self.root, self.paper, (spec,), context=cached_context
                ),
                mock.call(
                    self.root, self.paper, (spec,), context=fresh_context
                ),
            ]
        )
        checkpoint.assert_called_once_with(
            self.paper,
            fresh_context,
            repository_root=self.root,
        )
        self.assertFalse(prepared["checkpoint_reused"])

    def test_graph_identity_ignores_source_quote_but_binds_typed_route(self) -> None:
        quote = "The source theorem."
        item = {
            "claim_bearing": True,
            "source_kind": "theorem",
            "inventory_role": "named_result",
            "source_anchor_evidence": [
                {
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
            "semantic_contract": {
                "spec_declaration": "Fixture.SourceSpec",
                "evidence_declaration": "Fixture.SourceProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        source_map = {"items": {"theorem": item}}
        baseline = graph_contract.typed_route_projection(source_map)

        changed_quote_map = json.loads(json.dumps(source_map))
        changed_quote = "The source theorem, with a corrected citation."
        changed_quote_map["items"]["theorem"]["source_anchor_evidence"] = [
            {
                "quoted_text": changed_quote,
                "quoted_text_sha256": hashlib.sha256(
                    changed_quote.encode("utf-8")
                ).hexdigest(),
            }
        ]
        changed_quote_projection = graph_contract.typed_route_projection(
            changed_quote_map
        )
        self.assertEqual(changed_quote_projection, baseline)

        candidate_review_map = json.loads(json.dumps(source_map))
        candidate_review_map["source_named_result_inventory_review"] = {
            "complete": True,
            "candidate_presentations": [
                {
                    "id": "open_question",
                    "scope_disposition": "deep_audit_material",
                    "source_anchor": {"quoted_text": "An open question."},
                }
            ],
        }
        self.assertEqual(
            graph_contract.typed_route_projection(candidate_review_map),
            baseline,
        )

        changed_route_map = json.loads(json.dumps(source_map))
        changed_route_map["items"]["theorem"]["semantic_contract"][
            "evidence_declaration"
        ] = "Fixture.DifferentProof"
        changed_route_projection = graph_contract.typed_route_projection(
            changed_route_map
        )
        self.assertNotEqual(changed_route_projection, baseline)

    def test_v11_surface_does_not_admit_a_packet_cache_without_native_graph(self) -> None:
        """Presentation caches cannot replace Lean declaration authority."""

        self._select_v11()
        spec = "Fixture.SourceSpec"
        source_item = {
            "semantic_contract": {
                "spec_declaration": spec,
                "evidence_declaration": "Fixture.SourceProof",
                "evidence_mode": "proves",
            }
        }
        self._write_json(
            self.audit_dir / "paper_statement_map.json",
            {"items": {"source": source_item}},
        )
        context, _calls = self._build_context()
        route = mock.Mock(
            source_item_id="source",
            spec_declaration=spec,
            evidence_declaration="Fixture.SourceProof",
            evidence_mode="proves",
        )
        route_set = mock.Mock()
        route_set.result_route_by_specification.return_value = {spec: route}
        route_set.source_semantic_declarations.return_value = ()

        with (
            mock.patch.object(
                review_surface,
                "_current_packet_lean_cache",
                side_effect=AssertionError("packet cache gained accepting authority"),
            ),
            mock.patch.object(
                evidence.EvidenceRouteSet, "from_source_map", return_value=route_set
            ),
        ):
            with self.assertRaisesRegex(ValueError, "import-closure receipt"):
                review_surface.build_accepting_v11_review_surface(
                    evidence.ROOT,
                    self.paper,
                    [spec],
                    context=context,
                )

    def test_source_proof_obligation_projection_runs_once_per_exact_map(self) -> None:
        """Repeated strict lanes share source-index selection, not its verdict."""

        context, _calls = self._build_context()
        payload = {
            "items": {
                "result": {
                    "claim_bearing": True,
                    "source_kind": "theorem",
                }
            }
        }
        selected = mock.Mock(return_value={"result"})
        projected = mock.Mock(return_value=dict(payload["items"]))
        with (
            mock.patch.object(
                source_manifest,
                "source_coverage_mode_from_map",
                return_value=("named_theoretical_statements", ""),
            ),
            mock.patch.object(
                source_manifest,
                "_source_index_byte_pinned_anchor_item_ids_uncached",
                selected,
            ),
            mock.patch.object(
                source_manifest,
                "source_named_result_environment_kinds_from_map",
                return_value=set(),
            ),
            mock.patch.object(
                source_manifest,
                "filter_source_map_items_for_proof_obligations",
                projected,
            ),
        ):
            first = evidence._source_map_proof_obligation_items(
                self.paper, payload, context=context
            )
            second = evidence._source_map_proof_obligation_items(
                self.paper, payload, context=context
            )
            self.assertEqual(first, second)
            selected.assert_called_once()
            projected.assert_called_once()

            copied = replace(context)
            self.assertFalse(copied.issued_by_builder)
            evidence._source_map_proof_obligation_items(
                self.paper, payload, context=copied
            )

        self.assertEqual(selected.call_count, 2)
        self.assertEqual(projected.call_count, 2)

    def test_source_index_projection_runs_once_for_exact_transaction_map(self) -> None:
        """All strict consumers share one source-only reconciliation result."""

        context, _calls = self._build_context()
        payload = context.statement_map_snapshot.payload
        self.assertIsInstance(payload, dict)
        selector = mock.Mock(return_value={"source-result"})
        with mock.patch.object(
            source_manifest,
            "_source_index_byte_pinned_anchor_item_ids_uncached",
            selector,
        ):
            first = source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                context=context,
            )
            first.clear()
            self.assertEqual(
                source_manifest.source_index_byte_pinned_anchor_item_ids(
                    self.paper,
                    payload,
                    "named_theoretical_statements",
                    context=context,
                ),
                {"source-result"},
            )
            selector.assert_called_once()

            copied = replace(context)
            self.assertFalse(copied.issued_by_builder)
            source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                context=copied,
            )
            source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                context=copied,
            )
            self.assertEqual(selector.call_count, 3)

            source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                context=context,
                file_bytes_override={},
            )
            self.assertEqual(selector.call_count, 4)

            source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                {"items": {"different": {}}},
                "named_theoretical_statements",
                context=context,
            )
            self.assertEqual(selector.call_count, 5)

            source_manifest.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                repository_root=self.root,
                context=context,
            )
            self.assertEqual(selector.call_count, 6)

    def test_source_manifest_keeps_the_raw_map_for_nested_surface_projection(self) -> None:
        """A derived subset cannot trigger a second source-index reconciliation."""

        context, _calls = self._build_context()
        payload = context.statement_map_snapshot.payload
        self.assertIsInstance(payload, dict)
        scoped_payload = {"items": {}}
        semantic_surface = mock.Mock(return_value=[])
        with (
            mock.patch.object(
                source_manifest, "source_map_scope_integrity_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest,
                "source_coverage_mode_findings",
                return_value=("named_theoretical_statements", []),
            ),
            mock.patch.object(
                source_manifest, "source_artifact_pin_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest, "source_named_result_inventory_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest,
                "scoped_source_map_payload",
                return_value=(scoped_payload, {}),
            ),
            mock.patch.object(
                source_manifest, "source_anchor_evidence_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest, "semantic_context_requirement_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest,
                "user_approved_scope_exclusion_map_findings",
                return_value=[],
            ),
            mock.patch.object(
                source_manifest, "corrected_source_statement_map_findings", return_value=[]
            ),
            mock.patch.object(
                source_manifest,
                "semantic_surface_inventory_findings",
                semantic_surface,
            ),
        ):
            self.assertEqual(
                source_manifest.check_source_manifest(
                    self.paper,
                    "formalized",
                    context=context,
                ),
                [],
            )

        semantic_surface.assert_called_once_with(
            self.paper,
            "formalized",
            payload,
            context=context,
        )
        self.assertIs(semantic_surface.call_args.args[2], payload)

    def test_route_preflight_consumes_the_exact_evidence_context(self) -> None:
        """The cheap route gate freezes inputs before expensive Lean work."""

        context, _calls = self._build_context()
        correspondence = mock.Mock(return_value=[])
        repaired = mock.Mock(return_value=[])
        with (
            mock.patch.object(audit_repository, "PAPERS", self.root / "papers"),
            mock.patch.object(
                evidence,
                "source_spec_correspondence_inventory_findings",
                correspondence,
            ),
            mock.patch.object(
                source_manifest,
                "repaired_source_defect_route_preflight_findings",
                repaired,
            ),
        ):
            self.assertEqual(
                audit_repository.paper_closeout_fast_route_schema_findings(
                    self.paper.name,
                    context=context,
                ),
                [],
            )

        correspondence.assert_called_once_with(
            self.paper,
            "formalized",
            require_source_bytes=False,
            context=context,
        )
        repaired.assert_called_once_with(
            self.paper,
            "formalized",
            context=context,
        )

    def test_builder_issues_one_identity_context_for_nested_current_lanes(self) -> None:
        """The strict fingerprint gate is not replayed for each overlay lane."""

        self._write_current_source_record_with_map_pin()
        context, calls = self._build_context()
        identity, _corrected, judgments, _watch = calls
        state = context.require_legacy_source_record_state()
        self.assertIsNotNone(state.source_record_identity_context)
        self.assertFalse(isinstance(state.source_record_identity_context, dict))
        identity.assert_called_once()
        self.assertIs(
            judgments.call_args.kwargs["source_record_identity_context"],
            state.source_record_identity_context,
        )

    def test_stale_identity_skips_all_unusable_derived_materialization(self) -> None:
        diagnostics: dict[str, int] = {}
        identity_error = "source-record input fingerprint is stale"
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                return_value=identity_error,
            ),
            mock.patch.object(
                evidence,
                "_source_record_audit_identity_error",
                return_value=identity_error,
            ),
            mock.patch.object(
                evidence,
                "_corrected_model_scope_contract_findings",
            ) as corrected_scope,
            mock.patch.object(
                evidence,
                "load_configured_assumption_formalization_regularity_context",
            ) as regularity,
            mock.patch.object(
                evidence,
                "source_record_administrative_projection_rebind_context",
            ) as administrative_rebind,
            mock.patch.object(
                evidence,
                "_current_source_record_judgment_items",
            ) as judgments,
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            context = evidence.build_evidence_run_context(
                self.paper, diagnostics=diagnostics
            )

        state = context.require_legacy_source_record_state()
        self.assertEqual(state.source_record_identity_error, identity_error)
        self.assertFalse(context.corrected_scope_current)
        self.assertEqual(state.current_source_record_judgments, {})
        regularity.assert_not_called()
        administrative_rebind.assert_not_called()
        judgments.assert_not_called()
        corrected_scope.assert_not_called()
        self.assertNotIn(
            evidence.EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE,
            diagnostics,
        )
        self.assertNotIn(
            evidence.EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS,
            diagnostics,
        )

    def test_absent_semantic_contract_replay_still_runs_fingerprint(self) -> None:
        """An absent optional replay is not a reason to skip currentness work."""

        self._write_current_source_record_with_map_pin()
        fingerprint = mock.Mock(return_value="")
        watch = mock.Mock(return_value="stable-watch")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                watch,
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", return_value=""
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", return_value={}
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertEqual(
            context.require_legacy_source_record_state().semantic_contract_revalidation_error,
            "",
        )
        fingerprint.assert_called_once()
        watch.assert_called_once()

    def test_current_semantic_authority_skips_duplicate_identity_helper(self) -> None:
        """One completed Lean pass is reused inside the exact transaction."""

        self._write_current_source_record_with_map_pin()
        authority = object()
        fingerprint = mock.Mock(
            side_effect=AssertionError("semantic helper must not rerun")
        )
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "load_current_semantic_reuse_authority",
                return_value=authority,
            ),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", return_value=""
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", return_value={}
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertIs(
            context.require_legacy_source_record_state().semantic_reuse_authority,
            authority,
        )
        fingerprint.assert_not_called()

    def test_malformed_semantic_contract_replay_skips_fingerprint(self) -> None:
        """A present invalid replay fails before the costly identity subprocess."""

        self._write_current_source_record_with_map_pin()
        artifact = self.audit_dir / "source_record_semantic_contract_revalidation.json"
        self._write_json(artifact, {"malformed": True})
        fingerprint = mock.Mock(return_value="")
        watch = mock.Mock(return_value="stable-watch")
        identity = mock.Mock(return_value="semantic replay rejected")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                watch,
            ),
            mock.patch.object(evidence, "_source_record_audit_identity_error", identity),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        state = context.require_legacy_source_record_state()
        self.assertIn(
            "semantic-contract revalidation artifact has unsupported fields",
            state.semantic_contract_revalidation_error,
        )
        fingerprint.assert_not_called()
        watch.assert_not_called()
        self.assertEqual(
            identity.call_args.kwargs[
                "prevalidated_semantic_contract_revalidation_error"
            ],
            state.semantic_contract_revalidation_error,
        )

    def test_exact_input_change_fails_closed(self) -> None:
        diagnostics: dict[str, int] = {}
        context, _calls = self._build_context(diagnostics)
        self._write_json(
            self.audit_dir / "source_record_match_llm.json",
            {"items": {"changed": {}}},
        )

        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(
                context, diagnostics=diagnostics
            )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("exact inputs changed", findings[0].message)
        self.assertEqual(
            diagnostics[evidence.EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS], 1
        )

    def test_non_json_evidence_controls_use_the_frozen_bytes(self) -> None:
        assumptions = self.paper / "Assumptions.lean"
        assumptions.write_text(
            "axiom substantive_boundary : Prop\n", encoding="utf-8"
        )
        context, _calls = self._build_context()
        snapshot = context.json_snapshot(assumptions)
        self.assertIsNotNone(snapshot)
        assert snapshot is not None

        assumptions.write_text(
            "def transient_boundary : Prop := True\n", encoding="utf-8"
        )
        frozen_findings = evidence.check_vacuous_assumptions(
            self.paper,
            "formalized",
            source_bytes_override=snapshot.raw_bytes,
        )
        live_findings = evidence.check_vacuous_assumptions(
            self.paper,
            "formalized",
        )

        self.assertEqual(frozen_findings, [])
        self.assertEqual(len(live_findings), 1)
        self.assertIn("transient_boundary", live_findings[0].message)

    def test_configured_noncanonical_sidecar_is_frozen_and_watched(self) -> None:
        configured = self.audit_dir / "alternate" / "statement-review.json"
        configured_payload = {"items": {"opaque-row": {"judgment": "passes"}}}
        self._write_json(configured, configured_payload)
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "llm_statement_review": {
                        "match_judgment_file": (
                            "papers/Fixture/audit/alternate/statement-review.json"
                        )
                    }
                },
            },
        )

        context, _calls = self._build_context()

        self.assertEqual(context.json_payload(configured), configured_payload)
        self._write_json(configured, {"items": {"replacement": {}}})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("statement-review.json", findings[0].message)

    def test_default_administrative_rebind_creation_is_watched(self) -> None:
        rebind = (
            self.audit_dir
            / evidence.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        context, _calls = self._build_context()

        self._write_json(rebind, {"schema": "created-after-context"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(rebind.name, findings[0].message)

    def test_semantic_rebind_authority_is_frozen_and_watched(self) -> None:
        rebind = self.audit_dir / "source_record_semantic_rebind.json"
        self._write_json(rebind, {"schema": "initial-semantic-rebind"})
        context, _calls = self._build_context()
        snapshot = context.json_snapshot(rebind)
        self.assertIsNotNone(snapshot)
        assert snapshot is not None
        self.assertEqual(snapshot.raw_bytes, rebind.read_bytes())

        self._write_json(rebind, {"schema": "changed-semantic-rebind"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(rebind.name, findings[0].message)

    def test_semantic_rebind_declared_provenance_graph_is_frozen_and_watched(self) -> None:
        """The indirect source-record authority cannot reread a mutable parent.

        The test deliberately uses opaque filenames and a nested ``bytes_sha256``
        record.  Discovery is therefore through the typed byte-pinned graph,
        not through a sidecar basename or a judgment/function name.
        """

        root = self.audit_dir / "source_record_semantic_rebind.json"
        parent = self.audit_dir / "opaque-parent.json"
        leaf = self.audit_dir / "opaque-leaf.json"
        self._write_json(leaf, {"immutable": "leaf"})
        leaf_digest = hashlib.sha256(leaf.read_bytes()).hexdigest()
        self._write_json(
            parent,
            {
                "nested_provenance": {
                    "path": "audit/opaque-leaf.json",
                    "bytes_sha256": leaf_digest,
                }
            },
        )
        parent_digest = hashlib.sha256(parent.read_bytes()).hexdigest()
        self._write_json(
            root,
            {
                "prior_raw_audit": {
                    "path": "audit/opaque-parent.json",
                    "file_sha256": parent_digest,
                }
            },
        )

        context, _calls = self._build_context()
        self.assertIsNotNone(context.json_snapshot(root))
        self.assertIsNotNone(context.json_snapshot(parent))
        self.assertIsNotNone(context.json_snapshot(leaf))

        self._write_json(leaf, {"immutable": "changed"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(leaf.name, findings[0].message)

    def test_administrative_rebind_validator_receives_exact_snapshot_bytes(
        self,
    ) -> None:
        rebind = (
            self.audit_dir
            / evidence.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        self._write_json(rebind, {"schema": "exact-receipt"})

        with mock.patch.object(
            evidence,
            "load_administrative_projection_rebind_context",
            return_value=(None, rebind, ""),
        ) as loader:
            self._build_context()

        kwargs = loader.call_args.kwargs
        self.assertEqual(kwargs["receipt_bytes_override"], rebind.read_bytes())
        self.assertEqual(
            kwargs["raw_audit_bytes_override"],
            (self.audit_dir / "source_record_audit.json").read_bytes(),
        )
        self.assertEqual(
            kwargs["statement_map_bytes_override"],
            (self.audit_dir / "paper_statement_map.json").read_bytes(),
        )

    def test_regularity_validator_receives_exact_snapshot_inputs(self) -> None:
        regularity = (
            self.paper
            / evidence.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
        )
        self._write_json(regularity, {"schema": "exact-regularity"})
        source = self.paper / "source.txt"
        source.write_text("source bytes\n", encoding="utf-8")
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD: (
                    evidence.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
                ),
            },
        )

        with mock.patch.object(
            evidence,
            "load_configured_assumption_formalization_regularity_context",
            return_value=(None, ""),
        ) as loader:
            self._build_context()

        kwargs = loader.call_args.kwargs
        self.assertEqual(kwargs["ledger_bytes_override"], regularity.read_bytes())
        self.assertEqual(
            kwargs["source_artifact_sha256_override"],
            hashlib.sha256(source.read_bytes()).hexdigest(),
        )

    def test_corrected_scope_reference_artifacts_are_acquired_by_builder(self) -> None:
        approval = self.paper / "docs" / "approval.md"
        archive = self.paper / "source.txt"
        contract = self.audit_dir / "corrected.json"
        approval.parent.mkdir(parents=True)
        approval.write_bytes(b"approved\n")
        archive.write_bytes(b"archived source\n")
        self._write_json(contract, {"schema": "fixture"})
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "formalization_scope": {
                    "kind": evidence.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                    "approval": {"artifact_path": "docs/approval.md"},
                    "base_archive": {"path": "source.txt"},
                    "semantic_contract": {"path": "audit/corrected.json"},
                },
            },
        )

        context, _calls = self._build_context()

        for path in (approval, archive, contract):
            captured = context.json_snapshot(path)
            self.assertIsNotNone(captured)
            assert captured is not None
            self.assertEqual(captured.raw_bytes, path.read_bytes())

    def test_corrected_scope_validator_uses_frozen_artifact_receipts(self) -> None:
        approval_path = (self.paper / "docs" / "approval.md").resolve()
        archive_path = (self.paper / "source.txt").resolve()
        contract_path = (self.audit_dir / "corrected.json").resolve()
        approval_sha = "1" * 64
        archive_sha = "2" * 64
        contract_sha = "3" * 64
        status = {
            "status": "formalized",
            "formalization_scope": {
                "kind": evidence.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                "scope_id": "opaque-scope",
                "scope_role": evidence.WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
                "whole_paper_closeout_claimed": True,
                "archival_equivalence_claimed": False,
                "target_result_declarations": ["Fixture.result"],
                "model_spec_declarations": ["Fixture.Model"],
                "correction_ids": ["opaque-correction"],
                "approval": {
                    "artifact_path": "docs/approval.md",
                    "artifact_sha256": approval_sha,
                    "recorded_at": "2026-08-02",
                    "statement": "approved corrected target",
                },
                "base_archive": {
                    "path": "source.txt",
                    "sha256": archive_sha,
                },
                "semantic_contract": {
                    "path": "audit/corrected.json",
                    "sha256": contract_sha,
                },
            },
            "governing_corrections": [
                {
                    "id": "opaque-correction",
                    "clause": "corrected clause",
                    "source_anchor": "source.txt:1-1",
                    "relation": "source correction",
                    "model_evidence": "Fixture.result",
                    "does_not_claim_archive_derivation": True,
                }
            ],
        }
        snapshots = {
            approval_path: evidence.EvidenceJSONSnapshot(
                approval_path, approval_sha, None
            ),
            archive_path: evidence.EvidenceJSONSnapshot(
                archive_path, archive_sha, None
            ),
            contract_path: evidence.EvidenceJSONSnapshot(
                contract_path, contract_sha, {"schema": "unsupported"}
            ),
        }

        with (
            mock.patch.object(
                evidence,
                "load_json",
                side_effect=AssertionError("frozen artifact must not be reread"),
            ),
            mock.patch.object(
                evidence,
                "sha256_file",
                side_effect=AssertionError("frozen artifact must not be rehashed"),
            ),
        ):
            findings = evidence._corrected_model_scope_contract_findings(
                self.paper,
                "formalized",
                status,
                audit_payload_override={},
                prevalidated_source_record_identity_error="stale fixture audit",
                artifact_snapshots_override=snapshots,
            )

        messages = [finding.message for finding in findings]
        self.assertFalse(any("artifact_path must name" in item for item in messages))
        self.assertFalse(any("base_archive.path must name" in item for item in messages))
        self.assertFalse(any("does not match its tracked artifact" in item for item in messages))
        self.assertTrue(any("unsupported schema" in item for item in messages))

    def test_watched_producer_change_fails_closed(self) -> None:
        context, _calls = self._build_context()
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="changed-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("producer/source watch digest changed", findings[0].message)

    def test_watch_ignores_scratch_but_tracks_fingerprint_inputs(self) -> None:
        interface = self.paper / "PaperInterface.lean"
        interface.write_text("theorem result : True := by trivial\n", encoding="utf-8")
        payload = {
            "source_record_input_fingerprint": {
                "review_interface_source": {
                    "path": "papers/Fixture/PaperInterface.lean",
                    "sha256": hashlib.sha256(interface.read_bytes()).hexdigest(),
                }
            }
        }
        with mock.patch.object(evidence, "ROOT", self.root):
            before = evidence._source_record_identity_process_watch_digest(
                self.paper, audit_payload=payload
            )
            scratch = self.paper / ".review_traces" / "interactive-cache.json"
            self._write_json(scratch, {"large": "non-authority"})
            archival = self.audit_dir / ".prior_raw_diagnostic.json"
            self._write_json(archival, {"large": "non-authority"})
            after_scratch = evidence._source_record_identity_process_watch_digest(
                self.paper, audit_payload=payload
            )
            interface.write_text(
                "theorem result : False := by contradiction\n",
                encoding="utf-8",
            )
            after_semantic_change = (
                evidence._source_record_identity_process_watch_digest(
                    self.paper, audit_payload=payload
                )
            )

        self.assertEqual(before, after_scratch)
        self.assertNotEqual(before, after_semantic_change)

    def test_context_payloads_are_recursively_immutable(self) -> None:
        context, _calls = self._build_context()
        state = context.require_legacy_source_record_state()
        audit_payload = state.inputs.audit_snapshot.payload
        with self.assertRaises(TypeError):
            audit_payload["paper"] = "Renamed"
        nested = audit_payload["nested"]
        assert isinstance(nested, dict)
        rows = nested["rows"]
        assert isinstance(rows, list)
        with self.assertRaises(TypeError):
            rows.append("forged-obligation")
        judgment = state.current_source_record_judgments[
            "content-addressed-obligation"
        ]
        with self.assertRaises(TypeError):
            judgment["classification"] = "forged-match"

    def test_final_mutation_check_hashes_bytes_without_reparsing_json(self) -> None:
        context, _calls = self._build_context()
        with (
            mock.patch.object(
                evidence.json,
                "loads",
                side_effect=AssertionError("final check must not parse JSON"),
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(findings, [])

    def test_freezing_current_judgments_preserves_loader_authentication(self) -> None:
        loaded = differential._LoadedSourceRecordDifferentialRevalidationItem(
            {
                differential.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD: {
                    "receipt": "content-addressed"
                }
            }
        )
        frozen = evidence._freeze_json(
            {"obligation": loaded}, preserve_dict_subclasses=True
        )
        item = frozen["obligation"]

        self.assertTrue(
            differential.is_loaded_source_record_differential_revalidation_item(
                item
            )
        )
        with self.assertRaises(TypeError):
            item["classification"] = "forged-match"

    def test_primary_closeout_receipt_skips_only_duplicate_missing_count(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context()

        before = evidence.check_source_record_judgments(
            self.paper, "formalized", context=context
        )
        self.assertEqual(len(before), 1)
        self.assertIn("lack current validated judgments", before[0].message)
        self.assertFalse(
            evidence._has_current_primary_closeout_source_record_judgment_receipt(
                context
            )
        )

        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        # Publishing cannot be requested by a caller-provided Boolean or list;
        # it requires the primary source gate's no-argument staged capability.
        self.assertFalse(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )
        self.assertTrue(
            evidence._has_current_primary_closeout_source_record_judgment_receipt(
                context
            )
        )

        self.assertEqual(
            evidence.check_source_record_judgments(
                self.paper, "formalized", context=context
            ),
            [],
        )

    def test_primary_closeout_receipt_remains_bound_to_its_issued_context(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context()
        other_context, _other_calls = self._build_context()
        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )

        self.assertEqual(
            evidence.check_source_record_judgments(
                self.paper, "formalized", context=context
            ),
            [],
        )
        other = evidence.check_source_record_judgments(
            self.paper, "formalized", context=other_context
        )
        self.assertEqual(len(other), 1)
        self.assertIn("lack current validated judgments", other[0].message)

    def test_primary_closeout_receipt_does_not_suppress_raw_identity_error(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context(
            identity_error="source-record input fingerprint is stale"
        )
        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )

        findings = evidence.check_source_record_judgments(
            self.paper, "formalized", context=context
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("cannot support current judgments", findings[0].message)
        self.assertIn("fingerprint is stale", findings[0].message)

    def test_run_rejects_a_context_not_issued_by_the_builder(self) -> None:
        context, _calls = self._build_context()
        self.assertIsInstance(context, evidence.LegacyEvidenceRunContext)
        self.assertNotIsInstance(context, evidence.V11EvidenceRunContext)
        legacy_state = context.require_legacy_source_record_state()
        forged = replace(
            context,
            legacy_state=replace(
                legacy_state,
                source_record_identity_error="",
            ),
        )
        self.assertTrue(context.issued_by_builder)
        self.assertFalse(forged.issued_by_builder)
        with (
            mock.patch.object(evidence, "paper_dirs", return_value=[self.paper]),
            mock.patch.object(evidence, "check_report_generator", return_value=[]),
            mock.patch.object(evidence, "lake_targets", return_value=(set(), set())),
        ):
            findings = evidence.run("Fixture", False, context=forged)

        self.assertEqual(len(findings), 1)
        self.assertIn("not issued", findings[0].message)


if __name__ == "__main__":
    unittest.main()
