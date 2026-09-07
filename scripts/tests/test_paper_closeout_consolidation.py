#!/usr/bin/env python3
"""Tests for the staged, single-process paper closeout gate."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

from scripts import (
    audit_conclusion_provenance,
    audit_evidence_integrity,
    audit_repository,
    paper_closeout_executor,
    source_record_differential_revalidation,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
)


def legacy_source_record_state(
    audit_payload: dict[str, object],
    *,
    audit_path: Path | None = None,
    match_path: Path | None = None,
    source_record_identity_error: str = "",
) -> types.SimpleNamespace:
    """Build an explicit typed legacy lane for consolidation fixtures."""

    return types.SimpleNamespace(
        inputs=types.SimpleNamespace(
            audit_snapshot=types.SimpleNamespace(
                path=(
                    audit_path
                    or Path("papers/Fixture/audit/source_record_audit.json")
                ),
                payload=audit_payload,
            ),
            match_snapshot=types.SimpleNamespace(
                path=(
                    match_path
                    or Path("papers/Fixture/audit/source_record_match_llm.json")
                ),
                payload={},
            ),
            audit_path_error="",
            match_path_error="",
        ),
        source_record_identity_error=source_record_identity_error,
        semantic_reuse_authority=None,
        current_source_record_judgments={},
    )


class PaperCloseoutConsolidationTests(unittest.TestCase):
    def run_closeout(
        self,
        *,
        closeout_trace: dict[str, object] | None = None,
        root_build_findings: list[audit_repository.Finding] | None = None,
    ) -> list[audit_repository.Finding]:
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[],
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository,
                "check_paper_root_build_closeout",
                return_value=(
                    [] if root_build_findings is None else root_build_findings
                ),
            ),
        ):
            return audit_repository.run(
                include_active=True,
                strict_style=False,
                paper_filter="Fixture",
                paper_closeout=True,
                closeout_trace=closeout_trace,
            )

    def test_consolidated_closeout_runs_all_lanes_in_one_process(self) -> None:
        evidence_finding = audit_evidence_integrity.Finding(
            "WARN", "Fixture", "papers/Fixture/status.json", "evidence warning"
        )
        conclusion_finding = audit_conclusion_provenance.Finding(
            "Fixture", "paper_theorem", "h", ("result",), "circular premise"
        )
        with (
            mock.patch.object(
                audit_repository, "check_machine_paper_status", return_value=[]
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[evidence_finding],
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
                return_value=[conclusion_finding],
            ) as conclusion_run,
        ):
            findings = self.run_closeout()

        evidence_run.assert_called_once_with(
            "Fixture",
            False,
            False,
            require_source_bytes=True,
            context=mock.ANY,
            diagnostics=mock.ANY,
        )
        conclusion_run.assert_called_once_with(
            "Fixture",
            evidence_context=mock.ANY,
            theorem_realization_component_prevalidated=False,
        )
        self.assertEqual([finding.severity for finding in findings], ["WARN", "ERROR"])
        self.assertIn("evidence integrity", findings[0].message)
        self.assertIn("conclusion provenance", findings[1].message)
        self.assertEqual(
            findings[1].path,
            audit_repository.PAPERS / "Fixture" / "PaperInterface.lean",
        )

    def test_stateful_cli_closeout_requires_a_planner_identity(self) -> None:
        with mock.patch.object(
            sys,
            "argv",
            ["audit_repository.py", "--paper", "Fixture", "--paper-closeout"],
        ), self.assertRaises(SystemExit) as raised:
            audit_repository.main()
        self.assertEqual(raised.exception.code, 2)

    def test_stateful_cli_closeout_rejects_an_unbound_plan_identity(self) -> None:
        identity = "a" * 64
        with (
            mock.patch.object(
                sys,
                "argv",
                [
                    "audit_repository.py",
                    "--paper",
                    "Fixture",
                    "--paper-closeout",
                    "--operational-plan-identity",
                    identity,
                ],
            ),
            mock.patch.object(
                audit_repository, "runtime_engine_registration_error", return_value=""
            ),
            mock.patch.object(
                audit_repository,
                "load_validated_closeout_plan_receipt",
                return_value=(None, "closeout plan receipt is missing"),
            ),
            mock.patch.object(
                audit_repository.CloseoutExecutionLease, "acquire"
            ) as acquire,
        ):
            self.assertEqual(audit_repository.main(), 6)

        acquire.assert_not_called()

    def test_stateful_current_cli_delegates_before_mixed_executor(self) -> None:
        identity = "b" * 64
        with tempfile.TemporaryDirectory() as temporary:
            papers = Path(temporary) / "papers"
            folder = papers / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}),
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "audit_repository.py",
                        "--paper",
                        "Fixture",
                        "--paper-closeout",
                        "--operational-plan-identity",
                        identity,
                    ],
                ),
                mock.patch(
                    "scripts.current_closeout.strict_runner.main",
                    return_value=17,
                ) as current,
                mock.patch.object(
                    audit_repository, "load_validated_closeout_plan_receipt"
                ) as legacy_plan,
            ):
                self.assertEqual(audit_repository.main(), 17)
        current.assert_called_once_with(
            [
                "--paper",
                "Fixture",
                "--operational-plan-identity",
                identity,
            ]
        )
        legacy_plan.assert_not_called()

    def test_no_state_current_cli_delegates_before_mixed_executor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            papers = Path(temporary) / "papers"
            folder = papers / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            with (
                mock.patch.object(audit_repository, "PAPERS", papers),
                mock.patch.object(
                    sys,
                    "argv",
                    [
                        "audit_repository.py",
                        "--paper",
                        "Fixture",
                        "--paper-closeout",
                        "--no-closeout-state",
                    ],
                ),
                mock.patch(
                    "scripts.current_closeout.strict_runner.main", return_value=19
                ) as current,
                mock.patch.object(
                    audit_repository, "load_validated_closeout_plan_receipt"
                ) as legacy_plan,
            ):
                self.assertEqual(audit_repository.main(), 19)

        current.assert_called_once_with(
            ["--paper", "Fixture", "--no-closeout-state"]
        )
        legacy_plan.assert_not_called()

    def test_strict_root_build_targets_only_the_paper_root(self) -> None:
        """The strict gate must compile the delivered paper target, not a wrapper."""

        completed = subprocess.CompletedProcess(
            args=["lake", "build", "+Fixture"], returncode=0, stdout="", stderr=""
        )
        with mock.patch.object(
            audit_repository.subprocess, "run", return_value=completed
        ) as run:
            findings = audit_repository.check_paper_root_build_closeout("Fixture")

        self.assertEqual(findings, [])
        run.assert_called_once_with(
            ["env", "LEAN_NUM_THREADS=1", "lake", "build", "+Fixture"],
            cwd=audit_repository.ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=900,
        )

    def test_strict_root_build_rejects_zero_exit_lean_panic(self) -> None:
        completed = subprocess.CompletedProcess(
            args=["lake", "build", "+Fixture"],
            returncode=0,
            stdout="Build completed successfully.\n",
            stderr="PANIC at Lean.Expr.appArg! Lean.Expr:926:15: application expected\nbacktrace:\n...",
        )
        with mock.patch.object(
            audit_repository.subprocess, "run", return_value=completed
        ):
            findings = audit_repository.check_paper_root_build_closeout("Fixture")

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("Lean PANIC output", findings[0].message)

    def test_closeout_trace_uses_the_authoritative_run(self) -> None:
        trace: dict[str, object] = {}
        with (
            mock.patch.object(
                audit_repository, "check_machine_paper_status", return_value=[]
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[],
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
                return_value=[],
            ),
        ):
            findings = self.run_closeout(closeout_trace=trace)

        self.assertEqual(findings, [])
        self.assertEqual(trace["schema"], 1)
        self.assertEqual(trace["paper"], "Fixture")
        stages = trace["stages_seconds"]
        self.assertIsInstance(stages, dict)
        assert isinstance(stages, dict)
        self.assertEqual(tuple(stages), STRICT_CLOSEOUT_EXECUTION_STAGES)
        stage_timings = trace["strict_stage_timings"]
        self.assertIsInstance(stage_timings, dict)
        assert isinstance(stage_timings, dict)
        self.assertEqual(tuple(stage_timings), STRICT_CLOSEOUT_EXECUTION_STAGES)
        for timing in stage_timings.values():
            self.assertIsInstance(timing, dict)
            assert isinstance(timing, dict)
            self.assertIsInstance(timing.get("started_at"), str)
            self.assertIsInstance(timing.get("finished_at"), str)
            self.assertIsInstance(timing.get("elapsed_seconds"), float)
        self.assertIsInstance(trace.get("started_at"), str)
        self.assertIsInstance(trace.get("finished_at"), str)
        self.assertEqual(trace["primary_paper_gate_phases_seconds"], {})
        counters = trace["evidence_counters"]
        self.assertIsInstance(counters, dict)
        assert isinstance(counters, dict)
        self.assertEqual(counters.get("evidence_contexts_built"), 1)
        self.assertEqual(counters.get("validation_cache_hits"), 0)
        self.assertEqual(counters.get("validation_cache_misses"), 1)
        self.assertEqual(counters.get("validation_cache_entries"), 1)

    def test_closeout_artifact_error_stops_before_exact_context(self) -> None:
        blocker = audit_repository.Finding(
            "ERROR",
            Path("papers/Fixture/docs/AGENT_SOURCE_AUDIT.md"),
            "holistic audit is incomplete",
        )
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[blocker],
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository, "build_paper_closeout_evidence_context"
            ) as build_context,
        ):
            findings = audit_repository.run(
                include_active=True,
                strict_style=False,
                paper_filter="Fixture",
                paper_closeout=True,
            )
        self.assertEqual(findings, [blocker])
        build_context.assert_not_called()

    def test_document_gate_receives_policy_from_frozen_plan_surface(self) -> None:
        blocker = audit_repository.Finding(
            "ERROR",
            Path("papers/Fixture/docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json"),
            "one additional independent reviewer is required",
        )
        assurance = {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": 2,
        }
        with (
            mock.patch.object(
                paper_closeout_executor,
                "resolved_plan_final_holistic_audit_surface",
                return_value={"review_policy_assurance": assurance},
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[blocker],
            ) as document_gate,
            mock.patch.object(
                audit_repository, "build_paper_closeout_evidence_context"
            ) as build_context,
        ):
            findings = paper_closeout_executor.execute_paper_closeout(
                audit_repository,
                paper_filter="Fixture",
                library_premise_audit=False,
                require_source_bytes=True,
                deep_paper_prose=False,
                closeout_trace=None,
                closeout_progress_callback=None,
                operational_plan_identity="a" * 64,
                operational_plan_receipt={
                    "schema": 7,
                    "final_holistic_audit_surface_sha256": "b" * 64,
                    "all_selected_semantic_review_sha256": "c" * 64,
                },
            )

        self.assertEqual(findings, [blocker])
        self.assertEqual(
            document_gate.call_args.kwargs[
                "final_holistic_review_policy_assurance"
            ],
            assurance,
        )
        self.assertEqual(
            document_gate.call_args.kwargs[
                "all_selected_semantic_review_sha256"
            ],
            "c" * 64,
        )
        build_context.assert_not_called()

    def test_route_schema_error_uses_frozen_inputs_and_stops_before_lean(self) -> None:
        blocker = audit_repository.Finding(
            "ERROR",
            Path("papers/Fixture/audit/paper_statement_map.json"),
            "repaired source defect has no typed route",
        )
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[],
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[blocker],
            ),
            mock.patch.object(
                audit_repository,
                "build_paper_closeout_evidence_context",
                return_value=mock.Mock(),
            ) as build_context,
            mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "from_exact_evidence_context",
            ) as build_lean_context,
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ) as final_input_check,
        ):
            findings = audit_repository.run(
                include_active=True,
                strict_style=False,
                paper_filter="Fixture",
                paper_closeout=True,
            )
        self.assertEqual(findings, [blocker])
        build_context.assert_called_once()
        build_lean_context.assert_not_called()
        final_input_check.assert_called_once()

    def test_lean_context_error_still_finalizes_frozen_evidence_inputs(self) -> None:
        evidence_context = mock.Mock()
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[],
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "build_paper_closeout_evidence_context",
                return_value=evidence_context,
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "from_exact_evidence_context",
                side_effect=RuntimeError("Lean graph unavailable"),
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ) as final_input_check,
        ):
            findings = audit_repository.run(
                include_active=True,
                strict_style=False,
                paper_filter="Fixture",
                paper_closeout=True,
            )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("Lean-backed closeout context", findings[0].message)
        final_input_check.assert_called_once_with(
            evidence_context,
            diagnostics=mock.ANY,
            build_input_provider=None,
        )

    def test_primary_error_skips_later_expensive_lanes(self) -> None:
        primary = audit_repository.Finding(
            "ERROR", Path("papers/Fixture/status.json"), "primary error"
        )
        with (
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                return_value=[primary],
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
        ):
            findings = self.run_closeout()

        self.assertEqual(findings, [primary])
        evidence_run.assert_not_called()
        conclusion_run.assert_not_called()

    def test_root_build_failure_stops_before_primary_and_evidence_lanes(self) -> None:
        root_failure = audit_repository.Finding(
            "ERROR", Path("papers/Fixture.lean"), "focused paper-root build failed"
        )
        with (
            mock.patch.object(
                audit_repository, "check_machine_paper_status"
            ) as primary_gate,
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
        ):
            findings = self.run_closeout(root_build_findings=[root_failure])

        self.assertEqual(findings, [root_failure])
        primary_gate.assert_not_called()
        evidence_run.assert_not_called()
        conclusion_run.assert_not_called()

    def test_source_record_map_transaction_skew_stops_before_primary_gate(
        self,
    ) -> None:
        """A stale raw/map pair produces one root finding, not child cascades."""

        evidence_context = types.SimpleNamespace(
            legacy_source_record_state=legacy_source_record_state(
                {"paper_statement_map_sha256": "a" * 64},
                source_record_identity_error=(
                    "paper_statement_map_sha256 is stale for the current "
                    "paper_statement_map.json"
                ),
            ),
            paper_statement_map_sha256="b" * 64,
        )
        run_context = mock.Mock()
        with (
            mock.patch.object(
                audit_repository,
                "build_paper_closeout_evidence_context",
                return_value=evidence_context,
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "from_exact_evidence_context",
                return_value=run_context,
            ),
            mock.patch.object(
                audit_repository, "check_machine_paper_status"
            ) as primary_gate,
            mock.patch.object(
                audit_repository, "check_paper_root_build_closeout"
            ) as root_build,
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ) as finalize,
        ):
            findings = self.run_closeout()

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("closeout stopped before derived validation", findings[0].message)
        self.assertIn("does not issue or revise human review receipts", findings[0].message)
        primary_gate.assert_not_called()
        root_build.assert_not_called()
        evidence_run.assert_not_called()
        conclusion_run.assert_not_called()
        finalize.assert_called_once_with(
            evidence_context,
            diagnostics=mock.ANY,
            build_input_provider=run_context.build_input_provider,
        )

    def test_source_record_map_preflight_preserves_valid_semantic_reuse(
        self,
    ) -> None:
        """A byte-only map change remains reusable when freshness accepts it."""

        evidence_context = types.SimpleNamespace(
            legacy_source_record_state=legacy_source_record_state(
                {"paper_statement_map_sha256": "a" * 64}
            ),
            paper_statement_map_sha256="b" * 64,
        )

        self.assertEqual(
            audit_repository.paper_closeout_source_record_transaction_skew_findings(
                "Fixture", evidence_context
            ),
            [],
        )
        self.assertEqual(
            audit_repository.paper_closeout_evidence_context_prebuild_findings(
                "Fixture", evidence_context
            ),
            [],
        )

    def test_exact_current_v11_context_supersedes_historical_raw_map_skew(
        self,
    ) -> None:
        evidence_context = types.SimpleNamespace(
            legacy_source_record_state=legacy_source_record_state(
                {"paper_statement_map_sha256": "a" * 64},
                source_record_identity_error=(
                    "semantic-contract revalidation artifact has stale "
                    "paper-statement-map bytes"
                ),
            ),
            paper_statement_map_sha256="b" * 64,
        )
        run_context = types.SimpleNamespace(
            issued_by_builder=True,
            evidence_context=evidence_context,
            selected_v11_closeout=True,
            current_v11_closeout=True,
            v11_direct_semantic_review_current=True,
        )

        self.assertEqual(
            audit_repository.paper_closeout_evidence_context_prebuild_findings(
                "Fixture",
                evidence_context,
                run_context=run_context,
            ),
            [],
        )

        run_context.selected_v11_closeout = False
        run_context.current_v11_closeout = False
        run_context.v11_direct_semantic_review_current = False
        findings = (
            audit_repository.paper_closeout_evidence_context_prebuild_findings(
                "Fixture",
                evidence_context,
                run_context=run_context,
            )
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("closeout stopped before derived validation", findings[0].message)

    def test_selected_invalid_v11_stops_with_its_own_error_without_legacy_fallback(
        self,
    ) -> None:
        evidence_context = types.SimpleNamespace(
            audit_payload=None,
            paper_statement_map_sha256="b" * 64,
            source_record_identity_error="legacy source record is absent",
            audit_snapshot=types.SimpleNamespace(
                path=Path("papers/Fixture/audit/source_record_audit.json")
            ),
        )
        run_context = types.SimpleNamespace(
            issued_by_builder=True,
            evidence_context=evidence_context,
            selected_v11_closeout=True,
            current_v11_closeout=False,
            v11_lean_claim_graph_selected=True,
            v11_direct_semantic_review_current=False,
            v11_direct_semantic_review_error=(
                "material library review is stale for one declaration"
            ),
        )

        findings = audit_repository.paper_closeout_evidence_context_prebuild_findings(
            "Fixture",
            evidence_context,
            run_context=run_context,
        )

        self.assertEqual(len(findings), 1)
        self.assertIn("selected v11 semantic lane is not current", findings[0].message)
        self.assertIn("material library review is stale", findings[0].message)
        self.assertNotIn("legacy source record is absent", findings[0].message)
        self.assertIn("not fallback acceptance evidence", findings[0].message)

    def test_legacy_structural_inventory_never_bypasses_currentness(
        self,
    ) -> None:
        historical = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
        }
        context = types.SimpleNamespace(
            evidence_context=types.SimpleNamespace(audit_payload=historical),
            current_source_record_audit=lambda: (
                None,
                "semantic-contract revalidation artifact has stale paper map bytes",
            ),
        )

        payload, error = audit_repository.source_record_structural_payload_for_closeout(
            context,
        )
        self.assertIsNone(payload)
        self.assertIn("stale paper map bytes", error)

    def test_current_v11_raw_source_record_has_no_competing_semantic_lane(
        self,
    ) -> None:
        current = audit_repository.source_record_evidence_role_policy(
            exact_v11_direct_current=True
        )
        self.assertFalse(current.raw_semantic_authority)
        self.assertFalse(current.raw_auxiliary_routing_authority)

        legacy = audit_repository.source_record_evidence_role_policy(
            exact_v11_direct_current=False
        )
        self.assertTrue(legacy.raw_semantic_authority)
        self.assertTrue(legacy.raw_auxiliary_routing_authority)

    def test_source_record_identity_error_stops_before_focused_build(
        self,
    ) -> None:
        """A non-map raw identity failure must not pay for a Lean build."""

        evidence_context = types.SimpleNamespace(
            legacy_source_record_state=legacy_source_record_state(
                {"paper_statement_map_sha256": "a" * 64},
                source_record_identity_error=(
                    "source_record_input_fingerprint is stale for current source inputs"
                ),
            ),
            paper_statement_map_sha256="a" * 64,
        )
        run_context = mock.Mock()
        with (
            mock.patch.object(
                audit_repository,
                "check_dag_and_validation_report_closeout",
                return_value=[],
            ),
            mock.patch.object(
                paper_closeout_executor,
                "source_intake_readiness",
                return_value={"ready": True, "errors": []},
            ),
            mock.patch.object(
                audit_repository,
                "build_paper_closeout_evidence_context",
                return_value=evidence_context,
            ),
            mock.patch.object(
                audit_repository,
                "paper_closeout_fast_route_schema_findings",
                return_value=[],
            ),
            mock.patch.object(
                audit_repository.PaperCloseoutRunContext,
                "from_exact_evidence_context",
                return_value=run_context,
            ),
            mock.patch.object(
                audit_repository, "check_paper_root_build_closeout"
            ) as root_build,
            mock.patch.object(
                audit_repository, "check_machine_paper_status"
            ) as primary_gate,
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[],
            ) as finalize,
        ):
            findings = audit_repository.run(
                include_active=True,
                strict_style=False,
                paper_filter="Fixture",
                paper_closeout=True,
            )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("before focused Lean build", findings[0].message)
        self.assertIn("source-record identity is invalid", findings[0].message)
        root_build.assert_not_called()
        primary_gate.assert_not_called()
        evidence_run.assert_not_called()
        conclusion_run.assert_not_called()
        finalize.assert_called_once_with(
            evidence_context,
            diagnostics=mock.ANY,
            build_input_provider=run_context.build_input_provider,
        )

    def test_strict_source_handoff_publishes_only_after_clean_primary_gate(self) -> None:
        captured: dict[str, object] = {}

        def green_primary(**kwargs: object) -> list[audit_repository.Finding]:
            context = kwargs["run_context"]
            assert isinstance(context, audit_repository.PaperCloseoutRunContext)
            context.stage_strict_v11_source_record_judgment_handoff()
            captured["context"] = context.evidence_context
            return []

        def evidence_runner(
            _paper: str,
            _release: bool,
            _include_source_obligations: bool,
            **kwargs: object,
        ) -> list[audit_evidence_integrity.Finding]:
            context = kwargs["context"]
            self.assertIs(context, captured["context"])
            self.assertTrue(
                audit_evidence_integrity
                ._has_current_primary_closeout_source_record_judgment_receipt(context)
            )
            return []

        with (
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                side_effect=green_primary,
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                side_effect=evidence_runner,
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
                return_value=[],
            ),
        ):
            self.assertEqual(self.run_closeout(), [])

    def test_primary_error_does_not_publish_staged_strict_source_handoff(self) -> None:
        captured: dict[str, object] = {}
        primary = audit_repository.Finding(
            "ERROR", Path("papers/Fixture/status.json"), "primary error"
        )

        def red_primary(**kwargs: object) -> list[audit_repository.Finding]:
            context = kwargs["run_context"]
            assert isinstance(context, audit_repository.PaperCloseoutRunContext)
            context.stage_strict_v11_source_record_judgment_handoff()
            captured["context"] = context.evidence_context
            return [primary]

        with (
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                side_effect=red_primary,
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
            ) as evidence_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
        ):
            findings = self.run_closeout()

        self.assertEqual(findings, [primary])
        evidence_run.assert_not_called()
        conclusion_run.assert_not_called()
        context = captured["context"]
        self.assertFalse(
            audit_evidence_integrity
            ._has_current_primary_closeout_source_record_judgment_receipt(context)
        )

    def test_evidence_error_skips_conclusion_lane(self) -> None:
        evidence_error = audit_evidence_integrity.Finding(
            "ERROR", "Fixture", "papers/Fixture/status.json", "stale evidence"
        )
        with (
            mock.patch.object(
                audit_repository, "check_machine_paper_status", return_value=[]
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[evidence_error],
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
            ) as conclusion_run,
        ):
            findings = self.run_closeout()

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        conclusion_run.assert_not_called()

    def test_snapshot_transfer_failure_skips_conclusion_and_still_finalizes(
        self,
    ) -> None:
        mutation = audit_repository.Finding(
            "ERROR",
            Path("papers/Fixture/status.json"),
            "transaction changed",
        )
        with (
            mock.patch.object(
                audit_repository, "check_machine_paper_status", return_value=[]
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[],
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "source_record_audit_snapshot_from_evidence_context",
                return_value=(None, "configured judgment path escaped"),
            ),
            mock.patch.object(
                audit_conclusion_provenance, "_audit_paper"
            ) as conclusion_run,
            mock.patch.object(
                audit_repository,
                "paper_closeout_context_mutation_findings",
                return_value=[mutation],
            ) as finalize,
        ):
            findings = self.run_closeout()

        conclusion_run.assert_not_called()
        finalize.assert_called_once_with(
            mock.ANY,
            diagnostics=mock.ANY,
            build_input_provider=mock.ANY,
        )
        self.assertEqual(len(findings), 2)
        self.assertIn("could not reuse the exact closeout transaction", findings[0].message)
        self.assertIs(findings[1], mutation)

    def test_green_strict_v11_prevalidation_skips_only_repeated_component_pass(
        self,
    ) -> None:
        def green_primary(**kwargs: object) -> list[audit_repository.Finding]:
            prevalidated = kwargs["prevalidated_strict_v11_occurrence_papers"]
            assert isinstance(prevalidated, set)
            prevalidated.add("Fixture")
            return []

        with (
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                side_effect=green_primary,
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[],
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "has_current_v11_evidence_integrity_receipt",
                return_value=True,
            ) as receipt,
            mock.patch.object(
                audit_repository,
                "_load_conclusion_provenance_auditors",
                side_effect=AssertionError(
                    "accepted current v11 must not load historical conclusion code"
                ),
            ) as conclusion_loader,
        ):
            findings = self.run_closeout()

        self.assertEqual(findings, [])
        receipt.assert_called_once_with(
            mock.ANY,
        )
        conclusion_loader.assert_not_called()

    def test_unaccepted_prevalidation_still_runs_complete_conclusion_audit(
        self,
    ) -> None:
        context = object()
        audit = mock.Mock(return_value=[])
        with (
            mock.patch.object(
                audit_evidence_integrity,
                "has_current_v11_evidence_integrity_receipt",
                return_value=False,
            ) as receipt,
            mock.patch.object(
                audit_repository,
                "_load_conclusion_provenance_auditors",
                return_value=(mock.Mock(), audit),
            ) as conclusion_loader,
        ):
            findings = audit_repository.paper_closeout_conclusion_provenance_findings(
                "Fixture",
                theorem_realization_component_prevalidated=True,
                context=context,
            )

        self.assertEqual(findings, [])
        receipt.assert_called_once_with(context)
        conclusion_loader.assert_called_once_with()
        audit.assert_called_once_with(
            "Fixture",
            evidence_context=context,
            theorem_realization_component_prevalidated=True,
        )

    def test_v11_primary_graph_receipt_needs_no_legacy_raw_snapshot(self) -> None:
        context = object()
        with (
            mock.patch.object(
                audit_evidence_integrity,
                "has_current_v11_evidence_integrity_receipt",
                return_value=True,
            ) as receipt,
            mock.patch.object(
                audit_conclusion_provenance,
                "source_record_audit_snapshot_from_evidence_context",
                side_effect=AssertionError("v11 must not acquire legacy raw evidence"),
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "_audit_paper",
                side_effect=AssertionError("v11 must not replay legacy provenance"),
            ),
        ):
            findings = (
                audit_conclusion_provenance
                .audit_paper_for_consolidated_closeout_transaction(
                    "Fixture",
                    evidence_context=context,
                    theorem_realization_component_prevalidated=True,
                )
            )

        self.assertEqual(findings, [])
        receipt.assert_called_once_with(context)

    def test_absent_prevalidation_never_skips_component_pass(self) -> None:
        with (
            mock.patch.object(
                audit_repository,
                "check_machine_paper_status",
                return_value=[],
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[],
            ),
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
                return_value=[],
            ) as conclusion_run,
        ):
            findings = self.run_closeout()

        self.assertEqual(findings, [])
        conclusion_run.assert_called_once_with(
            "Fixture",
            evidence_context=mock.ANY,
            theorem_realization_component_prevalidated=False,
        )

    def test_conclusion_transaction_defers_hash_finalization_to_owner(self) -> None:
        context = object()
        snapshot = object()
        with (
            mock.patch.object(
                audit_conclusion_provenance,
                "source_record_audit_snapshot_from_evidence_context",
                return_value=(snapshot, ""),
            ),
            mock.patch.object(
                audit_conclusion_provenance, "_audit_paper", return_value=[]
            ) as audit,
        ):
            runner = (
                audit_conclusion_provenance
                .audit_paper_for_consolidated_closeout_transaction
            )
            findings = runner("Fixture", evidence_context=context)

        self.assertEqual(findings, [])
        audit.assert_called_once_with(
            "Fixture",
            theorem_realization_component_prevalidated=False,
            source_record_snapshot=snapshot,
            finalize_snapshot=False,
        )

    def test_package_closeout_cannot_borrow_a_duplicate_top_level_module(self) -> None:
        duplicate = types.ModuleType("audit_evidence_integrity")
        duplicate.run_for_consolidated_closeout_transaction = mock.Mock(  # type: ignore[attr-defined]
            return_value=[]
        )
        with (
            mock.patch.dict(sys.modules, {"audit_evidence_integrity": duplicate}),
            mock.patch.object(
                audit_repository, "check_machine_paper_status", return_value=[]
            ),
            mock.patch.object(
                audit_evidence_integrity,
                "run_for_consolidated_closeout_transaction",
                return_value=[],
            ) as package_run,
            mock.patch.object(
                audit_conclusion_provenance,
                "audit_paper_for_consolidated_closeout_transaction",
                return_value=[],
            ),
        ):
            self.run_closeout()

        package_run.assert_called_once()
        duplicate.run_for_consolidated_closeout_transaction.assert_not_called()  # type: ignore[attr-defined]

    def test_strict_v11_source_record_bridge_uses_authoritative_occurrence_gate(
        self,
    ) -> None:
        occurrence_finding = audit_conclusion_provenance.Finding(
            "Fixture",
            "paper_theorem",
            "h",
            ("result",),
            "missing occurrence contract",
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            (audit_dir / "paper_statement_map.json").write_text(
                json.dumps({"schema": 1}),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    audit_repository,
                    "source_spec_correspondence_requested",
                    return_value=True,
                ) as requested,
                mock.patch.object(
                    audit_conclusion_provenance,
                    "theorem_realization_component_contract_findings",
                    return_value=[occurrence_finding],
                ) as occurrence_gate,
            ):
                active, findings = (
                    audit_repository.strict_v11_occurrence_closeout_findings(
                        "Fixture",
                        folder,
                        {"theorem_realization_contract_schema": 1},
                        {"paper_theorem.h": {}},
                    )
                )

        self.assertTrue(active)
        requested.assert_called_once()
        occurrence_gate.assert_called_once()
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("paper_theorem", findings[0].message)
        self.assertIn("fields=result", findings[0].message)
        self.assertIn("missing occurrence contract", findings[0].message)

    def test_strict_v11_terminal_receipts_require_the_exact_context_issuer(
        self,
    ) -> None:
        """Only a builder-issued closeout context can feed terminal credit."""

        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            status_path = folder / "status.json"
            map_path = audit_dir / "paper_statement_map.json"
            status_payload = {"status": "formalized"}
            map_payload = {"items": {}}
            status_path.write_text(json.dumps(status_payload), encoding="utf-8")
            map_path.write_text(json.dumps(map_payload), encoding="utf-8")
            receipt = audit_repository.SemanticContractExecutableTerminalComponentReceipt(
                component_key="theorem-realization::fixture",
                source_judgment_key="fixture.source",
                component_sha256="a" * 64,
                structural_type_sha256="b" * 64,
                semantic_model_judgment_key="semantic-model::fixture",
                component_source_contract_association_sha256="c" * 64,
                source_item_key="formula-source",
                source_item_semantic_sha256="d" * 64,
                source_map_item_sha256="e" * 64,
                spec_declaration="Fixture.theoremSpec",
                evidence_declaration="Fixture.theorem",
                evidence_elaborated_signature_sha256="f" * 64,
                evidence_semantic_dependency_sha256="0" * 64,
                terminal_receipt_sha256="1" * 64,
            )

            unissued = audit_repository.PaperCloseoutRunContext("Fixture", folder)
            unissued.record_semantic_contract_executable_terminal_component_receipts(
                (receipt,)
            )
            self.assertEqual(
                unissued.current_semantic_contract_executable_terminal_component_receipts(),
                (),
            )

            evidence = mock.Mock(
                folder=folder.resolve(),
                issued_by_builder=True,
                audit_payload=None,
                input_snapshots=(
                    mock.Mock(path=status_path, payload=status_payload),
                    mock.Mock(path=map_path, payload=map_payload),
                ),
            )
            captured: dict[str, object] = {}

            def occurrence_gate(*_args: object, **kwargs: object) -> list[object]:
                captured["terminal_receipts"] = kwargs.get(
                    "semantic_contract_executable_terminal_component_receipts"
                )
                return []

            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "source_spec_correspondence_requested",
                    return_value=True,
                ),
                mock.patch.object(
                    audit_conclusion_provenance,
                    "theorem_realization_component_contract_findings",
                    side_effect=occurrence_gate,
                ),
            ):
                # Supplying a receipt to an unissued wrapper is ineffective:
                # the primary gate reads no terminal receipts from it.
                active, findings = audit_repository.strict_v11_occurrence_closeout_findings(
                    "Fixture",
                    folder,
                    {"theorem_realization_contract_schema": 1},
                    {},
                    run_context=unissued,
                )
                self.assertTrue(active)
                self.assertEqual(findings, [])
                self.assertEqual(captured["terminal_receipts"], ())

                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    "Fixture", folder, evidence_context=evidence
                )
                context.record_semantic_contract_executable_terminal_component_receipts(
                    (receipt,)
                )
                self.assertEqual(
                    context.current_semantic_contract_executable_terminal_component_receipts(),
                    (),
                )
                # The policy's private issuer marker is the only way a
                # builder-issued transaction can stage a receipt.
                context.record_semantic_contract_executable_terminal_component_receipts(
                    (receipt,),
                    _issuer=(
                        audit_repository
                        ._SEMANTIC_CONTRACT_EXECUTABLE_TERMINAL_RECEIPT_ISSUER
                    ),
                )
                active, findings = audit_repository.strict_v11_occurrence_closeout_findings(
                    "Fixture",
                    folder,
                    {"theorem_realization_contract_schema": 1},
                    {},
                    run_context=context,
                )

        self.assertTrue(active)
        self.assertEqual(findings, [])
        self.assertEqual(captured["terminal_receipts"], (receipt,))

    def test_strict_v11_recursive_field_receipts_require_the_exact_context_issuer(
        self,
    ) -> None:
        """A caller cannot inject scoped-field contract credit into a run."""

        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            status_path = folder / "status.json"
            map_path = audit_dir / "paper_statement_map.json"
            status_payload = {"status": "formalized"}
            map_payload = {"items": {}}
            status_path.write_text(json.dumps(status_payload), encoding="utf-8")
            map_path.write_text(json.dumps(map_payload), encoding="utf-8")
            receipt = audit_repository.RecursiveFieldExplicitParentComponentReceipt(
                component_key="theorem-realization::fixture-field",
                source_judgment_key="Fixture.Model.rate",
                component_sha256="a" * 64,
                structural_type_sha256="b" * 64,
                recursive_field_parent_route_sha256="c" * 64,
                source_item_key="source-item",
                source_item_semantic_sha256="d" * 64,
                source_map_item_sha256="e" * 64,
                root_record="Fixture.Model",
                field_scope_sha256="f" * 64,
                convention_id="fixture-convention",
                convention_sha256="0" * 64,
                parent_semantic_model_judgment_key="semantic-model::fixture",
                parent_qualified_declaration="Fixture.paperTheorem",
                parent_declaration_sha256="1" * 64,
                parent_elaborated_signature_sha256="2" * 64,
                parent_source_association_sha256="3" * 64,
            )
            unissued = audit_repository.PaperCloseoutRunContext("Fixture", folder)
            unissued.record_recursive_field_explicit_parent_component_receipts(
                (receipt,)
            )
            self.assertEqual(
                unissued.current_recursive_field_explicit_parent_component_receipts(),
                (),
            )
            evidence = mock.Mock(
                folder=folder.resolve(),
                issued_by_builder=True,
                audit_payload=None,
                input_snapshots=(
                    mock.Mock(path=status_path, payload=status_payload),
                    mock.Mock(path=map_path, payload=map_payload),
                ),
            )
            captured: dict[str, object] = {}

            def occurrence_gate(*_args: object, **kwargs: object) -> list[object]:
                captured["field_receipts"] = kwargs.get(
                    "recursive_field_explicit_parent_component_receipts"
                )
                return []

            with (
                mock.patch.object(
                    audit_repository, "exact_evidence_run_context", return_value=True
                ),
                mock.patch.object(
                    audit_repository,
                    "source_spec_correspondence_requested",
                    return_value=True,
                ),
                mock.patch.object(
                    audit_conclusion_provenance,
                    "theorem_realization_component_contract_findings",
                    side_effect=occurrence_gate,
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    "Fixture", folder, evidence_context=evidence
                )
                context.record_recursive_field_explicit_parent_component_receipts(
                    (receipt,)
                )
                self.assertEqual(
                    context.current_recursive_field_explicit_parent_component_receipts(),
                    (),
                )
                active, findings = audit_repository.strict_v11_occurrence_closeout_findings(
                    "Fixture",
                    folder,
                    {"theorem_realization_contract_schema": 1},
                    {},
                    run_context=context,
                )
                self.assertTrue(active)
                self.assertEqual(findings, [])
                self.assertEqual(captured["field_receipts"], ())

                context.record_recursive_field_explicit_parent_component_receipts(
                    (receipt,),
                    _issuer=(
                        audit_repository
                        ._RECURSIVE_FIELD_EXPLICIT_PARENT_RECEIPT_ISSUER
                    ),
                )
                active, findings = audit_repository.strict_v11_occurrence_closeout_findings(
                    "Fixture",
                    folder,
                    {"theorem_realization_contract_schema": 1},
                    {},
                    run_context=context,
                )

        self.assertTrue(active)
        self.assertEqual(findings, [])
        self.assertEqual(captured["field_receipts"], (receipt,))

    def test_recursive_field_receipt_preserves_loaded_differential_judgment(
        self,
    ) -> None:
        """A strict field issuer must retain authenticated overlay capability."""

        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            audit_dir = folder / "audit"
            audit_dir.mkdir(parents=True)
            judgment_path = audit_dir / "source_record_match_llm.json"
            audit_payload: dict[str, object] = {
                "source_record_audit_surface": {},
                "source_record_audit_sha256": "a" * 64,
            }
            evidence = types.SimpleNamespace(
                folder=folder.resolve(),
                legacy_source_record_state=legacy_source_record_state(
                    audit_payload,
                    audit_path=audit_dir / "source_record_audit.json",
                    match_path=judgment_path,
                ),
            )
            field_key = "Fixture.Model.rate"
            route = {
                "association_sha256": "b" * 64,
                "source_item": "source-item",
                "source_item_identities": [
                    {
                        "source_semantic_sha256": "c" * 64,
                        "source_map_item_sha256": "d" * 64,
                    }
                ],
                "root_record": "Fixture.Model",
                "field_scope_sha256": "e" * 64,
                "convention_id": "fixture-convention",
                "convention_sha256": "f" * 64,
                "parent_semantic_model_judgment_key": "semantic-model::fixture",
                "parent_reviewed_declaration_identity": {
                    "qualified_declaration": "Fixture.paperResult",
                    "declaration_sha256": "0" * 64,
                },
                "parent_elaborated_signature_identity": {
                    "qualified_declaration": "Fixture.paperResult",
                    "elaborated_signature_sha256": "1" * 64,
                },
                "parent_source_association_sha256": "2" * 64,
            }
            component = {
                "judgment_key": "theorem-realization::fixture-field",
                "source_judgment_key": field_key,
                "source_component_section": "recursive_field_items",
                "source_claim_component_role": "material",
                "source_claim_component_kind": "recursive_record_field",
                "source_claim_component_sha256": "3" * 64,
                "structural_type_sha256": "4" * 64,
                "recursive_field_explicit_parent_route": route,
                "nested_structures": [],
            }
            field_judgment = (
                source_record_differential_revalidation
                ._LoadedSourceRecordDifferentialRevalidationItem(
                    {
                        "source_record_differential_revalidation": {},
                    }
                )
            )
            parent = {"judgment_key": "semantic-model::fixture"}

            with (
                mock.patch.object(
                    audit_repository,
                    "exact_evidence_run_context",
                    return_value=True,
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_raw_integrity_error_if_current",
                    return_value="",
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_target_route_error",
                    return_value="",
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_audit_surface_view",
                    return_value=audit_payload,
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_expected_item_digests",
                    return_value={},
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_expected_item_digest_pins",
                    return_value={},
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_target_disposition_context",
                    return_value=({}, {}),
                ),
                mock.patch.object(
                    audit_repository,
                    "source_record_target_disposition_rebind_context",
                    return_value=(None, ""),
                ),
                mock.patch.object(
                    audit_repository,
                    "theorem_realization_components",
                    return_value=(("recursive_field_items", component),),
                ),
                mock.patch.object(
                    audit_repository,
                    "recursive_field_target_disposition_errors",
                    return_value=[],
                ),
                mock.patch.object(
                    audit_repository,
                    "_recursive_field_explicit_parent_semantic_model_item",
                    return_value=parent,
                ),
                mock.patch.object(
                    audit_repository,
                    "current_strict_v11_full_spec_source_record_semantic_model_judgment_keys",
                    return_value=frozenset({"semantic-model::fixture"}),
                ),
                mock.patch.object(
                    audit_repository,
                    "semantic_model_review_findings",
                    side_effect=AssertionError("strict parent must not need a duplicate review"),
                ),
            ):
                context = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
                    "Fixture", folder, evidence_context=evidence
                )
                with mock.patch.object(
                    context,
                    "source_record_judgments",
                    return_value={field_key: field_judgment},
                ):
                    receipts = (
                        audit_repository
                        ._recursive_field_explicit_parent_component_receipts(
                            "Fixture", folder, audit_payload, run_context=context
                        )
                    )

        self.assertEqual(len(receipts), 1)
        self.assertEqual(receipts[0].source_judgment_key, field_key)

    def test_v10_source_record_bridge_does_not_run_occurrence_gate(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            with (
                mock.patch.object(
                    audit_repository,
                    "source_spec_correspondence_requested",
                    return_value=False,
                ),
                mock.patch.object(
                    audit_conclusion_provenance,
                    "theorem_realization_component_contract_findings",
                ) as occurrence_gate,
            ):
                active, findings = (
                    audit_repository.strict_v11_occurrence_closeout_findings(
                        "Fixture", folder, {}, {}
                    )
                )

        self.assertFalse(active)
        self.assertEqual(findings, [])
        occurrence_gate.assert_not_called()

    def test_strict_v11_source_record_bridge_fails_closed_when_gate_crashes(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            with (
                mock.patch.object(
                    audit_repository,
                    "source_spec_correspondence_requested",
                    return_value=True,
                ),
                mock.patch.object(
                    audit_conclusion_provenance,
                    "theorem_realization_component_contract_findings",
                    side_effect=RuntimeError("fixture gate failure"),
                ),
            ):
                active, findings = (
                    audit_repository.strict_v11_occurrence_closeout_findings(
                        "Fixture", folder, {}, {}
                    )
                )

        self.assertTrue(active)
        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("could not run: fixture gate failure", findings[0].message)


if __name__ == "__main__":
    unittest.main()
