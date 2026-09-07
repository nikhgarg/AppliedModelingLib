#!/usr/bin/env python3
"""Every current strict stage is mandatory and fail-closed."""

from __future__ import annotations

import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
)
from scripts.paper_closeout_executor import execute_paper_closeout


@dataclass(frozen=True)
class Finding:
    severity: str
    path: Path
    message: str


class _BuildInputs:
    def diagnostics(self) -> dict[str, int]:
        return {}


class CurrentCloseoutStageFailClosedTests(unittest.TestCase):
    def test_each_registered_stage_failure_prevents_pass_issuance(self) -> None:
        for failing_stage in STRICT_CLOSEOUT_EXECUTION_STAGES:
            with self.subTest(stage=failing_stage), tempfile.TemporaryDirectory() as temp:
                self._assert_stage_failure(failing_stage, Path(temp))

    def _assert_stage_failure(self, failing_stage: str, root: Path) -> None:
        paper = "Fixture"
        folder = root / "papers" / paper
        folder.mkdir(parents=True)
        calls: list[str] = []
        exact_evidence_context = SimpleNamespace(runtime_cache_diagnostics=dict)

        class RunContext:
            selected_v11_closeout = True
            current_v11_closeout = True
            build_input_provider = _BuildInputs()

            def __init__(self) -> None:
                self.evidence_context = exact_evidence_context

            def diagnostics(self) -> dict[str, int]:
                return {}

            def evaluate_and_accept_current_v11_primary_gate(
                self,
            ) -> tuple[SimpleNamespace, object | None]:
                calls.append("primary_paper_gate")
                failed = failing_stage == "primary_paper_gate"
                result = SimpleNamespace(
                    configuration_errors=(),
                    semantic_errors=(("injected",) if failed else ()),
                    proof_errors=(),
                    axiom_errors=(),
                    structure_errors=(),
                )
                return result, None if failed else object()

        class ContextFactory:
            @staticmethod
            def from_exact_evidence_context(
                _paper: str,
                _folder: Path,
                *,
                evidence_context: object,
            ) -> RunContext:
                calls.append("acquire_lean_context")
                if failing_stage == "acquire_lean_context":
                    raise ValueError("injected")
                self.assertIs(evidence_context, exact_evidence_context)
                return RunContext()

        def finding(stage: str) -> list[Finding]:
            calls.append(stage)
            return (
                [Finding("ERROR", folder / "status.json", "injected")]
                if failing_stage == stage
                else []
            )

        def acquire(*_args: object, **_kwargs: object) -> object:
            calls.append("acquire_exact_context")
            if failing_stage == "acquire_exact_context":
                raise ValueError("injected")
            return exact_evidence_context

        audit = SimpleNamespace(
            ROOT=root,
            PAPERS=root / "papers",
            AUDIT_CONFIG=root / "papers" / "audit_config.json",
            AUDIT_CONFIG_PAYLOAD={"schema": 1},
            Finding=Finding,
            PaperCloseoutRunContext=ContextFactory,
            load_audit_config=lambda: {"schema": 1},
            check_dag_and_validation_report_closeout=(
                lambda **_kwargs: finding("closeout_artifact_preflight")
            ),
            build_paper_closeout_evidence_context=acquire,
            paper_closeout_fast_route_schema_findings=(
                lambda *_args, **_kwargs: finding("route_schema_preflight")
            ),
            paper_closeout_evidence_context_prebuild_findings=(
                lambda *_args, **_kwargs: finding(
                    "current_evidence_transaction_preflight"
                )
            ),
            check_paper_root_build_closeout=(
                lambda *_args, **_kwargs: finding("paper_root_build")
            ),
            check_machine_paper_status=mock.Mock(
                side_effect=AssertionError("legacy gate is unreachable")
            ),
            paper_closeout_evidence_integrity_findings=(
                lambda *_args, **_kwargs: finding("evidence_integrity")
            ),
            paper_closeout_conclusion_provenance_findings=(
                lambda *_args, **_kwargs: finding("conclusion_provenance")
            ),
            paper_closeout_context_mutation_findings=(
                lambda *_args, **_kwargs: finding("final_input_check")
            ),
            closeout_transaction_input_sha256=lambda _context: "c" * 64,
        )
        plan = {
            "paper": paper,
            "plan_identity_sha256": "a" * 64,
            "final_holistic_audit_surface_sha256": "b" * 64,
        }
        trace: dict[str, object] = {}
        with (
            mock.patch(
                "scripts.paper_closeout_executor.source_intake_readiness",
                return_value={
                    "ready": failing_stage != "closeout_artifact_preflight",
                    "errors": (
                        []
                        if failing_stage != "closeout_artifact_preflight"
                        else ["injected canonical source-surface failure"]
                    ),
                },
            ),
            mock.patch(
                "scripts.paper_closeout_executor._issue_current_closeout_pass"
            ) as issue,
            mock.patch(
                "scripts.paper_closeout_executor.finalize_current_closeout"
            ) as finalize,
        ):
            findings = execute_paper_closeout(
                audit,
                paper_filter=paper,
                library_premise_audit=False,
                require_source_bytes=True,
                deep_paper_prose=False,
                closeout_trace=trace,
                closeout_progress_callback=None,
                operational_plan_identity="a" * 64,
                operational_plan_receipt=plan,
            )

        self.assertTrue(any(item.severity == "ERROR" for item in findings))
        issue.assert_not_called()
        finalize.assert_not_called()
        if failing_stage == "closeout_artifact_preflight":
            self.assertNotIn(
                "closeout_artifact_preflight",
                calls,
                "canonical source preflight must short-circuit before report/DAG checks",
            )
        completed = tuple(trace["stages_seconds"])
        failure_index = STRICT_CLOSEOUT_EXECUTION_STAGES.index(failing_stage)
        expected = STRICT_CLOSEOUT_EXECUTION_STAGES[: failure_index + 1]
        if 2 <= failure_index < len(STRICT_CLOSEOUT_EXECUTION_STAGES) - 1:
            expected += ("final_input_check",)
        self.assertEqual(completed, expected)
        stage_timings = trace["strict_stage_timings"]
        self.assertEqual(tuple(stage_timings), expected)
        for timing in stage_timings.values():
            self.assertIsInstance(timing.get("started_at"), str)
            self.assertIsInstance(timing.get("finished_at"), str)
            self.assertIsInstance(timing.get("elapsed_seconds"), float)
        self.assertNotIn("current_closeout_finalization", trace)
        self.assertFalse(trace["current_closeout_published"])


if __name__ == "__main__":
    unittest.main()
