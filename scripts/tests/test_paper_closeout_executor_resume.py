from __future__ import annotations

import json
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.paper_closeout_executor import execute_paper_closeout


@dataclass(frozen=True)
class Finding:
    severity: str
    path: Path
    message: str


class _BuildInputProvider:
    def diagnostics(self) -> dict[str, int]:
        return {}


class _RunContext:
    def __init__(self, evidence_context: object) -> None:
        self.evidence_context = evidence_context
        self.build_input_provider = _BuildInputProvider()
        self.selected_v11_closeout = True
        self.handoff_staged = False
        self.handoff_count = 0

    def diagnostics(self) -> dict[str, int]:
        return {}

    def stage_strict_v11_source_record_judgment_handoff(self) -> None:
        self.handoff_staged = True

    def publish_staged_strict_v11_source_record_judgment_handoff(self) -> bool:
        if not self.handoff_staged:
            return False
        self.handoff_staged = False
        self.handoff_count += 1
        return True


class StrictStageNoResumeTests(unittest.TestCase):
    def test_same_plan_retry_executes_every_acceptance_stage(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = "Fixture23Paper"
            folder = root / "papers" / paper
            folder.mkdir(parents=True)
            counters = {
                "context": 0,
                "source_preflight": 0,
                "build": 0,
                "primary": 0,
                "evidence": 0,
                "conclusion": 0,
                "final_input": 0,
            }
            primary_should_fail = [True]
            evidence_should_fail = [True]
            contexts: list[_RunContext] = []

            class ContextFactory:
                @staticmethod
                def from_exact_evidence_context(
                    paper_id: str, paper_folder: Path, *, evidence_context: object
                ) -> _RunContext:
                    self.assertEqual(paper_id, paper)
                    self.assertEqual(paper_folder, folder)
                    context = _RunContext(evidence_context)
                    def evaluate_primary() -> tuple[SimpleNamespace, object | None]:
                        result = primary()
                        accepted = None if result.semantic_errors else object()
                        return result, accepted

                    context.evaluate_and_accept_current_v11_primary_gate = (  # type: ignore[attr-defined]
                        evaluate_primary
                    )
                    contexts.append(context)
                    return context

            def build_context(*_args: object, **_kwargs: object) -> object:
                counters["context"] += 1
                return SimpleNamespace(runtime_cache_diagnostics=dict)

            def source_preflight(*_args: object, **_kwargs: object) -> list[Finding]:
                counters["source_preflight"] += 1
                return []

            def build(*_args: object, **_kwargs: object) -> list[Finding]:
                counters["build"] += 1
                return []

            def primary() -> SimpleNamespace:
                counters["primary"] += 1
                return SimpleNamespace(
                    configuration_errors=(),
                    semantic_errors=(
                        ("retry primary",) if primary_should_fail[0] else ()
                    ),
                    proof_errors=(),
                    axiom_errors=(),
                    structure_errors=(),
                )

            def evidence(*_args: object, **_kwargs: object) -> list[Finding]:
                counters["evidence"] += 1
                if evidence_should_fail[0]:
                    return [Finding("ERROR", folder / "audit.json", "retry me")]
                return []

            def conclusion(*_args: object, **_kwargs: object) -> list[Finding]:
                counters["conclusion"] += 1
                return []

            def final_input(*_args: object, **_kwargs: object) -> list[Finding]:
                counters["final_input"] += 1
                return []

            audit = SimpleNamespace(
                ROOT=root,
                PAPERS=root / "papers",
                AUDIT_CONFIG=root / "audit_config.json",
                AUDIT_CONFIG_PAYLOAD={"schema": 1},
                Finding=Finding,
                PaperCloseoutRunContext=ContextFactory,
                load_audit_config=lambda: {"schema": 1},
                check_dag_and_validation_report_closeout=lambda **_kwargs: [],
                paper_closeout_fast_route_schema_findings=(
                    lambda _paper, **_kwargs: []
                ),
                build_paper_closeout_evidence_context=build_context,
                paper_closeout_evidence_context_prebuild_findings=source_preflight,
                check_paper_root_build_closeout=build,
                check_machine_paper_status=mock.Mock(
                    side_effect=AssertionError(
                        "selected v11 must not execute the mixed legacy checker"
                    )
                ),
                paper_closeout_evidence_integrity_findings=evidence,
                paper_closeout_conclusion_provenance_findings=conclusion,
                paper_closeout_context_mutation_findings=final_input,
                closeout_transaction_input_sha256=lambda _context: "c" * 64,
            )
            plan_identity = "a" * 64
            plan_receipt = {
                "final_holistic_audit_surface_sha256": "b" * 64
            }

            with (
                mock.patch(
                    "scripts.paper_closeout_executor.source_intake_readiness",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch(
                    "scripts.paper_closeout_executor._issue_current_closeout_pass",
                    return_value=mock.sentinel.current_pass,
                ) as issue_pass,
                mock.patch(
                    "scripts.paper_closeout_executor.finalize_current_closeout",
                    return_value={
                        "canonical_receipt": (
                            f"papers/{paper}/FINAL_CLOSURE_RECEIPT.md"
                        )
                    },
                ) as finalize,
            ):
                first_trace: dict[str, object] = {}
                first = execute_paper_closeout(
                    audit,
                    paper_filter=paper,
                    library_premise_audit=False,
                    require_source_bytes=True,
                    deep_paper_prose=False,
                    closeout_trace=first_trace,
                    closeout_progress_callback=None,
                    operational_plan_identity=plan_identity,
                    operational_plan_receipt=plan_receipt,
                )
                primary_should_fail[0] = False

                # A locally fabricated legacy checkpoint is inert. The current
                # executor has no success-resume reader for strict stages.
                forged = (
                    folder
                    / ".review_traces"
                    / "strict_stage_resume"
                    / plan_identity
                    / "paper_root_build.json"
                )
                forged.parent.mkdir(parents=True)
                forged.write_text(
                    json.dumps({"successful": True, "receipt_sha256": "0" * 64})
                    + "\n",
                    encoding="utf-8",
                )

                second_trace: dict[str, object] = {}
                second = execute_paper_closeout(
                    audit,
                    paper_filter=paper,
                    library_premise_audit=False,
                    require_source_bytes=True,
                    deep_paper_prose=False,
                    closeout_trace=second_trace,
                    closeout_progress_callback=None,
                    operational_plan_identity=plan_identity,
                    operational_plan_receipt=plan_receipt,
                )
                evidence_should_fail[0] = False
                third_trace: dict[str, object] = {}
                third = execute_paper_closeout(
                    audit,
                    paper_filter=paper,
                    library_premise_audit=False,
                    require_source_bytes=True,
                    deep_paper_prose=False,
                    closeout_trace=third_trace,
                    closeout_progress_callback=None,
                    operational_plan_identity=plan_identity,
                    operational_plan_receipt=plan_receipt,
                )

            self.assertTrue(any(item.severity == "ERROR" for item in first))
            self.assertTrue(any(item.severity == "ERROR" for item in second))
            self.assertFalse(any(item.severity == "ERROR" for item in third))
            self.assertEqual(counters["context"], 3)
            self.assertEqual(counters["source_preflight"], 3)
            self.assertEqual(counters["build"], 3)
            self.assertEqual(counters["primary"], 3)
            self.assertEqual(counters["evidence"], 2)
            self.assertEqual(counters["conclusion"], 1)
            self.assertEqual(counters["final_input"], 3)
            self.assertEqual(
                [context.handoff_count for context in contexts],
                [0, 0, 0],
            )
            self.assertNotIn("acceptance_stage_resume", third_trace)
            self.assertNotIn("same_plan_resume", third_trace)
            self.assertTrue(third_trace["current_closeout_published"])
            issue_pass.assert_called_once()
            finalize.assert_called_once_with(mock.sentinel.current_pass)


if __name__ == "__main__":
    unittest.main()
