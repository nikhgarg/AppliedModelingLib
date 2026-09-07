#!/usr/bin/env python3
"""Orchestrate one fail-closed closeout using repository-owned validators."""

from __future__ import annotations

import json
import re
import sys
import time
from collections.abc import Callable, Mapping, MutableMapping
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if __package__ in {None, ""}:
    repository_root = str(ROOT)
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

from scripts.closeout_intake_freeze import source_intake_readiness
from scripts.closeout_plan_receipt import (
    CLOSEOUT_PLAN_RECEIPT_SCHEMA,
    resolved_plan_final_holistic_audit_surface,
)
from scripts.current_closeout.finalization import (
    CloseoutFinalizationError,
    finalize_current_closeout,
)
from scripts.current_closeout.pass_capability import (
    CurrentCloseoutPassError,
    _issue_current_closeout_pass,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_STAGE_COUNT,
    require_strict_closeout_stage,
)
from scripts.current_closeout.primary_gate_transaction import (
    current_route_schema_preflight_findings,
)
from scripts.evidence_run_context import V11EvidenceRunContext

ProgressCallback = Callable[[Mapping[str, object]], None]


def execute_paper_closeout(
    audit: Any,
    *,
    paper_filter: str | None,
    library_premise_audit: bool,
    require_source_bytes: bool,
    deep_paper_prose: bool,
    closeout_trace: MutableMapping[str, object] | None,
    closeout_progress_callback: ProgressCallback | None,
    operational_plan_identity: str = "",
    operational_plan_receipt: Mapping[str, object] | None = None,
) -> list[Any]:
    """Run one paper through the authoritative closeout stage order."""

    closeout_started = time.perf_counter()
    closeout_started_at = datetime.now(timezone.utc)
    stage_times: dict[str, float] = {}
    # This is non-authoritative operational telemetry.  Keep it alongside the
    # existing elapsed-time projection so an operator can diagnose where a
    # closeout spent wall-clock time without making machine-local timestamps an
    # acceptance input or receipt identity.
    stage_timestamps: dict[str, dict[str, object]] = {}
    evidence_diagnostics: dict[str, int] = {}
    primary_gate_phase_times: dict[str, float] = {}
    run_context: Any | None = None
    evidence_context: Any | None = None
    completed_stage_count = 0
    current_closeout_finalization: dict[str, object] | None = None
    final_holistic_surface_identity = (
        str(
            operational_plan_receipt.get(
                "final_holistic_audit_surface_sha256"
            )
            or ""
        )
        .strip()
        .lower()
        if isinstance(operational_plan_receipt, Mapping)
        else ""
    )
    current_plan_requires_semantic_document_basis = bool(
        isinstance(operational_plan_receipt, Mapping)
        and operational_plan_receipt.get("schema") == CLOSEOUT_PLAN_RECEIPT_SCHEMA
    )
    all_selected_semantic_review_identity = (
        str(
            operational_plan_receipt.get(
                "all_selected_semantic_review_sha256"
            )
            or ""
        )
        .strip()
        .lower()
        if isinstance(operational_plan_receipt, Mapping)
        else ""
    )

    def finish(result: list[Any]) -> list[Any]:
        if closeout_trace is not None:
            runtime_cache_diagnostics: dict[str, int] = {}
            if evidence_context is not None:
                diagnostics_provider = getattr(
                    evidence_context, "runtime_cache_diagnostics", None
                )
                if callable(diagnostics_provider):
                    raw_diagnostics = diagnostics_provider()
                    if isinstance(raw_diagnostics, Mapping):
                        runtime_cache_diagnostics = {
                            str(key): int(value)
                            for key, value in raw_diagnostics.items()
                            if isinstance(value, int)
                        }
            build_input_diagnostics = (
                run_context.build_input_provider.diagnostics()
                if run_context is not None
                else {}
            )
            closeout_trace.update(
                {
                    "schema": 1,
                    "paper": paper_filter or "",
                    "stages_seconds": dict(stage_times),
                    "strict_stage_timings": dict(stage_timestamps),
                    "primary_paper_gate_phases_seconds": dict(
                        primary_gate_phase_times
                    ),
                    "evidence_counters": {
                        **evidence_diagnostics,
                        **runtime_cache_diagnostics,
                    },
                    "build_input_counters": build_input_diagnostics,
                    "closeout_context_counters": (
                        run_context.diagnostics() if run_context is not None else {}
                    ),
                    "transaction_input_sha256": (
                        audit.closeout_transaction_input_sha256(run_context)
                    ),
                    "total_seconds": round(
                        time.perf_counter() - closeout_started, 6
                    ),
                    "started_at": closeout_started_at.isoformat(),
                    "finished_at": datetime.now(timezone.utc).isoformat(),
                    "errors": sum(item.severity == "ERROR" for item in result),
                    "warnings": sum(item.severity == "WARN" for item in result),
                    "current_closeout_published": (
                        current_closeout_finalization is not None
                    ),
                    **(
                        {
                            "current_closeout_finalization": dict(
                                current_closeout_finalization
                            )
                        }
                        if current_closeout_finalization is not None
                        else {}
                    ),
                }
            )
        return result

    def progress(event: Mapping[str, object]) -> None:
        if closeout_progress_callback is None:
            return
        try:
            closeout_progress_callback(event)
        except Exception:  # noqa: BLE001, S110 - progress cannot affect evidence.
            pass

    def start_stage(name: str) -> float:
        name = require_strict_closeout_stage(name)
        started_at = datetime.now(timezone.utc).isoformat()
        stage_timestamps[name] = {"started_at": started_at}
        progress(
            {
                "schema": 1,
                "stage": name,
                "status": "started",
                "started_at": started_at,
                "completed_stage_count": completed_stage_count,
                "total_stage_count": STRICT_CLOSEOUT_STAGE_COUNT,
            }
        )
        return time.perf_counter()

    def record_stage(name: str, started: float) -> None:
        nonlocal completed_stage_count
        name = require_strict_closeout_stage(name)
        elapsed = round(time.perf_counter() - started, 6)
        stage_times[name] = elapsed
        finished_at = datetime.now(timezone.utc).isoformat()
        stage_timestamps.setdefault(name, {})["finished_at"] = finished_at
        stage_timestamps[name]["elapsed_seconds"] = elapsed
        completed_stage_count += 1
        progress(
            {
                "schema": 1,
                "stage": name,
                "status": "finished",
                "finished_at": finished_at,
                "completed_stage_count": completed_stage_count,
                "total_stage_count": STRICT_CLOSEOUT_STAGE_COUNT,
                "elapsed_seconds": elapsed,
            }
        )

    def run_strict_stage(
        name: str,
        operation: Callable[[], list[Any]],
    ) -> list[Any]:
        """Execute one acceptance-affecting stage in this strict transaction.

        The expensive Lean graph and semantic judgments are acquired before
        this transaction and may be reused by exact identity.  These terminal
        gates are intentionally cheap and never load success from a local
        checkpoint: a self-authenticated operational file must not suppress an
        acceptance-affecting validator.
        """

        stage_started = start_stage(name)
        stage_findings = operation()
        record_stage(name, stage_started)
        return stage_findings

    def has_error(findings: list[Any]) -> bool:
        return any(item.severity == "ERROR" for item in findings)

    def fail(path: Path, message: str) -> list[Any]:
        return finish([audit.Finding("ERROR", path, message)])

    def finish_after_input_check(
        findings: list[Any],
        *,
        authorize_current_success: bool = False,
    ) -> list[Any]:
        nonlocal current_closeout_finalization
        assert evidence_context is not None
        stage_started = start_stage("final_input_check")
        findings.extend(
            audit.paper_closeout_context_mutation_findings(
                evidence_context,
                diagnostics=evidence_diagnostics,
                build_input_provider=(
                    run_context.build_input_provider
                    if run_context is not None
                    else None
                ),
            )
        )
        record_stage("final_input_check", stage_started)
        if (
            authorize_current_success
            and run_context is not None
            and run_context.selected_v11_closeout
            and not has_error(findings)
        ):
            try:
                if not isinstance(operational_plan_receipt, Mapping):
                    raise CurrentCloseoutPassError(
                        "current closeout has no exact operational plan receipt"
                    )
                current_pass = _issue_current_closeout_pass(
                    audit.ROOT,
                    paper_filter,
                    plan_identity=operational_plan_identity,
                    plan_receipt=operational_plan_receipt,
                    evidence_context=evidence_context,
                    completed_stages=tuple(stage_times),
                    findings=tuple(findings),
                )
                current_closeout_finalization = finalize_current_closeout(
                    current_pass
                )
            except (
                CloseoutFinalizationError,
                CurrentCloseoutPassError,
                OSError,
                RuntimeError,
                TypeError,
                ValueError,
            ) as exc:
                findings.append(
                    audit.Finding(
                        "ERROR",
                        audit.PAPERS / paper_filter / "status.json",
                        f"`{paper_filter}` current strict gates passed, but "
                        f"the exact runtime pass could not be published: {exc}",
                    )
                )
        return finish(findings)

    if paper_filter is None:
        return fail(audit.PAPERS, "paper-closeout requires a paper folder")
    try:
        current_audit_config = audit.load_audit_config()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        return fail(
            audit.AUDIT_CONFIG,
            f"paper-closeout audit configuration is unavailable: {exc}",
        )
    if current_audit_config != audit.AUDIT_CONFIG_PAYLOAD:
        return fail(
            audit.AUDIT_CONFIG,
            "paper-closeout audit configuration changed after process startup; "
            "discard this run and restart the command",
        )

    if re.fullmatch(r"[0-9a-f]{64}", operational_plan_identity) and not re.fullmatch(
        r"[0-9a-f]{64}", final_holistic_surface_identity
    ):
        return fail(
            audit.PAPERS / paper_filter / "docs" / "AGENT_SOURCE_AUDIT.md",
            "current closeout plan has no typed final holistic audit surface identity",
        )
    if (
        current_plan_requires_semantic_document_basis
        and not re.fullmatch(
            r"[0-9a-f]{64}", all_selected_semantic_review_identity
        )
    ):
        return fail(
            audit.PAPERS / paper_filter / "docs" / "REPORT_MEMO_COVERAGE.json",
            "current closeout plan has no all-selected semantic-review identity",
        )
    try:
        frozen_final_holistic_surface = (
            resolved_plan_final_holistic_audit_surface(
                audit.ROOT, operational_plan_receipt
            )
            if isinstance(operational_plan_receipt, Mapping)
            else None
        )
    except (OSError, RuntimeError, TypeError, ValueError) as exc:
        return fail(
            audit.PAPERS / paper_filter / "status.json",
            "current closeout plan final holistic surface is unavailable: " + str(exc),
        )
    frozen_review_policy_assurance = (
        frozen_final_holistic_surface.get("review_policy_assurance")
        if isinstance(frozen_final_holistic_surface, Mapping)
        and isinstance(
            frozen_final_holistic_surface.get("review_policy_assurance"), Mapping
        )
        else None
    )

    stage_started = start_stage("closeout_artifact_preflight")
    # Validate the byte-pinned source surface before any report/DAG work.  A
    # source-anchor or named-result failure must never consume a Lean graph or
    # independent-review batch and then invalidate that later evidence.
    preflight_findings: list[audit.Finding] = []
    try:
        intake_readiness = source_intake_readiness(
            audit.PAPERS / paper_filter,
            repository_root=audit.ROOT,
        )
    except (OSError, RuntimeError, ValueError) as exc:
        intake_readiness = {
            "ready": False,
            "errors": [f"source-intake preflight is unavailable: {exc}"],
        }
    if intake_readiness.get("ready") is not True:
        errors = intake_readiness.get("errors")
        details = (
            "; ".join(str(error) for error in errors)
            if isinstance(errors, list) and errors
            else "source-intake preflight did not establish readiness"
        )
        preflight_findings.append(
            audit.Finding(
                "ERROR",
                audit.PAPERS / paper_filter / "status.json",
                f"`{paper_filter}` prospective intake boundary failed: {details}",
            )
        )
    if not has_error(preflight_findings):
        preflight_findings.extend(
            audit.check_dag_and_validation_report_closeout(
                include_active=True,
                paper_filter=paper_filter,
                force_selected_closeout=True,
                final_holistic_surface_sha256=final_holistic_surface_identity,
                all_selected_semantic_review_sha256=(
                    all_selected_semantic_review_identity
                    if current_plan_requires_semantic_document_basis
                    else None
                ),
                final_holistic_review_policy_assurance=(
                    frozen_review_policy_assurance
                ),
            )
        )
    record_stage("closeout_artifact_preflight", stage_started)
    if has_error(preflight_findings):
        return finish(preflight_findings)

    stage_started = start_stage("acquire_exact_context")
    try:
        # The builder-issued object, not a wrapper attribute, owns finalization.
        evidence_context = audit.build_paper_closeout_evidence_context(
            paper_filter,
            diagnostics=evidence_diagnostics,
            operational_plan_receipt=operational_plan_receipt,
        )
    except Exception as exc:  # noqa: BLE001 - closeout must fail closed.
        record_stage("acquire_exact_context", stage_started)
        return fail(
            audit.PAPERS / paper_filter / "status.json",
            f"`{paper_filter}` could not acquire one exact closeout evidence "
            f"transaction: {exc}",
        )
    record_stage("acquire_exact_context", stage_started)

    stage_started = start_stage("route_schema_preflight")
    if isinstance(evidence_context, V11EvidenceRunContext):
        route_schema_findings = [
            audit.Finding(finding.severity, Path(finding.path), finding.message)
            for finding in current_route_schema_preflight_findings(
                audit.ROOT, audit.PAPERS / paper_filter, context=evidence_context
            )
        ]
    else:
        route_schema_findings = audit.paper_closeout_fast_route_schema_findings(
            paper_filter, context=evidence_context
        )
    record_stage("route_schema_preflight", stage_started)
    preflight_findings.extend(route_schema_findings)
    if has_error(route_schema_findings):
        return finish_after_input_check(preflight_findings)

    stage_started = start_stage("acquire_lean_context")
    try:
        run_context = audit.PaperCloseoutRunContext.from_exact_evidence_context(
            paper_filter,
            audit.PAPERS / paper_filter,
            evidence_context=evidence_context,
        )
    except Exception as exc:  # noqa: BLE001 - closeout must fail closed.
        record_stage("acquire_lean_context", stage_started)
        return finish_after_input_check(
            [
                audit.Finding(
                    "ERROR",
                    audit.PAPERS / paper_filter / "status.json",
                    f"`{paper_filter}` could not acquire the Lean-backed closeout "
                    f"context: {exc}",
                )
            ]
        )
    record_stage("acquire_lean_context", stage_started)

    findings = list(preflight_findings)
    evidence_prebuild_findings = run_strict_stage(
        "current_evidence_transaction_preflight",
        lambda: (
            audit.paper_closeout_evidence_context_prebuild_findings(
                paper_filter,
                evidence_context,
                run_context=run_context,
            )
        ),
    )
    findings.extend(evidence_prebuild_findings)
    if has_error(evidence_prebuild_findings):
        return finish_after_input_check(findings)

    build_findings = run_strict_stage(
        "paper_root_build",
        lambda: audit.check_paper_root_build_closeout(paper_filter),
    )
    findings.extend(build_findings)
    if has_error(build_findings):
        return finish_after_input_check(findings)

    prevalidated_occurrence_papers: set[str] = set()

    def primary_gate_phase_progress(event: Mapping[str, object]) -> None:
        progress(
            {
                "schema": 1,
                "stage": "primary_paper_gate",
                "status": "running",
                "completed_stage_count": completed_stage_count,
                "total_stage_count": STRICT_CLOSEOUT_STAGE_COUNT,
                "phase_event": dict(event),
            }
        )

    def current_or_legacy_primary_gate() -> list[Any]:
        """Run the selected protocol's one primary accepting implementation."""

        assert run_context is not None
        if not run_context.selected_v11_closeout:
            return audit.check_machine_paper_status(
                library_premise_audit=library_premise_audit,
                paper_filter=paper_filter,
                paper_closeout=True,
                require_source_bytes=require_source_bytes,
                deep_paper_prose=deep_paper_prose,
                prevalidated_strict_v11_occurrence_papers=(
                    prevalidated_occurrence_papers
                ),
                run_context=run_context,
                phase_timings=primary_gate_phase_times,
                phase_progress_callback=primary_gate_phase_progress,
            )

        typed_started = time.perf_counter()
        try:
            result, accepted = (
                run_context.evaluate_and_accept_current_v11_primary_gate()
            )
        except Exception as exc:  # noqa: BLE001 - current acceptance fails closed.
            primary_gate_phase_times["current_v11_typed_conjunction"] = round(
                time.perf_counter() - typed_started,
                6,
            )
            return [
                audit.Finding(
                    "ERROR",
                    audit.PAPERS / paper_filter / "status.json",
                    f"`{paper_filter}` current v11 primary gate is unavailable: {exc}",
                )
            ]
        primary_gate_phase_times["current_v11_typed_conjunction"] = round(
            time.perf_counter() - typed_started,
            6,
        )
        error_families = (
            (
                "configuration",
                audit.PAPERS / paper_filter / "status.json",
                result.configuration_errors,
            ),
            (
                "semantic review",
                audit.PAPERS
                / paper_filter
                / "audit"
                / "v11_raw_source_spec_screening.json",
                result.semantic_errors,
            ),
            (
                "proof realization",
                audit.PAPERS / paper_filter / "PaperInterface.lean",
                result.proof_errors,
            ),
            (
                "axiom closure",
                audit.PAPERS / paper_filter / "PaperInterface.lean",
                result.axiom_errors,
            ),
            (
                "Lean source structure",
                audit.PAPERS / paper_filter / "PaperInterface.lean",
                result.structure_errors,
            ),
        )
        current_findings = [
            audit.Finding(
                "ERROR",
                path,
                f"`{paper_filter}` current v11 {family} gate failed: {message}",
            )
            for family, path, errors in error_families
            for message in errors
        ]
        if not current_findings and accepted is None:
            current_findings.append(
                audit.Finding(
                    "ERROR",
                    audit.PAPERS / paper_filter / "status.json",
                    f"`{paper_filter}` current v11 primary verdict passed but "
                    "did not issue its exact acceptance object",
                )
            )
        if not current_findings:
            prevalidated_occurrence_papers.add(paper_filter)
        return current_findings

    selected_v11_primary = run_context.selected_v11_closeout
    primary_findings = run_strict_stage(
        "primary_paper_gate",
        current_or_legacy_primary_gate,
    )
    findings.extend(primary_findings)
    if has_error(primary_findings):
        return finish_after_input_check(findings)

    # Publish reuse only after the complete primary paper gate passes.
    if not selected_v11_primary:
        run_context.publish_staged_strict_v11_source_record_judgment_handoff()

    evidence_findings = run_strict_stage(
        "evidence_integrity",
        lambda: audit.paper_closeout_evidence_integrity_findings(
            paper_filter,
            require_source_bytes=require_source_bytes,
            context=evidence_context,
            diagnostics=evidence_diagnostics,
        ),
    )
    findings.extend(evidence_findings)
    if has_error(evidence_findings):
        return finish_after_input_check(findings)

    conclusion_findings = run_strict_stage(
        "conclusion_provenance",
        lambda: audit.paper_closeout_conclusion_provenance_findings(
            paper_filter,
            theorem_realization_component_prevalidated=(
                paper_filter in prevalidated_occurrence_papers
            ),
            context=evidence_context,
        ),
    )
    findings.extend(conclusion_findings)
    return finish_after_input_check(
        findings,
        authorize_current_success=True,
    )
