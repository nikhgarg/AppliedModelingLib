#!/usr/bin/env python3
"""Run one current graph-native paper closeout in one accepting process."""

from __future__ import annotations

import argparse
import json
import re
import sys
from collections.abc import Mapping
from pathlib import Path

from scripts.check_formalization_engine_revision import (
    runtime_engine_registration_error,
)
from scripts.closeout_execution_state import (
    CloseoutExecutionLease,
    default_closeout_execution_path,
)
from scripts.closeout_plan_receipt import load_validated_closeout_plan_receipt
from scripts.current_closeout import runtime_api
from scripts.paper_closeout_executor import execute_paper_closeout

ROOT = Path(__file__).resolve().parents[2]


def _render_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(ROOT.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return str(path)


def _persisted_findings(
    findings: list[runtime_api.Finding],
) -> list[dict[str, str]]:
    return [
        {
            "severity": finding.severity,
            "path": _render_path(finding.path),
            "message": finding.message,
        }
        for finding in findings
    ]


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--deep-paper-prose", action="store_true")
    parser.add_argument("--allow-missing-source-bytes", action="store_true")
    parser.add_argument("--closeout-state", type=Path)
    parser.add_argument("--no-closeout-state", action="store_true")
    parser.add_argument(
        "--operational-plan-identity",
        default="",
        help="exact planner-issued identity for this current transaction",
    )
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    if args.closeout_state and args.no_closeout_state:
        raise SystemExit(
            "--closeout-state cannot be combined with --no-closeout-state"
        )
    if not args.no_closeout_state and not re.fullmatch(
        r"[0-9a-f]{64}", args.operational_plan_identity
    ):
        print(
            "current closeout not started: stateful execution requires the exact "
            "planner-issued --operational-plan-identity",
            file=sys.stderr,
        )
        return 6
    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        print(
            "current closeout not started: formalization engine runtime is not "
            "registered: " + engine_error,
            file=sys.stderr,
        )
        return 6
    plan_receipt: Mapping[str, object] | None = None
    if not args.no_closeout_state:
        plan_receipt, plan_error = load_validated_closeout_plan_receipt(
            ROOT,
            paper=args.paper,
            deep_paper_prose=args.deep_paper_prose,
            expected_plan_identity=args.operational_plan_identity,
        )
        if plan_error:
            print(
                "current closeout not started: planner receipt is absent, malformed, "
                "or stale: " + plan_error,
                file=sys.stderr,
            )
            return 6

    trace: dict[str, object] = {}
    lease: CloseoutExecutionLease | None = None
    if not args.no_closeout_state:
        state_path = args.closeout_state or default_closeout_execution_path(
            ROOT, args.paper
        )
        requested_argv = argv if argv is not None else sys.argv[1:]
        lease, lease_error = CloseoutExecutionLease.acquire(
            state_path,
            paper=args.paper,
            command=[
                sys.executable,
                "-m",
                __spec__.name if __spec__ else __name__,
                *requested_argv,
            ],
            request={
                "operational_plan_identity": args.operational_plan_identity,
            },
        )
        if lease is None:
            print(f"current closeout not started: {lease_error}", file=sys.stderr)
            return 2
        print(f"Closeout execution state: {state_path}")

    def publish_progress(event: Mapping[str, object]) -> None:
        if lease is None:
            return
        completed = event.get("completed_stage_count")
        total = event.get("total_stage_count")
        lease.heartbeat(
            stage=str(event.get("stage") or "strict_closeout"),
            completed_units=(
                completed
                if isinstance(completed, int) and not isinstance(completed, bool)
                else None
            ),
            total_units=(
                total
                if isinstance(total, int) and not isinstance(total, bool)
                else None
            ),
            details={
                str(key): value
                for key, value in event.items()
                if key
                not in {
                    "stage",
                    "completed_stage_count",
                    "total_stage_count",
                }
            },
        )

    try:
        findings = execute_paper_closeout(
            runtime_api,
            paper_filter=args.paper,
            library_premise_audit=False,
            require_source_bytes=not args.allow_missing_source_bytes,
            deep_paper_prose=args.deep_paper_prose,
            closeout_trace=trace,
            closeout_progress_callback=publish_progress,
            operational_plan_identity=args.operational_plan_identity,
            operational_plan_receipt=plan_receipt,
        )
    except BaseException as exc:
        if lease is not None:
            lease.fail(f"{type(exc).__name__}: {exc}")
        raise

    errors = [finding for finding in findings if finding.severity == "ERROR"]
    if not errors and trace.get("current_closeout_published") is not True:
        publication_error = runtime_api.Finding(
            "ERROR",
            runtime_api.PAPERS / args.paper / "status.json",
            f"`{args.paper}` strict stages returned without an in-process current "
            "closeout publication",
        )
        findings.append(publication_error)
        errors.append(publication_error)
    warnings = [finding for finding in findings if finding.severity == "WARN"]
    infos = [finding for finding in findings if finding.severity == "INFO"]
    exit_code = 1 if errors else 0
    if lease is not None:
        lease.complete(
            exit_code=exit_code,
            result={
                "semantic_closeout_passed": not errors,
                "errors": len(errors),
                "warnings": len(warnings),
                "infos": len(infos),
                "findings": _persisted_findings(findings),
                "trace": dict(trace),
                "operational_plan_identity": args.operational_plan_identity,
                "acceptance_credential": False,
            },
        )
    for finding in findings:
        print(finding.format())
    print(
        "Closeout trace: "
        + json.dumps(trace, sort_keys=True, separators=(",", ":"))
    )
    print(
        f"Current closeout complete: {len(errors)} error(s), "
        f"{len(warnings)} warning(s); paper {args.paper}"
    )
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
