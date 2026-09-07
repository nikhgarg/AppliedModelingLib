"""Run one strict paper closeout in a detached, duplicate-safe worker.

This launcher is operational infrastructure only.  It does not change audit
protocols, refresh paper artifacts, or turn its state into acceptance evidence.
The worker survives loss of the caller's terminal stream, writes the unchanged
strict audit output to an ignored log, and rejects a second live worker.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys
import time
import uuid
from collections.abc import Mapping
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_formalization_engine_revision import (
    runtime_engine_registration_error,
)
from scripts.closeout_execution_state import (
    CloseoutExecutionLease,
    atomic_write_json,
    closeout_worker_state_path,
    default_closeout_execution_path,
    effective_closeout_execution_state,
    execution_lock_is_held,
    read_execution_state,
    resolve_paper_folder,
    running_execution_summary,
)
from scripts.closeout_plan_receipt import (
    OPERATIONAL_PLAN_IDENTITY_SCHEMA,
    load_validated_closeout_plan_receipt,
)
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
    STRICT_CLOSEOUT_STAGE_COUNT,
)
from scripts.final_closure_receipt import (
    FinalClosureReceiptError,
    load_final_closure_receipt,
)

WORKER_LOG_FILE = "paper_closeout_worker.log"
LAUNCHER_LOG_FILE = "paper_closeout_launcher.log"


def _plan_receipt_error(
    paper: str,
    *,
    deep_paper_prose: bool,
    plan_identity: str,
    check_runtime_engine: bool = True,
) -> str:
    if not plan_identity:
        return (
            "a planner-issued closeout identity is required; run "
            "closeout_reuse_plan.py and use its exact command"
        )
    if check_runtime_engine:
        engine_error = runtime_engine_registration_error(ROOT)
        if engine_error:
            return f"formalization engine runtime is not registered: {engine_error}"
    _receipt, error = load_validated_closeout_plan_receipt(
        ROOT,
        paper=paper,
        deep_paper_prose=deep_paper_prose,
        expected_plan_identity=plan_identity,
    )
    return error


def worker_state_path(paper: str) -> Path:
    return closeout_worker_state_path(ROOT, paper)


def worker_log_path(paper: str, launch_id: str = "") -> Path:
    filename = (
        f"paper_closeout_worker.{launch_id}.log" if launch_id else WORKER_LOG_FILE
    )
    return ROOT / "papers" / paper / ".review_traces" / filename


def _audit_command(
    paper: str, *, deep_paper_prose: bool, plan_identity: str = ""
) -> list[str]:
    command = [
        sys.executable,
        "-m",
        "scripts.current_closeout.strict_runner",
        "--paper",
        paper,
    ]
    if deep_paper_prose:
        command.append("--deep-paper-prose")
    if plan_identity:
        command.extend(["--operational-plan-identity", plan_identity])
    return command


def _request_identity(
    paper: str,
    *,
    deep_paper_prose: bool,
    plan_identity: str = "",
) -> dict[str, Any]:
    # Preserve compatibility with existing operational states: the plan
    # identity is already a first-class request field, while the audit-command
    # hash represents only the semantic audit profile.  The worker still
    # passes the identity to the subprocess for state-write authorization.
    command = _audit_command(paper, deep_paper_prose=deep_paper_prose)
    return {
        "schema": 2,
        "paper": paper,
        "deep_paper_prose": deep_paper_prose,
        "operational_plan_identity": plan_identity,
        "operational_plan_identity_schema": OPERATIONAL_PLAN_IDENTITY_SCHEMA,
        "audit_command_sha256": hashlib.sha256(
            json.dumps(command, separators=(",", ":")).encode("utf-8")
        ).hexdigest(),
    }


def _terminate_child(process: subprocess.Popen[bytes]) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=5)
    except (OSError, subprocess.TimeoutExpired):
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except OSError:
            pass
        process.wait()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _inner_closeout_progress(
    paper: str, plan_identity: str
) -> tuple[str, int, int, dict[str, Any]] | None:
    """Return authenticated stage progress from the strict audit subprocess.

    The outer worker owns survivability and duplicate suppression; the inner
    The package-owned current runner owns the registered strict closeout stages.
    Older worker status discarded that richer state and exposed only ``0/1``
    plus a log-byte count. Mirror it only when paper and operational plan
    identity match, so a stale inner execution record cannot describe a new
    worker.
    This is observability metadata and never an acceptance credential.
    """

    state, error = read_execution_state(default_closeout_execution_path(ROOT, paper))
    if error or not isinstance(state, Mapping) or state.get("paper") != paper:
        return None
    request = state.get("request")
    if (
        not isinstance(request, Mapping)
        or request.get("operational_plan_identity") != plan_identity
    ):
        return None
    progress = state.get("progress")
    if not isinstance(progress, Mapping):
        return None
    stage = str(progress.get("stage") or "").strip()
    completed = progress.get("completed_units")
    total = progress.get("total_units")
    if (
        stage not in STRICT_CLOSEOUT_EXECUTION_STAGES
        or isinstance(completed, bool)
        or not isinstance(completed, int)
        or completed < 0
        or completed > STRICT_CLOSEOUT_STAGE_COUNT
        or total != STRICT_CLOSEOUT_STAGE_COUNT
    ):
        return None
    raw_details = progress.get("details")
    details = dict(raw_details) if isinstance(raw_details, Mapping) else {}
    details["inner_execution_state"] = str(state.get("state") or "")
    details["progress_source"] = "current_closeout_strict_runner"
    return stage, completed, STRICT_CLOSEOUT_STAGE_COUNT, details


def _inner_current_closeout_finalization(
    paper: str,
    plan_identity: str,
) -> dict[str, Any] | None:
    """Return only the current command's already-published finalization record.

    This is operational reporting, not authority.  The accepted graph was
    published inside the child process from its nonserializable runtime pass;
    the worker must never reconstruct that authority from this state.
    """

    state, error = read_execution_state(default_closeout_execution_path(ROOT, paper))
    if error or not isinstance(state, Mapping) or state.get("paper") != paper:
        return None
    request = state.get("request")
    result = state.get("result")
    trace = result.get("trace") if isinstance(result, Mapping) else None
    finalization = (
        trace.get("current_closeout_finalization")
        if isinstance(trace, Mapping)
        and trace.get("current_closeout_published") is True
        else None
    )
    if (
        not isinstance(request, Mapping)
        or request.get("operational_plan_identity") != plan_identity
        or state.get("state") != "complete"
        or state.get("exit_code") != 0
        or not isinstance(finalization, Mapping)
    ):
        return None
    return dict(finalization)


def _worker(
    paper: str,
    *,
    deep_paper_prose: bool,
    launch_id: str,
    plan_identity: str,
) -> int:
    if hasattr(signal, "SIGHUP"):
        signal.signal(signal.SIGHUP, signal.SIG_IGN)
    if not plan_identity:
        print(
            f"replan required: {_plan_receipt_error(paper, deep_paper_prose=deep_paper_prose, plan_identity=plan_identity)}",
            file=sys.stderr,
        )
        return 6
    if not re.fullmatch(r"[0-9a-f]{64}", plan_identity):
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "replan_required",
                    "reason": "closeout plan identity is not a SHA-256 digest",
                    "instruction": (
                        "run closeout_reuse_plan.py again and use its exact command"
                    ),
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 6
    state_path = worker_state_path(paper)
    log_path = worker_log_path(paper, launch_id)
    command = _audit_command(
        paper,
        deep_paper_prose=deep_paper_prose,
        plan_identity=plan_identity,
    )
    request = _request_identity(
        paper,
        deep_paper_prose=deep_paper_prose,
        plan_identity=plan_identity,
    )
    lease, error = CloseoutExecutionLease.acquire(
        state_path,
        paper=paper,
        command=command,
        launch_id=launch_id,
        request=request,
    )
    if lease is None:
        print(error, file=sys.stderr)
        return 2

    child: subprocess.Popen[bytes] | None = None
    try:
        log_path.parent.mkdir(parents=True, exist_ok=True)
        lease.running_payload["log_path"] = str(log_path.relative_to(ROOT))
        atomic_write_json(state_path, lease.running_payload)
        with log_path.open("wb") as log:
            child = subprocess.Popen(
                command,
                cwd=ROOT,
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
                close_fds=True,
                pass_fds=(lease.lock_fd,),
            )
            lease.record_child_process(child.pid)
            lease.heartbeat(
                stage="strict_closeout_startup",
                completed_units=0,
                total_units=STRICT_CLOSEOUT_STAGE_COUNT,
                details={"audit_log_bytes": 0},
            )
            while True:
                try:
                    return_code = child.wait(timeout=15)
                    break
                except subprocess.TimeoutExpired:
                    try:
                        log_bytes = log_path.stat().st_size
                    except OSError:
                        log_bytes = 0
                    inner = _inner_closeout_progress(paper, plan_identity)
                    if inner is None:
                        lease.heartbeat(
                            stage="strict_closeout_startup",
                            completed_units=0,
                            total_units=STRICT_CLOSEOUT_STAGE_COUNT,
                            details={"audit_log_bytes": log_bytes},
                        )
                    else:
                        stage, completed, total, details = inner
                        lease.heartbeat(
                            stage=stage,
                            completed_units=completed,
                            total_units=total,
                            details={**details, "audit_log_bytes": log_bytes},
                        )
            log.flush()
            os.fsync(log.fileno())
        # The child validates the operational plan before doing any work.  A
        # failed child cannot produce an acceptance credential, so preserve its
        # actual failure rather than paying for a second full plan validation
        # and potentially reporting a misleading replan requirement.  A
        # successful child still needs the post-run check for TOCTOU safety.
        final_plan_error = (
            _plan_receipt_error(
                paper,
                deep_paper_prose=deep_paper_prose,
                plan_identity=plan_identity,
            )
            if return_code == 0
            else ""
        )
        finalization: dict[str, Any] | None = None
        finalization_error = ""
        if return_code == 0 and not final_plan_error:
            finalization = _inner_current_closeout_finalization(
                paper,
                plan_identity,
            )
            if finalization is None:
                finalization_error = (
                    "current closeout child exited successfully without its "
                    "in-process publication record"
                )
        operational_exit_code = (
            7 if finalization_error else 6 if final_plan_error else return_code
        )
        lease.complete(
            exit_code=operational_exit_code,
            result={
                "semantic_closeout_passed": (
                    return_code == 0 and not final_plan_error
                ),
                "audit_exit_code": return_code,
                "audit_log": str(log_path.relative_to(ROOT)),
                "audit_log_sha256": _sha256_file(log_path),
                "operational_plan_identity": plan_identity,
                "operational_plan_identity_schema": (OPERATIONAL_PLAN_IDENTITY_SCHEMA),
                **(
                    {"replan_required": True, "reason": final_plan_error}
                    if final_plan_error
                    else {}
                ),
                **(
                    {"closeout_finalization": finalization}
                    if finalization is not None
                    else {}
                ),
                **(
                    {
                        "receipt_finalization_failed": True,
                        "reason": finalization_error,
                    }
                    if finalization_error
                    else {}
                ),
                "acceptance_credential": False,
            },
        )
    except BaseException as exc:
        if child is not None:
            _terminate_child(child)
        if lease.lock_fd >= 0:
            try:
                lease.fail(f"{type(exc).__name__}: {exc}")
            except BaseException:
                pass
        raise
    return operational_exit_code


def _wait_for_worker(
    paper: str,
    process: subprocess.Popen[bytes] | None,
    *,
    launch_id: str | None,
) -> int:
    state_path = worker_state_path(paper)
    while True:
        payload, error = read_execution_state(state_path)
        if error:
            return 2
        matching_launch = (
            payload is not None
            and not error
            and (launch_id is None or payload.get("launch_id") == launch_id)
        )
        if matching_launch:
            assert payload is not None
            state = payload.get("state")
            if state == "complete":
                raw_exit = payload.get("exit_code")
                return raw_exit if isinstance(raw_exit, int) else 2
            if state == "aborted":
                return 2
            if state == "running" and running_execution_summary(state_path) is None:
                return 2
        if process is None and payload is None:
            return 2
        if (
            process is None
            and payload is not None
            and launch_id is not None
            and payload.get("launch_id") != launch_id
        ):
            return 2
        if process is not None:
            return_code = process.poll()
            if return_code is not None and not matching_launch:
                return return_code if return_code != 0 else 2
        time.sleep(1.0)


def _wait_for_start(
    paper: str,
    process: subprocess.Popen[bytes],
    *,
    launch_id: str,
    timeout_seconds: float = 10.0,
) -> int:
    """Wait for lock acquisition or terminal failure, not for closeout itself."""

    state_path = worker_state_path(paper)
    deadline = time.monotonic() + timeout_seconds
    while time.monotonic() < deadline:
        payload, error = read_execution_state(state_path)
        if payload is not None and not error and payload.get("launch_id") == launch_id:
            state = payload.get("state")
            if state == "running":
                return 0
            if state == "complete":
                raw_exit = payload.get("exit_code")
                return raw_exit if isinstance(raw_exit, int) else 2
            if state == "aborted":
                return 2
        return_code = process.poll()
        if return_code is not None:
            return return_code if return_code != 0 else 2
        time.sleep(0.05)
    return 5


def _running_after_lock_transition(
    state_path: Path, *, timeout_seconds: float = 10.0
) -> tuple[dict[str, Any] | None, bool]:
    """Wait for a flock owner to publish state before reading old terminals."""

    active = running_execution_summary(state_path)
    if active is not None or not execution_lock_is_held(state_path):
        return active, False
    deadline = time.monotonic() + timeout_seconds
    while time.monotonic() < deadline:
        active = running_execution_summary(state_path)
        if active is not None:
            return active, False
        if not execution_lock_is_held(state_path):
            return None, False
        time.sleep(0.05)
    return None, execution_lock_is_held(state_path)


def _launch(
    paper: str,
    *,
    deep_paper_prose: bool,
    no_wait: bool,
    plan_identity: str,
    new_run: bool,
) -> int:
    if not plan_identity:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "replan_required",
                    "reason": _plan_receipt_error(
                        paper,
                        deep_paper_prose=deep_paper_prose,
                        plan_identity=plan_identity,
                    ),
                    "instruction": (
                        "run closeout_reuse_plan.py and use its exact command"
                    ),
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 6
    if not re.fullmatch(r"[0-9a-f]{64}", plan_identity):
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "replan_required",
                    "reason": "closeout plan identity is not a SHA-256 digest",
                    "instruction": (
                        "run closeout_reuse_plan.py again and use its exact command"
                    ),
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 6
    engine_error = runtime_engine_registration_error(ROOT)
    if engine_error:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "engine_registration_required",
                    "reason": engine_error,
                    "instruction": (
                        "commit an append-only registered engine transition, then replan"
                    ),
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 6
    state_path = worker_state_path(paper)
    active, unresolved_lock = _running_after_lock_transition(state_path)
    raw_execution_path = default_closeout_execution_path(ROOT, paper)
    request = _request_identity(
        paper,
        deep_paper_prose=deep_paper_prose,
        plan_identity=plan_identity,
    )
    if unresolved_lock:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "startup_unknown",
                    "instruction": "inspect --status; do not launch another closeout",
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 5
    raw_active: dict[str, Any] | None = None
    raw_unresolved_lock = False
    if active is None:
        raw_active, raw_unresolved_lock = _running_after_lock_transition(
            raw_execution_path
        )
    if raw_unresolved_lock:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "raw_closeout_startup_unknown",
                    "instruction": (
                        "inspect the raw closeout state; do not launch another closeout"
                    ),
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 5
    if raw_active is not None:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "already_running": True,
                    "same_request": False,
                    "conflicting_raw_closeout": raw_active,
                    "instruction": "wait for the existing raw closeout; do not launch a duplicate",
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 3
    if active is not None:
        same_request = active.get("request") == request
        print(
            json.dumps(
                {
                    "already_running": True,
                    "same_request": same_request,
                    **active,
                },
                indent=2,
                sort_keys=True,
            )
        )
        if not same_request:
            return 3
        return (
            0
            if no_wait
            else _wait_for_worker(
                paper,
                None,
                launch_id=(
                    str(active.get("launch_id")) if active.get("launch_id") else None
                ),
            )
        )

    prior, prior_error = read_execution_state(state_path)
    if prior_error and state_path.exists() and not new_run:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "state": "recovery_required",
                    "error": prior_error,
                    "instruction": "inspect state/log, then pass --new-run explicitly",
                    "acceptance_credential": False,
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 4
    if prior is not None and not new_run:
        prior_state = str(prior.get("state") or "")
        same_completed_request = (
            prior_state == "complete"
            and bool(plan_identity)
            and prior.get("request") == request
        )
        if same_completed_request:
            final_plan_error = _plan_receipt_error(
                paper,
                deep_paper_prose=deep_paper_prose,
                plan_identity=plan_identity,
                check_runtime_engine=False,
            )
            if final_plan_error:
                print(
                    json.dumps(
                        {
                            "paper": paper,
                            "state": "replan_required",
                            "reason": final_plan_error,
                            "instruction": (
                                "run closeout_reuse_plan.py again and use its exact command"
                            ),
                            "acceptance_credential": False,
                        },
                        indent=2,
                        sort_keys=True,
                    )
                )
                return 6
            raw_exit = prior.get("exit_code")
            print(
                json.dumps(
                    {
                        "paper": paper,
                        "already_complete": True,
                        "new_worker_started": False,
                        "launch_id": prior.get("launch_id"),
                        "exit_code": raw_exit,
                        "result": prior.get("result"),
                        "acceptance_credential": False,
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return raw_exit if isinstance(raw_exit, int) else 2
        if prior_state in {"running", "complete", "aborted"}:
            print(
                json.dumps(
                    {
                        "paper": paper,
                        "state": "new_run_confirmation_required",
                        "prior_state": prior_state,
                        "prior_launch_id": prior.get("launch_id"),
                        "instruction": "pass --new-run after confirming inputs changed or recovery is needed",
                        "acceptance_credential": False,
                    },
                    indent=2,
                    sort_keys=True,
                )
            )
            return 4

    launch_id = uuid.uuid4().hex
    launcher_log = state_path.with_name(LAUNCHER_LOG_FILE)
    launcher_log.parent.mkdir(parents=True, exist_ok=True)
    command = [
        sys.executable,
        str(ROOT / "scripts" / "run_paper_closeout.py"),
        "--paper",
        paper,
        "--worker",
        "--launch-id",
        launch_id,
    ]
    if plan_identity:
        command.extend(["--plan-identity", plan_identity])
    if deep_paper_prose:
        command.append("--deep-paper-prose")
    with launcher_log.open("ab") as bootstrap_log:
        process = subprocess.Popen(
            command,
            cwd=ROOT,
            stdin=subprocess.DEVNULL,
            stdout=bootstrap_log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
            close_fds=True,
        )
    startup_result = (
        _wait_for_start(paper, process, launch_id=launch_id) if no_wait else 0
    )
    print(
        json.dumps(
            {
                "paper": paper,
                "launch_id": launch_id,
                "worker_pid": process.pid,
                "state_path": str(state_path.relative_to(ROOT)),
                "log_path": str(worker_log_path(paper, launch_id).relative_to(ROOT)),
                "startup_acknowledged": startup_result == 0,
                **(
                    {
                        "instruction": (
                            "startup was not confirmed; inspect --status and do not "
                            "launch another closeout"
                        )
                    }
                    if startup_result == 5
                    else {}
                ),
                "acceptance_credential": False,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return (
        startup_result
        if no_wait
        else _wait_for_worker(paper, process, launch_id=launch_id)
    )


def _status(paper: str) -> int:
    try:
        receipt = load_final_closure_receipt(ROOT, paper)
    except FinalClosureReceiptError as exc:
        canonical_closeout: dict[str, Any] = {
            "state": "not_recorded",
            "reason": str(exc),
        }
    else:
        accepted_graph = receipt.payload.get("accepted_graph")
        canonical_closeout = {
            "state": "recorded",
            "receipt_path": receipt.path.relative_to(ROOT).as_posix(),
            "receipt_schema": receipt.payload.get("schema"),
            "closed_at": receipt.payload.get("closed_at"),
            **(
                {
                    "accepted_graph_sha256": accepted_graph.get("graph_sha256"),
                    "accepted_graph_pointer": accepted_graph.get("pointer"),
                }
                if isinstance(accepted_graph, Mapping)
                else {}
            ),
            "validation_command": (
                "python3 scripts/final_closure_receipt.py "
                f"--paper {paper} --check"
            ),
        }

    payload, error, namespace, state_path = effective_closeout_execution_state(
        ROOT, paper
    )
    if error:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "canonical_closeout": canonical_closeout,
                    "operational_execution": {
                        "state": "unreadable",
                        "error": error,
                    },
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    if payload is None:
        print(
            json.dumps(
                {
                    "paper": paper,
                    "canonical_closeout": canonical_closeout,
                    "operational_execution": {
                        "state": "not_started",
                        "acceptance_credential": False,
                    },
                },
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    output = dict(payload)
    output["execution_namespace"] = namespace
    output["live"] = running_execution_summary(state_path) is not None
    print(
        json.dumps(
            {
                "paper": paper,
                "canonical_closeout": canonical_closeout,
                "operational_execution": output,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder under papers/")
    parser.add_argument(
        "--deep-paper-prose",
        action="store_true",
        help="request the explicit deep all-prose audit scope",
    )
    parser.add_argument(
        "--no-wait",
        action="store_true",
        help="start or attach to the worker and return after printing its state path",
    )
    parser.add_argument(
        "--status",
        action="store_true",
        help="print the durable operational state without starting or attaching",
    )
    parser.add_argument(
        "--new-run",
        action="store_true",
        help="explicitly replace a prior terminal or recovery state with a new run",
    )
    parser.add_argument("--worker", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--launch-id", default="", help=argparse.SUPPRESS)
    parser.add_argument(
        "--plan-identity",
        default="",
        help=(
            "required non-authoritative closeout-plan SHA-256 printed by "
            "closeout_reuse_plan.py"
        ),
    )
    args = parser.parse_args()

    if args.plan_identity and not re.fullmatch(r"[0-9a-f]{64}", args.plan_identity):
        parser.error("--plan-identity must be a lowercase SHA-256 digest")

    folder = resolve_paper_folder(ROOT, args.paper)
    if folder is None:
        parser.error("--paper must name one existing paper folder")
    if args.worker and args.no_wait:
        parser.error("--worker cannot be combined with --no-wait")
    if args.status and (
        args.worker or args.no_wait or args.deep_paper_prose or args.new_run
    ):
        parser.error("--status cannot be combined with worker or launch options")
    if args.status:
        return _status(args.paper)
    if not args.plan_identity:
        parser.error(
            "new closeout workers require --plan-identity from "
            "closeout_reuse_plan.py; use --status for legacy inspection"
        )
    if args.worker:
        try:
            launch_id = uuid.UUID(hex=args.launch_id).hex
        except ValueError:
            parser.error("internal worker launch requires a valid --launch-id")
        return _worker(
            args.paper,
            deep_paper_prose=args.deep_paper_prose,
            launch_id=launch_id,
            plan_identity=args.plan_identity,
        )
    if args.launch_id:
        parser.error("--launch-id is internal to --worker")
    return _launch(
        args.paper,
        deep_paper_prose=args.deep_paper_prose,
        no_wait=args.no_wait,
        plan_identity=args.plan_identity,
        new_run=args.new_run,
    )


if __name__ == "__main__":
    raise SystemExit(main())
