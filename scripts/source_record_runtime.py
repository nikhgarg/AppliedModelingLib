#!/usr/bin/env python3
"""Operational progress and bounded subprocess runtime for source-record audits.

This module owns diagnostics and process lifecycle only. It does not select
paper claims, construct semantic obligations, decide cache admission, or issue
audit evidence.
"""

from __future__ import annotations

from contextvars import ContextVar
import fcntl
import json
import os
import signal
import subprocess
import sys
import threading
import time
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping


SOURCE_RECORD_LAKE_BUILD_TIMEOUT_SECONDS = 600
SOURCE_RECORD_LAKE_ENV_TIMEOUT_SECONDS = 60
SOURCE_RECORD_LEAN_ELABORATION_TIMEOUT_SECONDS = 600
SOURCE_RECORD_LEAN_CHECK_TIMEOUT_SECONDS = 600
SOURCE_RECORD_PROGRESS_HEARTBEAT_SECONDS = 30
_ACTIVE_SOURCE_RECORD_AUDIT_LOCK_FD: ContextVar[int | None] = ContextVar(
    "active_source_record_audit_lock_fd", default=None
)
_ACTIVE_SOURCE_RECORD_AUDIT_PROGRESS_UPDATER: ContextVar[
    Callable[[str], None] | None
] = ContextVar("active_source_record_audit_progress_updater", default=None)


@dataclass(frozen=True)
class CapturedSubprocessResult:
    """Result of one bounded source-record child process."""

    returncode: int
    stdout: str
    elapsed_seconds: float
    timed_out: bool = False


def _as_text_output(value: object) -> str:
    """Normalize subprocess output after a timeout across Python versions."""

    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return str(value)


def source_record_progress(
    message: str,
    *,
    progress_updater: Callable[[str], None] | None = None,
) -> None:
    """Emit diagnostics on stderr without contaminating JSON stdout output."""

    try:
        print(f"source-record audit: {message}", file=sys.stderr, flush=True)
    except (BrokenPipeError, OSError, ValueError):
        pass
    updater = (
        progress_updater
        if progress_updater is not None
        else _ACTIVE_SOURCE_RECORD_AUDIT_PROGRESS_UPDATER.get()
    )
    if updater is not None:
        try:
            updater(message)
        except (OSError, ValueError):
            pass


@contextmanager
def source_record_progress_phase(
    phase: str,
    *,
    heartbeat_seconds: float = SOURCE_RECORD_PROGRESS_HEARTBEAT_SECONDS,
):
    """Report a long audit phase while black-box Meta checks are running.

    Several semantic-contract passes live in shared audit helpers and do not
    expose their individual Lean subprocesses here.  A lightweight heartbeat
    makes a slow, serialized source-record run distinguishable from a lost
    terminal stream.  It is diagnostic only and never changes audit results.
    """

    started = time.monotonic()
    stopped = threading.Event()
    interval = max(float(heartbeat_seconds), 0.1)
    progress_updater = _ACTIVE_SOURCE_RECORD_AUDIT_PROGRESS_UPDATER.get()

    def heartbeat() -> None:
        while not stopped.wait(interval):
            source_record_progress(
                f"{phase} still running ({time.monotonic() - started:.0f}s elapsed)",
                progress_updater=progress_updater,
            )

    source_record_progress(f"{phase} started")
    worker = threading.Thread(
        target=heartbeat,
        name="source-record-audit-progress",
        daemon=True,
    )
    worker.start()
    try:
        yield
    finally:
        stopped.set()
        worker.join(timeout=interval + 1)
        source_record_progress(
            f"{phase} finished ({time.monotonic() - started:.1f}s elapsed)"
        )


def structural_scan_progress_summary(diagnostics: Mapping[str, Any]) -> str:
    """Render operational reuse counters without adding them to audit evidence."""

    raw_stages = diagnostics.get("stages")
    stages = (
        [stage for stage in raw_stages if isinstance(stage, Mapping)]
        if isinstance(raw_stages, list)
        else [diagnostics]
    )

    def total(field: str) -> int:
        return sum(
            int(stage.get(field) or 0)
            for stage in stages
            if type(stage.get(field) or 0) is int
        )

    return (
        f"{total('requested_count')} requested; "
        f"{total('reused_count')} reused; "
        f"{total('fresh_count')} fresh; "
        f"{total('missing_count')} missing; "
        f"{total('batch_count')} Lean batches"
    )


def run_source_record_subprocess(
    command: list[str],
    *,
    cwd: Path,
    phase: str,
    timeout_seconds: float,
    heartbeat_seconds: float = SOURCE_RECORD_PROGRESS_HEARTBEAT_SECONDS,
) -> CapturedSubprocessResult:
    """Run one Lake/Lean command with bounded, group-wide cleanup.

    ``subprocess.run(..., timeout=...)`` only kills its direct child.  Lake can
    have a Lean child of its own, so the audit instead creates a process group
    and kills/reaps that whole group on timeout.  Capturing child output keeps
    generated JSON deterministic; heartbeats go only to stderr.
    """

    timeout = max(float(timeout_seconds), 0.0)
    interval = max(float(heartbeat_seconds), 0.1)
    started = time.monotonic()
    source_record_progress(f"{phase} started (timeout {timeout:.0f}s)")
    lock_fd = _ACTIVE_SOURCE_RECORD_AUDIT_LOCK_FD.get()
    popen_kwargs: dict[str, object] = {
        "cwd": str(cwd),
        "stdout": subprocess.PIPE,
        "stderr": subprocess.STDOUT,
        "text": True,
        "start_new_session": True,
        "close_fds": True,
    }
    if lock_fd is not None:
        try:
            os.fstat(lock_fd)
        except OSError as exc:
            elapsed = time.monotonic() - started
            message = f"could not inherit active source-record lock for {phase}: {exc}"
            source_record_progress(f"{phase} failed to start ({elapsed:.1f}s elapsed)")
            return CapturedSubprocessResult(125, message, elapsed)
        popen_kwargs["pass_fds"] = (lock_fd,)
    try:
        proc = subprocess.Popen(command, **popen_kwargs)
    except OSError as exc:
        elapsed = time.monotonic() - started
        message = f"could not launch {phase}: {type(exc).__name__}: {exc}"
        source_record_progress(f"{phase} failed to start ({elapsed:.1f}s elapsed)")
        return CapturedSubprocessResult(125, message, elapsed)

    try:
        while True:
            elapsed = time.monotonic() - started
            remaining = timeout - elapsed
            if remaining <= 0:
                raise subprocess.TimeoutExpired(command, timeout)
            try:
                stdout, _stderr = proc.communicate(timeout=min(interval, remaining))
            except subprocess.TimeoutExpired:
                elapsed = time.monotonic() - started
                if elapsed < timeout:
                    source_record_progress(
                        f"{phase} still running ({elapsed:.0f}s elapsed)"
                    )
                    continue
                raise
            elapsed = time.monotonic() - started
            source_record_progress(
                f"{phase} finished ({elapsed:.1f}s elapsed; exit {proc.returncode})"
            )
            return CapturedSubprocessResult(
                proc.returncode,
                _as_text_output(stdout),
                elapsed,
            )
    except subprocess.TimeoutExpired as exc:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            stdout, _stderr = proc.communicate(timeout=5)
        except (OSError, subprocess.TimeoutExpired):
            stdout = exc.output
        elapsed = time.monotonic() - started
        output = _as_text_output(stdout)
        timeout_message = (
            f"source-record audit timed out during {phase} after {elapsed:.1f}s "
            f"(limit {timeout:.0f}s); killed its Lake/Lean process group"
        )
        source_record_progress(timeout_message)
        if output:
            output = f"{output}\n{timeout_message}\n"
        else:
            output = timeout_message + "\n"
        return CapturedSubprocessResult(124, output, elapsed, timed_out=True)
    except BaseException:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            proc.communicate(timeout=5)
        except (OSError, subprocess.TimeoutExpired):
            pass
        raise

class SourceRecordAuditLockUnavailable(RuntimeError):
    """Raised when another expensive source-record audit owns the repo lock."""


SOURCE_RECORD_AUDIT_LOCK_SCHEMA = 1
SOURCE_RECORD_AUDIT_LOCK_HEARTBEAT_SECONDS = 15.0
SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES = 16 * 1024


def source_record_audit_lock_path(root: Path) -> Path:
    """Return the one repository-wide lock used by expensive source scans."""

    return root / ".lake" / "source-record-audit.lock"


def _source_record_audit_lock_owner_payload(
    owner: Mapping[str, object] | None,
    *,
    started_at_epoch: float,
) -> dict[str, object]:
    """Build bounded diagnostic metadata without treating it as authority."""

    payload: dict[str, object] = {
        "schema": SOURCE_RECORD_AUDIT_LOCK_SCHEMA,
        "pid": os.getpid(),
        "started_at_epoch": started_at_epoch,
        "heartbeat_at_epoch": time.time(),
    }
    if not isinstance(owner, Mapping):
        return payload
    # These are observability labels only.  Restrict the serialized shape so a
    # caller cannot turn a lock file into an arbitrary diagnostic payload.
    for field in ("paper", "operation", "request_id"):
        value = str(owner.get(field) or "").strip()
        if value:
            payload[field] = value[:256]
    return payload


def _write_source_record_audit_lock_owner(
    handle: Any, payload: Mapping[str, object]
) -> None:
    """Rewrite owner metadata on the locked inode; never replace its path."""

    handle.seek(0)
    handle.truncate()
    json.dump(dict(payload), handle, sort_keys=True)
    handle.flush()
    os.fsync(handle.fileno())


def _bounded_source_record_audit_lock_owner_text(handle: Any) -> str:
    """Read bounded lock diagnostics without letting malformed bytes mask a lock."""

    try:
        handle.seek(0)
        text = handle.read(SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES + 1)
    except (OSError, UnicodeError):
        return ""
    if len(text) > SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES:
        return ""
    return text


def source_record_audit_lock_status(root: Path) -> dict[str, object]:
    """Return a read-only observation of the serialized source-scan lock.

    The PID is diagnostic only: sandboxed workers can live in an invisible PID
    namespace, so this function deliberately does not infer liveness or
    reclaim a lock.  Lock ownership remains the kernel ``flock`` on this exact
    inode; deleting or replacing the path would permit overlapping Lean scans.
    """

    root = root.resolve()
    lock_path = source_record_audit_lock_path(root)
    observed_at_epoch = time.time()
    result: dict[str, object] = {
        "schema": SOURCE_RECORD_AUDIT_LOCK_SCHEMA,
        "lock_path": str(lock_path),
        "observed_at_epoch": observed_at_epoch,
        "held": False,
        "owner_visibility": "not_available",
    }
    try:
        handle = lock_path.open("rb")
    except FileNotFoundError:
        result["state"] = "absent"
        return result
    except OSError as exc:
        result.update({"state": "unreadable", "error": str(exc)})
        return result
    lock_acquired = False
    try:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            result["held"] = True
            result["state"] = "held"
        else:
            lock_acquired = True
            result["state"] = "available"
        try:
            raw_owner = handle.read(SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES + 1)
        except OSError as exc:
            result.update({"owner_visibility": "unreadable", "error": str(exc)})
            return result
        if len(raw_owner) > SOURCE_RECORD_AUDIT_LOCK_MAX_OWNER_BYTES:
            result["owner_visibility"] = "too_large"
            return result
        try:
            owner_text = raw_owner.decode("utf-8")
        except UnicodeDecodeError:
            result["owner_visibility"] = "updating_or_malformed"
            return result
        if not owner_text.strip():
            result["owner_visibility"] = "empty"
            return result
        try:
            owner = json.loads(owner_text)
        except json.JSONDecodeError:
            result["owner_visibility"] = "updating_or_malformed"
            return result
        if not isinstance(owner, Mapping):
            result["owner_visibility"] = "malformed"
            return result
        owner_payload = dict(owner)
        result["owner"] = owner_payload
        result["owner_visibility"] = "last_owner" if lock_acquired else "recorded"
        heartbeat = owner_payload.get("heartbeat_at_epoch") or owner_payload.get(
            "started_at_epoch"
        )
        if isinstance(heartbeat, (int, float)) and not isinstance(heartbeat, bool):
            result["owner_age_seconds"] = max(0.0, observed_at_epoch - heartbeat)
        return result
    finally:
        if lock_acquired:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
        handle.close()


@contextmanager
def source_record_audit_lock(
    root: Path,
    timeout_seconds: float,
    *,
    owner: Mapping[str, object] | None = None,
):
    """Serialize isolated Lean source-record scans for one repository.

    The audit runs several isolated `lake`/`lean` processes.  Running multiple
    instances concurrently can exhaust the sandbox's process/descriptor budget
    and leave detached scans behind after a caller loses its stream.  A
    repository-local advisory lock makes that failure deterministic and gives
    callers a clear retry path instead.
    """

    lock_path = source_record_audit_lock_path(root)
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    with lock_path.open("a+", encoding="utf-8") as handle:
        deadline = time.monotonic() + max(timeout_seconds, 0.0)
        while True:
            try:
                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError as exc:
                if time.monotonic() >= deadline:
                    owner = _bounded_source_record_audit_lock_owner_text(handle).strip()
                    owner_detail = f" Current holder: {owner}." if owner else ""
                    raise SourceRecordAuditLockUnavailable(
                        "another source-record audit is already running for "
                        f"{root}; wait for it to finish and retry"
                        f"{owner_detail}"
                    ) from exc
                time.sleep(min(0.1, max(deadline - time.monotonic(), 0.0)))
        lock_context_token = _ACTIVE_SOURCE_RECORD_AUDIT_LOCK_FD.set(handle.fileno())
        started_at_epoch = time.time()
        owner_payload = _source_record_audit_lock_owner_payload(
            owner, started_at_epoch=started_at_epoch
        )
        owner_write_lock = threading.Lock()
        heartbeat_stop = threading.Event()
        progress_sequence = 0

        def record_progress(message: str) -> None:
            """Publish bounded phase diagnostics on the held lease inode."""

            nonlocal progress_sequence
            normalized = " ".join(str(message).split())
            if not normalized:
                return
            observed_at_epoch = time.time()
            try:
                with owner_write_lock:
                    progress_sequence += 1
                    owner_payload["progress_sequence"] = progress_sequence
                    owner_payload["progress_message"] = normalized[:512]
                    owner_payload["progress_at_epoch"] = observed_at_epoch
                    owner_payload["heartbeat_at_epoch"] = observed_at_epoch
                    _write_source_record_audit_lock_owner(handle, owner_payload)
            except OSError:
                # A lost diagnostic write cannot alter lock ownership or the
                # audit result. The independent heartbeat may still succeed.
                pass

        def refresh_owner_heartbeat() -> None:
            while not heartbeat_stop.wait(SOURCE_RECORD_AUDIT_LOCK_HEARTBEAT_SECONDS):
                owner_payload["heartbeat_at_epoch"] = time.time()
                try:
                    with owner_write_lock:
                        _write_source_record_audit_lock_owner(handle, owner_payload)
                except OSError:
                    # The lock holder still owns the inode.  A later status
                    # read can report stale metadata, but must never trigger
                    # an unsafe automatic replacement scan.
                    return

        heartbeat = threading.Thread(
            target=refresh_owner_heartbeat,
            name="source-record-audit-lock-heartbeat",
            daemon=True,
        )
        progress_context_token = _ACTIVE_SOURCE_RECORD_AUDIT_PROGRESS_UPDATER.set(
            record_progress
        )
        try:
            with owner_write_lock:
                _write_source_record_audit_lock_owner(handle, owner_payload)
            heartbeat.start()
            yield
        finally:
            heartbeat_stop.set()
            heartbeat.join(timeout=SOURCE_RECORD_AUDIT_LOCK_HEARTBEAT_SECONDS + 1)
            try:
                with owner_write_lock:
                    handle.seek(0)
                    handle.truncate()
                    handle.flush()
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
            finally:
                _ACTIVE_SOURCE_RECORD_AUDIT_PROGRESS_UPDATER.reset(
                    progress_context_token
                )
                _ACTIVE_SOURCE_RECORD_AUDIT_LOCK_FD.reset(lock_context_token)
