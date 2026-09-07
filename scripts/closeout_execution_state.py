#!/usr/bin/env python3
"""Durable, non-authoritative execution state for one paper closeout.

The semantic closeout remains owned by ``audit_repository.py``.  This module
only prevents an operator from starting the same expensive command twice when
its terminal stream is lost, and leaves a compact result that can be inspected
after the process exits.  Nothing persisted here is an acceptance credential.
"""

from __future__ import annotations

import hashlib
import json
import os
import tempfile
import time
import uuid
import fcntl
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

try:
    from scripts.paper_path_resolution import (
        resolve_paper_folder as resolve_paper_folder,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from paper_path_resolution import resolve_paper_folder as resolve_paper_folder


CLOSEOUT_EXECUTION_STATE_SCHEMA = 1
CLOSEOUT_EXECUTION_STATE_FILE = "paper_closeout_execution.json"
CLOSEOUT_WORKER_STATE_FILE = "paper_closeout_worker.json"
LEGACY_LOCK_WRITE_GRACE_SECONDS = 5.0


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def default_closeout_execution_path(root: Path, paper: str) -> Path:
    return root / "papers" / paper / ".review_traces" / CLOSEOUT_EXECUTION_STATE_FILE


def closeout_worker_state_path(root: Path, paper: str) -> Path:
    """Return the one canonical state and lock namespace used by the launcher."""

    return root / "papers" / paper / ".review_traces" / CLOSEOUT_WORKER_STATE_FILE


def _json_bytes(payload: Mapping[str, Any]) -> bytes:
    return (json.dumps(payload, indent=2, sort_keys=True) + "\n").encode("utf-8")


def atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    """Replace ``path`` atomically after fully writing and syncing its payload."""

    path.parent.mkdir(parents=True, exist_ok=True)
    fd, raw_temp = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temp = Path(raw_temp)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write(_json_bytes(payload))
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temp, path)
        try:
            directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        except OSError:
            directory_fd = -1
        if directory_fd >= 0:
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
    finally:
        try:
            temp.unlink()
        except FileNotFoundError:
            pass


def read_execution_state(path: Path) -> tuple[dict[str, Any] | None, str]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        return None, ""
    except (OSError, json.JSONDecodeError) as exc:
        return None, f"could not read closeout execution state: {exc}"
    if not isinstance(payload, dict):
        return None, "closeout execution state is not an object"
    if payload.get("schema") != CLOSEOUT_EXECUTION_STATE_SCHEMA:
        return None, "closeout execution state has an unsupported schema"
    if payload.get("acceptance_credential") is not False:
        return (
            None,
            "closeout execution state must explicitly deny acceptance authority",
        )
    return payload, ""


def _proc_identity(pid: int) -> dict[str, Any]:
    """Return enough Linux process identity to reject ordinary PID reuse."""

    identity: dict[str, Any] = {"pid": pid}
    proc = Path("/proc") / str(pid)
    try:
        raw_stat = (proc / "stat").read_text(encoding="utf-8")
        # Field 2 is a parenthesized command and may itself contain spaces.
        # Linux fields after the final ')' start at field 3; starttime is 22.
        suffix = raw_stat[raw_stat.rfind(")") + 2 :].split()
        if len(suffix) > 19:
            identity["start_ticks"] = suffix[19]
    except OSError:
        pass
    try:
        command = (proc / "cmdline").read_bytes()
        identity["command_sha256"] = hashlib.sha256(command).hexdigest()
    except OSError:
        pass
    try:
        identity["boot_id"] = (
            Path("/proc/sys/kernel/random/boot_id").read_text(encoding="utf-8").strip()
        )
    except OSError:
        pass
    return identity


def current_process_identity() -> dict[str, Any]:
    return _proc_identity(os.getpid())


def process_identity_is_live(raw_identity: object) -> bool:
    """Return whether the recorded process still has the same process identity."""

    if not isinstance(raw_identity, Mapping):
        return False
    pid = raw_identity.get("pid")
    if not isinstance(pid, int) or isinstance(pid, bool) or pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except PermissionError:
        # An unverifiable legacy owner must not be reclaimed as proven dead.
        return True
    except (ProcessLookupError, ValueError):
        return False
    except OSError:
        return False
    current = _proc_identity(pid)
    for field in ("boot_id", "start_ticks", "command_sha256"):
        recorded = raw_identity.get(field)
        if recorded is not None and current.get(field) != recorded:
            return False
    return True


def execution_lock_is_held(state_path: Path) -> bool:
    """Return whether the persistent per-paper lock has a live OS owner."""

    lock_path = state_path.with_name(f"{state_path.name}.lock")
    try:
        fd = os.open(lock_path, os.O_RDWR)
    except OSError:
        return False
    try:
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            return True
        legacy_conflict = _legacy_lock_conflict(fd, lock_path)
        fcntl.flock(fd, fcntl.LOCK_UN)
        return bool(legacy_conflict)
    finally:
        os.close(fd)


def _legacy_lock_conflict(fd: int, lock_path: Path) -> str:
    """Reject a live or just-created pre-flock sentinel after taking flock.

    Legacy workers did not take an OS lock, so acquiring ``flock`` alone does
    not establish exclusivity with them.  The check must happen before the
    persistent lock file is truncated.  A recent unreadable file is treated as
    a legacy writer in its create-before-write window; an old corrupt file is
    recoverable.
    """

    try:
        os.lseek(fd, 0, os.SEEK_SET)
        raw = os.read(fd, 1024 * 1024)
        stat = os.fstat(fd)
    except OSError as exc:
        return f"could not inspect existing closeout lock: {exc}"
    if not raw:
        age = max(0.0, time.time() - stat.st_mtime)
        return (
            "closeout lock is newly created but not yet readable; retry after "
            f"{LEGACY_LOCK_WRITE_GRACE_SECONDS:g} seconds"
            if age < LEGACY_LOCK_WRITE_GRACE_SECONDS
            else ""
        )
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        age = max(0.0, time.time() - stat.st_mtime)
        return (
            "closeout lock is newly created but not yet readable; retry after "
            f"{LEGACY_LOCK_WRITE_GRACE_SECONDS:g} seconds"
            if age < LEGACY_LOCK_WRITE_GRACE_SECONDS
            else ""
        )
    if not isinstance(payload, Mapping) or payload.get("lock_backend") == "flock_v1":
        return ""
    if not process_identity_is_live(payload.get("process_identity")):
        return ""
    identity = payload.get("process_identity")
    pid = identity.get("pid") if isinstance(identity, Mapping) else "?"
    return f"legacy paper closeout is already running as pid {pid}"


def _lock_path_matches_fd(fd: int, lock_path: Path) -> bool:
    """Return whether ``lock_path`` still names the open locked inode."""

    try:
        opened = os.fstat(fd)
        named = os.stat(lock_path, follow_symlinks=False)
    except OSError:
        return False
    return (opened.st_dev, opened.st_ino) == (named.st_dev, named.st_ino)


def running_execution_summary(path: Path) -> dict[str, Any] | None:
    """Return a compact live-execution summary, or ``None`` when not running."""

    payload, error = read_execution_state(path)
    if error or payload is None or payload.get("state") != "running":
        return None
    if payload.get("lock_backend") == "flock_v1":
        lock_held = execution_lock_is_held(path)
        recorded_owner_live = process_identity_is_live(payload.get("process_identity"))
        recorded_child_live = process_identity_is_live(
            payload.get("child_process_identity")
        )
        if not lock_held and not recorded_owner_live and not recorded_child_live:
            return None
    elif not process_identity_is_live(payload.get("process_identity")):
        # Compatibility with a worker launched by the schema-1 sentinel
        # implementation before flock-backed leases were introduced.
        return None
    identity = payload.get("process_identity")
    return {
        "paper": payload.get("paper"),
        "pid": identity.get("pid") if isinstance(identity, Mapping) else None,
        "started_at": payload.get("started_at"),
        "launch_id": payload.get("launch_id"),
        "request": payload.get("request"),
        "state_path": str(path),
        "instruction": "inspect this state; do not start a duplicate closeout",
    }


def effective_closeout_execution_state(
    root: Path, paper: str
) -> tuple[dict[str, Any] | None, str, str, Path]:
    """Resolve worker state with recovery from a completed detached child.

    If the launcher supervisor dies, its audit child retains the flock until it
    exits and writes the raw closeout terminal state. The abandoned worker JSON
    still says ``running`` afterward; prefer that raw terminal instead of
    scheduling an expensive duplicate audit.
    """

    worker_path = closeout_worker_state_path(root, paper)
    worker, worker_error = read_execution_state(worker_path)
    if worker_error:
        return None, worker_error, "worker", worker_path
    if worker is not None:
        if worker.get("paper") != paper:
            return (
                None,
                "worker closeout state belongs to a different paper",
                "worker_recovery_required",
                worker_path,
            )
        if (
            worker.get("state") != "running"
            or running_execution_summary(worker_path) is not None
        ):
            return worker, "", "worker", worker_path
        raw_path = default_closeout_execution_path(root, paper)
        raw, raw_error = read_execution_state(raw_path)
        if raw_error:
            return None, raw_error, "raw_recovery", raw_path
        if raw is not None:
            correlated_child = (
                raw.get("state") in {"complete", "aborted"}
                and raw.get("paper") == paper
                and isinstance(worker.get("child_process_identity"), Mapping)
                and raw.get("process_identity") == worker.get("child_process_identity")
                and raw.get("command") == worker.get("command")
            )
            if not correlated_child:
                return (
                    None,
                    "abandoned worker state has no exactly correlated terminal raw child state",
                    "raw_recovery_required",
                    raw_path,
                )
            recovered = dict(raw)
            worker_request = worker.get("request")
            if isinstance(worker_request, Mapping):
                recovered["request"] = dict(worker_request)
                recovered_result = (
                    dict(raw.get("result"))
                    if isinstance(raw.get("result"), Mapping)
                    else {}
                )
                for key in (
                    "operational_plan_identity",
                    "operational_plan_identity_schema",
                ):
                    request_value = worker_request.get(key)
                    result_value = recovered_result.get(key)
                    if (
                        result_value is not None
                        and result_value != ""
                        and result_value != request_value
                    ):
                        return (
                            None,
                            "correlated raw child result conflicts with its worker request",
                            "raw_recovery_required",
                            raw_path,
                        )
                    if request_value is not None and request_value != "":
                        recovered_result[key] = request_value
                recovered["result"] = recovered_result
            if worker.get("launch_id"):
                recovered["launch_id"] = worker["launch_id"]
            recovered["recovered_from_worker_state"] = True
            return recovered, "", "raw_recovered_child", raw_path
        return (
            None,
            "worker state says running but has no live lease or raw child state",
            "worker_recovery_required",
            worker_path,
        )

    raw_path = default_closeout_execution_path(root, paper)
    raw, raw_error = read_execution_state(raw_path)
    if (
        not raw_error
        and raw is not None
        and raw.get("state") == "running"
        and running_execution_summary(raw_path) is None
    ):
        return (
            None,
            "raw closeout state says running but has no live lease",
            "raw_recovery_required",
            raw_path,
        )
    if not raw_error and raw is not None and raw.get("paper") != paper:
        return (
            None,
            "raw closeout state belongs to a different paper",
            "raw_recovery_required",
            raw_path,
        )
    return raw, raw_error, "raw_legacy", raw_path


@dataclass
class CloseoutExecutionLease:
    """One process-owned operational lease for a paper closeout command."""

    state_path: Path
    lock_path: Path
    lease_id: str
    running_payload: dict[str, Any]
    lock_fd: int
    monotonic_started: float

    @classmethod
    def acquire(
        cls,
        state_path: Path,
        *,
        paper: str,
        command: list[str],
        launch_id: str = "",
        request: Mapping[str, Any] | None = None,
    ) -> tuple[CloseoutExecutionLease | None, str]:
        state_path = state_path.resolve()
        state_path.parent.mkdir(parents=True, exist_ok=True)
        lock_path = state_path.with_name(f"{state_path.name}.lock")
        lease_id = uuid.uuid4().hex
        process_identity = current_process_identity()
        running_payload: dict[str, Any] = {
            "schema": CLOSEOUT_EXECUTION_STATE_SCHEMA,
            "acceptance_credential": False,
            "operational_recovery_only": True,
            "paper": paper,
            "state": "running",
            "lease_id": lease_id,
            "lock_backend": "flock_v1",
            "process_identity": process_identity,
            "started_at": utc_now(),
            "command": command,
            **({"launch_id": launch_id} if launch_id else {}),
            **({"request": dict(request)} if request is not None else {}),
        }
        lock_payload = {
            "schema": CLOSEOUT_EXECUTION_STATE_SCHEMA,
            "acceptance_credential": False,
            "paper": paper,
            "lease_id": lease_id,
            "lock_backend": "flock_v1",
            "process_identity": process_identity,
            "started_at": running_payload["started_at"],
        }

        prior_state, prior_error = read_execution_state(state_path)
        if (
            not prior_error
            and prior_state is not None
            and prior_state.get("state") == "running"
            and (
                process_identity_is_live(prior_state.get("process_identity"))
                or process_identity_is_live(prior_state.get("child_process_identity"))
            )
        ):
            return None, f"paper closeout is already running; inspect {state_path}"

        for _attempt in range(3):
            created_lock_file = False
            try:
                fd = os.open(lock_path, os.O_RDWR | os.O_CREAT | os.O_EXCL, 0o600)
                created_lock_file = True
            except FileExistsError:
                try:
                    fd = os.open(lock_path, os.O_RDWR)
                except OSError as exc:
                    return None, f"could not open paper closeout execution lock: {exc}"
            except OSError as exc:
                return None, f"could not open paper closeout execution lock: {exc}"
            try:
                try:
                    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                except BlockingIOError:
                    os.close(fd)
                    return (
                        None,
                        f"paper closeout is already running; inspect {state_path}",
                    )
                legacy_conflict = (
                    "" if created_lock_file else _legacy_lock_conflict(fd, lock_path)
                )
                if legacy_conflict:
                    fcntl.flock(fd, fcntl.LOCK_UN)
                    os.close(fd)
                    return None, f"{legacy_conflict}; inspect {state_path}"
                if not _lock_path_matches_fd(fd, lock_path):
                    fcntl.flock(fd, fcntl.LOCK_UN)
                    os.close(fd)
                    continue

                lock_bytes = _json_bytes(lock_payload)
                os.ftruncate(fd, 0)
                os.lseek(fd, 0, os.SEEK_SET)
                written = 0
                while written < len(lock_bytes):
                    written += os.write(fd, lock_bytes[written:])
                os.fsync(fd)
                if not _lock_path_matches_fd(fd, lock_path):
                    fcntl.flock(fd, fcntl.LOCK_UN)
                    os.close(fd)
                    continue
                atomic_write_json(state_path, running_payload)
                if not _lock_path_matches_fd(fd, lock_path):
                    fcntl.flock(fd, fcntl.LOCK_UN)
                    os.close(fd)
                    continue
            except BaseException:
                try:
                    fcntl.flock(fd, fcntl.LOCK_UN)
                finally:
                    os.close(fd)
                raise
            return (
                cls(
                    state_path=state_path,
                    lock_path=lock_path,
                    lease_id=lease_id,
                    running_payload=running_payload,
                    lock_fd=fd,
                    monotonic_started=time.monotonic(),
                ),
                "",
            )
        return (
            None,
            f"closeout lock pathname changed during acquisition; inspect {state_path}",
        )

    def record_child_process(self, pid: int) -> None:
        """Persist the audit child's identity while retaining the same lease."""

        self.running_payload["child_process_identity"] = _proc_identity(pid)
        atomic_write_json(self.state_path, self.running_payload)

    def heartbeat(
        self,
        *,
        stage: str,
        completed_units: int | None = None,
        total_units: int | None = None,
        cache_hits: int | None = None,
        cache_misses: int | None = None,
        details: Mapping[str, Any] | None = None,
    ) -> None:
        """Atomically publish non-authoritative progress while holding the lease."""

        if self.lock_fd < 0 or not _lock_path_matches_fd(self.lock_fd, self.lock_path):
            raise RuntimeError("cannot heartbeat a closeout lease that is not held")
        progress: dict[str, Any] = {
            "schema": 1,
            "stage": str(stage).strip() or "unknown",
            "heartbeat_at": utc_now(),
            "elapsed_seconds": round(
                max(
                    0.0,
                    time.monotonic() - self.monotonic_started,
                ),
                3,
            ),
        }
        for key, value in (
            ("completed_units", completed_units),
            ("total_units", total_units),
            ("cache_hits", cache_hits),
            ("cache_misses", cache_misses),
        ):
            if value is not None:
                if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                    raise ValueError(f"closeout heartbeat {key} must be nonnegative")
                progress[key] = value
        if details:
            progress["details"] = dict(details)
        self.running_payload["progress"] = progress
        atomic_write_json(self.state_path, self.running_payload)

    def complete(
        self,
        *,
        exit_code: int,
        result: Mapping[str, Any],
    ) -> None:
        # Progress describes only a live operation. Keeping the last heartbeat
        # beside a terminal result made successful workers appear stuck at an
        # earlier inner stage. The terminal result already carries the final
        # closeout DAG, so publish one outcome authority and drop stale progress.
        terminal_base = {
            key: value
            for key, value in self.running_payload.items()
            if key != "progress"
        }
        payload = {
            **terminal_base,
            "state": "complete",
            "completed_at": utc_now(),
            "exit_code": exit_code,
            "result": dict(result),
        }
        # Retain the lease if the terminal write fails so the caller can record
        # an aborted result without admitting a concurrent replacement worker.
        atomic_write_json(self.state_path, payload)
        self._release_lock()

    def fail(self, message: str) -> None:
        payload = {
            **self.running_payload,
            "state": "aborted",
            "completed_at": utc_now(),
            "failure": message,
        }
        try:
            atomic_write_json(self.state_path, payload)
        finally:
            self._release_lock()

    def _release_lock(self) -> None:
        if self.lock_fd < 0:
            return
        try:
            fcntl.flock(self.lock_fd, fcntl.LOCK_UN)
        finally:
            os.close(self.lock_fd)
            self.lock_fd = -1
