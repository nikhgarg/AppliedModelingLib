#!/usr/bin/env python3
"""Fail-closed publication of canonical source-record audit artifacts."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import sys
import tempfile
from typing import Any


def load_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def source_record_audit_output_path(
    args: argparse.Namespace, root: Path, paper_dir: Path
) -> Path:
    """Resolve this invocation's requested generated audit artifact."""

    if args.out:
        candidate = Path(args.out)
        return candidate if candidate.is_absolute() else root / candidate
    return canonical_source_record_audit_path(paper_dir)


def canonical_source_record_audit_path(paper_dir: Path) -> Path:
    """Return the one canonical aggregate-cache artifact for a paper."""

    return paper_dir / "audit" / "source_record_audit.json"


def atomic_write_text_if_changed(path: Path, text: str) -> bool:
    """Atomically replace one generated text artifact only when bytes differ."""

    data = text.encode("utf-8")
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        existing_stat = path.stat()
    except OSError:
        existing_stat = None
    if existing_stat is not None and existing_stat.st_size == len(data):
        unchanged = True
        offset = 0
        try:
            with path.open("rb") as existing:
                while chunk := existing.read(1024 * 1024):
                    end = offset + len(chunk)
                    if chunk != memoryview(data)[offset:end]:
                        unchanged = False
                        break
                    offset = end
        except OSError:
            unchanged = False
        if unchanged and offset == len(data):
            return False

    temporary_path: Path | None = None
    try:
        with tempfile.NamedTemporaryFile(
            mode="wb",
            dir=path.parent,
            prefix=f".{path.name}.",
            suffix=".tmp",
            delete=False,
        ) as temporary:
            temporary_path = Path(temporary.name)
            os.fchmod(
                temporary.fileno(),
                (existing_stat.st_mode & 0o777) if existing_stat is not None else 0o644,
            )
            temporary.write(data)
            temporary.flush()
            os.fsync(temporary.fileno())
        os.replace(temporary_path, path)
        temporary_path = None
    finally:
        if temporary_path is not None:
            temporary_path.unlink(missing_ok=True)
    return True



def finalize_source_record_audit_output(
    args: argparse.Namespace,
    root: Path,
    paper_dir: Path,
    encoded: str,
    *,
    lean_returncode: int,
    has_recursion_failures: bool,
    input_change_during_scan_error: str = "",
) -> int:
    """Emit a diagnostic result and refresh canonical evidence only on success.

    A caller may request a noncanonical ``--out`` artifact for debugging even
    when Lean or recursion fails.  The canonical paper-local sidecar is
    evidence, however: it is written only after a non-``--no-lean`` run has
    returned success and reported no recursion failures. A normal full scan
    writes that canonical sidecar and emits a compact receipt. Printing the
    potentially multi-megabyte raw payload is an explicit ``--stdout``
    diagnostic mode, never the default transport.
    """

    output_path: Path | None = None
    canonical_path = canonical_source_record_audit_path(paper_dir)
    output_is_canonical = False
    emit_stdout = bool(getattr(args, "stdout", False))
    if args.out:
        output_path = source_record_audit_output_path(args, root, paper_dir)
        output_is_canonical = output_path.resolve() == canonical_path.resolve()
        # Preserve separate diagnostic artifacts, but defer a direct canonical
        # destination until every run-success condition below has been checked.
        if not output_is_canonical:
            atomic_write_text_if_changed(output_path, encoded + "\n")
    elif not emit_stdout and not args.no_lean:
        # A successful normal scan is evidence-producing work. Do not make a
        # caller reconstruct a canonical path from an unbounded stdout stream.
        output_path = canonical_path
        output_is_canonical = True
    if emit_stdout:
        print(encoded)

    if input_change_during_scan_error:
        if output_is_canonical:
            print(
                "refusing to replace canonical source-record audit because "
                + input_change_during_scan_error,
                file=sys.stderr,
            )
        return 4
    if lean_returncode != 0:
        if output_is_canonical:
            print(
                "refusing to replace canonical source-record audit after a failed Lean check",
                file=sys.stderr,
            )
        return 2
    if has_recursion_failures:
        if output_is_canonical:
            print(
                "refusing to replace canonical source-record audit after recursion failures",
                file=sys.stderr,
            )
        return 3
    if args.no_lean:
        if output_is_canonical:
            print(
                "refusing to replace canonical source-record audit from a --no-lean run",
                file=sys.stderr,
            )
            return 2
        return 0

    # A noncanonical output is a transport copy, and a direct/default canonical
    # destination reaches this point only after all full-run acceptance
    # conditions passed.
    if output_path is not None:
        atomic_write_text_if_changed(canonical_path, encoded + "\n")
    if not emit_stdout:
        print(
            json.dumps(
                {
                    "paper": args.paper,
                    "source_record_audit": str(canonical_path),
                    "canonical_refreshed": output_path is not None,
                    "lean_returncode": lean_returncode,
                },
                sort_keys=True,
            )
        )
    return 0
