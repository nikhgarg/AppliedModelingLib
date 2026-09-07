#!/usr/bin/env python3
"""Lean-owned transitive axiom-closure extraction shared by audit lanes."""

from __future__ import annotations

import os
import re
import signal
import subprocess
import tempfile
from pathlib import Path
from typing import Iterable


APPROVED_LEAN_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
PRINT_AXIOMS_RE = re.compile(
    r"'([^']+)'\s+depends on axioms:\s*\[(.*?)\]", re.S
)
PRINT_NO_AXIOMS_RE = re.compile(
    r"'([^']+)'\s+does not depend on any axioms"
)


class LeanAxiomClosureError(RuntimeError):
    """Lean could not produce the requested complete axiom closure."""


def parse_print_axioms_output(output: str) -> dict[str, set[str]]:
    """Parse Lean ``#print axioms`` output by fully qualified declaration."""

    parsed: dict[str, set[str]] = {}
    for match in PRINT_NO_AXIOMS_RE.finditer(output):
        parsed[match.group(1)] = set()
    for match in PRINT_AXIOMS_RE.finditer(output):
        parsed[match.group(1)] = {
            axiom.strip()
            for axiom in re.split(r",|\n", match.group(2))
            if axiom.strip()
        }
    return parsed


def _run_lean_script(
    root: Path,
    script: str,
    *,
    timeout_seconds: int,
) -> subprocess.CompletedProcess[str]:
    """Run one bounded temporary Lean script and kill its process group on timeout."""

    with tempfile.TemporaryDirectory(prefix="lean-axiom-closure-") as tmpdir:
        script_path = Path(tmpdir) / "axiom_closure.lean"
        script_path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(script_path)],
                cwd=str(root),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                start_new_session=True,
            )
            stdout, stderr = proc.communicate(timeout=timeout_seconds)
        except OSError as exc:
            raise LeanAxiomClosureError(f"Lean axiom audit could not run: {exc}") from exc
        except subprocess.TimeoutExpired as exc:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            try:
                proc.communicate(timeout=1)
            except (OSError, subprocess.TimeoutExpired):
                pass
            raise LeanAxiomClosureError("Lean axiom audit timed out") from exc
    return subprocess.CompletedProcess(
        proc.args,
        proc.returncode,
        stdout=stdout,
        stderr=stderr,
    )


def run_lean_axiom_closures(
    root: Path,
    import_module: str,
    declaration_names: Iterable[str],
    *,
    timeout_seconds: int = 180,
    build_timeout_seconds: int = 600,
    require_build: bool = True,
) -> dict[str, set[str]]:
    """Return Lean's complete transitive axiom set for each requested declaration.

    This function is the single execution path used by repository audits and
    terminal semantic revalidation. Python schedules the request and parses
    Lean's output; Lean itself computes the recursive dependency closure.
    """

    names = sorted({str(name).strip() for name in declaration_names if str(name).strip()})
    if not names:
        return {}
    module = str(import_module).strip()
    if not module:
        raise LeanAxiomClosureError("Lean axiom audit has no import module")
    if require_build:
        try:
            build = subprocess.run(
                ["lake", "build", f"+{module}"],
                cwd=str(root),
                check=False,
                capture_output=True,
                text=True,
                timeout=build_timeout_seconds,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise LeanAxiomClosureError(
                f"Lean axiom audit could not build {module}: {exc}"
            ) from exc
        if build.returncode != 0:
            details = (build.stderr or build.stdout).strip().splitlines()
            excerpt = " ".join(details[:3])[:600] if details else "nonzero status"
            raise LeanAxiomClosureError(
                f"Lean axiom audit could not build {module}: {excerpt}"
            )

    script = "\n".join(
        [
            f"import {module}",
            "set_option pp.universes false",
            "",
            *(f"#print axioms {name}" for name in names),
            "",
        ]
    )
    proc = _run_lean_script(root, script, timeout_seconds=timeout_seconds)
    if proc.returncode != 0:
        details = (proc.stderr or proc.stdout).strip().splitlines()
        excerpt = " ".join(details[:3])[:600] if details else "nonzero status"
        raise LeanAxiomClosureError(f"Lean axiom audit failed: {excerpt}")
    parsed = parse_print_axioms_output(proc.stdout)
    missing = sorted(set(names) - set(parsed))
    extra = sorted(set(parsed) - set(names))
    if missing or extra:
        detail = []
        if missing:
            detail.append("missing " + ", ".join(missing))
        if extra:
            detail.append("unexpected " + ", ".join(extra))
        raise LeanAxiomClosureError(
            "Lean axiom audit returned an inexact declaration inventory: "
            + "; ".join(detail)
        )
    return {name: parsed[name] for name in names}
