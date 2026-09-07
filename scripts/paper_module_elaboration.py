#!/usr/bin/env python3
"""Path-independent inventory and build command for paper-owned Lean sources.

Lake root targets may reuse imported paper artifacts. Current closeout and the
private paper checkpoint therefore share this one Git-backed source inventory
and one dependency-aware rehashed Lake command over every returned file. This
module does not parse Lean or decide semantic coverage.
"""

from __future__ import annotations

import subprocess
from collections.abc import Iterable
from pathlib import Path


class PaperModuleElaborationError(ValueError):
    """The tracked paper-module inventory is absent, unsafe, or incomplete."""


def tracked_paper_module_sources(root: Path, paper: str) -> tuple[Path, ...]:
    """Return every tracked paper-local source plus its tracked root module."""

    root = root.resolve()
    if not paper or Path(paper).name != paper or "/" in paper or "\\" in paper:
        raise PaperModuleElaborationError("paper must be one safe path component")
    papers = root / "papers"
    paper_dir = papers / paper
    if not paper_dir.is_dir():
        raise PaperModuleElaborationError(f"paper folder does not exist: {paper}")
    try:
        tracked = subprocess.run(
            [
                "git",
                "ls-files",
                "--",
                f"papers/{paper}",
                f"papers/{paper}.lean",
            ],
            cwd=root,
            text=True,
            capture_output=True,
            check=True,
        ).stdout.splitlines()
    except (OSError, subprocess.CalledProcessError) as exc:
        raise PaperModuleElaborationError(
            f"could not enumerate tracked paper modules: {exc}"
        ) from exc

    sources = tuple(
        sorted(
            (root / entry for entry in tracked if entry.endswith(".lean")),
            key=lambda path: path.relative_to(root).as_posix(),
        )
    )
    # Paper-local semantic Specs and exact theorem endpoints may be colocated
    # in PaperInterface.lean or split into a tracked ProofInterface.lean.
    # The tracked-source inventory below builds every owned module either way;
    # requiring the optional split file would reject a closed colocated paper
    # without adding a Lean-owned membership or proof check.
    required = (paper_dir / "PaperInterface.lean", papers / f"{paper}.lean")
    missing = [
        path.relative_to(root).as_posix()
        for path in required
        if not path.is_file() or path not in sources
    ]
    if missing:
        raise PaperModuleElaborationError(
            "current paper closeout requires tracked modules: " + ", ".join(missing)
        )
    if not sources:
        raise PaperModuleElaborationError(
            f"no tracked Lean modules found for paper `{paper}`"
        )
    return sources


def rehashed_module_build_command(
    root: Path,
    sources: Iterable[Path],
    *,
    single_threaded: bool,
) -> list[str]:
    """Return the one Lake command that rebuilds the exact source inventory."""

    root = root.resolve()
    targets: list[str] = []
    seen: set[str] = set()
    for source in sources:
        resolved = source.resolve()
        try:
            target = resolved.relative_to(root).as_posix()
        except ValueError as exc:
            raise PaperModuleElaborationError(
                f"paper build source is outside the repository: {source}"
            ) from exc
        if resolved.suffix != ".lean":
            raise PaperModuleElaborationError(
                f"paper build source is not a Lean file: {target}"
            )
        if target in seen:
            raise PaperModuleElaborationError(
                f"paper build source is duplicated: {target}"
            )
        seen.add(target)
        targets.append(target)
    if not targets:
        raise PaperModuleElaborationError("paper build source inventory is empty")

    command = ["lake", "--rehash", "build", *targets]
    if single_threaded:
        return ["env", "LEAN_NUM_THREADS=1", *command]
    return command


__all__ = [
    "PaperModuleElaborationError",
    "rehashed_module_build_command",
    "tracked_paper_module_sources",
]
