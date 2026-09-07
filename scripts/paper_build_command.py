#!/usr/bin/env python3
"""Canonical path-independent paper build commands.

This module owns the exact command-level invariant shared by current closeout
validation and historical evidence projection. It is deliberately independent
of either protocol so the current acceptance path never imports migration code
merely to recognize its own build target.
"""

from __future__ import annotations

import shlex


def is_exact_portable_paper_build_argv(argv: list[str], paper: str) -> bool:
    """Recognize Lake's two path-independent spellings of one paper target."""

    return argv in (
        ["lake", "build", paper],
        ["lake", "build", "+" + paper],
    )


def is_exact_portable_paper_build_command(command: object, paper: str) -> bool:
    """Recognize an exact paper-root build command before any work starts."""

    if not isinstance(command, str) or not command.strip():
        return False
    try:
        argv = shlex.split(command)
    except ValueError:
        return False
    return is_exact_portable_paper_build_argv(argv, paper)
