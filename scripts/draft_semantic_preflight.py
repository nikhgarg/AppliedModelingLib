#!/usr/bin/env python3
"""Print a non-evidence source/interface semantic preflight for one paper."""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.current_closeout.draft_semantic_preflight import (
    DraftSemanticPreflightError,
    build_draft_semantic_preflight,
)


def _atomic_write_text(path: Path, value: str) -> None:
    """Persist a non-evidence diagnostic bundle without partial output."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(value)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, path)
    except BaseException:
        temporary_path.unlink(missing_ok=True)
        raise


def _output_path(folder: Path, raw_path: str) -> Path:
    """Accept only ignored per-paper diagnostic paths for a preflight bundle."""

    candidate = Path(raw_path)
    if not candidate.is_absolute():
        candidate = ROOT / candidate
    candidate = candidate.resolve()
    trace_directory = (folder / ".review_traces").resolve()
    try:
        candidate.relative_to(trace_directory)
    except ValueError as exc:
        raise ValueError(
            "--output must be inside the paper's .review_traces directory"
        ) from exc
    return candidate


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True, help="paper folder under papers/")
    parser.add_argument(
        "--output",
        help=(
            "atomically persist the exact non-evidence stdout bundle under "
            "papers/<Paper>/.review_traces"
        ),
    )
    args = parser.parse_args()
    folder = ROOT / "papers" / args.paper
    if not folder.is_dir():
        parser.error(f"unknown paper `{args.paper}`")
    output_path: Path | None = None
    if args.output:
        try:
            output_path = _output_path(folder, args.output)
        except ValueError as exc:
            print(f"draft semantic preflight output refused: {exc}", file=sys.stderr)
            return 3
    try:
        payload = build_draft_semantic_preflight(ROOT, folder)
    except DraftSemanticPreflightError as exc:
        rendered_error = f"draft semantic preflight refused: {exc}\n"
        if output_path is not None:
            try:
                _atomic_write_text(output_path, rendered_error)
            except OSError as output_error:
                print(
                    f"draft semantic preflight output refused: {output_error}",
                    file=sys.stderr,
                )
                return 3
        sys.stderr.write(rendered_error)
        return 2
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if output_path is not None:
        try:
            _atomic_write_text(output_path, rendered)
        except OSError as exc:
            print(f"draft semantic preflight output refused: {exc}", file=sys.stderr)
            return 3
    sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
