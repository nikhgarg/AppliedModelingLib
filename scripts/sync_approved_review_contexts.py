#!/usr/bin/env python3
"""Synchronize settled maintainer decisions into one paper's review source map."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.current_closeout.approved_contexts import (
    apply_approved_review_context_projection,
    current_approved_review_context_projection,
    expected_approved_review_context_projection,
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    folder = ROOT / "papers" / args.paper
    path = folder / "audit" / "paper_statement_map.json"
    try:
        source_map = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as exc:
        print(f"approved review context sync refused: {exc}", file=sys.stderr)
        return 1
    if not isinstance(source_map, dict):
        print("approved review context sync refused: source map is not an object", file=sys.stderr)
        return 1
    expected, error = expected_approved_review_context_projection(folder, source_map)
    if error or expected is None:
        print(f"approved review context sync refused: {error}", file=sys.stderr)
        return 1
    if current_approved_review_context_projection(source_map) == expected:
        print(f"{args.paper}: approved review contexts are current")
        return 0
    if not args.write:
        print(f"{args.paper}: approved review contexts need synchronization")
        return 2
    updated = apply_approved_review_context_projection(source_map, expected)
    path.write_text(
        json.dumps(updated, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(f"{args.paper}: synchronized approved review contexts in {path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
