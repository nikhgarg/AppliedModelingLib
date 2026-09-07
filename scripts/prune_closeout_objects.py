#!/usr/bin/env python3
"""List or remove only content-addressed closeout objects with no live reference.

The default is read-only. ``--apply`` deletes an object only after scanning all
paper review-trace JSON and the transitive references of already reachable
objects. Tracked audit evidence and canonical paper artifacts are never in the
object-store namespace and cannot be selected by this command.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable, Mapping

try:
    from scripts.closeout_content_store import (
        CONTENT_OBJECT_STORE_RELATIVE,
        is_closeout_object_reference,
    )
except ModuleNotFoundError:
    from closeout_content_store import (
        CONTENT_OBJECT_STORE_RELATIVE,
        is_closeout_object_reference,
    )


ROOT = Path(__file__).resolve().parents[1]


def _references(value: object) -> set[str]:
    found: set[str] = set()
    if isinstance(value, Mapping):
        if is_closeout_object_reference(value):
            found.add(str(value["path"]))
        for child in value.values():
            found.update(_references(child))
    elif isinstance(value, list):
        for child in value:
            found.update(_references(child))
    return found


def _json_payloads(paths: Iterable[Path]) -> Iterable[object]:
    for path in paths:
        try:
            yield json.loads(path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            continue


def reachable_closeout_object_paths(root: Path) -> set[str]:
    """Return the transitive object paths owned by current trace references."""

    root = root.resolve()
    trace_paths = sorted((root / "papers").glob("*/.review_traces/**/*.json"))
    reachable: set[str] = set()
    pending: list[str] = []
    for payload in _json_payloads(trace_paths):
        pending.extend(sorted(_references(payload)))
    while pending:
        relative = pending.pop()
        if relative in reachable:
            continue
        reachable.add(relative)
        path = root / relative
        for payload in _json_payloads([path]):
            pending.extend(sorted(_references(payload) - reachable))
    return reachable


def unreferenced_closeout_objects(root: Path) -> list[Path]:
    root = root.resolve()
    store = root / CONTENT_OBJECT_STORE_RELATIVE
    reachable = reachable_closeout_object_paths(root)
    return [
        path
        for path in sorted(store.glob("*/*.json"))
        if path.relative_to(root).as_posix() not in reachable
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--apply",
        action="store_true",
        help="delete the listed unreferenced objects after the complete scan",
    )
    args = parser.parse_args()
    candidates = unreferenced_closeout_objects(ROOT)
    bytes_total = sum(path.stat().st_size for path in candidates)
    for path in candidates:
        print(path.relative_to(ROOT))
    print(
        json.dumps(
            {
                "unreferenced_object_count": len(candidates),
                "unreferenced_bytes": bytes_total,
                "applied": args.apply,
                "acceptance_credential": False,
            },
            sort_keys=True,
        )
    )
    if args.apply:
        for path in candidates:
            path.unlink()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
