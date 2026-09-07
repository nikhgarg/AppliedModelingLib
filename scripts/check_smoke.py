#!/usr/bin/env python3
"""Run lightweight smoke checks for key reusable artifacts.

The smoke pass focuses on importability and visibility:

1. Build `AppliedModelingLib` with the shared prelude.
2. Compile a curated `SmokeChecks.lean` file that imports standard front-facing modules.
3. Optionally, compile non-active paper root files.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
EXAMPLES = ROOT / "examples"
AUDIT_CONFIG = PAPERS / "audit_config.json"


def active_paper_names() -> set[str]:
    if not AUDIT_CONFIG.exists():
        return set()
    payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should contain a JSON object")
    if payload.get("schema") != 1:
        raise ValueError(f"{AUDIT_CONFIG.relative_to(ROOT)} should use schema 1")
    raw = payload.get("active_papers", [])
    if not isinstance(raw, list):
        raise ValueError("active_papers should be a list")
    return {str(item).strip() for item in raw if str(item).strip()}


ACTIVE_PAPERS = active_paper_names()


def run(cmd: list[str], *, cwd: Path = ROOT) -> None:
    print(f"running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=str(cwd), check=False, text=True, capture_output=True)
    print(result.stdout, end="")
    if result.returncode != 0:
        print(result.stderr, end="")
        raise SystemExit(result.returncode)


def paper_roots(include_active: bool) -> list[str]:
    roots: list[str] = []
    for path in sorted(PAPERS.iterdir()):
        if not path.is_dir():
            continue
        if path.name == "TEMPLATE":
            continue
        if path.name in ACTIVE_PAPERS and not include_active:
            continue
        root = PAPERS / f"{path.name}.lean"
        if root.exists():
            roots.append(path.name)
    return roots


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--include-papers", action="store_true", help="also compile non-active paper root modules")
    parser.add_argument("--include-active", action="store_true", help="include active papers in the paper-root pass")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    include_active = args.include_active

    run(["lake", "build", "+AppliedModelingLib"])
    run(["lake", "env", "lean", str(EXAMPLES / "SmokeChecks.lean")])

    if args.include_papers:
        for paper in paper_roots(include_active):
            run(["lake", "build", f"+{paper}"])

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
