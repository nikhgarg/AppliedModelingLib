#!/usr/bin/env python3
"""Run every audit test module in its own Python interpreter.

The evidence issuer deliberately rejects two distinct import identities in one
interpreter. ``unittest discover`` can combine otherwise valid test modules in
exactly that unsupported way, so the complete integration suite must isolate
modules rather than weaken the issuer boundary.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEST_DIRECTORY = ROOT / "scripts" / "tests"
TEST_COUNT_RE = re.compile(r"Ran\s+(\d+)\s+tests?\s+in")


def test_modules(pattern: str) -> list[str]:
    return [
        f"scripts.tests.{path.stem}"
        for path in sorted(TEST_DIRECTORY.glob(pattern))
        if path.is_file()
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--pattern",
        default="test_*.py",
        help="test-module filename pattern (default: %(default)s)",
    )
    parser.add_argument(
        "--start-at",
        metavar="TEST_MODULE",
        help="resume at this module stem or fully qualified module name",
    )
    args = parser.parse_args()
    modules = test_modules(args.pattern)
    if not modules:
        parser.error(f"no test modules match {args.pattern!r}")
    if args.start_at:
        start_module = args.start_at
        if not start_module.startswith("scripts.tests."):
            start_module = f"scripts.tests.{start_module.removesuffix('.py')}"
        try:
            modules = modules[modules.index(start_module) :]
        except ValueError:
            parser.error(f"start module {start_module!r} is not in the selected suite")

    suite_started = time.monotonic()
    total_tests = 0
    failures: list[str] = []
    for index, module in enumerate(modules, start=1):
        print(f"running [{index}/{len(modules)}] {module}", flush=True)
        result = subprocess.run(
            [sys.executable, "-m", "unittest", "-q", module],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        )
        output = result.stdout + result.stderr
        match = TEST_COUNT_RE.search(output)
        if match:
            total_tests += int(match.group(1))
        if result.returncode:
            failures.append(module)
            print(f"FAIL [{index}/{len(modules)}] {module}", flush=True)
            print(output.rstrip(), flush=True)
        elif index % 10 == 0 or index == len(modules):
            print(f"passed {index}/{len(modules)} modules", flush=True)

    elapsed = time.monotonic() - suite_started
    print(
        f"isolated audit tests: {total_tests} tests in {len(modules)} modules; "
        f"{len(failures)} failed modules; {elapsed:.1f}s",
        flush=True,
    )
    if failures:
        print("failed modules: " + ", ".join(failures), flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
