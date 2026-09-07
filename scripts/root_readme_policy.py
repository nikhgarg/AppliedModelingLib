#!/usr/bin/env python3
"""Keep generators away from the hand-written root README.

Human edits to README.md are allowed directly. This policy only blocks generated
README outputs and generated-block markers; agent-facing documentation still
requires explicit user instructions before an LLM edits the root README.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Iterable


_ROOT_PARSER = argparse.ArgumentParser(add_help=False)
_ROOT_PARSER.add_argument("--repo", type=Path)
_ROOT_ARGS, _ROOT_UNKNOWN = _ROOT_PARSER.parse_known_args(sys.argv[1:])
ROOT = (
    _ROOT_ARGS.repo.resolve()
    if _ROOT_ARGS.repo is not None
    else Path(
        os.environ.get("APPLIEDMODELINGLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
    ).resolve()
)
ROOT_README = ROOT / "README.md"

GENERATED_MARKERS = (
    "<!-- BEGIN GENERATED",
    "<!-- END GENERATED",
)


def root_relative(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def validate_root_readme() -> list[str]:
    """Return policy violations for generated root README edits."""

    messages: list[str] = []
    if not ROOT_README.exists():
        return [f"{root_relative(ROOT_README)} is missing"]

    text = ROOT_README.read_text(encoding="utf-8")
    for marker in GENERATED_MARKERS:
        if marker in text:
            messages.append(
                f"{root_relative(ROOT_README)} contains generated-output marker `{marker}`"
            )

    return messages


def assert_root_readme_policy() -> None:
    messages = validate_root_readme()
    if messages:
        raise ValueError("root README policy failed:\n- " + "\n- ".join(messages))


def assert_root_readme_locked() -> None:
    """Backward-compatible name for the non-locking README policy."""

    assert_root_readme_policy()


def assert_no_root_readme_outputs(paths: Iterable[Path]) -> None:
    root_readme = ROOT_README.resolve()
    offenders = [root_relative(path) for path in paths if path.resolve() == root_readme]
    if offenders:
        raise ValueError(
            "generators must not write the hand-written root README: "
            + ", ".join(offenders)
        )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo",
        type=Path,
        default=ROOT,
        help="repository checkout to validate (default: this script's repository)",
    )
    parser.add_argument(
        "--write-lock",
        action="store_true",
        help="deprecated no-op; human README edits no longer require a hash lock",
    )
    args = parser.parse_args()

    if args.repo.resolve() != ROOT:
        parser.error("--repo must be resolved during process bootstrap")

    if args.write_lock:
        print("root README hash locks are no longer used; nothing to write")
        return 0

    messages = validate_root_readme()
    if messages:
        print("root README policy failed:")
        for message in messages:
            print(f"- {message}")
        return 1
    print("root README policy passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
