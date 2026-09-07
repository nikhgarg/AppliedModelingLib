#!/usr/bin/env python3
"""Report shared-worktree state without changing files, refs, or stashes."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess
import sys
from typing import Iterable

try:
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:
    from tomllib_compat import tomllib


REPO_ROOT = Path(__file__).resolve().parent.parent
LEASE_DIR = REPO_ROOT / "coordination" / "active-work"


def git(args: Iterable[str], *, cwd: Path = REPO_ROOT, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["git", "-C", str(cwd), *args], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if check and result.returncode:
        raise RuntimeError(result.stderr.strip() or "git command failed")
    return result


def status_records(path: Path) -> int:
    output = git(["status", "--porcelain=v1", "-z"], cwd=path).stdout
    return sum(1 for record in output.split("\0") if len(record) >= 3 and record[2] == " ")


def is_merged(ref: str) -> bool:
    return git(["merge-base", "--is-ancestor", ref, "main"], check=False).returncode == 0


def open_branches(prefix: str, remote: bool) -> list[str]:
    refs = git(["for-each-ref", "--format=%(refname:short)", prefix]).stdout.splitlines()
    result: list[str] = []
    for ref in refs:
        if remote and (ref in {"origin", "origin/main"} or ref.startswith("origin/archive/")):
            continue
        if not remote and ref == "main":
            continue
        if not is_merged(ref):
            ahead = git(["rev-list", "--count", f"main..{ref}"]).stdout.strip()
            result.append(f"{ref} (ahead {ahead})")
    return result


def leases() -> list[str]:
    if not LEASE_DIR.exists():
        return []
    result: list[str] = []
    for path in sorted(LEASE_DIR.glob("*.toml")):
        try:
            with path.open("rb") as handle:
                data = tomllib.load(handle)
            agent = data["agent"]
            scopes = ", ".join(data["scopes"])
            summary = data["summary"]
            result.append(f"{agent}: {scopes} — {summary}")
        except (OSError, tomllib.TOMLDecodeError, KeyError, TypeError):
            result.append(f"INVALID LEASE: {path.relative_to(REPO_ROOT)}")
    return result


def worktrees() -> list[str]:
    blocks = [block.splitlines() for block in git(["worktree", "list", "--porcelain"]).stdout.split("\n\n") if block]
    result: list[str] = []
    for block in blocks:
        path_line = next((line for line in block if line.startswith("worktree ")), None)
        if path_line is None:
            continue
        path = Path(path_line.removeprefix("worktree "))
        ref = next((line.removeprefix("branch refs/heads/") for line in block if line.startswith("branch ")), "detached")
        prunable = any(line.startswith("prunable") for line in block)
        if prunable or not path.exists():
            result.append(f"{path} [{ref}] — prunable")
        else:
            result.append(f"{path} [{ref}] — {status_records(path)} dirty record(s)")
    return result


def print_section(title: str, entries: list[str]) -> None:
    print(title + ":")
    for entry in entries or ["none"]:
        print("  " + entry)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true", help="exit nonzero when attention items remain")
    args = parser.parse_args()
    branch = git(["branch", "--show-current"]).stdout.strip() or "detached"
    dirty = status_records(REPO_ROOT)
    upstream_exists = git(["show-ref", "--verify", "--quiet", "refs/remotes/origin/main"], check=False).returncode == 0
    divergence = git(["rev-list", "--left-right", "--count", "HEAD...origin/main"]).stdout.strip() if upstream_exists else "unavailable"
    stashes = git(["stash", "list", "--format=%gd: %s"]).stdout.splitlines()
    local_open = open_branches("refs/heads", remote=False)
    remote_open = open_branches("refs/remotes/origin", remote=True)
    lease_entries = leases()
    worktree_entries = worktrees()

    print(f"Repository: {REPO_ROOT}")
    print(f"Current branch: {branch}")
    print(f"Current worktree: {dirty} dirty record(s)")
    print(f"HEAD...origin/main: {divergence} (local-only, remote-only)")
    print_section("Active leases", lease_entries)
    print_section("Stashes", stashes)
    print_section("Unmerged local branches", local_open)
    print_section("Unmerged origin branches", remote_open)
    print_section("Worktrees", worktree_entries)

    worktree_attention = any("prunable" in entry or not entry.endswith("0 dirty record(s)") for entry in worktree_entries)
    attention = bool(dirty or lease_entries or stashes or local_open or remote_open or worktree_attention)
    if args.strict and attention:
        print("Strict status: attention required.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as exc:
        print(f"shared-worktree-status: {exc}", file=sys.stderr)
        raise SystemExit(2)
