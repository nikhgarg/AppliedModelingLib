#!/usr/bin/env python3
"""Manage path leases and exact checkpoint commits in the shared private worktree."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
from typing import Any, Iterable

try:
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:
    from tomllib_compat import tomllib


REPO_ROOT = Path(__file__).resolve().parent.parent
LEASE_DIR = REPO_ROOT / "coordination" / "active-work"
AGENT_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.-]{0,63}$")


class WorkflowError(RuntimeError):
    """A safe workflow precondition was not met."""


def git(args: Iterable[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        ["git", "-C", str(REPO_ROOT), *args], text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
    )
    if check and result.returncode:
        raise WorkflowError(result.stderr.strip() or "git command failed")
    return result


def git_lines(args: Iterable[str]) -> list[str]:
    return [line for line in git(args).stdout.split("\0") if line]


def validate_agent(agent: str) -> str:
    if not AGENT_RE.fullmatch(agent):
        raise WorkflowError("agent must use letters, digits, '.', '_' or '-' and be at most 64 characters")
    return agent


def normalize_scope(raw: str) -> str:
    if not raw or raw.startswith("/") or "\\" in raw:
        raise WorkflowError(f"scope must be a repository-relative slash path: {raw!r}")
    path = PurePosixPath(raw)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise WorkflowError(f"scope must be a concrete repository-relative path: {raw!r}")
    scope = path.as_posix()
    if scope == ".git" or scope.startswith(".git/"):
        raise WorkflowError("a lease may not claim .git")
    return scope


def lease_path(agent: str) -> Path:
    return LEASE_DIR / f"{validate_agent(agent)}.toml"


def load_lease(path: Path) -> dict[str, Any]:
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except (OSError, tomllib.TOMLDecodeError) as exc:
        raise WorkflowError(f"cannot read lease {path.relative_to(REPO_ROOT)}: {exc}") from exc
    if not isinstance(data.get("agent"), str) or not isinstance(data.get("scopes"), list):
        raise WorkflowError(f"lease {path.relative_to(REPO_ROOT)} is missing agent or scopes")
    data["scopes"] = [normalize_scope(scope) for scope in data["scopes"]]
    return data


def active_leases() -> list[tuple[Path, dict[str, Any]]]:
    if not LEASE_DIR.exists():
        return []
    return [(path, load_lease(path)) for path in sorted(LEASE_DIR.glob("*.toml"))]


def scopes_overlap(first: str, second: str) -> bool:
    return first == second or first.startswith(second + "/") or second.startswith(first + "/")


def owns(path: str, scopes: list[str]) -> bool:
    return any(path == scope or path.startswith(scope + "/") for scope in scopes)


def toml_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def write_lease(path: Path, data: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    scopes = ", ".join(toml_string(scope) for scope in data["scopes"])
    contents = "\n".join([
        f"agent = {toml_string(data['agent'])}",
        f"branch = {toml_string(data['branch'])}",
        f"worktree = {toml_string(data['worktree'])}",
        f"created_utc = {toml_string(data['created_utc'])}",
        f"summary = {toml_string(data['summary'])}",
        f"scopes = [{scopes}]",
        "",
    ])
    temporary = path.with_suffix(".toml.tmp")
    temporary.write_text(contents, encoding="utf-8")
    os.replace(temporary, path)


def current_branch() -> str:
    branch = git(["branch", "--show-current"]).stdout.strip()
    return branch or f"detached:{git(['rev-parse', '--short', 'HEAD']).stdout.strip()}"


def command_claim(args: argparse.Namespace) -> int:
    agent = validate_agent(args.agent)
    target = lease_path(agent)
    if target.exists():
        raise WorkflowError(f"{target.relative_to(REPO_ROOT)} already exists; release it before making a new claim")
    scopes = sorted(set(normalize_scope(scope) for scope in args.scope))
    if not scopes:
        raise WorkflowError("claim at least one --scope")
    for other_path, other in active_leases():
        for scope in scopes:
            for other_scope in other["scopes"]:
                if scopes_overlap(scope, other_scope):
                    raise WorkflowError(
                        f"{scope} overlaps {other_scope}, claimed by {other['agent']} "
                        f"in {other_path.relative_to(REPO_ROOT)}"
                    )
    summary = args.summary.strip()
    if not summary or "\n" in summary:
        raise WorkflowError("summary must be one nonempty line")
    worktree = git(["rev-parse", "--show-toplevel"]).stdout.strip()
    timestamp = dt.datetime.now(dt.timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")
    write_lease(target, {
        "agent": agent,
        "branch": current_branch(),
        "worktree": worktree,
        "created_utc": timestamp,
        "summary": summary,
        "scopes": scopes,
    })
    print(f"Claimed {', '.join(scopes)} for {agent}: {target.relative_to(REPO_ROOT)}")
    print("Commit the lease with the next scoped checkpoint; do not use git stash to change tasks.")
    return 0


def command_list(_: argparse.Namespace) -> int:
    leases = active_leases()
    if not leases:
        print("No active work claims.")
        return 0
    for path, lease in leases:
        print(f"{lease['agent']}: {', '.join(lease['scopes'])}")
        print(f"  {lease['branch']} | {lease['summary']} | {path.relative_to(REPO_ROOT)}")
    return 0


def command_release(args: argparse.Namespace) -> int:
    target, lease = lease_for(args.agent)
    lease_relative = target.relative_to(REPO_ROOT).as_posix()
    unfinished = [
        path for path in changed_paths()
        if path != lease_relative and owns(path, lease["scopes"])
    ]
    if unfinished:
        raise WorkflowError(
            "cannot release while claimed work is uncommitted: " + ", ".join(unfinished)
        )
    if staged_paths():
        raise WorkflowError("cannot release with a nonempty index; finish or unstage the existing scoped checkpoint first")
    message = args.message.strip()
    if not message:
        raise WorkflowError("release requires a nonempty --message")
    git(["rm", "--", lease_relative])
    git(["commit", "-m", message, "--", lease_relative])
    print(f"Released {lease_relative}: {git(['rev-parse', '--short', 'HEAD']).stdout.strip()}")
    return 0


def lease_for(agent: str) -> tuple[Path, dict[str, Any]]:
    target = lease_path(agent)
    if not target.exists():
        raise WorkflowError(f"no active lease for {agent}; claim paths before editing or checkpointing")
    return target, load_lease(target)


def command_check(args: argparse.Namespace) -> int:
    _, lease = lease_for(args.agent)
    outside = [normalize_scope(path) for path in args.path if not owns(normalize_scope(path), lease["scopes"])]
    if outside:
        raise WorkflowError(f"paths outside {args.agent}'s lease: {', '.join(outside)}")
    print("All paths are covered by the active lease.")
    return 0


def changed_paths() -> list[str]:
    paths = set(git_lines(["diff", "--name-only", "-z"]))
    paths.update(git_lines(["ls-files", "--others", "--exclude-standard", "-z"]))
    return sorted(paths)


def staged_paths() -> list[str]:
    return git_lines(["diff", "--cached", "--name-only", "-z"])


def command_checkpoint(args: argparse.Namespace) -> int:
    lease_file, lease = lease_for(args.agent)
    scopes = lease["scopes"]
    allowed = [*scopes, lease_file.relative_to(REPO_ROOT).as_posix()]
    foreign_staged = [path for path in staged_paths() if not owns(path, allowed)]
    if foreign_staged:
        raise WorkflowError(
            "the index already contains paths outside this lease; do not commit them: " + ", ".join(foreign_staged)
        )
    candidates = [path for path in changed_paths() if owns(path, allowed)]
    if args.dry_run:
        print("Would stage only:")
        print("\n".join(candidates) if candidates else "(no claimed changes)")
        return 0
    if candidates:
        git(["add", "-A", "--", *candidates])
    staged = staged_paths()
    foreign_staged = [path for path in staged if not owns(path, allowed)]
    if foreign_staged:
        raise WorkflowError("refusing a mixed checkpoint: " + ", ".join(foreign_staged))
    if not staged:
        print("No claimed changes to checkpoint.")
        return 0
    text_paths = [path for path in staged if not path.lower().endswith(".pdf")]
    if text_paths:
        check = git(["diff", "--cached", "--check", "--", *text_paths], check=False)
        if check.returncode:
            raise WorkflowError(check.stdout.strip() or check.stderr.strip() or "whitespace check failed")
    message = args.message.strip()
    if not message:
        raise WorkflowError("checkpoint requires a nonempty --message")
    git(["commit", "-m", message])
    print(f"Checkpoint committed for {args.agent}: {git(['rev-parse', '--short', 'HEAD']).stdout.strip()}")
    return 0


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    commands = result.add_subparsers(dest="command", required=True)
    claim = commands.add_parser("claim", help="claim disjoint repository paths")
    claim.add_argument("--agent", required=True)
    claim.add_argument("--scope", action="append", required=True)
    claim.add_argument("--summary", required=True)
    claim.set_defaults(func=command_claim)
    listing = commands.add_parser("list", help="list active path leases")
    listing.set_defaults(func=command_list)
    release = commands.add_parser("release", help="release an agent's lease")
    release.add_argument("--agent", required=True)
    release.add_argument("--message", required=True)
    release.set_defaults(func=command_release)
    check = commands.add_parser("check", help="verify paths belong to an active lease")
    check.add_argument("--agent", required=True)
    check.add_argument("--path", action="append", required=True)
    check.set_defaults(func=command_check)
    checkpoint = commands.add_parser("checkpoint", help="commit only claimed paths")
    checkpoint.add_argument("--agent", required=True)
    checkpoint.add_argument("--message", required=True)
    checkpoint.add_argument("--dry-run", action="store_true")
    checkpoint.set_defaults(func=command_checkpoint)
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        return args.func(args)
    except WorkflowError as exc:
        print(f"work-claim: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
