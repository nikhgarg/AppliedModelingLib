#!/usr/bin/env python3
"""Select exact-commit CI work without changing paper evidence or proof scope."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path, PurePosixPath
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scripts.lean_import_closure import (
    _candidate_blob_ids, _batch_blob_texts, imported_modules,
)
from scripts.tomllib_compat import tomllib


def git(repo, *args):
    return subprocess.check_output(["git", "-C", str(repo), *args])


def successful_main_base(repo: Path, head: str, runs: dict, repository: str) -> str:
    """Select an already successful ancestor, never an unverified push parent."""
    head = git(repo, "rev-parse", "--verify", head + "^{commit}").decode().strip()
    best = ""
    for run in runs.get("workflow_runs", []):
        sha = run.get("head_sha", "")
        if (run.get("status") != "completed" or run.get("conclusion") != "success"
                or run.get("event") != "push" or run.get("head_branch") != "main"
                or run.get("path", "").split("@")[0] != ".github/workflows/lean_action_ci.yml"
                or (run.get("head_repository") or {}).get("full_name") != repository
                or not isinstance(sha, str) or not re.fullmatch(r"[0-9a-f]{40}", sha)):
            continue
        def ancestor(a, b):
            return subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", a, b],
                                  stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
        if ancestor(sha, head) and (not best or ancestor(best, sha)):
            best = sha
    return best


def plan(repo: Path, base: str, head: str = "HEAD") -> dict:
    base = git(repo, "rev-parse", "--verify", base + "^{commit}").decode().strip()
    head = git(repo, "rev-parse", "--verify", head + "^{commit}").decode().strip()
    paths = sorted(filter(None, git(repo, "diff", "--no-renames", "--name-only", "-z", base, head).decode().split("\0")))
    result = {"mode": "integration", "base": base, "head": head, "papers": [], "targets": [], "changed_paths": paths}
    if subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor", base, head]).returncode:
        return result
    libraries = tomllib.loads(git(repo, "show", head + ":lakefile.toml").decode()).get("lean_lib", [])
    paper_targets = {p["name"] for p in libraries if p.get("srcDir") == "papers"}
    all_targets = {p["name"] for p in libraries}

    def owner(path):
        parts = PurePosixPath(path).parts
        if len(parts) >= 2 and parts[0] == "papers":
            name = PurePosixPath(parts[1]).stem if len(parts) == 2 else parts[1]
            return name if name in paper_targets else None
        return None

    def doc(path):
        return (path in {"README.md", "CONTRIBUTING.md", "CITATION.cff", ".github/workflows/pages.yml"}
                or path.startswith(("docs/", "site/", ".github/ISSUE_TEMPLATE/"))
                or path == ".github/pull_request_template.md")

    aggregates = {"papers/status.json", "papers/human_status.json", "docs/PAPER_STATUS.md", "site/index.html"}
    # Documentation scopes cannot hide build controls or Lean sources in a
    # documentation directory. Unknown paths and routing changes stay broad.
    if any(path.endswith(".lean") and not owner(path) for path in paths):
        return result
    if all(doc(path) or path in aggregates for path in paths):
        return {**result, "mode": "docs"}
    if not all(owner(path) or path in aggregates for path in paths):
        return result
    if any(set(library) - {"name", "srcDir", "roots"} for library in libraries):
        return result
    routes = []
    for library in libraries:
        roots = library.get("roots", [library["name"]])
        if not isinstance(roots, list) or not all(isinstance(root, str) for root in roots):
            return result
        routes.extend((root, library["name"], library.get("srcDir", ".")) for root in roots)

    def import_owner(module):
        matches = {target for root, target, _ in routes if module == root or module.startswith(root + ".")}
        return next(iter(matches)) if len(matches) == 1 else None

    def source_owner(path):
        matches = set()
        for root, target, source_dir in routes:
            try:
                relative = PurePosixPath(path).relative_to(source_dir)
            except ValueError:
                continue
            module = str(relative.with_suffix("")).replace("/", ".")
            if module == root or module.startswith(root + "."):
                matches.add(target)
        return next(iter(matches)) if len(matches) == 1 else None

    papers = {owner(path) for path in paths if owner(path)}
    tracked = set(filter(None, git(repo, "ls-tree", "-r", "--name-only", "-z", head).decode().split("\0")))
    if any(f"papers/{paper}/status.json" not in tracked for paper in papers):
        return result
    changed_lean = {owner(path) for path in paths if path.endswith(".lean")}
    targets = set(changed_lean)
    if changed_lean:
        # Union both committed dependency graphs: deletions and removed imports
        # still invalidate former consumers. Collapsing modules to their Lake
        # target is conservative and includes non-root modules within a paper.
        views = [_candidate_blob_ids(repo, candidate="tree", treeish=ref) for ref in (base, head)]
        blobs = {sha for view in views for path, sha in view.items()
                 if source_owner(path) in all_targets}
        texts = _batch_blob_texts(repo, blobs)
        imports = {sha: {import_owner(name) for name in imported_modules(text)} for sha, text in texts.items()}
        dependents = {}
        for view in views:
            for path, sha in view.items():
                target = source_owner(path)
                if target not in all_targets:
                    continue
                for dependency in imports[sha] & all_targets:
                    if dependency != target:
                        dependents.setdefault(dependency, set()).add(target)
        pending = list(targets)
        while pending:
            for dependent in dependents.get(pending.pop(), set()) - targets:
                targets.add(dependent)
                pending.append(dependent)
        if targets - paper_targets:
            return result
        papers |= targets
    return {**result, "mode": "papers", "papers": sorted(papers), "targets": sorted(targets)}


def run_checks(repo, selection, *, public=False):
    if selection["mode"] != "papers":
        raise ValueError("Scoped paper checks require a papers plan")
    source_flag = ["--allow-missing-source-bytes"] if public else []
    for paper in selection["papers"]:
        commands = [
            ["scripts/audit_conclusion_provenance.py", "--paper", paper],
            ["scripts/audit_evidence_integrity.py", "--paper", paper, *source_flag],
            ["scripts/review_dashboard.py", "--paper", paper, "--statement-check"],
            ["scripts/review_dashboard.py", "--paper", paper, "--paper-coverage-check"],
            ["scripts/audit_repository.py", "--paper", paper, "--include-active", "--library-premise-audit", "--info-limit", "0", *source_flag],
        ]
        for command in commands:
            require_clean_head(repo, selection["head"])
            print("Checking:", " ".join(command), flush=True)
            subprocess.run([sys.executable, *command], cwd=repo, check=True)
            require_clean_head(repo, selection["head"])


def require_clean_head(repo, head):
    if git(repo, "rev-parse", "HEAD").decode().strip() != head:
        raise ValueError("CI head changed during validation")
    subprocess.run(["git", "-C", str(repo), "diff", "--quiet", "HEAD", "--"], check=True)
    untracked = git(repo, "ls-files", "--others", "--exclude-standard", "-z").decode().split("\0")
    if any(path.endswith(".lean") for path in untracked):
        raise ValueError("Untracked Lean sources cannot participate in CI validation")


def prune_build_cache(repo: Path, head: str):
    """Remove orphaned module interfaces after restoring an older build cache."""
    root = repo / ".lake/build/lib/lean"
    if not root.exists():
        return
    if not root.resolve().is_relative_to(repo.resolve()):
        raise ValueError("Project build cache must stay inside the checkout")
    paths = _candidate_blob_ids(repo, candidate="tree", treeish=head)
    libraries = tomllib.loads(git(repo, "show", head + ":lakefile.toml").decode()).get("lean_lib", [])
    modules = set()
    for source_dir in {library.get("srcDir", ".") for library in libraries}:
        for path in paths:
            try:
                relative = PurePosixPath(path).relative_to(source_dir)
            except ValueError:
                continue
            modules.add(str(relative.with_suffix("")).replace("/", "."))
    for path in root.rglob("*"):
        relative = str(path.relative_to(root))
        for suffix in (".olean", ".ilean", ".trace"):
            if suffix in relative:
                module = relative.split(suffix, 1)[0].replace("/", ".")
                if module not in modules and (path.is_file() or path.is_symlink()):
                    path.unlink()
                break


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("plan", "build", "check", "prune-cache", "successful-main-base"))
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--base")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--github-output", type=Path)
    parser.add_argument("--public", action="store_true")
    parser.add_argument("--runs-json", type=Path)
    parser.add_argument("--repository")
    args = parser.parse_args()
    if args.action == "successful-main-base":
        if not args.runs_json or not args.repository:
            parser.error("successful-main-base requires --runs-json and --repository")
        print(successful_main_base(args.repo, args.head,
                                   json.loads(args.runs_json.read_text()), args.repository))
        return
    if not args.base:
        parser.error("this action requires --base")
    selection = plan(args.repo, args.base, args.head)
    if args.github_output:
        with args.github_output.open("a") as out:
            out.write("mode=" + selection["mode"] + "\n")
            out.write("build_lean=" + str(selection["mode"] == "integration" or bool(selection["targets"])).lower() + "\n")
    if args.action == "build":
        if selection["mode"] != "papers":
            raise ValueError("Scoped build requires a papers plan")
        if selection["targets"]:
            require_clean_head(args.repo, selection["head"])
            subprocess.run(["lake", "build", *selection["targets"]], cwd=args.repo, check=True)
            require_clean_head(args.repo, selection["head"])
    elif args.action == "check":
        run_checks(args.repo, selection, public=args.public)
    elif args.action == "prune-cache":
        prune_build_cache(args.repo, selection["head"])
    print(json.dumps(selection, indent=2))


if __name__ == "__main__":
    main()
