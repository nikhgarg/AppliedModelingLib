---
name: econcs-shared-worktree
description: Coordinate shared work in EconCSLib-private without lost changes, routine stashes, or stranded branches. Use for every private-repository branch, worktree, stash, checkpoint commit, pull, merge, push, recovery, or concurrent-agent handoff.
---

# EconCS Shared Worktree

Keep `main` usable by making ownership, checkpoints, and integration explicit.
This skill governs shared-worktree operations; it does not replace the
paper-specific formalization workflow.

## Start With A Lease And A Status Check

Before editing, run:

```bash
python3 scripts/shared_worktree_status.py
python3 scripts/work_claim.py claim \
  --agent <stable-agent-name> \
  --scope papers/<PaperName> \
  --summary "<one-sentence task>"
```

Use exact repository-relative path prefixes.  The command records the lease in
`coordination/active-work/<agent>.toml` and rejects overlap with another active
lease.  Claim every shared-library path that the task is expected to edit too.
Do not edit an overlapping path unless its owner releases the lease or the user
explicitly reassigns it.

## Normal Shared-Main Workflow

1. Work on `main` by default.  A task-local change belongs in the shared
   worktree when its lease is disjoint from all others.
2. Do not use `git stash` to change tasks, pull, rebase, or make room for
   another agent.  Leave an existing stash untouched unless the user explicitly
   requests a classified recovery or deletion.
3. At a meaningful validated seam, make a scoped checkpoint with the lease:

   ```bash
   python3 scripts/work_claim.py checkpoint \
     --agent <stable-agent-name> \
     --message "Checkpoint <paper or library seam>"
   ```

   The checkpoint refuses staged paths outside the agent's lease and stages
   only the claimed prefixes.  It never pushes.
4. Before a handoff, paper switch, or user status report, rerun
   `shared_worktree_status.py`; state the checkpoint commit, active lease, and
   any remaining external blocker.
5. Release a lease only after its work is committed or intentionally handed
   off.  Release is itself an exact one-file checkpoint, so it cannot leave an
   unstaged deletion or hide uncommitted claimed work:

   ```bash
   python3 scripts/work_claim.py release \
     --agent <stable-agent-name> \
     --message "Release <paper or library> lease"
   ```

Never use `git add -A` for ordinary shared work.  The only exception is an
explicit user-directed preservation checkpoint of the entire worktree.

## Durable Worktree And Preservation Gate

Substantive proof or library work must live in a persistent repository
worktree, normally under the repository parent, with a named local branch or
other durable Git ref.  Do not conduct a long proof campaign in `/tmp`, an
executor-owned scratch directory, or another location that background cleanup
may remove.  Temporary Lean files are suitable only for disposable experiments;
as soon as an experiment contains nontrivial proof work worth retaining,
integrate it into the claimed persistent path.

At each meaningful compiled seam, and before a model handoff, context reset,
long pause, or worktree cleanup, make a scoped checkpoint commit.  Prefer one
substantial mathematical seam over a stream of tiny commits, but never leave
the only copy of a reconstructed proof in an uncommitted temporary tree.  An
`.olean`, terminal transcript, or agent/session log is not a substitute for the
Lean source and must not be the sole recovery path.

Before removing or pruning any worktree, verify all of the following:

- `git status --short` is empty, or every remaining path has been explicitly
  classified as disposable;
- every retained commit is reachable from a named durable branch, tag, or
  archive ref in the persistent repository;
- the last retained source seam compiles from that persistent worktree; and
- any authorized push has been verified by comparing the exact remote ref with
  the local commit.

If any check fails, preserve the source first and do not remove the worktree.

## Branches And Integration

Create a branch only when the user requests one or an isolated integration is
necessary to merge a clean checkpoint with `origin/main`.  Before creating it,
record its purpose, base commit, lease owner, and removal condition in the
lease summary.  Do not use a branch merely to avoid seeing shared changes.

Never pull or merge into a dirty shared `main`.  First make a scoped checkpoint.
If `main` cannot be updated without touching another agent's dirty paths,
fetch and merge in a disposable integration worktree, validate the merge, push
only when authorized, then remove the disposable worktree and branch after the
remote ref is verified.

Before merging any non-`main` branch, inspect:

```bash
python3 scripts/shared_worktree_status.py
git log --oneline main..<branch>
git diff --name-status main...<branch>
```

Do not blindly merge a checkpoint branch, an archive branch, or a branch that
contains a different agent's active scope.

## Strict Handoff Gate

Use the strict mode before declaring shared work clean or complete:

```bash
python3 scripts/shared_worktree_status.py --strict
```

It reports dirty worktrees, active leases, stashes, and branches not merged
into `main`.  Resolve or explicitly report every item; never hide it by
stashing, resetting, or deleting a worktree.

## Recovery Boundary

For a pre-existing stash, preserve it first, inspect its tracked and untracked
parents, hash-classify every path, and restore only named nonconflicting files.
Do not use `git stash apply` or `git stash pop` wholesale.  See the private
repository operations skill for the exact recovery protocol.
