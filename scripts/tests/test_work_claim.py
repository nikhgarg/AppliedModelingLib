"""Exercise checkpoint ownership against real Git repositories."""

import argparse
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from scripts import work_claim


class WorkClaimCheckpointTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.git("init", "-q")
        self.git("config", "user.name", "Checkpoint Test")
        self.git("config", "user.email", "checkpoint@example.invalid")
        self.write("owned/keep.txt", "before\n")
        self.write("owned/delete.txt", "retained initially\n")
        self.write("unrelated.txt", "before\n")
        self.git("add", ".")
        self.git("commit", "-qm", "Initial files")
        for name, value in (
            ("REPO_ROOT", self.root),
            ("LEASE_DIR", self.root / "coordination/active-work"),
        ):
            replacement = patch.object(work_claim, name, value)
            replacement.start()
            self.addCleanup(replacement.stop)
        work_claim.write_lease(work_claim.lease_path("test"), {
            "agent": "test", "branch": "main", "worktree": str(self.root),
            "created_utc": "2026-09-05T00:00:00Z", "summary": "Scoped checkpoint",
            "scopes": ["owned", "retired/already-removed.txt"],
        })
        self.git("add", "coordination")
        self.git("commit", "-qm", "Record lease")
        self.args = argparse.Namespace(agent="test", message="Checkpoint owned files", dry_run=False)

    def git(self, *args):
        return subprocess.run(
            ["git", "-C", str(self.root), *args], check=True, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        ).stdout.strip()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def test_retired_scope_does_not_block_owned_edits_additions_or_deletions(self):
        self.write("owned/keep.txt", "after\n")
        self.write("owned/new.txt", "new\n")
        (self.root / "owned/delete.txt").unlink()
        self.write("unrelated.txt", "outside lease\n")
        self.write("unrelated-new.txt", "outside lease\n")
        self.assertEqual(work_claim.command_checkpoint(self.args), 0)
        self.assertEqual(set(self.git("diff-tree", "--no-commit-id", "--name-only", "-r", "HEAD").splitlines()), {
            "owned/keep.txt", "owned/new.txt", "owned/delete.txt",
        })
        self.assertEqual(self.git("show", "HEAD:unrelated.txt"), "before")
        self.assertIn("unrelated-new.txt", self.git("ls-files", "--others", "--exclude-standard"))
        self.assertEqual(self.git("diff", "--cached", "--name-only"), "")

    def test_missing_scope_with_no_changes_is_a_noop(self):
        previous = self.git("rev-parse", "HEAD")
        self.assertEqual(work_claim.command_checkpoint(self.args), 0)
        self.assertEqual(self.git("rev-parse", "HEAD"), previous)

    def test_owned_already_staged_change_is_committed(self):
        self.write("owned/keep.txt", "staged\n")
        self.git("add", "owned/keep.txt")
        self.assertEqual(work_claim.command_checkpoint(self.args), 0)
        self.assertEqual(self.git("show", "HEAD:owned/keep.txt"), "staged")

    def test_foreign_staged_change_is_rejected_before_owned_staging(self):
        self.write("unrelated.txt", "staged outside lease\n")
        self.git("add", "unrelated.txt")
        self.write("owned/keep.txt", "unstaged owned edit\n")
        previous = self.git("rev-parse", "HEAD")
        with self.assertRaisesRegex(work_claim.WorkflowError, "outside this lease"):
            work_claim.command_checkpoint(self.args)
        self.assertEqual(self.git("rev-parse", "HEAD"), previous)
        self.assertEqual(self.git("diff", "--cached", "--name-only"), "unrelated.txt")


if __name__ == "__main__":
    unittest.main()
