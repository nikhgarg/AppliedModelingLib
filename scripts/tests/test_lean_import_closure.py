#!/usr/bin/env python3
"""Regression tests for index/worktree Lean dependency closure."""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import lean_import_closure as closure  # noqa: E402


class LeanImportClosureTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.com")
        self.git("config", "user.name", "Fixture")
        paper = self.repo / "papers" / "Fixture"
        paper.mkdir(parents=True)
        (paper / "Base.lean").write_text("def base : Nat := 1\n", encoding="utf-8")
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Base\n\ntheorem visible : True := by trivial\n",
            encoding="utf-8",
        )
        (self.repo / "lean-toolchain").write_text(
            (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
            encoding="utf-8",
        )
        (self.repo / "lakefile.toml").write_text(
            'name = "Fixture"\n\n[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n'
        )
        (self.repo / "lake-manifest.json").write_text(
            '{"version":"1.2.0","packagesDir":".lake/packages",'
            '"packages":[],"name":"Fixture","lakeDir":".lake"}\n',
            encoding="utf-8",
        )
        helper = self.repo / closure.LEAN_IMPORT_GRAPH_HELPER
        helper.parent.mkdir(parents=True)
        shutil.copyfile(ROOT / closure.LEAN_IMPORT_GRAPH_HELPER, helper)
        self.loaded_modules = ("Fixture.Base", "Fixture.PaperInterface", "Init")
        self.git("add", ".")
        self.git("commit", "-qm", "baseline")

    def git(self, *args: str) -> None:
        subprocess.run(["git", *args], cwd=self.repo, check=True)

    def graph_loader(
        self, _root: Path, _entry_module: str, _timeout_seconds: int
    ) -> tuple[tuple[str, ...], str]:
        return tuple(sorted(self.loaded_modules)), ""

    def provider(self) -> closure.WorktreeImportClosureProvider:
        return closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=self.graph_loader,
        )

    def worktree_identity(self) -> str:
        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        self.assertIsNotNone(digest)
        return str(digest)

    def test_portable_receipt_round_trip_is_exact_and_non_accepting(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        assert record is not None

        payload = closure.lean_import_closure_receipt_payload("Fixture", record)
        self.assertFalse(payload["acceptance_credential"])
        self.assertEqual(
            closure.validated_lean_import_closure_receipt_payload(
                payload, paper="Fixture"
            ),
            payload,
        )

        mutated = dict(payload)
        mutated["paper"] = "Other"
        with self.assertRaisesRegex(ValueError, "identity is invalid"):
            closure.validated_lean_import_closure_receipt_payload(
                mutated, paper="Fixture"
            )

    def test_portable_receipt_accepts_complete_proof_interface_root(self) -> None:
        proof = self.repo / "papers" / "Fixture" / "ProofInterface.lean"
        proof.write_text("import Fixture.PaperInterface\n", encoding="utf-8")
        self.git("add", "papers/Fixture/ProofInterface.lean")
        self.git("commit", "-qm", "add proof interface")
        self.loaded_modules = (
            "Fixture.Base",
            "Fixture.PaperInterface",
            "Fixture.ProofInterface",
            "Init",
        )
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/ProofInterface.lean"
        )
        self.assertIsNone(problem)
        assert record is not None

        payload = closure.lean_import_closure_receipt_payload("Fixture", record)
        self.assertEqual(
            payload["entrypoint"], "papers/Fixture/ProofInterface.lean"
        )
        self.assertEqual(
            closure.validated_lean_import_closure_receipt_payload(
                payload, paper="Fixture"
            ),
            payload,
        )

    def test_portable_receipt_accepts_exact_paper_build_target_root(self) -> None:
        paper_target = self.repo / "papers" / "Fixture.lean"
        paper_target.write_text("import Fixture.PaperInterface\n", encoding="utf-8")
        self.git("add", "papers/Fixture.lean")
        self.git("commit", "-qm", "add paper build target")
        self.loaded_modules = (
            "Fixture",
            "Fixture.Base",
            "Fixture.PaperInterface",
            "Init",
        )
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture.lean"
        )
        self.assertIsNone(problem)
        assert record is not None

        payload = closure.lean_import_closure_receipt_payload("Fixture", record)
        self.assertEqual(payload["entrypoint"], "papers/Fixture.lean")
        self.assertEqual(
            closure.validated_lean_import_closure_receipt_payload(
                payload, paper="Fixture"
            ),
            payload,
        )

        with self.assertRaisesRegex(ValueError, "entrypoint is for another paper"):
            closure.lean_import_closure_receipt_payload("Other", record)

    def test_external_artifact_lookup_avoids_lake_env_and_streams_exact_bytes(
        self,
    ) -> None:
        manifest = {
            "packages": [{"name": "Dependency"}],
        }
        (self.repo / "lake-manifest.json").write_text(json.dumps(manifest))
        artifact = (
            self.repo
            / ".lake"
            / "packages"
            / "Dependency"
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Example"
            / "Module.olean"
        )
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"portable artifact bytes")
        prefix = self.repo / "toolchain"
        (prefix / "lib" / "lean").mkdir(parents=True)
        process = subprocess.CompletedProcess(
            ["lean", "--print-prefix"],
            0,
            stdout=(str(prefix) + "\n").encode(),
            stderr=b"",
        )
        with mock.patch.object(closure.subprocess, "run", return_value=process) as run:
            records, problem = closure.external_module_artifact_records(
                self.repo, ["Example.Module"]
            )
        self.assertEqual(problem, "")
        self.assertEqual(
            records,
            [
                {
                    "module": "Example.Module",
                    "byte_length": len(b"portable artifact bytes"),
                    "sha256": hashlib.sha256(b"portable artifact bytes").hexdigest(),
                }
            ],
        )
        self.assertEqual(run.call_args.args[0], ["lean", "--print-prefix"])

    def test_external_artifact_lookup_rejects_conflicting_candidates(self) -> None:
        (self.repo / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "Dependency"}]})
        )
        roots = (
            self.repo
            / ".lake"
            / "packages"
            / "Dependency"
            / ".lake"
            / "build"
            / "lib"
            / "lean",
            self.repo / ".lake" / "build" / "lib" / "lean",
        )
        for index, root in enumerate(roots):
            artifact = root / "Example" / "Module.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(f"candidate {index}".encode())
        prefix = self.repo / "toolchain"
        (prefix / "lib" / "lean").mkdir(parents=True)
        process = subprocess.CompletedProcess(
            ["lean", "--print-prefix"],
            0,
            stdout=(str(prefix) + "\n").encode(),
            stderr=b"",
        )
        with mock.patch.object(closure.subprocess, "run", return_value=process):
            records, problem = closure.external_module_artifact_records(
                self.repo, ["Example.Module"]
            )
        self.assertIsNone(records)
        self.assertIn("conflicting .olean artifacts", problem)

    def test_external_artifact_snapshot_rejects_timestamp_restored_mutation(
        self,
    ) -> None:
        (self.repo / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "Dependency"}]})
        )
        artifact = (
            self.repo
            / ".lake"
            / "packages"
            / "Dependency"
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Example"
            / "Module.olean"
        )
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"portable artifact bytes")
        original_stat = artifact.stat()
        prefix = self.repo / "toolchain"
        (prefix / "lib" / "lean").mkdir(parents=True)
        process = subprocess.CompletedProcess(
            ["lean", "--print-prefix"],
            0,
            stdout=(str(prefix) + "\n").encode(),
            stderr=b"",
        )
        with mock.patch.object(closure.subprocess, "run", return_value=process):
            snapshot, problem = closure.external_module_artifact_snapshot(
                self.repo, ["Example.Module"]
            )
        self.assertEqual(problem, "")
        assert snapshot is not None

        artifact.write_bytes(b"x" * len(b"portable artifact bytes"))
        os.utime(
            artifact,
            ns=(original_stat.st_atime_ns, original_stat.st_mtime_ns),
        )

        self.assertIn("changed after exact hashing", snapshot.current_problem())

    def test_external_artifact_finalization_rejects_a_new_candidate(self) -> None:
        (self.repo / "lake-manifest.json").write_text(
            json.dumps({"packages": [{"name": "Dependency"}]})
        )
        package_artifact = (
            self.repo
            / ".lake"
            / "packages"
            / "Dependency"
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Example"
            / "Module.olean"
        )
        package_artifact.parent.mkdir(parents=True)
        package_artifact.write_bytes(b"same artifact bytes")
        prefix = self.repo / "toolchain"
        (prefix / "lib" / "lean").mkdir(parents=True)
        process = subprocess.CompletedProcess(
            ["lean", "--print-prefix"],
            0,
            stdout=(str(prefix) + "\n").encode(),
            stderr=b"",
        )
        with mock.patch.object(closure.subprocess, "run", return_value=process):
            snapshot, problem = closure.external_module_artifact_snapshot(
                self.repo, ["Example.Module"]
            )
            self.assertEqual(problem, "")
            assert snapshot is not None
            unchanged_search, problem = closure.external_artifact_search_snapshot(
                self.repo
            )
            self.assertEqual(problem, "")
            assert unchanged_search is not None
            self.assertEqual(
                snapshot.current_problem(search_snapshot=unchanged_search), ""
            )

            duplicate = (
                self.repo
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "Example"
                / "Module.olean"
            )
            duplicate.parent.mkdir(parents=True)
            duplicate.write_bytes(b"same artifact bytes")
            changed_search, problem = closure.external_artifact_search_snapshot(
                self.repo
            )

        self.assertEqual(problem, "")
        assert changed_search is not None
        self.assertIn(
            "candidate set changed",
            snapshot.current_problem(search_snapshot=changed_search),
        )

    def test_non_git_root_returns_structured_fail_closed_problem(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            entrypoint = root / "papers" / "Fixture" / "PaperInterface.lean"
            entrypoint.parent.mkdir(parents=True)
            entrypoint.write_text("theorem visible : True := by trivial\n")
            graph_loader = mock.Mock(return_value=(("Fixture.PaperInterface",), ""))

            provider = closure.WorktreeImportClosureProvider(
                root,
                module_graph_loader=graph_loader,
                allow_dirty_worktree_sources=True,
            )
            record, problem = provider.record_for_entrypoint(
                "papers/Fixture/PaperInterface.lean"
            )

            self.assertIsNone(record)
            self.assertIsNotNone(problem)
            assert problem is not None
            self.assertEqual(problem.code, "git_inventory_unavailable")
            self.assertIn("Git candidate path inventory cannot be read", problem.reason)
            graph_loader.assert_not_called()
            self.assertEqual(provider.finalization_problems(), ())

    def test_worktree_rejects_import_resolving_only_to_untracked_module(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "Loose.lean").write_text("def loose : Nat := 2\n", encoding="utf-8")
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Base\nimport Fixture.Loose\n",
            encoding="utf-8",
        )

        issues = closure.dependency_closure_issues(self.repo, candidate="worktree")

        self.assertTrue(
            any("untracked Lean module" in issue.reason for issue in issues), issues
        )

    def test_index_rejects_staged_import_when_dependency_is_untracked(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "Loose.lean").write_text("def loose : Nat := 2\n", encoding="utf-8")
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Base\nimport Fixture.Loose\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")

        issues = closure.dependency_closure_issues(self.repo, candidate="index")

        self.assertTrue(
            any("untracked Lean module" in issue.reason for issue in issues), issues
        )

    def test_index_accepts_dependency_staged_with_entrypoint(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "Loose.lean").write_text("def loose : Nat := 2\n", encoding="utf-8")
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Base\nimport Fixture.Loose\n",
            encoding="utf-8",
        )
        self.git(
            "add", "papers/Fixture/PaperInterface.lean", "papers/Fixture/Loose.lean"
        )

        self.assertEqual(
            closure.dependency_closure_issues(self.repo, candidate="index"), []
        )

    def test_index_rejects_unstaged_change_in_imported_dependency(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Base\n\n-- staged interface edit\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")
        (paper / "Base.lean").write_text("def base : Nat := 99\n", encoding="utf-8")

        issues = closure.dependency_closure_issues(self.repo, candidate="index")

        self.assertTrue(
            any("unstaged changes" in issue.reason for issue in issues), issues
        )

    def test_missing_repository_owned_import_fails_closed(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.DoesNotExist\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")

        issues = closure.dependency_closure_issues(self.repo, candidate="index")

        self.assertTrue(
            any("repository-owned import" in issue.reason for issue in issues), issues
        )

    def test_unregistered_external_prefix_fails_closed(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "PaperInterface.lean").write_text(
            "import UnknownPackage.Module\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")

        issues = closure.dependency_closure_issues(self.repo, candidate="index")

        self.assertTrue(
            any(
                "explicit external-module registry" in issue.reason for issue in issues
            ),
            issues,
        )

    def test_import_text_inside_comment_is_ignored(self) -> None:
        source = (
            "/-! Example text.\nimport Fixture.NotARealImport\n-/\nimport Mathlib\n"
        )
        self.assertEqual(closure.imported_modules(source), ["Mathlib"])

    def test_committed_tree_closure_does_not_read_index(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.DoesNotExist\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")

        self.assertEqual(
            closure.dependency_closure_issues(
                self.repo, candidate="tree", treeish="HEAD"
            ),
            [],
        )

    def test_tree_extra_entrypoint_checks_changed_noninterface_module(self) -> None:
        detached = self.repo / "papers" / "Fixture" / "DetachedAudit.lean"
        detached.write_text(
            "import Fixture.DoesNotExist\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/DetachedAudit.lean")
        self.git("commit", "-qm", "changed detached Lean module")

        issues = closure.dependency_closure_issues(
            self.repo,
            candidate="tree",
            treeish="HEAD",
            extra_entrypoints=["papers/Fixture/DetachedAudit.lean"],
        )

        self.assertTrue(
            any(
                issue.entrypoint == "papers/Fixture/DetachedAudit.lean"
                and "repository-owned import" in issue.reason
                for issue in issues
            ),
            issues,
        )

    def test_worktree_identity_is_memoized_from_one_snapshot(self) -> None:
        provider = self.provider()
        first = provider.identity_for_entrypoint("papers/Fixture/PaperInterface.lean")
        (self.repo / "papers" / "Fixture" / "Base.lean").write_text(
            "def base : Nat := 2\n", encoding="utf-8"
        )

        second = provider.identity_for_entrypoint("papers/Fixture/PaperInterface.lean")

        self.assertEqual(first, second)

    def test_unimported_lean_change_does_not_change_worktree_identity(self) -> None:
        detached = self.repo / "papers" / "Fixture" / "Detached.lean"
        detached.write_text("def detached : Nat := 1\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Detached.lean")
        self.git("commit", "-qm", "add detached source")
        before = self.worktree_identity()

        detached.write_text("def detached : Nat := 999\n", encoding="utf-8")

        self.assertEqual(self.worktree_identity(), before)

    def test_staged_imported_body_change_changes_worktree_identity(self) -> None:
        before = self.worktree_identity()
        base = self.repo / "papers" / "Fixture" / "Base.lean"
        base.write_text("def base : Nat := 2\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Base.lean")

        self.assertNotEqual(self.worktree_identity(), before)

    def test_unstaged_imported_body_change_fails_closed(self) -> None:
        base = self.repo / "papers" / "Fixture" / "Base.lean"
        base.write_text("def base : Nat := 2\n", encoding="utf-8")

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "unstaged_imported_module")
        with self.assertRaises(closure.ImportClosureIdentityError) as caught:
            self.provider().require_identity_for_entrypoint(
                "papers/Fixture/PaperInterface.lean"
            )
        self.assertEqual(caught.exception.problem.code, problem.code)

    def test_entrypoint_body_change_changes_worktree_identity(self) -> None:
        before = self.worktree_identity()
        interface = self.repo / "papers" / "Fixture" / "PaperInterface.lean"
        interface.write_text(
            "import Fixture.Base\n\ntheorem visible : True := by exact True.intro\n",
            encoding="utf-8",
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")

        self.assertNotEqual(self.worktree_identity(), before)

    def test_unstaged_entrypoint_change_fails_closed(self) -> None:
        interface = self.repo / "papers" / "Fixture" / "PaperInterface.lean"
        interface.write_text(
            "import Fixture.Base\n\ntheorem visible : False := by sorry\n",
            encoding="utf-8",
        )

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "unstaged_entrypoint")

    def test_toolchain_or_lake_control_change_changes_worktree_identity(self) -> None:
        (self.repo / "lean-toolchain").write_text(
            "leanprover/lean4:v4.20.0\n", encoding="utf-8"
        )

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "control_file_unstaged")

    def test_absent_lakefile_variant_status_is_bound_into_identity(self) -> None:
        (self.repo / "lakefile.lean").write_text("import Lake\n", encoding="utf-8")

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "lake_routing_unavailable")

    def test_staged_control_identity_is_stable_after_commit(self) -> None:
        before = self.worktree_identity()
        path = self.repo / "lean-toolchain"
        path.write_text(
            path.read_text(encoding="utf-8") + "\n-- fixture control change\n",
            encoding="utf-8",
        )
        self.git("add", "lean-toolchain")
        staged = self.worktree_identity()
        self.git("commit", "-qm", "update toolchain")

        self.assertNotEqual(staged, before)
        self.assertEqual(self.worktree_identity(), staged)

    def test_untracked_import_returns_structured_problem(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "Loose.lean").write_text("def loose : Nat := 2\n", encoding="utf-8")
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Loose\n", encoding="utf-8"
        )
        self.git("add", "papers/Fixture/PaperInterface.lean")
        self.loaded_modules += ("Fixture.Loose",)

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "untracked_repository_import")
        self.assertEqual(problem.imported_module, "Fixture.Loose")

    def test_ambiguous_repository_import_returns_structured_problem(self) -> None:
        duplicate = self.repo / "Fixture" / "Base.lean"
        duplicate.parent.mkdir()
        duplicate.write_text("def duplicate : Nat := 3\n", encoding="utf-8")
        self.git("add", "Fixture/Base.lean")

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "ambiguous_repository_import")

    def test_external_import_association_changes_worktree_identity(self) -> None:
        interface = self.repo / "papers" / "Fixture" / "PaperInterface.lean"
        interface.write_text("import Lean\n", encoding="utf-8")
        self.git("add", "papers/Fixture/PaperInterface.lean")
        self.loaded_modules = ("Fixture.PaperInterface", "Init", "Lean")
        lean_identity = self.worktree_identity()
        interface.write_text("import Std\n", encoding="utf-8")
        self.git("add", "papers/Fixture/PaperInterface.lean")
        self.loaded_modules = ("Fixture.PaperInterface", "Init", "Std")

        self.assertNotEqual(self.worktree_identity(), lean_identity)

    def test_transitive_repository_source_is_bound_into_identity(self) -> None:
        paper = self.repo / "papers" / "Fixture"
        (paper / "Middle.lean").write_text(
            "import Fixture.Base\n\ndef middle : Nat := base\n", encoding="utf-8"
        )
        (paper / "PaperInterface.lean").write_text(
            "import Fixture.Middle\n", encoding="utf-8"
        )
        self.git(
            "add", "papers/Fixture/Middle.lean", "papers/Fixture/PaperInterface.lean"
        )
        self.git("commit", "-qm", "add transitive source")
        self.loaded_modules += ("Fixture.Middle",)
        before = self.worktree_identity()
        (paper / "Base.lean").write_text("def base : Nat := 8\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Base.lean")

        self.assertNotEqual(self.worktree_identity(), before)

    def test_unresolved_repository_import_returns_structured_problem(self) -> None:
        interface = self.repo / "papers" / "Fixture" / "PaperInterface.lean"
        interface.write_text("import Fixture.Missing\n", encoding="utf-8")
        self.git("add", "papers/Fixture/PaperInterface.lean")
        self.loaded_modules += ("Fixture.Missing",)

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertIsNotNone(problem)
        assert problem is not None
        self.assertEqual(problem.code, "unresolved_repository_import")

    def test_external_module_without_resolvable_artifact_fails_closed(self) -> None:
        interface = self.repo / "papers" / "Fixture" / "PaperInterface.lean"
        interface.write_text("import Unregistered.Widget\n", encoding="utf-8")
        self.git("add", "papers/Fixture/PaperInterface.lean")
        self.loaded_modules = (
            "Fixture.PaperInterface",
            "Init",
            "Unregistered.Widget",
        )

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertEqual(problem.code, "external_module_artifact_unavailable")

    def test_saved_closure_rehashes_exact_external_artifact_bytes(self) -> None:
        artifact = (
            self.repo
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Unregistered"
            / "Widget.olean"
        )
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(b"fixture external olean v1")
        self.loaded_modules = (
            "Fixture.Base",
            "Fixture.PaperInterface",
            "Init",
            "Unregistered.Widget",
        )
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        artifact.write_bytes(b"fixture external olean v2")

        digest, current_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )

        self.assertIsNone(digest)
        self.assertEqual(current_problem.code, "saved_external_module_artifact_changed")

    def test_live_graph_rejects_concurrent_imported_source_mutation(self) -> None:
        base = self.repo / "papers" / "Fixture" / "Base.lean"

        def mutating_loader(_root: Path, _entry_module: str, _timeout: int):
            base.write_text("def base : Nat := 99\n", encoding="utf-8")
            return tuple(sorted(self.loaded_modules)), ""

        provider = closure.WorktreeImportClosureProvider(
            self.repo, module_graph_loader=mutating_loader
        )
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertEqual(problem.code, "worktree_changed_during_lean_graph")

    def test_live_graph_ignores_concurrent_unrelated_repository_activity(self) -> None:
        def unrelated_loader(_root: Path, _entry_module: str, _timeout: int):
            unrelated = self.repo / "Other" / "Different.lean"
            unrelated.parent.mkdir()
            unrelated.write_text("def different : Nat := 1\n", encoding="utf-8")
            self.git("add", "Other/Different.lean")
            (self.repo / "scratch-note.txt").write_text("new\n", encoding="utf-8")
            return tuple(sorted(self.loaded_modules)), ""

        provider = closure.WorktreeImportClosureProvider(
            self.repo, module_graph_loader=unrelated_loader
        )

        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(problem)
        self.assertIsNotNone(digest)
        self.assertEqual(provider.finalization_problems(), ())

    def test_live_graph_rejects_concurrent_loaded_module_ambiguity(self) -> None:
        def ambiguous_loader(_root: Path, _entry_module: str, _timeout: int):
            duplicate = self.repo / "Fixture" / "Base.lean"
            duplicate.parent.mkdir()
            duplicate.write_text("def duplicate : Nat := 3\n", encoding="utf-8")
            self.git("add", "Fixture/Base.lean")
            return tuple(sorted(self.loaded_modules)), ""

        provider = closure.WorktreeImportClosureProvider(
            self.repo, module_graph_loader=ambiguous_loader
        )

        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertEqual(problem.code, "worktree_changed_during_lean_graph")

    def test_saved_closure_rehash_never_calls_live_graph_loader(self) -> None:
        baseline_provider = self.provider()
        record, problem = baseline_provider.record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)

        def forbidden_loader(_root: Path, _module: str, _timeout: int):
            raise AssertionError("cheap receipt reuse must not invoke Lean")

        current = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=forbidden_loader,
        )
        digest, problem = current.identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )

        self.assertIsNone(problem)
        self.assertEqual(
            digest,
            closure.lean_import_closure_payload_sha256(record),
        )

    def test_saved_closure_provider_finalizes_clean_reuse(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        provider = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=lambda *_args: (_ for _ in ()).throw(
                AssertionError("saved closure finalization invoked Lean")
            ),
            eager_source_snapshot=False,
        )
        digest, current_problem = provider.identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )

        self.assertIsNone(current_problem)
        self.assertEqual(digest, closure.lean_import_closure_payload_sha256(record))
        with mock.patch.object(
            closure,
            "external_module_artifact_records",
            wraps=closure.external_module_artifact_records,
        ) as external_records:
            self.assertEqual(provider.finalization_problems(), ())
        external_records.assert_called_once()

    def test_saved_closure_finalization_is_not_cached_after_clean_check(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        provider = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=lambda *_args: (_ for _ in ()).throw(
                AssertionError("saved closure finalization invoked Lean")
            ),
            eager_source_snapshot=False,
        )
        digest, current_problem = provider.identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(current_problem)
        self.assertEqual(provider.finalization_problems(), ())
        base = self.repo / "papers" / "Fixture" / "Base.lean"
        base.write_text("def base : Nat := 77\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Base.lean")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_source_changed",
            {problem.code for problem in problems},
        )

    def test_finalization_ignores_unrelated_repository_activity(self) -> None:
        tracked_note = self.repo / "tracked-finalization-input.txt"
        tracked_note.write_text("baseline\n", encoding="utf-8")
        self.git("add", tracked_note.name)
        self.git("commit", "-qm", "add unrelated finalization input")
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)

        staged = self.repo / "Other" / "Different.lean"
        staged.parent.mkdir()
        staged.write_text("def different : Nat := 1\n", encoding="utf-8")
        self.git("add", "Other/Different.lean")
        (self.repo / "Scratch.lean").write_text(
            "def scratch : Nat := 1\n", encoding="utf-8"
        )
        tracked_note.write_text("unrelated edit\n", encoding="utf-8")

        self.assertEqual(provider.finalization_problems(), ())

    def test_finalization_rejects_new_candidate_for_loaded_module(self) -> None:
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        duplicate = self.repo / "Fixture" / "Base.lean"
        duplicate.parent.mkdir()
        duplicate.write_text("def duplicate : Nat := 3\n", encoding="utf-8")
        self.git("add", "Fixture/Base.lean")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_source_association_changed",
            {item.code for item in problems},
        )

    def test_finalization_rejects_repository_candidate_for_external_module(
        self,
    ) -> None:
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        external_shadow = self.repo / "Init.lean"
        external_shadow.write_text("def shadow : Nat := 1\n", encoding="utf-8")
        self.git("add", "Init.lean")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_external_association_changed",
            {item.code for item in problems},
        )

    def test_finalization_checks_build_control_bytes(self) -> None:
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        toolchain = self.repo / "lean-toolchain"
        toolchain.write_text(
            toolchain.read_text(encoding="utf-8") + "\nchanged-after-validation\n",
            encoding="utf-8",
        )
        self.git("add", "lean-toolchain")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_controls_changed",
            {item.code for item in problems},
        )

    def test_graph_helper_refactor_does_not_change_saved_closure_identity(self) -> None:
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        helper = self.repo / closure.LEAN_IMPORT_GRAPH_HELPER
        helper.write_text(
            helper.read_text(encoding="utf-8") + "\n-- operational refactor\n",
            encoding="utf-8",
        )
        self.git("add", closure.LEAN_IMPORT_GRAPH_HELPER)

        self.assertEqual(provider.finalization_problems(), ())

    def test_legacy_graph_helper_control_does_not_reopen_saved_closure(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        assert record is not None
        helper = self.repo / closure.LEAN_IMPORT_GRAPH_HELPER
        helper_content = helper.read_bytes()
        legacy = dict(record)
        legacy["build_controls"] = [
            *record["build_controls"],
            {
                "path": closure.LEAN_IMPORT_GRAPH_HELPER,
                "tracked_in_index": True,
                "untracked": False,
                "path_kind": "file",
                "byte_length": len(helper_content),
                "sha256": hashlib.sha256(helper_content).hexdigest(),
            },
        ]
        legacy_digest = closure.lean_import_closure_payload_sha256(legacy)
        helper.write_text(
            helper.read_text(encoding="utf-8") + "\n-- later operational refactor\n",
            encoding="utf-8",
        )
        self.git("add", closure.LEAN_IMPORT_GRAPH_HELPER)

        digest, current_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", legacy
        )

        self.assertIsNone(current_problem)
        self.assertEqual(digest, legacy_digest)
        self.assertEqual(
            len(closure.validated_lean_import_closure_payload(legacy)["build_controls"]),
            3,
        )

    def test_finalization_checks_entrypoint_lake_routing(self) -> None:
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        lakefile = self.repo / "lakefile.toml"
        lakefile.write_text(
            'name = "Fixture"\nmoreLeanArgs = ["-Dfixture.changed=true"]\n\n'
            '[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n',
            encoding="utf-8",
        )
        self.git("add", "lakefile.toml")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_lake_routing_changed",
            {item.code for item in problems},
        )

    def test_finalization_checks_external_artifact_bytes(self) -> None:
        artifact = (
            self.repo
            / ".lake"
            / "build"
            / "lib"
            / "lean"
            / "Unregistered"
            / "Widget.olean"
        )
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(b"fixture external olean v1")
        self.loaded_modules = (
            "Fixture.Base",
            "Fixture.PaperInterface",
            "Init",
            "Unregistered.Widget",
        )
        provider = self.provider()
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNotNone(digest)
        self.assertIsNone(problem)
        self.assertEqual(provider.finalization_problems(), ())
        artifact.write_bytes(b"fixture external olean v2")

        problems = provider.finalization_problems()

        self.assertIn(
            "closure_finalization_external_artifacts_changed",
            {item.code for item in problems},
        )

    def test_saved_closure_rehash_reads_only_receipt_owned_sources(self) -> None:
        detached = self.repo / "papers" / "Fixture" / "Detached.lean"
        detached.write_text("def detached : Nat := 1\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Detached.lean")
        self.git("commit", "-qm", "add detached source")
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)

        provider = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=lambda *_args: (_ for _ in ()).throw(
                AssertionError("saved closure rehash invoked Lean")
            ),
            eager_source_snapshot=False,
        )
        self.assertEqual(provider._sources, {})
        receipt_paths = {str(item["path"]) for item in record["sources"]}
        reads = {path: 0 for path in receipt_paths}
        original_read_bytes = Path.read_bytes

        def counting_read_bytes(path: Path) -> bytes:
            try:
                relative = path.resolve().relative_to(self.repo).as_posix()
            except ValueError:
                relative = ""
            if relative in reads:
                reads[relative] += 1
            return original_read_bytes(path)

        with mock.patch.object(Path, "read_bytes", new=counting_read_bytes):
            digest, current_problem = provider.identity_from_saved_closure(
                "papers/Fixture/PaperInterface.lean",
                record,
            )
            snapshot = provider.repository_source_bytes_for_closure(record)

        self.assertIsNone(current_problem)
        self.assertEqual(digest, closure.lean_import_closure_payload_sha256(record))
        self.assertEqual(set(snapshot), receipt_paths)
        self.assertEqual(reads, {path: 1 for path in receipt_paths})
        self.assertEqual(
            set(provider._sources),
            {str(item["path"]) for item in record["sources"]},
        )
        self.assertNotIn("papers/Fixture/Detached.lean", provider._sources)

    def test_authoritative_provider_never_uses_python_import_parser(self) -> None:
        with mock.patch.object(
            closure,
            "imported_modules",
            side_effect=AssertionError("Python parser cannot supply credited closure"),
        ):
            digest = self.worktree_identity()

        self.assertRegex(digest, r"^[0-9a-f]{64}$")

    def test_dirty_worktree_mode_authenticates_exact_unstaged_source_bytes(
        self,
    ) -> None:
        paper = self.repo / "papers" / "Fixture"
        base = paper / "Base.lean"
        base.write_text("def base : Nat := 42\n", encoding="utf-8")

        strict_record, strict_problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(strict_record)
        self.assertEqual(strict_problem.code, "unstaged_imported_module")

        provider = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=self.graph_loader,
            eager_source_snapshot=False,
            allow_dirty_worktree_sources=True,
        )
        record, problem = provider.record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(problem)
        self.assertIsNotNone(record)
        assert record is not None
        base_record = next(
            item for item in record["sources"] if item["module"] == "Fixture.Base"
        )
        self.assertEqual(
            base_record["sha256"],
            hashlib.sha256(base.read_bytes()).hexdigest(),
        )
        self.assertEqual(provider.finalization_problems(), ())

        saved_provider = closure.WorktreeImportClosureProvider(
            self.repo,
            module_graph_loader=lambda *_args: (_ for _ in ()).throw(
                AssertionError("saved dirty-worktree closure invoked Lean")
            ),
            eager_source_snapshot=False,
            allow_dirty_worktree_sources=True,
        )
        digest, saved_problem = saved_provider.identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )
        self.assertIsNone(saved_problem)
        self.assertEqual(digest, closure.lean_import_closure_payload_sha256(record))
        self.assertEqual(saved_provider.finalization_problems(), ())

    def test_saved_closure_rehash_rejects_dependency_byte_change(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        base = self.repo / "papers" / "Fixture" / "Base.lean"
        base.write_text("def base : Nat := 42\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Base.lean")

        digest, current_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )

        self.assertIsNone(digest)
        self.assertEqual(current_problem.code, "saved_lean_closure_source_changed")

    def test_saved_closure_rehash_ignores_unimported_scratch_change(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        scratch = self.repo / "papers" / "Fixture" / "Scratch.lean"
        scratch.write_text("def scratch : Nat := 1\n", encoding="utf-8")
        self.git("add", "papers/Fixture/Scratch.lean")
        self.git("commit", "-qm", "add unrelated scratch")
        scratch.write_text("def scratch : Nat := 999\n", encoding="utf-8")

        digest, current_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )

        self.assertIsNone(current_problem)
        self.assertEqual(digest, closure.lean_import_closure_payload_sha256(record))

    def test_unrelated_lake_targets_are_portable_but_entry_routing_is_not(self) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        lakefile = self.repo / "lakefile.toml"
        lakefile.write_text(
            'name = "Fixture"\n'
            'defaultTargets = ["Unrelated"]\n\n'
            '[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n\n'
            '[[lean_lib]]\nname = "Unrelated"\nsrcDir = "unrelated"\n',
            encoding="utf-8",
        )
        self.git("add", "lakefile.toml")
        self.git("commit", "-qm", "change unrelated public targets")

        digest, current_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )
        self.assertIsNone(current_problem)
        self.assertEqual(digest, closure.lean_import_closure_payload_sha256(record))

        lakefile.write_text(
            'name = "Fixture"\n\n'
            '[[lean_lib]]\nname = "Fixture"\nsrcDir = "different"\n',
            encoding="utf-8",
        )
        self.git("add", "lakefile.toml")
        _, routing_problem = self.provider().identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", record
        )
        self.assertEqual(routing_problem.code, "saved_lean_closure_routing_changed")

    def test_package_lean_arguments_change_saved_routing_identity(self) -> None:
        lakefile = self.repo / "lakefile.toml"
        baseline_lakefile = lakefile.read_text(encoding="utf-8")
        for field in ("moreLeanArgs", "weakLeanArgs"):
            with self.subTest(field=field):
                record, problem = self.provider().record_for_entrypoint(
                    "papers/Fixture/PaperInterface.lean"
                )
                self.assertIsNone(problem)
                lakefile.write_text(
                    f'name = "Fixture"\n{field} = ["-Dfixture.changed=true"]\n\n'
                    '[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n',
                    encoding="utf-8",
                )
                self.git("add", "lakefile.toml")

                digest, routing_problem = self.provider().identity_from_saved_closure(
                    "papers/Fixture/PaperInterface.lean", record
                )

                self.assertIsNone(digest)
                self.assertEqual(
                    routing_problem.code, "saved_lean_closure_routing_changed"
                )
                lakefile.write_text(baseline_lakefile, encoding="utf-8")
                self.git("add", "lakefile.toml")

    def test_administrative_package_metadata_does_not_change_routing_identity(
        self,
    ) -> None:
        record, problem = self.provider().record_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )
        self.assertIsNone(problem)
        assert record is not None
        legacy = dict(record)
        routing = dict(record["lake_routing"])
        package = dict(routing["package_configuration"])
        package.update({"version": "1.0.0", "keywords": ["legacy"]})
        routing["package_configuration"] = package
        legacy["lake_routing"] = routing
        legacy_digest = closure.lean_import_closure_payload_sha256(legacy)
        lakefile = self.repo / "lakefile.toml"
        lakefile.write_text(
            'name = "Fixture"\n'
            'version = "99.0.0"\n'
            'keywords = ["changed", "administrative"]\n'
            'description = "presentation only"\n\n'
            '[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n',
            encoding="utf-8",
        )
        self.git("add", "lakefile.toml")

        provider = self.provider()
        digest, routing_problem = provider.identity_from_saved_closure(
            "papers/Fixture/PaperInterface.lean", legacy
        )

        self.assertIsNone(routing_problem)
        self.assertEqual(digest, legacy_digest)
        self.assertEqual(provider.finalization_problems(), ())

    def test_live_graph_fails_closed_when_entrypoint_is_omitted(self) -> None:
        self.loaded_modules = ("Fixture.Base", "Init")

        digest, problem = self.provider().identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertEqual(problem.code, "lean_module_graph_missing_entrypoint")

    def test_live_graph_failure_is_structured(self) -> None:
        def unavailable(_root: Path, _module: str, _timeout: int):
            return None, "fixture Lean failure"

        provider = closure.WorktreeImportClosureProvider(
            self.repo, module_graph_loader=unavailable
        )
        digest, problem = provider.identity_for_entrypoint(
            "papers/Fixture/PaperInterface.lean"
        )

        self.assertIsNone(digest)
        self.assertEqual(problem.code, "lean_module_graph_unavailable")

    def test_graph_only_loaded_module_closure_skips_lake_build(self) -> None:
        payload = {
            "schema": closure.LEAN_IMPORT_GRAPH_SCHEMA,
            "modules": ["Fixture.Base", "Fixture.PaperInterface", "Init"],
        }
        graph_result = subprocess.CompletedProcess(
            args=[],
            returncode=0,
            stdout=(
                closure.LEAN_IMPORT_GRAPH_MARKER + json.dumps(payload) + "\n"
            ).encode("utf-8"),
            stderr=b"",
        )
        with mock.patch.object(
            closure,
            "run_owned_lean_process",
            return_value=graph_result,
        ) as run:
            modules, error = closure.lean_loaded_module_closure(
                self.repo,
                "Fixture.PaperInterface",
                timeout_seconds=17,
                build_entry_module=False,
            )

        self.assertEqual(error, "")
        self.assertEqual(
            modules,
            ("Fixture.Base", "Fixture.PaperInterface", "Init"),
        )
        run.assert_called_once()
        command = run.call_args.args[0]
        self.assertEqual(command[:3], ["lake", "env", "lean"])
        self.assertNotIn("build", command)
        self.assertEqual(run.call_args.kwargs["cwd"], self.repo)
        self.assertEqual(run.call_args.kwargs["timeout"], 17)

    def test_default_loaded_module_closure_still_builds_entrypoint(self) -> None:
        payload = {
            "schema": closure.LEAN_IMPORT_GRAPH_SCHEMA,
            "modules": ["Fixture.Base", "Fixture.PaperInterface", "Init"],
        }
        build_result = subprocess.CompletedProcess(
            args=[], returncode=0, stdout=b"", stderr=b""
        )
        graph_result = subprocess.CompletedProcess(
            args=[],
            returncode=0,
            stdout=(
                closure.LEAN_IMPORT_GRAPH_MARKER + json.dumps(payload) + "\n"
            ).encode("utf-8"),
            stderr=b"",
        )
        with mock.patch.object(
            closure,
            "run_owned_lean_process",
            side_effect=(build_result, graph_result),
        ) as run:
            modules, error = closure.lean_loaded_module_closure(
                self.repo,
                "Fixture.PaperInterface",
                timeout_seconds=23,
            )

        self.assertEqual(error, "")
        self.assertEqual(
            modules,
            ("Fixture.Base", "Fixture.PaperInterface", "Init"),
        )
        self.assertEqual(run.call_count, 2)
        self.assertEqual(
            run.call_args_list[0].args[0],
            ["lake", "build", "+Fixture.PaperInterface:olean"],
        )
        self.assertEqual(run.call_args_list[0].kwargs["cwd"], self.repo)
        self.assertEqual(run.call_args_list[0].kwargs["timeout"], 23)
        self.assertEqual(run.call_args_list[0].kwargs["env"]["LEAN_NUM_THREADS"], "1")
        self.assertEqual(run.call_args_list[1].args[0][:3], ["lake", "env", "lean"])

    def test_build_environment_caps_threads_without_mutating_parent(self) -> None:
        with mock.patch.dict(closure.os.environ, {
            "LEAN_NUM_THREADS": "24", "BUILD_ENV_TEST_SENTINEL": "preserved",
        }):
            environment = closure.single_threaded_lean_build_environment()
            self.assertEqual(environment["LEAN_NUM_THREADS"], "1")
            self.assertEqual(environment["BUILD_ENV_TEST_SENTINEL"], "preserved")
            self.assertEqual(closure.os.environ["LEAN_NUM_THREADS"], "24")

    def test_native_closure_timeouts_kill_owned_group_and_preserve_cause(self) -> None:
        for build_entry_module in (True, False):
            with self.subTest(build=build_entry_module):
                process = mock.Mock(pid=123456)
                process.communicate.side_effect = [
                    subprocess.TimeoutExpired("native fixture", 600), (b"last output", b""),
                ]
                with (
                    mock.patch.object(closure.subprocess, "Popen", return_value=process) as popen,
                    mock.patch.object(closure.os, "killpg") as killpg,
                ):
                    modules, error = closure.lean_loaded_module_closure(
                        self.repo, "Fixture.PaperInterface", 600,
                        build_entry_module=build_entry_module,
                    )
                self.assertIsNone(modules)
                self.assertIn("timed out after 600 seconds", error)
                self.assertIn("Lake could not build" if build_entry_module else "Lean import-graph command failed", error)
                self.assertIs(popen.call_args.kwargs["start_new_session"], True)
                self.assertEqual(popen.call_args.kwargs["cwd"], self.repo)
                killpg.assert_called_once_with(process.pid, closure.signal.SIGKILL)
                self.assertEqual(process.communicate.call_args_list, [
                    mock.call(timeout=600), mock.call(timeout=1),
                ])

    def test_owned_native_process_cancellation_cleans_and_reraises(self) -> None:
        for interruption in (KeyboardInterrupt(), SystemExit(3)):
            with self.subTest(interruption=type(interruption).__name__):
                process = mock.Mock(pid=123456)
                process.communicate.side_effect = [interruption, (b"", b"")]
                with (
                    mock.patch.object(closure.subprocess, "Popen", return_value=process),
                    mock.patch.object(closure.os, "killpg") as killpg,
                    self.assertRaises(type(interruption)) as raised,
                ):
                    closure.run_owned_lean_process(["lake", "build"], cwd=self.repo, timeout=17)
                self.assertIs(raised.exception, interruption)
                killpg.assert_called_once_with(process.pid, closure.signal.SIGKILL)
                self.assertEqual(process.communicate.call_args_list, [
                    mock.call(timeout=17), mock.call(timeout=1),
                ])

    def test_owned_native_process_cleanup_error_preserves_original_failure(self) -> None:
        original = subprocess.TimeoutExpired("native fixture", 17)
        process = mock.Mock(pid=123456)
        process.communicate.side_effect = [original, OSError("drain failed")]
        process.kill.side_effect = ProcessLookupError()
        with (
            mock.patch.object(closure.subprocess, "Popen", return_value=process),
            mock.patch.object(closure.os, "killpg", side_effect=PermissionError()),
            self.assertRaises(subprocess.TimeoutExpired) as raised,
        ):
            closure.run_owned_lean_process(["lake", "build"], cwd=self.repo, timeout=17)
        self.assertIs(raised.exception, original)
        process.kill.assert_called_once_with()
        self.assertEqual(process.communicate.call_args_list, [
            mock.call(timeout=17), mock.call(timeout=1),
        ])

    def test_owned_native_process_preserves_output_and_nonzero_status(self) -> None:
        process = mock.Mock(returncode=7)
        process.communicate.return_value = (b"stdout", b"stderr")
        with (
            mock.patch.object(closure.subprocess, "Popen", return_value=process) as popen,
            mock.patch.object(closure.os, "killpg") as killpg,
        ):
            result = closure.run_owned_lean_process(
                ["lake", "build", "+Fixture.PaperInterface:olean"], cwd=self.repo,
                timeout=17, env={"LEAN_NUM_THREADS": "1"},
            )
        self.assertEqual((result.returncode, result.stdout, result.stderr), (7, b"stdout", b"stderr"))
        self.assertEqual(popen.call_args.kwargs["env"], {"LEAN_NUM_THREADS": "1"})
        killpg.assert_not_called()

    def test_real_lean_graph_observes_dependency_only_import_change(self) -> None:
        baseline, error = closure.lean_loaded_module_closure(
            self.repo, "Fixture.PaperInterface", timeout_seconds=120
        )
        self.assertEqual(error, "")
        self.assertIn("Fixture.Base", baseline)
        paper = self.repo / "papers" / "Fixture"
        (paper / "Extra.lean").write_text("def extra : Nat := 7\n", encoding="utf-8")
        (paper / "Base.lean").write_text(
            "import\n  Fixture.Extra\n\ndef base : Nat := extra\n",
            encoding="utf-8",
        )

        changed, error = closure.lean_loaded_module_closure(
            self.repo, "Fixture.PaperInterface", timeout_seconds=120
        )

        self.assertEqual(error, "")
        self.assertNotIn("Fixture.Extra", baseline)
        self.assertIn("Fixture.Extra", changed)


if __name__ == "__main__":
    unittest.main()
