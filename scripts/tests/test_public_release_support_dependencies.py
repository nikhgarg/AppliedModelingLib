#!/usr/bin/env python3
"""Focused tests for authenticated dependency-only public transport."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.lean_import_closure import (  # noqa: E402
    LAKE_ROUTING_SCHEMA,
    WORKTREE_IDENTITY_SCHEMA,
    lean_import_closure_payload_sha256,
)
from scripts.obligation_evidence_graph import (  # noqa: E402
    build_evidence_leaf,
    build_obligation_graph,
    lean_reviewed_semantic_target_leaf,
)
from scripts.portable_evidence_identity import canonical_json_bytes  # noqa: E402
from scripts.public_release_support_dependencies import (  # noqa: E402
    select_public_support_dependencies,
)


class PublicReleaseSupportDependenciesTests(unittest.TestCase):
    @staticmethod
    def init_repo(repo: Path) -> None:
        subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
        subprocess.run(
            ["git", "config", "user.email", "fixture@example.com"],
            cwd=repo,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Fixture"], cwd=repo, check=True
        )

    @staticmethod
    def commit(repo: Path, message: str) -> str:
        subprocess.run(["git", "add", "-A"], cwd=repo, check=True)
        subprocess.run(["git", "commit", "-qm", message], cwd=repo, check=True)
        return subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=repo,
            check=True,
            text=True,
            capture_output=True,
        ).stdout.strip()

    @staticmethod
    def put_json(repo: Path, path: str, value: object) -> None:
        destination = repo / path
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(canonical_json_bytes(value) + b"\n")

    def authenticated_fixture(
        self,
        repo: Path,
        *,
        support_files: dict[str, bytes] | None = None,
        closure_support_files: dict[str, bytes] | None = None,
        parent_visibility: str = "public",
    ) -> tuple[str, set[str]]:
        support_files = support_files or {
            "papers/SupportDependency/Core.lean": b"def supportValue : Nat := 1\n"
        }
        closure_support_files = closure_support_files or dict(support_files)
        parent_path = "papers/PublicParent/PaperInterface.lean"
        parent_blob = b"import SupportDependency.Core\n"
        for path, blob in {parent_path: parent_blob, **support_files}.items():
            destination = repo / path
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(blob)
        self.put_json(
            repo,
            "papers/PublicParent/status.json",
            {"id": "PublicParent", "repository_visibility": parent_visibility},
        )

        source_blobs = {parent_path: parent_blob, **closure_support_files}
        sources = []
        for path, blob in sorted(source_blobs.items()):
            module = path.removeprefix("papers/").removesuffix(".lean").replace("/", ".")
            sources.append(
                {
                    "module": module,
                    "path": path,
                    "byte_length": len(blob),
                    "sha256": hashlib.sha256(blob).hexdigest(),
                }
            )
        closure = {
            "schema": WORKTREE_IDENTITY_SCHEMA,
            "entrypoint": parent_path,
            "entry_module": "PublicParent.PaperInterface",
            "lean_loaded_modules": sorted(source["module"] for source in sources),
            "sources": sources,
            "external_import_modules": [],
            "external_module_artifacts_sha256": "2" * 64,
            "build_controls": [
                {
                    "path": path,
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": 0,
                    "sha256": "3" * 64,
                }
                for path in ("lean-toolchain", "lake-manifest.json")
            ],
            "lake_routing": {
                "schema": LAKE_ROUTING_SCHEMA,
                "kind": "lean",
                "sha256": "4" * 64,
                "byte_length": 0,
            },
        }
        closure_digest = lean_import_closure_payload_sha256(closure)
        target = lean_reviewed_semantic_target_leaf(
            contract_sha256="5" * 64,
            semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256="6" * 64,
        )
        build = build_evidence_leaf(
            contract_sha256="7" * 64,
            target_declaration_sha256s=[target.leaf_sha256],
            build_command_sha256="8" * 64,
            toolchain_sha256="9" * 64,
            lean_import_closure_sha256=closure_digest,
        )
        graph = build_obligation_graph(
            [target, build], root_leaf_sha256s=[build.leaf_sha256]
        )
        pack = {
            "schema": 1,
            "paper": "PublicParent",
            "accepted_graph": graph.projection(),
            "leaves": {
                digest: graph.leaves[digest].projection()
                for digest in graph.topological_leaf_sha256s
            },
            "paper_index": {},
        }
        base = "papers/PublicParent/audit/obligation_evidence"
        pointer = f"{base}/current_accepted_graph.json"
        pack_path = (
            f"{base}/accepted_graphs/sha256/{graph.graph_sha256[:2]}/"
            f"{graph.graph_sha256}.json"
        )
        preimage = (
            f"{base}/lean_import_closures/sha256/{closure_digest[:2]}/"
            f"{closure_digest}.json"
        )
        self.put_json(repo, pointer, {"schema": 2, "graph_sha256": graph.graph_sha256})
        self.put_json(repo, pack_path, pack)
        self.put_json(repo, preimage, closure)
        receipt = repo / "papers/PublicParent/FINAL_CLOSURE_RECEIPT.md"
        receipt.write_text(
            "+++\n"
            "schema = 6\n"
            'paper = "PublicParent"\n'
            'closure_status = "current"\n'
            "acceptance_credential = false\n"
            'closed_at = "2026-09-07"\n'
            "[accepted_graph]\n"
            f'pointer = "{pointer}"\n'
            f'graph_sha256 = "{graph.graph_sha256}"\n'
            "+++\n",
            encoding="utf-8",
        )
        candidate = self.commit(repo, "authenticated support fixture")
        paths = set(
            subprocess.run(
                ["git", "ls-tree", "-r", "--name-only", candidate],
                cwd=repo,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.splitlines()
        )
        return candidate, paths

    @staticmethod
    def private_blob_entries(paths: set[str]) -> list[dict[str, object]]:
        return [
            {
                "path": path,
                "kind": "file",
                "provenance": "private_blob",
                "public_safety_reviewed": True,
            }
            for path in sorted(paths)
            if path.startswith("papers/SupportDependency/")
        ]

    def test_selects_exact_authenticated_support_namespace(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            self.init_repo(repo)
            candidate, paths = self.authenticated_fixture(repo)
            result = select_public_support_dependencies(
                repo, candidate, paths, self.private_blob_entries(paths)
            )
            from scripts.public_release_candidate_guard import status_visibility_issues
            self.assertTrue(status_visibility_issues(repo, candidate))
            self.assertEqual(
                status_visibility_issues(repo, candidate, entries=self.private_blob_entries(paths)),
                [],
            )
        self.assertEqual(result.issues, ())
        self.assertEqual(result.eligible_namespaces, frozenset({"SupportDependency"}))
        self.assertEqual(
            result.eligible_paths,
            frozenset({"papers/SupportDependency/Core.lean"}),
        )

    def test_dependency_only_namespace_cannot_be_listed_as_a_public_paper(self) -> None:
        for path, payload in (
            ("papers/catalog.json", {"publication_overrides": {"SupportDependency": {}}}),
            ("papers/human_status.json", {"papers": [{"id": "SupportDependency"}]}),
        ):
            with self.subTest(path=path), tempfile.TemporaryDirectory() as temporary:
                repo = Path(temporary)
                self.init_repo(repo)
                _candidate, paths = self.authenticated_fixture(repo)
                self.put_json(repo, path, payload)
                candidate = self.commit(repo, "add unsupported public paper listing")
                paths.add(path)
                result = select_public_support_dependencies(
                    repo, candidate, paths, self.private_blob_entries(paths)
                )
                self.assertFalse(result.eligible_namespaces)
                self.assertTrue(any("public paper listing" in issue for issue in result.issues))

    def test_rejects_mismatched_and_unreferenced_lean_files(self) -> None:
        cases = {
            "mismatched": (
                {
                    "papers/SupportDependency/Core.lean": b"def supportValue : Nat := 2\n"
                },
                {
                    "papers/SupportDependency/Core.lean": b"def supportValue : Nat := 1\n"
                },
                "do not match",
            ),
            "unreferenced": (
                {
                    "papers/SupportDependency/Core.lean": b"def supportValue : Nat := 1\n",
                    "papers/SupportDependency/Extra.lean": b"def extra : Nat := 2\n",
                },
                {
                    "papers/SupportDependency/Core.lean": b"def supportValue : Nat := 1\n"
                },
                "not referenced",
            ),
        }
        for name, (files, closure_files, expected) in cases.items():
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temporary:
                repo = Path(temporary)
                self.init_repo(repo)
                candidate, paths = self.authenticated_fixture(
                    repo,
                    support_files=files,
                    closure_support_files=closure_files,
                )
                result = select_public_support_dependencies(
                    repo, candidate, paths, self.private_blob_entries(paths)
                )
                self.assertEqual(result.eligible_namespaces, frozenset())
                self.assertTrue(any(expected in issue for issue in result.issues), result)

    def test_rejects_nonlean_content_and_namespace_root(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            self.init_repo(repo)
            candidate, _paths = self.authenticated_fixture(repo)
            (repo / "papers/SupportDependency/README.md").write_text("support paper\n")
            (repo / "papers/SupportDependency.lean").write_text(
                "import SupportDependency.Core\n"
            )
            candidate = self.commit(repo, "add forbidden support surfaces")
            paths = set(
                subprocess.run(
                    ["git", "ls-tree", "-r", "--name-only", candidate],
                    cwd=repo,
                    check=True,
                    text=True,
                    capture_output=True,
                ).stdout.splitlines()
            )
            result = select_public_support_dependencies(
                repo, candidate, paths, self.private_blob_entries(paths)
            )
        self.assertEqual(result.eligible_namespaces, frozenset())
        self.assertTrue(any("must not expose" in issue for issue in result.issues), result)
        self.assertTrue(any("non-Lean file" in issue for issue in result.issues), result)

    def test_rejects_non_private_blob_new_export(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            self.init_repo(repo)
            candidate, paths = self.authenticated_fixture(repo)
            entries = self.private_blob_entries(paths)
            entries[0]["provenance"] = "public_base_addition"
            result = select_public_support_dependencies(repo, candidate, paths, entries)
        self.assertEqual(result.eligible_namespaces, frozenset())
        self.assertTrue(
            any("requires a reviewed exact-file private_blob" in issue for issue in result.issues),
            result,
        )

    def test_private_or_uncredentialed_parent_cannot_authorize_support(self) -> None:
        for case in ("private_parent", "tampered_graph"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as temporary:
                repo = Path(temporary)
                self.init_repo(repo)
                candidate, paths = self.authenticated_fixture(
                    repo,
                    parent_visibility=("private_only" if case == "private_parent" else "public"),
                )
                if case == "tampered_graph":
                    pointer = (
                        repo
                        / "papers/PublicParent/audit/obligation_evidence/"
                        "current_accepted_graph.json"
                    )
                    pointer.write_text(
                        json.dumps({"schema": 2, "graph_sha256": "a" * 64}) + "\n"
                    )
                    candidate = self.commit(repo, "tamper selected graph")
                    paths = set(
                        subprocess.run(
                            ["git", "ls-tree", "-r", "--name-only", candidate],
                            cwd=repo,
                            check=True,
                            text=True,
                            capture_output=True,
                        ).stdout.splitlines()
                    )
                result = select_public_support_dependencies(
                    repo, candidate, paths, self.private_blob_entries(paths)
                )
                self.assertEqual(result.eligible_namespaces, frozenset())
                self.assertTrue(
                    any(
                        "not referenced" in issue
                        or "cannot authenticate support dependency closure" in issue
                        for issue in result.issues
                    ),
                    result,
                )

    def test_rejects_inexact_candidate_path_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            self.init_repo(repo)
            candidate, paths = self.authenticated_fixture(repo)
            paths.remove("papers/SupportDependency/Core.lean")
            result = select_public_support_dependencies(
                repo, candidate, paths, self.private_blob_entries(paths)
            )
        self.assertEqual(result.eligible_paths, frozenset())
        self.assertIn("path inventory is not exact", result.issues[0])

    def test_namespace_with_status_is_not_dependency_only(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repo = Path(temporary)
            self.init_repo(repo)
            candidate, _paths = self.authenticated_fixture(repo)
            self.put_json(
                repo,
                "papers/SupportDependency/status.json",
                {"id": "SupportDependency", "repository_visibility": "private_only"},
            )
            candidate = self.commit(repo, "make support namespace paper-shaped")
            paths = set(
                subprocess.run(
                    ["git", "ls-tree", "-r", "--name-only", candidate],
                    cwd=repo,
                    check=True,
                    text=True,
                    capture_output=True,
                ).stdout.splitlines()
            )
            result = select_public_support_dependencies(
                repo, candidate, paths, self.private_blob_entries(paths)
            )
        self.assertNotIn("SupportDependency", result.eligible_namespaces)
        self.assertNotIn("papers/SupportDependency/Core.lean", result.eligible_paths)


if __name__ == "__main__":
    unittest.main()
