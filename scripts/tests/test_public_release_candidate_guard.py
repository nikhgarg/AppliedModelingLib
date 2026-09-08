#!/usr/bin/env python3
"""Regression tests for public release candidate allowlisting and visibility."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import public_release_candidate_guard as guard  # noqa: E402
from scripts import public_source_role_projection as role_projection  # noqa: E402
from scripts.obligation_evidence_projection import _source_role_contract  # noqa: E402
from scripts.corrected_target_identity import (  # noqa: E402
    CORRECTED_TARGET_RECORD_SHA256_FIELD,
    CORRECTED_TARGET_REVIEW_SHA256_FIELD,
    corrected_target_record_digest,
    corrected_target_review_digest,
)


def _private_corrected_target() -> dict[str, object]:
    statement = "Every feasible assignment has welfare at most the stated benchmark."
    excerpt = (
        "This private approval passage contains repository instructions and a user "
        "quotation that must remain outside every public source map."
    )
    target: dict[str, object] = {
        "schema": 1,
        "statement": statement,
        "archival_equivalence_claimed": False,
        "archival_source_locator": "Theorem 1",
        "archival_source_quote_sha256": "a" * 64,
        "governing_defect_ids": ["D1"],
        "approval": {
            "artifact_path": "docs/PRIVATE_APPROVAL.md",
            "artifact_protocol": "unique_normalized_artifact_excerpt_v1",
            "artifact_excerpt": excerpt,
            "artifact_excerpt_sha256": hashlib.sha256(excerpt.encode()).hexdigest(),
            "kind": "recorded_user_direction",
            "recorded_at": "2026-09-07",
            "reference": "private repository instruction",
            "target_statement_sha256": hashlib.sha256(statement.encode()).hexdigest(),
        },
    }
    target[CORRECTED_TARGET_RECORD_SHA256_FIELD] = corrected_target_record_digest(target)
    target[CORRECTED_TARGET_REVIEW_SHA256_FIELD] = corrected_target_review_digest(target)
    return target


def _public_corrected_target() -> dict[str, object]:
    private = _private_corrected_target()
    private.pop("approval")
    return private


def _projected_corrected_target_map() -> dict[str, object]:
    return {
        guard.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD: {
            "schema": guard.PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
            "approval_material_included": False,
        },
        "items": {
            "theorem_1": {
                "coverage_status": "corrected_source_statement",
                "corrected_target": _public_corrected_target(),
            },
            "support": {
                "coverage_status": "subsumed_by_selected_result",
                "corrected_target": _public_corrected_target(),
            },
        },
    }


class PublicReleaseCandidateGuardTests(unittest.TestCase):
    def test_paper_target_guard_checks_registered_roots_beyond_default_targets(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            self.init_repo(repo)
            (repo / "lakefile.toml").write_text(
                'name = "Fixture"\ndefaultTargets = []\n'
                '[[lean_lib]]\nname = "HiddenPaper"\nsrcDir = "papers"\n'
            )
            commit = self.commit(repo, "unexported registered paper")
            self.assertEqual(guard.public_paper_target_issues(repo, commit), [
                "public paper target HiddenPaper: registered root is not exported: "
                "papers/HiddenPaper.lean"
            ])
            (repo / "papers").mkdir()
            (repo / "papers/HiddenPaper.lean").write_text("import Lean\n")
            # A local file must not hide a missing file in the release commit.
            self.assertTrue(guard.public_paper_target_issues(repo, commit))
            complete = self.commit(repo, "export the registered root")
            self.assertEqual(guard.public_paper_target_issues(repo, complete), [])

    def test_paper_target_guard_uses_explicit_roots(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            self.init_repo(repo)
            (repo / "lakefile.toml").write_text(
                'name = "Fixture"\n[[lean_lib]]\nname = "Paper"\n'
                'srcDir = "papers"\nroots = ["Paper.ProofInterface"]\n'
            )
            (repo / "papers/Paper").mkdir(parents=True)
            (repo / "papers/Paper/ProofInterface.lean").write_text("import Lean\n")
            complete = self.commit(repo, "export explicit paper root")
            self.assertEqual(guard.public_paper_target_issues(repo, complete), [])

    def test_dependency_closure_resolves_explicit_lake_script_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            self.init_repo(repo)
            (repo / "lakefile.toml").write_text(
                'name = "Fixture"\n\n'
                '[[lean_lib]]\nname = "Fixture"\n\n'
                '[[lean_lib]]\nname = "FixtureAuditScripts"\n'
                'srcDir = "scripts"\nroots = ["fixture_audit_helper"]\n',
                encoding="utf-8",
            )
            entrypoint = repo / "AppliedModelingLib" / "AllForSemanticInventory.lean"
            bridge = repo / "AppliedModelingLib" / "Audit" / "SignatureManifest.lean"
            helper = repo / "scripts" / "fixture_audit_helper.lean"
            entrypoint.parent.mkdir(parents=True)
            bridge.parent.mkdir(parents=True)
            helper.parent.mkdir(parents=True)
            entrypoint.write_text(
                "import AppliedModelingLib.Audit.SignatureManifest\n",
                encoding="utf-8",
            )
            bridge.write_text("import fixture_audit_helper\n", encoding="utf-8")
            helper.write_text("import Lean\n", encoding="utf-8")
            candidate = self.commit(repo, "registered script helper")

            issues = guard._public_candidate_dependency_closure_issues(
                repo,
                candidate,
                extra_entrypoints={
                    "AppliedModelingLib/AllForSemanticInventory.lean"
                },
            )
            self.assertEqual(issues, [])

            bridge.write_text(
                "import fixture_audit_helper\nimport missing_audit_helper\n",
                encoding="utf-8",
            )
            candidate = self.commit(repo, "unregistered adjacent helper")
            issues = guard._public_candidate_dependency_closure_issues(
                repo,
                candidate,
                extra_entrypoints={
                    "AppliedModelingLib/AllForSemanticInventory.lean"
                },
            )
            self.assertTrue(
                any(
                    issue.imported_module == "missing_audit_helper"
                    and "explicit external-module registry" in issue.reason
                    for issue in issues
                ),
                issues,
            )

            bridge.write_text("import fixture_audit_helper\n", encoding="utf-8")
            helper.unlink()
            candidate = self.commit(repo, "missing registered script helper")
            issues = guard._public_candidate_dependency_closure_issues(
                repo,
                candidate,
                extra_entrypoints={
                    "AppliedModelingLib/AllForSemanticInventory.lean"
                },
            )
            self.assertTrue(
                any(
                    issue.imported_module == "fixture_audit_helper"
                    and "explicit external-module registry" in issue.reason
                    for issue in issues
                ),
                issues,
            )

    def test_selected_graph_authority_requires_public_engine_protocol_row(
        self,
    ) -> None:
        from scripts.portable_evidence_identity import portable_evidence_sha256

        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            self.init_repo(repo)
            engine = "a" * 64
            protocol = "b" * 64
            closeout_contract = "c" * 64
            authority_material = {
                "schema": 2,
                "acceptance_credential": False,
                "authority_kind": "current_runtime_pass",
                "paper": "Fixture",
                "engine_tree_sha256": engine,
                "closeout_contract_sha256": closeout_contract,
            }
            authority = {
                **authority_material,
                "authority_sha256": portable_evidence_sha256(
                    authority_material
                ),
            }
            graph_sha256 = "d" * 64
            pointer_path = (
                repo
                / "papers/Fixture/audit/obligation_evidence/"
                "current_accepted_graph.json"
            )
            pack_path = (
                repo
                / "papers/Fixture/audit/obligation_evidence/accepted_graphs/"
                f"sha256/{graph_sha256[:2]}/{graph_sha256}.json"
            )
            registry_path = repo / "config/formalization_engine_revisions.json"
            pointer_path.parent.mkdir(parents=True)
            pack_path.parent.mkdir(parents=True)
            registry_path.parent.mkdir(parents=True)
            pointer_path.write_text(
                json.dumps({"schema": 2, "graph_sha256": graph_sha256}),
                encoding="utf-8",
            )
            pack_path.write_text(
                json.dumps(
                    {
                        "leaves": {
                            "e" * 64: {
                                "kind": "paper_closure",
                                "semantic_payload": {
                                    "strict_closeout_authority": authority
                                },
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            def registry(registered_engine: str) -> dict[str, object]:
                return {
                    "schema": 2,
                    "boundary": (
                        "tracked-formalization-engine-production-sources-v1"
                    ),
                    "independent_registration_start_sequence": 1,
                    "revisions": [
                        {
                            "sequence": 1,
                            "engine_tree_sha256": registered_engine,
                            "formalization_review_protocol_sha256": protocol,
                            "rationale": (
                                "Register the exact public fixture authority."
                            ),
                            "verification": [
                                "Focused selected-authority registration test."
                            ],
                        }
                    ],
                }

            registry_path.write_text(json.dumps(registry(engine)), encoding="utf-8")
            candidate = self.commit(repo, "registered selected authority")
            self.assertEqual(
                guard.selected_graph_authority_registration_issues(
                    repo, candidate
                ),
                [],
            )

            registry_path.write_text(
                json.dumps(registry("f" * 64)), encoding="utf-8"
            )
            candidate = self.commit(repo, "missing selected authority")
            issues = guard.selected_graph_authority_registration_issues(
                repo, candidate
            )
            self.assertTrue(
                any(
                    engine in issue
                    and "no public engine/protocol registration" in issue
                    for issue in issues
                ),
                issues,
            )

    def test_public_artifact_scan_rejects_scope_approval_history(self) -> None:
        path = "papers/Fixture/audit/paper_statement_map.json"
        raw = {"items": {"claim": {"user_approved_scope_exclusion": {
            "approval_reference": "Private user exchange with an unpublished direction."
        }}}}
        self.assertTrue(guard._public_artifact_string_issues(raw, relative_path=path))
        raw["items"]["claim"]["user_approved_scope_exclusion"]["approval_reference"] = (
            guard.PUBLIC_WITHHELD_APPROVAL_REFERENCE
        )
        self.assertEqual(guard._public_artifact_string_issues(raw, relative_path=path), [])

    @staticmethod
    def init_repo(repo: Path) -> None:
        repo.mkdir(parents=True, exist_ok=True)
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
    def configure_origin(repo: Path, url: str, main_commit: str) -> None:
        subprocess.run(["git", "remote", "add", "origin", url], cwd=repo, check=True)
        subprocess.run(
            ["git", "update-ref", "refs/remotes/origin/main", main_commit],
            cwd=repo,
            check=True,
        )

    @staticmethod
    def write_approval(
        path: Path,
        *,
        candidate_commit: str,
        public_base_commit: str,
        allowlist: Path,
        private_source_commits: list[str],
        guard_sha256: str | None = None,
        trusted_tooling_sha256: str | None = None,
    ) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.parent.chmod(0o700)
        path.write_text(
            json.dumps(
                {
                    "schema": 2,
                    "candidate_commit": candidate_commit,
                    "public_base_commit": public_base_commit,
                    "allowlist_sha256": guard._sha256_bytes(allowlist.read_bytes()),
                    "guard_sha256": guard_sha256 or guard._guard_sha256(),
                    "trusted_tooling_sha256": (
                        trusted_tooling_sha256 or guard._trusted_tooling_sha256()
                    ),
                    "private_source_commits": sorted(private_source_commits),
                }
            ),
            encoding="utf-8",
        )
        path.chmod(0o600)

    def test_allowlist_requires_explicit_review_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "allowlist.json"
            path.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "entries": [
                            {
                                "path": "papers/Fixture/PaperInterface.lean",
                                "kind": "file",
                                "provenance": "private_blob",
                                "source_commit": "1" * 40,
                                "reason": "reviewed paper export",
                                "public_safety_reviewed": False,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )

            with self.assertRaisesRegex(ValueError, "public_safety_reviewed=true"):
                guard.load_allowlist(path)

    def test_reviewer_approval_requires_schema_2_tooling_pin(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            approval = Path(temp_dir) / "approval.json"
            approval.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "candidate_commit": "1" * 40,
                        "public_base_commit": "2" * 40,
                        "allowlist_sha256": "3" * 64,
                        "guard_sha256": "4" * 64,
                        "private_source_commits": [],
                    }
                ),
                encoding="utf-8",
            )
            approval.chmod(0o600)

            with self.assertRaisesRegex(ValueError, "schema-2"):
                guard.load_release_approval(approval)

    def test_trusted_tooling_digest_covers_production_files_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            scripts = Path(temp_dir) / "scripts"
            tests = scripts / "tests"
            cache = scripts / "__pycache__"
            tests.mkdir(parents=True)
            cache.mkdir()
            production = scripts / "guard.py"
            production.write_text("value = 1\n", encoding="utf-8")
            (tests / "test_guard.py").write_text("ignored = 1\n", encoding="utf-8")
            (cache / "guard.pyc").write_bytes(b"ignored")

            initial = guard._trusted_tooling_sha256(scripts)
            (tests / "test_guard.py").write_text("ignored = 2\n", encoding="utf-8")
            (cache / "guard.pyc").write_bytes(b"also ignored")
            self.assertEqual(guard._trusted_tooling_sha256(scripts), initial)

            production.write_text("value = 2\n", encoding="utf-8")
            self.assertNotEqual(guard._trusted_tooling_sha256(scripts), initial)

            (scripts / "new_helper.py").write_text("value = 3\n", encoding="utf-8")
            with_helper = guard._trusted_tooling_sha256(scripts)
            self.assertNotEqual(with_helper, initial)

            (scripts / "unsafe.py").symlink_to(production)
            with self.assertRaisesRegex(RuntimeError, "non-regular"):
                guard._trusted_tooling_sha256(scripts)

    def test_allowlist_matches_only_the_exact_file(self) -> None:
        entry = guard.AllowlistEntry(
            "papers/Public/status.json", "file", "private_blob", "1" * 40, "ok", None
        )
        self.assertTrue(guard.path_is_allowlisted("papers/Public/status.json", [entry]))
        self.assertFalse(guard.path_is_allowlisted("papers/Public", [entry]))
        self.assertFalse(guard.path_is_allowlisted("papers/PublicPrivate/status.json", [entry]))

    def test_public_base_edit_allowlist_requires_distinct_exact_blob_digests(self) -> None:
        base_entry = {
            "path": "lakefile.toml",
            "kind": "file",
            "provenance": "public_base_edit",
            "public_base_blob_sha256": "1" * 64,
            "candidate_blob_sha256": "2" * 64,
            "reason": "reviewed in-place public edit",
            "public_safety_reviewed": True,
        }

        entries = guard.parse_allowlist(
            json.dumps({"schema": 1, "entries": [base_entry]}).encode(),
            source="fixture",
        )

        self.assertEqual(entries[0].public_base_blob_sha256, "1" * 64)
        self.assertEqual(entries[0].candidate_blob_sha256, "2" * 64)
        for field, value, expected in (
            ("candidate_blob_sha256", None, "candidate_blob_sha256"),
            ("public_base_blob_sha256", "bad", "public_base_blob_sha256"),
            ("candidate_blob_sha256", "1" * 64, "distinct"),
            ("source_commit", "3" * 40, "cannot declare"),
        ):
            with self.subTest(field=field, value=value):
                candidate = dict(base_entry)
                if value is None:
                    candidate.pop(field)
                else:
                    candidate[field] = value
                with self.assertRaisesRegex(ValueError, expected):
                    guard.parse_allowlist(
                        json.dumps({"schema": 1, "entries": [candidate]}).encode(),
                        source="fixture",
                    )

    def test_public_base_addition_allowlist_requires_exact_candidate_digest(self) -> None:
        addition = {
            "path": "config/public-only.json",
            "kind": "file",
            "provenance": "public_base_addition",
            "candidate_blob_sha256": "2" * 64,
            "reason": "reviewed public-only trust configuration",
            "public_safety_reviewed": True,
        }

        entries = guard.parse_allowlist(
            json.dumps({"schema": 1, "entries": [addition]}).encode(),
            source="fixture",
        )

        self.assertIsNone(entries[0].public_base_blob_sha256)
        self.assertEqual(entries[0].candidate_blob_sha256, "2" * 64)
        for field, value, expected in (
            ("candidate_blob_sha256", None, "candidate_blob_sha256"),
            ("candidate_blob_sha256", "bad", "candidate_blob_sha256"),
            ("public_base_blob_sha256", "1" * 64, "cannot declare"),
            ("source_commit", "3" * 40, "cannot declare"),
        ):
            with self.subTest(field=field, value=value):
                candidate = dict(addition)
                if value is None:
                    candidate.pop(field)
                else:
                    candidate[field] = value
                with self.assertRaisesRegex(ValueError, expected):
                    guard.parse_allowlist(
                        json.dumps({"schema": 1, "entries": [candidate]}).encode(),
                        source="fixture",
                    )

    def test_allowlist_rejects_every_directory_entry(self) -> None:
        for directory in ("papers", "papers/Fixture", "scripts/reviewed"):
            with self.subTest(directory=directory), tempfile.TemporaryDirectory() as temp_dir:
                path = Path(temp_dir) / "allowlist.json"
                path.write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "entries": [
                                {
                                    "path": directory,
                                    "kind": "directory",
                                    "provenance": "private_blob",
                                    "source_commit": "1" * 40,
                                    "reason": "overbroad fixture",
                                    "public_safety_reviewed": True,
                                }
                            ],
                        }
                    ),
                    encoding="utf-8",
                )

                with self.assertRaisesRegex(ValueError, "kind must be file"):
                    guard.load_allowlist(path)

    def test_public_candidate_rejects_private_and_missing_visibility(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(
                ["git", "config", "user.email", "fixture@example.com"],
                cwd=repo,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Fixture"], cwd=repo, check=True
            )
            for paper, payload in {
                "Public": {"id": "Public", "repository_visibility": "public"},
                "Private": {"id": "Private", "repository_visibility": "private_only"},
                "Missing": {"id": "Missing"},
            }.items():
                folder = repo / "papers" / paper
                folder.mkdir(parents=True)
                (folder / "status.json").write_text(json.dumps(payload), encoding="utf-8")
            no_status = repo / "papers" / "NoStatus"
            no_status.mkdir(parents=True)
            (no_status / "PaperInterface.lean").write_text(
                "theorem visible : True := by trivial\n", encoding="utf-8"
            )
            (repo / "papers" / "RootOnly.lean").write_text(
                "import NoStatus.PaperInterface\n", encoding="utf-8"
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "candidate"], cwd=repo, check=True)

            issues = guard.status_visibility_issues(repo)

        self.assertTrue(
            any("Private" in issue and "private_only" in issue for issue in issues),
            issues,
        )
        self.assertTrue(any("Missing" in issue and "None" in issue for issue in issues), issues)
        self.assertTrue(
            any("NoStatus" in issue and "requires" in issue for issue in issues),
            issues,
        )
        self.assertTrue(
            any("RootOnly" in issue and "requires" in issue for issue in issues),
            issues,
        )
        self.assertFalse(any("papers/Public/status.json" in issue for issue in issues), issues)

    def test_public_paper_requires_committed_terminal_artifacts(self) -> None:
        for status in ("formalized", "partially formalized"):
            with self.subTest(status=status), tempfile.TemporaryDirectory() as temp_dir:
                repo = Path(temp_dir)
                self.init_repo(repo)
                folder = repo / "papers" / "Fixture"
                folder.mkdir(parents=True)
                (folder / "status.json").write_text(json.dumps({
                    "id": "Fixture", "status": status,
                    "repository_visibility": "public",
                }))
                missing_ref = self.commit(repo, "public paper without closeout")
                self.assertEqual(len(guard.status_visibility_issues(repo)), 2)

                pointer = folder / "audit/obligation_evidence/current_accepted_graph.json"
                pointer.parent.mkdir(parents=True)
                pointer.write_text('{}\n')
                (folder / "FINAL_CLOSURE_RECEIPT.md").write_text('receipt fixture\n')
                # Worktree artifacts cannot satisfy the exact candidate tree.
                self.assertEqual(len(guard.status_visibility_issues(repo)), 2)
                self.commit(repo, "retain terminal artifact paths")
                # This gate checks presence only; graph transport authenticates contents.
                self.assertEqual(guard.status_visibility_issues(repo), [])
                self.assertEqual(len(guard.status_visibility_issues(repo, missing_ref)), 2)

                pointer.unlink()
                self.commit(repo, "omit accepted graph pointer")
                issues = guard.status_visibility_issues(repo)
                self.assertEqual(len(issues), 1)
                self.assertIn("current_accepted_graph.json", issues[0])

    def test_changed_public_finalized_paper_requires_packet_and_readme_link(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
            subprocess.run(
                ["git", "config", "user.email", "fixture@example.com"],
                cwd=repo,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Fixture"], cwd=repo, check=True
            )
            folder = repo / "papers" / "Paper"
            folder.mkdir(parents=True)
            status_path = folder / "status.json"
            status_path.write_text(
                json.dumps(
                    {
                        "id": "Paper",
                        "repository_visibility": "public",
                        "status": "paper draft",
                    }
                ),
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "base"], cwd=repo, check=True)
            base = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=repo,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.strip()
            status_path.write_text(
                json.dumps(
                    {
                        "id": "Paper",
                        "repository_visibility": "public",
                        "status": "formalized",
                        "artifacts": {},
                    }
                ),
                encoding="utf-8",
            )
            subprocess.run(["git", "add", "."], cwd=repo, check=True)
            subprocess.run(["git", "commit", "-qm", "candidate"], cwd=repo, check=True)

            issues = guard.changed_formalized_packet_issues(
                repo, "HEAD", public_base_ref=base
            )

        self.assertTrue(any("human_review_packet_pdf" in issue for issue in issues), issues)
        self.assertTrue(any("HUMAN_REVIEW_PACKET.pdf" in issue for issue in issues), issues)

    def test_deleted_status_does_not_require_a_candidate_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            folder = repo / "papers" / "Paper"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Paper",
                        "repository_visibility": "public",
                        "status": "formalized",
                    }
                ),
                encoding="utf-8",
            )
            base = self.commit(repo, "base")
            subprocess.run(["git", "rm", "-qr", "papers/Paper"], cwd=repo, check=True)
            self.commit(repo, "delete paper")

            issues = guard.changed_formalized_packet_issues(
                repo, "HEAD", public_base_ref=base
            )

        self.assertEqual(issues, [])

    def test_private_blob_provenance_compares_exact_committed_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            for repo in (private, candidate):
                repo.mkdir()
                subprocess.run(["git", "init", "-q"], cwd=repo, check=True)
                subprocess.run(
                    ["git", "config", "user.email", "fixture@example.com"],
                    cwd=repo,
                    check=True,
                )
                subprocess.run(
                    ["git", "config", "user.name", "Fixture"], cwd=repo, check=True
                )
                (repo / "scripts").mkdir()
                (repo / "scripts" / "shared.py").write_text("value = 1\n", encoding="utf-8")
                subprocess.run(["git", "add", "."], cwd=repo, check=True)
                subprocess.run(["git", "commit", "-qm", "source"], cwd=repo, check=True)
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=private,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.strip()
            entry = guard.AllowlistEntry(
                "scripts/shared.py",
                "file",
                "private_blob",
                source_commit,
                "reviewed shared tool",
                None,
            )
            change = guard.CandidateChange("M", "scripts/shared.py")

            self.assertEqual(
                guard.source_provenance_issues(
                    candidate, private, "HEAD", [change], [entry]
                ),
                [],
            )
            (candidate / "scripts" / "shared.py").write_text(
                "value = 2\n", encoding="utf-8"
            )
            subprocess.run(
                ["git", "add", "scripts/shared.py"], cwd=candidate, check=True
            )
            subprocess.run(
                ["git", "commit", "-qm", "different"], cwd=candidate, check=True
            )
            issues = guard.source_provenance_issues(
                candidate, private, "HEAD", [change], [entry]
            )

        self.assertTrue(any("differs from private source commit" in issue for issue in issues), issues)

    def _display_projection_fixture(
        self, root: Path
    ) -> tuple[Path, Path, str, str, guard.AllowlistEntry, bytes, bytes]:
        """Create one candidate map with a source-free display manifest."""

        private = root / "private"
        candidate = root / "candidate"
        self.init_repo(private)
        self.init_repo(candidate)
        map_path = "papers/Fixture/audit/paper_statement_map.json"
        manifest_path = "papers/Fixture/audit/public_source_display_projection.json"
        quote = "Definition 1. A fixture object has one named property."
        quote_sha256 = guard._sha256_bytes(quote.encode("utf-8"))
        public_anchor = {
            "line_end": 1,
            "line_start": 1,
            "publication_locator": "cited publication",
            "quoted_text": quote,
            "quoted_text_sha256": quote_sha256,
        }
        public_context_anchor = {
            "line_end": 2,
            "line_start": 2,
            "publication_locator": "cited publication",
            "quoted_text": "Theorem 1. Every fixture object has that property.",
            "quoted_text_sha256": guard._sha256_bytes(
                b"Theorem 1. Every fixture object has that property."
            ),
        }
        private_map = {
            "paper": "Fixture",
            "source_artifact_path": ".audit_source/Fixture.txt",
            "source_artifact_sha256": "a" * 64,
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "fixture_definition": {
                    "source_kind": "definition",
                    "source_anchor_evidence": [
                        {**public_anchor, "path": ".audit_source/Fixture.txt"}
                    ],
                    "semantic_context_requirements": [
                        {
                            "semantic_role": "result",
                            "source_anchor_evidence": [
                                {
                                    **public_context_anchor,
                                    "path": ".audit_source/Fixture.txt",
                                }
                            ],
                        }
                    ],
                }
            },
        }
        private_path = private / map_path
        private_path.parent.mkdir(parents=True)
        private_blob = (json.dumps(private_map, sort_keys=True) + "\n").encode("utf-8")
        private_path.write_bytes(private_blob)
        source_commit = self.commit(private, "private source map")

        public_blob = guard.project_bytes(
            map_path, private_blob, include_source_display_marker=True
        )
        public_map = json.loads(public_blob.decode("utf-8"))
        public_anchor = public_map["items"]["fixture_definition"][
            "source_anchor_evidence"
        ][0]
        public_context_anchor = public_map["items"]["fixture_definition"][
            "semantic_context_requirements"
        ][0]["source_anchor_evidence"][0]
        manifest = {
            "generator": guard.PUBLIC_SOURCE_DISPLAY_PROJECTION_GENERATOR,
            "paper_id": "Fixture",
            "private_source_map_sha256": guard._sha256_bytes(private_blob),
            "public_manifest_path": manifest_path,
            "public_source_map_sha256": guard._sha256_bytes(public_blob),
            "raw_source_artifact_included": False,
            "raw_source_display_material": guard.PUBLIC_SOURCE_DISPLAY_PROJECTION_MATERIAL,
            "schema": guard.PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA,
            "selected_source_item_ids": ["fixture_definition"],
            "selected_source_items": {
                "fixture_definition": {
                    "source_anchors": [public_anchor],
                    "source_kind": "definition",
                    "semantic_context": [
                        {
                            "semantic_role": "result",
                            "source_anchors": [public_context_anchor],
                        }
                    ],
                }
            },
            "source_artifact_sha256": "a" * 64,
            "source_coverage_mode": "named_theoretical_statements",
        }
        candidate_map_path = candidate / map_path
        candidate_map_path.parent.mkdir(parents=True)
        candidate_map_path.write_bytes(public_blob)
        manifest_blob = (json.dumps(manifest, sort_keys=True) + "\n").encode("utf-8")
        (candidate / manifest_path).write_bytes(manifest_blob)
        candidate_commit = self.commit(candidate, "candidate display projection")
        entry = guard.AllowlistEntry(
            path=map_path,
            kind="file",
            provenance="private_projection",
            source_commit=source_commit,
            reason="projected source map",
            generator=guard.PUBLIC_PROJECTION_GENERATOR,
            private_source_blob_sha256=guard._sha256_bytes(private_blob),
            candidate_blob_sha256=guard._sha256_bytes(public_blob),
        )
        return (
            private,
            candidate,
            source_commit,
            candidate_commit,
            entry,
            public_blob,
            manifest_blob,
        )

    def test_public_display_projection_guard_binds_candidate_map_and_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (
                private,
                candidate,
                _source_commit,
                candidate_commit,
                entry,
                public_blob,
                manifest_blob,
            ) = self._display_projection_fixture(root)

            self.assertEqual(
                guard.public_source_display_projection_issues(
                    candidate,
                    candidate_commit,
                    [entry],
                    private_repo=private,
                ),
                [],
            )
            self.assertEqual(
                guard.source_provenance_issues(
                    candidate,
                    private,
                    candidate_commit,
                    [guard.CandidateChange("A", entry.path)],
                    [entry],
                ),
                [],
            )

            (candidate / "papers/Fixture/audit/public_source_display_projection.json").unlink()
            missing_manifest_commit = self.commit(candidate, "remove display manifest")
            missing_manifest_issues = guard.public_source_display_projection_issues(
                candidate, missing_manifest_commit, [entry], private_repo=private
            )

            # Restore the receipt and alter the projected map without refreshing
            # the bound candidate-map digest in its manifest.
            (candidate / "papers/Fixture/audit/public_source_display_projection.json").write_bytes(
                manifest_blob
            )
            tampered_map = json.loads(public_blob.decode("utf-8"))
            tampered_map["source_artifact_sha256"] = "b" * 64
            (candidate / "papers/Fixture/audit/paper_statement_map.json").write_text(
                json.dumps(tampered_map, sort_keys=True) + "\n", encoding="utf-8"
            )
            tampered_map_commit = self.commit(candidate, "tamper projected map")
            tampered_map_issues = guard.public_source_display_projection_issues(
                candidate, tampered_map_commit, [entry], private_repo=private
            )

            # Restore the exact projected map and alter only a semantic-context
            # anchor in the public manifest.  This exercises the non-direct
            # source context rather than merely its selected-item list.
            (candidate / "papers/Fixture/audit/paper_statement_map.json").write_bytes(
                public_blob
            )
            tampered_manifest = json.loads(manifest_blob.decode("utf-8"))
            tampered_manifest["selected_source_items"]["fixture_definition"][
                "semantic_context"
            ][0]["source_anchors"][0]["quoted_text"] = "altered excerpt"
            (candidate / "papers/Fixture/audit/public_source_display_projection.json").write_text(
                json.dumps(tampered_manifest, sort_keys=True) + "\n", encoding="utf-8"
            )
            tampered_anchor_commit = self.commit(candidate, "tamper manifest anchor")
            tampered_anchor_issues = guard.public_source_display_projection_issues(
                candidate, tampered_anchor_commit, [entry], private_repo=private
            )

            # A declared private-map hash must agree with the map's allowlisted
            # exact private provenance whenever the display manifest exposes it.
            tampered_private_hash = json.loads(manifest_blob.decode("utf-8"))
            tampered_private_hash["private_source_map_sha256"] = "c" * 64
            (candidate / "papers/Fixture/audit/public_source_display_projection.json").write_text(
                json.dumps(tampered_private_hash, sort_keys=True) + "\n", encoding="utf-8"
            )
            tampered_private_hash_commit = self.commit(candidate, "tamper private map binding")
            tampered_private_hash_issues = guard.public_source_display_projection_issues(
                candidate,
                tampered_private_hash_commit,
                [entry],
                private_repo=private,
            )

            # A candidate anchor cannot retain a local lookup path even if the
            # manifest's public-map digest is refreshed to bind that altered map.
            path_retaining_map = json.loads(public_blob.decode("utf-8"))
            path_retaining_map["items"]["fixture_definition"][
                "source_anchor_evidence"
            ][0]["path"] = ".audit_source/Fixture.txt"
            path_retaining_blob = (
                json.dumps(path_retaining_map, sort_keys=True) + "\n"
            ).encode("utf-8")
            path_retaining_manifest = json.loads(manifest_blob.decode("utf-8"))
            path_retaining_manifest["public_source_map_sha256"] = guard._sha256_bytes(
                path_retaining_blob
            )
            (candidate / "papers/Fixture/audit/paper_statement_map.json").write_bytes(
                path_retaining_blob
            )
            (candidate / "papers/Fixture/audit/public_source_display_projection.json").write_text(
                json.dumps(path_retaining_manifest, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            retained_path_commit = self.commit(candidate, "retain a source path")
            retained_path_issues = guard.public_source_display_projection_issues(
                candidate, retained_path_commit, [entry], private_repo=private
            )

            # A saved manifest cannot be used to authenticate an unmarked map.
            private_blob = subprocess.run(
                ["git", "show", f"{entry.source_commit}:{entry.path}"],
                cwd=private,
                check=True,
                stdout=subprocess.PIPE,
            ).stdout
            unmarked_blob = guard.project_bytes(entry.path, private_blob)
            (candidate / entry.path).write_bytes(unmarked_blob)
            (candidate / "papers/Fixture/audit/public_source_display_projection.json").write_bytes(
                manifest_blob
            )
            unmarked_commit = self.commit(candidate, "remove display marker")
            unmarked_issues = guard.public_source_display_projection_issues(
                candidate, unmarked_commit, [entry], private_repo=private
            )

        self.assertTrue(any("missing" in issue for issue in missing_manifest_issues), missing_manifest_issues)
        self.assertTrue(
            any("public_source_map_sha256" in issue for issue in tampered_map_issues),
            tampered_map_issues,
        )
        self.assertTrue(
            any("source_artifact_sha256" in issue for issue in tampered_map_issues),
            tampered_map_issues,
        )
        self.assertTrue(
            any("semantic context 0 source anchor 0" in issue for issue in tampered_anchor_issues),
            tampered_anchor_issues,
        )
        self.assertTrue(
            any("private_source_map_sha256" in issue for issue in tampered_private_hash_issues),
            tampered_private_hash_issues,
        )
        self.assertTrue(
            any("retains a source path" in issue for issue in retained_path_issues),
            retained_path_issues,
        )
        self.assertTrue(
            any("requires the exact display-projection marker" in issue
                for issue in unmarked_issues),
            unmarked_issues,
        )

    def test_public_role_projection_requires_pinned_map_and_exact_private_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (
                private,
                candidate,
                source_commit,
                _candidate_commit,
                entry,
                public_blob,
                manifest_blob,
            ) = self._display_projection_fixture(root)
            graph_sha256 = "9" * 64
            pointer_path = (
                "papers/Fixture/audit/obligation_evidence/current_accepted_graph.json"
            )
            pack_path = (
                "papers/Fixture/audit/obligation_evidence/accepted_graphs/sha256/"
                f"{graph_sha256[:2]}/{graph_sha256}.json"
            )
            pointer_bytes = (
                json.dumps(
                    {"schema": 2, "graph_sha256": graph_sha256}, sort_keys=True
                )
                + "\n"
            ).encode("utf-8")
            pack_bytes = b'{"fixture":"accepted graph bytes"}\n'
            for path, raw in ((pointer_path, pointer_bytes), (pack_path, pack_bytes)):
                destination = private / path
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(raw)
            pinned_commit = self.commit(private, "pin selected accepted graph")
            private_blob = subprocess.run(
                ["git", "show", f"{pinned_commit}:{entry.path}"],
                cwd=private,
                check=True,
                stdout=subprocess.PIPE,
            ).stdout
            entry = replace(entry, source_commit=pinned_commit)
            private_map = json.loads(private_blob)
            accepted_roles = {
                "fixture_definition": _source_role_contract(
                    private_map["items"]["fixture_definition"]
                )
            }
            envelope = role_projection.build_public_source_role_projection_envelope(
                paper="Fixture",
                private_source_map_bytes=private_blob,
                public_source_map_bytes=public_blob,
                public_display_manifest_bytes=manifest_blob,
                accepted_graph_sha256=graph_sha256,
                accepted_role_sha256s_by_source_item=accepted_roles,
            )
            envelope_path = (
                candidate / "papers/Fixture/audit/public_source_role_projection.json"
            )
            envelope_path.write_bytes(
                role_projection.canonical_public_source_role_projection_bytes(envelope)
            )
            candidate_commit = self.commit(candidate, "add public role projection")
            accepted_material = (
                graph_sha256,
                accepted_roles,
                pointer_bytes,
                pack_bytes,
                pack_path,
            )

            with mock.patch.object(
                guard,
                "_accepted_source_role_material",
                return_value=accepted_material,
            ):
                issues = guard.public_source_role_projection_issues(
                    candidate,
                    candidate_commit,
                    [entry],
                    private_repo=private,
                    public_base_ref=None,
                )
                missing_provenance = guard.public_source_role_projection_issues(
                    candidate,
                    candidate_commit,
                    [],
                    private_repo=private,
                    public_base_ref=None,
                )
                wrong_graph_material = (
                    graph_sha256,
                    accepted_roles,
                    b"different pointer bytes\n",
                    pack_bytes,
                    pack_path,
                )
            with mock.patch.object(
                guard,
                "_accepted_source_role_material",
                return_value=wrong_graph_material,
            ):
                wrong_graph = guard.public_source_role_projection_issues(
                    candidate,
                    candidate_commit,
                    [entry],
                    private_repo=private,
                    public_base_ref=None,
                )
            with mock.patch.object(
                guard,
                "_accepted_source_role_material",
                return_value=accepted_material,
            ):
                unchanged = guard.public_source_role_projection_issues(
                    candidate,
                    candidate_commit,
                    [],
                    private_repo=private,
                    public_base_ref=candidate_commit,
                )

        self.assertEqual(issues, [])
        self.assertEqual(unchanged, [])
        self.assertTrue(
            any("private_projection allowlist provenance" in issue
                for issue in missing_provenance),
            missing_provenance,
        )
        self.assertTrue(
            any("differs from the pinned private source commit" in issue
                for issue in wrong_graph),
            wrong_graph,
        )

    def test_packet_pdf_and_tex_private_workflow_scan_is_committed_and_bounded(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            docs = repo / "papers" / "Fixture" / "docs"
            docs.mkdir(parents=True)
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"not a real PDF")
            (docs / "unrelated.pdf").write_bytes(b"not a real PDF")
            (docs / "HUMAN_REVIEW_PACKET.tex").write_text(
                r"\texttt{.audit\_source/Fixture.txt}" + "\n",
                encoding="utf-8",
            )
            candidate_commit = self.commit(repo, "packet fixture")

            with mock.patch.object(guard.shutil, "which", return_value=None):
                unavailable_issues = guard.human_review_packet_pdf_content_issues(
                    repo, candidate_commit
                )

            original_run = subprocess.run

            def fake_pdftotext(command, *args, **kwargs):
                if command and command[0] == "pdftotext":
                    Path(command[-1]).write_text(
                        "byte-pinned private source extraction\n"
                        "Source locator: .audit_source/Fixture.txt:1\n",
                        encoding="utf-8",
                    )
                    return subprocess.CompletedProcess(command, 0, "", "")
                return original_run(command, *args, **kwargs)

            with (
                mock.patch.object(guard.shutil, "which", return_value="/usr/bin/pdftotext"),
                mock.patch.object(guard.subprocess, "run", side_effect=fake_pdftotext),
            ):
                pdf_issues = guard.human_review_packet_pdf_content_issues(
                    repo, candidate_commit
                )
            tex_issues = guard.public_artifact_content_issues(repo, candidate_commit)

        self.assertTrue(any("pdftotext is unavailable" in issue for issue in unavailable_issues), unavailable_issues)
        self.assertTrue(any("private source-extraction" in issue for issue in pdf_issues), pdf_issues)
        self.assertTrue(any("private audit-source" in issue for issue in pdf_issues), pdf_issues)
        self.assertTrue(any("private workflow reference" in issue for issue in pdf_issues), pdf_issues)
        self.assertGreaterEqual(len(pdf_issues), 3, pdf_issues)
        self.assertTrue(any("private TeX audit-source" in issue for issue in tex_issues), tex_issues)

    def test_public_pdf_scan_covers_non_packet_documents(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            docs = repo / "docs"
            docs.mkdir()
            (docs / "OVERVIEW.pdf").write_bytes(b"not a real PDF")
            candidate_commit = self.commit(repo, "public PDF fixture")

            original_run = subprocess.run

            def fake_pdftotext(command, *args, **kwargs):
                if command and command[0] == "pdftotext":
                    Path(command[-1]).write_text(
                        "A private proof body is not publication material.\n",
                        encoding="utf-8",
                    )
                    return subprocess.CompletedProcess(command, 0, "", "")
                return original_run(command, *args, **kwargs)

            with (
                mock.patch.object(guard.shutil, "which", return_value="/usr/bin/pdftotext"),
                mock.patch.object(guard.subprocess, "run", side_effect=fake_pdftotext),
            ):
                issues = guard.human_review_packet_pdf_content_issues(
                    repo, candidate_commit
                )

        self.assertTrue(any("docs/OVERVIEW.pdf" in issue for issue in issues), issues)
        self.assertTrue(any("private workflow reference" in issue for issue in issues), issues)

    def test_public_workflow_overview_pdf_allows_private_draft_guidance_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            overview = repo / "docs" / "FORMALIZATION_AUDIT_PROCEDURE_OVERVIEW.pdf"
            overview.parent.mkdir()
            overview.write_bytes(b"not a real PDF")
            candidate_commit = self.commit(repo, "workflow overview")

            original_run = subprocess.run

            def fake_pdftotext(command, *args, **kwargs):
                if command and command[0] == "pdftotext":
                    Path(command[-1]).write_text(
                        "A private by sorry body is temporary draft guidance.\n",
                        encoding="utf-8",
                    )
                    return subprocess.CompletedProcess(command, 0, "", "")
                return original_run(command, *args, **kwargs)

            with (
                mock.patch.object(guard.shutil, "which", return_value="/usr/bin/pdftotext"),
                mock.patch.object(guard.subprocess, "run", side_effect=fake_pdftotext),
            ):
                issues = guard.human_review_packet_pdf_content_issues(
                    repo, candidate_commit
                )

        self.assertFalse(issues, issues)

    def test_public_artifact_content_check_covers_root_docs_and_release_config(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            (repo / "README.md").write_text(
                "Use the private workflow before publishing.\n", encoding="utf-8"
            )
            config = repo / "config"
            config.mkdir()
            (config / "release.json").write_text(
                json.dumps({"note": "private repository context"}), encoding="utf-8"
            )
            candidate_commit = self.commit(repo, "reader-facing fixtures")
            issues = guard.public_artifact_content_issues(repo, candidate_commit)

        self.assertTrue(any(issue.startswith("README.md:") for issue in issues), issues)
        self.assertTrue(any(issue.startswith("config/release.json:") for issue in issues), issues)

    def test_private_projection_provenance_recomputes_exact_public_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            self.init_repo(private)
            self.init_repo(candidate)
            path = "papers/Fixture/audit/paper_statement_map.json"
            private_path = private / path
            private_path.parent.mkdir(parents=True)
            private_blob = json.dumps(
                {
                    "source_version": "arXiv; byte-pinned private text extraction",
                    "source_artifact_path": ".audit_source/Fixture.txt",
                    "source_artifact_sha256": "a" * 64,
                }
            ).encode("utf-8")
            private_path.write_bytes(private_blob)
            source_commit = self.commit(private, "private source")
            candidate_path = candidate / path
            candidate_path.parent.mkdir(parents=True)
            projected_blob = guard.project_bytes(path, private_blob)
            candidate_path.write_bytes(projected_blob)
            candidate_commit = self.commit(candidate, "candidate projection")
            entry = guard.AllowlistEntry(
                path=path,
                kind="file",
                provenance="private_projection",
                source_commit=source_commit,
                reason="public projection removes private audit provisioning",
                generator=guard.PUBLIC_PROJECTION_GENERATOR,
                private_source_blob_sha256=guard._sha256_bytes(private_blob),
                candidate_blob_sha256=guard._sha256_bytes(projected_blob),
            )
            change = guard.CandidateChange("A", path)

            issues = guard.source_provenance_issues(
                candidate, private, candidate_commit, [change], [entry]
            )
            wrong_entry = guard.AllowlistEntry(
                **{**entry.__dict__, "candidate_blob_sha256": "f" * 64}
            )
            wrong_digest_issues = guard.source_provenance_issues(
                candidate, private, candidate_commit, [change], [wrong_entry]
            )
            candidate_path.write_text('{"unreviewed":true}\n', encoding="utf-8")
            changed_commit = self.commit(candidate, "tampered projection")
            tamper_issues = guard.source_provenance_issues(
                candidate, private, changed_commit, [change], [entry]
            )

        self.assertEqual(issues, [])
        self.assertTrue(
            any("candidate_blob_sha256" in issue for issue in wrong_digest_issues),
            wrong_digest_issues,
        )
        self.assertTrue(
            any("trusted public projection" in issue for issue in tamper_issues),
            tamper_issues,
        )

    def test_changed_corrected_target_projection_requires_private_projection_provenance(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            self.init_repo(private)
            self.init_repo(candidate)
            path = "papers/Fixture/audit/paper_statement_map.json"
            private_path = private / path
            private_path.parent.mkdir(parents=True)
            private_blob = json.dumps(
                {
                    "items": {
                        "claim": {
                            "coverage_status": "corrected_source_statement",
                            "corrected_target": _private_corrected_target(),
                        }
                    }
                }
            ).encode("utf-8")
            private_path.write_bytes(private_blob)
            source_commit = self.commit(private, "private corrected target")
            public_blob = guard.project_bytes(path, private_blob)
            candidate_path = candidate / path
            candidate_path.parent.mkdir(parents=True)
            candidate_path.write_bytes(public_blob)
            candidate_commit = self.commit(candidate, "public corrected target projection")
            change = guard.CandidateChange("A", path)
            projection_entry = guard.AllowlistEntry(
                path=path,
                kind="file",
                provenance="private_projection",
                source_commit=source_commit,
                reason="withhold private approval material",
                generator=guard.PUBLIC_PROJECTION_GENERATOR,
                private_source_blob_sha256=guard._sha256_bytes(private_blob),
                candidate_blob_sha256=guard._sha256_bytes(public_blob),
            )
            private_blob_entry = guard.AllowlistEntry(
                path=path,
                kind="file",
                provenance="private_blob",
                source_commit=source_commit,
                reason="incorrect raw transport",
                generator=None,
            )

            valid = guard.source_provenance_issues(
                candidate,
                private,
                candidate_commit,
                [change],
                [projection_entry],
            )
            missing = guard.source_provenance_issues(
                candidate, private, candidate_commit, [change], []
            )
            wrong_mode = guard.source_provenance_issues(
                candidate,
                private,
                candidate_commit,
                [change],
                [private_blob_entry],
            )

        self.assertEqual(valid, [])
        self.assertTrue(
            any("requires private_projection provenance" in issue for issue in missing),
            missing,
        )
        self.assertTrue(
            any("requires private_projection provenance" in issue for issue in wrong_mode),
            wrong_mode,
        )

    def test_private_projection_allowlist_requires_exact_projection_receipts(self) -> None:
        entry = {
            "path": "papers/Fixture/audit/paper_statement_map.json",
            "kind": "file",
            "provenance": "private_projection",
            "source_commit": "1" * 40,
            "generator": guard.PUBLIC_PROJECTION_GENERATOR,
            "private_source_blob_sha256": "2" * 64,
            "candidate_blob_sha256": "3" * 64,
            "reason": "reviewed public projection",
            "public_safety_reviewed": True,
        }
        parsed = guard.parse_allowlist(
            json.dumps({"schema": 1, "entries": [entry]}).encode(), source="fixture"
        )
        self.assertEqual(parsed[0].private_source_blob_sha256, "2" * 64)
        for field, value, expected in (
            ("generator", "python3 unsafe.py", "must declare generator"),
            ("private_source_blob_sha256", None, "private_source_blob_sha256"),
            ("candidate_blob_sha256", "2" * 64, "distinct"),
            ("public_base_blob_sha256", "4" * 64, "cannot declare"),
        ):
            with self.subTest(field=field, value=value):
                candidate = dict(entry)
                if value is None:
                    candidate.pop(field)
                else:
                    candidate[field] = value
                with self.assertRaisesRegex(ValueError, expected):
                    guard.parse_allowlist(
                        json.dumps({"schema": 1, "entries": [candidate]}).encode(),
                        source="fixture",
                    )

    def test_public_artifact_content_check_rejects_workflow_not_source_excerpt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            map_path = repo / "papers" / "Fixture" / "audit" / "paper_statement_map.json"
            map_path.parent.mkdir(parents=True)
            map_path.write_text(
                json.dumps(
                    {
                        "source_version": "private source extraction",
                        "items": {
                            "claim": {
                                "source_anchor": {
                                    "path": "source.txt",
                                    "line_start": 1,
                                    "line_end": 1,
                                    "quoted_text": "source excerpt about an allocation condition",
                                    "quoted_text_sha256": hashlib.sha256(
                                        b"source excerpt about an allocation condition"
                                    ).hexdigest(),
                                },
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(
                repo,
                commit,
                [guard.CandidateChange("A", "papers/Fixture/audit/paper_statement_map.json")],
            )

        self.assertTrue(any("private source-extraction" in issue for issue in issues), issues)
        self.assertFalse(any("quoted_text" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_local_path_in_bound_source_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            map_path = repo / "papers" / "Fixture" / "audit" / "paper_statement_map.json"
            map_path.parent.mkdir(parents=True)
            quote = "/home/nkgarg/secret-private-workflow"
            map_path.write_text(
                json.dumps(
                    {
                        "items": {
                            "claim": {
                                "source_anchor": {
                                    "path": "source.txt",
                                    "line_start": 1,
                                    "line_end": 1,
                                    "quoted_text": quote,
                                    "quoted_text_sha256": hashlib.sha256(
                                        quote.encode("utf-8")
                                    ).hexdigest(),
                                }
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("local /tmp or /home path" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_bound_quote_outside_source_record(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            audit = repo / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            quote = "/home/nkgarg/secret-private-workflow"
            (audit / "record.json").write_text(
                json.dumps(
                    {
                        "quoted_text": quote,
                        "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
                        "publication_locator": "https://arxiv.org/abs/1234.5678",
                        "line_start": 1,
                        "line_end": 1,
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("local filesystem path" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_private_workflow_reference(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            site = repo / "site"
            site.mkdir()
            (site / "index.html").write_text(
                "New paper formalizations should start in a private workflow.\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(
                repo,
                commit,
                [guard.CandidateChange("A", "site/index.html")],
            )

        self.assertTrue(any("private workflow reference" in issue for issue in issues), issues)

    def test_public_artifact_content_check_allows_exact_landing_page_guidance(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            site = repo / "site"
            site.mkdir()
            (site / "index.html").write_text(
                "New paper formalizations should start in a private workflow and be\n"
                "            proposed to enter the library through a pull request when ready.\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertEqual(issues, [])

    def test_public_artifact_content_check_rejects_nested_quote_object_bypass(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            map_path = repo / "papers" / "Fixture" / "audit" / "paper_statement_map.json"
            map_path.parent.mkdir(parents=True)
            map_path.write_text(
                json.dumps({"quoted_text": {"hidden": "/tmp/private.txt"}}),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("hidden" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_unbound_scalar_quote_bypass(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            map_path = repo / "papers" / "Fixture" / "audit" / "paper_statement_map.json"
            map_path.parent.mkdir(parents=True)
            map_path.write_text(
                json.dumps({"quoted_text": "/tmp/private-record.txt"}),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("quoted_text" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_private_url_before_masking(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            audit = repo / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "reference_url": (
                            "https://github.com/nikhgarg/EconCSLib-private/tree/main/tmp/secret"
                        )
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("private repository or artifact URL" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_paper_named_local_transcript(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            status = repo / "papers" / "Fixture" / "status.json"
            status.parent.mkdir(parents=True)
            status.write_text(
                json.dumps(
                    {"artifacts": {"source_text": "papers/Fixture/Fixture.txt"}}
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("non-public source transcript locator" in issue for issue in issues), issues)

    def test_public_artifact_content_check_allows_internal_transcript_name_in_audit_sidecar(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            sidecar = repo / "papers" / "Fixture" / "audit" / "statement_match_llm.json"
            sidecar.parent.mkdir(parents=True)
            sidecar.write_text(
                json.dumps({"source_location": "sources/Fixture.txt:12-15"}),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertEqual(issues, [])

    def test_public_artifact_content_check_rejects_percent_encoded_private_url(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            docs = repo / "docs"
            docs.mkdir()
            (docs / "guide.md").write_text(
                "https://github.com/nikhgarg/EconCSLib%2Dprivate/tree/main\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("private repository or artifact URL" in issue for issue in issues), issues)

    def test_public_artifact_content_check_rejects_html_entity_private_url(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            site = repo / "site"
            site.mkdir()
            (site / "index.html").write_text(
                "https://github.com/nikhgarg/EconCSLib&#45;private/tree/main\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("private repository or artifact URL" in issue for issue in issues), issues)

    def test_session_insights_path_allowlist_keeps_general_skill_and_rejects_private_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            skill = repo / "skills/econcs-session-insights/SKILL.md"
            skill.parent.mkdir(parents=True)
            skill.write_text("Read ~/.codex/history.jsonl without committing it.\n", encoding="utf-8")
            commit = self.commit(repo, "general session-insights skill")
            self.assertFalse(guard.session_insights_path_issues(repo, commit))

            private_paths = [
                "skills/econcs-session-insights/references/raw-session.jsonl",
                "skills/econcs-session-insights/references/user-feedback-course-corrections.md",
                "wiki/examples/sanitized-example.md",
                "wiki/patterns/private-provenance.md",
                "wiki/evolution-log.md",
            ]
            for path in private_paths:
                extra = repo / path
                extra.parent.mkdir(parents=True, exist_ok=True)
                extra.write_text("benign-looking maintenance evidence\n", encoding="utf-8")
            self.commit(repo, "private maintenance records")
            (repo / "README.md").write_text("A later public edit.\n", encoding="utf-8")
            commit = self.commit(repo, "inherited records are still rejected")
            issues = guard.session_insights_path_issues(repo, commit)

        self.assertEqual(
            issues,
            [
                "unapproved session-insights artifact in public candidate: " + path
                for path in sorted(private_paths)
            ],
        )

    def test_public_artifact_content_check_scans_skills_but_exempts_approved_workflow_guides(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            skill = repo / "skills" / "example" / "SKILL.md"
            skill.parent.mkdir(parents=True)
            skill.write_text("Use EconCSLib-private for this workflow.\n", encoding="utf-8")
            ledger = (
                repo
                / "skills/econcs-session-insights/references/user-feedback-course-corrections.md"
            )
            ledger.parent.mkdir(parents=True)
            ledger.write_text("User history came from ~/.codex/history.jsonl.\n", encoding="utf-8")
            session_skill = repo / "skills/econcs-session-insights/SKILL.md"
            session_skill.write_text(
                "Read ~/.codex/history.jsonl without committing session data.\n",
                encoding="utf-8",
            )
            handbook = repo / "skills/econcs-formalizer/references/formalization-handbook.md"
            handbook.parent.mkdir(parents=True)
            handbook.write_text(
                "Use a local source cache and a private handoff when useful.\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "skills")
            issues = guard.public_artifact_content_issues(repo, commit)
            private_record_issues = guard.session_insights_path_issues(repo, commit)

        self.assertTrue(any("skills/example/SKILL.md" in issue for issue in issues), issues)
        self.assertTrue(
            any("user-feedback-course-corrections" in issue for issue in private_record_issues),
            private_record_issues,
        )
        self.assertFalse(any("econcs-session-insights/SKILL.md" in issue for issue in issues), issues)
        self.assertFalse(any("formalization-handbook.md" in issue for issue in issues), issues)

    def test_public_artifact_content_check_catches_inherited_public_blob(self) -> None:
        """A clean candidate diff cannot conceal a historical local-path leak."""

        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            audit = repo / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (audit / "source_record_audit.json").write_text(
                json.dumps({"paper_dir": "/tmp/old-candidate/papers/Fixture"}),
                encoding="utf-8",
            )
            base = self.commit(repo, "base with inherited receipt")
            (repo / "README.md").write_text("unrelated candidate change\n", encoding="utf-8")
            candidate = self.commit(repo, "candidate")

            issues = guard.public_artifact_content_issues(
                repo,
                candidate,
                [guard.CandidateChange("A", "README.md")],
            )

        self.assertNotEqual(base, candidate)
        self.assertTrue(any("source_record_audit.json" in issue for issue in issues), issues)

    def test_public_artifact_content_check_allows_ignore_rule_but_rejects_private_locators(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / ".gitignore").write_text(
                ".audit_source/\nsource/\nsources/\nsource.txt\n",
                encoding="utf-8",
            )
            docs = repo / "docs"
            docs.mkdir()
            (docs / "workflow.md").write_text(
                "EconCSLib-private stores sources/2101.05853.txt in source.pdf locally.\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")

            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertFalse(any(".gitignore" in issue for issue in issues), issues)
        self.assertTrue(any("private repository identity" in issue for issue in issues), issues)
        self.assertTrue(any("non-public source transcript" in issue for issue in issues), issues)
        self.assertTrue(any("non-public source artifact" in issue for issue in issues), issues)

    def test_public_artifact_content_check_allows_public_url_containing_home_prefix(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            audit = repo / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://homes.cs.washington.edu/~karlin/papers/auctions-journal.pdf"
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertFalse(issues, issues)

    def test_public_artifact_content_check_allows_only_hash_pinned_arxiv_source_tex(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            source = b"% official arXiv TeX may mention /tmp literally\n"
            paper = repo / "papers" / "Fixture"
            (paper / "source").mkdir(parents=True)
            (paper / "source" / "main.tex").write_bytes(source)
            audit = paper / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://arxiv.org/abs/2601.00001",
                        "source_artifact_sha256": guard._sha256_bytes(source),
                    }
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertFalse(issues, issues)

    def test_public_artifact_content_check_allows_documented_approved_source_tex_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            source = b"% official arXiv TeX\n"
            paper = repo / "papers" / "Fixture"
            (paper / "source").mkdir(parents=True)
            (paper / "source" / "main.tex").write_bytes(source)
            audit = paper / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://arxiv.org/abs/2601.00001",
                        "source_artifact_sha256": guard._sha256_bytes(source),
                    }
                ),
                encoding="utf-8",
            )
            docs = repo / "docs"
            docs.mkdir()
            (docs / "source.md").write_text(
                "Read papers/Fixture/source/main.tex or papers/<Paper>/source/<file>.tex.\n",
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertFalse(issues, issues)

    def test_public_artifact_content_check_rejects_unpinned_source_tex(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "source").mkdir(parents=True)
            (paper / "source" / "main.tex").write_text("official source\n", encoding="utf-8")
            audit = paper / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {"source_url": "https://arxiv.org/abs/2601.00001", "source_artifact_sha256": "0" * 64}
                ),
                encoding="utf-8",
            )
            commit = self.commit(repo, "candidate")
            issues = guard.public_artifact_content_issues(repo, commit)

        self.assertTrue(any("hash does not match" in issue for issue in issues), issues)

    def test_public_base_edit_provenance_pins_base_and_candidate_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            path = repo / "lakefile.toml"
            base_blob = b"name = \"base\"\n"
            candidate_blob = b"name = \"candidate\"\n"
            path.write_bytes(base_blob)
            base = self.commit(repo, "base")
            path.write_bytes(candidate_blob)
            candidate = self.commit(repo, "candidate")
            entry = guard.AllowlistEntry(
                "lakefile.toml",
                "file",
                "public_base_edit",
                None,
                "reviewed public-only edit",
                None,
                guard._sha256_bytes(base_blob),
                guard._sha256_bytes(candidate_blob),
            )
            change = guard.CandidateChange("M", "lakefile.toml")

            issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [change],
                [entry],
                public_base_ref=base,
            )
            wrong_base = guard.AllowlistEntry(
                **{**entry.__dict__, "public_base_blob_sha256": "f" * 64}
            )
            wrong_candidate = guard.AllowlistEntry(
                **{**entry.__dict__, "candidate_blob_sha256": "e" * 64}
            )
            base_issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [change],
                [wrong_base],
                public_base_ref=base,
            )
            candidate_issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [change],
                [wrong_candidate],
                public_base_ref=base,
            )

        self.assertEqual(issues, [])
        self.assertTrue(
            any("public_base_blob_sha256" in issue for issue in base_issues),
            base_issues,
        )
        self.assertTrue(
            any("candidate_blob_sha256" in issue for issue in candidate_issues),
            candidate_issues,
        )

    def test_public_base_addition_pins_absence_and_candidate_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            (repo / "README.md").write_text("base\n", encoding="utf-8")
            base = self.commit(repo, "base")
            added_blob = b'{"authority":"public-manifest"}\n'
            path = repo / "config" / "formalization_audit_protocol.json"
            path.parent.mkdir()
            path.write_bytes(added_blob)
            candidate = self.commit(repo, "candidate")
            entry = guard.AllowlistEntry(
                path="config/formalization_audit_protocol.json",
                kind="file",
                provenance="public_base_addition",
                source_commit=None,
                reason="reviewed public-only trust configuration",
                generator=None,
                candidate_blob_sha256=guard._sha256_bytes(added_blob),
            )
            change = guard.CandidateChange(
                "A", "config/formalization_audit_protocol.json"
            )

            issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [change],
                [entry],
                public_base_ref=base,
            )
            wrong_digest = guard.AllowlistEntry(
                **{**entry.__dict__, "candidate_blob_sha256": "e" * 64}
            )
            digest_issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [change],
                [wrong_digest],
                public_base_ref=base,
            )
            status_issues = guard.source_provenance_issues(
                repo,
                repo,
                candidate,
                [guard.CandidateChange("M", change.path)],
                [entry],
                public_base_ref=base,
            )

        self.assertEqual(issues, [])
        self.assertTrue(
            any("candidate_blob_sha256" in issue for issue in digest_issues),
            digest_issues,
        )
        self.assertTrue(
            any("must be an addition" in issue for issue in status_issues),
            status_issues,
        )

    def test_public_base_addition_cannot_launder_an_exact_private_blob(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            candidate_repo = root / "candidate"
            private_repo = root / "private"
            self.init_repo(candidate_repo)
            self.init_repo(private_repo)

            (candidate_repo / "README.md").write_text("base\n", encoding="utf-8")
            public_base = self.commit(candidate_repo, "public base")
            path = "config/public-only.json"
            candidate_path = candidate_repo / path
            candidate_path.parent.mkdir()
            candidate_path.write_text('{"scope":"public"}\n', encoding="utf-8")
            candidate = self.commit(candidate_repo, "candidate")

            private_path = private_repo / path
            private_path.parent.mkdir()
            private_path.write_bytes(candidate_path.read_bytes())
            private_commit = self.commit(private_repo, "private source")
            private_entry = guard.AllowlistEntry(
                path="scripts/reviewed.py",
                kind="file",
                provenance="private_blob",
                source_commit=private_commit,
                reason="pins the reviewed private source commit",
                generator=None,
            )
            addition = guard.AllowlistEntry(
                path=path,
                kind="file",
                provenance="public_base_addition",
                source_commit=None,
                reason="claimed public-only addition",
                generator=None,
                candidate_blob_sha256=guard._sha256_bytes(
                    candidate_path.read_bytes()
                ),
            )

            issues = guard.source_provenance_issues(
                candidate_repo,
                private_repo,
                candidate,
                [guard.CandidateChange("A", path)],
                [addition, private_entry],
                public_base_ref=public_base,
            )

        self.assertTrue(
            any("use private_blob provenance" in issue for issue in issues),
            issues,
        )

    def test_public_base_edit_rejects_add_delete_and_mode_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)

            addition = root / "addition"
            self.init_repo(addition)
            (addition / "README.md").write_text("base\n", encoding="utf-8")
            addition_base = self.commit(addition, "base")
            added_blob = b"added\n"
            (addition / "new.txt").write_bytes(added_blob)
            addition_candidate = self.commit(addition, "candidate")
            addition_entry = guard.AllowlistEntry(
                "new.txt",
                "file",
                "public_base_edit",
                None,
                "invalid addition",
                None,
                "1" * 64,
                guard._sha256_bytes(added_blob),
            )
            addition_issues = guard.source_provenance_issues(
                addition,
                addition,
                addition_candidate,
                [guard.CandidateChange("A", "new.txt")],
                [addition_entry],
                public_base_ref=addition_base,
            )

            deletion = root / "deletion"
            self.init_repo(deletion)
            deleted_blob = b"deleted\n"
            (deletion / "old.txt").write_bytes(deleted_blob)
            deletion_base = self.commit(deletion, "base")
            (deletion / "old.txt").unlink()
            deletion_candidate = self.commit(deletion, "candidate")
            deletion_entry = guard.AllowlistEntry(
                "old.txt",
                "file",
                "public_base_edit",
                None,
                "invalid deletion",
                None,
                guard._sha256_bytes(deleted_blob),
                "2" * 64,
            )
            deletion_issues = guard.source_provenance_issues(
                deletion,
                deletion,
                deletion_candidate,
                [guard.CandidateChange("D", "old.txt")],
                [deletion_entry],
                public_base_ref=deletion_base,
            )

            mode_change = root / "mode-change"
            self.init_repo(mode_change)
            base_blob = b"base\n"
            candidate_blob = b"candidate\n"
            mode_path = mode_change / "script.sh"
            mode_path.write_bytes(base_blob)
            mode_base = self.commit(mode_change, "base")
            mode_path.write_bytes(candidate_blob)
            mode_path.chmod(0o755)
            mode_candidate = self.commit(mode_change, "candidate")
            mode_entry = guard.AllowlistEntry(
                "script.sh",
                "file",
                "public_base_edit",
                None,
                "invalid mode change",
                None,
                guard._sha256_bytes(base_blob),
                guard._sha256_bytes(candidate_blob),
            )
            mode_issues = guard.source_provenance_issues(
                mode_change,
                mode_change,
                mode_candidate,
                [guard.CandidateChange("M", "script.sh")],
                [mode_entry],
                public_base_ref=mode_base,
            )

        self.assertTrue(
            any("in-place modification" in issue for issue in addition_issues),
            addition_issues,
        )
        self.assertTrue(
            any("public_base_deletion" in issue for issue in deletion_issues),
            deletion_issues,
        )
        self.assertTrue(
            any("Git mode or object type" in issue for issue in mode_issues),
            mode_issues,
        )

    def test_candidate_history_requires_one_commit_directly_on_exact_base(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            (repo / "README.md").write_text("base\n", encoding="utf-8")
            base = self.commit(repo, "base")
            (repo / "reviewed.txt").write_text("reviewed\n", encoding="utf-8")
            candidate = self.commit(repo, "release")

            history, issues = guard.candidate_history(repo, base, candidate)

        self.assertEqual(issues, [])
        self.assertEqual(len(history), 1)
        self.assertEqual(history[0].parent, base)

    def test_candidate_history_rejects_add_then_delete_intermediate_blob(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            (repo / "README.md").write_text("base\n", encoding="utf-8")
            base = self.commit(repo, "base")
            (repo / "private-secret.txt").write_text("secret\n", encoding="utf-8")
            self.commit(repo, "intermediate private blob")
            (repo / "private-secret.txt").unlink()
            candidate = self.commit(repo, "hide intermediate blob")

            _history, issues = guard.candidate_history(repo, base, candidate)

        self.assertTrue(any("exactly one squashed commit" in issue for issue in issues), issues)

    def test_private_blob_provenance_compares_git_mode_as_well_as_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            for repo in (private, candidate):
                self.init_repo(repo)
                (repo / "shared").write_text("target", encoding="utf-8")
                self.commit(repo, "base")
            source_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=private,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.strip()
            (candidate / "shared").unlink()
            (candidate / "shared").symlink_to("target")
            candidate_commit = self.commit(candidate, "change file into symlink")
            entry = guard.AllowlistEntry(
                "shared", "file", "private_blob", source_commit, "reviewed", None
            )

            issues = guard.source_provenance_issues(
                candidate,
                private,
                candidate_commit,
                [guard.CandidateChange("T", "shared")],
                [entry],
            )

        self.assertTrue(any("Git mode/type differs" in issue for issue in issues), issues)

    def test_candidate_rejects_symlink_even_when_private_mode_matches(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            candidate = root / "candidate"
            private = root / "private"
            for repo in (candidate, private):
                self.init_repo(repo)
                (repo / "target").write_text("public bytes\n", encoding="utf-8")
                (repo / "shared").symlink_to("target")
                self.commit(repo, "matching symlink")
            private_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=private,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.strip()
            candidate_commit = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=candidate,
                check=True,
                text=True,
                capture_output=True,
            ).stdout.strip()
            changes = [guard.CandidateChange("A", "shared")]
            entries = [
                guard.AllowlistEntry(
                    "shared", "file", "private_blob", private_commit,
                    "reviewed fixture", None,
                )
            ]

            self.assertEqual(
                guard.source_provenance_issues(
                    candidate,
                    private,
                    candidate_commit,
                    changes,
                    entries,
                ),
                [],
            )
            issues = guard.candidate_tree_entry_issues(
                candidate, candidate_commit, changes
            )

        self.assertTrue(any("regular file blob" in issue for issue in issues), issues)
        self.assertFalse(any("candidate blob differs" in issue for issue in issues), issues)

    def test_unused_allowlist_entry_is_rejected(self) -> None:
        used = guard.AllowlistEntry(
            "scripts/used.py", "file", "private_blob", "1" * 40, "used", None
        )
        unused = guard.AllowlistEntry(
            "scripts/unused.py", "file", "private_blob", "1" * 40, "unused", None
        )
        self.assertEqual(
            guard.unused_allowlist_issues([used, unused], {used}),
            ["allowlist entry is unused by candidate history: scripts/unused.py"],
        )

    def test_candidate_owned_allowlist_is_rejected_before_it_is_read(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            repo.mkdir()
            issues = guard.run_guard(
                repo,
                allowlist_path=repo / "candidate-controlled.json",
            )
        self.assertEqual(len(issues), 1)
        self.assertIn("outside the candidate", issues[0])

    def test_non_repository_private_path_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            candidate = root / "candidate"
            self.init_repo(candidate)
            allowlist = root / "allowlist.json"
            allowlist.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "entries": [
                            {
                                "path": "reviewed.txt",
                                "kind": "file",
                                "provenance": "private_blob",
                                "source_commit": "1" * 40,
                                "reason": "reviewed",
                                "public_safety_reviewed": True,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            approval = root / "reviewer" / "approval.json"
            self.write_approval(
                approval,
                candidate_commit="2" * 40,
                public_base_commit="3" * 40,
                allowlist=allowlist,
                private_source_commits=["1" * 40],
            )
            with (
                mock.patch.object(guard, "ROOT", root / "not-a-repository"),
                mock.patch.object(guard, "REVIEWER_APPROVAL_PATH", approval),
            ):
                issues = guard.run_guard(candidate, allowlist_path=allowlist)
        self.assertEqual(len(issues), 1)
        self.assertIn("canonical private ROOT is not a Git repository", issues[0])

    def test_canonical_remote_match_does_not_accept_lookalike_host(self) -> None:
        self.assertIsNotNone(
            guard.PUBLIC_REMOTE_RE.fullmatch(
                "https://github.com/nikhgarg/EconCSLib.git"
            )
        )
        self.assertIsNone(
            guard.PUBLIC_REMOTE_RE.fullmatch(
                "https://evilgithub.com/nikhgarg/EconCSLib.git"
            )
        )

    def test_renamed_public_repository_is_still_canonical(self) -> None:
        self.assertIsNotNone(guard.PUBLIC_REMOTE_RE.fullmatch("https://github.com/nikhgarg/AppliedModelingLib.git"))
        self.assertIsNone(guard.PUBLIC_REMOTE_RE.fullmatch("https://github.com/attacker/AppliedModelingLib.git"))

    def test_canonical_remote_checks_fetch_and_every_push_url(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            (repo / "README.md").write_text("base\n", encoding="utf-8")
            base = self.commit(repo, "base")
            self.configure_origin(
                repo, "https://github.com/nikhgarg/EconCSLib.git", base
            )

            self.assertEqual(
                guard.canonical_remote_issues(
                    repo,
                    remote="origin",
                    expected=guard.PUBLIC_REMOTE_RE,
                    label="public",
                ),
                [],
            )
            subprocess.run(
                [
                    "git",
                    "remote",
                    "set-url",
                    "--add",
                    "--push",
                    "origin",
                    "https://github.com/attacker/EconCSLib.git",
                ],
                cwd=repo,
                check=True,
            )
            issues = guard.canonical_remote_issues(
                repo,
                remote="origin",
                expected=guard.PUBLIC_REMOTE_RE,
                label="public",
            )

        self.assertTrue(any("push" in issue for issue in issues), issues)
        self.assertFalse(any("fetch" in issue for issue in issues), issues)

    def test_private_source_commit_must_be_reachable_from_origin_main(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "private"
            self.init_repo(repo)
            (repo / "reviewed.txt").write_text("version one\n", encoding="utf-8")
            main_commit = self.commit(repo, "main source")
            self.configure_origin(
                repo, "https://github.com/nikhgarg/EconCSLib-private.git", main_commit
            )
            (repo / "reviewed.txt").write_text("unpublished\n", encoding="utf-8")
            unpublished_commit = self.commit(repo, "unpublished source")
            entry = guard.AllowlistEntry(
                "reviewed.txt",
                "file",
                "private_blob",
                unpublished_commit,
                "reviewed fixture",
                None,
            )

            issues = guard.private_source_commit_issues(repo, [entry])

        self.assertTrue(any("not reachable" in issue for issue in issues), issues)

    def test_candidate_and_private_repository_cannot_share_git_storage(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "shared"
            self.init_repo(repo)
            (repo / "README.md").write_text("base\n", encoding="utf-8")
            self.commit(repo, "base")

            issues = guard.shared_git_storage_issues(repo, repo)

        self.assertEqual(len(issues), 2, issues)
        self.assertTrue(any("common directory" in issue for issue in issues), issues)
        self.assertTrue(any("object directory" in issue for issue in issues), issues)

    def test_candidate_cannot_borrow_private_objects_through_alternates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            self.init_repo(private)
            (private / "README.md").write_text("private\n", encoding="utf-8")
            self.commit(private, "source")
            subprocess.run(
                ["git", "clone", "-q", "--shared", str(private), str(candidate)],
                cwd=root,
                check=True,
            )

            issues = guard.shared_git_storage_issues(candidate, private)

        self.assertTrue(any("alternates" in issue for issue in issues), issues)

    def test_reviewer_approval_rejects_symlink(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            target = root / "target.json"
            target.write_text("{}", encoding="utf-8")
            approval = root / "approval.json"
            approval.symlink_to(target)

            with self.assertRaisesRegex(ValueError, "reviewer approval"):
                guard.load_release_approval(approval)

    def test_cli_does_not_expose_trust_anchor_overrides(self) -> None:
        for forbidden in (
            "--approval",
            "--base-ref",
            "--candidate-ref",
            "--private-repo",
            "--public-remote",
            "--branch-prefix",
        ):
            with self.subTest(forbidden=forbidden), mock.patch.object(
                sys,
                "argv",
                [
                    "public_release_candidate_guard.py",
                    "--repo",
                    "/tmp/candidate",
                    "--allowlist",
                    "/tmp/allowlist.json",
                    forbidden,
                    "attacker-value",
                ],
            ), contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                guard.main()

    def test_run_guard_allows_pr_without_approval_and_checks_authoritative_pins(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            self.init_repo(private)
            self.init_repo(candidate)
            (candidate / "lakefile.toml").write_text('name = "Fixture"\n', encoding="utf-8")

            (private / "reviewed.txt").write_text("reviewed\n", encoding="utf-8")
            source_commit = self.commit(private, "private source")
            self.configure_origin(
                private,
                "https://github.com/nikhgarg/EconCSLib-private.git",
                source_commit,
            )

            (candidate / "README.md").write_text("public base\n", encoding="utf-8")
            public_base = self.commit(candidate, "public base")
            self.configure_origin(
                candidate,
                "https://github.com/nikhgarg/EconCSLib.git",
                public_base,
            )
            subprocess.run(
                ["git", "switch", "-qc", "release/reviewed"],
                cwd=candidate,
                check=True,
            )
            (candidate / "reviewed.txt").write_text("reviewed\n", encoding="utf-8")
            candidate_commit = self.commit(candidate, "public release")

            allowlist = root / "allowlist.json"
            allowlist.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "entries": [
                            {
                                "path": "reviewed.txt",
                                "kind": "file",
                                "provenance": "private_blob",
                                "source_commit": source_commit,
                                "reason": "reviewed fixture export",
                                "public_safety_reviewed": True,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            approval = root / "reviewer" / "approval.json"
            self.write_approval(
                approval,
                candidate_commit=candidate_commit,
                public_base_commit=public_base,
                allowlist=allowlist,
                private_source_commits=[source_commit],
            )

            with (
                mock.patch.object(guard, "ROOT", private),
                mock.patch.object(guard, "REVIEWER_APPROVAL_PATH", approval),
                mock.patch.object(
                    guard, "generated_status_freshness_issues", return_value=[]
                ),
            ):
                with mock.patch.object(
                    guard,
                    "load_release_approval",
                    side_effect=AssertionError("PR validation read reviewer approval"),
                ):
                    issues = guard.run_guard(candidate, allowlist_path=allowlist)
                authoritative_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                with mock.patch.object(
                    guard,
                    "candidate_public_artifact_policy_issues",
                    return_value=["complete-tree policy sentinel"],
                ):
                    complete_tree_policy_issues = guard.run_guard(
                        candidate, allowlist_path=allowlist
                    )
                self.write_approval(
                    approval,
                    candidate_commit="f" * 40,
                    public_base_commit=public_base,
                    allowlist=allowlist,
                    private_source_commits=[source_commit],
                )
                candidate_pin_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                self.write_approval(
                    approval,
                    candidate_commit=candidate_commit,
                    public_base_commit="e" * 40,
                    allowlist=allowlist,
                    private_source_commits=[source_commit],
                )
                base_pin_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                self.write_approval(
                    approval,
                    candidate_commit=candidate_commit,
                    public_base_commit=public_base,
                    allowlist=allowlist,
                    private_source_commits=[],
                )
                source_pin_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                self.write_approval(
                    approval,
                    candidate_commit=candidate_commit,
                    public_base_commit=public_base,
                    allowlist=allowlist,
                    private_source_commits=[source_commit],
                    guard_sha256="d" * 64,
                )
                guard_pin_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                self.write_approval(
                    approval,
                    candidate_commit=candidate_commit,
                    public_base_commit=public_base,
                    allowlist=allowlist,
                    private_source_commits=[source_commit],
                    trusted_tooling_sha256="c" * 64,
                )
                tooling_pin_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )
                self.write_approval(
                    approval,
                    candidate_commit=candidate_commit,
                    public_base_commit=public_base,
                    allowlist=allowlist,
                    private_source_commits=[source_commit],
                )
                allowlist.write_bytes(allowlist.read_bytes() + b"\n")
                changed_allowlist_issues = guard.run_guard(
                    candidate, allowlist_path=allowlist, authoritative=True
                )

        self.assertEqual(issues, [])
        self.assertEqual(authoritative_issues, [])
        self.assertIn("complete-tree policy sentinel", complete_tree_policy_issues)
        self.assertTrue(
            any("candidate HEAD" in issue for issue in candidate_pin_issues),
            candidate_pin_issues,
        )
        self.assertTrue(
            any("public base" in issue for issue in base_pin_issues),
            base_pin_issues,
        )
        self.assertTrue(
            any("private source commits" in issue for issue in source_pin_issues),
            source_pin_issues,
        )
        self.assertTrue(
            any("release guard" in issue for issue in guard_pin_issues),
            guard_pin_issues,
        )
        self.assertTrue(
            any("trusted tooling bundle" in issue for issue in tooling_pin_issues),
            tooling_pin_issues,
        )
        self.assertTrue(
            any("allowlist bytes" in issue for issue in changed_allowlist_issues),
            changed_allowlist_issues,
        )

    def test_run_guard_accepts_reviewer_pinned_public_base_edit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            private = root / "private"
            candidate = root / "candidate"
            self.init_repo(private)
            self.init_repo(candidate)

            (private / "README.md").write_text("private\n", encoding="utf-8")
            private_commit = self.commit(private, "private base")
            self.configure_origin(
                private,
                "https://github.com/nikhgarg/EconCSLib-private.git",
                private_commit,
            )

            base_blob = b"name = \"public-base\"\n"
            candidate_blob = b"name = \"reviewed-candidate\"\n"
            (candidate / "lakefile.toml").write_bytes(base_blob)
            public_base = self.commit(candidate, "public base")
            self.configure_origin(
                candidate,
                "https://github.com/nikhgarg/EconCSLib.git",
                public_base,
            )
            subprocess.run(
                ["git", "switch", "-qc", "release/reviewed-base-edit"],
                cwd=candidate,
                check=True,
            )
            (candidate / "lakefile.toml").write_bytes(candidate_blob)
            candidate_commit = self.commit(candidate, "public release")

            allowlist = root / "allowlist.json"
            allowlist.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "entries": [
                            {
                                "path": "lakefile.toml",
                                "kind": "file",
                                "provenance": "public_base_edit",
                                "public_base_blob_sha256": guard._sha256_bytes(
                                    base_blob
                                ),
                                "candidate_blob_sha256": guard._sha256_bytes(
                                    candidate_blob
                                ),
                                "reason": "reviewed public-only metadata edit",
                                "public_safety_reviewed": True,
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            approval = root / "reviewer" / "approval.json"
            self.write_approval(
                approval,
                candidate_commit=candidate_commit,
                public_base_commit=public_base,
                allowlist=allowlist,
                private_source_commits=[],
            )

            with (
                mock.patch.object(guard, "ROOT", private),
                mock.patch.object(guard, "REVIEWER_APPROVAL_PATH", approval),
                mock.patch.object(
                    guard, "generated_status_freshness_issues", return_value=[]
                ),
            ):
                issues = guard.run_guard(candidate, allowlist_path=allowlist)

        self.assertEqual(issues, [])

    def test_source_map_declared_artifact_is_rejected_by_resolved_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            (paper / "docs").mkdir()
            (paper / "docs" / "source_microsoft_2013.txt").write_text(
                "private source\n", encoding="utf-8"
            )
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {"source_artifact_path": "docs/source_microsoft_2013.txt"}
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.source_artifact_leakage_issues(repo, candidate)

        self.assertTrue(
            any("source_artifact_path" in issue and "source_microsoft" in issue for issue in issues),
            issues,
        )

    def test_artifact_policy_scans_inherited_complete_candidate_tree(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            current = audit / "current_semantic_receipt.json"
            current.write_text("{}\n", encoding="utf-8")
            unreferenced = audit / "unreferenced_receipt.json"
            unreferenced.write_text("{}\n", encoding="utf-8")
            (paper / "PAPER_NOTES.md").write_text("private\n", encoding="utf-8")
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {
                            "current_receipt": current.relative_to(repo).as_posix()
                        },
                        "review_surface": {},
                        "untrusted_metadata": unreferenced.relative_to(repo).as_posix(),
                    }
                ),
                encoding="utf-8",
            )
            self.commit(repo, "public base with stale private artifacts")
            subprocess.run(
                ["git", "switch", "-qc", "release/update"], cwd=repo, check=True
            )
            (repo / "reviewed.txt").write_text("release\n", encoding="utf-8")
            candidate = self.commit(repo, "unrelated release change")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertFalse(any(str(current.name) in issue for issue in issues), issues)
        self.assertTrue(
            any("PAPER_NOTES.md" in issue and "private-document" in issue for issue in issues),
            issues,
        )
        self.assertTrue(
            any(
                "unreferenced_receipt.json" in issue
                and "unreferenced-audit-artifact" in issue
                for issue in issues
            ),
            issues,
        )

    def test_corrected_target_projection_structure_is_exact_and_withholds_approval(
        self,
    ) -> None:
        cases: tuple[tuple[str, object, str], ...] = (
            ("valid", _projected_corrected_target_map(), ""),
            (
                "missing_marker",
                {"items": _projected_corrected_target_map()["items"]},
                "exact public projection marker",
            ),
            (
                "wrong_marker",
                {
                    **_projected_corrected_target_map(),
                    guard.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD: {
                        "schema": 2,
                        "approval_material_included": False,
                    },
                },
                "exact public projection marker",
            ),
            (
                "marker_without_target",
                {
                    guard.PUBLIC_CORRECTED_TARGET_PROJECTION_FIELD: {
                        "schema": guard.PUBLIC_CORRECTED_TARGET_PROJECTION_SCHEMA,
                        "approval_material_included": False,
                    },
                    "items": {},
                },
                "has no corrected targets",
            ),
        )
        for name, payload, expected in cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp_dir:
                repo = Path(temp_dir)
                self.init_repo(repo)
                audit = repo / "papers" / "Fixture" / "audit"
                audit.mkdir(parents=True)
                map_path = audit / "paper_statement_map.json"
                map_path.write_text(json.dumps(payload))
                candidate = self.commit(repo, "corrected target projection fixture")
                paths = set(
                    subprocess.run(
                        ["git", "ls-tree", "-r", "--name-only", candidate],
                        cwd=repo,
                        check=True,
                        text=True,
                        capture_output=True,
                    ).stdout.splitlines()
                )
                selected, issues = guard._candidate_corrected_target_artifacts(
                    repo, candidate, paths
                )
                self.assertEqual(selected, set())
                if expected:
                    self.assertTrue(any(expected in issue for issue in issues), issues)
                else:
                    self.assertEqual(issues, [])

        malformed_cases = (
            ("approval", lambda target: target.__setitem__("approval", {"secret": "text"}), "private approval"),
            (
                "record",
                lambda target: target.__setitem__(CORRECTED_TARGET_RECORD_SHA256_FIELD, "0"),
                CORRECTED_TARGET_RECORD_SHA256_FIELD,
            ),
            (
                "review",
                lambda target: target.__setitem__(CORRECTED_TARGET_REVIEW_SHA256_FIELD, "0" * 64),
                CORRECTED_TARGET_REVIEW_SHA256_FIELD,
            ),
        )
        for name, mutate, expected in malformed_cases:
            with self.subTest(name=name), tempfile.TemporaryDirectory() as temp_dir:
                repo = Path(temp_dir)
                self.init_repo(repo)
                payload = _projected_corrected_target_map()
                target = payload["items"]["theorem_1"]["corrected_target"]
                mutate(target)
                audit = repo / "papers" / "Fixture" / "audit"
                audit.mkdir(parents=True)
                (audit / "paper_statement_map.json").write_text(json.dumps(payload))
                candidate = self.commit(repo, "malformed corrected target projection")
                paths = {"papers/Fixture/audit/paper_statement_map.json"}
                _selected, issues = guard._candidate_corrected_target_artifacts(
                    repo, candidate, paths
                )
                self.assertTrue(any(expected in issue for issue in issues), issues)

    def test_unselected_corrected_target_does_not_authorize_an_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir)
            self.init_repo(repo)
            audit = repo / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            (audit / "SOURCE_TARGET_STATEMENTS.md").write_text("Unbound content.")
            (audit / "paper_statement_map.json").write_text(
                json.dumps(_projected_corrected_target_map())
            )
            candidate = self.commit(repo, "unselected correction fixture")
            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)
        self.assertTrue(any("SOURCE_TARGET_STATEMENTS.md" in issue and "unreferenced" in issue
                            for issue in issues), issues)

    def test_public_graph_artifacts_require_the_selected_closure_preimage(self) -> None:
        from scripts.lean_import_closure import (
            WORKTREE_IDENTITY_SCHEMA, LAKE_ROUTING_SCHEMA,
            lean_import_closure_payload_sha256,
        )
        from scripts.obligation_evidence_graph import (
            build_evidence_leaf, build_obligation_graph, lean_reviewed_semantic_target_leaf,
        )
        from scripts.portable_evidence_identity import canonical_json_bytes

        closure = {
            "schema": WORKTREE_IDENTITY_SCHEMA,
            "entrypoint": "papers/Fixture/ProofInterface.lean",
            "entry_module": "Fixture.ProofInterface",
            "lean_loaded_modules": ["Fixture.ProofInterface"],
            "sources": [{"module": "Fixture.ProofInterface",
                         "path": "papers/Fixture/ProofInterface.lean",
                         "byte_length": 0, "sha256": "1" * 64}],
            "external_import_modules": [],
            "external_module_artifacts_sha256": "2" * 64,
            "build_controls": [
                {"path": path, "tracked_in_index": True, "untracked": False,
                 "path_kind": "file", "byte_length": 0, "sha256": "3" * 64}
                for path in ("lean-toolchain", "lake-manifest.json")
            ],
            "lake_routing": {"schema": LAKE_ROUTING_SCHEMA, "kind": "lean",
                             "sha256": "4" * 64, "byte_length": 0},
        }
        closure_digest = lean_import_closure_payload_sha256(closure)
        target = lean_reviewed_semantic_target_leaf(
            contract_sha256="5" * 64, semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256="6" * 64,
        )
        build = build_evidence_leaf(
            contract_sha256="7" * 64, target_declaration_sha256s=[target.leaf_sha256],
            build_command_sha256="8" * 64, toolchain_sha256="9" * 64,
            lean_import_closure_sha256=closure_digest,
        )
        graph = build_obligation_graph([target, build], root_leaf_sha256s=[build.leaf_sha256])
        pack = {"schema": 1, "paper": "Fixture", "accepted_graph": graph.projection(),
                "leaves": {d: graph.leaves[d].projection() for d in graph.topological_leaf_sha256s},
                "paper_index": {}}
        base = "papers/Fixture/audit/obligation_evidence"
        pointer = base + "/current_accepted_graph.json"
        pack_path = f"{base}/accepted_graphs/sha256/{graph.graph_sha256[:2]}/{graph.graph_sha256}.json"
        preimage = f"{base}/lean_import_closures/sha256/{closure_digest[:2]}/{closure_digest}.json"
        for case in ("valid", "missing", "tampered", "unselected", "wrong_receipt"):
            with self.subTest(case=case), tempfile.TemporaryDirectory() as temp_dir:
                repo = Path(temp_dir)
                self.init_repo(repo)
                def put(path, value):
                    destination = repo / path
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    destination.write_bytes(canonical_json_bytes(value) + b"\n")
                put(pointer, {"schema": 2, "graph_sha256": graph.graph_sha256})
                put(pack_path, pack)
                if case != "missing":
                    value = dict(closure)
                    if case == "tampered":
                        value["external_module_artifacts_sha256"] = "a" * 64
                    put(preimage, value)
                if case == "unselected":
                    put(f"{base}/lean_import_closures/sha256/aa/{'a' * 64}.json", closure)
                receipt_digest = "b" * 64 if case == "wrong_receipt" else graph.graph_sha256
                (repo / "papers/Fixture/FINAL_CLOSURE_RECEIPT.md").write_text(
                    '+++\nschema = 6\npaper = "Fixture"\nclosure_status = "current"\n'
                    'acceptance_credential = false\nclosed_at = "2026-09-06"\n'
                    f'[accepted_graph]\npointer = "{pointer}"\ngraph_sha256 = "{receipt_digest}"\n+++\n'
                )
                candidate = self.commit(repo, "selected graph transport fixture")
                issues = guard.candidate_public_artifact_policy_issues(repo, candidate)
                if case == "valid":
                    self.assertEqual(issues, [])
                elif case == "unselected":
                    self.assertTrue(any("unreferenced-audit-artifact" in issue for issue in issues), issues)
                else:
                    self.assertTrue(any("cannot select current graph artifacts" in issue for issue in issues), issues)

    def test_artifact_policy_allows_absent_optional_review_destination(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {},
                        "review_surface": {
                            "llm_paper_coverage_review": {
                                "defect_support_judgment_file": (
                                    "papers/Fixture/audit/"
                                    "defect_support_match_llm.json"
                                )
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertEqual(issues, [])

    def test_artifact_policy_rejects_absent_declared_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {
                            "current_receipt": (
                                "papers/Fixture/audit/current_receipt.json"
                            )
                        },
                        "review_surface": {},
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertTrue(
            any("declared current audit artifact is absent" in issue for issue in issues),
            issues,
        )

    def test_absent_optional_route_does_not_exempt_present_unreferenced_artifact(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "unreferenced_receipt.json").write_text("{}\n", encoding="utf-8")
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {},
                        "review_surface": {
                            "llm_paper_coverage_review": {
                                "defect_support_judgment_file": (
                                    "papers/Fixture/audit/"
                                    "defect_support_match_llm.json"
                                )
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertTrue(
            any(
                "unreferenced_receipt.json" in issue
                and "unreferenced-audit-artifact" in issue
                for issue in issues
            ),
            issues,
        )

    def test_absent_optional_route_must_still_be_safe_and_canonical(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {},
                        "review_surface": {
                            "llm_paper_coverage_review": {
                                "defect_support_judgment_file": (
                                    "papers/Fixture/audit/../"
                                    "defect_support_match_llm.json"
                                )
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertTrue(
            any("unsafe or noncanonical" in issue for issue in issues),
            issues,
        )

    def test_artifact_policy_rejects_invalid_status_exception(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            receipt = audit / "current_receipt.before_review.json"
            receipt.write_text("{}\n", encoding="utf-8")
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {
                            "current_receipt": receipt.relative_to(repo).as_posix()
                        },
                        "review_surface": {},
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertTrue(
            any("policy configuration is invalid" in issue for issue in issues), issues
        )

    def test_artifact_policy_does_not_check_deleted_paper_or_status(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {},
                        "review_surface": {},
                    }
                ),
                encoding="utf-8",
            )
            private_note = paper / "FORMALIZATION_PLAN.md"
            private_note.write_text("private\n", encoding="utf-8")
            self.commit(repo, "base")
            private_note.unlink()
            (paper / "status.json").unlink()
            paper.rmdir()
            candidate = self.commit(repo, "delete excluded paper")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertEqual(issues, [])

    def test_artifact_policy_rejects_cross_paper_status_exception(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "status.json").write_text(
                json.dumps(
                    {
                        "id": "Fixture",
                        "repository_visibility": "public",
                        "artifacts": {
                            "current_receipt": "papers/Other/audit/current_receipt.json"
                        },
                        "review_surface": {},
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertTrue(
            any("must stay beneath papers/Fixture/audit/" in issue for issue in issues),
            issues,
        )

    def test_source_map_companion_scan_paths_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            (paper / "scan.pdf").write_bytes(b"scan")
            (paper / "ocr-input.pdf").write_bytes(b"ocr")
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "canonical.txt",
                        "source_text_companion": {
                            "canonical_text": {"path": "canonical.txt"},
                            "visual_primary_scan": {"path": "scan.pdf"},
                            "transcript_input_scan": {"path": "ocr-input.pdf"},
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.source_artifact_leakage_issues(repo, candidate)

        self.assertEqual(len(issues), 2, issues)
        self.assertTrue(any("visual_primary_scan" in issue for issue in issues), issues)
        self.assertTrue(any("transcript_input_scan" in issue for issue in issues), issues)

    def test_official_arxiv_tex_artifact_is_an_explicit_public_exception(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            source = paper / "source" / "source.tex"
            source.parent.mkdir()
            source_bytes = b"\\documentclass{article}\\begin{document}Official arXiv source.\\end{document}\n"
            source.write_bytes(source_bytes)
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://arxiv.org/abs/2601.00001v2",
                        "source_artifact_path": "source/source.tex",
                        "source_artifact_sha256": hashlib.sha256(source_bytes).hexdigest(),
                        "items": {
                            "claim": {
                                "source_anchor_evidence": [
                                    {"path": "source/source.tex", "line_start": 1, "line_end": 1}
                                ]
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            leakage = guard.source_artifact_leakage_issues(repo, candidate)
            policy = guard.candidate_public_artifact_policy_issues(repo, candidate)

        self.assertEqual(leakage, [])
        self.assertEqual(policy, [])

    def test_source_map_archive_surface_archive_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            (paper / "source.tar").write_bytes(b"private source archive")
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "audit/source_archive_surface.tex",
                        "source_archive_surface": {
                            "archive": {"path": "source.tar"},
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.source_artifact_leakage_issues(repo, candidate)

        self.assertEqual(len(issues), 1, issues)
        self.assertTrue(any("source_archive_surface.archive" in issue for issue in issues), issues)

    def test_source_map_item_level_source_byte_paths_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            for filename in ("item-input.data", "anchor-input.data", "nested-anchor.data"):
                (paper / filename).write_text("private source bytes\n", encoding="utf-8")
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "omitted-canonical.data",
                        "items": {
                            "claim": {
                                "source_text_file": "item-input.data",
                                "source_anchor_evidence": [
                                    {"path": "anchor-input.data", "line_start": 1, "line_end": 1}
                                ],
                                "corrected_target": {
                                    "source_anchor_evidence": [
                                        {
                                            "path": "nested-anchor.data",
                                            "line_start": 1,
                                            "line_end": 1,
                                        }
                                    ]
                                },
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.source_artifact_leakage_issues(repo, candidate)

        self.assertEqual(len(issues), 3, issues)
        self.assertTrue(
            any("source_text_file" in issue and "item-input" in issue for issue in issues),
            issues,
        )
        self.assertTrue(
            any(
                "source_anchor_evidence" in issue and "anchor-input" in issue
                for issue in issues
            ),
            issues,
        )
        self.assertTrue(
            any(
                "corrected_target" in issue and "nested-anchor" in issue
                for issue in issues
            ),
            issues,
        )

    def test_source_map_item_path_cannot_escape_its_paper_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paper = repo / "papers" / "Fixture"
            (paper / "audit").mkdir(parents=True)
            (paper / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "claim": {
                                "source_anchor_evidence": [
                                    {"path": "../Other/neutral.data"}
                                ]
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            candidate = self.commit(repo, "candidate")

            issues = guard.source_artifact_leakage_issues(repo, candidate)

        self.assertTrue(
            any("leaves its paper directory" in issue for issue in issues), issues
        )

    def test_forbidden_path_backup_covers_archives_but_not_citation_source(self) -> None:
        self.assertIsNotNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/source_tex/arxiv_source.tar"
            )
        )
        self.assertIsNotNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/source_arxiv.tar"
            )
        )
        self.assertIsNotNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/source/subdir/unreviewed.tex"
            )
        )
        self.assertIsNotNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/Source/unreviewed.tex"
            )
        )
        self.assertIsNotNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/opaque-payload.7z"
            )
        )
        self.assertIsNone(
            guard.FORBIDDEN_PUBLIC_PATH_RE.search(
                "papers/Fixture/audit/citation_source.txt"
            )
        )

    def test_private_named_public_workflow_paths_have_only_exact_exceptions(self) -> None:
        expected_contributor_docs = {
            "docs/ARCHITECTURE.md",
            "docs/PUBLIC_RELEASE_CHECKLIST.md",
            "docs/REVIEW_DASHBOARD.md",
            "docs/contributing/README.md",
        }
        self.assertLessEqual(
            expected_contributor_docs,
            guard.PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS,
        )
        self.assertNotIn(
            "docs/contributing/PRIVATE_NOTES.md",
            guard.PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS,
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            paths = {
                "docs/PRIVATE_DEVELOPMENT_WORKFLOW.md": "public workflow\n",
                "scripts/private_paper_checkpoint.py": "# public workflow helper\n",
                "site/private_preview_server.py": "# localhost preview helper\n",
                "docs/PRIVATE_RELEASE_SECRETS.md": "must remain private\n",
            }
            for relative, content in paths.items():
                target = repo / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_text(content, encoding="utf-8")
            candidate = self.commit(repo, "candidate")

            issues = guard.forbidden_candidate_path_issues(repo, candidate)

        self.assertEqual(
            issues,
            [
                "forbidden private/source artifact path in public candidate: "
                "docs/PRIVATE_RELEASE_SECRETS.md"
            ],
        )
        for relative in guard.PUBLIC_PRIVATE_NAMED_WORKFLOW_PATHS:
            with self.subTest(relative=relative):
                self.assertIsNotNone(guard.FORBIDDEN_PUBLIC_PATH_RE.search(relative))
        self.assertNotIn(
            "docs/PRIVATE_RELEASE_SECRETS.md",
            guard.PUBLIC_PRIVATE_NAMED_WORKFLOW_PATHS,
        )

    def test_reviewed_stage_guides_and_readme_boundary_pass_content_check(self) -> None:
        stage_paths = {
            "skills/econcs-formalizer/references/human-facing-artifacts.md",
            "skills/econcs-formalizer/references/intake-and-source-surface.md",
            "skills/econcs-formalizer/references/release-and-sync.md",
            "skills/econcs-shared-worktree/SKILL.md",
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            for relative in stage_paths:
                target = repo / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((guard.ROOT / relative).read_bytes())
            (repo / "README.md").write_text(
                guard.PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE + "\n",
                encoding="utf-8",
            )
            candidate = self.commit(repo, "reviewed contributor guidance")
            self.assertEqual(guard.public_artifact_content_issues(repo, candidate), [])
            (repo / "README.md").write_text(
                guard.PUBLIC_README_PRIVATE_WORKFLOW_GUIDANCE
                + "\nPrivate source cache: /tmp/unreviewed.txt\n",
                encoding="utf-8",
            )
            candidate = self.commit(repo, "unreviewed nearby private content")
            self.assertTrue(guard.public_artifact_content_issues(repo, candidate))

    def test_lean_source_citations_preserve_proofs_without_allowing_private_paths(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            repo = Path(temp_dir) / "candidate"
            self.init_repo(repo)
            target = repo / "papers/Fixture/Proof.lean"
            target.parent.mkdir(parents=True)
            target.write_text("/- Source: source.txt:20-30, source_tex/proof.tex, and source.pdf. -/\ntheorem checked : True := True.intro\n")
            candidate = self.commit(repo, "source citation in exact Lean blob")
            self.assertEqual(guard.public_artifact_content_issues(repo, candidate), [])
            target.write_text("/- Source: /home/reviewer/private/source.txt -/\ntheorem checked : True := True.intro\n")
            candidate = self.commit(repo, "private machine path remains forbidden")
            self.assertTrue(guard.public_artifact_content_issues(repo, candidate))
            for filename in ("source.txt", "source.pdf"):
                with self.subTest(filename=filename):
                    source = repo / "papers/Fixture" / filename
                    source.write_text("Source bytes remain excluded.\n")
                    candidate = self.commit(repo, "unapproved source artifact")
                    self.assertTrue(guard.forbidden_candidate_path_issues(repo, candidate))

    def test_generated_status_check_invokes_trusted_script_with_candidate_repo(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            candidate = root / "candidate"
            self.init_repo(candidate)
            (candidate / ".gitignore").write_text("ambient-cache\n", encoding="utf-8")
            self.commit(candidate, "candidate")
            (candidate / "ambient-cache").write_text(
                "must not enter tree-only checkout\n", encoding="utf-8"
            )
            trusted = root / "trusted_status_sync.py"
            trusted.write_text(
                "import os, pathlib, sys\n"
                "expected = pathlib.Path(sys.argv[sys.argv.index('--repo') + 1])\n"
                "propagated = pathlib.Path(os.environ['APPLIEDMODELINGLIB_REPO_ROOT'])\n"
                f"original = pathlib.Path({str(candidate.resolve())!r})\n"
                "ok = (expected == pathlib.Path.cwd() == propagated\n"
                "      and expected != original\n"
                "      and not (expected / 'ambient-cache').exists()\n"
                "      and '--check' in sys.argv)\n"
                "raise SystemExit(0 if ok else 9)\n",
                encoding="utf-8",
            )
            with mock.patch.object(guard, "TRUSTED_STATUS_SYNC", trusted):
                issues = guard.generated_status_freshness_issues(candidate)

        self.assertEqual(issues, [])

    def test_generated_status_check_imports_trusted_sibling_under_isolation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            candidate = root / "candidate"
            self.init_repo(candidate)
            (candidate / "root_readme_policy.py").write_text(
                "ORIGIN = 'candidate'\n", encoding="utf-8"
            )
            self.commit(candidate, "candidate")

            trusted = root / "trusted"
            trusted.mkdir()
            (trusted / "root_readme_policy.py").write_text(
                "ORIGIN = 'trusted'\n", encoding="utf-8"
            )
            status_sync = trusted / "sync_paper_status.py"
            status_sync.write_text(
                "from root_readme_policy import ORIGIN\n"
                "raise SystemExit(0 if ORIGIN == 'trusted' else 9)\n",
                encoding="utf-8",
            )

            with mock.patch.object(guard, "TRUSTED_STATUS_SYNC", status_sync):
                issues = guard.generated_status_freshness_issues(candidate)

        self.assertEqual(issues, [])

    def test_trusted_status_helpers_share_cross_checkout_repository_root(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            candidate = Path(temp_dir).resolve()
            (candidate / "config").mkdir()
            (candidate / "config" / "formalization_audit_protocol.json").write_bytes(
                (ROOT / "config" / "formalization_audit_protocol.json").read_bytes()
            )
            module_paths = [
                ROOT / "scripts" / "root_readme_policy.py",
                ROOT / "scripts" / "formalization_protocol.py",
                ROOT / "scripts" / "review_dashboard.py",
                ROOT / "scripts" / "audit_evidence_integrity.py",
            ]
            probe = (
                "import importlib.util, os, pathlib, sys\n"
                f"root = pathlib.Path({str(ROOT)!r})\n"
                f"candidate = pathlib.Path({str(candidate)!r})\n"
                "sys.path[:0] = [str(root), str(root / 'scripts')]\n"
                "os.environ['APPLIEDMODELINGLIB_REPO_ROOT'] = str(candidate)\n"
                f"paths = {[str(path) for path in module_paths]!r}\n"
                "for index, raw in enumerate(paths):\n"
                "    name = f'root_probe_{index}'\n"
                "    spec = importlib.util.spec_from_file_location(name, raw)\n"
                "    module = importlib.util.module_from_spec(spec)\n"
                "    sys.modules[name] = module\n"
                "    spec.loader.exec_module(module)\n"
                "    assert module.ROOT == candidate, (raw, module.ROOT, candidate)\n"
            )
            result = subprocess.run(
                [sys.executable, "-I", "-c", probe],
                cwd=ROOT,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                check=False,
            )

        self.assertEqual(result.returncode, 0, result.stdout)


if __name__ == "__main__":
    unittest.main()
