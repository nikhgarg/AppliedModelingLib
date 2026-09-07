#!/usr/bin/env python3
"""Adversarial tests for the isolated paper-contribution boundary."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from contextlib import nullcontext
from pathlib import Path
from unittest import mock

from scripts import paper_contribution as contribution
from scripts import paper_target_registration as registration


PAPER = "ABC26EfficientPaper"
EXISTING = "XYZ25ExistingPaper"
PROVIDER = "DEF24ProviderPaper"
BASE_LAKEFILE = f'''name = "Fixture"
version = "0.1.0"
defaultTargets = ["AppliedModelingLib"]

[[lean_lib]]
name = "AppliedModelingLib"

[[lean_lib]]
name = "{EXISTING}"
srcDir = "papers"
'''


class GitFixture:
    def __init__(self, root: Path) -> None:
        self.root = root
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.com")
        self.git("config", "user.name", "Fixture")
        (root / "lakefile.toml").write_text(BASE_LAKEFILE, encoding="utf-8")
        self.write_paper(EXISTING, status="formalized")
        (root / "docs").mkdir()
        (root / "site").mkdir()
        (root / "docs" / "PAPER_STATUS.md").write_text("# Status\n")
        (root / "papers" / "status.json").write_text("{}\n")
        (root / "papers" / "human_status.json").write_text("{}\n")
        (root / "site" / "index.html").write_text(
            "<html>\n"
            "<!-- BEGIN GENERATED LIBRARY COMPONENT ROWS -->\n"
            "base library rows\n"
            "<!-- END GENERATED LIBRARY COMPONENT ROWS -->\n"
            "<!-- BEGIN GENERATED PROJECT STATS -->\n"
            "base stats\n"
            "<!-- END GENERATED PROJECT STATS -->\n"
            "<!-- BEGIN GENERATED PAPER STATUS ROWS -->\n"
            "base paper rows\n"
            "<!-- END GENERATED PAPER STATUS ROWS -->\n"
            "</html>\n",
            encoding="utf-8",
        )
        self.commit("base")
        self.git("tag", "base")

    def git(self, *args: str) -> str:
        proc = subprocess.run(
            ["git", *args],
            cwd=self.root,
            text=True,
            capture_output=True,
            check=True,
        )
        return proc.stdout.strip()

    def write_paper(self, paper: str, *, status: str) -> None:
        folder = self.root / "papers" / paper
        folder.mkdir(parents=True, exist_ok=True)
        (folder / "PaperInterface.lean").write_text(
            f"namespace {paper}\nend {paper}\n", encoding="utf-8"
        )
        (folder / "status.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "id": paper,
                    "repository_visibility": "public",
                    "status": status,
                }
            )
            + "\n",
            encoding="utf-8",
        )
        (self.root / "papers" / f"{paper}.lean").write_text(
            f"import {paper}.PaperInterface\n", encoding="utf-8"
        )

    def add_new_paper(self, *, status: str = "formalized") -> None:
        self.write_paper(PAPER, status=status)
        registration.register_paper_target(self.root / "lakefile.toml", PAPER)

    def commit(self, message: str) -> None:
        self.git("add", "--all")
        self.git("commit", "-q", "-m", message)


class PaperContributionDoctorTests(unittest.TestCase):
    @staticmethod
    def _tool_result(*args: object, **kwargs: object) -> subprocess.CompletedProcess[str]:
        return subprocess.CompletedProcess(args=args, returncode=0, stdout="tool version\n")

    def test_doctor_accepts_python_310(self) -> None:
        with (
            mock.patch.object(contribution.sys, "version_info", (3, 10, 0)),
            mock.patch.object(
                contribution.shutil, "which", side_effect=lambda name: f"/usr/bin/{name}"
            ),
            mock.patch.object(
                contribution.subprocess, "run", side_effect=self._tool_result
            ),
        ):
            contribution._doctor()

    def test_doctor_rejects_python_39(self) -> None:
        with (
            mock.patch.object(contribution.sys, "version_info", (3, 9, 0)),
            mock.patch.object(
                contribution.shutil, "which", side_effect=lambda name: f"/usr/bin/{name}"
            ),
            mock.patch.object(
                contribution.subprocess, "run", side_effect=self._tool_result
            ),
            self.assertRaisesRegex(contribution.ContributionError, "Python >= 3.10"),
        ):
            contribution._doctor()


class PaperContributionScopeTests(unittest.TestCase):
    def plan(self, fixture: GitFixture) -> contribution.ContributionPlan:
        with (
            mock.patch.object(contribution, "ROOT", fixture.root),
            mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
        ):
            return contribution.contribution_plan("base")

    def test_source_history_names_do_not_block_explicit_citation_notes(self) -> None:
        self.assertTrue(
            contribution._unsafe_public_artifact(
                f"papers/{PAPER}/transcript.md"
            )
        )
        self.assertFalse(
            contribution._unsafe_public_artifact(
                f"papers/{PAPER}/citation_source.txt"
            )
        )

    def test_source_history_blocks_source_trees_and_archives(self) -> None:
        for path in (
            f"papers/{PAPER}/source_tex/main.tex",
            f"papers/{PAPER}/sources/main.tex",
            f"papers/{PAPER}/.audit_source/transcript.txt",
            f"papers/{PAPER}/paper-source.tar.xz",
            f"papers/{PAPER}/submission.rar",
        ):
            with self.subTest(path=path):
                self.assertTrue(contribution._unsafe_public_artifact(path))
        self.assertFalse(
            contribution._unsafe_public_artifact(
                f"papers/{PAPER}/docs/DependencyDAG.tex"
            )
        )

    def test_exact_new_paper_and_registration_select_only_that_paper(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            fixture.commit("paper")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "paper")
        self.assertEqual(plan.paper, PAPER)
        self.assertTrue(plan.new_paper)
        self.assertEqual(plan.profile, "full")
        self.assertEqual(plan.reasons, ())
        self.assertNotIn(EXISTING, {change.path for change in plan.changed_paths})

    def test_generated_aggregate_escalates_instead_of_reading_other_papers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            (fixture.root / "papers" / "status.json").write_text(
                '{"updated": true}\n'
            )
            fixture.commit("paper plus aggregate")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("generated aggregate" in reason for reason in plan.reasons))

    def test_exact_aggregate_projection_has_its_own_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status = fixture.root / "papers" / "status.json"
            status.write_text('{"updated": true}\n', encoding="utf-8")
            fixture.commit("refresh aggregate")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "aggregate")
        self.assertEqual(plan.paper, "")
        self.assertEqual(plan.reasons, ())

    def test_docs_status_projection_precedes_docs_only_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status = fixture.root / "docs" / "PAPER_STATUS.md"
            status.write_text("# Updated status\n", encoding="utf-8")
            fixture.commit("refresh docs aggregate")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "aggregate")

    def test_aggregate_mixed_with_documentation_escalates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            (fixture.root / "papers" / "status.json").write_text('{"updated": true}\n')
            (fixture.root / "docs" / "GUIDE.md").write_text("# Guide\n")
            fixture.commit("mixed aggregate and docs")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")

        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            (fixture.root / "docs" / "PAPER_STATUS.md").write_text(
                "# Updated aggregate\n"
            )
            (fixture.root / "docs" / "GUIDE.md").write_text("# Guide\n")
            fixture.commit("mixed docs aggregate")

            docs_mixed = self.plan(fixture)

        self.assertEqual(docs_mixed.mode, "integration")
        self.assertTrue(
            any("may not be mixed" in reason for reason in docs_mixed.reasons)
        )

    def test_aggregate_delete_or_mode_change_escalates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status = fixture.root / "papers" / "status.json"
            status.unlink()
            fixture.commit("delete aggregate")
            deleted = self.plan(fixture)

        self.assertEqual(deleted.mode, "integration")
        self.assertTrue(any("must be modified" in reason for reason in deleted.reasons))

        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status = fixture.root / "papers" / "status.json"
            status.write_text('{"updated": true}\n')
            status.chmod(0o755)
            fixture.commit("make aggregate executable")
            executable = self.plan(fixture)

        self.assertEqual(executable.mode, "integration")
        self.assertTrue(any("regular file" in reason for reason in executable.reasons))

    def test_aggregate_site_may_change_only_generated_regions(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            site = fixture.root / "site" / "index.html"
            site.write_text(
                site.read_text().replace("base paper rows", "updated paper rows")
            )
            fixture.commit("refresh generated site rows")
            generated = self.plan(fixture)

        self.assertEqual(generated.mode, "aggregate")

        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            site = fixture.root / "site" / "index.html"
            site.write_text(site.read_text().replace("<html>", "<html data-edited>"))
            fixture.commit("edit static site shell")
            static = self.plan(fixture)

        self.assertEqual(static.mode, "integration")
        self.assertTrue(any("outside generated" in reason for reason in static.reasons))

    def test_aggregate_branch_must_be_based_on_exact_comparison_base(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status = fixture.root / "papers" / "status.json"
            status.write_text('{"updated": true}\n')
            fixture.commit("aggregate candidate")
            fixture.git("tag", "aggregate-candidate")

            fixture.git("switch", "-q", "-c", "advanced-base", "base")
            (fixture.root / "CONTRIBUTING.md").write_text("advanced base\n")
            fixture.commit("advance comparison base")
            fixture.git("tag", "comparison-base")

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
            ):
                plan = contribution.contribution_plan(
                    "comparison-base", "aggregate-candidate"
                )

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("branch rebased" in reason for reason in plan.reasons))

    def test_behind_base_paper_cannot_select_candidate_controlled_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- candidate proof edit\n")
            fixture.commit("paper candidate")
            fixture.git("tag", "paper-candidate")

            fixture.git("switch", "-q", "-c", "advanced-paper-base", "base")
            (fixture.root / "CONTRIBUTING.md").write_text("advanced policy\n")
            fixture.commit("advance paper base")
            fixture.git("tag", "paper-comparison-base")

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
            ):
                plan = contribution.contribution_plan(
                    "paper-comparison-base", "paper-candidate"
                )

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("branch rebased" in reason for reason in plan.reasons))

    def test_reverted_nonaggregate_history_cannot_use_aggregate_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            temporary_doc = fixture.root / "docs" / "TEMP.md"
            temporary_doc.write_text("temporary\n")
            fixture.commit("touch nonaggregate history")
            temporary_doc.unlink()
            (fixture.root / "papers" / "status.json").write_text(
                '{"updated": true}\n'
            )
            fixture.commit("leave aggregate-only diff")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("aggregate-only history" in reason for reason in plan.reasons))

    def test_merge_commit_cannot_use_aggregate_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            candidate_branch = fixture.git("branch", "--show-current")
            (fixture.root / "papers" / "status.json").write_text(
                '{"updated": true}\n'
            )
            fixture.commit("aggregate candidate")

            fixture.git("switch", "-q", "-c", "empty-side", "base")
            fixture.git("commit", "--allow-empty", "-q", "-m", "empty side")
            fixture.git("switch", "-q", candidate_branch)
            fixture.git("merge", "--no-ff", "-q", "-m", "merge side", "empty-side")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("no merge commits" in reason for reason in plan.reasons))

    def test_shared_or_second_paper_change_escalates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            existing = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            existing.write_text(existing.read_text() + "\n-- unrelated\n")
            fixture.commit("two papers")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertIn("more than one paper is changed", plan.reasons)

    def test_noncanonical_lake_rewrite_escalates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            lakefile = fixture.root / "lakefile.toml"
            lakefile.write_text(lakefile.read_text() + "\n# extra rewrite\n")
            fixture.commit("paper plus lake rewrite")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("not exactly" in reason for reason in plan.reasons))

    def test_cross_paper_import_is_provisional_until_the_lean_graph_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            interface = fixture.root / "papers" / PAPER / "PaperInterface.lean"
            interface.write_text(
                f"import «{EXISTING}».PaperInterface\n" + interface.read_text()
            )
            fixture.commit("cross paper import")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "paper")
        self.assertEqual(plan.reasons, ())

    def test_required_interface_deletion_escalates(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.unlink()
            fixture.commit("delete paper file")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("missing paper-facing interface" in reason for reason in plan.reasons))

    def test_obsolete_paper_local_file_can_be_deleted_without_global_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            obsolete = fixture.root / "papers" / EXISTING / "Obsolete.lean"
            obsolete.write_text("-- obsolete\n")
            fixture.commit("add obsolete fixture")
            fixture.git("tag", "contribution-base")
            obsolete.unlink()
            fixture.commit("remove obsolete fixture")
            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
            ):
                plan = contribution.contribution_plan("contribution-base")

        self.assertEqual(plan.mode, "paper")
        self.assertEqual(plan.paper, EXISTING)

    def test_existing_paper_only_change_remains_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- proof-body edit\n")
            fixture.commit("existing paper")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "paper")
        self.assertEqual(plan.paper, EXISTING)
        self.assertFalse(plan.new_paper)

    def test_full_status_downgrade_escalates_to_integration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status_path = fixture.root / "papers" / EXISTING / "status.json"
            payload = json.loads(status_path.read_text(encoding="utf-8"))
            payload["status"] = "not started"
            status_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            fixture.commit("downgrade paper")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("downgraded" in reason for reason in plan.reasons))

    def test_public_to_private_change_escalates_to_integration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            status_path = fixture.root / "papers" / EXISTING / "status.json"
            payload = json.loads(status_path.read_text(encoding="utf-8"))
            payload["repository_visibility"] = "private_only"
            status_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            fixture.commit("hide paper")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(any("public paper" in reason for reason in plan.reasons))

    def test_source_blob_added_then_deleted_blocks_public_history(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            source = fixture.root / "papers" / PAPER / "authors-version.pdf"
            source.write_bytes(b"licensed source bytes")
            fixture.commit("accidentally add source")
            source.unlink()
            interface = fixture.root / "papers" / PAPER / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- proof work\n")
            fixture.commit("remove source")

            plan = self.plan(fixture)

        self.assertTrue(plan.blocked)
        self.assertTrue(any("source artifact" in reason for reason in plan.reasons))

    def test_extracted_transcript_added_then_deleted_blocks_public_history(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            transcript = fixture.root / "papers" / PAPER / "transcript.md"
            transcript.write_text("verbatim source text\n", encoding="utf-8")
            fixture.commit("accidentally add transcript")
            transcript.unlink()
            fixture.commit("delete transcript")

            plan = self.plan(fixture)

        self.assertTrue(plan.blocked)
        self.assertTrue(any("transcript.md" in reason for reason in plan.reasons))

    def test_reverted_shared_edit_still_escalates_from_paper_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            shared = fixture.root / "CONTRIBUTING.md"
            shared.write_text("temporary shared edit\n", encoding="utf-8")
            fixture.commit("mixed edit")
            shared.unlink()
            interface = fixture.root / "papers" / PAPER / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- proof work\n")
            fixture.commit("revert shared edit")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(
            any("commit history touched" in reason for reason in plan.reasons)
        )

    def test_docs_only_change_does_not_schedule_lean_or_paper_audits(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            docs = fixture.root / "docs"
            docs.mkdir(exist_ok=True)
            (docs / "GUIDE.md").write_text("# Guide\n")
            fixture.commit("docs")

            plan = self.plan(fixture)

        self.assertEqual(plan.mode, "docs")
        self.assertEqual(plan.paper, "")

    def test_trusted_classifier_can_inspect_a_separate_candidate_repo(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            fixture.commit("paper")
            trusted_root = contribution.ROOT
            trusted_papers = contribution.PAPERS

            with contribution._scope_repository(fixture.root):
                self.assertEqual(contribution.ROOT, fixture.root.resolve())
                plan = contribution.contribution_plan("base")

            self.assertEqual(contribution.ROOT, trusted_root)
            self.assertEqual(contribution.PAPERS, trusted_papers)

        self.assertEqual(plan.mode, "paper")
        self.assertEqual(plan.paper, PAPER)

    def test_candidate_classifier_edit_cannot_select_the_paper_lane(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            script = fixture.root / "scripts" / "paper_contribution.py"
            script.parent.mkdir()
            script.write_text("# trusted baseline\n", encoding="utf-8")
            fixture.commit("add trusted classifier")
            fixture.git("tag", "trusted-base")

            fixture.add_new_paper()
            script.write_text(
                "print('mode=paper')  # candidate tries to narrow CI\n",
                encoding="utf-8",
            )
            fixture.commit("paper plus candidate classifier rewrite")

            with contribution._scope_repository(fixture.root):
                plan = contribution.contribution_plan("trusted-base")

        self.assertEqual(plan.mode, "integration")
        self.assertTrue(
            any(
                reason == "shared path changed: scripts/paper_contribution.py"
                for reason in plan.reasons
            )
        )


class PaperContributionSemanticIsolationTests(unittest.TestCase):
    def test_quoted_cross_paper_import_is_rejected_by_lean_module_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            interface = fixture.root / "papers" / PAPER / "PaperInterface.lean"
            interface.write_text(
                f"import «{EXISTING}».PaperInterface\n" + interface.read_text(),
                encoding="utf-8",
            )

            def graph_loader(
                root: Path, entry_module: str, _timeout: int
            ) -> tuple[tuple[str, ...], str]:
                self.assertEqual(root, fixture.root)
                self.assertEqual(entry_module, PAPER)
                self.assertIn(f"«{EXISTING}»", interface.read_text(encoding="utf-8"))
                return (
                    tuple(
                        sorted(
                            {
                                PAPER,
                                f"{PAPER}.PaperInterface",
                                f"{EXISTING}.PaperInterface",
                                "Init",
                            }
                        )
                    ),
                    "",
                )

            with mock.patch.object(contribution, "ROOT", fixture.root):
                dependencies = contribution._semantic_cross_paper_dependencies(
                    PAPER,
                    {PAPER, EXISTING},
                    module_graph_loader=graph_loader,
                )

        self.assertEqual(dependencies, (f"{EXISTING}.PaperInterface",))

    def test_transitive_cross_paper_import_through_local_bridge_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            folder = fixture.root / "papers" / PAPER
            (folder / "Bridge.lean").write_text(
                f"import {EXISTING}.PaperInterface\n", encoding="utf-8"
            )
            (folder / "PaperInterface.lean").write_text(
                f"import {PAPER}.Bridge\n", encoding="utf-8"
            )

            def graph_loader(
                _root: Path, _entry_module: str, _timeout: int
            ) -> tuple[tuple[str, ...], str]:
                return (
                    tuple(
                        sorted(
                            {
                                PAPER,
                                f"{PAPER}.PaperInterface",
                                f"{PAPER}.Bridge",
                                f"{EXISTING}.PaperInterface",
                            }
                        )
                    ),
                    "",
                )

            with mock.patch.object(contribution, "ROOT", fixture.root):
                dependencies = contribution._semantic_cross_paper_dependencies(
                    PAPER,
                    {PAPER, EXISTING},
                    module_graph_loader=graph_loader,
                )

        self.assertEqual(dependencies, (f"{EXISTING}.PaperInterface",))

    def test_semantic_graph_detects_path_owned_paper_without_lake_registration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.write_paper(PROVIDER, status="formalized")

            def graph_loader(
                _root: Path, _entry_module: str, _timeout: int
            ) -> tuple[tuple[str, ...], str]:
                return (
                    (PAPER, f"{PAPER}.PaperInterface", f"{PROVIDER}.MainTheorems"),
                    "",
                )

            with mock.patch.object(contribution, "ROOT", fixture.root):
                dependencies = contribution._semantic_cross_paper_dependencies(
                    PAPER,
                    {PAPER, EXISTING},
                    module_graph_loader=graph_loader,
                )

        self.assertEqual(dependencies, (f"{PROVIDER}.MainTheorems",))

    def test_unavailable_lean_graph_fails_closed(self) -> None:
        def unavailable(
            _root: Path, _entry_module: str, _timeout: int
        ) -> tuple[None, str]:
            return None, "graph unavailable"

        with self.assertRaisesRegex(
            contribution.ContributionError, "graph unavailable"
        ):
            contribution._semantic_cross_paper_dependencies(
                PAPER,
                {PAPER, EXISTING},
                module_graph_loader=unavailable,
            )

    def test_existing_paper_may_retain_exact_base_cross_paper_modules(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.write_paper(PROVIDER, status="formalized")
            registration.register_paper_target(fixture.root / "lakefile.toml", PROVIDER)
            fixture.commit("add provider and base dependency")
            fixture.git("tag", "dependency-base")
            base_root = fixture.root / "detached-base"

            def dependencies(
                _paper: str,
                _libraries: set[str],
                *,
                root: Path | None = None,
                module_graph_loader: object | None = None,
            ) -> tuple[str, ...]:
                del module_graph_loader
                self.assertIn(root, {None, base_root})
                return (f"{PROVIDER}.PaperInterface",)

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(
                    contribution,
                    "_trusted_base_checkout",
                    return_value=nullcontext(base_root),
                ),
                mock.patch.object(
                    contribution,
                    "_semantic_cross_paper_dependencies",
                    side_effect=dependencies,
                ),
            ):
                contribution._assert_semantically_isolated_paper(
                    EXISTING,
                    trusted_base="dependency-base",
                )

    def test_uncommitted_existing_paper_defers_base_graph_until_pr_check(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.add_new_paper()
            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(
                    contribution,
                    "_semantic_cross_paper_dependencies",
                    return_value=(f"{PROVIDER}.PaperInterface",),
                ),
            ):
                contribution._assert_semantically_isolated_paper(
                    EXISTING,
                    allow_existing_development_dependencies=True,
                )

                with self.assertRaisesRegex(
                    contribution.ContributionError, "reaches other paper"
                ):
                    contribution._assert_semantically_isolated_paper(PAPER)

    def test_existing_paper_cannot_widen_its_base_cross_paper_closure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.write_paper(PROVIDER, status="formalized")
            registration.register_paper_target(fixture.root / "lakefile.toml", PROVIDER)
            fixture.commit("add provider and base dependency")
            fixture.git("tag", "dependency-base")
            base_root = fixture.root / "detached-base"

            def dependencies(
                _paper: str,
                _libraries: set[str],
                *,
                root: Path | None = None,
                module_graph_loader: object | None = None,
            ) -> tuple[str, ...]:
                del module_graph_loader
                if root == base_root:
                    return (f"{PROVIDER}.PaperInterface",)
                return (
                    f"{PROVIDER}.NewResult",
                    f"{PROVIDER}.PaperInterface",
                )

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(
                    contribution,
                    "_trusted_base_checkout",
                    return_value=nullcontext(base_root),
                ),
                mock.patch.object(
                    contribution,
                    "_semantic_cross_paper_dependencies",
                    side_effect=dependencies,
                ),
            ):
                with self.assertRaisesRegex(
                    contribution.ContributionError,
                    rf"introduces new other-paper module.*{PROVIDER}\.NewResult",
                ):
                    contribution._assert_semantically_isolated_paper(
                        EXISTING,
                        trusted_base="dependency-base",
                    )

    def test_trusted_base_graph_failure_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            fixture.write_paper(PROVIDER, status="formalized")
            registration.register_paper_target(fixture.root / "lakefile.toml", PROVIDER)
            fixture.commit("add provider")
            fixture.git("tag", "dependency-base")
            base_root = fixture.root / "detached-base"

            def dependencies(
                _paper: str,
                _libraries: set[str],
                *,
                root: Path | None = None,
                module_graph_loader: object | None = None,
            ) -> tuple[str, ...]:
                del module_graph_loader
                if root == base_root:
                    raise contribution.ContributionError("base graph unavailable")
                return (f"{PROVIDER}.PaperInterface",)

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(
                    contribution,
                    "_trusted_base_checkout",
                    return_value=nullcontext(base_root),
                ),
                mock.patch.object(
                    contribution,
                    "_semantic_cross_paper_dependencies",
                    side_effect=dependencies,
                ),
            ):
                with self.assertRaisesRegex(
                    contribution.ContributionError, "base graph unavailable"
                ):
                    contribution._assert_semantically_isolated_paper(
                        EXISTING,
                        trusted_base="dependency-base",
                    )

    def test_trusted_base_checkout_reads_exact_commit_and_only_lean_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- candidate-only\n")
            (fixture.root / "papers" / EXISTING / "source.pdf").write_bytes(
                b"source bytes must not enter the base build tree"
            )
            fixture.commit("candidate edit")

            with mock.patch.object(contribution, "ROOT", fixture.root):
                with contribution._trusted_base_checkout("base") as base_root:
                    base_interface = (
                        base_root / "papers" / EXISTING / "PaperInterface.lean"
                    )
                    self.assertNotIn("candidate-only", base_interface.read_text())
                    self.assertFalse(
                        (base_root / "papers" / EXISTING / "source.pdf").exists()
                    )
                    self.assertTrue((base_root / "lakefile.toml").is_file())


class PaperContributionCommandTests(unittest.TestCase):
    def new_args(self) -> object:
        return contribution.parse_args(
            [
                "new",
                "https://example.test/paper",
                "--folder",
                PAPER,
                "--title",
                "Efficient Paper",
                "--authors",
                "A. Author",
                "--version",
                "published v1",
                "--no-download",
            ]
        )

    def test_new_facade_registers_target_and_creates_audit_handoff(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            papers.mkdir()
            (root / "lakefile.toml").write_text(BASE_LAKEFILE, encoding="utf-8")

            def scaffold(_command: object) -> None:
                folder = papers / PAPER
                (folder / "docs").mkdir(parents=True, exist_ok=True)
                (papers / f"{PAPER}.lean").write_text(
                    f"import {PAPER}.PaperInterface\n", encoding="utf-8"
                )

            with (
                mock.patch.object(contribution, "ROOT", root),
                mock.patch.object(contribution, "PAPERS", papers),
                mock.patch.object(
                    contribution, "_run", side_effect=scaffold
                ) as runner,
            ):
                contribution._new_paper(self.new_args())

            lake = (root / "lakefile.toml").read_text(encoding="utf-8")
            self.assertIn(f'name = "{PAPER}"', lake)
            self.assertTrue(
                (papers / PAPER / "docs" / "AGENT_SOURCE_AUDIT.md").is_file()
            )
            self.assertIn(
                [
                    contribution.PYTHON,
                    "scripts/sync_paper_status.py",
                    "--paper",
                    PAPER,
                ],
                [call.args[0] for call in runner.call_args_list],
            )

    def test_new_facade_removes_only_its_partial_scaffold_after_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            papers.mkdir()
            (root / "lakefile.toml").write_text(BASE_LAKEFILE, encoding="utf-8")

            def fail_after_write(_command: object) -> None:
                (papers / PAPER).mkdir()
                (papers / f"{PAPER}.lean").write_text("partial\n")
                raise subprocess.CalledProcessError(1, ["new_paper.py"])

            with (
                mock.patch.object(contribution, "ROOT", root),
                mock.patch.object(contribution, "PAPERS", papers),
                mock.patch.object(contribution, "_run", side_effect=fail_after_write),
            ):
                with self.assertRaises(subprocess.CalledProcessError):
                    contribution._new_paper(self.new_args())

            self.assertFalse((papers / PAPER).exists())
            self.assertFalse((papers / f"{PAPER}.lean").exists())
            self.assertNotIn(PAPER, (root / "lakefile.toml").read_text())

    def test_new_facade_rolls_back_registration_after_post_install_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            papers.mkdir()
            lakefile = root / "lakefile.toml"
            lakefile.write_text(BASE_LAKEFILE, encoding="utf-8")
            original_lake = lakefile.read_bytes()

            def scaffold(_command: object) -> None:
                folder = papers / PAPER
                (folder / "docs").mkdir(parents=True, exist_ok=True)
                (papers / f"{PAPER}.lean").write_text(
                    f"import {PAPER}.PaperInterface\n", encoding="utf-8"
                )

            def fail_after_install(path: Path, paper: str) -> object:
                plan = registration.plan_paper_target_registration(path, paper)
                registration._atomic_install(plan)
                raise registration.PaperTargetRegistrationError("injected verify failure")

            with (
                mock.patch.object(contribution, "ROOT", root),
                mock.patch.object(contribution, "PAPERS", papers),
                mock.patch.object(contribution, "_run", side_effect=scaffold),
                mock.patch.object(
                    registration,
                    "register_paper_target",
                    side_effect=fail_after_install,
                ),
            ):
                with self.assertRaisesRegex(
                    contribution.ContributionError, "could not register paper target"
                ):
                    contribution._new_paper(self.new_args())

            self.assertEqual(lakefile.read_bytes(), original_lake)
            self.assertFalse((papers / PAPER).exists())
            self.assertFalse((papers / f"{PAPER}.lean").exists())

    def test_full_profile_has_no_unscoped_or_duplicate_audit_command(self) -> None:
        with mock.patch.object(
            contribution,
            "_paper_status",
            return_value={"id": PAPER, "status": "formalized"},
        ):
            commands = contribution._validation_commands(
                PAPER,
                fast=False,
                allow_missing_source_bytes=True,
            )

        self.assertEqual(
            commands[0],
            ["lake", "build", f"+{PAPER}"],
        )
        flat = [" ".join(command) for command in commands]
        closeouts = [command for command in flat if "audit_repository.py" in command]
        self.assertEqual(len(closeouts), 1)
        self.assertIn(f"--paper {PAPER}", closeouts[0])
        self.assertIn("--paper-closeout", closeouts[0])
        self.assertIn("--allow-missing-source-bytes", closeouts[0])
        self.assertIn("--no-closeout-state", closeouts[0])
        self.assertFalse(any("sync_paper_status.py --check" in command for command in flat))
        self.assertFalse(any("audit_evidence_integrity.py" in command for command in flat))
        self.assertFalse(any("audit_conclusion_provenance.py" in command for command in flat))

    def test_fast_profile_builds_only_the_interface_without_default_targets(self) -> None:
        with mock.patch.object(
            contribution,
            "_paper_status",
            return_value={"id": PAPER, "status": "formalized"},
        ):
            commands = contribution._validation_commands(
                PAPER,
                fast=True,
                allow_missing_source_bytes=True,
            )

        self.assertEqual(
            commands[0],
            ["lake", "build", f"+{PAPER}.PaperInterface"],
        )
        self.assertEqual(len(commands), 1)
        self.assertTrue(commands[0][-1].startswith("+"))

    def test_check_with_base_uses_exact_committed_diff_range(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- committed edit\n")
            fixture.commit("paper edit")
            expected_merge_base = fixture.git("merge-base", "base", "HEAD")
            expected_head = fixture.git("rev-parse", "HEAD")

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
                mock.patch.object(contribution, "_run") as runner,
                mock.patch.object(contribution, "_assert_semantically_isolated_paper"),
            ):
                contribution.check_paper(
                    EXISTING,
                    base="base",
                    fast=True,
                    allow_missing_source_bytes=True,
                )

        self.assertEqual(
            runner.call_args_list[-1].args[0],
            [
                "git",
                "diff",
                "--check",
                expected_merge_base,
                expected_head,
                "--",
                f"papers/{EXISTING}",
                f"papers/{EXISTING}.lean",
                "lakefile.toml",
                f":(exclude)papers/{EXISTING}/source/",
            ],
        )

    def test_check_with_base_rejects_a_dirty_worktree_before_commands(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- committed edit\n")
            fixture.commit("paper edit")
            interface.write_text(interface.read_text() + "\n-- dirty edit\n")

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
                mock.patch.object(contribution, "_run") as runner,
            ):
                with self.assertRaisesRegex(
                    contribution.ContributionError, "clean worktree"
                ):
                    contribution.check_paper(
                        EXISTING,
                        base="base",
                        fast=True,
                        allow_missing_source_bytes=True,
                    )

        runner.assert_not_called()

    def test_check_with_base_rejects_mutation_before_next_phase(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
            interface.write_text(interface.read_text() + "\n-- committed edit\n")
            fixture.commit("paper edit")

            def mutate_after_build(_argv: list[str], **_kwargs: object) -> None:
                interface.write_text(interface.read_text() + "\n-- runtime mutation\n")

            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
                mock.patch.object(contribution, "_run", side_effect=mutate_after_build),
                mock.patch.object(
                    contribution, "_assert_semantically_isolated_paper"
                ) as semantic,
            ):
                with self.assertRaisesRegex(
                    contribution.ContributionError,
                    "validation changed committed input bytes",
                ):
                    contribution.check_paper(
                        EXISTING,
                        base="base",
                        fast=True,
                        allow_missing_source_bytes=True,
                    )

        semantic.assert_not_called()

    def test_direct_blob_check_ignores_assume_unchanged_index_tricks(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            head = fixture.git("rev-parse", "HEAD")
            with (
                mock.patch.object(contribution, "ROOT", fixture.root),
                mock.patch.object(contribution, "PAPERS", fixture.root / "papers"),
            ):
                snapshot = contribution._committed_input_snapshot(head, EXISTING)
                interface = fixture.root / "papers" / EXISTING / "PaperInterface.lean"
                interface.write_text(interface.read_text() + "\n-- hidden edit\n")
                fixture.git(
                    "update-index",
                    "--assume-unchanged",
                    f"papers/{EXISTING}/PaperInterface.lean",
                )
                self.assertEqual(fixture.git("status", "--porcelain=v1"), "")

                with self.assertRaisesRegex(
                    contribution.ContributionError,
                    "validation changed committed input bytes",
                ):
                    contribution._require_committed_identity(
                        head,
                        inputs=snapshot,
                    )

    def test_trusted_script_digest_detects_out_of_worktree_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = GitFixture(Path(temp_dir))
            trusted = fixture.root / "trusted-scripts"
            trusted.mkdir()
            helper = trusted / "lean_import_closure.py"
            helper.write_text("TRUSTED = True\n", encoding="utf-8")
            digest = contribution._script_tree_digest(trusted)
            helper.write_text("TRUSTED = False\n", encoding="utf-8")

            with mock.patch.object(contribution, "ROOT", fixture.root):
                with self.assertRaisesRegex(
                    contribution.ContributionError,
                    "modified the trusted CI helper",
                ):
                    contribution._require_committed_identity(
                        fixture.git("rev-parse", "HEAD"),
                        trusted_scripts=(trusted, digest),
                    )

    def test_scaffold_ignores_local_source_directories_and_archives(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir) / PAPER
            paper_dir.mkdir()
            (paper_dir / ".gitignore").write_text("*.pdf\n", encoding="utf-8")

            contribution._extend_scaffold_source_ignores(paper_dir)
            first = (paper_dir / ".gitignore").read_text(encoding="utf-8")
            contribution._extend_scaffold_source_ignores(paper_dir)
            second = (paper_dir / ".gitignore").read_text(encoding="utf-8")

        self.assertIn("source_tex/", first)
        self.assertIn("sources/", first)
        self.assertIn("*.tar.*", first)
        self.assertEqual(second, first)

    def test_terminal_strict_reuse_requires_a_current_matching_receipt(self) -> None:
        identity = "d" * 64
        terminal_state = {
            "state": "complete",
            "exit_code": 0,
            "result": {
                "semantic_closeout_passed": True,
                "operational_plan_identity": identity,
            },
        }
        with (
            mock.patch.object(
                contribution, "runtime_engine_registration_error", return_value=""
            ),
            mock.patch.object(
                contribution, "closeout_worker_state_path", return_value=Path("state")
            ),
            mock.patch.object(
                contribution, "read_execution_state", return_value=(terminal_state, "")
            ),
            mock.patch.object(
                contribution,
                "load_validated_closeout_plan_receipt",
                return_value=({}, ""),
            ) as receipt,
        ):
            self.assertTrue(
                contribution._strict_closeout_completion_is_current(
                    PAPER, plan_identity=identity, deep_paper_prose=False
                )
            )

        receipt.assert_called_once_with(
            contribution.ROOT,
            paper=PAPER,
            deep_paper_prose=False,
            expected_plan_identity=identity,
        )

    def test_terminal_strict_reuse_rejects_a_stale_receipt(self) -> None:
        identity = "e" * 64
        terminal_state = {
            "state": "complete",
            "exit_code": 0,
            "result": {
                "semantic_closeout_passed": True,
                "operational_plan_identity": identity,
            },
        }
        with (
            mock.patch.object(
                contribution, "runtime_engine_registration_error", return_value=""
            ),
            mock.patch.object(
                contribution, "closeout_worker_state_path", return_value=Path("state")
            ),
            mock.patch.object(
                contribution, "read_execution_state", return_value=(terminal_state, "")
            ),
            mock.patch.object(
                contribution,
                "load_validated_closeout_plan_receipt",
                return_value=(None, "receipt inputs changed"),
            ),
        ):
            self.assertFalse(
                contribution._strict_closeout_completion_is_current(
                    PAPER, plan_identity=identity, deep_paper_prose=False
                )
            )

    def test_post_closeout_graph_loader_never_builds_the_candidate(self) -> None:
        from scripts import lean_import_closure

        with mock.patch.object(
            lean_import_closure,
            "lean_loaded_module_closure",
            return_value=((PAPER,), ""),
        ) as closure:
            loader = contribution._graph_only_lean_module_graph_loader()
            modules, error = loader(contribution.ROOT, PAPER, 17)

        self.assertEqual(modules, (PAPER,))
        self.assertEqual(error, "")
        closure.assert_called_once_with(
            contribution.ROOT,
            PAPER,
            17,
            build_entry_module=False,
        )

    def test_current_closeout_isolation_uses_the_graph_only_candidate_loader(
        self,
    ) -> None:
        from scripts import lean_import_closure

        identity = "f" * 64
        plan = {
            "plan_identity_sha256": identity,
            "next_action": {"id": "inspect_existing_closeout"},
            "last_closeout_execution": {
                "state": "complete",
                "exit_code": 0,
                "result": {
                    "semantic_closeout_passed": True,
                    "operational_plan_identity": identity,
                },
            },
        }
        captured: list[object] = []

        def capture_isolation(*_args: object, **kwargs: object) -> None:
            captured.append(kwargs["module_graph_loader"])

        with (
            mock.patch.object(
                contribution,
                "_paper_status",
                return_value={"id": PAPER, "status": "formalized"},
            ),
            mock.patch.object(contribution, "_run_json", return_value=plan),
            mock.patch.object(contribution, "_run"),
            mock.patch.object(
                contribution,
                "_assert_semantically_isolated_paper",
                side_effect=capture_isolation,
            ),
            mock.patch.object(
                lean_import_closure,
                "lean_loaded_module_closure",
                return_value=((PAPER,), ""),
            ) as closure,
        ):
            contribution.check_paper(
                PAPER,
                base=None,
                fast=False,
                allow_missing_source_bytes=False,
            )
            self.assertEqual(len(captured), 1)
            loader = captured[0]
            assert callable(loader)
            loader(contribution.ROOT, PAPER, 19)

        closure.assert_called_once_with(
            contribution.ROOT,
            PAPER,
            19,
            build_entry_module=False,
        )

    def test_planner_reuses_current_exact_success_without_rerun(self) -> None:
        identity = "a" * 64
        plan = {
            "plan_identity_sha256": identity,
            "next_action": {"id": "inspect_existing_closeout"},
            "last_closeout_execution": {
                "state": "complete",
                "exit_code": 0,
                "result": {
                    "semantic_closeout_passed": True,
                    "operational_plan_identity": identity,
                },
            },
        }
        with (
            mock.patch.object(contribution, "_run_json", return_value=plan),
            mock.patch.object(contribution, "_run") as runner,
        ):
            contribution._execute_planned_closeout(PAPER)
        runner.assert_not_called()

    def test_full_check_stops_at_source_preflight_before_build_or_isolation(self) -> None:
        source_stop = {
            "next_action": {
                "id": "review_current_source_record_delta",
                "reason": "current raw receipt needs a semantic delta review",
            }
        }
        with (
            mock.patch.object(
                contribution,
                "_paper_status",
                return_value={"id": PAPER, "status": "formalized"},
            ),
            mock.patch.object(contribution, "_run_json", return_value=source_stop),
            mock.patch.object(contribution, "_run") as runner,
            mock.patch.object(
                contribution, "_assert_semantically_isolated_paper"
            ) as semantic,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError, "review_current_source_record_delta"
            ):
                contribution.check_paper(
                    PAPER,
                    base=None,
                    fast=False,
                    allow_missing_source_bytes=False,
                )

        self.assertEqual(
            [call.args[0] for call in runner.call_args_list],
            [
                [
                    contribution.PYTHON,
                    "scripts/sync_paper_status.py",
                    "--paper",
                    PAPER,
                    "--check",
                ]
            ],
        )
        semantic.assert_not_called()

    def test_full_check_replans_after_one_paper_build(self) -> None:
        identity = "c" * 64
        build = {
            "id": "paper_build",
            "state": "ready_now",
            "argv": ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{PAPER}"],
        }
        strict = {
            "id": "strict_closeout",
            "argv": [
                "python3",
                "scripts/run_paper_closeout.py",
                "--paper",
                PAPER,
                "--plan-identity",
                identity,
            ],
        }
        plans = [
            {"next_action": build, "actions": [build]},
            {"plan_identity_sha256": identity, "next_action": strict},
        ]
        events: list[str] = []

        def record_command(argv: list[str], **_kwargs: object) -> None:
            if argv == [
                contribution.PYTHON,
                "scripts/sync_paper_status.py",
                "--paper",
                PAPER,
                "--check",
            ]:
                events.append("sync")
            elif argv == ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{PAPER}"]:
                events.append("build")
            elif argv == [
                contribution.PYTHON,
                "scripts/run_paper_closeout.py",
                "--paper",
                PAPER,
                "--plan-identity",
                identity,
            ]:
                events.append("strict")
            elif argv[:3] == ["git", "diff", "--check"]:
                events.append("diff")
            else:  # pragma: no cover - keeps the scheduling assertion exact.
                self.fail(f"unexpected command: {argv}")

        def record_isolation(*_args: object, **_kwargs: object) -> None:
            events.append("isolation")

        with (
            mock.patch.object(
                contribution,
                "_paper_status",
                return_value={"id": PAPER, "status": "formalized"},
            ),
            mock.patch.object(contribution, "_run_json", side_effect=plans),
            mock.patch.object(
                contribution, "_strict_closeout_completion_is_current", return_value=True
            ) as terminal,
            mock.patch.object(contribution, "_run", side_effect=record_command),
            mock.patch.object(
                contribution,
                "_assert_semantically_isolated_paper",
                side_effect=record_isolation,
            ),
        ):
            contribution.check_paper(
                PAPER,
                base=None,
                fast=False,
                allow_missing_source_bytes=False,
            )

        self.assertEqual(
            events,
            ["sync", "build", "isolation", "strict", "diff"],
        )
        self.assertEqual(events.count("build"), 1)
        terminal.assert_called_once_with(
            PAPER, plan_identity=identity, deep_paper_prose=False
        )

    def test_planner_runs_only_safe_actions_and_replans(self) -> None:
        identity = "b" * 64
        build = {
            "id": "paper_build",
            "state": "ready_now",
            "argv": ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{PAPER}"],
        }
        plans = [
            {
                "next_action": build,
                "actions": [build],
            },
            {
                "plan_identity_sha256": identity,
                "next_action": {
                    "id": "strict_closeout",
                    "argv": [
                        "python3",
                        "scripts/run_paper_closeout.py",
                        "--paper",
                        PAPER,
                        "--plan-identity",
                        identity,
                    ],
                }
            },
        ]
        with (
            mock.patch.object(contribution, "_run_json", side_effect=plans),
            mock.patch.object(contribution, "_run") as runner,
            mock.patch.object(
                contribution, "_strict_closeout_completion_is_current", return_value=True
            ),
        ):
            contribution._execute_planned_closeout(PAPER)
        self.assertEqual(
            [call.args[0] for call in runner.call_args_list],
            [
                ["env", "LEAN_NUM_THREADS=1", "lake", "build", f"+{PAPER}"],
                [
                    contribution.PYTHON,
                    "scripts/run_paper_closeout.py",
                    "--paper",
                    PAPER,
                    "--plan-identity",
                    identity,
                ],
            ],
        )

    def test_retired_manifest_refresh_action_fails_closed(self) -> None:
        plan = {
            "next_action": {
                "id": "fresh_manifest_batch",
                "argv": [
                    "python3",
                    "scripts/refresh_closeout_manifest_cache.py",
                    "--paper",
                    PAPER,
                ],
            }
        }
        with (
            mock.patch.object(contribution, "_run_json", return_value=plan),
            mock.patch.object(contribution, "_run") as runner,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError,
                "closeout stopped at `fresh_manifest_batch`",
            ):
                contribution._execute_planned_closeout(PAPER)
        runner.assert_not_called()

    def test_planner_stops_immediately_at_deterministic_receipt_publication_error(
        self,
    ) -> None:
        plan = {
            "operational_plan_error": "the Lean closure projection is malformed",
            "next_action": {
                "id": "replan_current_inputs",
                "retryable": False,
                "publication_disposition": "deterministic_input",
                "input_identity_sha256": "a" * 64,
                "reason": "the exact operational input snapshot could not be frozen",
            },
        }
        with (
            mock.patch.object(contribution, "_run_json", return_value=plan) as planner_run,
            mock.patch.object(contribution, "_run") as runner,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError, "deterministic_input"
            ):
                contribution._execute_planned_closeout(PAPER)

        planner_run.assert_called_once()
        runner.assert_not_called()

    def test_planner_retries_each_receipt_publication_race_identity_once(self) -> None:
        def race(identity: str) -> dict[str, object]:
            return {
                "next_action": {
                    "id": "replan_current_inputs",
                    "retryable": True,
                    "publication_disposition": "source_race",
                    "input_identity_sha256": identity,
                    "reason": "Lean source closure changed during publication",
                }
            }

        terminal_identity = "c" * 64
        terminal = {
            "plan_identity_sha256": terminal_identity,
            "next_action": {"id": "inspect_existing_closeout"},
            "last_closeout_execution": {
                "state": "complete",
                "exit_code": 0,
                "result": {
                    "semantic_closeout_passed": True,
                    "operational_plan_identity": terminal_identity,
                },
            },
        }
        with (
            mock.patch.object(
                contribution,
                "_run_json",
                side_effect=[race("a" * 64), race("b" * 64), terminal],
            ) as planner_run,
            mock.patch.object(contribution, "_run") as runner,
        ):
            contribution._execute_planned_closeout(PAPER)

        self.assertEqual(planner_run.call_count, 3)
        runner.assert_not_called()

    def test_planner_rejects_repeated_receipt_publication_race_without_new_inputs(
        self,
    ) -> None:
        race = {
            "next_action": {
                "id": "replan_current_inputs",
                "retryable": True,
                "publication_disposition": "compiled_race",
                "input_identity_sha256": "a" * 64,
                "reason": "compiled Lean closure changed during publication",
            }
        }
        with (
            mock.patch.object(
                contribution, "_run_json", side_effect=[race, race]
            ) as planner_run,
            mock.patch.object(contribution, "_run") as runner,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError, "repeated the same receipt-publication race"
            ):
                contribution._execute_planned_closeout(PAPER)

        self.assertEqual(planner_run.call_count, 2)
        runner.assert_not_called()

    def test_planner_safe_action_id_cannot_smuggle_an_arbitrary_command(self) -> None:
        plan = {
            "next_action": {
                "id": "paper_build",
                "argv": ["rm", "-rf", "papers"],
            }
        }
        with (
            mock.patch.object(contribution, "_run_json", return_value=plan),
            mock.patch.object(contribution, "_run") as runner,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError, "not canonical"
            ):
                contribution._execute_planned_closeout(PAPER)
        runner.assert_not_called()

    def test_planner_stops_at_human_semantic_review(self) -> None:
        plan = {
            "next_action": {
                "id": "inspect_invalid_semantic_items",
                "reason": "one item requires review",
                "argv": ["python3", "scripts/semantic_audit_reuse.py"],
            }
        }
        with (
            mock.patch.object(contribution, "_run_json", return_value=plan),
            mock.patch.object(contribution, "_run") as runner,
        ):
            with self.assertRaisesRegex(
                contribution.ContributionError, "inspect_invalid_semantic_items"
            ):
                contribution._execute_planned_closeout(PAPER)
        runner.assert_not_called()

    def test_partial_profile_keeps_every_command_paper_scoped(self) -> None:
        with mock.patch.object(
            contribution,
            "_paper_status",
            return_value={"id": PAPER, "status": "partially formalized"},
        ):
            commands = contribution._validation_commands(
                PAPER,
                fast=False,
                allow_missing_source_bytes=False,
            )

        for command in commands[1:]:
            self.assertIn("--paper", command)
            self.assertIn(PAPER, command)
        self.assertFalse(any("audit_repository.py" in command for command in commands))

    def test_init_spec_pins_exact_source_bytes_and_refuses_overwrite(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source = root / "source.txt"
            output = root / "statement-spec.json"
            source.write_bytes(b"Theorem 1. Exact source.\n")
            args = contribution.parse_args(
                [
                    "init-spec",
                    str(source),
                    "--version",
                    "published v1",
                    "--output",
                    str(output),
                ]
            )

            contribution._init_spec(args)
            payload = json.loads(output.read_text())
            self.assertEqual(
                payload["source_artifact_sha256"],
                hashlib.sha256(source.read_bytes()).hexdigest(),
            )
            with self.assertRaises(contribution.ContributionError):
                contribution._init_spec(args)


if __name__ == "__main__":
    unittest.main()
