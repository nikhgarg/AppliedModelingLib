#!/usr/bin/env python3
"""Regression tests for source-complete paper checkpoint elaboration."""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import paper_module_elaboration
from scripts import private_paper_checkpoint as checkpoint
from scripts.current_closeout import runtime_api
from scripts.paper_module_elaboration import (
    PaperModuleElaborationError,
    rehashed_module_build_command,
    tracked_paper_module_sources,
)


class PaperModuleSourceTests(unittest.TestCase):
    def test_build_command_is_path_safe_and_single_owned(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            sources = [root / "papers" / "Fixture.lean"]
            self.assertEqual(
                rehashed_module_build_command(
                    root,
                    sources,
                    single_threaded=True,
                ),
                [
                    "env",
                    "LEAN_NUM_THREADS=1",
                    "lake",
                    "--rehash",
                    "build",
                    "papers/Fixture.lean",
                ],
            )
            with self.assertRaisesRegex(
                PaperModuleElaborationError,
                "outside the repository",
            ):
                rehashed_module_build_command(
                    root,
                    [root.parent / "Outside.lean"],
                    single_threaded=True,
                )

    def test_enumerates_every_tracked_paper_source_not_only_root(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            papers = root / "papers"
            paper = "Fixture"
            folder = papers / paper
            (folder / "Proofs").mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (folder / "ProofInterface.lean").write_text("", encoding="utf-8")
            (folder / "Assumptions.lean").write_text("", encoding="utf-8")
            (folder / "Proofs" / "Step.lean").write_text("", encoding="utf-8")
            (papers / f"{paper}.lean").write_text("", encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "paper_interface": {
                            "path": f"papers/{paper}/PaperInterface.lean"
                        }
                    }
                ),
                encoding="utf-8",
            )
            git_output = "\n".join(
                [
                    f"papers/{paper}.lean",
                    f"papers/{paper}/Assumptions.lean",
                    f"papers/{paper}/PaperInterface.lean",
                    f"papers/{paper}/ProofInterface.lean",
                    f"papers/{paper}/Proofs/Step.lean",
                ]
            )
            old_root, old_papers = checkpoint.ROOT, checkpoint.PAPERS
            checkpoint.ROOT, checkpoint.PAPERS = root, papers
            self.addCleanup(setattr, checkpoint, "ROOT", old_root)
            self.addCleanup(setattr, checkpoint, "PAPERS", old_papers)
            with mock.patch.object(
                checkpoint.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    args=["git", "ls-files"], returncode=0, stdout=git_output
                ),
            ) as run:
                sources = checkpoint.paper_module_sources(folder, paper)
            self.assertEqual(
                [checkpoint.rel(source) for source in sources],
                [
                    "papers/Fixture.lean",
                    "papers/Fixture/Assumptions.lean",
                    "papers/Fixture/PaperInterface.lean",
                    "papers/Fixture/ProofInterface.lean",
                    "papers/Fixture/Proofs/Step.lean",
                ],
            )
            self.assertEqual(run.call_args.args[0][:3], ["git", "ls-files", "--"])

    def test_colocated_proof_endpoints_need_no_proofinterface_file(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text("", encoding="utf-8")
            (root / "papers" / "Fixture.lean").write_text("", encoding="utf-8")
            tracked = "\n".join(
                [
                    "papers/Fixture.lean",
                    "papers/Fixture/PaperInterface.lean",
                ]
            )
            with mock.patch.object(
                paper_module_elaboration.subprocess,
                "run",
                return_value=subprocess.CompletedProcess(
                    args=["git", "ls-files"], returncode=0, stdout=tracked
                ),
            ):
                sources = tracked_paper_module_sources(root, "Fixture")
            self.assertEqual(
                [path.relative_to(root).as_posix() for path in sources],
                ["papers/Fixture.lean", "papers/Fixture/PaperInterface.lean"],
            )

    def test_main_elaborates_paper_and_explicit_shared_lean_sources(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            papers = root / "papers"
            paper = "Fixture"
            folder = papers / paper
            shared = root / "AppliedModelingLib" / "Shared.lean"
            folder.mkdir(parents=True)
            shared.parent.mkdir(parents=True)
            shared.write_text("", encoding="utf-8")

            old_root, old_papers = checkpoint.ROOT, checkpoint.PAPERS
            checkpoint.ROOT, checkpoint.PAPERS = root, papers
            self.addCleanup(setattr, checkpoint, "ROOT", old_root)
            self.addCleanup(setattr, checkpoint, "PAPERS", old_papers)
            sources = [
                papers / f"{paper}.lean",
                folder / "Assumptions.lean",
                folder / "PaperInterface.lean",
            ]
            with mock.patch.object(
                checkpoint, "paper_module_sources", return_value=sources
            ), mock.patch.object(
                checkpoint, "run", return_value=subprocess.CompletedProcess([], 0)
            ) as run, mock.patch.object(
                checkpoint.sys,
                "argv",
                [
                    "private_paper_checkpoint.py",
                    paper,
                    "--include-path",
                    "AppliedModelingLib/Shared.lean",
                ],
            ):
                self.assertEqual(checkpoint.main(), 0)

            commands = [call.args[0] for call in run.call_args_list]
            self.assertEqual(
                commands[0],
                [
                    "lake",
                    "--rehash",
                    "build",
                    "papers/Fixture.lean",
                    "papers/Fixture/Assumptions.lean",
                    "papers/Fixture/PaperInterface.lean",
                    "AppliedModelingLib/Shared.lean",
                ],
            )


class CurrentCloseoutModuleElaborationTests(unittest.TestCase):
    def test_strict_closeout_elaborates_every_tracked_source(self) -> None:
        sources = (
            runtime_api.ROOT / "papers" / "Fixture" / "PaperInterface.lean",
            runtime_api.ROOT / "papers" / "Fixture" / "ProofInterface.lean",
            runtime_api.ROOT / "papers" / "Fixture.lean",
        )
        completed = subprocess.CompletedProcess([], 0, stdout="", stderr="")
        with (
            mock.patch.object(
                runtime_api,
                "tracked_paper_module_sources",
                return_value=sources,
            ),
            mock.patch.object(
                runtime_api.subprocess,
                "run",
                return_value=completed,
            ) as run,
        ):
            self.assertEqual(
                runtime_api.check_paper_root_build_closeout("Fixture"), []
            )
        self.assertEqual(run.call_count, 1)
        self.assertEqual(
            run.call_args.args[0],
            [
                "env",
                "LEAN_NUM_THREADS=1",
                "lake",
                "--rehash",
                "build",
                *(source.relative_to(runtime_api.ROOT).as_posix() for source in sources),
            ],
        )

    def test_inventory_failure_stops_before_lean(self) -> None:
        with (
            mock.patch.object(
                runtime_api,
                "tracked_paper_module_sources",
                side_effect=PaperModuleElaborationError("missing ProofInterface"),
            ),
            mock.patch.object(runtime_api.subprocess, "run") as run,
        ):
            findings = runtime_api.check_paper_root_build_closeout("Fixture")
        self.assertEqual(len(findings), 1)
        self.assertIn("missing ProofInterface", findings[0].message)
        run.assert_not_called()

    def test_zero_exit_panic_in_any_module_fails_closeout(self) -> None:
        source = runtime_api.ROOT / "papers" / "Fixture" / "ProofInterface.lean"
        completed = subprocess.CompletedProcess(
            [],
            0,
            stdout="",
            stderr="PANIC at Lean.Expr.appArg!\nbacktrace:\n...",
        )
        with (
            mock.patch.object(
                runtime_api,
                "tracked_paper_module_sources",
                return_value=(source,),
            ),
            mock.patch.object(runtime_api.subprocess, "run", return_value=completed),
        ):
            findings = runtime_api.check_paper_root_build_closeout("Fixture")
        self.assertEqual(len(findings), 1)
        self.assertIn("Lean PANIC output", findings[0].message)


if __name__ == "__main__":
    unittest.main()
