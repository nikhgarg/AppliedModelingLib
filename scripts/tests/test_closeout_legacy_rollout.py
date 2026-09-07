#!/usr/bin/env python3
"""Regression tests for trusted-rollout legacy closeout adoption."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import closeout_intake_freeze as intake
from scripts.closeout_plan_receipt import content_input_snapshot


class CloseoutLegacyRolloutTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.git("init", "-q")
        self.git("config", "user.email", "fixture@example.com")
        self.git("config", "user.name", "Fixture")
        paper = self.root / "papers" / "Fixture"
        audit = paper / "audit"
        audit.mkdir(parents=True)
        (paper / "PaperInterface.lean").write_text(
            "theorem visible : True := by trivial\n", encoding="utf-8"
        )
        (self.root / "papers" / "Fixture.lean").write_text(
            "import Fixture.PaperInterface\n", encoding="utf-8"
        )
        (paper / "REPORT.md").write_text("selected\n", encoding="utf-8")
        (paper / "README.md").write_text("unselected\n", encoding="utf-8")
        (audit / "source_record_audit.json").write_text(
            json.dumps(
                {
                    "lean_import_closure": self.closure(
                        entrypoint="papers/Fixture/PaperInterface.lean",
                        modules=["Fixture.PaperInterface", "Init"],
                        sources={
                            "Fixture.PaperInterface": (
                                "papers/Fixture/PaperInterface.lean"
                            )
                        },
                        external=["Init"],
                    )
                }
            ),
            encoding="utf-8",
        )
        self.git("add", ".")
        self.git("commit", "-qm", "rollout")
        self.rollout = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=self.root,
            check=True,
            stdout=subprocess.PIPE,
            text=True,
        ).stdout.strip()

    def git(self, *args: str) -> None:
        subprocess.run(["git", *args], cwd=self.root, check=True)

    def closure(
        self,
        *,
        entrypoint: str,
        modules: list[str],
        sources: dict[str, str],
        external: list[str],
    ) -> dict[str, object]:
        source_records = []
        for module, relative in sorted(sources.items(), key=lambda item: item[1]):
            content = (self.root / relative).read_bytes()
            source_records.append(
                {
                    "module": module,
                    "path": relative,
                    "byte_length": len(content),
                    "sha256": hashlib.sha256(content).hexdigest(),
                }
            )
        controls = []
        for relative in ("lean-toolchain", "lake-manifest.json"):
            controls.append(
                {
                    "path": relative,
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": 1,
                    "sha256": "a" * 64,
                }
            )
        entry_module = (
            "Fixture.PaperInterface"
            if entrypoint.endswith("PaperInterface.lean")
            else "Fixture"
        )
        return {
            "schema": "econcslib.lean-loaded-import-closure/v2",
            "entrypoint": entrypoint,
            "entry_module": entry_module,
            "lean_loaded_modules": sorted(modules),
            "sources": source_records,
            "external_import_modules": sorted(external),
            "external_module_artifacts_sha256": "b" * 64,
            "build_controls": controls,
            "lake_routing": {
                "schema": "econcslib.entry-module-lake-routing/v2",
                "kind": "toml",
                "package_configuration": {"name": "FixturePackage"},
                "lean_library": {"name": "Fixture"},
            },
        }

    def test_selected_content_is_exact_but_unselected_prose_is_neutral(self) -> None:
        report = self.root / "papers" / "Fixture" / "REPORT.md"
        identity = content_input_snapshot(self.root, [report])[
            "papers/Fixture/REPORT.md"
        ]
        with mock.patch.object(
            intake, "INTAKE_FREEZE_LEGACY_BASELINE_COMMIT", self.rollout
        ):
            self.assertEqual(
                intake._rollout_content_input_error(
                    self.root, "papers/Fixture/REPORT.md", identity
                ),
                "",
            )
            (self.root / "papers" / "Fixture" / "README.md").write_text(
                "administrative edit\n", encoding="utf-8"
            )
            self.assertEqual(
                intake._rollout_content_input_error(
                    self.root, "papers/Fixture/REPORT.md", identity
                ),
                "",
            )
            report.write_text("changed selected input\n", encoding="utf-8")
            changed = content_input_snapshot(self.root, [report])[
                "papers/Fixture/REPORT.md"
            ]
            self.assertIn(
                "differs from rollout",
                intake._rollout_content_input_error(
                    self.root, "papers/Fixture/REPORT.md", changed
                ),
            )

    def test_rollout_lean_graph_detects_lost_repository_ownership(self) -> None:
        current = self.closure(
            entrypoint="papers/Fixture.lean",
            modules=["Fixture", "Fixture.PaperInterface", "Init"],
            sources={
                "Fixture": "papers/Fixture.lean",
                "Fixture.PaperInterface": "papers/Fixture/PaperInterface.lean",
            },
            external=["Init"],
        )
        lost = self.closure(
            entrypoint="papers/Fixture.lean",
            modules=["Fixture", "Fixture.PaperInterface", "Init"],
            sources={"Fixture": "papers/Fixture.lean"},
            external=["Fixture.PaperInterface", "Init"],
        )
        added_external = self.closure(
            entrypoint="papers/Fixture.lean",
            modules=[
                "Fixture",
                "Fixture.PaperInterface",
                "Init",
                "NewPackage.Runtime",
            ],
            sources={
                "Fixture": "papers/Fixture.lean",
                "Fixture.PaperInterface": "papers/Fixture/PaperInterface.lean",
            },
            external=["Init", "NewPackage.Runtime"],
        )
        with mock.patch.object(
            intake, "INTAKE_FREEZE_LEGACY_BASELINE_COMMIT", self.rollout
        ):
            self.assertEqual(
                intake._rollout_graph_errors(self.root, "Fixture", current), []
            )
            errors = intake._rollout_graph_errors(self.root, "Fixture", lost)
            added_errors = intake._rollout_graph_errors(
                self.root, "Fixture", added_external
            )
        self.assertTrue(
            any("Fixture.PaperInterface" in error for error in errors), errors
        )
        self.assertTrue(
            any("NewPackage.Runtime" in error for error in added_errors), added_errors
        )


if __name__ == "__main__":
    unittest.main()
