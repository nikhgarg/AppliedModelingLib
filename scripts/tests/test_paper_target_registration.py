#!/usr/bin/env python3
"""Focused tests for append-only paper target registration."""

from __future__ import annotations

import copy
import json
import os
import stat
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import paper_target_registration as registration
from scripts.tomllib_compat import tomllib


BASE_LAKEFILE = """name = "FixturePackage"
version = "1.2.3"
defaultTargets = ["AppliedModelingLib", "Existing24Paper"]

[leanOptions]
relaxedAutoImplicit = false

[[lean_lib]]
name = "AppliedModelingLib"

[[lean_lib]]
name = "Existing24Paper"
srcDir = "papers"
"""


class PaperTargetRegistrationTests(unittest.TestCase):
    def fixture(self, root: Path, content: str = BASE_LAKEFILE) -> Path:
        lakefile = root / "lakefile.toml"
        lakefile.write_text(content, encoding="utf-8")
        return lakefile

    def test_plan_is_append_only_and_preserves_all_existing_toml_content(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            original = lakefile.read_bytes()
            original_payload = tomllib.loads(original.decode("utf-8"))

            plan = registration.plan_paper_target_registration(
                lakefile, "ABC26EfficientPaper"
            )

            self.assertEqual(lakefile.read_bytes(), original)
            self.assertTrue(plan.rendered_bytes.startswith(original))
            self.assertEqual(
                plan.rendered_bytes[len(original) :],
                b'\n[[lean_lib]]\nname = "ABC26EfficientPaper"\nsrcDir = "papers"\n',
            )
            expected = copy.deepcopy(original_payload)
            expected["lean_lib"].append(
                {"name": "ABC26EfficientPaper", "srcDir": "papers"}
            )
            self.assertEqual(plan.rendered_payload, expected)
            self.assertEqual(
                plan.rendered_payload["defaultTargets"],
                original_payload["defaultTargets"],
            )

    def test_exact_addition_rejects_semantically_equal_or_extra_rewrites(self) -> None:
        canonical = (
            BASE_LAKEFILE
            + '\n[[lean_lib]]\nname = "ABC26EfficientPaper"\n'
            + 'srcDir = "papers"\n'
        )
        self.assertTrue(
            registration.registration_is_exact_addition(
                BASE_LAKEFILE, canonical, "ABC26EfficientPaper"
            )
        )
        self.assertFalse(
            registration.registration_is_exact_addition(
                BASE_LAKEFILE,
                canonical + "# unrelated candidate rewrite\n",
                "ABC26EfficientPaper",
            )
        )
        reformatted = canonical.replace('version = "1.2.3"', 'version="1.2.3"')
        self.assertFalse(
            registration.registration_is_exact_addition(
                BASE_LAKEFILE, reformatted, "ABC26EfficientPaper"
            )
        )

    def test_register_replaces_atomically_and_preserves_file_mode(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            lakefile = self.fixture(root)
            lakefile.chmod(0o640)

            plan = registration.register_paper_target(
                lakefile, "ABC26EfficientPaper"
            )

            self.assertEqual(lakefile.read_bytes(), plan.rendered_bytes)
            self.assertEqual(stat.S_IMODE(lakefile.stat().st_mode), 0o640)
            self.assertEqual(
                list(root.glob(".lakefile.toml.registration-*")), []
            )
            payload = tomllib.loads(lakefile.read_text(encoding="utf-8"))
            self.assertEqual(
                payload["lean_lib"][-1],
                {"name": "ABC26EfficientPaper", "srcDir": "papers"},
            )
            self.assertEqual(
                payload["defaultTargets"], ["AppliedModelingLib", "Existing24Paper"]
            )

    def test_plan_rejects_invalid_paper_ids(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            for paper_id in (
                "lower26Paper",
                "ABC26",
                "ABC26paper",
                "ABC26Paper/Elsewhere",
                "ABC26Paper-Name",
                "",
            ):
                with self.subTest(paper_id=paper_id):
                    with self.assertRaisesRegex(
                        registration.PaperTargetRegistrationError,
                        "paper id must match",
                    ):
                        registration.plan_paper_target_registration(lakefile, paper_id)

    def test_plan_rejects_existing_and_conflicting_target(self) -> None:
        cases = {
            "duplicate": BASE_LAKEFILE,
            "conflict": BASE_LAKEFILE.replace(
                'name = "Existing24Paper"\nsrcDir = "papers"',
                'name = "Existing24Paper"\nsrcDir = "other"',
            ),
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            for label, content in cases.items():
                with self.subTest(label=label):
                    lakefile = self.fixture(root, content)
                    before = lakefile.read_bytes()
                    with self.assertRaisesRegex(
                        registration.PaperTargetRegistrationError,
                        "already registered|conflicts",
                    ):
                        registration.plan_paper_target_registration(
                            lakefile, "Existing24Paper"
                        )
                    self.assertEqual(lakefile.read_bytes(), before)

    def test_plan_rejects_preexisting_duplicate_or_case_conflicting_targets(self) -> None:
        duplicate = (
            BASE_LAKEFILE
            + '\n[[lean_lib]]\nname = "AppliedModelingLib"\nsrcDir = "duplicate"\n'
        )
        case_conflict = (
            BASE_LAKEFILE
            + '\n[[lean_lib]]\nname = "aPPLIEDmODELINGlIB"\nsrcDir = "duplicate"\n'
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            for label, content in (
                ("duplicate", duplicate),
                ("case conflict", case_conflict),
            ):
                with self.subTest(label=label):
                    lakefile = self.fixture(root, content)
                    with self.assertRaisesRegex(
                        registration.PaperTargetRegistrationError,
                        "duplicate|case-conflicting",
                    ):
                        registration.plan_paper_target_registration(
                            lakefile, "ABC26EfficientPaper"
                        )

    def test_plan_rejects_malformed_toml_and_symlinked_lakefile(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            malformed = self.fixture(root, "name = [\n")
            with self.assertRaisesRegex(
                registration.PaperTargetRegistrationError, "not valid TOML"
            ):
                registration.plan_paper_target_registration(
                    malformed, "ABC26EfficientPaper"
                )

            target = root / "real.toml"
            target.write_text(BASE_LAKEFILE, encoding="utf-8")
            link = root / "linked.toml"
            link.symlink_to(target.name)
            with self.assertRaisesRegex(
                registration.PaperTargetRegistrationError, "symlinked"
            ):
                registration.plan_paper_target_registration(
                    link, "ABC26EfficientPaper"
                )

    def test_register_detects_mutation_after_planning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            lakefile = self.fixture(root)
            plan = registration.plan_paper_target_registration(
                lakefile, "ABC26EfficientPaper"
            )
            lakefile.write_text(BASE_LAKEFILE + "\n# concurrent edit\n", encoding="utf-8")

            with self.assertRaisesRegex(
                registration.PaperTargetRegistrationError,
                "changed after registration planning",
            ):
                registration._atomic_install(plan)

            self.assertIn("concurrent edit", lakefile.read_text(encoding="utf-8"))
            self.assertEqual(
                list(root.glob(".lakefile.toml.registration-*")), []
            )

    def test_registration_rollback_restores_exact_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            original = lakefile.read_bytes()
            plan = registration.register_paper_target(
                lakefile, "ABC26EfficientPaper"
            )

            registration.restore_paper_target_registration(plan)

            self.assertEqual(lakefile.read_bytes(), original)

    def test_registration_rollback_refuses_a_concurrent_edit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            plan = registration.register_paper_target(
                lakefile, "ABC26EfficientPaper"
            )
            lakefile.write_text(
                lakefile.read_text(encoding="utf-8") + "# concurrent\n",
                encoding="utf-8",
            )

            with self.assertRaisesRegex(
                registration.PaperTargetRegistrationError, "refusing rollback"
            ):
                registration.restore_paper_target_registration(plan)

    def test_atomic_replace_failure_leaves_original_and_removes_temporary_file(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            lakefile = self.fixture(root)
            before = lakefile.read_bytes()
            plan = registration.plan_paper_target_registration(
                lakefile, "ABC26EfficientPaper"
            )

            with mock.patch.object(os, "replace", side_effect=OSError("injected")):
                with self.assertRaisesRegex(OSError, "injected"):
                    registration._atomic_install(plan)

            self.assertEqual(lakefile.read_bytes(), before)
            self.assertEqual(
                list(root.glob(".lakefile.toml.registration-*")), []
            )

    def test_cli_plan_is_machine_readable_and_does_not_write(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            before = lakefile.read_bytes()
            with mock.patch("builtins.print") as printer:
                result = registration.main(
                    [
                        "plan",
                        "ABC26EfficientPaper",
                        "--lakefile",
                        str(lakefile),
                    ]
                )

            self.assertEqual(result, 0)
            self.assertEqual(lakefile.read_bytes(), before)
            payload = json.loads(printer.call_args.args[0])
            self.assertEqual(payload["paper"], "ABC26EfficientPaper")
            self.assertEqual(payload["action"], "append_registration")
            self.assertFalse(payload["written"])
            self.assertFalse(payload["default_targets_changed"])

    def test_integration_build_includes_every_registered_target(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            with mock.patch.object(
                registration.subprocess,
                "run",
                return_value=mock.Mock(returncode=0, stdout="", stderr=""),
            ) as runner:
                result = registration.build_registered_targets(lakefile)

        self.assertEqual(result, 0)
        runner.assert_called_once_with(
            ["lake", "-q", "build", "AppliedModelingLib", "Existing24Paper"],
            cwd=lakefile.resolve().parent,
            capture_output=True,
            text=True,
            check=False,
        )

    def test_integration_build_rejects_zero_exit_panic_without_replaying_log(self) -> None:
        panic = (
            "warning: ordinary linter\n"
            "PANIC at Lean.Expr.appArg! Lean.Expr:926:15: application expected\n"
            "backtrace:\nvery long frame\n"
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir))
            with mock.patch.object(
                registration.subprocess,
                "run",
                return_value=mock.Mock(returncode=0, stdout=panic, stderr=""),
            ), mock.patch("sys.stderr") as error_stream:
                result = registration.build_registered_targets(lakefile)

        self.assertEqual(result, 1)
        rendered = " ".join(
            str(call.args[0]) for call in error_stream.write.call_args_list if call.args
        )
        self.assertIn("Lean PANIC output", rendered)
        self.assertIn("PANIC at Lean.Expr.appArg!", rendered)
        self.assertNotIn("ordinary linter", rendered)

    def test_integration_build_does_not_trust_default_targets(self) -> None:
        content = BASE_LAKEFILE.replace(
            'defaultTargets = ["AppliedModelingLib", "Existing24Paper"]',
            'defaultTargets = ["AppliedModelingLib"]',
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            lakefile = self.fixture(Path(temp_dir), content)

            self.assertEqual(
                registration.registered_target_names(lakefile),
                ("AppliedModelingLib", "Existing24Paper"),
            )


if __name__ == "__main__":
    unittest.main()
