#!/usr/bin/env python3
"""Regression tests for the prospective formalization-engine revision guard."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.check_formalization_engine_revision import (
    BOUNDARY_ID,
    RELATION_COMPATIBLE,
    CandidateBlob,
    EngineRevisionError,
    GitCandidateView,
    bootstrap_payload,
    engine_tree_digest,
    formalization_review_protocol_digest,
    is_engine_source_path,
    updated_payload,
    validate_append_only_history,
    validate_revision_ledger,
    validated_recorded_engine_revision_ledger,
    validate_runtime_engine_registration,
)
from scripts.formalization_protocol import (
    formalization_review_protocol_digest as authoritative_review_protocol_digest,
)
from scripts.legacy_v10_trust_ledger import ENGINE_SOURCE_PATHS
from scripts.theorem_realization_transition import MATERIAL_ARTIFACT_PATHS
from scripts.source_record_raw_producer_compatibility import (
    RAW_PRODUCER_COMPATIBILITY_INVARIANT,
)


ROOT = Path(__file__).resolve().parents[2]


def blob(path: str, content: bytes, *, mode: str = "100644") -> CandidateBlob:
    return CandidateBlob(path=path, mode=mode, oid="unused", content=content)


def raw_producer_identities(label: str) -> list[dict[str, str]]:
    return [
        {
            "path": "scripts/lean_signature_manifest_helper.lean",
            "sha256": "a" * 63 + label,
            "status": "present",
        },
        {
            "path": (
                "skills/econcs-formalizer/scripts/"
                "source_record_audit.py#fresh-raw-generation"
            ),
            "sha256": "b" * 63 + label,
            "status": "present",
        },
    ]


def raw_producer_compatibility_grant() -> dict[str, object]:
    return {
        "schema": 1,
        "invariant": RAW_PRODUCER_COMPATIBILITY_INVARIANT,
        "predecessor_raw_producer_code_identity_sets": [
            raw_producer_identities("1")
        ],
        "successor_raw_producer_code_identities": raw_producer_identities("2"),
    }


class FormalizationEngineRevisionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.engine_v1 = engine_tree_digest(
            [blob("scripts/audit_repository.py", b"result = 1\n")]
        )[0]
        self.engine_v2 = engine_tree_digest(
            [blob("scripts/audit_repository.py", b"result = int(1)\n")]
        )[0]
        self.protocol_v1 = "a" * 64
        self.protocol_v2 = "b" * 64

    def bootstrap(self) -> dict[str, object]:
        return bootstrap_payload(
            engine_sha256=self.engine_v1,
            protocol_sha256=self.protocol_v1,
            file_count=1,
        )

    def initialize_runtime_repository(self, root: Path) -> tuple[Path, dict[str, object]]:
        subprocess.run(["git", "init", "-q"], cwd=root, check=True)
        subprocess.run(
            ["git", "config", "user.email", "fixture@example.com"],
            cwd=root,
            check=True,
        )
        subprocess.run(
            ["git", "config", "user.name", "Fixture"], cwd=root, check=True
        )
        source = root / "scripts" / "engine.py"
        source.parent.mkdir(parents=True)
        source.write_text("value = 1\n", encoding="utf-8")
        protocol = {
            "schema": 1,
            "audit_versions": {},
            "coverage": {"normal_mode": {"rule": "Fixture prose."}},
            "reuse": {"semantic_engine_epoch": "fixture-v1"},
            "classification": {},
            "pacing": {"rule": "Fixture prose."},
        }
        config = root / "config"
        config.mkdir()
        (config / "formalization_audit_protocol.json").write_text(
            json.dumps(protocol, indent=2) + "\n", encoding="utf-8"
        )
        protocol_digest = formalization_review_protocol_digest(protocol)
        engine_digest = engine_tree_digest(
            [blob("scripts/engine.py", source.read_bytes())]
        )[0]
        ledger = bootstrap_payload(
            engine_sha256=engine_digest,
            protocol_sha256=protocol_digest,
            file_count=1,
        )
        (config / "formalization_engine_revisions.json").write_text(
            json.dumps(ledger, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        (root / ".gitignore").write_text("scripts/ignored.py\n", encoding="utf-8")
        subprocess.run(["git", "add", "."], cwd=root, check=True)
        subprocess.run(["git", "commit", "-qm", "baseline"], cwd=root, check=True)
        return source, protocol

    def test_boundary_is_location_based_and_automatically_includes_guard(self) -> None:
        self.assertTrue(
            is_engine_source_path("scripts/check_formalization_engine_revision.py")
        )
        self.assertTrue(
            is_engine_source_path(
                "skills/econcs-formalizer/scripts/source_record_audit.py"
            )
        )
        self.assertTrue(is_engine_source_path("scripts/helper.lean"))
        self.assertTrue(
            is_engine_source_path("AppliedModelingLib/Audit/SignatureManifest.lean")
        )
        self.assertTrue(is_engine_source_path("lakefile.toml"))
        self.assertFalse(
            is_engine_source_path("scripts/tests/test_formalization_engine_revision.py")
        )
        self.assertFalse(
            is_engine_source_path("scripts/public_release_candidate_guard.py")
        )
        self.assertFalse(
            is_engine_source_path("scripts/public_release_projection.py")
        )
        self.assertFalse(is_engine_source_path("docs/audit_repository.py"))

    def test_guard_state_is_not_paper_semantic_evidence(self) -> None:
        self.assertNotIn(
            "scripts/check_formalization_engine_revision.py", ENGINE_SOURCE_PATHS
        )
        self.assertNotIn(
            "config/formalization_engine_revisions.json", MATERIAL_ARTIFACT_PATHS
        )

    def test_engine_identity_observes_content_path_mode_addition_and_deletion(
        self,
    ) -> None:
        original = [blob("scripts/a.py", b"x = 1\n")]
        original_digest = engine_tree_digest(original)[0]
        variants = (
            [blob("scripts/a.py", b"x = 2\n")],
            [blob("scripts/b.py", b"x = 1\n")],
            [blob("scripts/a.py", b"x = 1\n", mode="100755")],
            [*original, blob("scripts/b.py", b"y = 1\n")],
        )
        for candidate in variants:
            with self.subTest(candidate=candidate):
                self.assertNotEqual(engine_tree_digest(candidate)[0], original_digest)

    def test_paper_lake_target_does_not_change_engine_identity(self) -> None:
        common = b'''[leanOptions]\nrelaxedAutoImplicit = false\n\n[[require]]\nname = "mathlib"\nrev = "v1"\n\n[[lean_lib]]\nname = "AppliedModelingLib"\n\n[[lean_lib]]\nname = "AppliedModelingLibAuditScripts"\nsrcDir = "scripts"\n\n'''
        first = common + b'''[[lean_lib]]\nname = "PaperOne"\nsrcDir = "papers"\n'''
        second = first + b'''\n[[lean_lib]]\nname = "PaperTwo"\nsrcDir = "papers"\n'''
        self.assertEqual(
            engine_tree_digest([blob("lakefile.toml", first)]),
            engine_tree_digest([blob("lakefile.toml", second)]),
        )

    def test_audit_lake_configuration_changes_engine_identity(self) -> None:
        original = b'''[leanOptions]\nrelaxedAutoImplicit = false\n\n[[require]]\nname = "mathlib"\nrev = "v1"\n\n[[lean_lib]]\nname = "AppliedModelingLib"\n\n[[lean_lib]]\nname = "AppliedModelingLibAuditScripts"\nsrcDir = "scripts"\n'''
        changed = original.replace(b'rev = "v1"', b'rev = "v2"')
        self.assertNotEqual(
            engine_tree_digest([blob("lakefile.toml", original)]),
            engine_tree_digest([blob("lakefile.toml", changed)]),
        )

    def test_protocol_projection_matches_authoritative_digest(self) -> None:
        payload = json.loads(
            (ROOT / "config" / "formalization_audit_protocol.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(
            formalization_review_protocol_digest(payload),
            authoritative_review_protocol_digest(payload),
        )

    def test_protocol_prose_is_neutral_but_structured_policy_is_not(self) -> None:
        payload = json.loads(
            (ROOT / "config" / "formalization_audit_protocol.json").read_text(
                encoding="utf-8"
            )
        )
        original = formalization_review_protocol_digest(payload)
        prose = copy.deepcopy(payload)
        prose["pacing"]["rule"] += " Clarified."
        prose["coverage"]["normal_mode"]["rule"] += " Clarified."
        prose["audit_versions"]["source_record"]["meaning"] += " Clarified."
        self.assertEqual(formalization_review_protocol_digest(prose), original)

        structured = copy.deepcopy(payload)
        structured["reuse"]["semantic_engine_epoch"] = "fixture-v2"
        self.assertNotEqual(formalization_review_protocol_digest(structured), original)

    def test_unchanged_registered_candidate_passes(self) -> None:
        validate_revision_ledger(
            self.bootstrap(),
            current_engine_sha256=self.engine_v1,
            current_protocol_sha256=self.protocol_v1,
        )

    def test_cli_can_inspect_an_explicit_repository_from_trusted_checkout(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.initialize_runtime_repository(root)
            command = [
                "python3",
                str(ROOT / "scripts" / "check_formalization_engine_revision.py"),
                "--repo",
                str(root),
                "--tree",
                "HEAD",
                "--show-current",
            ]
            result = subprocess.run(
                command,
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        payload = json.loads(result.stdout)
        self.assertEqual(payload["engine_file_count"], 1)

    def test_unregistered_engine_or_protocol_change_fails(self) -> None:
        for engine, protocol in (
            (self.engine_v2, self.protocol_v1),
            (self.engine_v1, self.protocol_v2),
        ):
            with self.subTest(engine=engine, protocol=protocol):
                with self.assertRaises(EngineRevisionError):
                    validate_revision_ledger(
                        self.bootstrap(),
                        current_engine_sha256=engine,
                        current_protocol_sha256=protocol,
                    )

    def test_engine_only_change_gets_an_independent_registration(self) -> None:
        updated = updated_payload(
            self.bootstrap(),
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v1,
            rationale=(
                "This refactor preserves the semantic review decision contract."
            ),
            verification=["focused compatibility regression"],
        )
        revision = updated["revisions"][-1]
        self.assertNotIn("relation_to_previous", revision)
        self.assertNotIn("previous_engine_tree_sha256", revision)
        validate_revision_ledger(
            updated,
            current_engine_sha256=self.engine_v2,
            current_protocol_sha256=self.protocol_v1,
        )

        invalid = copy.deepcopy(updated)
        invalid["revisions"][-1]["previous_engine_tree_sha256"] = self.engine_v1
        with self.assertRaisesRegex(EngineRevisionError, "fields are malformed"):
            validate_revision_ledger(
                invalid,
                current_engine_sha256=self.engine_v2,
                current_protocol_sha256=self.protocol_v1,
            )

    def test_independent_registration_rejects_pairwise_raw_producer_grant(
        self,
    ) -> None:
        updated = updated_payload(
            self.bootstrap(),
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v1,
            rationale="The implementation keeps reviewed raw-obligation semantics.",
            verification=["raw-producer compatibility grant regression"],
        )
        updated["revisions"][-1]["raw_producer_compatibility"] = (
            raw_producer_compatibility_grant()
        )
        with self.assertRaisesRegex(
            EngineRevisionError, "cannot carry a pairwise raw-producer"
        ):
            validate_revision_ledger(
                updated,
                current_engine_sha256=self.engine_v2,
                current_protocol_sha256=self.protocol_v1,
            )

    def test_protocol_change_gets_an_independent_registration(self) -> None:
        updated = updated_payload(
            self.bootstrap(),
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v2,
            rationale="The accepted semantic review contract changes materially.",
            verification=["semantic transition regression"],
        )
        revision = updated["revisions"][-1]
        self.assertNotIn("relation_to_previous", revision)
        self.assertEqual(
            revision["formalization_review_protocol_sha256"], self.protocol_v2
        )
        validate_revision_ledger(
            updated,
            current_engine_sha256=self.engine_v2,
            current_protocol_sha256=self.protocol_v2,
        )

        invalid = copy.deepcopy(updated)
        invalid["revisions"][-1]["engine_tree_sha256"] = self.engine_v1
        invalid["revisions"][-1]["formalization_review_protocol_sha256"] = (
            self.protocol_v1
        )
        with self.assertRaisesRegex(EngineRevisionError, "duplicates an existing"):
            validate_revision_ledger(
                invalid,
                current_engine_sha256=self.engine_v2,
                current_protocol_sha256=self.protocol_v1,
            )

    def test_legacy_chain_link_and_second_bootstrap_fail_closed(self) -> None:
        updated = {
            "schema": 1,
            "boundary": BOUNDARY_ID,
            "revisions": [
                {
                    "sequence": 1,
                    "engine_tree_sha256": self.engine_v1,
                    "formalization_review_protocol_sha256": self.protocol_v1,
                    "relation_to_previous": "bootstrap",
                    "rationale": "Legacy bootstrap remains immutable provenance.",
                    "verification": ["legacy bootstrap regression"],
                },
                {
                    "sequence": 2,
                    "engine_tree_sha256": self.engine_v2,
                    "formalization_review_protocol_sha256": self.protocol_v1,
                    "relation_to_previous": RELATION_COMPATIBLE,
                    "previous_engine_tree_sha256": self.engine_v1,
                    "previous_formalization_review_protocol_sha256": self.protocol_v1,
                    "rationale": "Legacy linked history remains strictly validated.",
                    "verification": ["legacy link regression"],
                },
            ],
        }
        broken = copy.deepcopy(updated)
        broken["revisions"][-1]["previous_engine_tree_sha256"] = "c" * 64
        with self.assertRaisesRegex(EngineRevisionError, "does not link"):
            validate_revision_ledger(
                broken,
                current_engine_sha256=self.engine_v2,
                current_protocol_sha256=self.protocol_v1,
            )

        second_bootstrap = copy.deepcopy(updated)
        revision = second_bootstrap["revisions"][-1]
        revision["relation_to_previous"] = "bootstrap"
        revision.pop("previous_engine_tree_sha256")
        revision.pop("previous_formalization_review_protocol_sha256")
        with self.assertRaisesRegex(EngineRevisionError, "another bootstrap"):
            validate_revision_ledger(
                second_bootstrap,
                current_engine_sha256=self.engine_v2,
                current_protocol_sha256=self.protocol_v1,
            )

    def test_empty_prospective_placeholder_is_not_acceptance(self) -> None:
        with self.assertRaisesRegex(EngineRevisionError, "no registered bootstrap"):
            validate_revision_ledger(
                {"schema": 1, "boundary": BOUNDARY_ID, "revisions": []},
                current_engine_sha256=self.engine_v1,
                current_protocol_sha256=self.protocol_v1,
            )

    def test_accepted_history_must_be_extended_not_rebootstrapped(self) -> None:
        base = self.bootstrap()
        appended = updated_payload(
            base,
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v1,
            rationale="The implementation changes but review meaning is preserved.",
            verification=["focused compatibility regression"],
        )
        validate_append_only_history(appended, base)

        replacement = bootstrap_payload(
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v1,
            file_count=1,
        )
        with self.assertRaisesRegex(EngineRevisionError, "rewritten"):
            validate_append_only_history(replacement, base)

        placeholder = {"schema": 1, "boundary": BOUNDARY_ID, "revisions": []}
        validate_append_only_history(base, placeholder)

    def test_legacy_history_migrates_once_to_independent_authorities(self) -> None:
        legacy = {
            "schema": 1,
            "boundary": BOUNDARY_ID,
            "revisions": [
                {
                    "sequence": 1,
                    "engine_tree_sha256": self.engine_v1,
                    "formalization_review_protocol_sha256": self.protocol_v1,
                    "relation_to_previous": "bootstrap",
                    "rationale": "Legacy bootstrap remains immutable provenance.",
                    "verification": ["legacy bootstrap regression"],
                }
            ],
        }
        migrated = updated_payload(
            legacy,
            engine_sha256=self.engine_v2,
            protocol_sha256=self.protocol_v1,
            rationale="The next engine is registered without a version-pair bridge.",
            verification=["independent registration migration regression"],
        )
        self.assertEqual(migrated["revisions"][:1], legacy["revisions"])
        self.assertEqual(migrated["independent_registration_start_sequence"], 2)
        self.assertNotIn("relation_to_previous", migrated["revisions"][1])
        validate_append_only_history(migrated, legacy)
        validate_revision_ledger(
            migrated,
            current_engine_sha256=self.engine_v2,
            current_protocol_sha256=self.protocol_v1,
        )

    def test_index_and_tree_views_ignore_unstaged_bytes_exactly(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            subprocess.run(
                ["git", "config", "user.email", "fixture@example.com"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "config", "user.name", "Fixture"], cwd=root, check=True
            )
            source = root / "scripts" / "engine.py"
            source.parent.mkdir(parents=True)
            source.write_text("value = 1\n", encoding="utf-8")
            test_source = root / "scripts" / "tests" / "test_engine.py"
            test_source.parent.mkdir(parents=True)
            test_source.write_text("value = 1\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "baseline"], cwd=root, check=True)

            index_view = GitCandidateView(root, tree=None)
            tree_view = GitCandidateView(root, tree="HEAD")
            index_original = engine_tree_digest(index_view.engine_blobs())
            tree_original = engine_tree_digest(tree_view.engine_blobs())
            self.assertEqual(index_original, tree_original)
            self.assertEqual(index_original[1], 1)

            source.write_text("value = 2\n", encoding="utf-8")
            unstaged = engine_tree_digest(
                GitCandidateView(root, tree=None).engine_blobs()
            )
            self.assertEqual(unstaged, index_original)

            subprocess.run(["git", "add", str(source)], cwd=root, check=True)
            staged = engine_tree_digest(
                GitCandidateView(root, tree=None).engine_blobs()
            )
            committed = engine_tree_digest(
                GitCandidateView(root, tree="HEAD").engine_blobs()
            )
            self.assertNotEqual(staged[0], index_original[0])
            self.assertEqual(committed, tree_original)

            test_source.write_text("value = 2\n", encoding="utf-8")
            subprocess.run(["git", "add", str(test_source)], cwd=root, check=True)
            after_test_only_change = engine_tree_digest(
                GitCandidateView(root, tree=None).engine_blobs()
            )
            self.assertEqual(after_test_only_change, staged)

    def test_engine_blob_inventory_uses_one_batch_object_read(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            subprocess.run(["git", "init", "-q"], cwd=root, check=True)
            scripts = root / "scripts"
            scripts.mkdir()
            (scripts / "a.py").write_text("a = 1\n", encoding="utf-8")
            (scripts / "b.py").write_text("b = 1\n", encoding="utf-8")
            subprocess.run(["git", "add", "."], cwd=root, check=True)
            subprocess.run(
                [
                    "git",
                    "-c",
                    "user.name=Fixture",
                    "-c",
                    "user.email=fixture@example.com",
                    "commit",
                    "-qm",
                    "fixture",
                ],
                cwd=root,
                check=True,
            )
            view = GitCandidateView(root, tree="HEAD")
            original_run = subprocess.run
            with mock.patch.object(
                subprocess, "run", wraps=original_run
            ) as run_command:
                blobs = view.engine_blobs()
            batch_calls = [
                call
                for call in run_command.call_args_list
                if call.args and call.args[0][:3] == ["git", "cat-file", "--batch"]
            ]
            self.assertEqual(len(blobs), 2)
            self.assertEqual(len(batch_calls), 1)

    def test_runtime_gate_rejects_dirty_engine_ledger_and_structured_protocol(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source, protocol = self.initialize_runtime_repository(root)
            baseline = validate_runtime_engine_registration(root)

            source.write_text("value = 2\n", encoding="utf-8")
            with self.assertRaisesRegex(EngineRevisionError, "differs from clean HEAD"):
                validate_runtime_engine_registration(root)
            source.write_text("value = 1\n", encoding="utf-8")

            subprocess.run(
                ["git", "update-index", "--assume-unchanged", "scripts/engine.py"],
                cwd=root,
                check=True,
            )
            source.write_text("value = 2\n", encoding="utf-8")
            with self.assertRaisesRegex(EngineRevisionError, "scripts/engine.py"):
                validate_runtime_engine_registration(root)
            subprocess.run(
                ["git", "update-index", "--no-assume-unchanged", "scripts/engine.py"],
                cwd=root,
                check=True,
            )
            source.write_text("value = 1\n", encoding="utf-8")

            test_only = root / "scripts" / "tests" / "test_engine.py"
            test_only.parent.mkdir()
            test_only.write_text("value = 4\n", encoding="utf-8")
            self.assertEqual(
                validate_runtime_engine_registration(root).engine_tree_sha256,
                baseline.engine_tree_sha256,
            )

            ignored = root / "scripts" / "ignored.py"
            ignored.write_text("value = 3\n", encoding="utf-8")
            with self.assertRaisesRegex(EngineRevisionError, "ignored.py"):
                validate_runtime_engine_registration(root)
            ignored.unlink()

            protocol_path = root / "config" / "formalization_audit_protocol.json"
            prose_only = copy.deepcopy(protocol)
            prose_only["pacing"]["rule"] = "Reworded fixture prose."
            protocol_path.write_text(
                json.dumps(prose_only, indent=2) + "\n", encoding="utf-8"
            )
            self.assertEqual(
                validate_runtime_engine_registration(root).review_semantic_class_sha256,
                baseline.review_semantic_class_sha256,
            )

            semantic = copy.deepcopy(protocol)
            semantic["reuse"]["semantic_engine_epoch"] = "fixture-v2"
            protocol_path.write_text(
                json.dumps(semantic, indent=2) + "\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(EngineRevisionError, "audit_protocol"):
                validate_runtime_engine_registration(root)
            protocol_path.write_text(
                json.dumps(protocol, indent=2) + "\n", encoding="utf-8"
            )

            ledger_path = root / "config" / "formalization_engine_revisions.json"
            ledger_path.write_text(ledger_path.read_text(encoding="utf-8") + "\n")
            with self.assertRaisesRegex(EngineRevisionError, "engine_revisions"):
                validate_runtime_engine_registration(root)

    def test_registered_compatible_commit_preserves_review_semantic_class(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source, _protocol = self.initialize_runtime_repository(root)
            before = validate_runtime_engine_registration(root)
            ledger_path = root / "config" / "formalization_engine_revisions.json"
            ledger = json.loads(ledger_path.read_text(encoding="utf-8"))

            source.write_text("value = int(1)\n", encoding="utf-8")
            engine_digest = engine_tree_digest(
                [blob("scripts/engine.py", source.read_bytes())]
            )[0]
            updated = updated_payload(
                ledger,
                engine_sha256=engine_digest,
                protocol_sha256=before.review_semantic_class_sha256,
                rationale="The fixture refactor preserves all review decisions.",
                verification=["runtime compatibility regression"],
            )
            ledger_path.write_text(
                json.dumps(updated, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(EngineRevisionError, "differs from clean HEAD"):
                validate_runtime_engine_registration(root)

            subprocess.run(["git", "add", str(source), str(ledger_path)], cwd=root, check=True)
            subprocess.run(["git", "commit", "-qm", "compatible"], cwd=root, check=True)
            after = validate_runtime_engine_registration(root)
            self.assertEqual(after.revision_sequence, 2)
            self.assertEqual(after.registration_kind, "independent")
            self.assertEqual(
                after.review_semantic_class_sha256,
                before.review_semantic_class_sha256,
            )

    def test_recorded_issuer_history_is_readable_during_uncommitted_engine_work(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            source, _protocol = self.initialize_runtime_repository(root)
            baseline = validated_recorded_engine_revision_ledger(root)

            source.write_text("value = 2\n", encoding="utf-8")
            with self.assertRaisesRegex(EngineRevisionError, "differs from clean HEAD"):
                validate_runtime_engine_registration(root)

            recorded = validated_recorded_engine_revision_ledger(root)
            self.assertEqual(recorded, baseline)
            self.assertEqual(len(recorded["revisions"]), 1)


if __name__ == "__main__":
    unittest.main()
