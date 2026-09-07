#!/usr/bin/env python3
"""Focused tests for semantic-contract closure producer identities."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_signature_manifest as manifest_module
from scripts.python_source_slice_identity import (
    transitive_top_level_source_slice_identity,
)


ROOT = Path(__file__).resolve().parents[2]
MANIFEST_SOURCE = ROOT / "scripts" / "lean_signature_manifest.py"
CLOSURE_ROOTS = ("run_lean_semantic_contract_closure_manifests",)


class PythonSourceSliceIdentityTests(unittest.TestCase):
    @staticmethod
    def write_manifest_source_fixture(path: Path, source: str) -> None:
        path.write_text(source, encoding="utf-8")
        for dependency in (
            "lean_import_closure.py",
            "lean_process_diagnostics.py",
            "formalization_protocol.py",
            "python_source_slice_identity.py",
            "semantic_reuse_authority.py",
        ):
            (path.parent / dependency).write_bytes(
                (MANIFEST_SOURCE.parent / dependency).read_bytes()
            )

    def identity_for_source(self, source: str) -> dict[str, str]:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "producer.py"
            path.write_text(source, encoding="utf-8")
            identity = transitive_top_level_source_slice_identity(path, ("public",))
        self.assertIsNotNone(identity)
        assert identity is not None
        return identity

    def test_unreachable_function_change_does_not_change_slice(self) -> None:
        first = self.identity_for_source(
            """RELEVANT = 1
UNRELATED = 10

def helper():
    return RELEVANT

def public():
    return helper()

def unrelated():
    return UNRELATED + 1
"""
        )
        second = self.identity_for_source(
            """RELEVANT = 1
UNRELATED = 10

def helper():
    return RELEVANT

def public():
    return helper()

def unrelated():
    return UNRELATED + 999
"""
        )
        self.assertEqual(first, second)

    def test_reachable_helper_and_constant_changes_change_slice(self) -> None:
        baseline = self.identity_for_source(
            """RELEVANT = 1

def helper():
    return RELEVANT

def public():
    return helper()
"""
        )
        helper_changed = self.identity_for_source(
            """RELEVANT = 1

def helper():
    return RELEVANT + 1

def public():
    return helper()
"""
        )
        constant_changed = self.identity_for_source(
            """RELEVANT = 2

def helper():
    return RELEVANT

def public():
    return helper()
"""
        )
        self.assertNotEqual(
            baseline["source_slice_sha256"],
            helper_changed["source_slice_sha256"],
        )
        self.assertNotEqual(
            baseline["source_slice_sha256"],
            constant_changed["source_slice_sha256"],
        )

    def test_dynamic_module_namespace_access_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "dynamic.py"
            path.write_text(
                """def public(name):
    return globals()[name]
""",
                encoding="utf-8",
            )
            identity = transitive_top_level_source_slice_identity(path, ("public",))
        self.assertIsNone(identity)

    def test_unreachable_local_import_remains_outside_slice(self) -> None:
        baseline = self.identity_for_source(
            """VALUE = 1

def public():
    return VALUE

def unrelated():
    from .missing_local_module import value
    return value
"""
        )
        modified = self.identity_for_source(
            """VALUE = 1

def public():
    return VALUE

def unrelated():
    from .another_missing_module import value
    return value + 99
"""
        )
        self.assertEqual(baseline, modified)

    def test_reachable_local_import_and_recursive_dependency_are_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            producer = directory / "producer.py"
            helper = directory / "helper.py"
            dependency = directory / "dependency.py"
            producer.write_text(
                """from helper import action

def public():
    return action()
""",
                encoding="utf-8",
            )
            helper.write_text(
                """from dependency import VALUE

def action():
    return VALUE
""",
                encoding="utf-8",
            )
            dependency.write_text("VALUE = 1\n", encoding="utf-8")
            baseline = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )

            helper.write_text(
                """from dependency import VALUE

def action():
    return VALUE + 1
""",
                encoding="utf-8",
            )
            helper_changed = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )
            helper.write_text(
                """from dependency import VALUE

def action():
    return VALUE
""",
                encoding="utf-8",
            )
            dependency.write_text("VALUE = 2\n", encoding="utf-8")
            dependency_changed = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )

        self.assertIsNotNone(baseline)
        self.assertIsNotNone(helper_changed)
        self.assertIsNotNone(dependency_changed)
        assert baseline is not None
        assert helper_changed is not None
        assert dependency_changed is not None
        self.assertNotEqual(
            baseline["source_slice_sha256"],
            helper_changed["source_slice_sha256"],
        )
        self.assertNotEqual(
            baseline["source_slice_sha256"],
            dependency_changed["source_slice_sha256"],
        )
        self.assertEqual(baseline["local_import_count"], "2")

    def test_local_parent_package_initializer_is_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            package = directory / "package"
            package.mkdir()
            producer = directory / "producer.py"
            producer.write_text(
                """from package.helper import action

def public():
    return action()
""",
                encoding="utf-8",
            )
            (package / "helper.py").write_text(
                """from . import VALUE

def action():
    return VALUE
""",
                encoding="utf-8",
            )
            initializer = package / "__init__.py"
            initializer.write_text("VALUE = 1\n", encoding="utf-8")
            baseline = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )
            initializer.write_text("VALUE = 2\n", encoding="utf-8")
            modified = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )

        self.assertIsNotNone(baseline)
        self.assertIsNotNone(modified)
        assert baseline is not None and modified is not None
        self.assertNotEqual(
            baseline["source_slice_sha256"], modified["source_slice_sha256"]
        )

    def test_unresolved_relative_and_dynamic_imports_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            relative = Path(temporary) / "relative.py"
            relative.write_text(
                """def public():
    from .missing_local_module import value
    return value
""",
                encoding="utf-8",
            )
            dynamic = Path(temporary) / "dynamic.py"
            dynamic.write_text(
                """import importlib

def public(name):
    return importlib.import_module(name)
""",
                encoding="utf-8",
            )
            imported_alias = Path(temporary) / "imported_alias.py"
            imported_alias.write_text(
                """from importlib import import_module as im

def public(name):
    return im(name)
""",
                encoding="utf-8",
            )
            module_alias = Path(temporary) / "module_alias.py"
            module_alias.write_text(
                """import importlib as il

def public(name):
    return il.import_module(name)
""",
                encoding="utf-8",
            )

            relative_identity = transitive_top_level_source_slice_identity(
                relative, ("public",)
            )
            dynamic_identity = transitive_top_level_source_slice_identity(
                dynamic, ("public",)
            )
            imported_alias_identity = transitive_top_level_source_slice_identity(
                imported_alias, ("public",)
            )
            module_alias_identity = transitive_top_level_source_slice_identity(
                module_alias, ("public",)
            )

        self.assertIsNone(relative_identity)
        self.assertIsNone(dynamic_identity)
        self.assertIsNone(imported_alias_identity)
        self.assertIsNone(module_alias_identity)

    def test_exact_package_import_fallback_is_one_bound_provider(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / ".git").mkdir()
            scripts = root / "scripts"
            scripts.mkdir()
            producer = scripts / "producer.py"
            helper = scripts / "helper.py"
            producer.write_text(
                """if __package__:
    from .helper import VALUE, action as run
else:
    from helper import VALUE, action as run

def public():
    return VALUE + run()
""",
                encoding="utf-8",
            )
            helper.write_text("VALUE = 1\ndef action(): return 2\n", encoding="utf-8")
            baseline = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )
            helper.write_text("VALUE = 1\ndef action(): return 3\n", encoding="utf-8")
            changed = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )

        self.assertIsNotNone(baseline)
        self.assertIsNotNone(changed)
        assert baseline is not None and changed is not None
        self.assertNotEqual(
            baseline["source_slice_sha256"], changed["source_slice_sha256"]
        )

    def test_mismatched_conditional_import_fallback_remains_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            producer = directory / "producer.py"
            (directory / "first.py").write_text("VALUE = 1\n", encoding="utf-8")
            (directory / "second.py").write_text("VALUE = 1\n", encoding="utf-8")
            producer.write_text(
                """if __package__:
    from .first import VALUE
else:
    from second import VALUE

def public():
    return VALUE
""",
                encoding="utf-8",
            )
            identity = transitive_top_level_source_slice_identity(
                producer, ("public",)
            )
        self.assertIsNone(identity)

    def test_production_slice_binds_lean_import_closure_implementation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / ".git").mkdir()
            scripts = root / "scripts"
            scripts.mkdir()
            producer = scripts / MANIFEST_SOURCE.name
            producer.write_bytes(MANIFEST_SOURCE.read_bytes())
            for dependency in (
                "lean_import_closure.py",
                "lean_process_diagnostics.py",
                "formalization_protocol.py",
                "python_source_slice_identity.py",
                "semantic_reuse_authority.py",
            ):
                (scripts / dependency).write_bytes(
                    (MANIFEST_SOURCE.parent / dependency).read_bytes()
                )
            baseline = transitive_top_level_source_slice_identity(
                producer, CLOSURE_ROOTS
            )
            local_import = scripts / "lean_import_closure.py"
            local_import.write_bytes(
                local_import.read_bytes() + b"\n# changed local implementation\n"
            )
            modified = transitive_top_level_source_slice_identity(
                producer, CLOSURE_ROOTS
            )

        self.assertIsNotNone(baseline)
        self.assertIsNotNone(modified)
        assert baseline is not None and modified is not None
        self.assertGreaterEqual(int(baseline["local_import_count"]), 2)
        self.assertNotEqual(
            baseline["source_slice_sha256"], modified["source_slice_sha256"]
        )

    def test_real_manifest_cache_change_is_outside_closure_slice(self) -> None:
        source = MANIFEST_SOURCE.read_text(encoding="utf-8")
        old = '"""Hash one exact persisted manifest-cache context."""'
        new = '"""Changed unreachable manifest-cache implementation marker."""'
        self.assertIn(old, source)
        changed = source.replace(old, new, 1)
        with tempfile.TemporaryDirectory() as temporary:
            baseline_path = Path(temporary) / "baseline.py"
            changed_path = Path(temporary) / "changed.py"
            self.write_manifest_source_fixture(baseline_path, source)
            self.write_manifest_source_fixture(changed_path, changed)
            baseline = transitive_top_level_source_slice_identity(
                baseline_path, CLOSURE_ROOTS
            )
            modified = transitive_top_level_source_slice_identity(
                changed_path, CLOSURE_ROOTS
            )
        self.assertIsNotNone(baseline)
        self.assertEqual(baseline, modified)

    def test_real_closure_constant_change_changes_closure_slice(self) -> None:
        source = MANIFEST_SOURCE.read_text(encoding="utf-8")
        old = "SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE = 2"
        new = "SEMANTIC_CONTRACT_CLOSURE_CHUNK_SIZE = 3"
        self.assertIn(old, source)
        changed = source.replace(old, new, 1)
        with tempfile.TemporaryDirectory() as temporary:
            baseline_path = Path(temporary) / "baseline.py"
            changed_path = Path(temporary) / "changed.py"
            self.write_manifest_source_fixture(baseline_path, source)
            self.write_manifest_source_fixture(changed_path, changed)
            baseline = transitive_top_level_source_slice_identity(
                baseline_path, CLOSURE_ROOTS
            )
            modified = transitive_top_level_source_slice_identity(
                changed_path, CLOSURE_ROOTS
            )
        self.assertIsNotNone(baseline)
        self.assertIsNotNone(modified)
        assert baseline is not None and modified is not None
        self.assertNotEqual(
            baseline["source_slice_sha256"],
            modified["source_slice_sha256"],
        )

    def test_production_identity_no_longer_hashes_whole_wrapper(self) -> None:
        identity = manifest_module._semantic_contract_closure_extractor_identity()
        self.assertIsNotNone(identity)
        assert identity is not None
        self.assertEqual(identity["schema"], "4")
        self.assertNotIn("python_wrapper_sha256", identity)
        self.assertRegex(identity["python_source_slice_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(
            identity["python_source_slice_builder_sha256"], r"^[0-9a-f]{64}$"
        )


class ClosureModuleIdentityReattachmentTests(unittest.TestCase):
    EXTRACTOR = {
        "schema": "4",
        "canonical_surface_representation": (
            "lean_compact_canonical_surface_sha256_v2"
        ),
        "digest_algorithm": "sha256",
        "lean_helper_sha256": "9" * 64,
        "python_source_slice_schema": "2",
        "python_source_slice_sha256": "a" * 64,
        "python_source_slice_builder_sha256": "8" * 64,
        "python_source_slice_roots_sha256": "7" * 64,
        "python_source_slice_symbols_sha256": "6" * 64,
        "python_source_slice_symbol_count": "10",
        "python_source_slice_local_imports_sha256": "5" * 64,
        "python_source_slice_local_import_count": "2",
    }
    HASH_TOOL = {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": "/verified/sha256sum",
        "executable_sha256": "b" * 64,
        "version_stdout_sha256": "d" * 64,
        "version_banner": "sha256sum fixture",
        "known_vector": "sha256(abc)",
        "known_vector_sha256": (
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        ),
    }
    SPECIFICATION = "Fixture.Spec"
    MODULE_IDENTITIES = [
        {
            "origin_class": "paper",
            "module_origin": "Fixture.Core",
            "artifact_scope": "workspace",
            "artifact_sha256": "c" * 64,
        }
    ]

    def raw_manifest(self) -> dict[str, object]:
        surface = {"binder_domains": [], "body": {"tag": "true"}}
        nodes = [
            {
                "structural_path": "result",
                "node_role": "body",
                "origin_class": "paper",
                "module_origin": "Fixture.Core",
                "declaration": "Fixture.Core.result",
                "canonical_identity": {"tag": "definition"},
            }
        ]
        structural_payload = {
            "schema": manifest_module.SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "passes": True,
            "expanded": 1,
            "surface_mode": "closure_expanded",
            "surface": surface,
            "nodes": [
                {
                    "structural_path": "result",
                    "node_role": "body",
                    "origin_class": "paper",
                }
            ],
            "failure_tags": [],
        }
        return {
            "schema": manifest_module.SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
            "spec": self.SPECIFICATION,
            "passes": True,
            "expanded": 1,
            "surface_mode": "closure_expanded",
            "surface": surface,
            "nodes": nodes,
            "reached_modules": [
                {
                    "origin_class": "paper",
                    "module_origin": "Fixture.Core",
                }
            ],
            "failures": [],
            "scope": {
                "hash_tool_path": self.HASH_TOOL["resolved_path"],
                "foundation_modules": ["Init"],
            },
            "sha256": manifest_module._closure_json_sha256(structural_payload),
            "surface_sha256": manifest_module._closure_json_sha256(surface),
        }

    def attached_manifest(self, root: Path) -> dict[str, object]:
        with (
            mock.patch.object(
                manifest_module,
                "_semantic_contract_closure_extractor_identity",
                return_value=self.EXTRACTOR,
            ),
            mock.patch.object(
                manifest_module,
                "_closure_module_identity_snapshot",
                return_value={self.SPECIFICATION: self.MODULE_IDENTITIES},
            ),
        ):
            attached = manifest_module._with_semantic_contract_closure_module_identities(
                root,
                {self.SPECIFICATION: self.raw_manifest()},
                hash_tool_identity=self.HASH_TOOL,
                timeout_seconds=5,
            )
        return attached[self.SPECIFICATION]

    def reattach(
        self,
        root: Path,
        manifest: dict[str, object],
        identities: list[dict[str, str]] | None = None,
    ) -> dict[str, dict[str, object]]:
        with (
            mock.patch.object(
                manifest_module,
                "_semantic_contract_closure_extractor_identity",
                return_value=self.EXTRACTOR,
            ),
            mock.patch.object(
                manifest_module,
                "_semantic_contract_closure_hash_tool_identity",
                return_value=self.HASH_TOOL,
            ),
            mock.patch.object(
                manifest_module,
                "_closure_module_identity_snapshot",
                return_value={
                    self.SPECIFICATION: identities or self.MODULE_IDENTITIES
                },
            ),
        ):
            return manifest_module.reattach_semantic_contract_closure_module_identities(
                root,
                {self.SPECIFICATION: manifest},
                timeout_seconds=5,
            )

    def test_reattachment_accepts_exact_current_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lake-manifest.json").write_text("{}", encoding="utf-8")
            (root / "lean-toolchain").write_text("fixture", encoding="utf-8")
            manifest = self.attached_manifest(root)
            rebound = self.reattach(root, manifest)
        self.assertEqual(set(rebound), {self.SPECIFICATION})
        self.assertEqual(rebound[self.SPECIFICATION], manifest)

    def test_reattachment_rejects_core_contract_and_artifact_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lake-manifest.json").write_text("{}", encoding="utf-8")
            (root / "lean-toolchain").write_text("fixture", encoding="utf-8")
            baseline = self.attached_manifest(root)

            tampered_core = dict(baseline)
            tampered_core["surface"] = {"binder_domains": [], "body": {"tag": "false"}}
            self.assertEqual(self.reattach(root, tampered_core), {})

            changed_implementation = dict(baseline)
            changed_implementation["closure_extractor_identity"] = {
                **self.EXTRACTOR,
                "python_source_slice_sha256": "4" * 64,
            }
            self.assertEqual(
                self.reattach(root, changed_implementation),
                {self.SPECIFICATION: baseline},
            )

            changed_contract = dict(baseline)
            changed_contract["closure_extractor_contract_identity"] = {
                **baseline["closure_extractor_contract_identity"],
                "contract": "different_contract",
            }
            self.assertEqual(self.reattach(root, changed_contract), {})

            changed_artifacts = [
                {**self.MODULE_IDENTITIES[0], "artifact_sha256": "d" * 64}
            ]
            self.assertEqual(
                self.reattach(root, baseline, changed_artifacts),
                {},
            )

    def test_legacy_implementation_identity_migrates_without_lean_replay(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "lake-manifest.json").write_text("{}", encoding="utf-8")
            (root / "lean-toolchain").write_text("fixture", encoding="utf-8")
            baseline = self.attached_manifest(root)
            legacy = dict(baseline)
            legacy.pop("closure_extractor_contract_identity")
            legacy["closure_module_context_sha256"] = manifest_module._closure_json_sha256(
                {
                    "schema": manifest_module.SEMANTIC_CONTRACT_CLOSURE_SCHEMA,
                    "foundation_context_sha256": legacy[
                        "closure_foundation_context_sha256"
                    ],
                    "module_identities": legacy["closure_module_identities"],
                    "extractor_identity": legacy["closure_extractor_identity"],
                }
            )
            rebound = self.reattach(root, legacy)

        self.assertEqual(set(rebound), {self.SPECIFICATION})
        self.assertEqual(
            rebound[self.SPECIFICATION]["closure_extractor_contract_identity"],
            baseline["closure_extractor_contract_identity"],
        )
        self.assertEqual(
            rebound[self.SPECIFICATION]["closure_module_context_sha256"],
            baseline["closure_module_context_sha256"],
        )


if __name__ == "__main__":
    unittest.main()
