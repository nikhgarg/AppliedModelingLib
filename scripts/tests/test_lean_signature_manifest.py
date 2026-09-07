#!/usr/bin/env python3
"""Integration tests for Lean-elaborated signature manifests."""

from __future__ import annotations

import hashlib
import contextlib
import io
import json
import os
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import lean_signature_manifest as manifest_module
from scripts import lean_import_closure as import_closure
from scripts import audit_repository
from scripts import review_dashboard
from scripts.lean_signature_manifest import run_lean_signature_manifests_for_source
from scripts.lean_signature_manifest import (
    repository_module_names_in_import_closure,
    recursive_field_safety_locator_identity,
    run_lean_constructor_field_slot_counts_for_source,
    run_lean_inductive_constructor_field_slot_counts_for_source,
    run_lean_constructor_result_type_matches_for_source,
    run_lean_proposition_spec_proof_matches_for_source,
    run_lean_recursive_field_proposition_sorts,
    run_lean_recursive_field_proposition_sorts_for_source,
    run_lean_semantic_contract_closure_manifests,
    run_lean_semantic_contract_closure_manifests_for_source,
    run_lean_semantic_contract_matches_for_source,
    run_lean_source_premise_false_eliminators_for_source,
    run_lean_type_witness_payload_safeties,
    run_lean_type_witness_payload_safeties_for_source,
)


ROOT = Path(__file__).resolve().parents[2]


class LeanSignatureManifestTests(unittest.TestCase):
    IMPORT_MANIFEST_HASH_TOOL_IDENTITY = {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": "/fixture/sha256sum",
        "executable_sha256": "f" * 64,
        "version_stdout_sha256": "e" * 64,
        "version_banner": "sha256sum fixture",
        "known_vector": "sha256(abc)",
        "known_vector_sha256": (
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        ),
    }

    def enriched_import_manifest_results(
        self, manifests: dict[str, dict[str, str]]
    ) -> dict[str, dict[str, object]]:
        """Return the production wrapper fields for mocked Lean output."""

        portable_hash_tool = (
            manifest_module.portable_semantic_hash_tool_identity(
                self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY
            )
        )
        return {
            name: {
                **manifest,
                "canonical_representation": manifest_module.CANONICAL_REPRESENTATION,
                "semantic_hash_tool_identity": portable_hash_tool,
            }
            for name, manifest in manifests.items()
        }

    def manifests(self, source: str, names: list[str]) -> dict[str, dict]:
        result = run_lean_signature_manifests_for_source(ROOT, source, names)
        self.assertEqual(set(result), set(names))
        return result

    def test_semantic_closure_extractor_has_a_current_source_identity(self) -> None:
        """Import refactors must not silently disable every closure receipt."""

        identity = manifest_module._semantic_contract_closure_extractor_identity()
        self.assertIsNotNone(identity)
        assert identity is not None
        self.assertEqual(identity["schema"], "4")
        self.assertEqual(
            identity["canonical_surface_representation"],
            "lean_compact_canonical_surface_sha256_v2",
        )
        self.assertRegex(identity["python_source_slice_sha256"], r"^[0-9a-f]{64}$")

    def test_oversized_definition_value_uses_exact_compact_fingerprint(self) -> None:
        """A large valid data definition must not erase its sibling rows."""

        def definition_manifest(payload: str) -> dict[str, object]:
            return {
                "schema": manifest_module.MANIFEST_SCHEMA,
                "declaration_kind": "definition",
                "conclusion_mode": "type_and_value",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {
                            "tag": "definition",
                            "type": {"tag": "sort", "level": {"tag": "zero"}},
                            "value": {
                                "tag": "opaque_fixture_payload",
                                "payload": payload,
                            },
                        },
                        "display": "Fixture := exact large value",
                    }
                ],
            }

        large = "a" * (manifest_module.MAX_COMPACT_CANONICAL_BYTES + 1)
        first = definition_manifest(large + "0")
        second = definition_manifest(large + "1")
        first_digest = manifest_module.signature_manifest_digest(first)
        second_digest = manifest_module.signature_manifest_digest(second)

        self.assertRegex(first_digest, r"^[0-9a-f]{64}$")
        self.assertRegex(second_digest, r"^[0-9a-f]{64}$")
        self.assertNotEqual(first_digest, second_digest)
        canonical = manifest_module._canonical_payload(first)
        self.assertIsNotNone(canonical)
        assert canonical is not None
        result = canonical["atoms"][0]["canonical"]
        self.assertEqual(set(result), {"tag", "sha256"})
        self.assertEqual(result["tag"], "definition")

        small = definition_manifest("small")
        small_canonical = manifest_module._canonical_payload(small)
        self.assertIsNotNone(small_canonical)
        assert small_canonical is not None
        self.assertIn("value", small_canonical["atoms"][0]["canonical"])

    def test_oversized_theorem_atoms_use_exact_compact_fingerprints(self) -> None:
        """Large valid theorem binders and conclusions remain exact signatures."""

        def theorem_manifest(binder_payload: str, result_payload: str) -> dict[str, object]:
            return {
                "schema": manifest_module.MANIFEST_SCHEMA,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "arg0",
                        "role": "parameter",
                        "binder_info": "explicit",
                        "canonical": {
                            "tag": "fixture_binder",
                            "payload": binder_payload,
                        },
                    },
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {
                            "tag": "fixture_result",
                            "payload": result_payload,
                        },
                    },
                ],
            }

        large = "a" * (manifest_module.MAX_COMPACT_CANONICAL_BYTES + 1)
        first = theorem_manifest(large + "binder-0", large + "result-0")
        same = theorem_manifest(large + "binder-0", large + "result-0")
        changed_binder = theorem_manifest(large + "binder-1", large + "result-0")
        changed_result = theorem_manifest(large + "binder-0", large + "result-1")

        first_digest = manifest_module.signature_manifest_digest(first)
        self.assertRegex(first_digest, r"^[0-9a-f]{64}$")
        self.assertEqual(
            first_digest,
            manifest_module.signature_manifest_digest(same),
        )
        self.assertNotEqual(
            first_digest,
            manifest_module.signature_manifest_digest(changed_binder),
        )
        self.assertNotEqual(
            first_digest,
            manifest_module.signature_manifest_digest(changed_result),
        )

        canonical = manifest_module._canonical_payload(first)
        self.assertIsNotNone(canonical)
        assert canonical is not None
        for atom in canonical["atoms"]:
            self.assertEqual(set(atom["canonical"]), {"tag", "sha256"})
            self.assertEqual(atom["canonical"]["tag"], "canonical")
        self.assertEqual(canonical["atoms"][0]["binder_info"], "explicit")

        small = theorem_manifest("small binder", "small result")
        small_canonical = manifest_module._canonical_payload(small)
        self.assertIsNotNone(small_canonical)
        assert small_canonical is not None
        self.assertIn("payload", small_canonical["atoms"][0]["canonical"])
        self.assertIn("payload", small_canonical["atoms"][1]["canonical"])

    def test_helper_hash_transport_uses_private_files_not_pipes(self) -> None:
        """Keep restricted runtimes free of helper-owned process descriptors."""

        helper = manifest_module.HELPER_PATH.read_text(encoding="utf-8")
        self.assertIn("IO.FS.createTempDir", helper)
        self.assertIn("stdin := .null", helper)
        self.assertIn("stdout := .null", helper)
        self.assertIn("stderr := .null", helper)
        self.assertIn('"exec \\"$1\\" \\"$2\\" > \\"$3\\""', helper)
        self.assertNotIn("IO.Process.output", helper)
        self.assertNotIn(".piped", helper)

    def test_compiled_helper_is_a_thin_reexport_of_receipt_pinned_source(
        self,
    ) -> None:
        """Prevent the injected and compiled Lean command bodies from drifting."""

        compiled_path = ROOT / manifest_module.COMPILED_AUDIT_HELPER_SOURCE
        compiled = compiled_path.read_text(encoding="utf-8")
        helper = manifest_module.HELPER_PATH.read_text(encoding="utf-8")
        lake = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
        audit_library_stanza = """[[lean_lib]]
name = "AppliedModelingLibAuditScripts"
srcDir = "scripts"
roots = ["lean_signature_manifest_helper"]
"""

        self.assertEqual(lake.count(audit_library_stanza), 1)
        self.assertTrue(compiled.startswith("import lean_signature_manifest_helper\n"))
        self.assertNotIn("elab_rules : command", compiled)
        self.assertEqual(compiled.count("import lean_signature_manifest_helper"), 1)
        self.assertGreaterEqual(helper.count("elab_rules : command"), 3)

    def test_compiled_helper_reexport_registers_the_lean_audit_commands(
        self,
    ) -> None:
        """Exercise one semantic command through the stable compiled import."""

        self.assertTrue(
            manifest_module._build_compiled_audit_helper(ROOT, timeout_seconds=120)
        )
        source = """import AppliedModelingLib.Audit.SignatureManifest

namespace Fixture

def sourceSpec : Prop := True
theorem sourceSpec_proof : sourceSpec := trivial

#proposition_spec_proof_match "Fixture.sourceSpec" "Fixture.sourceSpec_proof"

end Fixture
"""
        with tempfile.TemporaryDirectory() as temp_dir:
            fixture = Path(temp_dir) / "CompiledAuditHelperFixture.lean"
            fixture.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(fixture)],
                cwd=ROOT,
                text=True,
                capture_output=True,
                check=False,
                timeout=120,
            )

        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(
            'LEAN_PROPOSITION_SPEC_PROOF_MATCH:{"matches":true',
            result.stdout,
        )

    def test_manifest_context_digest_ignores_hash_tool_install_location(self) -> None:
        context = {
            "schema": 3,
            "import_module": "Fixture.PaperInterface",
            "olean_fingerprint": ["a" * 64, 10],
            "helper_fingerprint": ["b" * 64, 20],
            "semantic_hash_tool_identity": self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY,
            "canonical_representation": manifest_module.CANONICAL_REPRESENTATION,
            "audit_scope_fingerprint": "c" * 64,
            "audit_modules": ["Fixture.PaperInterface"],
            "semantic_module_fingerprints": [
                ["Fixture.PaperInterface", ["a" * 64, 10]]
            ],
        }
        relocated = {
            **context,
            "semantic_hash_tool_identity": {
                **self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY,
                "resolved_path": "/other/machine/bin/sha256sum",
            },
        }
        self.assertEqual(
            manifest_module.signature_manifest_cache_context_sha256(context),
            manifest_module.signature_manifest_cache_context_sha256(relocated),
        )

    def saved_lean_import_closure(
        self,
        root: Path,
        entry_module: str,
        source_modules: tuple[str, ...],
    ) -> dict[str, object]:
        """Create an exact saved receipt for a filesystem-only fixture."""

        controls = {
            "lean-toolchain": b"leanprover/lean4:test\n",
            "lake-manifest.json": b"{}\n",
        }
        for relative, content in controls.items():
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        lakefile = root / "lakefile.lean"
        lakefile.write_bytes(b"-- fixture routing\n")

        sources: list[dict[str, object]] = []
        for module in sorted(source_modules):
            path = manifest_module._repository_module_source_path(root, module)
            self.assertIsNotNone(path)
            assert path is not None
            content = path.read_bytes()
            sources.append(
                {
                    "module": module,
                    "path": path.relative_to(root).as_posix(),
                    "byte_length": len(content),
                    "sha256": hashlib.sha256(content).hexdigest(),
                }
            )
        sources.sort(key=lambda item: str(item["path"]))
        entry_path = manifest_module._repository_module_source_path(root, entry_module)
        self.assertIsNotNone(entry_path)
        assert entry_path is not None
        external_artifacts_sha256 = import_closure.external_module_artifacts_sha256([])
        payload = {
            "schema": import_closure.WORKTREE_IDENTITY_SCHEMA,
            "entrypoint": entry_path.relative_to(root).as_posix(),
            "entry_module": entry_module,
            "lean_loaded_modules": sorted(source_modules),
            "sources": sources,
            "external_import_modules": [],
            "external_module_artifacts_sha256": external_artifacts_sha256,
            "build_controls": [
                {
                    "path": relative,
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(controls[relative]),
                    "sha256": hashlib.sha256(controls[relative]).hexdigest(),
                }
                for relative in import_closure.WORKTREE_IDENTITY_CONTROL_PATHS
            ],
            "lake_routing": {
                "schema": import_closure.LAKE_ROUTING_SCHEMA,
                "kind": "lean",
                "byte_length": len(lakefile.read_bytes()),
                "sha256": hashlib.sha256(lakefile.read_bytes()).hexdigest(),
            },
        }
        return import_closure.validated_lean_import_closure_payload(payload)

    def test_repository_import_closure_is_exact_and_includes_root_module(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            shared = root / "AppliedModelingLib" / "Shared"
            paper.mkdir(parents=True)
            shared.mkdir(parents=True)
            (root / "AppliedModelingLib.lean").write_text(
                "import AppliedModelingLib.Shared.Core\n", encoding="utf-8"
            )
            (shared / "Core.lean").write_text("def shared := 1\n", encoding="utf-8")
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\nimport AppliedModelingLib\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text(
                "/- import Fixture.Unused -/\ndef model := shared\n", encoding="utf-8"
            )
            (paper / "Unused.lean").write_text("def unused := 0\n", encoding="utf-8")

            closure = repository_module_names_in_import_closure(
                root, "Fixture.PaperInterface"
            )

        self.assertEqual(
            closure,
            (
                "AppliedModelingLib",
                "AppliedModelingLib.Shared.Core",
                "Fixture.Model",
                "Fixture.PaperInterface",
            ),
        )

    def test_repository_import_closure_fails_closed_on_missing_local_module(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Missing\n", encoding="utf-8"
            )

            closure = repository_module_names_in_import_closure(
                root, "Fixture.PaperInterface"
            )

        self.assertEqual(closure, ())

    def test_repository_import_closure_fails_closed_on_ambiguous_module(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "Fixture").mkdir(parents=True)
            (root / "papers" / "Fixture").mkdir(parents=True)
            for interface in (
                root / "Fixture" / "PaperInterface.lean",
                root / "papers" / "Fixture" / "PaperInterface.lean",
            ):
                interface.write_text("import Mathlib\n", encoding="utf-8")

            closure = repository_module_names_in_import_closure(
                root, "Fixture.PaperInterface"
            )

        self.assertEqual(closure, ())

    def test_repository_ownership_snapshot_matches_exact_module_routing(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "Root.lean").write_text("def root := 1\n", encoding="utf-8")
            (root / "AppliedModelingLib" / "Model.lean").parent.mkdir(parents=True)
            (root / "AppliedModelingLib" / "Model.lean").write_text(
                "def model := 1\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture" / "Model.lean").parent.mkdir(
                parents=True
            )
            (root / "papers" / "Fixture" / "Model.lean").write_text(
                "def model := 1\n", encoding="utf-8"
            )
            (root / "Fixture" / "Model.lean").parent.mkdir(parents=True)
            (root / "Fixture" / "Model.lean").write_text(
                "def duplicate := 1\n", encoding="utf-8"
            )
            snapshot = import_closure.repository_module_ownership_snapshot(root)

            for module in (
                "Root",
                "AppliedModelingLib.Model",
                "Fixture.Model",
                "Mathlib.Data.Finset.Basic",
            ):
                self.assertEqual(
                    snapshot.candidates(module),
                    manifest_module._repository_module_source_candidates(
                        root, module
                    ),
                )

    def test_repository_ownership_snapshot_is_refreshed_for_finalization(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers").mkdir()
            before = import_closure.repository_module_ownership_snapshot(root)
            self.assertEqual(before.candidates("Mathlib.NewOwner"), ())

            local_owner = root / "Mathlib" / "NewOwner.lean"
            local_owner.parent.mkdir()
            local_owner.write_text("def local := 1\n", encoding="utf-8")
            after = import_closure.repository_module_ownership_snapshot(root)

            self.assertEqual(before.candidates("Mathlib.NewOwner"), ())
            self.assertEqual(after.candidates("Mathlib.NewOwner"), (local_owner,))

    def test_paper_owned_import_scope_excludes_pinned_shared_terminals(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            shared = root / "AppliedModelingLib" / "Shared"
            nested = paper / "Nested"
            paper.mkdir(parents=True)
            shared.mkdir(parents=True)
            nested.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\nimport AppliedModelingLib.Shared.Core\n",
                encoding="utf-8",
            )
            (paper / "Model.lean").write_text(
                "import Fixture.Nested.Core\n", encoding="utf-8"
            )
            (nested / "Core.lean").write_text("def local := 1\n", encoding="utf-8")
            (shared / "Core.lean").write_text("def shared := 1\n", encoding="utf-8")
            (paper / "Unused.lean").write_text("def unused := 0\n", encoding="utf-8")

            with mock.patch.object(
                manifest_module,
                "_lean_loaded_module_candidates",
                side_effect=[
                    (
                        "AppliedModelingLib.Shared.Core",
                        "Fixture.Model",
                        "Fixture.Nested.Core",
                        "Fixture.PaperInterface",
                        "Mathlib",
                    ),
                    ("Fixture.Model", "Fixture.Nested.Core", "Mathlib"),
                ],
            ):
                interface_scope = (
                    manifest_module.paper_owned_module_names_in_import_closure(
                        root, paper, "Fixture.PaperInterface"
                    )
                )
                model_scope = (
                    manifest_module.paper_owned_module_names_in_import_closure(
                        root, paper, "Fixture.Model"
                    )
                )

        self.assertEqual(
            interface_scope,
            (
                "Fixture.Model",
                "Fixture.Nested.Core",
                "Fixture.PaperInterface",
            ),
        )
        self.assertEqual(model_scope, ("Fixture.Model", "Fixture.Nested.Core"))

    def test_unshared_loaded_module_scope_never_uses_python_snapshot_cache(
        self,
    ) -> None:
        manifest_module._LEAN_LOADED_MODULE_CLOSURE_CACHE.clear()
        self.addCleanup(manifest_module._LEAN_LOADED_MODULE_CLOSURE_CACHE.clear)
        with (
            mock.patch.object(
                manifest_module,
                "repository_build_input_snapshot",
                return_value="exact-input-snapshot",
            ) as snapshot,
            mock.patch(
                "scripts.lean_import_closure.lean_loaded_module_closure",
                return_value=(("Fixture.Model", "Fixture.PaperInterface"), ""),
            ) as loaded,
        ):
            first = manifest_module._lean_loaded_module_candidates(
                ROOT, "Fixture.PaperInterface", timeout_seconds=91
            )
            second = manifest_module._lean_loaded_module_candidates(
                ROOT, "Fixture.PaperInterface", timeout_seconds=91
            )

        self.assertEqual(first, ("Fixture.Model", "Fixture.PaperInterface"))
        self.assertEqual(second, first)
        self.assertEqual(loaded.call_count, 2)
        snapshot.assert_not_called()

    def test_repository_build_snapshot_tracks_exact_transitive_source_bytes(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            model = paper / "Model.lean"
            interface.write_text("import Fixture.Model\n", encoding="utf-8")
            model.write_text("def value := 1\n", encoding="utf-8")
            before_stat = model.stat()
            before = manifest_module.repository_build_input_snapshot(
                root, "Fixture.PaperInterface"
            )

            model.write_text("def value := 2\n", encoding="utf-8")
            os.utime(
                model,
                ns=(before_stat.st_atime_ns, before_stat.st_mtime_ns),
            )
            after = manifest_module.repository_build_input_snapshot(
                root, "Fixture.PaperInterface"
            )

        self.assertIsNotNone(before)
        self.assertIsNotNone(after)
        self.assertNotEqual(before, after)

    def test_build_snapshot_provider_reads_shared_modules_once_per_run(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            shared = root / "AppliedModelingLib" / "Common.lean"
            shared.parent.mkdir(parents=True)
            shared.write_text("def common := 1\n", encoding="utf-8")
            for paper_name in ("First", "Second"):
                paper = root / "papers" / paper_name
                paper.mkdir(parents=True)
                (paper / "PaperInterface.lean").write_text(
                    "import AppliedModelingLib.Common\n",
                    encoding="utf-8",
                )

            first_receipt = self.saved_lean_import_closure(
                root,
                "First.PaperInterface",
                ("AppliedModelingLib.Common", "First.PaperInterface"),
            )
            second_receipt = self.saved_lean_import_closure(
                root,
                "Second.PaperInterface",
                ("AppliedModelingLib.Common", "Second.PaperInterface"),
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=first_receipt,
            )
            provider.adopt_lean_import_closure_payload(second_receipt)
            self.assertTrue(
                provider.owns_exact_lean_import_closure_payload(first_receipt)
            )
            self.assertTrue(
                provider.owns_exact_lean_import_closure_payload(second_receipt)
            )
            self.assertFalse(
                provider.owns_exact_lean_import_closure_payload(
                    {**first_receipt, "entry_module": "Changed.PaperInterface"}
                )
            )
            first = manifest_module.repository_build_input_snapshot(
                root,
                "First.PaperInterface",
                provider=provider,
            )
            second = manifest_module.repository_build_input_snapshot(
                root,
                "Second.PaperInterface",
                provider=provider,
            )
            repeated = manifest_module.repository_build_input_snapshot(
                root,
                "First.PaperInterface",
                provider=provider,
            )
            diagnostics = provider.diagnostics()
            unchanged = provider.finalize_unchanged()

        self.assertIsNotNone(first)
        self.assertIsNotNone(second)
        self.assertEqual(repeated, first)
        self.assertEqual(diagnostics["source_reads"], 3)
        self.assertEqual(diagnostics["source_reuses"], 1)
        self.assertEqual(diagnostics["parse_requests"], 0)
        self.assertEqual(diagnostics["snapshot_reuses"], 1)
        self.assertTrue(unchanged)

    def test_provider_finalization_reuses_exact_external_artifact_snapshot(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )

            with mock.patch.object(
                import_closure,
                "external_module_artifact_snapshot",
                wraps=import_closure.external_module_artifact_snapshot,
            ) as artifact_snapshot:
                provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                    root,
                    lean_import_closure_payload=receipt,
                )
                self.assertTrue(provider.finalize_unchanged())

            self.assertEqual(artifact_snapshot.call_count, 1)
            self.assertEqual(
                provider.diagnostics()["external_artifact_snapshot_reuses"],
                1,
            )

    def test_graph_authenticated_provider_does_not_replay_ambient_artifacts(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            model = paper / "Model.lean"
            model.write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            receipt = import_closure.validated_lean_import_closure_payload(
                {
                    **receipt,
                    "lean_loaded_modules": [
                        *receipt["lean_loaded_modules"],
                        "Mathlib",
                    ],
                    "external_import_modules": ["Mathlib"],
                    "external_module_artifacts_sha256": "a" * 64,
                }
            )

            with mock.patch.object(
                import_closure,
                "external_module_artifact_snapshot",
                side_effect=AssertionError(
                    "accepted-graph verification replayed ambient artifacts"
                ),
            ) as artifact_snapshot:
                guard = (
                    manifest_module.graph_authenticated_lean_import_closure_guard(
                        root,
                        receipt,
                    )
                )
                self.assertFalse(hasattr(guard, "snapshot"))
                self.assertTrue(guard.finalize_unchanged())

            artifact_snapshot.assert_not_called()
            model.write_text("def value := 2\n", encoding="utf-8")
            self.assertFalse(guard.finalize_unchanged())

            model.write_text("def value := 1\n", encoding="utf-8")
            lakefile = root / "lakefile.lean"
            routing = lakefile.read_bytes()
            lakefile.write_bytes(routing + b"-- changed route\n")
            with self.assertRaisesRegex(ValueError, "Lake routing changed"):
                manifest_module.graph_authenticated_lean_import_closure_guard(
                    root,
                    receipt,
                )

            lakefile.write_bytes(routing)
            (root / "Mathlib.lean").write_text(
                "def newlyLocal := 1\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(ValueError, "gained repository source"):
                manifest_module.graph_authenticated_lean_import_closure_guard(
                    root,
                    receipt,
                )

    def test_repository_source_projection_never_adopts_or_hashes_artifacts(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            model = paper / "Model.lean"
            interface.write_text("import Fixture.Model\n", encoding="utf-8")
            model.write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            receipt = import_closure.validated_lean_import_closure_payload(
                {
                    **receipt,
                    "lean_loaded_modules": [
                        *receipt["lean_loaded_modules"],
                        "Mathlib",
                    ],
                    "external_import_modules": ["Mathlib"],
                    "external_module_artifacts_sha256": "a" * 64,
                }
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(root)
            with mock.patch.object(
                import_closure,
                "external_module_artifact_snapshot",
                side_effect=AssertionError(
                    "review projection hashed accepting build artifacts"
                ),
            ) as artifact_snapshot:
                snapshot = provider.validated_repository_source_snapshot(receipt)

            artifact_snapshot.assert_not_called()
            self.assertEqual(
                tuple(row[0] for row in snapshot),
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            self.assertEqual(provider.repository_source_snapshot("Fixture.PaperInterface"), ())
            self.assertFalse(provider.owns_exact_lean_import_closure_payload(receipt))

            model.write_text("def value := 2\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "source bytes changed"):
                provider.validated_repository_source_snapshot(receipt)

    def test_legacy_control_receipt_preserves_old_build_snapshot_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            helper_path = root / import_closure.LEAN_IMPORT_GRAPH_HELPER
            helper_path.parent.mkdir(parents=True)
            helper_content = b"-- historical graph helper\n"
            helper_path.write_bytes(helper_content)
            legacy = dict(receipt)
            legacy["build_controls"] = [
                *receipt["build_controls"],
                {
                    "path": import_closure.LEAN_IMPORT_GRAPH_HELPER,
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(helper_content),
                    "sha256": hashlib.sha256(helper_content).hexdigest(),
                },
            ]
            (root / "lakefile.lean").unlink()
            (root / "lakefile.toml").write_text(
                'name = "Fixture"\n'
                'version = "1.0.0"\n'
                'keywords = ["historical"]\n\n'
                '[[lean_lib]]\nname = "Fixture"\nsrcDir = "papers"\n',
                encoding="utf-8",
            )
            legacy["lake_routing"] = {
                "schema": import_closure.LAKE_ROUTING_SCHEMA,
                "kind": "toml",
                "package_configuration": {
                    "name": "Fixture",
                    "version": "1.0.0",
                    "keywords": ["historical"],
                },
                "lean_library": {"name": "Fixture", "srcDir": "papers"},
            }
            legacy = import_closure.validated_lean_import_closure_payload(legacy)

            identities = [
                ("module", str(raw["module"]), str(raw["sha256"]))
                for raw in sorted(
                    legacy["sources"], key=lambda item: str(item["module"])
                )
            ]
            for raw in legacy["build_controls"]:
                identities.append(
                    ("control", str(raw["path"]), str(raw["sha256"]))
                )
            identities.append(
                (
                    "lean_import_closure",
                    "Fixture.PaperInterface",
                    hashlib.sha256(
                        json.dumps(
                            legacy,
                            ensure_ascii=True,
                            sort_keys=True,
                            separators=(",", ":"),
                        ).encode("utf-8")
                    ).hexdigest(),
                )
            )
            historical_snapshot = hashlib.sha256(
                json.dumps(
                    identities,
                    ensure_ascii=True,
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()

            helper_path.write_bytes(b"-- refactored operational helper\n")
            graph_loader = mock.Mock(
                side_effect=AssertionError("legacy receipt must avoid Lean")
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=legacy,
                module_graph_loader=graph_loader,
            )

            self.assertEqual(
                provider.snapshot("Fixture.PaperInterface"), historical_snapshot
            )
            self.assertEqual(
                import_closure.lean_import_closure_payload_sha256(
                    provider.lean_import_closure_receipt("Fixture.PaperInterface")
                ),
                import_closure.lean_import_closure_payload_sha256(legacy),
            )
            self.assertEqual(
                len(provider.repository_source_snapshot("Fixture.PaperInterface")), 2
            )
            self.assertTrue(provider.finalize_unchanged())
            graph_loader.assert_not_called()

    def test_build_snapshot_provider_rejects_mutation_before_publish(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            model = paper / "Model.lean"
            interface.write_text("import Fixture.Model\n", encoding="utf-8")
            model.write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
            )

            self.assertIsNotNone(provider.snapshot("Fixture.PaperInterface"))
            model.write_text("def value := 2\n", encoding="utf-8")

            self.assertFalse(provider.finalize_unchanged())
            self.assertEqual(
                provider.diagnostics()["finalization_failures"],
                1,
            )

    def test_semantic_authority_adopts_current_sources_without_old_byte_replay(
        self,
    ) -> None:
        from scripts.source_record_semantic_reuse import (
            CurrentSemanticReuseAuthority,
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            model = paper / "Model.lean"
            interface.write_text("import Fixture.Model\n", encoding="utf-8")
            model.write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            # This edit invalidates the historical file-container receipt. A
            # completed Lean pass has separately established that its reviewed
            # declarations retain the canonical semantic identity.
            model.write_text("-- documentation only\ndef value := 1\n", encoding="utf-8")
            watched_paths = (
                interface,
                model,
                root / "lean-toolchain",
                root / "lake-manifest.json",
            )
            material = tuple(
                (
                    path.relative_to(root).as_posix(),
                    "present",
                    hashlib.sha256(path.read_bytes()).hexdigest(),
                )
                for path in watched_paths
            )
            authority = CurrentSemanticReuseAuthority(
                paper="Fixture",
                raw_audit_file_sha256="a" * 64,
                semantic_identity_sha256="b" * 64,
                reviewed_declarations=("Fixture.Spec",),
                watched_repository_material=material,
                result={},
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
                semantic_reuse_authority=authority,
            )

            snapshots = provider.repository_source_snapshot(
                "Fixture.PaperInterface"
            )
            self.assertEqual(
                {module for module, _path, _content, _digest in snapshots},
                {"Fixture.Model", "Fixture.PaperInterface"},
            )
            self.assertEqual(
                provider.diagnostics()["semantic_receipts_adopted"], 1
            )
            self.assertTrue(provider.finalize_unchanged())
            model.write_text("def value := 2\n", encoding="utf-8")
            self.assertFalse(provider.finalize_unchanged())

    def test_build_snapshot_provider_rejects_new_routing_ambiguity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.PaperInterface",),
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
            )

            self.assertIsNotNone(provider.snapshot("Fixture.PaperInterface"))
            duplicate = root / "Fixture"
            duplicate.mkdir()
            (duplicate / "PaperInterface.lean").write_text(
                "import Mathlib\n", encoding="utf-8"
            )

            self.assertFalse(provider.finalize_unchanged())

    def test_saved_receipt_avoids_lean_and_ignores_unrelated_paper_files(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            graph_loader = mock.Mock(
                side_effect=AssertionError("saved receipt must avoid Lean")
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
                module_graph_loader=graph_loader,
            )

            loaded = provider.lean_loaded_module_names("Fixture.PaperInterface")
            snapshots = provider.repository_source_snapshot("Fixture.PaperInterface")
            unrelated = root / "papers" / "Other" / "Scratch.lean"
            unrelated.parent.mkdir(parents=True)
            unrelated.write_text("def scratch := 0\n", encoding="utf-8")

            self.assertEqual(
                loaded,
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            self.assertEqual(
                tuple(module for module, _path, _content, _digest in snapshots),
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            graph_loader.assert_not_called()
            self.assertTrue(provider.finalize_unchanged())

    def test_saved_receipt_reports_every_changed_source_in_one_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            interface = paper / "PaperInterface.lean"
            model = paper / "Model.lean"
            interface.write_text("import Fixture.Model\n", encoding="utf-8")
            model.write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            interface.write_text("import Fixture.Model\n-- changed\n", encoding="utf-8")
            model.write_text("def value := 2\n", encoding="utf-8")

            with self.assertRaises(ValueError) as raised:
                manifest_module.RepositoryBuildInputSnapshotProvider(
                    root,
                    lean_import_closure_payload=receipt,
                )

        message = str(raised.exception)
        self.assertIn("2 problem(s)", message)
        self.assertIn(
            "Lean import-closure source bytes changed: "
            "papers/Fixture/Model.lean",
            message,
        )
        self.assertIn(
            "Lean import-closure source bytes changed: "
            "papers/Fixture/PaperInterface.lean",
            message,
        )

    def test_lean_receipt_closure_includes_dependency_python_diagnostic_misses(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import\n  Fixture.Model\n",
                encoding="utf-8",
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
            )

            authoritative = provider.module_names_in_import_closure(
                "Fixture.PaperInterface"
            )
            diagnostic = provider.diagnostic_python_module_names_in_import_closure(
                "Fixture.PaperInterface"
            )

        self.assertEqual(
            authoritative,
            ("Fixture.Model", "Fixture.PaperInterface"),
        )
        self.assertEqual(diagnostic, ("Fixture.PaperInterface",))

    def test_provider_runs_lean_graph_once_when_saved_receipt_is_absent(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            subprocess.run(
                ["git", "init", "-q"],
                cwd=root,
                check=True,
            )
            subprocess.run(
                ["git", "add", "."],
                cwd=root,
                check=True,
            )
            graph_loader = mock.Mock(
                return_value=(
                    ("Fixture.Model", "Fixture.PaperInterface"),
                    "",
                )
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                module_graph_loader=graph_loader,
            )

            first = provider.snapshot("Fixture.PaperInterface")
            second = provider.snapshot("Fixture.PaperInterface")

            self.assertIsNotNone(first)
            self.assertEqual(second, first)
            graph_loader.assert_called_once_with(
                root.resolve(), "Fixture.PaperInterface", 600
            )
            self.assertEqual(provider.diagnostics()["parse_requests"], 0)
            self.assertTrue(provider.finalize_unchanged())

    def test_provider_preserves_bounded_non_authoritative_discovery_error(self) -> None:
        root = Path("/tmp/diagnostic-fixture")
        provider = manifest_module.RepositoryBuildInputSnapshotProvider(root)
        reason = "Lake could not build +Fixture.PaperInterface:olean: timed out after 600 seconds; " + "x" * 5000
        worktree = mock.Mock()
        worktree.record_for_entrypoint.return_value = (None, mock.Mock(reason=reason))
        provider._live_closure_provider = worktree
        with mock.patch.object(manifest_module, "_repository_module_source_path",
                               return_value=root / "papers/Fixture/PaperInterface.lean"):
            self.assertEqual(provider.lean_loaded_module_names("Fixture.PaperInterface"), ())
        error = provider.lean_loaded_module_error("Fixture.PaperInterface")
        self.assertIn("timed out after 600 seconds", error)
        self.assertIn("+Fixture.PaperInterface:olean", error)
        self.assertLessEqual(len(error), 1200)
        self.assertEqual(provider.lean_loaded_module_error("Other"), "")
        worktree.record_for_entrypoint.assert_called_once()
        self.assertEqual(provider._closure_receipts, {})

    def test_shared_provider_reuses_one_receipt_for_build_and_environment_layers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            paper.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def value := 1\n", encoding="utf-8")
            artifact_root = root / ".lake" / "build" / "lib" / "lean" / "Fixture"
            artifact_root.mkdir(parents=True)
            (artifact_root / "PaperInterface.olean").write_bytes(b"interface")
            (artifact_root / "Model.olean").write_bytes(b"model")
            receipt = self.saved_lean_import_closure(
                root,
                "Fixture.PaperInterface",
                ("Fixture.Model", "Fixture.PaperInterface"),
            )
            provider = manifest_module.RepositoryBuildInputSnapshotProvider(
                root,
                lean_import_closure_payload=receipt,
            )

            input_snapshot = manifest_module._build_target_input_snapshot(
                root,
                "Fixture.PaperInterface",
                provider=provider,
            )
            artifact_snapshot = manifest_module._build_target_artifact_snapshot(
                root,
                "Fixture.PaperInterface",
                provider=provider,
            )
            first_environment = manifest_module._structural_scan_environment_snapshot(
                root,
                "Fixture.PaperInterface",
                provider=provider,
            )
            second_environment = manifest_module._structural_scan_environment_snapshot(
                root,
                "Fixture.PaperInterface",
                provider=provider,
            )
            diagnostics = provider.diagnostics()

            self.assertIsNotNone(input_snapshot)
            self.assertIsNotNone(artifact_snapshot)
            self.assertEqual(first_environment, second_environment)
            self.assertEqual(diagnostics["source_reads"], 2)
            self.assertEqual(diagnostics["parse_requests"], 0)
            self.assertEqual(diagnostics["closure_requests"], 4)
            self.assertEqual(diagnostics["closure_reuses"], 4)
            self.assertEqual(diagnostics["snapshot_requests"], 3)
            self.assertEqual(diagnostics["snapshot_reuses"], 2)
            self.assertTrue(provider.finalize_unchanged())

    def test_loaded_module_authority_reuses_shared_provider_receipt(self) -> None:
        manifest_module._LEAN_LOADED_MODULE_CLOSURE_CACHE.clear()
        self.addCleanup(manifest_module._LEAN_LOADED_MODULE_CLOSURE_CACHE.clear)
        provider = mock.Mock()
        provider.root = ROOT.resolve()
        provider.lean_loaded_module_names.return_value = (
            "Fixture.Model",
            "Fixture.PaperInterface",
        )
        with (
            mock.patch.object(
                manifest_module,
                "repository_build_input_snapshot",
                return_value="shared-input-snapshot",
            ) as snapshot,
            mock.patch(
                "scripts.lean_import_closure.lean_loaded_module_closure",
                return_value=(("Fixture.Model", "Fixture.PaperInterface"), ""),
            ) as loaded,
        ):
            first = manifest_module._lean_loaded_module_candidates(
                ROOT,
                "Fixture.PaperInterface",
                timeout_seconds=91,
                provider=provider,
            )
            second = manifest_module._lean_loaded_module_candidates(
                ROOT,
                "Fixture.PaperInterface",
                timeout_seconds=91,
                provider=provider,
            )

        self.assertEqual(first, second)
        loaded.assert_not_called()
        snapshot.assert_not_called()
        self.assertEqual(provider.lean_loaded_module_names.call_count, 2)

    def test_import_runners_forward_one_provider_to_the_build_layer(self) -> None:
        provider = mock.Mock()
        provider.root = ROOT.resolve()
        calls = [
            lambda: manifest_module.run_lean_proposition_spec_proof_matches(
                ROOT,
                "Fixture.PaperInterface",
                [("Fixture.target", "Fixture.proof")],
                build_input_provider=provider,
            ),
            lambda: manifest_module.run_lean_semantic_contract_matches(
                ROOT,
                "Fixture.PaperInterface",
                [("Fixture.target", "Fixture.proof", "Fixture.refutation")],
                build_input_provider=provider,
            ),
            lambda: manifest_module.run_lean_semantic_contract_transparency_checks(
                ROOT,
                "Fixture.PaperInterface",
                ["Fixture.Spec"],
                ("Fixture.PaperInterface",),
                build_input_provider=provider,
            ),
            lambda: manifest_module.run_lean_semantic_contract_closure_manifests(
                ROOT,
                "Fixture.PaperInterface",
                ["Fixture.Spec"],
                ("Fixture.PaperInterface",),
                build_input_provider=provider,
            ),
        ]
        with (
            mock.patch.object(
                manifest_module,
                "_build_import_target",
                return_value=False,
            ) as build,
            mock.patch.object(
                manifest_module,
                "_semantic_contract_closure_hash_tool_identity",
                return_value=self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY,
            ),
        ):
            for call in calls:
                with self.subTest(call=call):
                    self.assertEqual(call(), {})
                    self.assertIs(build.call_args.kwargs["provider"], provider)
                    build.reset_mock()

    def test_build_target_reuses_exact_successful_snapshot_in_process(self) -> None:
        manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear()
        self.addCleanup(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear)
        process = mock.Mock(returncode=0)
        process.communicate.return_value = ("", "")
        with (
            mock.patch.object(
                manifest_module,
                "_build_target_input_snapshot",
                return_value="source-snapshot",
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_artifact_snapshot",
                return_value=(("Fixture.PaperInterface", ("olean-sha256", 42)),),
            ),
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=process
            ) as popen,
        ):
            self.assertTrue(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )
            self.assertTrue(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )

        self.assertEqual(popen.call_count, 1)

    def test_native_module_builds_share_single_thread_environment(self) -> None:
        root = Path("/tmp/repository")
        process = mock.Mock(returncode=0)
        process.communicate.return_value = ("", "")
        self.addCleanup(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear)
        with mock.patch.dict(os.environ, {
            "LEAN_NUM_THREADS": "24", "BUILD_ENV_TEST_SENTINEL": "preserved",
        }):
            with (
                mock.patch.object(manifest_module, "_compiled_audit_module_available", return_value=True),
                mock.patch.object(manifest_module, "run_owned_lean_process", return_value=process) as run,
            ):
                self.assertTrue(manifest_module._build_compiled_audit_helper(root, 17))
            self.assertEqual(run.call_args.args[0], [
                "lake", "build", "+" + manifest_module.COMPILED_AUDIT_HELPER_MODULE,
            ])
            self.assertEqual(run.call_args.kwargs["timeout"], 17)
            self.assertEqual(run.call_args.kwargs["env"]["LEAN_NUM_THREADS"], "1")
            self.assertEqual(run.call_args.kwargs["env"]["BUILD_ENV_TEST_SENTINEL"], "preserved")

            for provider in (None, mock.Mock(root=root)):
                with self.subTest(shared_provider=provider is not None):
                    manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear()
                    with (
                        mock.patch.object(manifest_module, "_build_target_input_snapshot", return_value="source") as snapshot,
                        mock.patch.object(manifest_module, "_build_target_artifact_snapshot", return_value=("artifact",)),
                        mock.patch.object(manifest_module.subprocess, "Popen", return_value=process) as popen,
                    ):
                        self.assertTrue(manifest_module._build_import_target(
                            root, "Fixture.PaperInterface", 23, provider=provider,
                        ))
                    self.assertEqual(popen.call_args.args[0], ["lake", "build", "+Fixture.PaperInterface"])
                    self.assertEqual(popen.call_args.kwargs["env"]["LEAN_NUM_THREADS"], "1")
                    self.assertEqual(popen.call_args.kwargs["env"]["BUILD_ENV_TEST_SENTINEL"], "preserved")
                    self.assertIs(popen.call_args.kwargs["start_new_session"], True)
                    self.assertIs(snapshot.call_args.kwargs["provider"], provider)
                    process.communicate.assert_called_with(timeout=23)
            self.assertEqual(os.environ["LEAN_NUM_THREADS"], "24")

    def test_build_target_rejects_source_mutation_during_build(self) -> None:
        manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear()
        self.addCleanup(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear)
        process = mock.Mock(returncode=0)
        process.communicate.return_value = ("", "")
        with (
            mock.patch.object(
                manifest_module,
                "_build_target_input_snapshot",
                side_effect=("before", "after", "after"),
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_artifact_snapshot",
                return_value=(("Fixture.PaperInterface", ("olean-sha256", 42)),),
            ),
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=process
            ),
        ):
            self.assertFalse(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )

        self.assertEqual(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE, {})

    def test_build_target_rechecks_sources_before_reusing_cached_build(self) -> None:
        manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear()
        self.addCleanup(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear)
        process = mock.Mock(returncode=0)
        process.communicate.return_value = ("", "")
        with (
            mock.patch.object(
                manifest_module,
                "_build_target_input_snapshot",
                side_effect=(
                    "stable",
                    "stable",
                    "stable",
                    "stable",
                    "changed",
                    "changed",
                    "changed",
                ),
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_artifact_snapshot",
                return_value=(("Fixture.PaperInterface", ("olean-sha256", 42)),),
            ),
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=process
            ) as popen,
        ):
            self.assertTrue(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )
            self.assertFalse(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )

        self.assertEqual(popen.call_count, 2)

    def test_build_target_rejects_dependency_artifact_mutation_before_reuse(
        self,
    ) -> None:
        manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear()
        self.addCleanup(manifest_module._SUCCESSFUL_BUILD_SNAPSHOT_CACHE.clear)
        process = mock.Mock(returncode=0)
        process.communicate.return_value = ("", "")
        target_artifacts = (
            ("Fixture.Model", ("model-before", 12)),
            ("Fixture.PaperInterface", ("target-stable", 18)),
        )
        changed_dependency_artifacts = (
            ("Fixture.Model", ("model-after", 12)),
            ("Fixture.PaperInterface", ("target-stable", 18)),
        )
        with (
            mock.patch.object(
                manifest_module,
                "_build_target_input_snapshot",
                return_value="unchanged-sources",
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_artifact_snapshot",
                side_effect=(
                    target_artifacts,
                    target_artifacts,
                    changed_dependency_artifacts,
                    changed_dependency_artifacts,
                    changed_dependency_artifacts,
                ),
            ),
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=process
            ) as popen,
        ):
            self.assertTrue(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )
            self.assertTrue(
                manifest_module._build_import_target(
                    Path("/tmp/repository"), "Fixture.PaperInterface", 10
                )
            )

        self.assertEqual(popen.call_count, 2)

    def test_build_artifact_snapshot_hashes_exact_dependency_olean_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "Fixture"
            build = root / ".lake" / "build" / "lib" / "lean" / "Fixture"
            paper.mkdir(parents=True)
            build.mkdir(parents=True)
            (paper / "PaperInterface.lean").write_text(
                "import Fixture.Model\n", encoding="utf-8"
            )
            (paper / "Model.lean").write_text("def model := 1\n", encoding="utf-8")
            dependency = build / "Model.olean"
            dependency.write_bytes(b"dependency-before")
            (build / "PaperInterface.olean").write_bytes(b"target-is-unchanged")
            before_stat = dependency.stat()
            before = manifest_module._build_target_artifact_snapshot(
                root, "Fixture.PaperInterface"
            )

            dependency.write_bytes(b"dependency-after!")
            os.utime(
                dependency,
                ns=(before_stat.st_atime_ns, before_stat.st_mtime_ns),
            )
            after = manifest_module._build_target_artifact_snapshot(
                root, "Fixture.PaperInterface"
            )

        self.assertIsNotNone(before)
        self.assertIsNotNone(after)
        self.assertNotEqual(before, after)
        self.assertEqual(
            dict(before or ())["Fixture.PaperInterface"],
            dict(after or ())["Fixture.PaperInterface"],
        )

    def test_check_preview_parser_keeps_unindented_let_chain(self) -> None:
        output = """@first :
let quota := 3
quota = 3
@second : True
"""
        self.assertEqual(
            review_dashboard._parse_lean_check_previews(output, ["first", "second"]),
            {
                "first": "let quota := 3 quota = 3",
                "second": "True",
            },
        )

    def test_binder_and_declaration_renaming_preserve_digest(self) -> None:
        source = """
universe u
axiom first {alpha : Type u} [DecidableEq alpha] (x : alpha)
  (h : x = x) : x = x
axiom unrelatedName {beta : Type u} [DecidableEq beta] (y : beta)
  (proof : y = y) : y = y
"""
        manifests = self.manifests(source, ["first", "unrelatedName"])
        self.assertEqual(
            manifests["first"]["sha256"], manifests["unrelatedName"]["sha256"]
        )
        self.assertEqual(
            manifests["first"]["semantic_dependency_manifest"][
                "semantic_dependency_sha256"
            ],
            manifests["unrelatedName"]["semantic_dependency_manifest"][
                "semantic_dependency_sha256"
            ],
        )

    def test_implicit_instance_and_proposition_binders_are_all_atoms(self) -> None:
        source = """
universe u
axiom checked {alpha : Type u} [DecidableEq alpha] (x : alpha)
  (h : x = x) : x = x
"""
        manifest = self.manifests(source, ["checked"])["checked"]
        roles = [atom["role"] for atom in manifest["atoms"]]
        infos = [atom.get("binder_info") for atom in manifest["atoms"][:-1]]
        self.assertEqual(
            roles, ["parameter", "parameter", "parameter", "assumption", "conclusion"]
        )
        self.assertEqual(infos, ["implicit", "instImplicit", "explicit", "explicit"])

    def test_domain_and_conclusion_changes_change_digest(self) -> None:
        source = """
axiom natDomain (x : Nat) : x = x
axiom intDomain (x : Int) : x = x
axiom differentResult (x : Nat) : True
"""
        manifests = self.manifests(
            source, ["natDomain", "intDomain", "differentResult"]
        )
        baseline = manifests["natDomain"]["sha256"]
        self.assertNotEqual(baseline, manifests["intDomain"]["sha256"])
        self.assertNotEqual(baseline, manifests["differentResult"]["sha256"])

    def test_anonymous_arrows_are_binder_atoms(self) -> None:
        source = "axiom arrowRow : True → False → True\n"
        atoms = self.manifests(source, ["arrowRow"])["arrowRow"]["atoms"]
        self.assertEqual([atom["ref"] for atom in atoms], ["b/0", "b/1", "result"])
        self.assertEqual(
            [atom["role"] for atom in atoms], ["assumption", "assumption", "conclusion"]
        )

    def test_execution_state_refinement_shape_uses_elaborated_types_not_names(
        self,
    ) -> None:
        source = """
import Mathlib
structure FirstTrace (State : Type) where
  transition : State -> State -> Prop
  initial : State
  terminal : State
  run : Relation.ReflTransGen transition initial terminal
structure RenamedContainer (Carrier : Type) where
  unrelatedBinaryValue : Carrier -> Carrier -> Prop
  beginning : Carrier
  ending : Carrier
  evidence : Relation.ReflTransGen unrelatedBinaryValue beginning ending
structure RelationOnly (Carrier : Type) where
  unrelatedBinaryValue : Carrier -> Carrier -> Prop
inductive CustomTrail {Node : Type} (edge : Node -> Node -> Prop) :
    Node -> Node -> Prop where
  | single (start finish : Node) :
      edge start finish -> CustomTrail edge start finish
inductive ArbitraryReach {Point : Type} (law : Point -> Point -> Prop) :
    Point -> Point -> Prop where
  | link (left right : Point) :
      law left right -> ArbitraryReach law left right
structure CustomTrace (Node : Type) where
  edge : Node -> Node -> Prop
  start : Node
  finish : Node
  witness : CustomTrail edge start finish
structure ArbitrarilyNamedPayload (Point : Type) where
  rule : Point -> Point -> Prop
  left : Point
  right : Point
  certificate : ArbitraryReach rule left right
axiom firstEndpoint {State : Type} (trace : FirstTrace State) : True
axiom renamedEndpoint {Carrier : Type} (payload : RenamedContainer Carrier) : True
axiom ordinaryEndpoint {Carrier : Type} (payload : RelationOnly Carrier) : True
axiom customEndpoint {Node : Type} (trace : CustomTrace Node) : True
axiom arbitraryEndpoint {Point : Type}
    (payload : ArbitrarilyNamedPayload Point) : True
"""
        manifests = self.manifests(
            source,
            [
                "firstEndpoint",
                "renamedEndpoint",
                "ordinaryEndpoint",
                "customEndpoint",
                "arbitraryEndpoint",
            ],
        )
        first = manifests["firstEndpoint"][
            "elaborated_execution_state_refinement_shape"
        ]
        renamed = manifests["renamedEndpoint"][
            "elaborated_execution_state_refinement_shape"
        ]
        ordinary = manifests["ordinaryEndpoint"][
            "elaborated_execution_state_refinement_shape"
        ]
        custom = manifests["customEndpoint"][
            "elaborated_execution_state_refinement_shape"
        ]
        arbitrary = manifests["arbitraryEndpoint"][
            "elaborated_execution_state_refinement_shape"
        ]

        self.assertEqual(first["schema"], 2)
        self.assertEqual(
            first["detector_basis"],
            "lean_statement_dependency_graph_structural_v1",
        )
        self.assertTrue(first["scan_complete"])
        self.assertTrue(first["has_refl_trans_gen_path"])
        self.assertTrue(first["has_relation_valued_state_transition"])
        self.assertTrue(first["detected"])
        self.assertEqual(
            {
                key: renamed[key]
                for key in (
                    "scan_complete",
                    "has_refl_trans_gen_path",
                    "has_relation_valued_state_transition",
                    "detected",
                )
            },
            {
                key: first[key]
                for key in (
                    "scan_complete",
                    "has_refl_trans_gen_path",
                    "has_relation_valued_state_transition",
                    "detected",
                )
            },
        )
        self.assertFalse(ordinary["has_refl_trans_gen_path"])
        self.assertFalse(ordinary["detected"])
        for shape in (custom, arbitrary):
            self.assertTrue(shape["scan_complete"])
            self.assertTrue(shape["has_refl_trans_gen_path"])
            self.assertTrue(shape["has_relation_valued_state_transition"])
            self.assertTrue(shape["detected"])

        malformed = json.loads(json.dumps(manifests["firstEndpoint"]))
        malformed["elaborated_execution_state_refinement_shape"]["detector_basis"] = (
            "untrusted_detector"
        )
        self.assertIsNone(manifest_module.normalize_signature_manifest(malformed))
        self.assertIsNone(manifest_module.semantic_dependency_manifest(malformed))

        baseline_dependency = manifest_module.semantic_dependency_manifest(
            manifests["firstEndpoint"]
        )
        changed_shape = json.loads(json.dumps(manifests["firstEndpoint"]))
        changed_shape["elaborated_execution_state_refinement_shape"].update(
            {
                "has_refl_trans_gen_path": False,
                "detected": False,
            }
        )
        changed_dependency = manifest_module.semantic_dependency_manifest(changed_shape)
        self.assertIsNotNone(baseline_dependency)
        self.assertIsNotNone(changed_dependency)
        assert baseline_dependency is not None and changed_dependency is not None
        self.assertNotEqual(
            baseline_dependency["semantic_dependency_sha256"],
            changed_dependency["semantic_dependency_sha256"],
        )

    def test_transparent_definition_value_telescope_preserves_written_outer_binders(
        self,
    ) -> None:
        source = """
def terminal (n : Nat) : Prop := n = n
def sourceSpec (Carrier : Type) : Prop := ∀ alpha : List (Fin 2), terminal alpha.length
"""
        manifest = self.manifests(source, ["sourceSpec"])["sourceSpec"]
        presentation = manifest["transparent_value_presentation_telescope"]
        self.assertIsInstance(presentation, dict)
        assert isinstance(presentation, dict)
        self.assertEqual(presentation["schema"], 1)
        self.assertEqual(
            presentation["reduction"], "definition_value_outer_telescope"
        )
        atoms = presentation["atoms"]
        self.assertEqual([atom["ref"] for atom in atoms], ["b/0", "b/1", "result"])
        self.assertEqual(
            [atom["role"] for atom in atoms],
            ["parameter", "parameter", "conclusion"],
        )
        self.assertEqual(atoms[0]["display"], "Type")
        self.assertEqual(atoms[1]["display"], "List (Fin 2)")
        self.assertIn("terminal", atoms[2]["display"])

        normalized = manifest_module.normalize_signature_manifest(manifest)
        self.assertIsNotNone(normalized)
        assert normalized is not None
        self.assertEqual(
            normalized["transparent_value_presentation_telescope"],
            presentation,
        )

    def test_transparent_definition_value_telescope_preserves_terminal_negation(
        self,
    ) -> None:
        source = """
def Property (n : Nat) : Prop := n = n
def negativeSpec : Prop := ∀ n : Nat, n > 0 → ¬ Property n
axiom negativeProof (n : Nat) (h : n > 0) : ¬ Property n
"""
        manifests = self.manifests(source, ["negativeSpec", "negativeProof"])
        presentation = manifests["negativeSpec"][
            "transparent_value_presentation_telescope"
        ]
        self.assertIsInstance(presentation, dict)
        assert isinstance(presentation, dict)
        self.assertEqual(
            [atom["role"] for atom in presentation["atoms"]],
            ["parameter", "assumption", "conclusion"],
        )
        self.assertIn("¬Property", presentation["atoms"][-1]["display"])
        self.assertEqual(
            [atom["role"] for atom in manifests["negativeProof"]["atoms"]],
            ["parameter", "assumption", "assumption", "conclusion"],
        )
        self.assertEqual(
            manifests["negativeProof"]["atoms"][-1]["display"], "False"
        )

    def test_review_display_exposes_material_existential_witness_domain(self) -> None:
        source = """
def witnessSpec : Prop :=
  ∃ packet : {values : List Nat // values.length ≤ 3}, packet.1.length ≤ 3
"""
        manifest = self.manifests(source, ["witnessSpec"])["witnessSpec"]
        presentation = manifest["transparent_value_presentation_telescope"]
        result_display = presentation["atoms"][-1]["display"]
        self.assertIn("packet : { values : List Nat // values.length ≤ 3 }", result_display)
        self.assertIn("packet.val.length ≤ 3", result_display)

        surface = manifest_module.review_claim_atom_surface(manifest)
        self.assertIsNotNone(surface)
        assert surface is not None
        target = manifest_module.review_claim_target_text(
            {
                "display": result_display,
                "review_claim_atoms": surface["claim_atoms"],
                "review_claim_atoms_sha256": surface["claim_atoms_sha256"],
            }
        )
        self.assertIn("packet : { values : List Nat // values.length ≤ 3 }", target)

    def test_review_display_does_not_elide_proof_irrelevant_arguments(self) -> None:
        """A semantic reviewer must never receive Lean's `⋯` placeholder."""

        source = """
def sourceMass (rate : Nat) (_rate_pos : 0 < rate) : Nat := rate
def sourceSpec (rate : Nat) (rate_pos : 0 < rate) : Prop :=
  sourceMass rate rate_pos = rate
"""
        manifest = self.manifests(source, ["sourceSpec"])["sourceSpec"]
        surface = manifest_module.review_claim_atom_surface(manifest)
        self.assertIsNotNone(surface)
        assert surface is not None
        rendered = "\n".join(
            str(atom["display"]) for atom in surface["claim_atoms"]
        )
        self.assertNotIn("⋯", rendered)
        self.assertIn("sourceMass rate rate_pos", rendered)

    def test_review_claim_surface_uses_only_lean_emitted_atom_roles(self) -> None:
        source = """
def sourceSpec (n : Nat) (header : n = n) : Prop :=
  (n > 0) → ¬ n < 0
def sourceValue (n : Nat) : Nat := n + 1
"""
        manifests = self.manifests(source, ["sourceSpec", "sourceValue"])

        spec_surface = manifest_module.review_claim_atom_surface(
            manifests["sourceSpec"]
        )
        self.assertIsNotNone(spec_surface)
        assert spec_surface is not None
        self.assertEqual(
            [atom["role"] for atom in spec_surface["claim_atoms"]],
            ["parameter", "assumption", "assumption", "conclusion"],
        )
        self.assertIn("¬", spec_surface["claim_atoms"][-1]["display"])
        self.assertRegex(spec_surface["claim_atoms_sha256"], r"^[0-9a-f]{64}$")

        value_surface = manifest_module.review_claim_atom_surface(
            manifests["sourceValue"]
        )
        self.assertIsNotNone(value_surface)
        assert value_surface is not None
        self.assertEqual(
            [atom["role"] for atom in value_surface["claim_atoms"]],
            ["parameter", "conclusion"],
        )

        malformed = json.loads(json.dumps(manifests["sourceSpec"]))
        malformed["transparent_value_presentation_telescope"]["atoms"][-1][
            "role"
        ] = "assumption"
        self.assertIsNone(manifest_module.review_claim_atom_surface(malformed))

    def test_reducible_alias_cannot_hide_binders(self) -> None:
        source = """
abbrev Wrapped : Prop := ∀ n : Nat, n = n
axiom throughAlias : Wrapped
axiom writtenDirectly : ∀ value : Nat, value = value
"""
        manifests = self.manifests(source, ["throughAlias", "writtenDirectly"])
        self.assertEqual(
            manifests["throughAlias"]["sha256"],
            manifests["writtenDirectly"]["sha256"],
        )
        self.assertEqual(
            [atom["ref"] for atom in manifests["throughAlias"]["atoms"]],
            ["b/0", "result"],
        )

    def test_result_let_is_zeta_normalized_before_manifest_serialization(self) -> None:
        source = """
def rawLaw : Nat := 1
theorem zetaRow : let law := rawLaw; law = rawLaw := rfl
"""
        canonical = self.manifests(source, ["zetaRow"])["zetaRow"]["atoms"][-1][
            "canonical"
        ]
        self.assertIsInstance(canonical, dict)
        self.assertNotEqual(canonical.get("tag"), "let")
        _head, arguments = audit_repository._canonical_application_head_and_args(
            canonical
        )
        self.assertGreaterEqual(len(arguments), 2)
        self.assertEqual(arguments[-2], arguments[-1])

    def test_prop_definition_body_is_name_independent_and_body_sensitive(self) -> None:
        source = """
abbrev firstPredicate (x : Nat) : Prop := x = 0
abbrev renamedPredicate (value : Nat) : Prop := value = 0
abbrev changedPredicate (x : Nat) : Prop := x = 1
"""
        manifests = self.manifests(
            source, ["firstPredicate", "renamedPredicate", "changedPredicate"]
        )
        self.assertEqual(
            manifests["firstPredicate"]["sha256"],
            manifests["renamedPredicate"]["sha256"],
        )
        self.assertNotEqual(
            manifests["firstPredicate"]["sha256"],
            manifests["changedPredicate"]["sha256"],
        )

    def test_data_definition_body_is_name_independent_and_body_sensitive(self) -> None:
        source = """
def firstFormula (x : Nat) : Nat := x + 1
def renamedFormula (value : Nat) : Nat := value + 1
def changedFormula (x : Nat) : Nat := x + 2
"""
        manifests = self.manifests(
            source, ["firstFormula", "renamedFormula", "changedFormula"]
        )
        self.assertEqual(
            manifests["firstFormula"]["sha256"],
            manifests["renamedFormula"]["sha256"],
        )
        self.assertNotEqual(
            manifests["firstFormula"]["sha256"],
            manifests["changedFormula"]["sha256"],
        )

    def test_root_structure_fields_are_name_independent_and_semantically_frozen(
        self,
    ) -> None:
        source = """
structure FirstPackage : Prop where
  conclusion : True
structure RenamedPackage : Prop where
  unrelatedFieldName : True
structure AddedPremisePackage : Prop where
  secretPremise : False
  conclusion : True
structure ChangedConclusionPackage : Prop where
  conclusion : False
"""
        manifests = self.manifests(
            source,
            [
                "FirstPackage",
                "RenamedPackage",
                "AddedPremisePackage",
                "ChangedConclusionPackage",
            ],
        )
        baseline = manifests["FirstPackage"]
        self.assertEqual(baseline["sha256"], manifests["RenamedPackage"]["sha256"])
        self.assertNotEqual(
            baseline["sha256"], manifests["AddedPremisePackage"]["sha256"]
        )
        self.assertNotEqual(
            baseline["sha256"], manifests["ChangedConclusionPackage"]["sha256"]
        )
        self.assertEqual(baseline["atoms"][-1]["canonical"]["tag"], "inductive")
        self.assertTrue(
            review_dashboard.is_proposition_specification_manifest(baseline)
        )

    def test_root_inductive_constructors_are_name_independent_and_semantically_frozen(
        self,
    ) -> None:
        source = """
inductive FirstTree where
  | empty : FirstTree
  | branch : Nat -> FirstTree
inductive RenamedTree where
  | unrelatedEmpty : RenamedTree
  | unrelatedBranch : Nat -> RenamedTree
inductive ChangedTree where
  | empty : ChangedTree
  | branch : Int -> ChangedTree
"""
        manifests = self.manifests(source, ["FirstTree", "RenamedTree", "ChangedTree"])
        self.assertEqual(
            manifests["FirstTree"]["sha256"], manifests["RenamedTree"]["sha256"]
        )
        self.assertNotEqual(
            manifests["FirstTree"]["sha256"], manifests["ChangedTree"]["sha256"]
        )

    def test_expanded_local_inductive_constructors_do_not_break_import_closure(
        self,
    ) -> None:
        source = """
inductive LocalThreshold where
  | negInf : LocalThreshold
  | finite : Nat -> LocalThreshold
  | posInf : LocalThreshold
abbrev LocalThresholdAlias := LocalThreshold
def endpoint : LocalThresholdAlias := LocalThreshold.negInf
theorem thresholdRow : ∃ threshold : Nat → LocalThreshold, threshold 0 = endpoint := by
  exact ⟨fun _ => endpoint, rfl⟩
"""
        manifests = manifest_module._run_manifest_script(
            ROOT,
            f"import Lean\n{source}",
            ["thresholdRow"],
            120,
        )
        self.assertEqual(set(manifests), {"thresholdRow"})
        self.assertTrue(manifests["thresholdRow"]["sha256"])

    def test_theorem_proof_body_remains_outside_manifest(self) -> None:
        source = """
theorem firstProof (x : Nat) : x = x := rfl
theorem unrelatedProofName (value : Nat) : value = value := by simp
"""
        manifests = self.manifests(source, ["firstProof", "unrelatedProofName"])
        self.assertEqual(
            manifests["firstProof"]["sha256"],
            manifests["unrelatedProofName"]["sha256"],
        )

    def test_proposition_spec_requires_matching_theorem_type(self) -> None:
        source = """
def targetSpec (x : Nat) : Prop := x = x
theorem targetProof (x : Nat) : targetSpec x := rfl
theorem wrongProof (x : Nat) : True := True.intro
"""
        manifests = self.manifests(source, ["targetSpec", "targetProof", "wrongProof"])
        self.assertTrue(
            review_dashboard.is_proposition_definition_manifest(manifests["targetSpec"])
        )
        routes = [("targetSpec", "targetProof"), ("targetSpec", "wrongProof")]
        matches = run_lean_proposition_spec_proof_matches_for_source(
            ROOT, source, routes
        )
        self.assertTrue(matches[("targetSpec", "targetProof")])
        self.assertFalse(matches[("targetSpec", "wrongProof")])

    def test_proposition_spec_route_handles_inner_forall_and_implication(self) -> None:
        source = """
def targetSpec (n : Nat) : Prop := ∀ m : Nat, m = n → n = m
theorem targetProof (n : Nat) : targetSpec n := by
  intro m h
  exact h.symm
theorem expandedProof (n m : Nat) : m = n → n = m := by
  intro h
  exact h.symm
theorem extraHypothesis (n : Nat) (h : n = n) : targetSpec n := by
  intro m hm
  exact hm.symm
theorem wrongConclusion (n : Nat) : ∀ m : Nat, m = n → m = n := by
  intro m h
  exact h
"""
        routes = [
            ("targetSpec", "targetProof"),
            ("targetSpec", "expandedProof"),
            ("targetSpec", "extraHypothesis"),
            ("targetSpec", "wrongConclusion"),
        ]
        matches = run_lean_proposition_spec_proof_matches_for_source(
            ROOT, source, routes
        )
        self.assertEqual(set(matches), set(routes))
        self.assertTrue(matches[("targetSpec", "targetProof")])
        self.assertTrue(matches[("targetSpec", "expandedProof")])
        self.assertFalse(matches[("targetSpec", "extraHypothesis")])
        self.assertFalse(matches[("targetSpec", "wrongConclusion")])

    def test_prop_structure_requires_and_accepts_a_matching_theorem_route(self) -> None:
        source = """
structure Claim (n : Nat) : Prop where
  evidence : n = n
theorem claimProof (n : Nat) : Claim n := by
  exact Claim.mk rfl
theorem wrongProof (n : Nat) : True := True.intro
"""
        manifests = self.manifests(source, ["Claim", "claimProof", "wrongProof"])
        self.assertTrue(
            review_dashboard.is_proposition_specification_manifest(manifests["Claim"])
        )
        routes = [("Claim", "claimProof"), ("Claim", "wrongProof")]
        matches = run_lean_proposition_spec_proof_matches_for_source(
            ROOT, source, routes
        )
        self.assertTrue(matches[("Claim", "claimProof")])
        self.assertFalse(matches[("Claim", "wrongProof")])

    def test_proposition_spec_route_preserves_universe_generality(self) -> None:
        source = """
universe u v
def polySpec {alpha : Type u} (x : alpha) : Prop := x = x
theorem renamedPolyProof {beta : Type v} (y : beta) : polySpec y := rfl
theorem monoProof {alpha : Type} (x : alpha) : polySpec x := rfl
"""
        routes = [
            ("polySpec", "renamedPolyProof"),
            ("polySpec", "monoProof"),
        ]
        matches = run_lean_proposition_spec_proof_matches_for_source(
            ROOT, source, routes
        )
        self.assertEqual(set(matches), set(routes))
        self.assertTrue(matches[("polySpec", "renamedPolyProof")])
        self.assertFalse(matches[("polySpec", "monoProof")])

    def test_constructor_result_type_match_preserves_parameters_and_universes(
        self,
    ) -> None:
        source = """
universe u
structure Parcel (alpha : Type u) (n : Nat) where
  value : alpha

def genericParcel {alpha : Type u} (m : Nat) (x : alpha) : Parcel alpha m :=
  ⟨x⟩
def fixedParcel {alpha : Type u} (x : alpha) : Parcel alpha 0 :=
  ⟨x⟩
abbrev AliasParcel (alpha : Type u) (n : Nat) := Parcel alpha n
def aliasParcel {alpha : Type u} (m : Nat) (x : alpha) : AliasParcel alpha m :=
  ⟨x⟩
def shiftedParcel {alpha : Type u} (m : Nat) (x : alpha) : Parcel alpha (m + 1) :=
  ⟨x⟩
axiom reviewedParcel {alpha : Type u} (n : Nat) (payload : Parcel alpha n) : True
axiom reviewedParcelZero {alpha : Type u} (payload : Parcel alpha 0) : True
"""
        routes = [
            ("reviewedParcel", "payload", "genericParcel"),
            ("reviewedParcel", "payload", "fixedParcel"),
            ("reviewedParcel", "payload", "aliasParcel"),
            ("reviewedParcel", "payload", "shiftedParcel"),
            ("reviewedParcelZero", "payload", "fixedParcel"),
        ]
        matches = run_lean_constructor_result_type_matches_for_source(
            ROOT, source, routes
        )
        self.assertEqual(set(matches), set(routes))
        self.assertTrue(matches[("reviewedParcel", "payload", "genericParcel")])
        self.assertTrue(matches[("reviewedParcel", "payload", "aliasParcel")])
        self.assertFalse(matches[("reviewedParcel", "payload", "fixedParcel")])
        self.assertFalse(matches[("reviewedParcel", "payload", "shiftedParcel")])
        self.assertTrue(matches[("reviewedParcelZero", "payload", "fixedParcel")])

    def test_recursive_field_payload_safety_uses_elaborated_slots(self) -> None:
        source = """
structure Safe (n : Nat) where
  bounded : Fin n
  finite : Finset Nat
structure Indexed (P : Prop) [Decidable P] where
  witness : Fin (if P then 1 else 0)
structure Contra (P : Prop) [Decidable P] where
  witness : Fin (if P then 1 else 0) -> Fin 0
structure GenericFunction (A : Type) where
  witness : A -> Fin 0
structure Relations (A : Type) where
  relation : A -> Prop
inductive Pack (P : Prop) [Decidable P] : Nat -> Type
  | mk (n : Nat) (w : Fin (if P then n + 1 else 0)) : Pack P n
inductive Weird (P : Prop) [Decidable P] : Nat -> Type
  | mk (w : Fin (if P then 1 else 0)) : Weird P w.val
inductive Mixed (P : Prop) [Decidable P] : Nat -> Type
  | mk (n : Nat) (w : Fin (if P then 1 else 0)) : Mixed P w.val
inductive RenamedWeird (Q : Prop) [Decidable Q] : Nat -> Type
  | alternate (payload : Fin (if Q then 1 else 0)) : RenamedWeird Q payload.val
structure RenamedOne where
  alpha : Finset Nat
structure RenamedTwo where
  beta : Finset Nat
structure ParenthesizedAlpha where
  visible : Nat
  (hidden : False)
class ParenthesizedBeta where
  visible : Nat
  (renamedHidden : False)
"""

        def projection(name: str, index: int) -> dict[str, object]:
            locator: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": name,
                "field_index": index,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        def constructor(name: str, index: int) -> dict[str, object]:
            locator = {
                "schema": 1,
                "kind": "constructor_argument",
                "constructor": name,
                "field_index": index,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        locators = [
            projection("Safe.bounded", 0),
            projection("Safe.finite", 1),
            projection("Indexed.witness", 0),
            projection("Contra.witness", 0),
            projection("GenericFunction.witness", 0),
            projection("Relations.relation", 0),
            constructor("Pack.mk", 0),
            constructor("Weird.mk", 0),
            constructor("Mixed.mk", 0),
            constructor("Mixed.mk", 1),
            constructor("RenamedWeird.alternate", 0),
            projection("RenamedOne.alpha", 0),
            projection("RenamedTwo.beta", 0),
            projection("ParenthesizedAlpha.hidden", 1),
            projection("ParenthesizedBeta.renamedHidden", 1),
        ]
        receipts = run_lean_recursive_field_proposition_sorts_for_source(
            ROOT, source, locators
        )
        self.assertEqual(
            set(receipts),
            {str(locator["field_identity_sha256"]) for locator in locators},
        )
        by_declaration = {
            str(receipt.get("declaration") or receipt.get("constructor")): receipt
            for receipt in receipts.values()
        }
        self.assertEqual(
            by_declaration["Safe.bounded"]["payload_safety"],
            "requires_source_or_lean_closure",
        )
        self.assertEqual(
            by_declaration["Safe.finite"]["payload_safety"], "structural_data"
        )
        for declaration in (
            "Indexed.witness",
            "Contra.witness",
            "GenericFunction.witness",
            "Relations.relation",
            "Pack.mk",
            "Weird.mk",
            "RenamedWeird.alternate",
        ):
            self.assertIn(
                by_declaration[declaration]["payload_safety"],
                {"requires_source_or_lean_closure", "requires_semantic_route"},
            )
        self.assertEqual(
            by_declaration["Relations.relation"]["payload_safety"],
            "requires_semantic_route",
        )
        self.assertEqual(
            by_declaration["RenamedOne.alpha"]["payload_safety"],
            by_declaration["RenamedTwo.beta"]["payload_safety"],
        )
        self.assertEqual(
            by_declaration["RenamedOne.alpha"]["normalized_type_sha256"],
            by_declaration["RenamedTwo.beta"]["normalized_type_sha256"],
        )
        self.assertEqual(
            by_declaration["Weird.mk"]["payload_safety"],
            by_declaration["RenamedWeird.alternate"]["payload_safety"],
        )
        for declaration in (
            "ParenthesizedAlpha.hidden",
            "ParenthesizedBeta.renamedHidden",
        ):
            self.assertEqual(by_declaration[declaration]["value_sort"], "true")
            self.assertEqual(
                by_declaration[declaration]["payload_safety"], "proof_payload"
            )
        mixed_slots = {
            int(receipt["field_index"]): receipt
            for receipt in receipts.values()
            if receipt.get("constructor") == "Mixed.mk"
        }
        self.assertEqual(mixed_slots[0]["payload_safety"], "structural_data")
        self.assertIn(
            mixed_slots[1]["payload_safety"],
            {"requires_source_or_lean_closure", "requires_semantic_route"},
        )
        self.assertEqual(
            run_lean_constructor_field_slot_counts_for_source(
                ROOT,
                source,
                [
                    "Pack.mk",
                    "Weird.mk",
                    "Mixed.mk",
                    "RenamedWeird.alternate",
                    "ParenthesizedAlpha.mk",
                    "ParenthesizedBeta.mk",
                ],
            ),
            {
                "Pack.mk": 1,
                "Weird.mk": 1,
                "Mixed.mk": 2,
                "RenamedWeird.alternate": 1,
                "ParenthesizedAlpha.mk": 2,
                "ParenthesizedBeta.mk": 2,
            },
        )
        self.assertEqual(
            run_lean_inductive_constructor_field_slot_counts_for_source(
                ROOT,
                source,
                ["Pack", "Weird", "Mixed", "RenamedWeird"],
            ),
            {
                "Pack": {"Pack.mk": 1},
                "Weird": {"Weird.mk": 1},
                "Mixed": {"Mixed.mk": 2},
                "RenamedWeird": {"RenamedWeird.alternate": 1},
            },
        )

    def test_recursive_field_safety_preserves_sort_and_nnreal_review_routes(
        self,
    ) -> None:
        source = """
import Mathlib.Data.NNReal.Defs
structure AuditNestedCarrier (A : Type) where
  payload : A
structure Surface where
  probabilityScale : NNReal
  semanticCondition : Prop
  carrier : Type
structure Outer (A : Type) where
  nested : AuditNestedCarrier A
"""

        def projection(name: str, index: int) -> dict[str, object]:
            locator: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": name,
                "field_index": index,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        locators = [
            projection("Surface.probabilityScale", 0),
            projection("Surface.semanticCondition", 1),
            projection("Surface.carrier", 2),
            projection("Outer.nested", 0),
        ]
        receipts = run_lean_recursive_field_proposition_sorts_for_source(
            ROOT, source, locators
        )
        by_declaration = {
            str(receipt["declaration"]): receipt for receipt in receipts.values()
        }
        self.assertEqual(
            by_declaration["Surface.probabilityScale"]["payload_safety"],
            "structural_data",
        )
        self.assertEqual(
            by_declaration["Surface.probabilityScale"]["foundation_head"],
            "NNReal",
        )
        for declaration in ("Surface.semanticCondition", "Surface.carrier"):
            self.assertEqual(
                by_declaration[declaration]["payload_safety"],
                "requires_semantic_route",
            )
            self.assertEqual(by_declaration[declaration]["route"], "sort_carrier")
        self.assertEqual(
            by_declaration["Outer.nested"]["payload_safety"],
            "requires_source_or_lean_closure",
        )

    def test_indexed_constructor_direct_prop_slots_have_exact_receipts(self) -> None:
        """Direct Prop fields retain exact Lean receipts beside data slots."""

        source = """
inductive IndexedTransition (P : Prop) : Nat -> Nat -> Prop
  | advance {before after : Nat} (winner : Nat)
      (hnotTerminal : Not (before = after))
      (hactive : P)
      (hquota : winner = winner) : IndexedTransition P before after
"""

        def constructor(index: int) -> dict[str, object]:
            locator: dict[str, object] = {
                "schema": 1,
                "kind": "constructor_argument",
                "constructor": "IndexedTransition.advance",
                "field_index": index,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        locators = [constructor(index) for index in range(4)]
        receipts = run_lean_recursive_field_proposition_sorts_for_source(
            ROOT, source, locators
        )
        self.assertEqual(
            set(receipts),
            {str(locator["field_identity_sha256"]) for locator in locators},
        )
        slots = {int(receipt["field_index"]): receipt for receipt in receipts.values()}
        self.assertEqual(slots[0]["value_sort"], "false")
        self.assertEqual(slots[0]["payload_safety"], "structural_data")
        for index in (1, 2, 3):
            self.assertEqual(slots[index]["value_sort"], "true")
            self.assertEqual(slots[index]["payload_safety"], "proof_payload")
            self.assertRegex(
                str(slots[index]["normalized_type_sha256"]), r"^[0-9a-f]{64}$"
            )
        self.assertEqual(
            run_lean_inductive_constructor_field_slot_counts_for_source(
                ROOT, source, ["IndexedTransition"]
            ),
            {"IndexedTransition": {"IndexedTransition.advance": 4}},
        )

    def test_ggrs_transition_and_policy_slots_do_not_discard_receipt_batch(
        self,
    ) -> None:
        """Regression for the paper's mixed relation, data, and proof slots."""

        module = "GGRS26CombattingGerrymanderingRCV.BallotRoutedSTV"
        policy_constructor = (
            "GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVTransferPolicy.mk"
        )
        constructors = [
            policy_constructor,
            "GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVTransition.elect",
            "GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVTransition.eliminate",
        ]
        locators: list[dict[str, object]] = []
        for constructor_name in constructors:
            for field_index in range(8):
                locator: dict[str, object] = {
                    "schema": 1,
                    "kind": "constructor_argument",
                    "constructor": constructor_name,
                    "field_index": field_index,
                }
                locator["field_identity_sha256"] = (
                    recursive_field_safety_locator_identity(locator)
                )
                locators.append(locator)
        receipts = run_lean_recursive_field_proposition_sorts(ROOT, module, locators)
        self.assertEqual(
            set(receipts),
            {str(locator["field_identity_sha256"]) for locator in locators},
        )
        proof_marker_sha256 = hashlib.sha256(
            b"unserializable_elaborated_field_type:true:proof_payload:direct_proposition"
        ).hexdigest()
        relation_marker_sha256 = hashlib.sha256(
            b"unserializable_elaborated_field_type:false:requires_semantic_route:predicate_or_relation"
        ).hexdigest()
        policy_slots = {
            int(receipt["field_index"]): receipt
            for receipt in receipts.values()
            if receipt.get("constructor") == policy_constructor
        }
        self.assertEqual(set(policy_slots), set(range(8)))
        for field_index in (0, 1):
            self.assertEqual(policy_slots[field_index]["value_sort"], "false")
            self.assertEqual(
                policy_slots[field_index]["payload_safety"], "requires_semantic_route"
            )
            self.assertEqual(
                policy_slots[field_index]["normalized_type_sha256"],
                relation_marker_sha256,
            )
        for field_index in range(2, 8):
            self.assertEqual(policy_slots[field_index]["value_sort"], "true")
            self.assertEqual(
                policy_slots[field_index]["payload_safety"], "proof_payload"
            )
            self.assertEqual(
                policy_slots[field_index]["normalized_type_sha256"],
                proof_marker_sha256,
            )
        for constructor_name in constructors[1:]:
            slots = {
                int(receipt["field_index"]): receipt
                for receipt in receipts.values()
                if receipt.get("constructor") == constructor_name
            }
            self.assertEqual(set(slots), set(range(8)))
            self.assertEqual(slots[0]["value_sort"], "false")
            self.assertEqual(
                slots[0]["payload_safety"], "requires_source_or_lean_closure"
            )
            self.assertRegex(str(slots[0]["normalized_type_sha256"]), r"^[0-9a-f]{64}$")
            self.assertNotIn(
                slots[0]["normalized_type_sha256"],
                {proof_marker_sha256, relation_marker_sha256},
            )
            for field_index in range(1, 8):
                self.assertEqual(slots[field_index]["value_sort"], "true")
                self.assertEqual(slots[field_index]["payload_safety"], "proof_payload")
                self.assertEqual(
                    slots[field_index]["normalized_type_sha256"],
                    proof_marker_sha256,
                )

    def test_type_witness_payload_safety_catches_wrapped_and_opaque_witnesses(
        self,
    ) -> None:
        source = """
opaque Hidden (P : Prop) : Type
opaque ImportedStyleBox : Type -> Prop
axiom nonemptyWitness (P : Prop) : Nonempty (PLift.{0} P)
axiom existsSubtype (P : Prop) : Exists (fun _ : {n : Nat // P} => True)
axiom opaqueWitness (P : Prop) : Nonempty (Hidden P)
axiom boxedWitness (P : Prop) : ImportedStyleBox (PLift.{0} P)
axiom safeWitness : Nonempty (Fin 3)
"""
        receipts = run_lean_type_witness_payload_safeties_for_source(
            ROOT,
            source,
            [
                "nonemptyWitness",
                "existsSubtype",
                "opaqueWitness",
                "boxedWitness",
                "safeWitness",
            ],
        )
        self.assertEqual(
            set(receipts),
            {
                "nonemptyWitness",
                "existsSubtype",
                "opaqueWitness",
                "boxedWitness",
                "safeWitness",
            },
        )
        for declaration in (
            "nonemptyWitness",
            "existsSubtype",
            "opaqueWitness",
            "boxedWitness",
        ):
            self.assertTrue(receipts[declaration])
            self.assertNotEqual(
                receipts[declaration][0]["payload_safety"], "structural_data"
            )
        self.assertEqual(
            receipts["safeWitness"][0]["payload_safety"],
            "requires_source_or_lean_closure",
        )

    def test_type_witness_payload_safety_tracks_productive_logical_role(self) -> None:
        """Lean, not lexical occurrence, decides whether a result supplies a witness."""

        source = """
structure Packet where
  payload : Nat
  obligation : True

axiom positiveNonempty : Nonempty Packet
axiom conjunction : True ∧ Nonempty Packet
axiom antecedentOnly : Nonempty Packet → True
axiom negatedOnly : ¬ Nonempty Packet
axiom negatedAntecedent : (¬ Nonempty Packet) → True
axiom positiveConsequent : True → Nonempty Packet
axiom productiveIff : True ↔ Nonempty Packet
axiom positiveExists : ∃ _p : Packet, True
axiom negatedExists : ¬ ∃ _p : Packet, True
"""
        names = [
            "positiveNonempty",
            "conjunction",
            "antecedentOnly",
            "negatedOnly",
            "negatedAntecedent",
            "positiveConsequent",
            "productiveIff",
            "positiveExists",
            "negatedExists",
        ]
        receipts = run_lean_type_witness_payload_safeties_for_source(
            ROOT, source, names
        )

        self.assertEqual(set(receipts), set(names))
        for declaration in (
            "antecedentOnly",
            "negatedOnly",
            "negatedAntecedent",
            "negatedExists",
        ):
            self.assertEqual(receipts[declaration], [], declaration)
        for declaration in (
            "positiveNonempty",
            "conjunction",
            "positiveConsequent",
            "productiveIff",
            "positiveExists",
        ):
            self.assertEqual(len(receipts[declaration]), 1, declaration)
            receipt = receipts[declaration][0]
            self.assertEqual(receipt["occurrence_role"], "provided_result")
            self.assertEqual(receipt["witness_type_head"], "Packet")
        self.assertTrue(receipts["positiveExists"][0]["path"].endswith("/exists"))
        for declaration in (
            "positiveNonempty",
            "conjunction",
            "positiveConsequent",
            "productiveIff",
        ):
            self.assertTrue(
                receipts[declaration][0]["path"].endswith("/nonempty"),
                declaration,
            )

    def test_type_witness_payload_safety_skips_proof_exists_and_keeps_large_body(
        self,
    ) -> None:
        """Proof binders are not certificate data, but their body still is scanned."""

        witness_count = 64
        witness = "Nonempty (PLift.{0} P)"
        body = witness
        for _ in range(witness_count - 1):
            body = f"({body}) ∧ {witness}"
        source = f"""
axiom proofBoundLargeWitness (P : Prop) : ∃ h : P = P, {body}
"""
        receipts = run_lean_type_witness_payload_safeties_for_source(
            ROOT,
            source,
            ["proofBoundLargeWitness"],
        )
        self.assertEqual(set(receipts), {"proofBoundLargeWitness"})
        large_receipts = receipts["proofBoundLargeWitness"]
        self.assertEqual(len(large_receipts), witness_count)
        paths = {str(receipt["path"]) for receipt in large_receipts}
        self.assertEqual(
            len(paths),
            witness_count,
        )
        self.assertTrue(
            all(receipt["value_sort"] == "false" for receipt in large_receipts)
        )
        self.assertTrue(
            all(
                receipt["payload_safety"] != "proof_payload"
                for receipt in large_receipts
            )
        )

    def test_dependent_indices_reject_nonfoundation_constants(self) -> None:
        """A closed opaque or paper definition cannot become structural data."""

        source = """
opaque hiddenIndex : Nat
opaque renamedHiddenIndex : Nat
def paperLocalIndex : Nat := 2
structure OpaqueIndex where
  payload : Fin hiddenIndex
structure RenamedOpaqueIndex where
  payload : Fin renamedHiddenIndex
structure DefinedIndex where
  payload : Fin paperLocalIndex
structure DirectEmptyFin where
  payload : Fin 0
structure RenamedDirectEmptyFin where
  alternate : Fin 0
structure ProductWithEmptyFin where
  payload : Nat × Fin 0
structure ListWithEmptyFin where
  payload : List (Fin 0)
structure OptionWithEmptyFin where
  payload : Option (Fin 0)
structure FoundationNat where
  payload : Nat
structure FoundationFinset where
  payload : Finset Nat
structure FoundationIndex where
  payload : Fin (Nat.succ 0)
"""

        def projection(name: str) -> dict[str, object]:
            locator: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": name,
                "field_index": 0,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        locators = [
            projection("OpaqueIndex.payload"),
            projection("RenamedOpaqueIndex.payload"),
            projection("DefinedIndex.payload"),
            projection("DirectEmptyFin.payload"),
            projection("RenamedDirectEmptyFin.alternate"),
            projection("ProductWithEmptyFin.payload"),
            projection("ListWithEmptyFin.payload"),
            projection("OptionWithEmptyFin.payload"),
            projection("FoundationNat.payload"),
            projection("FoundationFinset.payload"),
            projection("FoundationIndex.payload"),
        ]
        receipts = run_lean_recursive_field_proposition_sorts_for_source(
            ROOT, source, locators
        )
        by_declaration = {
            str(receipt["declaration"]): receipt for receipt in receipts.values()
        }
        for declaration in (
            "OpaqueIndex.payload",
            "RenamedOpaqueIndex.payload",
            "DefinedIndex.payload",
            "DirectEmptyFin.payload",
            "RenamedDirectEmptyFin.alternate",
            "ProductWithEmptyFin.payload",
            "ListWithEmptyFin.payload",
            "OptionWithEmptyFin.payload",
            "FoundationIndex.payload",
        ):
            with self.subTest(declaration=declaration):
                self.assertEqual(
                    by_declaration[declaration]["payload_safety"],
                    "requires_source_or_lean_closure",
                )
        for declaration in ("FoundationNat.payload", "FoundationFinset.payload"):
            with self.subTest(declaration=declaration):
                self.assertEqual(
                    by_declaration[declaration]["payload_safety"],
                    "structural_data",
                )

    def test_function_payloads_never_receive_structural_data_credit(self) -> None:
        """A function-valued field needs a closure even over foundational types."""

        source = """
structure FunctionContra where
  payload : Nat -> Fin 0
structure RenamedFunctionContra where
  ordinary : Nat -> Fin 0
structure FoundationFunction where
  payload : Nat -> Nat
"""

        def projection(name: str) -> dict[str, object]:
            locator: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": name,
                "field_index": 0,
            }
            locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
                locator
            )
            return locator

        locators = [
            projection("FunctionContra.payload"),
            projection("RenamedFunctionContra.ordinary"),
            projection("FoundationFunction.payload"),
        ]
        receipts = run_lean_recursive_field_proposition_sorts_for_source(
            ROOT, source, locators
        )
        for receipt in receipts.values():
            self.assertEqual(
                receipt["payload_safety"], "requires_source_or_lean_closure"
            )

    def test_type_witness_payload_safety_fails_closed_on_deep_prop_wrappers(
        self,
    ) -> None:
        """Traversal exhaustion may not erase a hidden nonstructural witness."""

        def wrapper_chain(prefix: str, wrapper: str, levels: int) -> str:
            lines = [f"abbrev {prefix}0 (P : Prop) : Prop := Nonempty (PLift.{{0}} P)"]
            lines.extend(
                f"abbrev {prefix}{index} (P : Prop) : Prop := "
                f"{wrapper} ({prefix}{index - 1} P)"
                for index in range(1, levels + 1)
            )
            return "\n".join(lines)

        source = "\n".join(
            [
                "opaque Wrapper : Prop -> Prop",
                "opaque RenamedWrapper : Prop -> Prop",
                wrapper_chain("WithinFuel", "Wrapper", 124),
                wrapper_chain("Deep", "Wrapper", 514),
                wrapper_chain("RenamedDeep", "RenamedWrapper", 514),
                "axiom withinFuelWitness (P : Prop) : WithinFuel124 P",
                "axiom deepWitness (P : Prop) : Deep514 P",
                "axiom renamedDeepWitness (P : Prop) : RenamedDeep514 P",
                "",
            ]
        )
        within_fuel = run_lean_type_witness_payload_safeties_for_source(
            ROOT, source, ["withinFuelWitness"]
        )
        self.assertEqual(set(within_fuel), {"withinFuelWitness"})
        self.assertEqual(
            within_fuel["withinFuelWitness"][0]["payload_safety"],
            "requires_source_or_lean_closure",
        )
        for declaration in ("deepWitness", "renamedDeepWitness"):
            with self.subTest(declaration=declaration):
                self.assertEqual(
                    run_lean_type_witness_payload_safeties_for_source(
                        ROOT, source, [declaration]
                    ),
                    {},
                )

    def test_constructor_result_type_gate_reelaborates_current_source_overlay(
        self,
    ) -> None:
        route = ("Fixture.reviewed", "payload", "Fixture.genericParcel")
        source = """namespace Fixture
structure Parcel (n : Nat) where
  value : Nat
def genericParcel (n : Nat) : Parcel n := ⟨n⟩
axiom reviewed (n : Nat) (payload : Parcel n) : True
end Fixture
"""
        elaborated_sources: list[str] = []

        def fake_run(command: list[str], **_kwargs: object) -> object:
            if command == ["lake", "env"]:
                return type(
                    "Result", (), {"returncode": 0, "stdout": "LEAN_PATH=/lake-path\n"}
                )()
            self.assertEqual(command[:3], ["lake", "env", "env"])
            self.assertTrue(str(command[3]).startswith("LEAN_PATH="))
            self.assertIn("--root", command)
            elaborated_sources.append(Path(command[-1]).read_text(encoding="utf-8"))
            Path(command[command.index("-o") + 1]).write_bytes(b"fresh olean")
            Path(command[command.index("-i") + 1]).write_bytes(b"fresh ilean")
            return type("Result", (), {"returncode": 0, "stdout": ""})()

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            interface = root / "papers" / "Fixture" / "PaperInterface.lean"
            interface.parent.mkdir(parents=True)
            interface.write_text(source, encoding="utf-8")
            stale = root / ".lake" / "build" / "lib" / "lean" / "Fixture"
            stale.mkdir(parents=True)
            (stale / "PaperInterface.olean").write_bytes(b"stale interface")
            manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()
            try:
                with (
                    mock.patch.object(
                        manifest_module, "_build_import_target", return_value=True
                    ),
                    mock.patch.object(
                        manifest_module.subprocess, "run", side_effect=fake_run
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_constructor_result_type_match_script",
                        return_value={route: True},
                    ) as matcher,
                ):
                    matches = manifest_module.run_lean_constructor_result_type_matches(
                        root,
                        "Fixture.PaperInterface",
                        [route],
                        review_source_path=interface,
                    )
            finally:
                manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()

        self.assertEqual(matches, {route: True})
        self.assertEqual(elaborated_sources, [source])
        matcher.assert_called_once()
        self.assertEqual(
            matcher.call_args.args[1], "import Lean\nimport Fixture.PaperInterface"
        )
        overlay_lean_path = matcher.call_args.kwargs["lean_path"]
        self.assertIn("constructor-result-type-fresh-", overlay_lean_path)
        self.assertIn("/lake-path", overlay_lean_path)
        self.assertNotIn(str(stale), overlay_lean_path)

    def test_constructor_result_type_gate_fails_closed_when_source_changes(
        self,
    ) -> None:
        route = ("Fixture.reviewed", "payload", "Fixture.genericParcel")
        source = """namespace Fixture
structure Parcel (n : Nat) where
  value : Nat
def genericParcel (n : Nat) : Parcel n := ⟨n⟩
axiom reviewed (n : Nat) (payload : Parcel n) : True
end Fixture
"""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            interface = root / "papers" / "Fixture" / "PaperInterface.lean"
            interface.parent.mkdir(parents=True)
            interface.write_text(source, encoding="utf-8")
            stale = root / ".lake" / "build" / "lib" / "lean" / "Fixture"
            stale.mkdir(parents=True)
            (stale / "PaperInterface.olean").write_bytes(b"stale interface")

            def fake_run(command: list[str], **_kwargs: object) -> object:
                if command == ["lake", "env"]:
                    return type(
                        "Result",
                        (),
                        {"returncode": 0, "stdout": "LEAN_PATH=/lake-path\n"},
                    )()
                Path(command[command.index("-o") + 1]).write_bytes(b"fresh olean")
                Path(command[command.index("-i") + 1]).write_bytes(b"fresh ilean")
                interface.write_text(
                    source + "\n-- changed during audit\n", encoding="utf-8"
                )
                return type("Result", (), {"returncode": 0, "stdout": ""})()

            manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()
            try:
                with (
                    mock.patch.object(
                        manifest_module, "_build_import_target", return_value=True
                    ),
                    mock.patch.object(
                        manifest_module.subprocess, "run", side_effect=fake_run
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_constructor_result_type_match_script",
                    ) as matcher,
                ):
                    matches = manifest_module.run_lean_constructor_result_type_matches(
                        root,
                        "Fixture.PaperInterface",
                        [route],
                        review_source_path=interface,
                    )
            finally:
                manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()

        self.assertEqual(matches, {})
        matcher.assert_not_called()

    def test_constructor_result_type_gate_never_falls_back_to_copied_artifact(
        self,
    ) -> None:
        route = ("Fixture.reviewed", "payload", "Fixture.genericParcel")
        source = """namespace Fixture
structure Parcel (n : Nat) where
  value : Nat
def genericParcel (n : Nat) : Parcel n := ⟨n⟩
axiom reviewed (n : Nat) (payload : Parcel n) : True
end Fixture
"""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            interface = root / "papers" / "Fixture" / "PaperInterface.lean"
            interface.parent.mkdir(parents=True)
            interface.write_text(source, encoding="utf-8")
            stale = root / ".lake" / "build" / "lib" / "lean" / "Fixture"
            stale.mkdir(parents=True)
            (stale / "PaperInterface.olean").write_bytes(b"stale interface")

            def fake_run(command: list[str], **_kwargs: object) -> object:
                if command == ["lake", "env"]:
                    return type(
                        "Result",
                        (),
                        {"returncode": 0, "stdout": "LEAN_PATH=/lake-path\n"},
                    )()
                # Deliberately leave no output artifact. A copied stale olean
                # would make this pass if the overlay deletion regressed.
                return type("Result", (), {"returncode": 0, "stdout": ""})()

            manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()
            try:
                with (
                    mock.patch.object(
                        manifest_module, "_build_import_target", return_value=True
                    ),
                    mock.patch.object(
                        manifest_module.subprocess, "run", side_effect=fake_run
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_constructor_result_type_match_script",
                    ) as matcher,
                ):
                    matches = manifest_module.run_lean_constructor_result_type_matches(
                        root,
                        "Fixture.PaperInterface",
                        [route],
                        review_source_path=interface,
                    )
            finally:
                manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()

        self.assertEqual(matches, {})
        matcher.assert_not_called()

    def test_semantic_contracts_are_exact_and_name_independent(self) -> None:
        source = """
def coupledExecutionSpec (machine : Nat → Nat × Nat) : Prop :=
  ∀ input output cost, machine input = (output, cost) → cost ≤ input + 1
theorem disconnectedArithmetic (machine : Nat → Nat × Nat) :
    ∀ input, (machine input).2 ≤ (machine input).2 := by
  intro input
  exact Nat.le_refl _

def initialCommutationSpec (step transform : Nat → Nat) : Prop :=
  ∀ initial, step (transform initial) = step (transform initial)
theorem postStepOnly (step transform : Nat → Nat) :
    ∀ initial, step (transform (step initial)) = step (transform (step initial)) := by
  intro initial
  rfl

def impossiblePoint (value : Nat) : Prop := value ≠ value
theorem exactNegativeEvidence (renamed : Nat) : Not (impossiblePoint renamed) := by
  simp [impossiblePoint]
theorem negativeConjunctOnly (renamed : Nat) :
    Not (impossiblePoint renamed) ∧ True := by
  exact ⟨exactNegativeEvidence renamed, True.intro⟩

def pointwiseSpec (operation : Nat → Nat) : Prop :=
  ∀ element, operation element = operation element
theorem whollyRenamedWitness (unrelated : Nat → Nat) : pointwiseSpec unrelated := by
  intro element
  rfl

def sourceDefinition (value : Nat) : Prop := value = value
def sourceDefinitionSpec (value : Nat) : Prop := value = value
theorem sourceDefinitionRealizes (value : Nat) :
    sourceDefinition value ↔ sourceDefinitionSpec value := by
  rfl
theorem sourceDefinitionWrong (value : Nat) :
    sourceDefinition value ↔ True := by
  simp [sourceDefinition]
"""
        routes = [
            ("coupledExecutionSpec", "disconnectedArithmetic", "proves"),
            ("initialCommutationSpec", "postStepOnly", "proves"),
            ("impossiblePoint", "negativeConjunctOnly", "refutes"),
            ("impossiblePoint", "exactNegativeEvidence", "refutes"),
            ("pointwiseSpec", "whollyRenamedWitness", "proves"),
            ("sourceDefinitionSpec", "sourceDefinitionRealizes", "definitionally_realizes"),
            ("sourceDefinitionSpec", "sourceDefinitionWrong", "definitionally_realizes"),
        ]
        matches = run_lean_semantic_contract_matches_for_source(ROOT, source, routes)
        self.assertEqual(set(matches), set(routes))
        self.assertFalse(matches[routes[0]])
        self.assertFalse(matches[routes[1]])
        self.assertFalse(matches[routes[2]])
        self.assertTrue(matches[routes[3]])
        self.assertTrue(matches[routes[4]])
        self.assertTrue(matches[routes[5]])
        self.assertFalse(matches[routes[6]])

    def test_spec_closure_manifest_is_name_stable_and_keeps_proof_types_and_instance_args(
        self,
    ) -> None:
        source = """
namespace ClosureFixture
def originalWrapper (n : Nat) : Nat := n + 1
def renamedWrapper (value : Nat) : Nat := value + 1
def firstSpec (n : Nat) : Prop := originalWrapper n = n + 1
def secondSpec (value : Nat) : Prop := renamedWrapper value = value + 1
def nestedWrapper (n : Nat) : Nat := originalWrapper n
def boundedSpec (n : Nat) : Prop := nestedWrapper n = n + 1

def choiceSpec {alpha : Type} (witness : Nonempty alpha) : Prop :=
  Classical.choice witness = Classical.choice witness
def instanceSpec {alpha : Type} [Inhabited alpha] : Prop :=
  (default : alpha) = default

structure Model where
  value : Nat
  value_nonnegative : 0 ≤ value
def consumesProof (n : Nat) (_ : 0 ≤ n) : Prop := n = n
def proofProjectionSpec (model : Model) : Prop :=
  consumesProof model.value (Model.value_nonnegative model)
end ClosureFixture
"""
        names = [
            "ClosureFixture.firstSpec",
            "ClosureFixture.secondSpec",
            "ClosureFixture.choiceSpec",
            "ClosureFixture.instanceSpec",
            "ClosureFixture.proofProjectionSpec",
        ]
        manifests = run_lean_semantic_contract_closure_manifests_for_source(
            ROOT, source, names
        )
        self.assertEqual(set(manifests), set(names))
        self.assertTrue(all(manifest["passes"] for manifest in manifests.values()))
        self.assertEqual(
            manifests["ClosureFixture.firstSpec"]["sha256"],
            manifests["ClosureFixture.secondSpec"]["sha256"],
        )
        self.assertEqual(
            manifests["ClosureFixture.firstSpec"]["surface_sha256"],
            manifests["ClosureFixture.secondSpec"]["surface_sha256"],
        )
        foundation_identities = manifests["ClosureFixture.firstSpec"][
            "closure_module_identities"
        ]
        # This inline fixture reaches only the compact Init foundation root.
        # Foundation roots are pinned once by package/toolchain context;
        # exact artifact rows are reserved for paper and unregistered-external
        # modules.
        self.assertEqual(foundation_identities, [])
        self.assertRegex(
            manifests["ClosureFixture.firstSpec"]["closure_foundation_context_sha256"],
            r"^[0-9a-f]{64}$",
        )

        choice = manifests["ClosureFixture.choiceSpec"]
        self.assertEqual(
            choice["surface"]["binder_domains"][1]["domain_is_proposition"], True
        )
        self.assertIn(
            "Classical.choice", [node["declaration"] for node in choice["nodes"]]
        )
        self.assertEqual(
            choice["surface"]["representation"],
            "lean_compact_canonical_surface_sha256_v2",
        )
        self.assertRegex(
            choice["surface"]["body_fingerprint"]["canonical_sha256"],
            r"^[0-9a-f]{64}$",
        )

        instance = manifests["ClosureFixture.instanceSpec"]
        self.assertEqual(
            instance["surface"]["binder_domains"][1]["binder_info"], "instImplicit"
        )

        proof_projection = manifests["ClosureFixture.proofProjectionSpec"]
        self.assertTrue(proof_projection["passes"], proof_projection["failures"])
        self.assertNotIn(
            "theorem_local_dependency",
            [failure["tag"] for failure in proof_projection["failures"]],
        )

        exhausted = run_lean_semantic_contract_closure_manifests_for_source(
            ROOT,
            source,
            ["ClosureFixture.boundedSpec"],
            max_expansions=1,
        )["ClosureFixture.boundedSpec"]
        self.assertFalse(exhausted["passes"])
        self.assertIn(
            "fuel_exhausted", [failure["tag"] for failure in exhausted["failures"]]
        )

    def test_rejected_spec_closure_keeps_terminal_fingerprint_surface(self) -> None:
        source = """
namespace ClosureFixture
opaque hiddenTerm : Nat
def rejectedSpec : Prop := hiddenTerm = hiddenTerm
theorem hiddenWitness : Nonempty Nat := ⟨0⟩
def theoremSelectedSpec : Prop :=
  Classical.choice hiddenWitness = Classical.choice hiddenWitness
axiom hiddenAxiom : Prop
def axiomSelectedSpec : Prop := hiddenAxiom
end ClosureFixture
"""
        manifests = run_lean_semantic_contract_closure_manifests_for_source(
            ROOT,
            source,
            [
                "ClosureFixture.rejectedSpec",
                "ClosureFixture.theoremSelectedSpec",
                "ClosureFixture.axiomSelectedSpec",
            ],
        )
        manifest = manifests["ClosureFixture.rejectedSpec"]
        self.assertFalse(manifest["passes"])
        self.assertEqual(manifest["surface_mode"], "terminal_fingerprints")
        self.assertIsNotNone(manifest["surface"])
        self.assertTrue(manifest["surface_sha256"])
        self.assertIn(
            "opaque_local_dependency",
            [failure["tag"] for failure in manifest["failures"]],
        )
        self.assertIn(
            "ClosureFixture.hiddenTerm",
            [node["declaration"] for node in manifest["nodes"]],
        )
        theorem_selected = manifests["ClosureFixture.theoremSelectedSpec"]
        self.assertTrue(theorem_selected["passes"], theorem_selected["failures"])
        self.assertNotIn(
            "theorem_local_dependency",
            [failure["tag"] for failure in theorem_selected["failures"]],
        )
        self.assertNotIn(
            "ClosureFixture.hiddenWitness",
            [node["declaration"] for node in theorem_selected["nodes"]],
        )
        self.assertEqual(
            theorem_selected["surface"]["representation"],
            "lean_compact_canonical_surface_sha256_v2",
        )
        axiom_selected = manifests["ClosureFixture.axiomSelectedSpec"]
        self.assertFalse(axiom_selected["passes"])
        self.assertIn(
            "axiom_local_dependency",
            [failure["tag"] for failure in axiom_selected["failures"]],
        )

    def test_compact_spec_surface_receipt_is_validated_without_expanded_tree(
        self,
    ) -> None:
        fingerprint = {
            "tag": "expr_fingerprint",
            "canonical_sha256": "a" * 64,
            "canonical_bytes": "33",
        }
        decoded = {
            "schema": "1",
            "spec": "Fixture.SourceSpec",
            "passes": True,
            "expanded": "4",
            "surface_mode": "closure_fingerprints",
            "surface": {
                "tag": "spec_surface_fingerprints",
                "schema": "2",
                "binder_domains": [
                    {
                        "index": "0",
                        "binder_info": "explicit",
                        "domain_is_proposition": False,
                        "fingerprint": fingerprint,
                    }
                ],
                "body_fingerprint": fingerprint,
            },
            "nodes": [],
            "reached_modules": [{"origin_class": "paper", "module_origin": "Fixture"}],
            "failures": [],
            "scope": {
                "paper_modules": ["Fixture"],
                "workspace_modules": ["Fixture"],
                "foundation_modules": ["Init"],
                "foreign_model_definitions": [],
                "foreign_model_modules": [],
                "hash_tool_path": "/usr/bin/sha256sum",
                "inline_paper_scope": False,
            },
        }

        normalized = manifest_module._normalize_semantic_contract_closure(decoded)

        self.assertIsNotNone(normalized)
        assert normalized is not None
        self.assertEqual(normalized["surface_mode"], "closure_fingerprints")
        self.assertEqual(
            normalized["surface"]["representation"],
            "lean_canonical_surface_sha256_v1",
        )
        self.assertNotIn("body", normalized["surface"])

        decoded["surface"]["schema"] = "3"
        compact_normalized = manifest_module._normalize_semantic_contract_closure(
            decoded
        )
        self.assertIsNotNone(compact_normalized)
        assert compact_normalized is not None
        self.assertEqual(
            compact_normalized["surface"]["representation"],
            "lean_compact_canonical_surface_sha256_v2",
        )

        decoded["nodes"] = [
            {
                "structural_path": "statement/foreign_model",
                "node_role": "terminal",
                "origin_class": "foreign_model_definition",
                "module_origin": "Sibling.Model",
                "declaration": "Sibling.Model.definition",
                "canonical_identity": {
                    "tag": "definition",
                    "declaration_kind": "definition",
                    "declaration_type_hash": "1",
                    "declaration_value_hash": "2",
                },
            }
        ]
        decoded["reached_modules"].append(
            {
                "origin_class": "foreign_model_definition",
                "module_origin": "Sibling.Model",
            }
        )
        foreign_normalized = manifest_module._normalize_semantic_contract_closure(
            decoded
        )
        self.assertIsNotNone(foreign_normalized)
        assert foreign_normalized is not None
        self.assertEqual(
            foreign_normalized["nodes"][0]["origin_class"],
            "foreign_model_definition",
        )

    def test_compact_closure_pins_paper_artifacts_not_package_root_pseudo_modules(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            build_root = root / ".lake" / "build" / "lib" / "lean"
            artifact = build_root / "Fixture.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"compiled paper module")
            snapshot = manifest_module._closure_module_identity_snapshot(
                root,
                {
                    "Fixture.SourceSpec": {
                        "surface_mode": "closure_fingerprints",
                        "reached_modules": [
                            {
                                "origin_class": "paper",
                                "module_origin": "Fixture",
                            },
                            {
                                "origin_class": "foundation",
                                "module_origin": "Mathlib",
                            },
                        ],
                    }
                },
                timeout_seconds=5,
                lean_path=str(build_root),
            )

        self.assertEqual(
            [
                identity["module_origin"]
                for identity in snapshot["Fixture.SourceSpec"]
            ],
            ["Fixture"],
        )

    def test_semantic_contract_closure_output_has_structured_hard_cap(self) -> None:
        class FakeProcess:
            returncode = 0
            pid = 999999

            def communicate(self, timeout: int) -> tuple[str, str]:
                del timeout
                return "x" * 129, ""

        stderr = io.StringIO()
        with (
            mock.patch.object(
                manifest_module, "MAX_SEMANTIC_CONTRACT_CLOSURE_OUTPUT_BYTES", 128
            ),
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=FakeProcess()
            ),
            contextlib.redirect_stderr(stderr),
        ):
            result = manifest_module._run_semantic_contract_closure_script(
                ROOT,
                "import Lean",
                ["Fixture.SourceSpec"],
                ("Fixture",),
                ("Fixture",),
                ("Init",),
                inline_paper_scope=False,
                max_expansions=16,
                timeout_seconds=5,
            )

        self.assertEqual(result, {})
        diagnostic = stderr.getvalue()
        self.assertIn(
            manifest_module.SEMANTIC_CONTRACT_CLOSURE_OUTPUT_LIMIT_SENTINEL,
            diagnostic,
        )
        self.assertIn('"max_output_bytes":128', diagnostic)
        self.assertIn('"output_bytes":129', diagnostic)

    def test_semantic_contract_closure_runner_uses_finite_budgets(self) -> None:
        captured: dict[str, object] = {}

        class FakeProcess:
            returncode = 0
            pid = 999999

            def communicate(self, timeout: int) -> tuple[str, str]:
                del timeout
                return "", ""

        def fake_popen(args: list[str], **kwargs: object) -> FakeProcess:
            captured["args"] = args
            captured["path"] = args[-1]
            captured["script"] = Path(args[-1]).read_text(encoding="utf-8")
            captured["kwargs"] = kwargs
            return FakeProcess()

        with (
            mock.patch.object(
                manifest_module.subprocess, "Popen", side_effect=fake_popen
            ),
            contextlib.redirect_stderr(io.StringIO()),
        ):
            result = manifest_module._run_semantic_contract_closure_script(
                ROOT,
                "import Lean",
                ["Fixture.SourceSpec"],
                ("Fixture",),
                ("Fixture",),
                ("Init",),
                inline_paper_scope=False,
                max_expansions=16,
                timeout_seconds=5,
            )

        self.assertEqual(result, {})
        script = str(captured["script"])
        self.assertIn(
            "set_option maxRecDepth "
            + str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_RECURSION_DEPTH),
            script,
        )
        self.assertIn(
            "set_option maxHeartbeats "
            + str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_HEARTBEATS),
            script,
        )
        self.assertNotIn("set_option maxHeartbeats 0", script)
        self.assertNotIn("set_option maxRecDepth 100000", script)
        self.assertEqual(
            captured["args"],
            [
                sys.executable,
                str(manifest_module.CLOSURE_SUBPROCESS_TRAMPOLINE_PATH),
                "--address-space-bytes",
                str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_ADDRESS_SPACE_BYTES),
                "--",
                "lake",
                "env",
                "lean",
                "-M",
                str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_MEMORY_MB),
                "-j",
                str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_THREADS),
                captured["path"],
            ],
        )
        kwargs = captured["kwargs"]
        self.assertIsInstance(kwargs, dict)
        assert isinstance(kwargs, dict)
        self.assertIs(kwargs["stdin"], manifest_module.subprocess.DEVNULL)
        self.assertTrue(kwargs["close_fds"])
        self.assertNotIn("preexec_fn", kwargs)

    def test_semantic_contract_closure_timeout_is_actionable(self) -> None:
        class FakeProcess:
            returncode = -9
            pid = 999999
            calls = 0

            def communicate(self, timeout: int) -> tuple[str, str]:
                self.calls += 1
                if self.calls == 1:
                    raise subprocess.TimeoutExpired("lean", timeout)
                return "", ""

        stderr = io.StringIO()
        with (
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=FakeProcess()
            ),
            mock.patch.object(manifest_module.os, "killpg"),
            contextlib.redirect_stderr(stderr),
        ):
            result = manifest_module._run_semantic_contract_closure_script(
                ROOT,
                "import Lean",
                ["Fixture.first", "Fixture.second"],
                ("Fixture",),
                ("Fixture",),
                ("Init",),
                inline_paper_scope=False,
                max_expansions=16,
                timeout_seconds=5,
            )

        self.assertEqual(result, {})
        diagnostic = stderr.getvalue()
        self.assertIn(
            manifest_module.SEMANTIC_CONTRACT_CLOSURE_RUNNER_FAILURE_SENTINEL,
            diagnostic,
        )
        self.assertIn('"failure_kind":"wall_timeout"', diagnostic)
        self.assertIn('"requested_count":2', diagnostic)
        self.assertIn(
            '"max_heartbeats":'
            + str(manifest_module.SEMANTIC_CONTRACT_CLOSURE_MAX_HEARTBEATS),
            diagnostic,
        )

    def test_semantic_contract_closure_signal_exit_is_actionable(self) -> None:
        class FakeProcess:
            returncode = -9
            pid = 999999

            def communicate(self, timeout: int) -> tuple[str, str]:
                del timeout
                return "", ""

        stderr = io.StringIO()
        with (
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=FakeProcess()
            ),
            contextlib.redirect_stderr(stderr),
        ):
            result = manifest_module._run_semantic_contract_closure_script(
                ROOT,
                "import Lean",
                ["Fixture.SourceSpec"],
                ("Fixture",),
                ("Fixture",),
                ("Init",),
                inline_paper_scope=False,
                max_expansions=16,
                timeout_seconds=5,
            )

        self.assertEqual(result, {})
        diagnostic = stderr.getvalue()
        self.assertIn('"failure_kind":"signal_exit"', diagnostic)
        self.assertIn('"returncode":-9', diagnostic)
        self.assertIn('"signal_number":9', diagnostic)

    def test_semantic_contract_closure_communication_error_is_actionable(self) -> None:
        class FakeProcess:
            returncode = None
            pid = 999999
            killed = False

            def communicate(self, timeout: int) -> tuple[str, str]:
                del timeout
                raise OSError("stream descriptor unavailable")

            def kill(self) -> None:
                self.killed = True

        process = FakeProcess()
        stderr = io.StringIO()
        with (
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=process
            ),
            mock.patch.object(manifest_module.os, "killpg", side_effect=OSError()),
            contextlib.redirect_stderr(stderr),
        ):
            result = manifest_module._run_semantic_contract_closure_script(
                ROOT,
                "import Lean",
                ["Fixture.SourceSpec"],
                ("Fixture",),
                ("Fixture",),
                ("Init",),
                inline_paper_scope=False,
                max_expansions=16,
                timeout_seconds=5,
            )

        self.assertEqual(result, {})
        self.assertTrue(process.killed)
        diagnostic = stderr.getvalue()
        self.assertIn('"failure_kind":"communication_error"', diagnostic)
        self.assertIn("stream descriptor unavailable", diagnostic)

    def test_manifest_script_uses_wall_timeout_not_lean_heartbeats(self) -> None:
        captured: dict[str, str] = {}

        class FakeProcess:
            returncode = 0
            pid = 999999

            def communicate(self, timeout: int) -> tuple[bytes, bytes]:
                del timeout
                return b"", b""

        def fake_popen(args: list[str], **_kwargs: object) -> FakeProcess:
            captured["script"] = Path(args[-1]).read_text(encoding="utf-8")
            return FakeProcess()

        hash_tool = manifest_module._semantic_contract_closure_hash_tool_identity()
        self.assertIsNotNone(hash_tool)
        assert hash_tool is not None
        with mock.patch.object(
            manifest_module.subprocess, "Popen", side_effect=fake_popen
        ):
            result = manifest_module._run_manifest_script(
                ROOT,
                "import Lean",
                ["Fixture.SourceSpec"],
                timeout_seconds=5,
                hash_tool_path=hash_tool["resolved_path"],
            )

        self.assertEqual(result, {})
        self.assertIn("set_option maxRecDepth 100000", captured["script"])
        self.assertIn("set_option maxHeartbeats 0", captured["script"])

    def test_manifest_script_timeout_emits_structured_missing_batch_diagnostic(
        self,
    ) -> None:
        class FakeProcess:
            returncode = -9
            pid = 999999
            calls = 0

            def communicate(self, timeout: int) -> tuple[bytes, bytes]:
                self.calls += 1
                if self.calls == 1:
                    raise subprocess.TimeoutExpired("lean", timeout)
                return b"", b""

        hash_tool = manifest_module._semantic_contract_closure_hash_tool_identity()
        self.assertIsNotNone(hash_tool)
        assert hash_tool is not None
        stderr = io.StringIO()
        names = ["Fixture.first", "Fixture.second"]
        with (
            mock.patch.object(
                manifest_module.subprocess, "Popen", return_value=FakeProcess()
            ),
            mock.patch.object(manifest_module.os, "killpg"),
            contextlib.redirect_stderr(stderr),
        ):
            result = manifest_module._run_manifest_script(
                ROOT,
                "import Lean",
                names,
                timeout_seconds=5,
                hash_tool_path=hash_tool["resolved_path"],
            )

        self.assertEqual(result, {})
        diagnostic = stderr.getvalue()
        self.assertIn(
            manifest_module.LEAN_SIGNATURE_MANIFEST_TIMEOUT_SENTINEL,
            diagnostic,
        )
        self.assertIn('"requested_count":2', diagnostic)
        self.assertIn('"completed_count":0', diagnostic)
        self.assertIn('"missing_count":2', diagnostic)

    def test_closure_cache_rehashes_reached_paper_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            build_root = root / ".lake" / "build" / "lib" / "lean"
            artifact = build_root / "Fixture.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"first compiled artifact")
            specification = "Fixture.Spec"
            raw_manifest = {
                "scope": {
                    "hash_tool_path": "/verified/sha256sum",
                    "foundation_modules": ["Init"],
                    "foreign_model_definitions": [],
                    "foreign_model_modules": [],
                },
                "reached_modules": [
                    {"origin_class": "paper", "module_origin": "Fixture"}
                ],
            }
            extracted = mock.Mock(return_value={specification: raw_manifest})
            manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()
            try:
                with (
                    mock.patch.object(
                        manifest_module,
                        "_semantic_contract_closure_hash_tool_identity",
                        return_value={
                            **self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY,
                            "resolved_path": "/verified/sha256sum",
                        },
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_build_import_target",
                        return_value=True,
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_compiled_audit_helper_available",
                        return_value=True,
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_build_compiled_audit_helper",
                        return_value=True,
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_file_content_fingerprint",
                        return_value=(1, 1),
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_lake_env_lean_path",
                        return_value=str(build_root),
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_semantic_contract_closure_script",
                        extracted,
                    ),
                ):
                    first = run_lean_semantic_contract_closure_manifests(
                        root,
                        "Fixture",
                        [specification],
                        ("Fixture",),
                    )[specification]
                    cached = run_lean_semantic_contract_closure_manifests(
                        root,
                        "Fixture",
                        [specification],
                        ("Fixture",),
                    )[specification]
                    self.assertEqual(extracted.call_count, 1)
                    self.assertEqual(
                        first["closure_module_identities"],
                        cached["closure_module_identities"],
                    )

                    artifact.write_bytes(b"second compiled artifact")
                    refreshed = run_lean_semantic_contract_closure_manifests(
                        root,
                        "Fixture",
                        [specification],
                        ("Fixture",),
                    )[specification]
                    self.assertEqual(extracted.call_count, 2)
                    self.assertNotEqual(
                        first["closure_module_identities"][0]["artifact_sha256"],
                        refreshed["closure_module_identities"][0][
                            "artifact_sha256"
                        ],
                    )
            finally:
                manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()

    def test_unrelated_workspace_artifact_does_not_invalidate_closure_cache(
        self,
    ) -> None:
        specification = "Paper.SourceSpec"
        import_module = "Paper.PaperInterface"
        hash_tool = {
            **self.IMPORT_MANIFEST_HASH_TOOL_IDENTITY,
            "resolved_path": "/verified/sha256sum",
        }
        extractor = {"schema": "fixture", "source_slice_sha256": "b" * 64}
        raw_manifest = {
            "scope": {
                "hash_tool_path": hash_tool["resolved_path"],
                "foundation_modules": ["Init"],
                "foreign_model_definitions": [],
                "foreign_model_modules": [],
            },
            "reached_modules": [
                {
                    "origin_class": "paper",
                    "module_origin": import_module,
                }
            ],
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            build = root / ".lake" / "build" / "lib" / "lean" / "Paper"
            build.mkdir(parents=True)
            (build / "PaperInterface.olean").write_bytes(b"paper interface")
            unrelated = build / "UnrelatedProof.olean"
            unrelated.write_bytes(b"unrelated before")
            manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()
            try:
                with (
                    mock.patch.object(
                        manifest_module, "_build_import_target", return_value=True
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_semantic_contract_closure_hash_tool_identity",
                        return_value=hash_tool,
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_semantic_contract_closure_extractor_identity",
                        return_value=extractor,
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_lean_loaded_module_candidates",
                        return_value=(import_module,),
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_lake_env_lean_path",
                        return_value=str(root / ".lake" / "build" / "lib" / "lean"),
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_semantic_contract_closure_script",
                        return_value={specification: raw_manifest},
                    ) as run_script,
                ):
                    before = run_lean_semantic_contract_closure_manifests(
                        root,
                        import_module,
                        [specification],
                        (import_module,),
                    )
                    unrelated.write_bytes(b"unrelated artifact rebuilt")
                    after = run_lean_semantic_contract_closure_manifests(
                        root,
                        import_module,
                        [specification],
                        (import_module,),
                    )
                self.assertEqual(before, after)
                self.assertEqual(set(after), {specification})
                run_script.assert_called_once()
                self.assertEqual(run_script.call_args.args[4], (import_module,))
            finally:
                manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()

    def test_loaded_workspace_scope_respects_first_lean_path_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            workspace = root / ".lake" / "build" / "lib" / "lean"
            external = root / "external-lean"
            for base, module in (
                (workspace, "Shadowed.Module"),
                (workspace, "Workspace.Only"),
                (external, "Shadowed.Module"),
            ):
                artifact = base / Path(*module.split(".")).with_suffix(".olean")
                artifact.parent.mkdir(parents=True, exist_ok=True)
                artifact.write_bytes(f"{base}:{module}".encode("utf-8"))

            loaded = ("Shadowed.Module", "Workspace.Only")
            external_first = manifest_module._loaded_workspace_module_scope(
                root,
                loaded,
                os.pathsep.join((str(external), str(workspace))),
            )
            workspace_first = manifest_module._loaded_workspace_module_scope(
                root,
                loaded,
                os.pathsep.join((str(workspace), str(external))),
            )

        self.assertIsNotNone(external_first)
        self.assertIsNotNone(workspace_first)
        assert external_first is not None and workspace_first is not None
        self.assertEqual(external_first[0], ("Workspace.Only",))
        self.assertEqual(workspace_first[0], ("Shadowed.Module", "Workspace.Only"))
        self.assertNotEqual(external_first[1], workspace_first[1])

    def test_closure_extraction_rejects_reached_paper_artifact_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            build_root = root / ".lake" / "build" / "lib" / "lean"
            artifact = build_root / "Fixture.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"before extraction")
            specification = "Fixture.Spec"
            raw_manifest = {
                "scope": {
                    "hash_tool_path": "/verified/sha256sum",
                    "foundation_modules": ["Init"],
                    "foreign_model_definitions": [],
                    "foreign_model_modules": [],
                },
                "reached_modules": [
                    {"origin_class": "paper", "module_origin": "Fixture"}
                ],
            }

            def mutate_during_extraction(*args: object, **kwargs: object) -> dict:
                del args, kwargs
                artifact.write_bytes(b"during extraction")
                return {specification: raw_manifest}

            manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()
            try:
                with (
                        mock.patch.object(
                            manifest_module,
                            "_semantic_contract_closure_hash_tool_identity",
                            return_value={"resolved_path": "/verified/sha256sum"},
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_build_import_target",
                            return_value=True,
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_built_olean_fingerprint",
                            return_value=(1, 1),
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_file_content_fingerprint",
                            return_value=(1, 1),
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_paper_module_olean_fingerprints",
                            return_value=(),
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_lake_env_lean_path",
                            return_value=str(build_root),
                        ),
                        mock.patch.object(
                            manifest_module,
                            "_run_semantic_contract_closure_script",
                            side_effect=mutate_during_extraction,
                        ),
                ):
                    result = run_lean_semantic_contract_closure_manifests(
                        root,
                        "Fixture",
                        [specification],
                        ("Fixture",),
                    )
                self.assertEqual(result, {})
                self.assertEqual(
                    manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE,
                    {},
                )
            finally:
                manifest_module._SEMANTIC_CONTRACT_CLOSURE_CACHE.clear()

    def test_spec_closure_blocks_workspace_terminal_and_pins_same_typed_foundations(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            import_graph = (ROOT / ".lake" / "packages" / "importGraph").resolve()
            cli = (ROOT / ".lake" / "packages" / "Cli").resolve()
            self.assertTrue(import_graph.is_dir())
            self.assertTrue(cli.is_dir())
            (root / "scripts").mkdir()
            (root / "scripts" / "lean_import_graph_helper.lean").write_text(
                (ROOT / "scripts" / "lean_import_graph_helper.lean").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            (root / "lean-toolchain").write_text(
                (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            (root / "lakefile.toml").write_text(
                f"""name = \"ClosureFixture\"
version = \"0.1.0\"
defaultTargets = [\"A\"]

[[require]]
name = \"Cli\"
path = {json.dumps(str(cli))}

[[require]]
name = \"importGraph\"
path = {json.dumps(str(import_graph))}

[[lean_lib]]
name = \"A\"

[[lean_lib]]
name = \"B\"
""",
                encoding="utf-8",
            )
            (root / "B.lean").write_text(
                """namespace ExternalFixture
opaque first : Nat
opaque second : Nat
end ExternalFixture
""",
                encoding="utf-8",
            )
            (root / "A.lean").write_text(
                """import B

namespace A
def FirstSpec : Prop := ExternalFixture.first = ExternalFixture.first
def SecondSpec : Prop := ExternalFixture.second = ExternalFixture.second
def firstRenamedHelper (n : Nat) : Nat := n + 1
def FirstRenamedSpec (n : Nat) : Prop := firstRenamedHelper n = n + 1
def secondRenamedHelper (n : Nat) : Nat := n + 1
def SecondRenamedSpec (n : Nat) : Prop := secondRenamedHelper n = n + 1
def changedHelper (n : Nat) : Nat := n + 2
def ChangedSpec (n : Nat) : Prop := changedHelper n = n + 1
end A
""",
                encoding="utf-8",
            )
            build = subprocess.run(
                ["lake", "build", "ImportGraph.Imports.RequiredModules", "A"],
                cwd=root,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=120,
                check=False,
            )
            self.assertEqual(build.returncode, 0, build.stdout)

            renamed = run_lean_semantic_contract_closure_manifests(
                root,
                "A",
                [
                    "A.FirstRenamedSpec",
                    "A.SecondRenamedSpec",
                    "A.ChangedSpec",
                    "A.FirstSpec",
                ],
                ("A",),
                timeout_seconds=120,
                build_timeout_seconds=120,
            )
            self.assertEqual(
                set(renamed),
                {
                    "A.FirstRenamedSpec",
                    "A.SecondRenamedSpec",
                    "A.ChangedSpec",
                    "A.FirstSpec",
                },
            )
            first_renamed = renamed["A.FirstRenamedSpec"]
            second_renamed = renamed["A.SecondRenamedSpec"]
            self.assertTrue(first_renamed["passes"], first_renamed["failures"])
            self.assertTrue(second_renamed["passes"], second_renamed["failures"])
            self.assertEqual(
                first_renamed["surface_mode"], "closure_fingerprints"
            )
            self.assertIn("body_fingerprint", first_renamed["surface"])
            self.assertNotEqual(
                first_renamed["surface_sha256"],
                renamed["A.ChangedSpec"]["surface_sha256"],
            )
            self.assertNotIn("expr_hash", json.dumps(first_renamed["surface"]))
            self.assertEqual(
                first_renamed["closure_hash_tool_identity"]["known_vector_sha256"],
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            )
            self.assertEqual(
                first_renamed["closure_extractor_identity"][
                    "canonical_surface_representation"
                ],
                "lean_compact_canonical_surface_sha256_v2",
            )

            blocked_manifest = renamed["A.FirstSpec"]
            self.assertFalse(blocked_manifest["passes"])
            workspace_nodes = [
                node
                for node in blocked_manifest["nodes"]
                if node["origin_class"] == "workspace"
            ]
            self.assertTrue(workspace_nodes)
            self.assertEqual(workspace_nodes[0]["module_origin"], "B")
            self.assertIn(
                "unregistered_workspace_dependency",
                [failure["tag"] for failure in blocked_manifest["failures"]],
            )
            self.assertRegex(
                blocked_manifest["closure_module_context_sha256"], r"^[0-9a-f]{64}$"
            )

    def test_compact_closure_hashes_shared_declaration_dag_once(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            import_graph = (ROOT / ".lake" / "packages" / "importGraph").resolve()
            cli = (ROOT / ".lake" / "packages" / "Cli").resolve()
            (root / "scripts").mkdir()
            (root / "scripts" / "lean_import_graph_helper.lean").write_text(
                (ROOT / "scripts" / "lean_import_graph_helper.lean").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            (root / "lean-toolchain").write_text(
                (ROOT / "lean-toolchain").read_text(encoding="utf-8"),
                encoding="utf-8",
            )
            (root / "lakefile.toml").write_text(
                f"""name = \"SharedClosureFixture\"
version = \"0.1.0\"
defaultTargets = [\"A\"]

[[require]]
name = \"Cli\"
path = {json.dumps(str(cli))}

[[require]]
name = \"importGraph\"
path = {json.dumps(str(import_graph))}

[[lean_lib]]
name = \"A\"
""",
                encoding="utf-8",
            )
            declarations = ["namespace A", "def layer0 : Prop := True"]
            declarations.extend(
                f"def layer{index} : Prop := layer{index - 1} ∧ layer{index - 1}"
                for index in range(1, 29)
            )
            declarations.extend(["def SharedDagSpec : Prop := layer28", "end A", ""])
            (root / "A.lean").write_text("\n".join(declarations), encoding="utf-8")
            build = subprocess.run(
                ["lake", "build", "ImportGraph.Imports.RequiredModules", "A"],
                cwd=root,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                timeout=120,
                check=False,
            )
            self.assertEqual(build.returncode, 0, build.stdout)

            manifest = run_lean_semantic_contract_closure_manifests(
                root,
                "A",
                ["A.SharedDagSpec"],
                ("A",),
                max_expansions=64,
                timeout_seconds=60,
                build_timeout_seconds=120,
            )["A.SharedDagSpec"]
            self.assertTrue(manifest["passes"], manifest["failures"])
            self.assertEqual(
                manifest["surface"]["representation"],
                "lean_compact_canonical_surface_sha256_v2",
            )
            self.assertLess(
                int(manifest["surface"]["body_fingerprint"]["canonical_bytes"]),
                1024,
            )
            self.assertLessEqual(manifest["expanded"], 32)

    def test_import_semantic_contracts_use_bounded_route_chunks(self) -> None:
        routes = [
            (
                f"ChunkedSemantic.spec{index:02}",
                f"ChunkedSemantic.evidence{index:02}",
                "proves",
            )
            for index in range(50)
        ]
        chunks = manifest_module._semantic_contract_match_batches(routes)
        expected = {route: index % 2 == 0 for index, route in enumerate(routes)}
        chunk_results = [
            {
                **{route: expected[route] for route in chunk},
                **(
                    {("Unexpected.spec", "Unexpected.evidence", "proves"): True}
                    if index == 0
                    else {}
                ),
            }
            for index, chunk in enumerate(chunks)
        ]
        manifest_module._SEMANTIC_CONTRACT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module, "_build_import_target", return_value=True
                ),
                mock.patch.object(
                    manifest_module, "_built_olean_fingerprint", return_value=(1, 2)
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_semantic_contract_script",
                    side_effect=chunk_results,
                ) as run_script,
            ):
                result = manifest_module.run_lean_semantic_contract_matches(
                    ROOT, "ChunkedSemantic.Module", routes, timeout_seconds=91
                )
        finally:
            manifest_module._SEMANTIC_CONTRACT_CACHE.clear()
        self.assertEqual(result, expected)
        self.assertEqual([call.args[2] for call in run_script.call_args_list], chunks)
        self.assertEqual(
            [call.args[3] for call in run_script.call_args_list],
            [91] * len(chunks),
        )
        self.assertLessEqual(
            len(chunks), manifest_module.MAX_SEMANTIC_CONTRACT_MATCH_CHUNKS
        )

    def test_semantic_contract_batches_start_at_their_stated_capacity(self) -> None:
        """An ordinary ten-row paper shares one bounded Lean import."""

        transparency_names = [f"Paper.spec{index}" for index in range(10)]
        closure_names = [f"Paper.spec{index}" for index in range(10)]
        routes = [
            (f"Paper.spec{index}", f"Paper.proof{index}", "proves")
            for index in range(10)
        ]

        self.assertEqual(
            manifest_module._semantic_contract_transparency_batches(transparency_names),
            [
                transparency_names[:2],
                transparency_names[2:4],
                transparency_names[4:6],
                transparency_names[6:8],
                transparency_names[8:],
            ],
        )
        self.assertEqual(
            manifest_module._semantic_contract_closure_batches(closure_names),
            [
                closure_names[:2],
                closure_names[2:4],
                closure_names[4:6],
                closure_names[6:8],
                closure_names[8:],
            ],
        )
        self.assertEqual(
            manifest_module._semantic_contract_match_batches(routes),
            [routes],
        )

    def test_import_semantic_contracts_retry_only_missing_routes(self) -> None:
        routes = [
            (
                f"ResidualSemantic.spec{index:02}",
                f"ResidualSemantic.evidence{index:02}",
                "proves",
            )
            for index in range(
                manifest_module.MIN_CHUNKED_SEMANTIC_CONTRACT_MATCH_ROUTES
            )
        ]
        chunks = [
            routes[index : index + manifest_module.SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE]
            for index in range(
                0, len(routes), manifest_module.SEMANTIC_CONTRACT_MATCH_CHUNK_SIZE
            )
        ]
        self.assertEqual(len(chunks), 2)
        expected = {route: index % 2 == 0 for index, route in enumerate(routes)}
        missing_chunk = chunks[1]
        initial_results = [
            {route: expected[route] for route in chunks[0]},
            {},
        ]
        retry_results = [{route: expected[route]} for route in missing_chunk]
        manifest_module._SEMANTIC_CONTRACT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module, "_build_import_target", return_value=True
                ),
                mock.patch.object(
                    manifest_module, "_built_olean_fingerprint", return_value=(1, 2)
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_semantic_contract_script",
                    side_effect=[*initial_results, *retry_results],
                ) as run_script,
            ):
                result = manifest_module.run_lean_semantic_contract_matches(
                    ROOT, "ResidualSemantic.Module", routes, timeout_seconds=91
                )
        finally:
            manifest_module._SEMANTIC_CONTRACT_CACHE.clear()
        self.assertEqual(result, expected)
        self.assertIn(False, result.values())
        self.assertEqual(
            [call.args[2] for call in run_script.call_args_list],
            [chunks[0], chunks[1], *[[route] for route in missing_chunk]],
        )
        self.assertEqual(
            [call.args[3] for call in run_script.call_args_list],
            [91] * (len(chunks) + len(missing_chunk)),
        )

    def test_semantic_contract_retries_bisect_before_singletons(self) -> None:
        routes = [
            (f"Adaptive.spec{index}", f"Adaptive.proof{index}", "proves")
            for index in range(7)
        ]
        calls: list[list[tuple[str, str, str]]] = []

        def run_batch(
            batch: list[tuple[str, str, str]],
        ) -> dict[tuple[str, str, str], bool]:
            calls.append(batch)
            return {batch[0]: True} if len(batch) == 1 else {}

        recovered = manifest_module._semantic_contract_adaptive_retries(
            routes, run_batch
        )

        self.assertEqual(recovered, {route: True for route in routes})
        self.assertEqual(calls[0], routes[:3])
        self.assertIn(routes[3:], calls)
        self.assertLess(len(calls), 2 * len(routes))

    def test_source_premise_false_eliminator_uses_elaborated_input_shape(self) -> None:
        source = """
structure OriginalSourceModel (alpha : Type) where
  observed : alpha

abbrev CompletelyRenamedWrapper (beta : Type) := OriginalSourceModel beta

axiom directEliminator {alpha : Type} (model : OriginalSourceModel alpha) : False
axiom throughTransparentAlias {beta : Type} (input : CompletelyRenamedWrapper beta) : False
axiom unrelatedFalse (count : Nat) : False
axiom proofPremiseRequired {alpha : Type}
    (model : OriginalSourceModel alpha) (extra : True) : False
axiom candidateDataParameter {alpha : Type} (count : Nat)
    (model : OriginalSourceModel alpha) : False
"""
        matches = run_lean_source_premise_false_eliminators_for_source(
            ROOT, source, ["OriginalSourceModel"]
        )
        self.assertEqual(set(matches), {"OriginalSourceModel"})
        routes = {item["candidate"]: item for item in matches["OriginalSourceModel"]}
        self.assertEqual(
            set(routes),
            {
                "directEliminator",
                "throughTransparentAlias",
                "candidateDataParameter",
            },
        )
        self.assertTrue(routes["directEliminator"]["direct_eliminator"])
        self.assertTrue(routes["throughTransparentAlias"]["direct_eliminator"])
        self.assertFalse(routes["candidateDataParameter"]["direct_eliminator"])
        self.assertEqual(
            routes["candidateDataParameter"]["candidate_only_data_binder_indices"],
            ["1"],
        )

    def test_recursive_definition_self_name_is_not_hashed(self) -> None:
        source = """
def firstCountdown : Nat → Nat
  | 0 => 0
  | n + 1 => firstCountdown n
def renamedCountdown : Nat → Nat
  | 0 => 0
  | k + 1 => renamedCountdown k
"""
        manifests = self.manifests(source, ["firstCountdown", "renamedCountdown"])
        self.assertEqual(
            manifests["firstCountdown"]["sha256"],
            manifests["renamedCountdown"]["sha256"],
        )

    def test_generated_proof_helper_in_definition_is_manifested(self) -> None:
        source = """
def fairnessObjective (n : Nat) : Nat :=
  have h : n = n := rfl
  n
"""
        manifests = self.manifests(source, ["fairnessObjective"])
        self.assertTrue(manifests["fairnessObjective"]["sha256"])

    def test_local_definition_closure_is_name_independent_and_transitive(self) -> None:
        source = """
namespace FirstPaper
def sourceFormula (x : Nat) : Nat := x + 1
def wrapper (x : Nat) : Nat := sourceFormula x
end FirstPaper
namespace RenamedPaper
def unrelatedHelperName (value : Nat) : Nat := value + 1
def unrelatedWrapperName (value : Nat) : Nat := unrelatedHelperName value
end RenamedPaper
namespace ChangedPaper
def sourceFormula (x : Nat) : Nat := x + 2
def wrapper (x : Nat) : Nat := sourceFormula x
end ChangedPaper
"""
        names = [
            "FirstPaper.wrapper",
            "RenamedPaper.unrelatedWrapperName",
            "ChangedPaper.wrapper",
        ]
        manifests = self.manifests(source, names)
        self.assertEqual(
            manifests["FirstPaper.wrapper"]["sha256"],
            manifests["RenamedPaper.unrelatedWrapperName"]["sha256"],
        )
        self.assertNotEqual(
            manifests["FirstPaper.wrapper"]["sha256"],
            manifests["ChangedPaper.wrapper"]["sha256"],
        )

    def test_top_level_dependency_body_drift_changes_wrapper_digest(self) -> None:
        before = self.manifests(
            "def helper (x : Nat) := x + 1\ndef wrapper (x : Nat) := helper x\n",
            ["wrapper"],
        )
        after = self.manifests(
            "def helper (x : Nat) := x + 2\ndef wrapper (x : Nat) := helper x\n",
            ["wrapper"],
        )
        self.assertNotEqual(before["wrapper"]["sha256"], after["wrapper"]["sha256"])

    def test_eta_short_abbrev_alias_has_definition_manifest(self) -> None:
        source = """
universe u
theorem target {alpha : Type u} (x : alpha) (h : x = x) : x = x := h
abbrev compactAlias := @target
abbrev etaLongAlias {beta : Type u} (y : beta) (proof : y = y) : y = y :=
  target y proof
"""
        manifests = self.manifests(source, ["compactAlias", "etaLongAlias"])
        self.assertEqual(
            manifests["compactAlias"]["sha256"],
            manifests["etaLongAlias"]["sha256"],
        )
        self.assertEqual(
            [atom["role"] for atom in manifests["compactAlias"]["atoms"]],
            ["parameter", "parameter", "assumption", "conclusion"],
        )
        self.assertEqual(manifests["compactAlias"]["declaration_kind"], "definition")

    def test_reducible_function_result_does_not_add_outer_binder_atoms(self) -> None:
        source = """
universe u
abbrev ArbitraryOutputAlias (Carrier : Type u) := Carrier → Nat
def unrelatedBuilder {Carrier : Type u} (fallback : Nat) :
    ArbitraryOutputAlias Carrier :=
  fun _ => fallback
"""
        manifest = self.manifests(source, ["unrelatedBuilder"])["unrelatedBuilder"]
        self.assertEqual(
            [atom["role"] for atom in manifest["atoms"]],
            ["parameter", "parameter", "conclusion"],
        )
        self.assertEqual(manifest["atoms"][0]["display"], "Type u")
        self.assertEqual(manifest["atoms"][1]["display"], "Nat")

    def test_explicit_forall_result_preserves_its_binder_atom(self) -> None:
        source = """
def arbitraryExplicitForall (seed : Nat) : ∀ index : Nat, index = index :=
  fun index => rfl
"""
        manifest = self.manifests(source, ["arbitraryExplicitForall"])[
            "arbitraryExplicitForall"
        ]
        self.assertEqual(
            [atom["role"] for atom in manifest["atoms"]],
            ["parameter", "parameter", "conclusion"],
        )
        self.assertEqual(
            [atom["display"] for atom in manifest["atoms"][:-1]],
            ["Nat", "Nat"],
        )

    def test_theorem_proof_wrapper_expands_spec_quantifier_atoms(self) -> None:
        source = """
def unrelatedClosedSpec : Prop := ∀ witness : Nat, witness = witness
theorem arbitraryProofWrapper : unrelatedClosedSpec :=
  fun witness => rfl
"""
        manifest = self.manifests(source, ["arbitraryProofWrapper"])[
            "arbitraryProofWrapper"
        ]
        self.assertEqual(
            [atom["role"] for atom in manifest["atoms"]],
            ["parameter", "conclusion"],
        )
        self.assertEqual(manifest["atoms"][0]["display"], "Nat")

    def test_sibling_namespace_dependency_body_drift_changes_wrapper_digest(
        self,
    ) -> None:
        before_source = """
namespace Paper.Main
def sourceFormula (x : Nat) := x + 1
end Paper.Main
namespace Paper.Interface
def wrapper (x : Nat) := Paper.Main.sourceFormula x
end Paper.Interface
"""
        after_source = before_source.replace("x + 1", "x + 2")
        before = self.manifests(before_source, ["Paper.Interface.wrapper"])
        after = self.manifests(after_source, ["Paper.Interface.wrapper"])
        self.assertNotEqual(
            before["Paper.Interface.wrapper"]["sha256"],
            after["Paper.Interface.wrapper"]["sha256"],
        )

    def test_local_structure_is_represented_and_local_axiom_fails_per_row(self) -> None:
        source = """
namespace LocalModel
structure S where
  x : Nat
def read (s : S) : Nat := s.x
axiom A : Prop
axiom row (h : A) : A
end LocalModel
"""
        manifests = run_lean_signature_manifests_for_source(
            ROOT, source, ["LocalModel.read", "LocalModel.row"]
        )
        self.assertEqual(set(manifests), {"LocalModel.read"})
        self.assertTrue(manifests["LocalModel.read"]["sha256"])

    def test_imported_repository_dependency_closure_is_compact(self) -> None:
        names = [
            "AppliedModelingLib.Matching.CompleteLatticeOn.exists_lub",
            "AppliedModelingLib.Matching.CompleteLatticeOn.exists_glb",
        ]
        manifests = manifest_module.run_lean_signature_manifests(
            ROOT, "AppliedModelingLib.Markets.Matching.ContinuumCutoff", names
        )
        self.assertEqual(set(manifests), set(names))
        for manifest in manifests.values():
            encoded = json.dumps(manifest, sort_keys=True).encode("utf-8")
            self.assertLess(len(encoded), 100_000)
            self.assertIn('"sha256"', encoded.decode("utf-8"))

    def test_helper_failure_returns_no_manifest(self) -> None:
        self.assertEqual(
            run_lean_signature_manifests_for_source(
                ROOT, "axiom existing : True\n", ["missingDeclaration"]
            ),
            {},
        )

    def test_import_build_failure_fails_closed_before_manifest_run(self) -> None:
        with (
            mock.patch.object(
                manifest_module, "_build_import_target", return_value=False
            ),
            mock.patch.object(manifest_module, "_run_manifest_script") as run_script,
        ):
            result = manifest_module.run_lean_signature_manifests(
                ROOT, "FreshCheckout.MissingModule", ["FreshCheckout.row"]
            )
        self.assertEqual(result, {})
        run_script.assert_not_called()

    def test_audit_scope_is_the_exact_review_module_not_its_namespace(self) -> None:
        modules = (
            "KR21Monoculture.MainTheorems",
            "KR21Monoculture.PaperInterface",
            "KR21Monoculture.UnrelatedExperimentalProof",
            "Shared.Dependency",
        )
        scope = manifest_module._audit_module_scope(
            "KR21Monoculture.PaperInterface", modules
        )
        self.assertEqual(scope, ("KR21Monoculture.PaperInterface",))
        self.assertEqual(
            scope,
            manifest_module._audit_module_scope(
                "KR21Monoculture.PaperInterface", tuple(reversed(modules))
            ),
        )

    def test_recursive_field_safety_large_surface_uses_bounded_batches(self) -> None:
        def locator(index: int) -> dict[str, object]:
            value: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": f"LargeSlots.Model.field{index}",
                "field_index": 0,
            }
            value["field_identity_sha256"] = recursive_field_safety_locator_identity(
                value
            )
            return value

        locators = [locator(index) for index in range(49)]
        ordered_locators = sorted(
            locators, key=lambda item: str(item["field_identity_sha256"])
        )
        batches = manifest_module._recursive_field_safety_batches(ordered_locators)
        expected = {
            str(item["field_identity_sha256"]): {"status": "ok"} for item in locators
        }
        manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module, "_built_olean_fingerprint", return_value=(1, 2)
                ),
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_recursive_field_proposition_sort_script",
                    side_effect=[
                        {
                            str(item["field_identity_sha256"]): expected[
                                str(item["field_identity_sha256"])
                            ]
                            for item in batch
                        }
                        for batch in batches
                    ],
                ) as run_script,
            ):
                result = manifest_module.run_lean_recursive_field_proposition_sorts(
                    ROOT, "LargeSlots.Module", locators
                )
            self.assertEqual(result, expected)
            self.assertEqual(
                [call.args[2] for call in run_script.call_args_list], batches
            )
            self.assertEqual(
                [call.args[3] for call in run_script.call_args_list],
                [manifest_module.MAX_CHUNKED_RECURSIVE_FIELD_SAFETY_TIMEOUT_SECONDS]
                * len(batches),
            )
        finally:
            manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()

    def test_recursive_field_safety_bisects_only_missing_slots(self) -> None:
        def locator(index: int) -> dict[str, object]:
            value: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": f"MissingSlots.Model.field{index}",
                "field_index": 0,
            }
            value["field_identity_sha256"] = recursive_field_safety_locator_identity(
                value
            )
            return value

        locators = [locator(index) for index in range(25)]
        ordered = sorted(locators, key=lambda item: str(item["field_identity_sha256"]))
        initial, final = manifest_module._recursive_field_safety_batches(ordered)
        expected = {
            str(item["field_identity_sha256"]): {"status": "ok"} for item in locators
        }

        def run_script(_root, _source, batch, _timeout):
            if batch == initial:
                return {}
            return {
                str(item["field_identity_sha256"]): expected[
                    str(item["field_identity_sha256"])
                ]
                for item in batch
            }

        manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_recursive_field_proposition_sort_script",
                    side_effect=run_script,
                ) as run_script_mock,
            ):
                result = manifest_module.run_lean_recursive_field_proposition_sorts(
                    ROOT, "MissingSlots.Module", locators
                )
            self.assertEqual(result, expected)
            self.assertEqual(
                [call.args[2] for call in run_script_mock.call_args_list],
                [initial, initial[:12], initial[12:], final],
            )
        finally:
            manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()

    def test_recursive_field_safety_small_batch_isolates_one_bad_locator(self) -> None:
        """One invalid slot cannot erase every valid receipt in a small batch."""

        def locator(index: int) -> dict[str, object]:
            value: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": f"SmallSlots.Model.field{index}",
                "field_index": 0,
            }
            value["field_identity_sha256"] = recursive_field_safety_locator_identity(
                value
            )
            return value

        locators = [locator(index) for index in range(3)]
        bad_identity = str(locators[1]["field_identity_sha256"])

        def run_script(_root, _source, batch, _timeout):
            identities = {str(item["field_identity_sha256"]) for item in batch}
            if bad_identity in identities:
                return {}
            return {identity: {"status": "ok"} for identity in identities}

        manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_recursive_field_proposition_sort_script",
                    side_effect=run_script,
                ) as run_script_mock,
            ):
                result = manifest_module.run_lean_recursive_field_proposition_sorts(
                    ROOT, "SmallSlots.Module", locators
                )
            self.assertEqual(
                set(result),
                {
                    str(locators[0]["field_identity_sha256"]),
                    str(locators[2]["field_identity_sha256"]),
                },
            )
            self.assertGreater(run_script_mock.call_count, 1)
        finally:
            manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()

    def test_type_witness_safety_bisects_and_preserves_independent_receipts(
        self,
    ) -> None:
        """An exact singleton failure must not erase adjacent result receipts."""

        names = [
            "Fixture.result0",
            "Fixture.result1",
            "Fixture.result2",
            "Fixture.result3",
        ]
        failed_name = names[2]
        expected = {
            name: [{"path": f"result/{index}", "status": "ok"}]
            for index, name in enumerate(names)
            if name != failed_name
        }

        def run_script(_root, _source, batch, _timeout):
            if failed_name in batch:
                return {}
            return {name: expected[name] for name in batch}

        manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_type_witness_payload_safety_script",
                    side_effect=run_script,
                ) as run_script_mock,
            ):
                result = run_lean_type_witness_payload_safeties(
                    ROOT,
                    "Fixture.PaperInterface",
                    names,
                )
            self.assertEqual(result, expected)
            self.assertEqual(
                [call.args[2] for call in run_script_mock.call_args_list],
                [
                    names,
                    names[:2],
                    names[2:],
                    [names[2]],
                    [names[3]],
                ],
            )
            self.assertNotIn(failed_name, result)
        finally:
            manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()

    def test_type_witness_safety_medium_surface_uses_bounded_batches(self) -> None:
        """A paper-sized result surface avoids one all-or-nothing helper call."""

        names = [f"Fixture.result{index:02}" for index in range(27)]
        batches = manifest_module._type_witness_payload_safety_batches(names)
        expected = {name: [] for name in names}
        manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_type_witness_payload_safety_script",
                    side_effect=[{name: [] for name in batch} for batch in batches],
                ) as run_script,
            ):
                result = run_lean_type_witness_payload_safeties(
                    ROOT,
                    "Fixture.PaperInterface",
                    names,
                )
            self.assertEqual(result, expected)
            self.assertEqual(
                [call.args[2] for call in run_script.call_args_list], batches
            )
            self.assertEqual(
                [call.args[3] for call in run_script.call_args_list],
                [
                    manifest_module.MAX_CHUNKED_TYPE_WITNESS_PAYLOAD_SAFETY_TIMEOUT_SECONDS
                ]
                * len(batches),
            )
            self.assertTrue(
                all(
                    len(batch) <= manifest_module.TYPE_WITNESS_PAYLOAD_SAFETY_CHUNK_SIZE
                    for batch in batches
                )
            )
        finally:
            manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()

    def test_recursive_field_safety_overlapping_request_runs_only_missing_locator(
        self,
    ) -> None:
        def locator(index: int) -> dict[str, object]:
            value: dict[str, object] = {
                "schema": 1,
                "kind": "projection",
                "declaration": f"Overlap.Model.field{index}",
                "field_index": 0,
            }
            value["field_identity_sha256"] = recursive_field_safety_locator_identity(
                value
            )
            return value

        locators = [locator(index) for index in range(3)]

        def run_script(_root, _source, batch, _timeout):
            return {
                str(item["field_identity_sha256"]): {
                    "status": "ok",
                    "marker": item["declaration"],
                }
                for item in batch
            }

        diagnostics: dict[str, object] = {}
        manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_recursive_field_proposition_sort_script",
                    side_effect=run_script,
                ) as run_script_mock,
            ):
                first = run_lean_recursive_field_proposition_sorts(
                    ROOT, "Overlap.Module", locators[:2]
                )
                second = run_lean_recursive_field_proposition_sorts(
                    ROOT,
                    "Overlap.Module",
                    locators[1:],
                    diagnostics_out=diagnostics,
                )

            first_batch = sorted(
                locators[:2],
                key=lambda item: str(item["field_identity_sha256"]),
            )
            self.assertEqual(
                [call.args[2] for call in run_script_mock.call_args_list],
                [first_batch, [locators[2]]],
            )
            self.assertEqual(len(first), 2)
            self.assertEqual(len(second), 2)
            self.assertEqual(diagnostics["requested_count"], 2)
            self.assertEqual(diagnostics["reused_count"], 1)
            self.assertEqual(diagnostics["fresh_count"], 1)
        finally:
            manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()

    def test_slot_count_overlapping_request_runs_only_missing_constructor(
        self,
    ) -> None:
        constructors = ["Overlap.CtorA", "Overlap.CtorB", "Overlap.CtorC"]
        inductives = ["Overlap.IndA", "Overlap.IndB", "Overlap.IndC"]
        manifest_module._CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()
        manifest_module._INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_constructor_field_slot_count_script",
                    side_effect=lambda _root, _source, names, _timeout: {
                        name: index + 1 for index, name in enumerate(names)
                    },
                ) as constructor_script,
                mock.patch.object(
                    manifest_module,
                    "_run_inductive_constructor_field_slot_count_script",
                    side_effect=lambda _root, _source, names, _timeout: {
                        name: {f"{name}.mk": 1} for name in names
                    },
                ) as inductive_script,
            ):
                manifest_module.run_lean_constructor_field_slot_counts(
                    ROOT, "Overlap.Module", constructors[:2]
                )
                constructor_result = (
                    manifest_module.run_lean_constructor_field_slot_counts(
                        ROOT, "Overlap.Module", constructors[1:]
                    )
                )
                manifest_module.run_lean_inductive_constructor_field_slot_counts(
                    ROOT, "Overlap.Module", inductives[:2]
                )
                inductive_result = (
                    manifest_module.run_lean_inductive_constructor_field_slot_counts(
                        ROOT, "Overlap.Module", inductives[1:]
                    )
                )

            self.assertEqual(
                [call.args[2] for call in constructor_script.call_args_list],
                [constructors[:2], [constructors[2]]],
            )
            self.assertEqual(
                [call.args[2] for call in inductive_script.call_args_list],
                [inductives[:2], [inductives[2]]],
            )
            self.assertEqual(set(constructor_result), set(constructors[1:]))
            self.assertEqual(set(inductive_result), set(inductives[1:]))
        finally:
            manifest_module._CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()
            manifest_module._INDUCTIVE_CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()

    def test_type_witness_overlapping_request_reuses_explicit_empty_receipt(
        self,
    ) -> None:
        names = ["Overlap.resultA", "Overlap.resultB", "Overlap.resultC"]
        diagnostics: dict[str, object] = {}
        manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_type_witness_payload_safety_script",
                    side_effect=lambda _root, _source, batch, _timeout: {
                        name: [] for name in batch
                    },
                ) as run_script,
            ):
                run_lean_type_witness_payload_safeties(
                    ROOT, "Overlap.Module", names[:2]
                )
                result = run_lean_type_witness_payload_safeties(
                    ROOT,
                    "Overlap.Module",
                    [names[0], names[2]],
                    diagnostics_out=diagnostics,
                )

            self.assertEqual(
                [call.args[2] for call in run_script.call_args_list],
                [names[:2], [names[2]]],
            )
            self.assertEqual(result, {names[0]: [], names[2]: []})
            self.assertEqual(diagnostics["reused_count"], 1)
            self.assertEqual(diagnostics["fresh_count"], 1)
        finally:
            manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()

    def test_constructor_result_false_verdict_is_cached_but_missing_verdict_is_not(
        self,
    ) -> None:
        false_route = ("Fixture.reviewed", "payload", "Fixture.incompatible")
        missing_route = ("Fixture.reviewed", "payload", "Fixture.unavailable")
        manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            source_path = root / "Fixture" / "PaperInterface.lean"
            source_path.parent.mkdir(parents=True)
            source_path.write_text("theorem placeholder : True := trivial\n")
            source_sha256 = hashlib.sha256(source_path.read_bytes()).hexdigest()

            def run_script(_root, _source, routes, _timeout, *, lean_path):
                del lean_path
                if false_route in routes:
                    return {false_route: False}
                return {missing_route: True}

            try:
                with (
                    mock.patch.object(
                        manifest_module,
                        "_structural_scan_environment_identity",
                        return_value="environment",
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_fresh_constructor_result_type_overlay",
                        side_effect=lambda *_args, **_kwargs: contextlib.nullcontext(
                            ("overlay", source_sha256)
                        ),
                    ),
                    mock.patch.object(
                        manifest_module,
                        "_run_constructor_result_type_match_script",
                        side_effect=run_script,
                    ) as matcher,
                ):
                    first = manifest_module.run_lean_constructor_result_type_matches(
                        root,
                        "Fixture.PaperInterface",
                        [false_route, missing_route],
                        review_source_path=source_path,
                    )
                    second = manifest_module.run_lean_constructor_result_type_matches(
                        root,
                        "Fixture.PaperInterface",
                        [false_route, missing_route],
                        review_source_path=source_path,
                    )

                self.assertEqual(first, {false_route: False})
                self.assertEqual(second, {false_route: False, missing_route: True})
                self.assertEqual(
                    [call.args[2] for call in matcher.call_args_list],
                    [[false_route, missing_route], [missing_route]],
                )
            finally:
                manifest_module._CONSTRUCTOR_RESULT_TYPE_MATCH_CACHE.clear()

    def test_source_premise_empty_candidate_list_is_cached_but_missing_target_is_not(
        self,
    ) -> None:
        clean = "Fixture.CleanModel"
        missing = "Fixture.UnavailableModel"
        calls = 0

        def run_script(_root, _source, names, _modules, _timeout):
            nonlocal calls
            calls += 1
            if calls == 1:
                return {clean: []}
            return {
                missing: [
                    {
                        "candidate": "Fixture.falseOfUnavailable",
                        "direct_eliminator": True,
                    }
                ]
            }

        manifest_module._SOURCE_PREMISE_FALSE_SCAN_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_source_premise_false_scan_script",
                    side_effect=run_script,
                ) as scan,
            ):
                first = manifest_module.run_lean_source_premise_false_eliminators(
                    ROOT, "Fixture.Module", [clean, missing]
                )
                second = manifest_module.run_lean_source_premise_false_eliminators(
                    ROOT, "Fixture.Module", [clean, missing]
                )

            self.assertEqual(first, {clean: []})
            self.assertEqual(set(second), {clean, missing})
            self.assertEqual(
                [call.args[2] for call in scan.call_args_list],
                [[clean, missing], [missing]],
            )
        finally:
            manifest_module._SOURCE_PREMISE_FALSE_SCAN_CACHE.clear()

    def test_structural_scan_cache_rejects_dependency_only_artifact_change(
        self,
    ) -> None:
        constructor = "Fixture.Model.mk"
        environments = iter(
            [
                "environment-before",
                "environment-before",
                "environment-after",
                "environment-after",
            ]
        )
        manifest_module._CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    side_effect=lambda *_args, **_kwargs: next(environments),
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_constructor_field_slot_count_script",
                    side_effect=[{constructor: 1}, {constructor: 2}],
                ) as run_script,
            ):
                first = manifest_module.run_lean_constructor_field_slot_counts(
                    ROOT, "Fixture.Module", [constructor]
                )
                second = manifest_module.run_lean_constructor_field_slot_counts(
                    ROOT, "Fixture.Module", [constructor]
                )

            self.assertEqual(first, {constructor: 1})
            self.assertEqual(second, {constructor: 2})
            self.assertEqual(run_script.call_count, 2)
        finally:
            manifest_module._CONSTRUCTOR_FIELD_SLOT_COUNT_CACHE.clear()

    def test_structural_scan_environment_identity_binds_dependency_artifacts(
        self,
    ) -> None:
        before = (("Fixture.Module", ("a" * 64, 1)),)
        after = (("Fixture.Module", ("b" * 64, 1)),)
        artifact_snapshots = iter([before, before, after, after])
        with (
            mock.patch.object(
                manifest_module, "_build_import_target", return_value=True
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_input_snapshot",
                return_value="c" * 64,
            ),
            mock.patch.object(
                manifest_module,
                "_build_target_artifact_snapshot",
                side_effect=lambda *_args, **_kwargs: next(artifact_snapshots),
            ),
            mock.patch.object(
                manifest_module,
                "_file_content_fingerprint",
                return_value=("d" * 64, 1),
            ),
        ):
            first = manifest_module._structural_scan_environment_identity(
                ROOT, "Fixture.Module", build_timeout_seconds=1
            )
            second = manifest_module._structural_scan_environment_identity(
                ROOT, "Fixture.Module", build_timeout_seconds=1
            )

        self.assertIsNotNone(first)
        self.assertIsNotNone(second)
        self.assertNotEqual(first, second)

    def test_structural_scan_cache_rejects_mid_scan_environment_mutation(self) -> None:
        locator: dict[str, object] = {
            "schema": 1,
            "kind": "projection",
            "declaration": "Fixture.Model.field",
            "field_index": 0,
        }
        locator["field_identity_sha256"] = recursive_field_safety_locator_identity(
            locator
        )
        identity = str(locator["field_identity_sha256"])
        diagnostics: dict[str, object] = {}
        manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    side_effect=["environment-before", "environment-after"],
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_recursive_field_proposition_sort_script",
                    return_value={identity: {"status": "ok"}},
                ),
            ):
                result = run_lean_recursive_field_proposition_sorts(
                    ROOT,
                    "Fixture.Module",
                    [locator],
                    diagnostics_out=diagnostics,
                )

            self.assertEqual(result, {})
            self.assertTrue(diagnostics["environment_changed"])
            self.assertEqual(
                manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE, {}
            )
        finally:
            manifest_module._RECURSIVE_FIELD_PROPOSITION_SORT_CACHE.clear()

    def test_structural_scan_cache_returns_copies(self) -> None:
        name = "Fixture.result"
        manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()
        try:
            with (
                mock.patch.object(
                    manifest_module,
                    "_structural_scan_environment_identity",
                    return_value="environment",
                ),
                mock.patch.object(
                    manifest_module,
                    "_run_type_witness_payload_safety_script",
                    return_value={name: [{"path": "result/0", "status": "ok"}]},
                ) as run_script,
            ):
                first = run_lean_type_witness_payload_safeties(
                    ROOT, "Fixture.Module", [name]
                )
                first[name][0]["status"] = "mutated"
                second = run_lean_type_witness_payload_safeties(
                    ROOT, "Fixture.Module", [name]
                )

            self.assertEqual(second[name][0]["status"], "ok")
            self.assertEqual(run_script.call_count, 1)
        finally:
            manifest_module._TYPE_WITNESS_PAYLOAD_SAFETY_CACHE.clear()

    def test_workspace_inventory_uses_exact_built_module_origins(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            build = root / ".lake" / "build" / "lib" / "lean"
            (build / "Paper").mkdir(parents=True)
            (build / "Shared").mkdir()
            (build / "Paper" / "Interface.olean").write_bytes(b"paper")
            (build / "Shared" / "Hidden.olean").write_bytes(b"shared")
            inventory = manifest_module._built_workspace_module_inventory(root)
        self.assertIsNotNone(inventory)
        modules, identity = inventory or ((), "")
        self.assertEqual(modules, ("Paper.Interface", "Shared.Hidden"))
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_semantic_artifact_identity_rejects_same_size_restored_mtime(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            artifact = Path(temp_dir) / "Module.olean"
            artifact.write_bytes(b"first")
            timestamp = artifact.stat().st_mtime_ns
            first = manifest_module._file_content_fingerprint(artifact)
            first_closure = manifest_module._closure_module_artifact_sha256(artifact)

            artifact.write_bytes(b"other")
            os.utime(artifact, ns=(timestamp, timestamp))
            second = manifest_module._file_content_fingerprint(artifact)
            second_closure = manifest_module._closure_module_artifact_sha256(artifact)

        self.assertNotEqual(first, second)
        self.assertNotEqual(first_closure, second_closure)

    def test_elaborated_proposition_graph_traverses_connectives_and_wrapper(
        self,
    ) -> None:
        manifest = self.manifests(
            """
def Wrap (p : Prop) : Prop := p
axiom demo (A B C : Prop) : (A ∧ Wrap (B → C)) ↔ (A ∧ (B → C))
""",
            ["demo"],
        )["demo"]
        graph = manifest["elaborated_proposition_graph"]
        self.assertTrue(graph["complete"])
        kinds = {node["kind"] for node in graph["nodes"]}
        self.assertTrue(
            {"iff", "conjunction", "transparent_wrapper", "implication"} <= kinds
        )
        self.assertTrue(any(edge["role"] == "expanded_body" for edge in graph["edges"]))

    def test_elaborated_proposition_graph_shares_deep_repeated_states(
        self,
    ) -> None:
        definitions = ["def Shared0 (p : Prop) : Prop := p"]
        definitions.extend(
            f"def Shared{index} (p : Prop) : Prop := "
            f"Shared{index - 1} p ∧ Shared{index - 1} p"
            for index in range(1, 14)
        )
        manifest = self.manifests(
            "\n".join([*definitions, "axiom demo (p : Prop) : Shared13 p"]),
            ["demo"],
        )["demo"]
        graph = manifest["elaborated_proposition_graph"]

        self.assertTrue(graph["complete"])
        self.assertLess(len(graph["nodes"]), 200)
        incoming = {node["path"]: 0 for node in graph["nodes"]}
        for edge in graph["edges"]:
            incoming[edge["target"]] += 1
        self.assertGreater(max(incoming.values()), 1)
        self.assertNotIn(
            "fuel_exhausted",
            {failure["tag"] for failure in graph["failures"]},
        )

    def test_elaborated_proposition_graph_retries_without_term_expansion(
        self,
    ) -> None:
        source = """
import Mathlib
namespace RecursiveTermFixture
noncomputable section

def countAtLeast {A : Type*} [Fintype A]
    (values : A → ℝ) (price : ℝ) : Nat :=
  ((Finset.univ : Finset A).filter fun i => price ≤ values i).card

def cappedRevenue {A : Type*} [Fintype A]
    (values : A → ℝ) (capacity : Nat) (price : ℝ) : ℝ :=
  (min capacity (countAtLeast values price) : ℝ) * price

def candidateRevenue {A : Type*} [Fintype A]
    (values : A → ℝ) (capacity : Nat) (i : A) : ℝ :=
  if 0 ≤ values i then cappedRevenue values capacity (values i) else 0

def fixedBenchmark {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) : ℝ :=
  (Finset.univ : Finset A).sup'
    (by
      obtain ⟨i⟩ := (inferInstance : Nonempty A)
      exact ⟨i, Finset.mem_univ i⟩)
    (candidateRevenue values capacity)

theorem existsMaximizer {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) :
    ∃ i : A, fixedBenchmark values capacity =
      candidateRevenue values capacity i := by
  classical
  let H : (Finset.univ : Finset A).Nonempty := by
    obtain ⟨i⟩ := (inferInstance : Nonempty A)
    exact ⟨i, by simp⟩
  obtain ⟨i, _hi, hmax⟩ :=
    (Finset.univ : Finset A).exists_mem_eq_sup'
      (f := candidateRevenue values capacity) H
  exact ⟨i, hmax⟩

def maximizer {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) : A :=
  Classical.choose (existsMaximizer values capacity)

def threshold {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) : ℝ :=
  let i := maximizer values capacity
  if 0 ≤ values i then values i else 0

def wrappedBenchmark {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) : ℝ :=
  fixedBenchmark values capacity

def resultContract (left right : Prop) : Prop := left ∧ right

axiom reviewedResult {A : Type*} [Fintype A] [Nonempty A]
    (values : A → ℝ) (capacity : Nat) :
    resultContract
      (∃ i : A, threshold values capacity = values i)
      (cappedRevenue values capacity (threshold values capacity) =
        wrappedBenchmark values capacity)

end
end RecursiveTermFixture
"""
        hash_tool = manifest_module._semantic_contract_closure_hash_tool_identity()
        self.assertIsNotNone(hash_tool)
        assert hash_tool is not None
        manifests = manifest_module._run_manifest_script(
            ROOT,
            source,
            ["RecursiveTermFixture.reviewedResult"],
            120,
            "RecursiveTermFixture",
            str(hash_tool["resolved_path"]),
        )
        manifest = manifests["RecursiveTermFixture.reviewedResult"]
        graph = manifest["elaborated_proposition_graph"]
        self.assertTrue(graph["complete"])
        self.assertEqual(graph["failures"], [])
        kinds = {node["kind"] for node in graph["nodes"]}
        self.assertTrue({"transparent_wrapper", "conjunction"} <= kinds)
        self.assertTrue(any(edge["role"] == "expanded_body" for edge in graph["edges"]))
        dependency_graph = manifest["semantic_dependency_graph"]
        self.assertTrue(dependency_graph["complete"])
        declarations = {node["declaration"] for node in dependency_graph["nodes"]}
        self.assertTrue(
            {
                "RecursiveTermFixture.candidateRevenue",
                "RecursiveTermFixture.fixedBenchmark",
                "RecursiveTermFixture.threshold",
            }
            <= declarations
        )

    def test_elaborated_proposition_graph_is_local_name_independent(self) -> None:
        source = """
namespace FirstPaper
def sourceFormula (p q : Prop) : Prop := p ∧ q
def wrapper (p q : Prop) : Prop := sourceFormula p q
end FirstPaper
namespace RenamedPaper
def unrelatedHelperName (left right : Prop) : Prop := left ∧ right
def unrelatedWrapperName (left right : Prop) : Prop :=
  unrelatedHelperName left right
end RenamedPaper
namespace ChangedPaper
def sourceFormula (p q : Prop) : Prop := p ↔ q
def wrapper (p q : Prop) : Prop := sourceFormula p q
end ChangedPaper
axiom firstRow (p q : Prop) : FirstPaper.wrapper p q
axiom renamedRow (left right : Prop) :
  RenamedPaper.unrelatedWrapperName left right
axiom changedRow (p q : Prop) : ChangedPaper.wrapper p q
"""
        manifests = self.manifests(source, ["firstRow", "renamedRow", "changedRow"])
        graph_hashes = {
            name: manifests[name]["elaborated_proposition_graph"][
                "semantic_graph_sha256"
            ]
            for name in manifests
        }
        self.assertEqual(graph_hashes["firstRow"], graph_hashes["renamedRow"])
        self.assertNotEqual(graph_hashes["firstRow"], graph_hashes["changedRow"])

    def test_elaborated_proposition_graph_normalizer_requires_rooted_dag(
        self,
    ) -> None:
        graph = {
            "schema": 1,
            "complete": True,
            "nodes": [
                {
                    "path": "result",
                    "kind": "constant",
                    "semantic_sha256": "1" * 64,
                },
                {
                    "path": "result/left",
                    "kind": "metadata",
                    "semantic_sha256": "2" * 64,
                },
                {
                    "path": "result/shared",
                    "kind": "constant",
                    "semantic_sha256": "3" * 64,
                },
            ],
            "edges": [
                {
                    "source": "result",
                    "target": "result/left",
                    "role": "left",
                },
                {
                    "source": "result",
                    "target": "result/shared",
                    "role": "right",
                },
                {
                    "source": "result/left",
                    "target": "result/shared",
                    "role": "body",
                },
            ],
            "failures": [],
        }
        normalized = manifest_module.normalize_elaborated_proposition_graph(graph)
        self.assertIsNotNone(normalized)
        assert normalized is not None

        changed_role = json.loads(json.dumps(graph))
        changed_role["edges"][1]["role"] = "argument"
        changed = manifest_module.normalize_elaborated_proposition_graph(changed_role)
        self.assertIsNotNone(changed)
        assert changed is not None
        self.assertNotEqual(
            normalized["semantic_graph_sha256"],
            changed["semantic_graph_sha256"],
        )

        invalid_graphs = []
        duplicate_edge = json.loads(json.dumps(graph))
        duplicate_edge["edges"].append(dict(duplicate_edge["edges"][0]))
        invalid_graphs.append(duplicate_edge)

        cyclic = json.loads(json.dumps(graph))
        cyclic["edges"].append(
            {
                "source": "result/shared",
                "target": "result/left",
                "role": "projected",
            }
        )
        invalid_graphs.append(cyclic)

        unreachable = json.loads(json.dumps(graph))
        unreachable["nodes"].append(
            {
                "path": "orphan",
                "kind": "constant",
                "semantic_sha256": "4" * 64,
            }
        )
        unreachable["edges"].append(
            {"source": "orphan", "target": "orphan", "role": "body"}
        )
        invalid_graphs.append(unreachable)

        root_has_parent = json.loads(json.dumps(graph))
        root_has_parent["edges"].append(
            {
                "source": "result/shared",
                "target": "result",
                "role": "body",
            }
        )
        invalid_graphs.append(root_has_parent)

        zero_indegree = json.loads(json.dumps(graph))
        zero_indegree["nodes"].append(
            {
                "path": "unparented",
                "kind": "constant",
                "semantic_sha256": "5" * 64,
            }
        )
        invalid_graphs.append(zero_indegree)

        for invalid in invalid_graphs:
            with self.subTest(edges=len(invalid["edges"])):
                self.assertIsNone(
                    manifest_module.normalize_elaborated_proposition_graph(invalid)
                )

    def test_semantic_dependency_manifest_rejects_stale_aggregate_digest(
        self,
    ) -> None:
        manifest = self.manifests("axiom demo : True", ["demo"])["demo"]
        tampered = json.loads(json.dumps(manifest))
        node = tampered["semantic_dependency_graph"]["nodes"][0]
        node["canonical_identity"] = {
            "tag": "local_axiom",
            "sha256": "f" * 64,
        }
        node.pop("semantic_identity_sha256", None)
        self.assertIsNone(manifest_module.semantic_dependency_manifest(tampered))

    def test_revalidation_basis_is_complete_and_excludes_stale_artifacts(
        self,
    ) -> None:
        manifest = self.manifests("def demo : Prop := True", ["demo"])["demo"]
        basis = manifest_module.lean_manifest_revalidation_basis(manifest)
        self.assertIsNotNone(basis)
        assert basis is not None
        self.assertEqual(
            manifest_module.signature_manifest_digest(basis),
            manifest_module.signature_manifest_digest(manifest),
        )
        self.assertNotIn("semantic_dependency_module_identities", basis)
        self.assertNotIn("semantic_dependency_environment_identities", basis)
        self.assertNotIn("semantic_dependency_manifest", basis)
        self.assertEqual(basis["schema"], manifest_module.MANIFEST_SCHEMA)

    def test_transitive_external_module_and_environment_pins_are_exact(self) -> None:
        canonical = {
            "schema": 1,
            "root_declaration": "Fixture.root",
            "complete": True,
            "nodes": [
                {
                    "declaration": "Fixture.root",
                    "module_origin": "Fixture",
                    "origin_class": "review_closure",
                    "declaration_kind": "theorem",
                    "canonical_identity": {
                        "tag": "local_theorem",
                        "sha256": "1" * 64,
                    },
                }
            ],
            "edges": [],
            "failures": [],
            "semantic_external_module_origins": ["Package.A", "Package.B"],
            "realization_external_module_origins": ["Package.A", "Package.B"],
        }
        proposition = {
            "schema": 1,
            "complete": True,
            "nodes": [
                {
                    "path": "result",
                    "kind": "constant",
                    "semantic_sha256": "2" * 64,
                }
            ],
            "edges": [],
            "failures": [],
        }
        environment = [
            {"path": "lean-toolchain", "sha256": "3" * 64},
            {"path": "lake-manifest.json", "sha256": "4" * 64},
        ]
        modules = [
            {
                "module_origin": "Package.A",
                "artifact_scope": "external",
                "artifact_sha256": "5" * 64,
                "dependency_lane": "semantic",
            },
            {
                "module_origin": "Package.B",
                "artifact_scope": "external",
                "artifact_sha256": "6" * 64,
                "dependency_lane": "semantic",
            },
        ]
        manifest = {
            "semantic_dependency_graph": canonical,
            "elaborated_proposition_graph": proposition,
        }
        first = manifest_module.semantic_dependency_manifest(
            manifest, modules, environment
        )
        self.assertIsNotNone(first)
        assert first is not None
        self.assertEqual(
            {item["module_origin"] for item in first["module_identities"]},
            {"Package.A", "Package.B"},
        )
        self.assertIsNone(
            manifest_module.semantic_dependency_manifest(
                manifest, modules[:-1], environment
            )
        )
        changed_modules = json.loads(json.dumps(modules))
        changed_modules[1]["artifact_sha256"] = "7" * 64
        changed = manifest_module.semantic_dependency_manifest(
            manifest, changed_modules, environment
        )
        self.assertIsNotNone(changed)
        assert changed is not None
        self.assertNotEqual(
            first["semantic_dependency_sha256"],
            changed["semantic_dependency_sha256"],
        )
        self.assertIsNone(
            manifest_module.semantic_dependency_manifest(manifest, modules, [])
        )

    def test_proof_only_change_preserves_statement_dependency_identity(self) -> None:
        first = self.manifests("theorem demo : True := by exact True.intro", ["demo"])[
            "demo"
        ]["semantic_dependency_manifest"]
        second = self.manifests(
            """
theorem demo : True := by
  have unused : (1 : Nat) + 0 = 1 := Nat.add_zero 1
  exact True.intro
""",
            ["demo"],
        )["demo"]["semantic_dependency_manifest"]
        self.assertEqual(
            first["semantic_dependency_sha256"],
            second["semantic_dependency_sha256"],
        )
        self.assertNotEqual(
            first["realization_dependency_sha256"],
            second["realization_dependency_sha256"],
        )

    def test_proof_only_local_nodes_require_exact_realization_artifact(self) -> None:
        graph = {
            "schema": 1,
            "root_declaration": "Fixture.Paper.endpoint",
            "complete": True,
            "nodes": [
                {
                    "declaration": "Fixture.Paper.endpoint",
                    "module_origin": "Fixture.Paper",
                    "origin_class": "review_closure",
                    "declaration_kind": "theorem",
                    "canonical_identity": {"tag": "sort", "level": {"tag": "zero"}},
                },
                {
                    "declaration": "Fixture.Proofs.helper",
                    "module_origin": "Fixture.Proofs",
                    "origin_class": "review_closure",
                    "declaration_kind": "theorem",
                    "canonical_identity": {"tag": "realization_artifact_terminal_v1"},
                },
            ],
            "edges": [
                {
                    "source": "Fixture.Paper.endpoint",
                    "target": "Fixture.Proofs.helper",
                    "role": "proof_uses_constant",
                }
            ],
            "failures": [],
            "semantic_external_module_origins": [],
            "realization_external_module_origins": [],
        }
        proposition = {
            "schema": 1,
            "complete": True,
            "nodes": [
                {
                    "path": "result",
                    "kind": "sort",
                    "semantic_sha256": "2" * 64,
                }
            ],
            "edges": [],
            "failures": [],
        }
        shape = {
            "schema": 2,
            "detector_basis": "lean_statement_dependency_graph_structural_v1",
            "scan_complete": True,
            "canonical_nodes_scanned": 1,
            "has_refl_trans_gen_path": False,
            "has_relation_valued_state_transition": False,
            "detected": False,
        }
        manifest = {
            "semantic_dependency_graph": graph,
            "elaborated_proposition_graph": proposition,
            "elaborated_execution_state_refinement_shape": shape,
        }
        environment = [
            {"path": "lean-toolchain", "sha256": "3" * 64},
            {"path": "lake-manifest.json", "sha256": "4" * 64},
        ]
        artifact = {
            "module_origin": "Fixture.Proofs",
            "artifact_scope": "workspace",
            "artifact_sha256": "5" * 64,
            "dependency_lane": "realization",
        }

        self.assertIsNone(
            manifest_module.semantic_dependency_manifest(manifest, [], environment)
        )
        accepted = manifest_module.semantic_dependency_manifest(
            manifest, [artifact], environment
        )
        self.assertIsNotNone(accepted)
        assert accepted is not None
        changed = dict(artifact)
        changed["artifact_sha256"] = "6" * 64
        changed_receipt = manifest_module.semantic_dependency_manifest(
            manifest, [changed], environment
        )
        self.assertIsNotNone(changed_receipt)
        assert changed_receipt is not None
        self.assertNotEqual(
            accepted["realization_dependency_sha256"],
            changed_receipt["realization_dependency_sha256"],
        )

    def test_item_revalidation_accepts_same_semantics_across_olean_change(
        self,
    ) -> None:
        declaration = "Fixture.Paper.reviewed"
        raw_graph = {
            "schema": 1,
            "root_declaration": declaration,
            "complete": True,
            "realization_complete": True,
            "nodes": [
                {
                    "declaration": declaration,
                    "module_origin": "Fixture.Paper",
                    "origin_class": "review_closure",
                    "declaration_kind": "theorem",
                    "canonical_identity": {
                        "tag": "theorem",
                        "type": {"tag": "sort", "level": {"tag": "zero"}},
                    },
                }
            ],
            "edges": [],
            "failures": [],
            "semantic_external_module_origins": [],
            "realization_external_module_origins": [],
        }
        graph = manifest_module.normalize_semantic_dependency_graph(raw_graph)
        self.assertIsNotNone(graph)
        assert graph is not None
        shape = {
            "schema": 2,
            "detector_basis": "lean_statement_dependency_graph_structural_v1",
            "scan_complete": True,
            "canonical_nodes_scanned": 1,
            "has_refl_trans_gen_path": False,
            "has_relation_valued_state_transition": False,
            "detected": False,
        }
        root_identity = next(
            node["semantic_identity_sha256"]
            for node in graph["nodes"]
            if node["declaration"] == declaration
        )
        manifest = {
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "semantic_dependency_graph": graph,
            "elaborated_execution_state_refinement_shape": shape,
        }
        receipt = {
            "schema": 1,
            "declaration_kind": "theorem",
            "conclusion_mode": "type_only",
            "root_semantic_identity_sha256": root_identity,
            "semantic_dependency_graph": graph,
            "elaborated_execution_state_refinement_shape": shape,
        }
        prior_context = {
            "schema": 3,
            "import_module": "Fixture.Paper",
            "olean_fingerprint": ["a" * 64, 1],
            "helper_fingerprint": ["b" * 64, 2],
            "semantic_hash_tool_identity": {"sha256": "c" * 64},
            "canonical_representation": manifest_module.CANONICAL_REPRESENTATION,
            "audit_modules": ["Fixture.Paper"],
        }
        current_context = {
            **prior_context,
            "olean_fingerprint": ["d" * 64, 1],
        }

        parsed = manifest_module.parse_signature_manifest_revalidation_output(
            manifest_module.SIGNATURE_MANIFEST_REVALIDATION_SENTINEL
            + declaration
            + ":"
            + json.dumps(
                {
                    "schema": 1,
                    "declaration_kind": "theorem",
                    "conclusion_mode": "type_only",
                    "semantic_dependency_graph": raw_graph,
                    "elaborated_execution_state_refinement_shape": shape,
                }
            )
        )
        self.assertEqual(
            parsed[declaration]["root_semantic_identity_sha256"], root_identity
        )

        self.assertTrue(
            manifest_module.signature_manifest_item_revalidation_matches(
                manifest,
                receipt,
                declaration=declaration,
                prior_context=prior_context,
                current_context=current_context,
            )
        )
        changed_receipt = {
            **receipt,
            "root_semantic_identity_sha256": "e" * 64,
        }
        self.assertFalse(
            manifest_module.signature_manifest_item_revalidation_matches(
                manifest,
                changed_receipt,
                declaration=declaration,
                prior_context=prior_context,
                current_context=current_context,
            )
        )

if __name__ == "__main__":
    unittest.main()
