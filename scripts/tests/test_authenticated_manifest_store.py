#!/usr/bin/env python3
"""Focused tests for the authenticated persistent manifest store."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import authenticated_manifest_store as STORE
from scripts import review_dashboard as DASHBOARD


class AuthenticatedManifestStoreTests(unittest.TestCase):
    SIGNATURE = "a" * 64
    DEPENDENCY = "b" * 64
    HASH_TOOL = {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": "/fixture/hash",
        "executable_sha256": "c" * 64,
        "version_stdout_sha256": "d" * 64,
        "version_banner": "sha256sum fixture",
        "known_vector": "sha256(abc)",
        "known_vector_sha256": (
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        ),
    }

    def context(self, module: str = "Fixture.Interface") -> dict[str, object]:
        return {
            "schema": 3,
            "import_module": module,
            "olean_fingerprint": ["d" * 64, 10],
            "helper_fingerprint": ["e" * 64, 20],
            "semantic_hash_tool_identity": dict(self.HASH_TOOL),
            "canonical_representation": "lean_compact_canonical_v2",
            "audit_scope_fingerprint": "f" * 64,
            "audit_modules": [module],
            "semantic_module_fingerprints": [[module, ["d" * 64, 10]]],
        }

    def manifest(
        self,
        *,
        signature: str | None = None,
        dependency: str | None = None,
        graph: dict[str, object] | None = None,
    ) -> dict[str, object]:
        return {
            "sha256": signature or self.SIGNATURE,
            "canonical_representation": "lean_compact_canonical_v2",
            "semantic_hash_tool_identity": dict(self.HASH_TOOL),
            "elaborated_proposition_graph": graph or {"schema": 1, "nodes": []},
            "semantic_dependency_manifest": {
                "semantic_dependency_sha256": dependency or self.DEPENDENCY
            },
        }

    def resume_manifest(
        self,
        *,
        signature: str | None = None,
        dependency: str | None = None,
    ) -> dict[str, object]:
        """Carrier-compatible Lean payload for exact-context resume tests."""

        manifest = self.manifest(signature=signature, dependency=dependency)
        manifest.update(
            {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [{"ref": "result", "role": "conclusion"}],
                "elaborated_execution_state_refinement_shape": {
                    "schema": 2,
                    "scan_complete": True,
                    "detected": False,
                },
                "elaborated_transparent_result_value_graph": None,
                "semantic_dependency_graph": {
                    "schema": 1,
                    "complete": True,
                    "realization_complete": True,
                    "semantic_graph_sha256": "1" * 64,
                    "realization_graph_sha256": "2" * 64,
                },
            }
        )
        return manifest

    def resume_binding(self, qualified: str) -> dict[str, str]:
        return {
            "qualified_declaration": qualified,
            "source_file": "Interface.lean",
            "declaration_kind": "theorem",
            "lean_source_declaration": "theorem reviewed : True",
        }

    def semantic_dependency(self, manifest: object) -> object:
        return (
            manifest.get("semantic_dependency_manifest", {})
            if isinstance(manifest, dict)
            else {}
        )

    def digest(self, manifest: object) -> str:
        return str(manifest.get("sha256") or "") if isinstance(manifest, dict) else ""

    def candidate(
        self,
        qualified: str,
        *,
        manifest: dict[str, object] | None = None,
        context: dict[str, object] | None = None,
        authority_binding: dict[str, object] | None = None,
    ) -> dict[str, object]:
        return {
            "qualified_declaration": qualified,
            "manifest": manifest or self.manifest(),
            "context": context or self.context(),
            "authority_binding": authority_binding
            or self.authority_binding(qualified),
        }

    def authority_binding(
        self,
        qualified: str,
        *,
        source_sha256: str | None = None,
    ) -> dict[str, object]:
        return {
            "qualified_declaration": qualified,
            "source_sha256": source_sha256 or "1" * 64,
        }

    def current_binding(
        self,
        qualified: str,
        *,
        manifest: dict[str, object] | None = None,
        authority_binding: dict[str, object] | None = None,
    ) -> dict[str, object]:
        current_manifest = manifest or self.manifest()
        dependency = self.semantic_dependency(current_manifest)
        return {
            "authority_binding": authority_binding
            or self.authority_binding(qualified),
            "elaborated_signature_sha256": self.digest(current_manifest),
            "semantic_dependency_sha256": str(
                dependency.get("semantic_dependency_sha256") or ""
            ),
            "elaborated_proposition_graph_sha256": (
                STORE.elaborated_proposition_graph_sha256(
                    current_manifest.get("elaborated_proposition_graph")
                )
            ),
        }

    def current_binding_digest(
        self,
        qualified: str,
        binding: dict[str, object] | None = None,
    ) -> str:
        current = binding or self.current_binding(qualified)
        authority_binding = current.get("authority_binding")
        self.assertIsInstance(authority_binding, dict)
        return STORE.declaration_authority_binding_sha256(
            qualified_declaration=qualified,
            authority_binding=authority_binding,
            elaborated_signature_sha256=str(
                current.get("elaborated_signature_sha256") or ""
            ),
            semantic_dependency_sha256=str(
                current.get("semantic_dependency_sha256") or ""
            ),
            elaborated_proposition_graph_sha256=str(
                current.get("elaborated_proposition_graph_sha256") or ""
            ),
        )

    def patches(self):
        return (
            mock.patch.object(STORE, "signature_manifest_digest", side_effect=self.digest),
            mock.patch.object(
                STORE,
                "semantic_dependency_manifest",
                side_effect=self.semantic_dependency,
            ),
        )

    def test_tracked_authority_is_compact_and_carrier_is_ignored(self) -> None:
        first = "Fixture.Interface.first"
        second = "Fixture.Interface.second"
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted = STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(first), self.candidate(second)],
                )
            authority_path = STORE.authenticated_manifest_authority_path(paper_dir)
            carrier_path = STORE.authenticated_manifest_carrier_path(paper_dir)
            authority = json.loads(authority_path.read_text(encoding="utf-8"))
            carrier = json.loads(carrier_path.read_text(encoding="utf-8"))

        self.assertEqual(accepted, {first, second})
        self.assertEqual(authority_path.parent.name, "audit")
        self.assertEqual(carrier_path.parent.name, ".review_traces")
        self.assertEqual(len(authority["contexts"]), 1)
        self.assertTrue(all("manifest" not in entry for entry in authority["entries"]))
        self.assertTrue(all("manifest" in entry for entry in carrier["entries"]))

    def test_merge_preserves_unmentioned_superset_entries(self) -> None:
        reviewed = "Fixture.Interface.reviewed"
        auxiliary = "Fixture.Interface.auxiliary"
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(reviewed), self.candidate(auxiliary)],
                )
                accepted = STORE.merge_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(reviewed)],
                )
                _paper, _contexts, entries = STORE._validated_store_entries(
                    paper_dir
                )

        self.assertEqual(accepted, {reviewed, auxiliary})
        self.assertEqual(set(entries), {reviewed, auxiliary})

    def test_merge_replaces_overlap_and_preserves_unmentioned_entry(self) -> None:
        reviewed = "Fixture.Interface.reviewed"
        auxiliary = "Fixture.Interface.auxiliary"
        replacement_signature = "9" * 64
        replacement_dependency = "8" * 64
        replacement_manifest = self.manifest(
            signature=replacement_signature,
            dependency=replacement_dependency,
            graph={"schema": 1, "nodes": ["replacement"]},
        )
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(reviewed), self.candidate(auxiliary)],
                )
                STORE.merge_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(reviewed, manifest=replacement_manifest)
                    ],
                )
                _paper, _contexts, entries = STORE._validated_store_entries(
                    paper_dir
                )

        self.assertEqual(set(entries), {reviewed, auxiliary})
        self.assertEqual(
            entries[reviewed][0]["elaborated_signature_sha256"],
            replacement_signature,
        )
        self.assertEqual(
            entries[reviewed][0]["semantic_dependency_sha256"],
            replacement_dependency,
        )
        self.assertEqual(
            entries[auxiliary][0]["elaborated_signature_sha256"], self.SIGNATURE
        )

    def test_merge_does_not_preserve_malformed_or_duplicate_prior_entries(
        self,
    ) -> None:
        prior = "Fixture.Interface.prior"
        current = "Fixture.Interface.current"
        for corruption in ("duplicate_authority", "malformed_carrier"):
            with self.subTest(corruption=corruption), tempfile.TemporaryDirectory() as temporary:
                paper_dir = Path(temporary) / "Fixture"
                digest_patch, dependency_patch = self.patches()
                with digest_patch, dependency_patch:
                    STORE.publish_authenticated_manifest_store(
                        paper_dir=paper_dir,
                        paper="Fixture",
                        candidates=[self.candidate(prior)],
                    )
                authority_path = STORE.authenticated_manifest_authority_path(
                    paper_dir
                )
                carrier_path = STORE.authenticated_manifest_carrier_path(paper_dir)
                if corruption == "duplicate_authority":
                    authority = json.loads(
                        authority_path.read_text(encoding="utf-8")
                    )
                    authority["entries"].append(dict(authority["entries"][0]))
                    authority["entries_sha256"] = STORE.canonical_json_sha256(
                        authority["entries"]
                    )
                    authority_path.write_text(
                        json.dumps(authority), encoding="utf-8"
                    )
                else:
                    carrier = json.loads(carrier_path.read_text(encoding="utf-8"))
                    carrier["entries"][0]["manifest"][
                        "elaborated_proposition_graph"
                    ] = {"schema": 1, "nodes": ["tampered"]}
                    carrier_path.write_text(json.dumps(carrier), encoding="utf-8")

                digest_patch, dependency_patch = self.patches()
                with digest_patch, dependency_patch:
                    accepted = STORE.merge_authenticated_manifest_store(
                        paper_dir=paper_dir,
                        paper="Fixture",
                        candidates=[self.candidate(current)],
                    )
                    _paper, _contexts, entries = STORE._validated_store_entries(
                        paper_dir
                    )

                self.assertEqual(accepted, {current})
                self.assertEqual(set(entries), {current})

    def test_merged_preserved_entries_reject_a_changed_context(self) -> None:
        reviewed = "Fixture.Interface.reviewed"
        auxiliary = "Fixture.Interface.auxiliary"
        context = self.context()
        changed_context = self.context()
        changed_context["helper_fingerprint"] = ["0" * 64, 20]
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(reviewed, context=context),
                        self.candidate(auxiliary, context=context),
                    ],
                )
                STORE.merge_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(reviewed, context=context)],
                )
                seed = mock.Mock(return_value={reviewed, auxiliary})
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        reviewed: self.current_binding(reviewed),
                        auxiliary: self.current_binding(auxiliary),
                    },
                    current_contexts=[changed_context],
                    reattach=lambda _root, manifests, timeout_seconds: {
                        key: dict(value) for key, value in manifests.items()
                    },
                    seed=seed,
                )

        self.assertEqual(accepted, {})
        self.assertEqual(diagnostics["candidate_count"], 2)
        self.assertEqual(diagnostics["seeded_count"], 0)
        self.assertEqual(
            diagnostics["rejected_by_reason"],
            {"current_context_identity_changed": [auxiliary, reviewed]},
        )
        seed.assert_not_called()

    def test_current_semantic_binding_reuses_manifest_across_context_change(
        self,
    ) -> None:
        reviewed = "Fixture.Interface.reviewed"
        context = self.context()
        changed_context = self.context()
        changed_context["helper_fingerprint"] = ["0" * 64, 20]
        binding = self.current_binding(reviewed)
        semantic_binding = {
            field: str(binding[field])
            for field in (
                "elaborated_signature_sha256",
                "semantic_dependency_sha256",
                "elaborated_proposition_graph_sha256",
            )
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(reviewed, context=context)],
                )
                seed = mock.Mock(return_value={reviewed})
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={reviewed: binding},
                    current_contexts=[changed_context],
                    semantic_revalidated_bindings={reviewed: semantic_binding},
                    reattach=lambda _root, manifests, timeout_seconds: {
                        key: dict(value) for key, value in manifests.items()
                    },
                    seed=seed,
                )

        self.assertEqual(set(accepted), {reviewed})
        self.assertEqual(diagnostics["fresh_required_count"], 0)
        self.assertEqual(diagnostics["rejected_by_reason"], {})
        self.assertEqual(
            seed.call_args.kwargs["current_context"], changed_context
        )

    def test_prime_scopes_diagnostics_and_work_to_requested_roots(self) -> None:
        requested = "Fixture.Interface.requested"
        unrelated = "Fixture.Interface.unrelated"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(requested, context=context),
                        self.candidate(unrelated, context=context),
                    ],
                )
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        requested: self.current_binding(requested),
                    },
                    current_contexts=[context],
                    requested_declarations=[requested],
                    reattach=lambda _root, manifests, timeout_seconds: {
                        key: dict(value) for key, value in manifests.items()
                    },
                    seed=lambda _root, _module, requested_names, manifests, **_kwargs: (
                        set(requested_names) & set(manifests)
                    ),
                )

        self.assertEqual(set(accepted), {requested})
        self.assertEqual(diagnostics["requested_count"], 1)
        self.assertEqual(diagnostics["candidate_count"], 1)
        self.assertEqual(diagnostics["fresh_required_count"], 0)
        self.assertEqual(diagnostics["rejected_by_reason"], {})

    def test_prime_returns_only_entries_accepted_by_independent_seed(self) -> None:
        first = "Fixture.Interface.first"
        second = "Fixture.Interface.second"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(first, context=context),
                        self.candidate(second, context=context),
                    ],
                )
                seed = mock.Mock(return_value={second})
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        first: self.current_binding(first),
                        second: self.current_binding_digest(second),
                    },
                    current_contexts=[context],
                    reattach=lambda _root, manifests, timeout_seconds: {
                        key: dict(value) for key, value in manifests.items()
                    },
                    seed=seed,
                )

        self.assertEqual(set(accepted), {second})
        self.assertEqual(diagnostics["seeded_declarations"], [second])
        self.assertEqual(diagnostics["fresh_required_count"], 1)
        self.assertEqual(
            diagnostics["rejected_by_reason"],
            {"context_cache_seed_rejected": [first]},
        )
        self.assertEqual(set(seed.call_args.args[2]), {first, second})
        self.assertEqual(set(seed.call_args.args[3]), {first, second})
        self.assertEqual(seed.call_args.kwargs["current_context"], context)

    def test_prime_rejects_self_consistent_forged_manifest_authority(
        self,
    ) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        true_manifest = self.manifest()
        forged_manifest = self.manifest(
            signature="9" * 64,
            dependency="8" * 64,
            graph={"schema": 1, "nodes": ["forged"]},
        )
        # The forged store deliberately retains the genuine source-binding
        # body.  Its own authority and carrier are otherwise self-consistent.
        # Only the independently reconstructed full declaration binding can
        # detect that the mathematical manifest identities were replaced.
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=forged_manifest,
                            context=context,
                            authority_binding=self.authority_binding(qualified),
                        )
                    ],
                )
                reattach = mock.Mock(return_value={qualified: forged_manifest})
                seed = mock.Mock(return_value={qualified})
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        qualified: self.current_binding(
                            qualified,
                            manifest=true_manifest,
                        )
                    },
                    current_contexts=[context],
                    reattach=reattach,
                    seed=seed,
                )

        self.assertEqual(accepted, {})
        self.assertEqual(
            diagnostics["rejected_by_reason"],
            {"current_declaration_binding_changed": [qualified]},
        )
        reattach.assert_not_called()
        seed.assert_not_called()

    def test_prime_rejects_changed_or_missing_current_source_binding(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        cases = {
            "changed": {
                qualified: self.current_binding(
                    qualified,
                    authority_binding=self.authority_binding(
                        qualified,
                        source_sha256="2" * 64,
                    ),
                )
            },
            "missing": {},
        }
        for label, current_bindings in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temporary:
                paper_dir = Path(temporary) / "Fixture"
                digest_patch, dependency_patch = self.patches()
                with digest_patch, dependency_patch:
                    STORE.publish_authenticated_manifest_store(
                        paper_dir=paper_dir,
                        paper="Fixture",
                        candidates=[self.candidate(qualified, context=context)],
                    )
                    reattach = mock.Mock(return_value={qualified: self.manifest()})
                    seed = mock.Mock(return_value={qualified})
                    accepted, diagnostics = (
                        STORE.prime_authenticated_manifest_store(
                            root=Path(temporary),
                            paper_dir=paper_dir,
                            current_declaration_bindings=current_bindings,
                            current_contexts=[context],
                            reattach=reattach,
                            seed=seed,
                        )
                    )

                self.assertEqual(accepted, {})
                expected_reason = (
                    "current_declaration_binding_changed"
                    if label == "changed"
                    else "current_declaration_binding_missing"
                )
                self.assertEqual(
                    diagnostics["rejected_by_reason"],
                    {expected_reason: [qualified]},
                )
                reattach.assert_not_called()
                seed.assert_not_called()

    def test_prime_reports_context_provider_once_and_hands_context_to_seed(
        self,
    ) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(qualified, context=context)],
                )
                context_provider = mock.Mock(return_value=context)
                seed = mock.Mock(return_value={qualified})
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        qualified: self.current_binding(qualified)
                    },
                    context_provider=context_provider,
                    reattach=lambda _root, manifests, timeout_seconds: {
                        key: dict(value) for key, value in manifests.items()
                    },
                    seed=seed,
                )

        self.assertEqual(set(accepted), {qualified})
        context_provider.assert_called_once()
        self.assertEqual(diagnostics["context_provider_call_count"], 1)
        self.assertEqual(seed.call_args.kwargs["current_context"], context)

    def test_tampered_carrier_payload_is_a_cache_miss(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(qualified, context=context)],
                )
            carrier_path = STORE.authenticated_manifest_carrier_path(paper_dir)
            carrier = json.loads(carrier_path.read_text(encoding="utf-8"))
            carrier["entries"][0]["manifest"]["elaborated_proposition_graph"] = {
                "schema": 1,
                "nodes": ["tampered"],
            }
            carrier_path.write_text(json.dumps(carrier), encoding="utf-8")
            seed = mock.Mock(return_value={qualified})
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        qualified: self.current_binding(qualified)
                    },
                    current_contexts=[context],
                    seed=seed,
                )

        self.assertEqual(accepted, {})
        self.assertEqual(diagnostics["candidate_count"], 0)
        seed.assert_not_called()

    def test_missing_ignored_carrier_is_a_cache_miss(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(qualified, context=context)],
                )
            STORE.authenticated_manifest_carrier_path(paper_dir).unlink()
            seed = mock.Mock(return_value={qualified})
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        qualified: self.current_binding(qualified)
                    },
                    current_contexts=[context],
                    seed=seed,
                )

        self.assertEqual(accepted, {})
        self.assertEqual(diagnostics["candidate_count"], 0)
        seed.assert_not_called()

    def legacy_row(
        self, qualified: str, manifest: dict[str, object]
    ) -> dict[str, object]:
        return {
            "full_name": qualified,
            "lean_signature_sha256": self.SIGNATURE,
            "lean_signature_manifest": manifest,
            "llm_match_reason": "mutable dashboard prose is not authority",
        }

    def authority_row(
        self,
        qualified: str,
        graph: dict[str, object],
        *,
        legacy_embedded_graph: bool = False,
    ) -> dict[str, object]:
        row: dict[str, object] = {
            "qualified_declaration": qualified,
            "lean_source_declaration": "theorem reviewed : True := by trivial",
            "source_file": "papers/Fixture/Interface.lean",
            "source_sha256": "1" * 64,
            "elaborated_signature_sha256": self.SIGNATURE,
            "semantic_dependency_sha256": self.DEPENDENCY,
        }
        if legacy_embedded_graph:
            row["elaborated_proposition_graph"] = graph
        else:
            row["elaborated_proposition_graph_sha256"] = (
                STORE.elaborated_proposition_graph_sha256(graph)
            )
        return row

    def test_schema20_migration_requires_every_exact_semantic_coordinate(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        graph = {"schema": 1, "nodes": []}
        context = self.context()
        manifest = self.manifest(graph=graph)
        legacy = {
            "schema": 20,
            "paper": "Fixture",
            "rows": [
                self.legacy_row(qualified, manifest),
                {
                    "name": "unqualified_neighbor",
                    "lean_signature_sha256": self.SIGNATURE,
                    "lean_signature_manifest": manifest,
                },
            ],
            "signature_contexts": {"Interface.lean": context},
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted = STORE.migrate_legacy_schema20_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    validated_configured_rows=[self.authority_row(qualified, graph)],
                    legacy_cache=legacy,
                )

        self.assertEqual(accepted, {qualified})

    def test_schema20_migration_accepts_legacy_embedded_graph_authority(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        graph = {"schema": 1, "nodes": []}
        manifest = self.manifest(graph=graph)
        legacy = {
            "schema": 20,
            "paper": "Fixture",
            "rows": [self.legacy_row(qualified, manifest)],
            "signature_contexts": {"Interface.lean": self.context()},
        }
        with tempfile.TemporaryDirectory() as temporary:
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted = STORE.migrate_legacy_schema20_manifest_store(
                    paper_dir=Path(temporary) / "Fixture",
                    paper="Fixture",
                    validated_configured_rows=[
                        self.authority_row(
                            qualified,
                            graph,
                            legacy_embedded_graph=True,
                        )
                    ],
                    legacy_cache=legacy,
                )

        self.assertEqual(accepted, {qualified})

    def test_graph_authority_rejects_conflicting_compact_and_legacy_pins(self) -> None:
        graph = {"schema": 1, "nodes": []}
        row = self.authority_row(
            "Fixture.Interface.reviewed",
            graph,
            legacy_embedded_graph=True,
        )
        row["elaborated_proposition_graph_sha256"] = "9" * 64

        self.assertEqual(
            STORE.configured_review_row_proposition_graph_sha256(row),
            "",
        )

    def test_graph_authority_rejects_present_malformed_transitional_fields(self) -> None:
        graph = {"schema": 1, "nodes": []}
        malformed_compact = self.authority_row(
            "Fixture.Interface.reviewed",
            graph,
            legacy_embedded_graph=True,
        )
        malformed_compact["elaborated_proposition_graph_sha256"] = "not-a-digest"
        malformed_embedded = self.authority_row(
            "Fixture.Interface.reviewed",
            graph,
        )
        malformed_embedded["elaborated_proposition_graph"] = []

        self.assertEqual(
            STORE.configured_review_row_proposition_graph_sha256(
                malformed_compact
            ),
            "",
        )
        self.assertEqual(
            STORE.configured_review_row_proposition_graph_sha256(
                malformed_embedded
            ),
            "",
        )

    def test_invalid_then_valid_duplicate_candidate_is_omitted(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        invalid = self.candidate(qualified)
        invalid["manifest"] = "malformed"
        valid = self.candidate(qualified)
        digest_patch, dependency_patch = self.patches()
        with digest_patch, dependency_patch:
            authority, carrier, accepted = (
                STORE.build_authenticated_manifest_store_payloads(
                    paper="Fixture",
                    candidates=[invalid, valid],
                )
            )

        self.assertEqual(accepted, set())
        self.assertEqual(authority["entries"], [])
        self.assertEqual(carrier["entries"], [])

    def test_duplicate_tracked_authority_coordinate_is_a_cache_miss(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[self.candidate(qualified, context=context)],
                )
            authority_path = STORE.authenticated_manifest_authority_path(paper_dir)
            authority = json.loads(authority_path.read_text(encoding="utf-8"))
            authority["entries"].append(dict(authority["entries"][0]))
            authority["entries_sha256"] = STORE.canonical_json_sha256(
                authority["entries"]
            )
            authority_path.write_text(json.dumps(authority), encoding="utf-8")
            seed = mock.Mock(return_value={qualified})
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted, diagnostics = STORE.prime_authenticated_manifest_store(
                    root=Path(temporary),
                    paper_dir=paper_dir,
                    current_declaration_bindings={
                        qualified: self.current_binding(qualified)
                    },
                    current_contexts=[context],
                    seed=seed,
                )

        self.assertEqual(accepted, {})
        self.assertEqual(diagnostics["candidate_count"], 0)
        seed.assert_not_called()

    def test_schema20_migration_rejects_individual_graph_and_dependency_mismatches(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        graph = {"schema": 1, "nodes": []}
        cases = {
            "graph": self.manifest(graph={"schema": 1, "nodes": ["different"]}),
            "dependency": self.manifest(dependency="9" * 64, graph=graph),
            "signature": self.manifest(signature="8" * 64, graph=graph),
        }
        for label, manifest in cases.items():
            with self.subTest(label=label), tempfile.TemporaryDirectory() as temporary:
                legacy = {
                    "schema": 20,
                    "paper": "Fixture",
                    "rows": [self.legacy_row(qualified, manifest)],
                    "signature_contexts": {"Interface.lean": self.context()},
                }
                digest_patch, dependency_patch = self.patches()
                with digest_patch, dependency_patch:
                    accepted = STORE.migrate_legacy_schema20_manifest_store(
                        paper_dir=Path(temporary) / "Fixture",
                        paper="Fixture",
                        validated_configured_rows=[
                            self.authority_row(qualified, graph)
                        ],
                        legacy_cache=legacy,
                    )
                self.assertEqual(accepted, set())

    def test_schema20_migration_rejects_duplicate_authority_rows(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        graph = {"schema": 1, "nodes": []}
        manifest = self.manifest(graph=graph)
        authority_row = self.authority_row(qualified, graph)
        legacy = {
            "schema": 20,
            "paper": "Fixture",
            "rows": [self.legacy_row(qualified, manifest)],
            "signature_contexts": {"Interface.lean": self.context()},
        }
        with tempfile.TemporaryDirectory() as temporary:
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                accepted = STORE.migrate_legacy_schema20_manifest_store(
                    paper_dir=Path(temporary) / "Fixture",
                    paper="Fixture",
                    validated_configured_rows=[authority_row, dict(authority_row)],
                    legacy_cache=legacy,
                )

        self.assertEqual(accepted, set())

    def test_cache_orchestration_is_outside_raw_producer_markers(self) -> None:
        source = (
            Path(__file__).resolve().parents[2]
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        ).read_text(encoding="utf-8")
        lines = source.splitlines()
        begin = [
            index
            for index, line in enumerate(lines)
            if line.strip() == "# SOURCE_RECORD_RAW_PRODUCER_BEGIN"
        ]
        end = [
            index
            for index, line in enumerate(lines)
            if line.strip() == "# SOURCE_RECORD_RAW_PRODUCER_END"
        ]
        self.assertEqual(len(begin), 1)
        self.assertEqual(len(end), 1)
        raw_block = "\n".join(lines[begin[0] + 1 : end[0]])
        self.assertNotIn("prime_source_record_signature_manifest_store(", raw_block)
        self.assertNotIn("publish_source_record_signature_manifest_store(", raw_block)
        self.assertNotIn(
            "checkpoint_source_record_manifest_resume_cache(", raw_block
        )

    def test_current_raw_row_reconstructs_exact_dashboard_binding(self) -> None:
        qualified = "Fixture.PaperInterface.reviewed"
        graph = {"schema": 1, "nodes": []}
        manifest = self.manifest(graph=graph)
        source = (
            "namespace Fixture.PaperInterface\n"
            "theorem reviewed : True := by trivial\n"
            "end Fixture.PaperInterface\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text(source, encoding="utf-8")
            item = mock.Mock(
                full_name=qualified,
                lean_signature_manifest=manifest,
                lean_signature_sha256=self.SIGNATURE,
                kind="theorem",
            )
            with (
                mock.patch.object(DASHBOARD, "ROOT", root),
                mock.patch.object(
                    DASHBOARD, "review_source_file", return_value=interface
                ),
                mock.patch.object(
                    DASHBOARD,
                    "assumption_source_file",
                    return_value=folder / "Assumptions.lean",
                ),
                mock.patch.object(
                    DASHBOARD,
                    "merge_authenticated_manifest_store",
                    return_value={qualified},
                ) as publish,
            ):
                DASHBOARD.publish_review_signature_manifest_store(
                    folder,
                    [item],
                    {"PaperInterface.lean": self.context("Fixture.PaperInterface")},
                )
                raw_row = {
                    "row": "nonsemantic-navigation-label",
                    "qualified_declaration": qualified,
                    "source_file": "papers/Fixture/PaperInterface.lean",
                    "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                    # The source-record producer retains the proof body while
                    # the dashboard store binds its parsed type/signature.
                    "lean_source_declaration": source.split("\n", 1)[1],
                    "elaborated_signature_sha256": self.SIGNATURE,
                    "semantic_dependency_sha256": self.DEPENDENCY,
                    "elaborated_proposition_graph_sha256": (
                        STORE.elaborated_proposition_graph_sha256(graph)
                    ),
                }
                bindings = DASHBOARD.current_review_signature_manifest_bindings(
                    folder, [raw_row]
                )
                renamed_bindings = (
                    DASHBOARD.current_review_signature_manifest_bindings(
                        folder,
                        [{**raw_row, "row": "different-navigation-label"}],
                    )
                )

        published = publish.call_args.kwargs["candidates"][0]["authority_binding"]
        self.assertEqual(bindings, renamed_bindings)
        self.assertEqual(bindings[qualified]["authority_binding"], published)
        self.assertNotIn(
            "by trivial",
            bindings[qualified]["authority_binding"]["lean_source_declaration"],
        )
        self.assertEqual(
            bindings[qualified]["semantic_dependency_sha256"], self.DEPENDENCY
        )

    def test_current_raw_row_binding_rejects_stale_ambiguous_or_malformed_rows(
        self,
    ) -> None:
        qualified = "Fixture.PaperInterface.reviewed"
        graph_sha256 = STORE.elaborated_proposition_graph_sha256(
            {"schema": 1, "nodes": []}
        )
        source = (
            "namespace Fixture.PaperInterface\n"
            "theorem reviewed : True := by trivial\n"
            "end Fixture.PaperInterface\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text(source, encoding="utf-8")
            row = {
                "qualified_declaration": qualified,
                "source_file": "papers/Fixture/PaperInterface.lean",
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "elaborated_signature_sha256": self.SIGNATURE,
                "semantic_dependency_sha256": self.DEPENDENCY,
                "elaborated_proposition_graph_sha256": graph_sha256,
            }
            with (
                mock.patch.object(DASHBOARD, "ROOT", root),
                mock.patch.object(
                    DASHBOARD, "review_source_file", return_value=interface
                ),
                mock.patch.object(
                    DASHBOARD,
                    "assumption_source_file",
                    return_value=folder / "Assumptions.lean",
                ),
            ):
                stale = {**row, "source_sha256": "9" * 64}
                malformed = {
                    **row,
                    "semantic_dependency_sha256": "not-a-digest",
                }
                self.assertEqual(
                    DASHBOARD.current_review_signature_manifest_bindings(
                        folder, [stale]
                    ),
                    {},
                )
                self.assertEqual(
                    DASHBOARD.current_review_signature_manifest_bindings(
                        folder, [malformed]
                    ),
                    {},
                )
                self.assertEqual(
                    DASHBOARD.current_review_signature_manifest_bindings(
                        folder, [row, dict(row)]
                    ),
                    {},
                )

    def test_closeout_prime_uses_only_supplied_current_contexts(self) -> None:
        qualified = "Fixture.PaperInterface.reviewed"
        graph = {"schema": 1, "nodes": []}
        source = (
            "namespace Fixture.PaperInterface\n"
            "theorem reviewed : True := by trivial\n"
            "end Fixture.PaperInterface\n"
        )
        context = self.context("Fixture.PaperInterface")
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text(source, encoding="utf-8")
            row = {
                "qualified_declaration": qualified,
                "source_file": "papers/Fixture/PaperInterface.lean",
                "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
                "elaborated_signature_sha256": self.SIGNATURE,
                "semantic_dependency_sha256": self.DEPENDENCY,
                "elaborated_proposition_graph_sha256": (
                    STORE.elaborated_proposition_graph_sha256(graph)
                ),
            }
            diagnostics = {
                "schema": 1,
                "paper": "Fixture",
                "candidate_count": 1,
                "context_count": 1,
                "accepted_context_count": 1,
                "context_provider_call_count": 0,
                "seeded_count": 1,
                "seeded_declarations": [qualified],
                "fresh_required_count": 0,
                "rejected_by_reason": {},
                "store_status": "validated",
            }
            with (
                mock.patch.object(DASHBOARD, "ROOT", root),
                mock.patch.object(
                    DASHBOARD, "review_source_file", return_value=interface
                ),
                mock.patch.object(
                    DASHBOARD,
                    "assumption_source_file",
                    return_value=folder / "Assumptions.lean",
                ),
                mock.patch.object(
                    DASHBOARD,
                    "prime_authenticated_manifest_store",
                    return_value=({qualified: self.manifest(graph=graph)}, diagnostics),
                ) as prime,
            ):
                result = DASHBOARD.prime_review_signature_manifest_store(
                    folder,
                    {"PaperInterface.lean": context},
                    allow_migration_write=False,
                    validated_configured_review_rows=[row],
                )

        call = prime.call_args.kwargs
        self.assertEqual(call["current_contexts"], [context])
        self.assertIs(
            call["context_provider"],
            DASHBOARD._unavailable_manifest_cache_context,
        )
        self.assertEqual(set(call["current_declaration_bindings"]), {qualified})
        self.assertEqual(result["seeded_count"], 1)
        self.assertEqual(result["configured_review_row_count"], 1)
        self.assertEqual(result["current_declaration_binding_count"], 1)

    def test_standalone_dashboard_prime_does_not_read_store(self) -> None:
        with mock.patch.object(
            DASHBOARD, "prime_authenticated_manifest_store"
        ) as prime:
            diagnostics = DASHBOARD.prime_review_signature_manifest_store(
                Path("papers/Fixture"), {}, allow_migration_write=False
            )

        prime.assert_not_called()
        self.assertEqual(
            diagnostics["store_status"],
            "skipped_without_independent_current_bindings",
        )

    def test_dashboard_subset_publish_preserves_raw_auxiliary_entry(self) -> None:
        reviewed = "Fixture.Interface.reviewed"
        auxiliary = "Fixture.Interface.auxiliary"
        context = self.context()
        reviewed_manifest = self.manifest()
        item = mock.Mock(
            full_name=reviewed,
            lean_signature_manifest=reviewed_manifest,
            lean_signature_sha256=self.SIGNATURE,
            kind="theorem",
        )
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            interface = folder / "Interface.lean"
            interface.touch()
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=folder,
                    paper="Fixture",
                    candidates=[
                        self.candidate(reviewed, context=context),
                        self.candidate(auxiliary, context=context),
                    ],
                )
                with (
                    mock.patch.object(
                        DASHBOARD, "review_source_file", return_value=interface
                    ),
                    mock.patch.object(
                        DASHBOARD,
                        "assumption_source_file",
                        return_value=folder / "Assumptions.lean",
                    ),
                    mock.patch.object(
                        DASHBOARD,
                        "parse_review_source_declarations",
                        return_value=[
                            (
                                "theorem",
                                "reviewed",
                                reviewed,
                                "theorem reviewed : True := by trivial",
                                "",
                                1,
                                interface,
                            )
                        ],
                    ),
                ):
                    accepted = DASHBOARD.publish_review_signature_manifest_store(
                        folder,
                        [item],
                        {"Interface.lean": context},
                    )
                _paper, _contexts, entries = STORE._validated_store_entries(folder)

        self.assertEqual(accepted, {reviewed, auxiliary})
        self.assertEqual(set(entries), {reviewed, auxiliary})

    def test_item_revalidation_seeds_unchanged_declaration_after_context_change(
        self,
    ) -> None:
        qualified = "Fixture.Interface.reviewed"
        source_file = "papers/Fixture/Interface.lean"
        declaration = "theorem reviewed : True := by trivial"
        graph = {"schema": 1, "nodes": []}
        prior_context = self.context()
        current_context = self.context()
        current_context["olean_fingerprint"] = ["9" * 64, 30]
        current_context["audit_scope_fingerprint"] = "8" * 64
        current_context["semantic_module_fingerprints"] = [
            ["Fixture.Interface", ["9" * 64, 30]]
        ]
        manifest = self.manifest(graph=graph)
        prior_row = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "lean_source_declaration": declaration,
            "elaborated_signature_sha256": self.SIGNATURE,
            "semantic_dependency_sha256": self.DEPENDENCY,
            "elaborated_proposition_graph_sha256": (
                STORE.elaborated_proposition_graph_sha256(graph)
            ),
        }
        receipt = {
            "semantic_dependency_graph": {"schema": 1},
            "elaborated_execution_state_refinement_shape": {"schema": 1},
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=manifest,
                            context=prior_context,
                        )
                    ],
                )
                with (
                    mock.patch.object(
                        STORE,
                        "signature_manifest_item_revalidation_matches",
                        return_value=True,
                    ) as matches,
                    mock.patch.object(
                        STORE,
                        "elaborated_proposition_graph_sha256",
                        return_value=STORE.elaborated_proposition_graph_sha256(graph),
                    ),
                ):
                    accepted, diagnostics = (
                        STORE.prime_authenticated_manifest_store_with_item_revalidation(
                            root=paper_dir.parent,
                            paper_dir=paper_dir,
                            authenticated_prior_rows=[prior_row],
                            current_declarations={
                                qualified: {
                                    "source_file": source_file,
                                    "lean_source_declaration": declaration,
                                }
                            },
                            prior_contexts=[prior_context],
                            current_contexts=[current_context],
                            revalidate=mock.Mock(
                                return_value={qualified: receipt}
                            ),
                            reattach=mock.Mock(
                                side_effect=lambda _root, manifests, **_kwargs: manifests
                            ),
                            seed=mock.Mock(return_value={qualified}),
                        )
                    )

        self.assertEqual(set(accepted), {qualified})
        self.assertEqual(diagnostics["item_revalidation_requested_count"], 1)
        self.assertEqual(diagnostics["item_revalidated_count"], 1)
        self.assertEqual(diagnostics["fresh_required_count"], 0)
        matches.assert_called_once()

    def test_item_revalidation_rejects_changed_declaration_before_lean(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        source_file = "papers/Fixture/Interface.lean"
        graph = {"schema": 1, "nodes": []}
        prior_context = self.context()
        prior_row = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "lean_source_declaration": "theorem reviewed : True := by trivial",
            "elaborated_signature_sha256": self.SIGNATURE,
            "semantic_dependency_sha256": self.DEPENDENCY,
            "elaborated_proposition_graph_sha256": (
                STORE.elaborated_proposition_graph_sha256(graph)
            ),
        }
        revalidate = mock.Mock()
        seed = mock.Mock()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=self.manifest(graph=graph),
                            context=prior_context,
                        )
                    ],
                )
                accepted, diagnostics = (
                    STORE.prime_authenticated_manifest_store_with_item_revalidation(
                        root=paper_dir.parent,
                        paper_dir=paper_dir,
                        authenticated_prior_rows=[prior_row],
                        current_declarations={
                            qualified: {
                                "source_file": source_file,
                                "lean_source_declaration": (
                                    "theorem reviewed : False := by trivial"
                                ),
                            }
                        },
                        prior_contexts=[prior_context],
                        current_contexts=[prior_context],
                        revalidate=revalidate,
                        reattach=mock.Mock(),
                        seed=seed,
                    )
                )

        self.assertEqual(accepted, {})
        self.assertEqual(
            diagnostics["rejected_by_reason"]["declaration_source_changed"],
            [qualified],
        )
        revalidate.assert_not_called()
        seed.assert_not_called()

    def test_item_revalidation_rejects_raw_authority_identity_mismatch(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        source_file = "papers/Fixture/Interface.lean"
        declaration = "theorem reviewed : True := by trivial"
        graph = {"schema": 1, "nodes": []}
        context = self.context()
        prior_row = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "lean_source_declaration": declaration,
            "elaborated_signature_sha256": "9" * 64,
            "semantic_dependency_sha256": self.DEPENDENCY,
            "elaborated_proposition_graph_sha256": (
                STORE.elaborated_proposition_graph_sha256(graph)
            ),
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=self.manifest(graph=graph),
                            context=context,
                        )
                    ],
                )
                accepted, diagnostics = (
                    STORE.prime_authenticated_manifest_store_with_item_revalidation(
                        root=paper_dir.parent,
                        paper_dir=paper_dir,
                        authenticated_prior_rows=[prior_row],
                        current_declarations={
                            qualified: {
                                "source_file": source_file,
                                "lean_source_declaration": declaration,
                            }
                        },
                        prior_contexts=[context],
                        current_contexts=[context],
                        revalidate=mock.Mock(),
                        reattach=mock.Mock(),
                        seed=mock.Mock(),
                    )
                )

        self.assertEqual(accepted, {})
        self.assertEqual(
            diagnostics["rejected_by_reason"][
                "prior_raw_manifest_identity_mismatch"
            ],
            [qualified],
        )

    def test_item_revalidation_rejects_compact_semantic_mismatch(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        source_file = "papers/Fixture/Interface.lean"
        declaration = "theorem reviewed : True := by trivial"
        graph = {"schema": 1, "nodes": []}
        prior_context = self.context()
        current_context = self.context()
        current_context["olean_fingerprint"] = ["9" * 64, 30]
        current_context["audit_scope_fingerprint"] = "8" * 64
        current_context["semantic_module_fingerprints"] = [
            ["Fixture.Interface", ["9" * 64, 30]]
        ]
        prior_row = {
            "qualified_declaration": qualified,
            "source_file": source_file,
            "lean_source_declaration": declaration,
            "elaborated_signature_sha256": self.SIGNATURE,
            "semantic_dependency_sha256": self.DEPENDENCY,
            "elaborated_proposition_graph_sha256": (
                STORE.elaborated_proposition_graph_sha256(graph)
            ),
        }
        reattach = mock.Mock()
        seed = mock.Mock()
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=self.manifest(graph=graph),
                            context=prior_context,
                        )
                    ],
                )
                with mock.patch.object(
                    STORE,
                    "signature_manifest_item_revalidation_matches",
                    return_value=False,
                ) as matches:
                    accepted, diagnostics = (
                        STORE.prime_authenticated_manifest_store_with_item_revalidation(
                            root=paper_dir.parent,
                            paper_dir=paper_dir,
                            authenticated_prior_rows=[prior_row],
                            current_declarations={
                                qualified: {
                                    "source_file": source_file,
                                    "lean_source_declaration": declaration,
                                }
                            },
                            prior_contexts=[prior_context],
                            current_contexts=[current_context],
                            revalidate=mock.Mock(
                                return_value={
                                    qualified: {
                                        "semantic_dependency_graph": {"schema": 1},
                                        "elaborated_execution_state_refinement_shape": {
                                            "schema": 1
                                        },
                                    }
                                }
                            ),
                            reattach=reattach,
                            seed=seed,
                        )
                    )

        self.assertEqual(accepted, {})
        self.assertEqual(
            diagnostics["rejected_by_reason"][
                "manifest_item_semantics_changed"
            ],
            [qualified],
        )
        matches.assert_called_once()
        reattach.assert_called_once_with(
            paper_dir.parent, {}, timeout_seconds=300
        )
        seed.assert_not_called()

    def test_exact_context_resume_attestation_seeds_without_revalidation(self) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        manifest = self.resume_manifest()
        binding = self.resume_binding(qualified)
        reattach = mock.Mock(side_effect=lambda _root, manifests, **_kwargs: manifests)
        seed = mock.Mock(side_effect=lambda _root, _module, manifests, _pins, **_kwargs: set(manifests))
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with (
                digest_patch,
                dependency_patch,
                mock.patch.object(
                    STORE,
                    "run_lean_signature_manifest_revalidations",
                    side_effect=AssertionError("exact resume must not revalidate"),
                ) as revalidate,
            ):
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=manifest,
                            context=context,
                            authority_binding={"producer": "generic"},
                        )
                    ],
                )
                accepted, diagnostics = (
                    STORE.prime_exact_context_attested_resume_manifests(
                        root=paper_dir.parent,
                        paper_dir=paper_dir,
                        import_module="Fixture.Interface",
                        semantic_dependency_modules=("Fixture.Interface",),
                        current_context=context,
                        current_bindings={qualified: binding},
                        resume_records={
                            qualified: {"binding": binding, "manifest": manifest}
                        },
                        reattach=reattach,
                        seed=seed,
                    )
                )

        self.assertEqual(set(accepted), {qualified})
        self.assertEqual(diagnostics["seeded_count"], 1)
        self.assertEqual(
            diagnostics["store_status"], "validated_exact_context_resume_attestation"
        )
        revalidate.assert_not_called()
        reattach.assert_called_once()
        seed.assert_called_once()

    def test_interrupted_current_context_resume_requires_carrier_and_lean_revalidation(
        self,
    ) -> None:
        """A pre-publication checkpoint reuses only carrier-backed Lean output."""

        qualified = "Fixture.Interface.reviewed"
        prior_context = self.context()
        current_context = self.context()
        current_context["olean_fingerprint"] = ["9" * 64, 30]
        current_context["audit_scope_fingerprint"] = "8" * 64
        current_context["semantic_module_fingerprints"] = [
            ["Fixture.Interface", ["9" * 64, 30]]
        ]
        manifest = self.resume_manifest()
        binding = self.resume_binding(qualified)
        receipt = {
            "semantic_dependency_graph": manifest["semantic_dependency_graph"],
            "elaborated_execution_state_refinement_shape": manifest[
                "elaborated_execution_state_refinement_shape"
            ],
        }
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=manifest,
                            context=prior_context,
                            authority_binding={"producer": "generic"},
                        )
                    ],
                )
                authority_path = STORE.authenticated_manifest_authority_path(paper_dir)
                carrier_path = STORE.authenticated_manifest_carrier_path(paper_dir)
                authority_before = authority_path.read_text(encoding="utf-8")
                carrier_before = carrier_path.read_text(encoding="utf-8")
                revalidate = mock.Mock(return_value={qualified: receipt})
                reattach = mock.Mock(
                    side_effect=lambda _root, manifests, **_kwargs: manifests
                )
                seed = mock.Mock(
                    side_effect=lambda _root, _module, manifests, _pins, **_kwargs: set(
                        manifests
                    )
                )
                with mock.patch.object(
                    STORE,
                    "signature_manifest_item_revalidation_matches",
                    return_value=True,
                ) as matches:
                    accepted, diagnostics = (
                        STORE.prime_attested_resume_manifests_with_current_revalidation(
                            root=paper_dir.parent,
                            paper_dir=paper_dir,
                            import_module="Fixture.Interface",
                            semantic_dependency_modules=("Fixture.Interface",),
                            current_context=current_context,
                            current_bindings={qualified: binding},
                            resume_records={
                                qualified: {
                                    "manifest_cache_context_sha256": (
                                        STORE.signature_manifest_cache_context_sha256(
                                            current_context
                                        )
                                    ),
                                    "binding": binding,
                                    "manifest": manifest,
                                }
                            },
                            revalidate=revalidate,
                            reattach=reattach,
                            seed=seed,
                        )
                    )
                authority_after = authority_path.read_text(encoding="utf-8")
                carrier_after = carrier_path.read_text(encoding="utf-8")

        self.assertEqual(set(accepted), {qualified})
        self.assertEqual(
            diagnostics["store_status"], "validated_current_recovery_revalidation"
        )
        self.assertEqual(diagnostics["item_revalidation_requested_count"], 1)
        self.assertEqual(diagnostics["item_revalidated_count"], 1)
        revalidate.assert_called_once()
        matches.assert_called_once()
        reattach.assert_called_once()
        seed.assert_called_once()
        self.assertEqual(authority_after, authority_before)
        self.assertEqual(carrier_after, carrier_before)

    def test_interrupted_current_context_resume_rejects_stale_context_before_lean(
        self,
    ) -> None:
        qualified = "Fixture.Interface.reviewed"
        prior_context = self.context()
        current_context = self.context()
        current_context["olean_fingerprint"] = ["9" * 64, 30]
        current_context["audit_scope_fingerprint"] = "8" * 64
        current_context["semantic_module_fingerprints"] = [
            ["Fixture.Interface", ["9" * 64, 30]]
        ]
        manifest = self.resume_manifest()
        binding = self.resume_binding(qualified)
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            digest_patch, dependency_patch = self.patches()
            with digest_patch, dependency_patch:
                STORE.publish_authenticated_manifest_store(
                    paper_dir=paper_dir,
                    paper="Fixture",
                    candidates=[
                        self.candidate(
                            qualified,
                            manifest=manifest,
                            context=prior_context,
                            authority_binding={"producer": "generic"},
                        )
                    ],
                )
                revalidate = mock.Mock()
                seed = mock.Mock()
                accepted, diagnostics = (
                    STORE.prime_attested_resume_manifests_with_current_revalidation(
                        root=paper_dir.parent,
                        paper_dir=paper_dir,
                        import_module="Fixture.Interface",
                        semantic_dependency_modules=("Fixture.Interface",),
                        current_context=current_context,
                        current_bindings={qualified: binding},
                        resume_records={
                            qualified: {
                                "manifest_cache_context_sha256": (
                                    STORE.signature_manifest_cache_context_sha256(
                                        prior_context
                                    )
                                ),
                                "binding": binding,
                                "manifest": manifest,
                            }
                        },
                        revalidate=revalidate,
                        reattach=mock.Mock(),
                        seed=seed,
                    )
                )

        self.assertEqual(accepted, {})
        self.assertEqual(diagnostics["item_revalidation_requested_count"], 0)
        self.assertEqual(
            diagnostics["rejected_by_reason"]["resume_context_or_record_malformed"],
            [qualified],
        )
        revalidate.assert_not_called()
        seed.assert_not_called()

    def test_exact_context_resume_attestation_rejects_binding_context_and_payload_mismatches(
        self,
    ) -> None:
        qualified = "Fixture.Interface.reviewed"
        context = self.context()
        manifest = self.resume_manifest()
        binding = self.resume_binding(qualified)
        cases = {
            "binding": (
                context,
                {**binding, "lean_source_declaration": "theorem changed : True"},
                manifest,
                "resume_binding_changed",
            ),
            "context": (
                {
                    **context,
                    "olean_fingerprint": ["9" * 64, 10],
                    "semantic_module_fingerprints": [
                        ["Fixture.Interface", ["9" * 64, 10]]
                    ],
                },
                binding,
                manifest,
                None,
            ),
            "payload": (
                context,
                binding,
                {**manifest, "atoms": [{"ref": "changed", "role": "conclusion"}]},
                "resume_payload_not_attested",
            ),
        }
        for case, (current_context, resume_binding, resume_manifest, reason) in cases.items():
            with self.subTest(case=case), tempfile.TemporaryDirectory() as temporary:
                paper_dir = Path(temporary) / "Fixture"
                reattach = mock.Mock()
                seed = mock.Mock()
                digest_patch, dependency_patch = self.patches()
                with digest_patch, dependency_patch:
                    STORE.publish_authenticated_manifest_store(
                        paper_dir=paper_dir,
                        paper="Fixture",
                        candidates=[
                            self.candidate(
                                qualified,
                                manifest=manifest,
                                context=context,
                                authority_binding={"producer": "generic"},
                            )
                        ],
                    )
                    accepted, diagnostics = (
                        STORE.prime_exact_context_attested_resume_manifests(
                            root=paper_dir.parent,
                            paper_dir=paper_dir,
                            import_module="Fixture.Interface",
                            semantic_dependency_modules=("Fixture.Interface",),
                            current_context=current_context,
                            current_bindings={qualified: binding},
                            resume_records={
                                qualified: {
                                    "binding": resume_binding,
                                    "manifest": resume_manifest,
                                }
                            },
                            reattach=reattach,
                            seed=seed,
                        )
                    )

                self.assertEqual(accepted, {})
                self.assertEqual(diagnostics["seeded_count"], 0)
                if reason is not None:
                    self.assertIn(
                        qualified,
                        diagnostics["rejected_by_reason"].get(reason, []),
                    )
                reattach.assert_not_called()
                seed.assert_not_called()

    def test_refresh_enables_progress_and_manifest_store_publication(self) -> None:
        folder = Path("papers/Fixture")
        with mock.patch.object(DASHBOARD, "review_items_for_paper") as review:
            DASHBOARD.refresh_cached_review_rows(folder)

        review.assert_called_once()
        kwargs = review.call_args.kwargs
        self.assertFalse(kwargs["use_cache"])
        self.assertTrue(kwargs["require_current_signatures"])
        self.assertTrue(kwargs["publish_manifest_store"])
        self.assertTrue(callable(kwargs["progress"]))

    def test_successful_mutable_refresh_publishes_after_row_cache_write(self) -> None:
        events: list[str] = []
        progress: list[str] = []
        context = self.context()
        item = mock.Mock()
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            interface = folder / "Interface.lean"
            report = folder / "FINAL_VALIDATION_REPORT.md"
            with (
                mock.patch.object(
                    DASHBOARD,
                    "_cache_source_hashes",
                    return_value={"surface": "current"},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "current_review_signature_contexts",
                    return_value={"Interface.lean": context},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "prime_review_signature_manifest_store",
                    return_value={
                        "seeded_count": 0,
                        "fresh_required_count": 1,
                        "store_status": "validated",
                    },
                ),
                mock.patch.object(DASHBOARD, "review_source_file", return_value=interface),
                mock.patch.object(
                    DASHBOARD, "paper_relative_file", return_value=report
                ),
                mock.patch.object(
                    DASHBOARD, "parse_interface_items", return_value=[item]
                ),
                mock.patch.object(
                    DASHBOARD,
                    "write_cached_review_rows",
                    side_effect=lambda *_args, **_kwargs: events.append("write"),
                ),
                mock.patch.object(
                    DASHBOARD,
                    "publish_review_signature_manifest_store",
                    side_effect=lambda *_args, **_kwargs: (
                        events.append("publish") or {"Fixture.Interface.reviewed"}
                    ),
                ),
            ):
                items = DASHBOARD.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    require_current_signatures=True,
                    validated_configured_review_rows=(),
                    publish_manifest_store=True,
                    progress=progress.append,
                )

        self.assertEqual(items, [item])
        self.assertEqual(events, ["write", "publish"])
        self.assertTrue(
            any("authenticated manifest store published" in line for line in progress)
        )

    def test_mutable_refresh_compactly_revalidates_authenticated_prior_rows(self) -> None:
        """An ordinary refresh may seed only after item-level revalidation."""

        context = self.context()
        item = mock.Mock()
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            interface = folder / "Interface.lean"
            report = folder / "FINAL_VALIDATION_REPORT.md"
            with (
                mock.patch.object(
                    DASHBOARD,
                    "_cache_source_hashes",
                    return_value={"surface": "current"},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "current_review_signature_contexts",
                    return_value={"Interface.lean": context},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "prime_review_signature_manifest_store",
                    return_value={
                        "seeded_count": 0,
                        "fresh_required_count": 1,
                        "store_status": "skipped_without_independent_current_bindings",
                    },
                ) as primary_prime,
                mock.patch.object(
                    DASHBOARD,
                    "prime_review_signature_manifest_store_from_prior",
                    return_value={
                        "seeded_count": 1,
                        "fresh_required_count": 0,
                        "store_status": "validated_with_item_revalidation",
                    },
                ) as prior_prime,
                mock.patch.object(DASHBOARD, "review_source_file", return_value=interface),
                mock.patch.object(
                    DASHBOARD, "paper_relative_file", return_value=report
                ),
                mock.patch.object(
                    DASHBOARD, "parse_interface_items", return_value=[item]
                ),
                mock.patch.object(DASHBOARD, "write_cached_review_rows"),
            ):
                items = DASHBOARD.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    require_current_signatures=True,
                )

        self.assertEqual(items, [item])
        primary_prime.assert_called_once()
        prior_prime.assert_called_once_with(
            folder, {"Interface.lean": context}
        )

    def test_frozen_refresh_never_reads_prior_mutable_cache(self) -> None:
        """Frozen closeouts stay within their transaction-owned inputs."""

        context = self.context()
        item = mock.Mock()
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            interface = folder / "Interface.lean"
            status = folder / "status.json"
            report = folder / "FINAL_VALIDATION_REPORT.md"
            inputs = DASHBOARD.DashboardAuditInputs.from_file_snapshots(
                folder.parent,
                {
                    interface: b"theorem reviewed : True := by trivial\n",
                    status: b"{}\n",
                    report: b"",
                },
            )
            with (
                mock.patch.object(
                    DASHBOARD,
                    "current_review_signature_contexts",
                    return_value={"Interface.lean": context},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "prime_review_signature_manifest_store",
                    return_value={
                        "seeded_count": 0,
                        "fresh_required_count": 1,
                        "store_status": "validated",
                    },
                ),
                mock.patch.object(
                    DASHBOARD, "prime_review_signature_manifest_store_from_prior"
                ) as prior_prime,
                mock.patch.object(DASHBOARD, "review_source_file", return_value=interface),
                mock.patch.object(
                    DASHBOARD, "paper_relative_file", return_value=report
                ),
                mock.patch.object(
                    DASHBOARD, "parse_interface_items", return_value=[item]
                ),
            ):
                rows = DASHBOARD.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    require_current_signatures=True,
                    persist_cache_rebind=False,
                    audit_inputs=inputs,
                    validated_configured_review_rows=(),
                )

        self.assertEqual(rows, [item])
        prior_prime.assert_not_called()

    def test_strict_dashboard_does_not_publish_persistent_manifest_store(self) -> None:
        events: list[str] = []
        context = self.context()
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            interface = folder / "Interface.lean"
            report = folder / "FINAL_VALIDATION_REPORT.md"
            with (
                mock.patch.object(
                    DASHBOARD,
                    "_cache_source_hashes",
                    side_effect=lambda _folder, **_kwargs: {"surface": "current"},
                ),
                mock.patch.object(
                    DASHBOARD,
                    "current_review_signature_contexts",
                    side_effect=lambda _folder, **_kwargs: (
                        events.append("context") or {"Interface.lean": context}
                    ),
                ),
                mock.patch.object(
                    DASHBOARD,
                    "prime_review_signature_manifest_store",
                    side_effect=lambda _folder, _contexts, **_kwargs: (
                        events.append("prime") or {}
                    ),
                ),
                mock.patch.object(
                    DASHBOARD,
                    "review_source_file",
                    return_value=interface,
                ),
                mock.patch.object(
                    DASHBOARD,
                    "paper_relative_file",
                    return_value=report,
                ),
                mock.patch.object(
                    DASHBOARD,
                    "parse_interface_items",
                    side_effect=lambda *_args, **_kwargs: (
                        events.append("parse") or []
                    ),
                ),
                mock.patch.object(
                    DASHBOARD,
                    "write_cached_review_rows",
                    side_effect=lambda *_args, **_kwargs: events.append("write"),
                ),
                mock.patch.object(
                    DASHBOARD,
                    "publish_review_signature_manifest_store",
                    side_effect=lambda *_args, **_kwargs: (
                        events.append("publish") or set()
                    ),
                ),
            ):
                items = DASHBOARD.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    require_current_signatures=True,
                )

        self.assertEqual(items, [])
        self.assertEqual(
            events,
            ["context", "prime", "parse", "context", "write"],
        )


if __name__ == "__main__":
    unittest.main()
