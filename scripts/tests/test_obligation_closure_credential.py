from __future__ import annotations

import json
import copy
import subprocess
import sys
import tempfile
import threading
import unittest
from contextlib import ExitStack, nullcontext
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import obligation_closure_credential as credential
from scripts.obligation_evidence_issuance import (
    TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
    issue_obligation_evidence_attestation,
)
from scripts.obligation_evidence_store import (
    ObligationEvidenceStoreError,
    load_lean_import_closure_preimage,
    load_accepted_obligation_graph,
    load_paper_obligation_bundle,
    store_accepting_paper_obligation_bundle,
    store_accepted_obligation_graph,
    store_lean_import_closure_preimage,
    store_paper_obligation_bundle,
)
from scripts.obligation_paper_bundle import (
    paper_obligation_terminal_verification_sha256,
)
from scripts.tests.test_obligation_paper_index import PaperObligationIndexTests, sha
from scripts.tests.test_accepted_obligation_graph import strict_authority
from scripts.obligation_evidence_contracts import (
    PAPER_CLOSURE_CONTRACT,
    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT,
)


class ObligationClosureCredentialTests(unittest.TestCase):
    def test_terminal_recovery_forwards_authenticated_prerequisite_owners(
        self,
    ) -> None:
        paper = "Fixture"
        accepted_closure_sha256 = sha("1")
        current_closure_sha256 = sha("9")
        toolchain_sha256 = sha("2")
        proof_endpoint = sha("3")
        build_leaf = SimpleNamespace(
            semantic_payload={
                "target_declaration_sha256s": [proof_endpoint],
                "build_command_sha256": credential.portable_evidence_sha256(
                    {"schema": 1, "argv": ["lake", "build", paper]}
                ),
                "lean_import_closure_sha256": accepted_closure_sha256,
                "toolchain_sha256": toolchain_sha256,
            }
        )
        loaded = SimpleNamespace(
            paper_index=SimpleNamespace(
                leaf_sha256s_by_kind={
                    credential.ObligationKind.BUILD: ("build",)
                },
                route_leaf_sha256s_by_source_item={
                    "claim": {"proof_endpoint": (proof_endpoint,)}
                },
            ),
            graph=SimpleNamespace(leaves={"build": build_leaf}),
        )
        accepted_closure = {
            "build_controls": [
                {"path": "lean-toolchain", "sha256": toolchain_sha256}
            ]
        }
        current_closure = {
            "build_controls": [
                {"path": "lean-toolchain", "sha256": toolchain_sha256}
            ]
        }
        owners = {"Fixture.Model": "model_source"}
        provider = SimpleNamespace(
            adopt_lean_import_closure_payload=mock.Mock(),
            finalize_unchanged=mock.Mock(return_value=True),
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            audit = root / "papers" / paper / "audit"
            audit.mkdir(parents=True)
            status_path = audit.parent / "status.json"
            closure_path = audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json"
            paper_ledger = audit / "paper_semantic_prerequisites.json"
            library_ledger = audit / "library_semantic_review.json"
            semantic_path = audit / "paper_statement_map.json"
            for path in (
                status_path,
                closure_path,
                paper_ledger,
                library_ledger,
                semantic_path,
            ):
                path.write_text("{}\n", encoding="utf-8")

            def load_json(path: Path, _label: str) -> dict:
                if path == status_path:
                    return {"build_target": f"lake build {paper}"}
                if path == closure_path:
                    return {"lean_import_closure": current_closure}
                raise AssertionError(f"unexpected JSON input: {path}")

            with (
                mock.patch.object(credential, "_json", side_effect=load_json),
                mock.patch.object(
                    credential,
                    "validated_lean_import_closure_receipt_payload",
                    return_value={
                        "lean_import_closure": current_closure,
                        "lean_import_closure_sha256": current_closure_sha256,
                    },
                ),
                mock.patch.object(
                    credential,
                    "validated_lean_import_closure_payload",
                    return_value=current_closure,
                ),
                mock.patch.object(
                    credential,
                    "lean_import_closure_payload_sha256",
                    return_value=current_closure_sha256,
                ),
                mock.patch.object(
                    credential,
                    "load_lean_import_closure_preimage",
                    return_value=accepted_closure,
                ),
                mock.patch.object(
                    credential,
                    "lean_import_closure_source_only_recovery_problem",
                    return_value="",
                ),
                mock.patch(
                    "scripts.lean_signature_manifest."
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    credential,
                    "_recorded_issued_review_metadata",
                    return_value=({}, {}, owners),
                ) as recorded,
                mock.patch.object(
                    credential,
                    "revalidate_terminal_lean_semantics",
                    return_value=(provider, (semantic_path,)),
                ) as revalidate,
            ):
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "build leaf Lean import closure is stale",
                ):
                    credential._validate_current_build(
                        root,
                        paper,
                        loaded,
                        SimpleNamespace(),
                        accepted_graph_external_artifact_authority=False,
                    )
                revalidate.assert_not_called()
                result = credential._validate_current_build(
                    root,
                    paper,
                    loaded,
                    SimpleNamespace(),
                    accepted_graph_external_artifact_authority=True,
                )
                self.assertTrue(result[0].finalize_unchanged())
                closure_path.write_text('{"post_return":true}\n', encoding="utf-8")
                self.assertFalse(result[0].finalize_unchanged())
                closure_path.write_text("{}\n", encoding="utf-8")
                paper_ledger.write_text("{}\n", encoding="utf-8")

                def mutate_owner_input(*_args: object, **_kwargs: object):
                    paper_ledger.write_text('{"changed":true}\n', encoding="utf-8")
                    return provider, (semantic_path,)

                revalidate.side_effect = mutate_owner_input
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "source ownership changed during terminal verification",
                ):
                    credential._validate_current_build(
                        root,
                        paper,
                        loaded,
                        SimpleNamespace(),
                        accepted_graph_external_artifact_authority=True,
                    )

                paper_ledger.write_text("{}\n", encoding="utf-8")
                closure_path.write_text("{}\n", encoding="utf-8")

                def mutate_current_carrier(*_args: object, **_kwargs: object):
                    closure_path.write_text('{"changed":true}\n', encoding="utf-8")
                    return provider, (semantic_path,)

                revalidate.side_effect = mutate_current_carrier
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "receipt changed during terminal verification",
                ):
                    credential._validate_current_build(
                        root,
                        paper,
                        loaded,
                        SimpleNamespace(),
                        accepted_graph_external_artifact_authority=True,
                    )

        self.assertIs(result[0].delegate, provider)
        self.assertEqual(
            set(result[1]),
            {
                status_path,
                closure_path,
                paper_ledger,
                library_ledger,
                semantic_path,
            },
        )
        self.assertTrue(result[2])
        self.assertEqual(recorded.call_count, 3)
        self.assertEqual(
            revalidate.call_args.kwargs[
                "authenticated_prerequisite_source_items_by_declaration"
            ],
            owners,
        )
        self.assertIs(
            revalidate.call_args.kwargs["build_input_provider"], provider
        )
        self.assertIs(
            revalidate.call_args.kwargs["accepted_import_closure"],
            accepted_closure,
        )
        self.assertIs(
            revalidate.call_args.kwargs["current_import_closure"],
            current_closure,
        )

    def test_retained_closure_preimage_is_authenticated_by_selected_digest(
        self,
    ) -> None:
        repository = Path(__file__).resolve().parents[2]
        retained = next(
            (
                repository
                / "papers/GKGMM19IterativeLocalVoting/audit/obligation_evidence/"
                "lean_import_closures/sha256"
            ).glob("*/*.json")
        )
        closure = json.loads(retained.read_bytes())
        digest = credential.lean_import_closure_payload_sha256(closure)
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            stored = store_lean_import_closure_preimage(
                root,
                "Fixture",
                digest,
                closure,
            )
            self.assertEqual(
                dict(load_lean_import_closure_preimage(root, "Fixture", digest)),
                closure,
            )
            stored.write_text("{}\n", encoding="utf-8")
            with self.assertRaises(ObligationEvidenceStoreError):
                load_lean_import_closure_preimage(root, "Fixture", digest)

    def test_source_only_recovery_preserves_build_and_dependency_boundary(
        self,
    ) -> None:
        repository = Path(__file__).resolve().parents[2]
        retained = next(
            (
                repository
                / "papers/GKGMM19IterativeLocalVoting/audit/obligation_evidence/"
                "lean_import_closures/sha256"
            ).glob("*/*.json")
        )
        accepted = json.loads(retained.read_bytes())
        current = copy.deepcopy(accepted)
        current["sources"][0]["sha256"] = sha("f")
        current["sources"][0]["byte_length"] += 1
        self.assertEqual(
            credential.lean_import_closure_source_only_recovery_problem(
                accepted, current
            ),
            "",
        )
        mutations = (
            (
                "lake-manifest package versions",
                lambda value: value["build_controls"][1].update(
                    {"sha256": sha("e")}
                ),
                "build_controls",
            ),
            (
                "toolchain",
                lambda value: value["build_controls"][0].update(
                    {"sha256": sha("d")}
                ),
                "build_controls",
            ),
            (
                "external artifacts",
                lambda value: value.update(
                    {"external_module_artifacts_sha256": sha("c")}
                ),
                "external_module_artifacts_sha256",
            ),
            (
                "Lake routing",
                lambda value: value["lake_routing"]["package_configuration"].update(
                    {"name": "DifferentPackage"}
                ),
                "lake_routing",
            ),
        )
        for label, mutate, expected_field in mutations:
            with self.subTest(label=label):
                changed = copy.deepcopy(current)
                mutate(changed)
                self.assertIn(
                    expected_field,
                    credential.lean_import_closure_source_only_recovery_problem(
                        accepted, changed
                    ),
                )

    def test_publication_rejects_portable_or_caller_constructed_authority(self) -> None:
        with mock.patch.object(
            credential,
            "load_paper_obligation_bundle",
        ) as load_bundle:
            with self.assertRaisesRegex(
                credential.ObligationClosureCredentialError,
                "current in-process pass",
            ):
                credential.publish_current_obligation_bundle_as_accepted_graph(
                    Path("/repository"),
                    "Fixture",
                    current_closeout_pass=strict_authority(),
                )
        load_bundle.assert_not_called()

    def test_publication_retains_exact_build_closure_before_pointer_selection(
        self,
    ) -> None:
        repository = Path(__file__).resolve().parents[2]
        retained = next(
            (
                repository
                / "papers/GKGMM19IterativeLocalVoting/audit/obligation_evidence/"
                "lean_import_closures/sha256"
            ).glob("*/*.json")
        )
        closure = json.loads(retained.read_bytes())
        digest = credential.lean_import_closure_payload_sha256(closure)
        provider = SimpleNamespace(
            owns_exact_lean_import_closure_payload=lambda value: value == closure
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            pointer = credential.current_accepted_graph_path(root, "Fixture")
            pointer.parent.mkdir(parents=True)
            pointer.write_bytes(b"old selection\n")
            accepted_pass = SimpleNamespace(
                repository_root=root.resolve(),
                paper="Fixture",
                build_input_provider=provider,
                final_holistic_surface=lambda: {"paper": "Fixture"},
                lean_closure_projection=lambda: {
                    "lean_import_closure": closure
                },
            )
            build_leaf = SimpleNamespace(
                semantic_payload={"lean_import_closure_sha256": sha("0")}
            )
            loaded = SimpleNamespace(
                paper_index=SimpleNamespace(
                    leaf_sha256s_by_kind={
                        credential.ObligationKind.BUILD: ("build",)
                    }
                ),
                graph=SimpleNamespace(leaves={"build": build_leaf}),
            )
            controls = SimpleNamespace(preflight=SimpleNamespace())
            authority = strict_authority()

            def common_patches():
                return (
                    mock.patch.object(
                        credential,
                        "validate_current_closeout_pass",
                        return_value=accepted_pass,
                    ),
                    mock.patch.object(
                        credential,
                        "current_closeout_pass_authority",
                        return_value=authority,
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_audit_surface_contract_is_supported",
                        return_value=True,
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_audit_surface_sha256",
                        return_value=sha("6"),
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_source_assurance_v2_sha256",
                        return_value=sha("7"),
                    ),
                    mock.patch.object(
                        credential,
                        "load_paper_obligation_bundle",
                        return_value=loaded,
                    ),
                    mock.patch.object(
                        credential,
                        "_prepare_current_controls",
                        return_value=controls,
                    ),
                )

            with ExitStack() as stack:
                for patcher in common_patches():
                    stack.enter_context(patcher)
                select = stack.enter_context(mock.patch.object(
                    credential, "store_accepted_obligation_graph"
                ))
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "disagrees with the build leaf",
                ):
                    credential.publish_current_obligation_bundle_as_accepted_graph(
                        root,
                        "Fixture",
                        current_closeout_pass=accepted_pass,
                    )
            select.assert_not_called()
            self.assertEqual(pointer.read_bytes(), b"old selection\n")

            build_leaf.semantic_payload["lean_import_closure_sha256"] = digest
            order: list[str] = []

            class StopAfterSelection(RuntimeError):
                pass

            with ExitStack() as stack:
                for patcher in common_patches():
                    stack.enter_context(patcher)
                stack.enter_context(mock.patch.object(
                    credential,
                    "store_lean_import_closure_preimage",
                    side_effect=lambda *_args, **_kwargs: (
                        order.append("preimage") or retained
                    ),
                ))
                stack.enter_context(mock.patch.object(
                    credential,
                    "store_accepted_obligation_graph",
                    side_effect=lambda *_args, **_kwargs: (
                        order.append("selection")
                        or (_ for _ in ()).throw(StopAfterSelection())
                    ),
                ))
                with self.assertRaises(StopAfterSelection):
                    credential.publish_current_obligation_bundle_as_accepted_graph(
                        root,
                        "Fixture",
                        current_closeout_pass=accepted_pass,
                    )
            self.assertEqual(order, ["preimage", "selection"])

    def test_terminal_migration_lock_blocks_interleaved_publication(self) -> None:
        authority = strict_authority()
        migration_entered = threading.Event()
        release_migration = threading.Event()
        publication_attempted = threading.Event()
        publication_entered = threading.Event()
        thread_errors: list[BaseException] = []

        class PublicationReachedBundleLoad(RuntimeError):
            pass

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            accepted_pass = SimpleNamespace(
                repository_root=root.resolve(),
                paper="Fixture",
                build_input_provider=SimpleNamespace(),
                final_holistic_surface=lambda: {"paper": "Fixture"},
            )

            def hold_migration(locked_root: Path, paper: str) -> Path:
                self.assertEqual((locked_root, paper), (root.resolve(), "Fixture"))
                migration_entered.set()
                if not release_migration.wait(2):
                    raise AssertionError("test did not release terminal migration")
                return root / "papers" / paper / "FINAL_CLOSURE_RECEIPT.md"

            def load_after_lock(*_args, **_kwargs):
                publication_entered.set()
                raise PublicationReachedBundleLoad()

            def run_migration() -> None:
                try:
                    credential.migrate_accepted_terminal_source_assurance_v1_to_v2(
                        root, "Fixture"
                    )
                except BaseException as exc:  # Preserve worker failures for assertion.
                    thread_errors.append(exc)

            def run_publication() -> None:
                try:
                    credential.publish_current_obligation_bundle_as_accepted_graph(
                        root,
                        "Fixture",
                        current_closeout_pass=accepted_pass,
                    )
                except PublicationReachedBundleLoad:
                    return
                except BaseException as exc:  # Preserve worker failures for assertion.
                    thread_errors.append(exc)

            with (
                mock.patch.object(
                    credential,
                    "_migrate_accepted_terminal_source_assurance_v1_to_v2_under_lock",
                    side_effect=hold_migration,
                ),
                mock.patch.object(
                    credential,
                    "validate_current_closeout_pass",
                    return_value=accepted_pass,
                ),
                mock.patch.object(
                    credential,
                    "current_closeout_pass_authority",
                    return_value=authority,
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_audit_surface_contract_is_supported",
                    return_value=True,
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_audit_surface_sha256",
                    return_value=sha("6"),
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_v2_sha256",
                    side_effect=lambda _surface: (
                        publication_attempted.set() or sha("7")
                    ),
                ),
                mock.patch.object(
                    credential,
                    "load_paper_obligation_bundle",
                    side_effect=load_after_lock,
                ),
            ):
                migration = threading.Thread(target=run_migration)
                publication = threading.Thread(target=run_publication)
                migration.start()
                self.assertTrue(migration_entered.wait(1))
                publication.start()
                self.assertTrue(publication_attempted.wait(1))
                self.assertFalse(publication_entered.wait(0.1))
                release_migration.set()
                migration.join(2)
                publication.join(2)

            self.assertFalse(migration.is_alive())
            self.assertFalse(publication.is_alive())
            self.assertTrue(publication_entered.is_set())
            self.assertEqual(thread_errors, [])

    def test_terminal_selection_lock_preserves_body_oserror_and_releases(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            body_error = OSError("publication body failed")
            try:
                with credential._terminal_selection_lock(root, "Fixture"):
                    raise body_error
            except OSError as exc:
                self.assertIs(exc, body_error)
            else:
                self.fail("terminal lock relabeled or swallowed the body OSError")

            reacquired = False
            with credential._terminal_selection_lock(root, "Fixture"):
                reacquired = True
            self.assertTrue(reacquired)

    def test_graph_controls_do_not_require_predecessor_correspondence_worksheet(
        self,
    ) -> None:
        preflight = mock.Mock()
        with mock.patch.object(
            credential,
            "_json",
            side_effect=[{"paper": "Fixture"}, {}, {}],
        ), mock.patch.object(
            credential,
            "structural_obligation_preflight",
            return_value=preflight,
        ) as structural:
            result, _paths, _source_map = credential._current_preflight(
                Path("/tmp/fixture"), "Fixture"
            )

        self.assertIs(result, preflight)
        preflight.require_current.assert_called_once_with()
        self.assertFalse(
            structural.call_args.kwargs["require_source_spec_correspondence"]
        )
        self.assertFalse(
            structural.call_args.kwargs["require_prerequisite_ledger_bindings"]
        )
        self.assertEqual(
            _paths,
            (Path("/tmp/fixture/papers/Fixture/audit/paper_statement_map.json"),),
        )

    def test_import_does_not_load_terminal_recovery_or_presentation(self) -> None:
        root = Path(__file__).resolve().parents[2]
        process = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import json, sys; "
                    "import scripts.obligation_closure_credential; "
                    "print(json.dumps([name for name in ("
                    "'scripts.terminal_lean_semantic_revalidation', "
                    "'scripts.obligation_current_material', "
                    "'scripts.review_dashboard', "
                    "'scripts.audit_evidence_integrity') if name in sys.modules]))"
                ),
            ],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), [])

    def fixture(self):
        graph = PaperObligationIndexTests().complete_graph()
        index, preflight = PaperObligationIndexTests().complete_index(graph)
        terminal = paper_obligation_terminal_verification_sha256(index, graph)
        terminal_issuances = tuple(
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
                authority_sha256=sha("4"),
                evidence_record_sha256=terminal,
            )
            for leaf in graph.leaves.values()
        )
        legacy_issuances = tuple(
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("5"),
                authority_sha256=sha("6"),
                evidence_record_sha256=sha("7"),
            )
            for leaf in graph.leaves.values()
        )
        return graph, index, preflight, terminal_issuances, legacy_issuances

    def test_schema5_receipt_is_only_a_pointer_to_accepting_bundle(self) -> None:
        graph, index, preflight, issuances, _legacy = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            store_accepting_paper_obligation_bundle(
                root,
                "Fixture",
                index,
                graph,
                issuances,
                preflight=preflight,
            )
            loaded = load_paper_obligation_bundle(root, "Fixture")
            payload = credential._receipt_payload(root, "Fixture", loaded)
            receipt_path = folder / "FINAL_CLOSURE_RECEIPT.md"
            receipt_path.write_text(
                credential.render_obligation_closure_receipt(payload),
                encoding="utf-8",
            )
            controls = SimpleNamespace()
            with (
                mock.patch.object(
                    credential,
                    "_prepare_current_controls",
                    return_value=controls,
                ),
                mock.patch.object(credential, "_finalize_controls") as finalize,
            ):
                verified = credential.validate_obligation_closure_receipt(
                    root,
                    "Fixture",
                    receipt_path=receipt_path,
                    payload=payload,
                )
            finalize.assert_called_once_with(controls)
            self.assertEqual(verified.graph_sha256, graph.graph_sha256)
            self.assertFalse(payload["acceptance_credential"])
            self.assertTrue(loaded.bundle.acceptance_credential)

    def test_schema6_receipt_is_only_a_view_of_the_accepted_graph(self) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            store_accepted_obligation_graph(
                root,
                "Fixture",
                index,
                graph,
                preflight=preflight,
                strict_closeout_authority=strict_authority(),
                final_holistic_audit_surface_sha256=sha("6"),
                source_assurance_sha256=sha("7"),
            )
            accepted = load_accepted_obligation_graph(
                root,
                "Fixture",
                preflight=preflight,
                authenticated_authority_sha256s=[sha("4")],
            )
            payload = credential._accepted_graph_receipt_payload(
                root, "Fixture", accepted.graph_sha256
            )
            receipt_path = folder / "FINAL_CLOSURE_RECEIPT.md"
            receipt_path.write_text(
                credential.render_obligation_closure_receipt(payload),
                encoding="utf-8",
            )
            controls = SimpleNamespace(
                loaded=accepted,
                preflight=preflight,
                authority_sha256s=(sha("4"),),
                terminal_validation_route="lean_semantic_recovery",
                terminal_validation_detail=(
                    "Lean import-closure source bytes changed: Fixture.Support.lean"
                ),
            )
            with (
                mock.patch.object(
                    credential,
                    "_prepare_accepted_graph_controls",
                    return_value=controls,
                ),
                mock.patch.object(credential, "_finalize_controls") as finalize,
                mock.patch.object(
                    credential,
                    "_selected_accepted_graph_from_receipt",
                    side_effect=AssertionError(
                        "schema-6 validation must not load the accepted graph twice"
                    ),
                ),
            ):
                verified = credential.validate_obligation_closure_receipt(
                    root,
                    "Fixture",
                    receipt_path=receipt_path,
                    payload=payload,
                )
            finalize.assert_called_once_with(controls)
            self.assertEqual(verified.credential_sha256, accepted.graph_sha256)
            self.assertEqual(verified.graph_sha256, graph.graph_sha256)
            self.assertIsNone(verified.bundle_sha256)
            self.assertEqual(
                verified.terminal_validation_route, "lean_semantic_recovery"
            )
            self.assertIn(
                "Fixture.Support.lean", verified.terminal_validation_detail
            )
            self.assertFalse(payload["acceptance_credential"])

    def test_schema6_acceptance_objects_are_identical_across_checkout_roots(
        self,
    ) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        snapshots = []
        with (
            tempfile.TemporaryDirectory() as first,
            tempfile.TemporaryDirectory() as second,
        ):
            for temp_dir in (first, second):
                root = Path(temp_dir)
                folder = root / "papers" / "Fixture"
                folder.mkdir(parents=True)
                store_accepted_obligation_graph(
                    root,
                    "Fixture",
                    index,
                    graph,
                    preflight=preflight,
                    strict_closeout_authority=strict_authority(),
                    final_holistic_audit_surface_sha256=sha("6"),
                    source_assurance_sha256=sha("7"),
                )
                evidence = folder / "audit" / "obligation_evidence"
                snapshot = {
                    path.relative_to(evidence).as_posix(): path.read_bytes()
                    for path in sorted(evidence.rglob("*.json"))
                }
                self.assertTrue(snapshot)
                self.assertTrue(
                    all(
                        str(root).encode() not in payload
                        for payload in snapshot.values()
                    )
                )
                snapshots.append(snapshot)

        self.assertEqual(snapshots[0], snapshots[1])

    def test_schema6_preflight_loads_current_pointer_once_and_checks_receipt_hash(
        self,
    ) -> None:
        preflight = SimpleNamespace()
        current = SimpleNamespace(graph_sha256=sha("1"))
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            with (
                mock.patch.object(
                    credential,
                    "_current_preflight",
                    return_value=(preflight, (), {}),
                ),
                mock.patch.object(
                    credential,
                    "_validate_current_source",
                    return_value=None,
                ),
                mock.patch.object(
                    credential,
                    "_registered_engine_authorities",
                    return_value=(sha("2"), (sha("2"),)),
                ),
                mock.patch.object(
                    credential,
                    "load_accepted_obligation_graph",
                    return_value=current,
                ) as load,
                mock.patch.object(
                    credential,
                    "_validate_current_build",
                    side_effect=AssertionError(
                        "receipt mismatch must stop before build validation"
                    ),
                ),
            ):
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "does not select the current accepted graph",
                ):
                    credential._prepare_accepted_graph_controls(
                        root,
                        "Fixture",
                        graph_sha256=sha("3"),
                    )

            load.assert_called_once_with(
                root,
                "Fixture",
                preflight=preflight,
                authenticated_authority_sha256s=(sha("2"),),
                require_current_aggregate_identity=False,
            )

    def test_recorded_card_surface_prefers_explicit_routes_over_shared_atoms(
        self,
    ) -> None:
        shared_atom = sha("1")
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                routes=(
                    SimpleNamespace(
                        source_item_id="definition_left",
                        semantic_review_declaration="Fixture.left",
                        semantic_declarations=("Fixture.left",),
                    ),
                    SimpleNamespace(
                        source_item_id="definition_right",
                        semantic_review_declaration="Fixture.right",
                        semantic_declarations=("Fixture.right",),
                    ),
                )
            )
        )
        current = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "definition_left": {"source_atom": (shared_atom,)},
                    "definition_right": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.left": {"source_atom": (shared_atom,)},
                    "Fixture.right": {"source_atom": (shared_atom,)},
                },
            )
        )

        projected = credential._recorded_card_review_declarations_by_source_item(
            current, preflight
        )

        self.assertEqual(
            projected,
            {
                "definition_left": ("Fixture.left",),
                "definition_right": ("Fixture.right",),
            },
        )

    def test_recorded_card_surface_rejects_ambiguous_unrouted_prerequisite(
        self,
    ) -> None:
        shared_atom = sha("1")
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                routes=(
                    SimpleNamespace(
                        source_item_id="definition_left",
                        semantic_review_declaration="Fixture.left",
                        semantic_declarations=("Fixture.left",),
                    ),
                    SimpleNamespace(
                        source_item_id="definition_right",
                        semantic_review_declaration="Fixture.right",
                        semantic_declarations=("Fixture.right",),
                    ),
                )
            )
        )
        current = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "definition_left": {"source_atom": (shared_atom,)},
                    "definition_right": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.recursive_helper": {"source_atom": (shared_atom,)},
                },
            )
        )

        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "do not resolve to one source item",
        ):
            credential._recorded_card_review_declarations_by_source_item(
                current, preflight
            )

    def test_recorded_card_surface_uses_authenticated_owner_before_atom_fallback(
        self,
    ) -> None:
        shared_atom = sha("1")
        preflight = SimpleNamespace(route_set=SimpleNamespace(routes=()))
        current = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "definition_left": {"source_atom": (shared_atom,)},
                    "definition_right": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.recursive_helper": {"source_atom": (shared_atom,)}
                },
            )
        )

        projected = credential._recorded_card_review_declarations_by_source_item(
            current,
            preflight,
            authenticated_prerequisite_source_items_by_declaration={
                "Fixture.recursive_helper": "definition_left"
            },
        )

        self.assertEqual(
            projected,
            {"definition_left": ("Fixture.recursive_helper",)},
        )

    def test_recorded_card_surface_rejects_authenticated_owner_conflicting_with_route(
        self,
    ) -> None:
        shared_atom = sha("1")
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                routes=(
                    SimpleNamespace(
                        source_item_id="definition_left",
                        semantic_review_declaration="Fixture.recursive_helper",
                        semantic_declarations=("Fixture.recursive_helper",),
                    ),
                )
            )
        )
        current = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "definition_left": {"source_atom": (shared_atom,)},
                    "definition_right": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.recursive_helper": {"source_atom": (shared_atom,)}
                },
            )
        )

        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "source owner conflicts with typed route",
        ):
            credential._recorded_card_review_declarations_by_source_item(
                current,
                preflight,
                authenticated_prerequisite_source_items_by_declaration={
                    "Fixture.recursive_helper": "definition_right"
                },
            )

    def test_recorded_card_surface_allows_shared_typed_route_owner(
        self,
    ) -> None:
        shared_atom = sha("1")
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                routes=(
                    SimpleNamespace(
                        source_item_id="definition_left",
                        semantic_review_declaration="Fixture.shared",
                        semantic_declarations=("Fixture.shared",),
                    ),
                    SimpleNamespace(
                        source_item_id="definition_right",
                        semantic_review_declaration="Fixture.shared",
                        semantic_declarations=("Fixture.shared",),
                    ),
                )
            )
        )
        current = SimpleNamespace(
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "definition_left": {"source_atom": (shared_atom,)},
                    "definition_right": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.shared": {"source_atom": (shared_atom,)}
                },
            )
        )

        projected = credential._recorded_card_review_declarations_by_source_item(
            current,
            preflight,
            authenticated_prerequisite_source_items_by_declaration={
                "Fixture.shared": "definition_left"
            },
        )

        self.assertEqual(
            projected,
            {
                "definition_left": ("Fixture.shared",),
                "definition_right": ("Fixture.shared",),
            },
        )

    def test_recorded_graph_projection_never_checks_live_source_or_lean(self) -> None:
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                result_specifications=lambda: ("Fixture.claimSpec",)
            )
        )
        current = SimpleNamespace(
            graph_sha256=sha("1"),
            paper_index=SimpleNamespace(
                prerequisite_leaf_sha256s_by_declaration={"Fixture.Model": {}}
            ),
        )
        payload = {"schema": 6}
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            with (
                mock.patch.object(
                    credential,
                    "_current_preflight",
                    return_value=(preflight, (), {}),
                ),
                mock.patch.object(
                    credential,
                    "_recorded_engine_authorities",
                    return_value=(sha("2"),),
                ),
                mock.patch.object(
                    credential,
                    "_selected_accepted_graph_from_receipt",
                    return_value=current,
                ) as selected,
                mock.patch.object(
                    credential,
                    "_recorded_source_lean_verdicts_by_source_item",
                    return_value={"claim": "matches"},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_source_input_bundles_by_source_item",
                    return_value={"claim": sha("9")},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_review_declarations_by_source_item",
                    return_value={"claim": ("Fixture.claimSpec",)},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_card_review_declarations_by_source_item",
                    return_value={"claim": ("Fixture.Model", "Fixture.claimSpec")},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_claim_semantic_targets_by_specification",
                    return_value={"Fixture.claimSpec": sha("3")},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_prerequisite_semantic_targets_by_declaration",
                    return_value={"Fixture.Model": sha("4")},
                ),
                mock.patch.object(
                    credential,
                    "_recorded_issued_review_metadata",
                    return_value=(
                        {"Fixture.claimSpec": {"reason": "Recorded reason"}},
                        {"Fixture.Model": {"reason": "Recorded prerequisite"}},
                        {"Fixture.Model": "model_source"},
                    ),
                ),
                mock.patch.object(
                    credential,
                    "_validate_current_source",
                    side_effect=AssertionError("display projection read source bytes"),
                ),
                mock.patch.object(
                    credential,
                    "_validate_current_build",
                    side_effect=AssertionError("display projection launched Lean"),
                ),
            ):
                result = credential.validate_nonaccepting_recorded_graph_projection(
                    root, "Fixture", payload
                )

        self.assertEqual(result.graph_sha256, sha("1"))
        self.assertEqual(
            result.review_declarations_by_source_item,
            {"claim": ("Fixture.claimSpec",)},
        )
        self.assertEqual(
            result.card_review_declarations_by_source_item,
            {"claim": ("Fixture.Model", "Fixture.claimSpec")},
        )
        self.assertEqual(
            result.source_lean_verdicts_by_source_item, {"claim": "matches"}
        )
        self.assertEqual(
            result.source_input_bundle_sha256s_by_source_item,
            {"claim": sha("9")},
        )
        self.assertEqual(
            result.claim_semantic_target_sha256s_by_specification,
            {"Fixture.claimSpec": sha("3")},
        )
        self.assertEqual(
            result.prerequisite_semantic_target_sha256s_by_declaration,
            {"Fixture.Model": sha("4")},
        )
        self.assertEqual(
            result.source_review_metadata_by_specification,
            {"Fixture.claimSpec": {"reason": "Recorded reason"}},
        )
        self.assertEqual(
            result.prerequisite_review_metadata_by_declaration,
            {"Fixture.Model": {"reason": "Recorded prerequisite"}},
        )
        self.assertTrue(result.reviewed_display_surface_complete)
        selected.assert_called_once_with(
            root,
            "Fixture",
            payload,
            preflight=preflight,
            authority_sha256s=(sha("2"),),
        )

    def test_recorded_review_metadata_requires_exact_accepted_leaf_issuance(
        self,
    ) -> None:
        terminal_authority = sha("9")
        direct_judgment = sha("1")
        direct_lean = sha("2")
        direct_source = sha("3")
        direct_target = sha("4")
        prerequisite_judgment = sha("5")
        prerequisite_lean = sha("6")
        prerequisite_source = sha("7")
        prerequisite_target = sha("8")
        direct_row = {
            "source_item": "claim",
            "semantic_target_declaration": "Fixture.claimSpec",
            "judgment": "matches",
            "source_input_bundle_sha256": direct_source,
            "lean_expanded_statement_sha256": direct_target,
            "reason": "Exact accepted direct reason.",
            "validator": "recorded reviewer",
            "validated_at": "2026-09-05T12:00:00+00:00",
        }
        prerequisite_row = {
            "paper_declaration": "Fixture.Model",
            "source_item": "prerequisite_source",
            "judgment": "matches",
            "source_input_bundle_sha256": prerequisite_source,
            "paper_semantic_target_sha256": prerequisite_target,
            "reason": "Exact accepted prerequisite reason.",
            "validator": "recorded prerequisite reviewer",
            "validator_type": "llm_as_judge",
            "validated_at": "2026-09-05T12:01:00+00:00",
        }
        current = SimpleNamespace(
            closure_leaf=SimpleNamespace(
                semantic_payload={"terminal_authority_sha256": terminal_authority}
            ),
            semantic_graph=SimpleNamespace(
                leaves={
                    direct_judgment: SimpleNamespace(
                        kind=credential.ObligationKind.SOURCE_LEAN_JUDGMENT,
                        semantic_payload={
                            "verdict": "matches",
                            "verbatim_source_bundle_sha256": direct_source,
                            "lean_declaration_sha256": direct_lean,
                        },
                    ),
                    direct_lean: SimpleNamespace(
                        semantic_payload={
                            "reviewed_semantic_target_sha256": direct_target
                        }
                    ),
                    prerequisite_judgment: SimpleNamespace(
                        kind=credential.ObligationKind.SOURCE_LEAN_JUDGMENT,
                        semantic_payload={
                            "verdict": "matches",
                            "verbatim_source_bundle_sha256": prerequisite_source,
                            "lean_declaration_sha256": prerequisite_lean,
                        },
                    ),
                    prerequisite_lean: SimpleNamespace(
                        semantic_payload={
                            "reviewed_semantic_target_sha256": prerequisite_target
                        }
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {"source_lean_judgment": (direct_judgment,)}
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Model": {
                        "source_lean_judgment": (prerequisite_judgment,)
                    }
                },
            ),
        )
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                result_routes=lambda: (
                    SimpleNamespace(
                        source_item_id="claim",
                        spec_declaration="Fixture.claimSpec",
                    ),
                )
            )
        )

        def row_sha256(row: object) -> str:
            return credential.hashlib.sha256(
                credential.canonical_json_bytes(row)
            ).hexdigest()

        issuances = (
            {
                "leaf_sha256": direct_judgment,
                "evidence_record_sha256": row_sha256(direct_row),
                "authority_sha256": terminal_authority,
                "assurance_contract_sha256": (
                    credential.STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
                ),
            },
            {
                "leaf_sha256": prerequisite_judgment,
                "evidence_record_sha256": row_sha256(prerequisite_row),
                "authority_sha256": terminal_authority,
                "assurance_contract_sha256": (
                    credential.STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
                ),
            },
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            audit = root / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)

            def write_ledgers(
                row: dict[str, object],
                prerequisite: dict[str, object] = prerequisite_row,
            ) -> None:
                (audit / "v11_raw_source_spec_screening.json").write_text(
                    json.dumps(
                        {
                            "schema": 3,
                            "paper": "Fixture",
                            "items": {"Fixture.claimSpec": row},
                        }
                    ),
                    encoding="utf-8",
                )
                (audit / "paper_semantic_prerequisites.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": "Fixture",
                            "items": {"Fixture.Model": prerequisite},
                        }
                    ),
                    encoding="utf-8",
                )
                (audit / "library_semantic_review.json").write_text(
                    json.dumps({"schema": 1, "paper": "Fixture", "items": {}}),
                    encoding="utf-8",
                )

            write_ledgers(direct_row)
            with mock.patch.object(
                credential,
                "load_obligation_evidence_store_snapshot",
                return_value=SimpleNamespace(issuances=issuances),
            ):
                direct, prerequisites, owners = (
                    credential._recorded_issued_review_metadata(
                        root, "Fixture", current, preflight
                    )
                )
                self.assertEqual(
                    direct["Fixture.claimSpec"]["reason"],
                    "Exact accepted direct reason.",
                )
                self.assertEqual(
                    prerequisites["Fixture.Model"]["validated_at"],
                    "2026-09-05T12:01:00+00:00",
                )
                self.assertEqual(
                    prerequisites["Fixture.Model"]["_evidence_record_sha256"],
                    row_sha256(prerequisite_row),
                )
                self.assertEqual(owners, {"Fixture.Model": "prerequisite_source"})

                write_ledgers(
                    {**direct_row, "reason": "Changed after closeout."}
                )
                changed, still_bound, still_owned = (
                    credential._recorded_issued_review_metadata(
                        root, "Fixture", current, preflight
                    )
                )
                self.assertNotIn("Fixture.claimSpec", changed)
                self.assertIn("Fixture.Model", still_bound)
                self.assertEqual(
                    still_owned, {"Fixture.Model": "prerequisite_source"}
                )

                write_ledgers(
                    direct_row,
                    {**prerequisite_row, "source_item": "mutated_source"},
                )
                _direct, mutated, mutated_owners = (
                    credential._recorded_issued_review_metadata(
                        root, "Fixture", current, preflight
                    )
                )
                self.assertNotIn("Fixture.Model", mutated)
                self.assertNotIn("Fixture.Model", mutated_owners)

            unbound = tuple(
                {**issuance, "authority_sha256": sha("a")}
                for issuance in issuances
            )
            write_ledgers(direct_row)
            with mock.patch.object(
                credential,
                "load_obligation_evidence_store_snapshot",
                return_value=SimpleNamespace(issuances=unbound),
            ):
                direct, prerequisites, owners = (
                    credential._recorded_issued_review_metadata(
                        root, "Fixture", current, preflight
                    )
                )
            self.assertEqual(direct, {})
            self.assertEqual(prerequisites, {})
            self.assertEqual(owners, {})

    def test_recorded_projection_joins_result_and_prerequisite_judgments(self) -> None:
        direct_judgment = sha("1")
        condition_judgment = sha("2")
        second_condition_judgment = sha("3")
        result_atom = sha("4")
        condition_atom = sha("5")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    direct_judgment: SimpleNamespace(
                        semantic_payload={"verdict": "matches"}
                    ),
                    condition_judgment: SimpleNamespace(
                        semantic_payload={"verdict": "matches"}
                    ),
                    second_condition_judgment: SimpleNamespace(
                        semantic_payload={"verdict": "uncertain"}
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "result": {
                        "source_atom": (result_atom,),
                        "source_lean_judgment": (direct_judgment,),
                    },
                    "condition": {"source_atom": (condition_atom,)},
                    "unreviewed_deep_item": {"source_atom": (sha("6"),)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Condition": {
                        "source_atom": (condition_atom,),
                        "source_lean_judgment": (condition_judgment,),
                    },
                    "Fixture.SecondConditionView": {
                        "source_atom": (condition_atom,),
                        "source_lean_judgment": (second_condition_judgment,),
                    },
                },
            ),
        )

        verdicts = credential._recorded_source_lean_verdicts_by_source_item(
            current,
            SimpleNamespace(
                require_current=lambda: None,
                prerequisite_source_item_by_declaration={
                    "Fixture.Condition": "condition",
                    "Fixture.SecondConditionView": "condition",
                },
            ),
        )

        self.assertEqual(verdicts["result"], "matches")
        self.assertEqual(verdicts["condition"], "uncertain")
        self.assertNotIn("unreviewed_deep_item", verdicts)

    def test_recorded_projection_exports_exact_source_bundles_for_both_lanes(
        self,
    ) -> None:
        direct_judgment = sha("1")
        condition_judgment = sha("2")
        result_atom = sha("3")
        condition_atom = sha("4")
        result_bundle = sha("5")
        condition_bundle = sha("6")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    direct_judgment: SimpleNamespace(
                        semantic_payload={
                            "verbatim_source_bundle_sha256": result_bundle
                        }
                    ),
                    condition_judgment: SimpleNamespace(
                        semantic_payload={
                            "verbatim_source_bundle_sha256": condition_bundle
                        }
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "result": {
                        "source_atom": (result_atom,),
                        "source_lean_judgment": (direct_judgment,),
                    },
                    "condition": {"source_atom": (condition_atom,)},
                    "unreviewed": {"source_atom": (sha("7"),)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Condition": {
                        "source_atom": (condition_atom,),
                        "source_lean_judgment": (condition_judgment,),
                    }
                },
            ),
        )

        bundles = credential._recorded_source_input_bundles_by_source_item(
            current,
            SimpleNamespace(
                require_current=lambda: None,
                prerequisite_source_item_by_declaration={
                    "Fixture.Condition": "condition"
                },
            ),
        )

        self.assertEqual(bundles["result"], result_bundle)
        self.assertEqual(bundles["condition"], condition_bundle)
        self.assertNotIn("unreviewed", bundles)

    def test_recorded_projection_preserves_source_free_shared_atom_bundles(
        self,
    ) -> None:
        first_judgment = sha("1")
        second_judgment = sha("2")
        condition_atom = sha("3")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    first_judgment: SimpleNamespace(
                        semantic_payload={"verbatim_source_bundle_sha256": sha("4")}
                    ),
                    second_judgment: SimpleNamespace(
                        semantic_payload={"verbatim_source_bundle_sha256": sha("5")}
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "condition": {"source_atom": (condition_atom,)},
                    "condition_view": {"source_atom": (condition_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Condition": {
                        "source_atom": (condition_atom,),
                        "source_lean_judgment": (first_judgment,),
                    },
                    "Fixture.ConditionView": {
                        "source_atom": (condition_atom,),
                        "source_lean_judgment": (second_judgment,),
                    },
                },
            ),
        )

        bundles = credential._recorded_source_input_bundles_by_source_item(
            current,
            SimpleNamespace(
                require_current=lambda: None,
                prerequisite_source_item_by_declaration={},
            ),
        )

        self.assertEqual(bundles["condition"], (sha("4"), sha("5")))
        self.assertEqual(bundles["condition_view"], (sha("4"), sha("5")))

    def test_recorded_projection_uses_authenticated_owner_for_shared_atom_bundles(
        self,
    ) -> None:
        shared_atom = sha("1")
        left_judgment = sha("2")
        right_judgment = sha("3")
        left_bundle = sha("4")
        right_bundle = sha("5")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    left_judgment: SimpleNamespace(
                        semantic_payload={
                            "verbatim_source_bundle_sha256": left_bundle
                        }
                    ),
                    right_judgment: SimpleNamespace(
                        semantic_payload={
                            "verbatim_source_bundle_sha256": right_bundle
                        }
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "dimension": {"source_atom": (shared_atom,)},
                    "recovery": {"source_atom": (shared_atom,)},
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Dimension": {
                        "source_atom": (shared_atom,),
                        "source_lean_judgment": (left_judgment,),
                    },
                    "Fixture.Recovery": {
                        "source_atom": (shared_atom,),
                        "source_lean_judgment": (right_judgment,),
                    },
                },
            ),
        )

        bundles = credential._recorded_source_input_bundles_by_source_item(
            current,
            SimpleNamespace(
                require_current=lambda: None,
                prerequisite_source_item_by_declaration={},
            ),
            authenticated_prerequisite_source_items_by_declaration={
                "Fixture.Dimension": "dimension",
                "Fixture.Recovery": "recovery",
            },
        )

        self.assertEqual(
            bundles,
            {"dimension": left_bundle, "recovery": right_bundle},
        )

    def test_recorded_projection_exports_exact_result_and_prerequisite_targets(
        self,
    ) -> None:
        result_leaf = sha("1")
        result_judgment = sha("2")
        prerequisite_leaf = sha("3")
        prerequisite_judgment = sha("4")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    result_leaf: SimpleNamespace(
                        kind=credential.ObligationKind.LEAN_DECLARATION,
                        semantic_payload={
                            "semantic_target_kind": "spec_proposition",
                            "reviewed_semantic_target_sha256": sha("5"),
                        },
                    ),
                    result_judgment: SimpleNamespace(
                        kind=credential.ObligationKind.SOURCE_LEAN_JUDGMENT,
                        semantic_payload={
                            "lean_declaration_sha256": result_leaf,
                            "verdict": "matches",
                        },
                    ),
                    prerequisite_leaf: SimpleNamespace(
                        kind=credential.ObligationKind.LEAN_DECLARATION,
                        semantic_payload={
                            "semantic_target_kind": "semantic_prerequisite",
                            "reviewed_semantic_target_sha256": sha("6"),
                        },
                    ),
                    prerequisite_judgment: SimpleNamespace(
                        kind=credential.ObligationKind.SOURCE_LEAN_JUDGMENT,
                        semantic_payload={
                            "lean_declaration_sha256": prerequisite_leaf,
                            "verdict": "matches",
                        },
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                route_leaf_sha256s_by_source_item={
                    "claim": {
                        "semantic_review": (result_leaf,),
                        "spec": (result_leaf,),
                        "source_lean_judgment": (result_judgment,),
                    }
                },
                prerequisite_leaf_sha256s_by_declaration={
                    "AppliedModelingLib.Shared.Model": {
                        "lean_declaration": (prerequisite_leaf,),
                        "source_lean_judgment": (prerequisite_judgment,),
                    }
                },
            ),
        )
        route = SimpleNamespace(
            source_item_id="claim",
            spec_declaration="Fixture.claimSpec",
            semantic_review_target_kind=SimpleNamespace(value="spec_proposition"),
        )
        preflight = SimpleNamespace(
            route_set=SimpleNamespace(
                result_route_by_specification=lambda: {"Fixture.claimSpec": route}
            )
        )

        self.assertEqual(
            credential._recorded_claim_semantic_targets_by_specification(
                current, preflight
            ),
            {"Fixture.claimSpec": sha("5")},
        )
        self.assertEqual(
            credential._recorded_prerequisite_semantic_targets_by_declaration(current),
            {"AppliedModelingLib.Shared.Model": sha("6")},
        )

    def test_recorded_target_projection_rejects_nonmatching_judgment(self) -> None:
        lean_leaf = sha("1")
        judgment_leaf = sha("2")
        current = SimpleNamespace(
            semantic_graph=SimpleNamespace(
                leaves={
                    lean_leaf: SimpleNamespace(
                        kind=credential.ObligationKind.LEAN_DECLARATION,
                        semantic_payload={
                            "semantic_target_kind": "semantic_prerequisite",
                            "reviewed_semantic_target_sha256": sha("3"),
                        },
                    ),
                    judgment_leaf: SimpleNamespace(
                        kind=credential.ObligationKind.SOURCE_LEAN_JUDGMENT,
                        semantic_payload={
                            "lean_declaration_sha256": lean_leaf,
                            "verdict": "uncertain",
                        },
                    ),
                }
            ),
            paper_index=SimpleNamespace(
                prerequisite_leaf_sha256s_by_declaration={
                    "Fixture.Model": {
                        "lean_declaration": (lean_leaf,),
                        "source_lean_judgment": (judgment_leaf,),
                    }
                }
            ),
        )

        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "positive source judgment",
        ):
            credential._recorded_prerequisite_semantic_targets_by_declaration(current)

    def test_legacy_receipt_cannot_be_promoted_without_current_strict_closeout(
        self,
    ) -> None:
        graph, index, preflight, _terminal, legacy_issuances = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            store_paper_obligation_bundle(
                root,
                "Fixture",
                index,
                graph,
                legacy_issuances,
                preflight=preflight,
            )
            with self.assertRaisesRegex(
                credential.ObligationClosureCredentialError,
                "run the current strict closeout",
            ):
                (
                    credential.promote_current_obligation_bundle_to_acceptance(
                        root,
                        "Fixture",
                        authenticated_predecessor_sha256=sha("6"),
                    )
                )
            self.assertFalse((folder / "FINAL_CLOSURE_RECEIPT.md").exists())

    def test_aggregate_drift_does_not_replay_current_import_closure(self) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        drifted = replace(
            preflight,
            source_inventory_sha256=sha("a"),
            route_schema_sha256=sha("b"),
            structural_preflight_sha256=sha("c"),
        )
        provider = SimpleNamespace(root=Path("/repo"))
        loaded = SimpleNamespace(
            graph_sha256=graph.graph_sha256,
            paper_index=index,
            graph=graph,
            closure_leaf=SimpleNamespace(
                contract_sha256=PAPER_CLOSURE_CONTRACT.contract_sha256
            ),
        )
        with (
            mock.patch.object(
                credential,
                "_current_preflight",
                return_value=(drifted, (), {}),
            ),
            mock.patch.object(
                credential, "_validate_current_source", return_value=None
            ),
            mock.patch.object(
                credential,
                "_registered_engine_authorities",
                return_value=(sha("4"), (sha("4"),)),
            ),
            mock.patch.object(
                credential,
                "load_accepted_obligation_graph",
                return_value=loaded,
            ) as load,
            mock.patch.object(
                credential,
                "_validate_current_build",
                return_value=(provider, (), False, ""),
            ) as validate_build,
            mock.patch.object(
                credential,
                "revalidate_terminal_lean_semantics",
                side_effect=AssertionError(
                    "aggregate labels cannot replay an exact current import closure"
                ),
            ) as revalidate,
            mock.patch.object(credential, "_snapshot", return_value={}),
        ):
            controls = credential._prepare_accepted_graph_controls(
                Path("/repo"), "Fixture"
            )
        load.assert_called_once_with(
            Path("/repo"),
            "Fixture",
            preflight=drifted,
            authenticated_authority_sha256s=(sha("4"),),
            require_current_aggregate_identity=False,
        )
        revalidate.assert_not_called()
        validate_build.assert_called_once_with(
            Path("/repo"),
            "Fixture",
            loaded,
            drifted,
            accepted_graph_external_artifact_authority=True,
        )
        self.assertIs(controls.input_guard, provider)
        self.assertEqual(
            controls.terminal_validation_route, "exact_import_closure"
        )
        self.assertEqual(controls.terminal_validation_detail, "")

    def test_exact_only_controls_cannot_recover_interleaved_closure_drift(
        self,
    ) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        loaded = SimpleNamespace(
            graph_sha256=graph.graph_sha256,
            paper_index=index,
            graph=graph,
            closure_leaf=SimpleNamespace(
                contract_sha256=PAPER_CLOSURE_CONTRACT.contract_sha256
            ),
        )

        def reject_drift(*_args, **kwargs):
            self.assertFalse(
                kwargs["accepted_graph_external_artifact_authority"]
            )
            raise credential.ObligationClosureCredentialError(
                "build leaf Lean import closure is stale"
            )

        with (
            mock.patch.object(
                credential,
                "_current_preflight",
                return_value=(preflight, (), {}),
            ),
            mock.patch.object(
                credential, "_validate_current_source", return_value=None
            ),
            mock.patch.object(
                credential,
                "_registered_engine_authorities",
                return_value=(sha("4"), (sha("4"),)),
            ),
            mock.patch.object(
                credential,
                "load_accepted_obligation_graph",
                return_value=loaded,
            ),
            mock.patch.object(
                credential,
                "_validate_current_build",
                side_effect=reject_drift,
            ) as validate_build,
            mock.patch.object(
                credential,
                "revalidate_terminal_lean_semantics",
                side_effect=AssertionError("migration must never run native recovery"),
            ) as revalidate,
        ):
            with self.assertRaisesRegex(
                credential.ObligationClosureCredentialError,
                "Lean import closure is stale",
            ):
                credential._prepare_accepted_graph_controls(
                    Path("/repo"),
                    "Fixture",
                    allow_lean_semantic_recovery=False,
                )
        validate_build.assert_called_once()
        revalidate.assert_not_called()

    def test_accepted_semantic_reader_rejects_stale_lean_before_unchanged_ledgers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            audit = root / "papers" / "Fixture" / "audit"
            audit.mkdir(parents=True)
            ledger_paths = tuple(
                audit / name
                for name in (
                    "v11_raw_source_spec_screening.json",
                    "paper_semantic_prerequisites.json",
                    "library_semantic_review.json",
                )
            )
            for path in ledger_paths:
                path.write_text('{"items": {}}\n', encoding="utf-8")
            before = {path: path.read_bytes() for path in ledger_paths}
            with mock.patch.object(
                credential,
                "_prepare_accepted_graph_controls",
                side_effect=credential.ObligationClosureCredentialError(
                    "build leaf Lean import closure is stale"
                ),
            ) as prepare:
                with self.assertRaisesRegex(
                    credential.ObligationClosureCredentialError,
                    "Lean import closure is stale",
                ):
                    credential.authenticated_current_accepted_graph_semantic_review_inputs(
                        root,
                        "Fixture",
                    )
            prepare.assert_called_once_with(
                root.resolve(),
                "Fixture",
                allow_lean_semantic_recovery=False,
            )
            self.assertEqual(
                before,
                {path: path.read_bytes() for path in ledger_paths},
            )

    def test_accepted_semantic_reader_requires_modern_target_identities(self) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        current = SimpleNamespace(
            semantic_graph=graph,
            paper_index=index,
        )
        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "lacks modern reviewed target identities",
        ):
            credential._accepted_graph_direct_target_identities(
                current,
                preflight,
            )

    def test_current_terminal_assurances_reject_source_and_holistic_drift(
        self,
    ) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        loaded = SimpleNamespace(
            graph_sha256=graph.graph_sha256,
            paper_index=index,
            graph=graph,
            closure_leaf=SimpleNamespace(
                contract_sha256=(
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
                ),
                semantic_payload={
                    "source_assurance_sha256": sha("1"),
                    "final_holistic_audit_surface_sha256": sha("3"),
                },
            ),
        )

        def attempt(
            *, source_sha: str, v2_sha: str = sha("8"),
            holistic_errors=(), historical_sha=(),
            expected_historical_mode=None, assurance_payload=None,
            expected_policy_count=None,
        ):
            selected_sources = set(
                credential.prerequisite_source_judgments_by_source_item(index, preflight)
            ) | {
                key for key, roles in index.route_leaf_sha256s_by_source_item.items()
                if roles.get("source_lean_judgment")
            }
            with (
                mock.patch.object(
                    credential, "current_reviewed_source_item_ids",
                    return_value=selected_sources,
                ) as source_selector,
                mock.patch.object(
                    credential,
                    "_current_preflight",
                    return_value=(preflight, (), {}),
                ),
                mock.patch.object(
                    credential, "_validate_current_source", return_value=None
                ),
                mock.patch.object(
                    credential,
                    "_registered_engine_authorities",
                    return_value=(sha("4"), (sha("4"),)),
                ),
                mock.patch.object(
                    credential,
                    "load_accepted_obligation_graph",
                    return_value=loaded,
                ),
                mock.patch.object(
                    credential,
                    "build_current_final_holistic_source_assurance_projection",
                    return_value=(assurance_payload or {"schema": 2}),
                ) as assurance_projection,
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_projection_sha256",
                    return_value=source_sha,
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_v2_projection",
                    return_value={
                        "schema": 2,
                        "v1_source_assurance_schema": (
                            assurance_payload or {"schema": 2}
                        ).get("schema", 2),
                        "review_policy_assurance": (
                            assurance_payload or {}
                        ).get("review_policy_assurance"),
                    },
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_v2_projection_sha256",
                    return_value=v2_sha,
                ),
                mock.patch.object(
                    credential,
                    "historical_final_holistic_source_assurance_sha256s",
                    return_value=frozenset(historical_sha),
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_audit_hard_errors",
                    return_value=list(holistic_errors),
                ) as document_gate,
            ):
                try:
                    return credential._prepare_accepted_graph_controls(
                        Path("/repo"), "Fixture"
                    )
                finally:
                    if assurance_projection.called:
                        source_selector.assert_called_once_with(
                            index, graph, preflight, source_map={},
                        )
                        expected_sources = set(
                            credential.prerequisite_source_judgments_by_source_item(
                                index, preflight
                            )
                        ) | {
                            key for key, roles in
                            index.route_leaf_sha256s_by_source_item.items()
                            if roles.get("source_lean_judgment")
                        }
                        self.assertEqual(
                            assurance_projection.call_args.kwargs[
                                "reviewed_source_item_ids"
                            ],
                            expected_sources,
                        )
                    if expected_historical_mode is not None:
                        self.assertEqual(
                            document_gate.call_args.kwargs[
                                "allow_historical_missing_scope"
                            ],
                            expected_historical_mode,
                        )
                    if expected_policy_count is not None:
                        self.assertEqual(
                            document_gate.call_args.kwargs[
                                "review_policy_assurance"
                            ]["required_final_adversary_count"],
                            expected_policy_count,
                        )

        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "source inventory, correction, defect, fidelity",
        ):
            attempt(source_sha=sha("9"))
        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "final holistic audit is stale",
        ):
            attempt(
                source_sha=sha("1"),
                holistic_errors=(SimpleNamespace(message="wrong surface"),),
                expected_historical_mode=False,
                assurance_payload={
                    "schema": 3,
                    "review_policy_assurance": {
                        "schema": 1,
                        "source_scope": "all_named_theory",
                        "repeat_final_scope": "main_primary",
                        "required_final_adversary_count": 2,
                    },
                },
                expected_policy_count=2,
            )
        # A v2 root authenticates the same review policy while ignoring the
        # legacy prose-bearing v1 digest.
        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "final holistic audit is stale",
        ):
            attempt(
                source_sha=sha("9"),
                v2_sha=sha("1"),
                holistic_errors=(SimpleNamespace(message="wrong surface"),),
                expected_historical_mode=False,
                assurance_payload={
                    "schema": 3,
                    "review_policy_assurance": {
                        "schema": 1,
                        "source_scope": "all_named_theory",
                        "repeat_final_scope": "main_primary",
                        "required_final_adversary_count": 2,
                    },
                },
                expected_policy_count=2,
            )
        # Reading an exact historical assurance does not waive the separate
        # current document gate (or the following source/build controls).
        with self.assertRaisesRegex(
            credential.ObligationClosureCredentialError,
            "final holistic audit is stale",
        ):
            attempt(
                source_sha=sha("9"),
                historical_sha=(sha("1"),),
                holistic_errors=(SimpleNamespace(message="wrong surface"),),
                expected_historical_mode=True,
            )

    def test_v2_reader_retains_ordinary_semantic_recovery_route(self) -> None:
        graph, index, preflight, _issuances, _legacy = self.fixture()
        review_policy = {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": 2,
        }
        loaded = SimpleNamespace(
            graph_sha256=graph.graph_sha256,
            paper_index=index,
            graph=graph,
            closure_leaf=SimpleNamespace(
                contract_sha256=(
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
                ),
                semantic_payload={
                    "source_assurance_sha256": sha("1"),
                    "final_holistic_audit_surface_sha256": sha("3"),
                },
            ),
        )
        provider = SimpleNamespace()
        with (
            mock.patch.object(
                credential,
                "_current_preflight",
                return_value=(preflight, (), {}),
            ),
            mock.patch.object(
                credential, "_validate_current_source", return_value=None
            ),
            mock.patch.object(
                credential,
                "_registered_engine_authorities",
                return_value=(sha("4"), (sha("4"),)),
            ),
            mock.patch.object(
                credential,
                "load_accepted_obligation_graph",
                return_value=loaded,
            ),
            mock.patch.object(
                credential,
                "current_reviewed_source_item_ids",
                return_value={"theorem1"},
            ),
            mock.patch.object(
                credential,
                "build_current_final_holistic_source_assurance_projection",
                return_value={
                    "schema": 3,
                    "review_policy_assurance": review_policy,
                },
            ),
            mock.patch.object(
                credential,
                "final_holistic_source_assurance_projection_sha256",
                return_value=sha("9"),
            ),
            mock.patch.object(
                credential,
                "final_holistic_source_assurance_v2_projection",
                return_value={
                    "schema": 2,
                    "v1_source_assurance_schema": 3,
                    "review_policy_assurance": review_policy,
                },
            ),
            mock.patch.object(
                credential,
                "final_holistic_source_assurance_v2_projection_sha256",
                return_value=sha("1"),
            ),
            mock.patch.object(
                credential, "final_holistic_audit_hard_errors", return_value=[]
            ),
            mock.patch.object(
                credential,
                "validated_final_adversarial_review_artifact_paths",
                return_value=(),
            ),
            mock.patch.object(
                credential,
                "_validate_current_build",
                return_value=(provider, (), True, "source-only closure drift"),
            ) as validate_build,
            mock.patch.object(credential, "_snapshot", return_value={}),
        ):
            controls = credential._prepare_accepted_graph_controls(
                Path("/repo"), "Fixture"
            )
        validate_build.assert_called_once_with(
            Path("/repo"),
            "Fixture",
            loaded,
            preflight,
            accepted_graph_external_artifact_authority=True,
        )
        self.assertEqual(controls.terminal_validation_route, "lean_semantic_recovery")
        self.assertEqual(
            controls.terminal_validation_detail,
            "source-only closure drift",
        )

    def test_terminal_v1_to_v2_migration_reuses_only_frozen_inputs(self) -> None:
        authority = strict_authority()
        preflight = SimpleNamespace()
        semantic_graph = SimpleNamespace(
            leaves={"semantic-leaf": object()},
            graph_sha256=sha("d"),
        )
        paper_index = SimpleNamespace(index_sha256=sha("e"))
        v1_sha = sha("a")
        v2_sha = sha("b")
        final_audit_sha = sha("c")
        old = SimpleNamespace(
            graph_sha256=sha("f"),
            graph=semantic_graph,
            paper_index=paper_index,
            closure_leaf=SimpleNamespace(
                contract_sha256=(
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
                ),
                semantic_payload={
                    "source_assurance_sha256": v1_sha,
                    "final_holistic_audit_surface_sha256": final_audit_sha,
                    "strict_closeout_authority": authority.projection(),
                },
            ),
        )
        migrated = SimpleNamespace(
            graph_sha256=sha("9"),
            graph=semantic_graph,
            paper_index=paper_index,
            closure_leaf=SimpleNamespace(
                semantic_payload={
                    "source_assurance_sha256": v2_sha,
                    "final_holistic_audit_surface_sha256": final_audit_sha,
                    "strict_closeout_authority": authority.projection(),
                }
            ),
        )
        controls = SimpleNamespace(
            loaded=old,
            preflight=preflight,
            authority_sha256s=(authority.engine_tree_sha256,),
            terminal_validation_route="exact_import_closure",
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            pointer = credential.current_accepted_graph_path(root, "Fixture")
            pointer.parent.mkdir(parents=True)
            old_pointer_bytes = credential.canonical_json_bytes(
                {"schema": 2, "graph_sha256": old.graph_sha256}
            ) + b"\n"
            pointer.write_bytes(old_pointer_bytes)
            old_receipt_bytes = b"old receipt\n"
            receipt_path = root / "papers" / "Fixture" / "FINAL_CLOSURE_RECEIPT.md"
            receipt_path.write_bytes(old_receipt_bytes)

            def select_migrated(*_args, **_kwargs):
                credential._atomic_write(
                    pointer,
                    credential.canonical_json_bytes(
                        {"schema": 2, "graph_sha256": migrated.graph_sha256}
                    )
                    + b"\n",
                )
                return pointer

            with (
                mock.patch.object(
                    credential,
                    "_current_preflight",
                    return_value=(preflight, (), {}),
                ),
                mock.patch.object(
                    credential,
                    "load_accepted_obligation_graph",
                    return_value=migrated,
                ),
                mock.patch.object(
                    credential,
                    "current_reviewed_source_item_ids",
                    return_value={"theorem1"},
                ),
                mock.patch.object(
                    credential,
                    "build_current_final_holistic_source_assurance_projection",
                    return_value={"schema": 3},
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_projection_sha256",
                    return_value=v1_sha,
                ),
                mock.patch.object(
                    credential,
                    "_prepare_accepted_graph_controls",
                    return_value=controls,
                ) as prepare,
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_v2_projection",
                    return_value={"schema": 2},
                ),
                mock.patch.object(
                    credential,
                    "final_holistic_source_assurance_v2_projection_sha256",
                    return_value=v2_sha,
                ),
                mock.patch.object(
                    credential,
                    "build_accepted_obligation_graph",
                    return_value=SimpleNamespace(graph_sha256=migrated.graph_sha256),
                ),
                mock.patch.object(
                    credential,
                    "store_accepted_obligation_graph",
                    side_effect=select_migrated,
                ) as store,
                mock.patch.object(
                    credential, "_selected_accepted_graph_from_receipt"
                ),
                mock.patch.object(credential, "_finalize_controls") as finalize,
            ):
                receipt = (
                    credential.migrate_accepted_terminal_source_assurance_v1_to_v2(
                        root, "Fixture"
                    )
                )
            migrated_receipt_bytes = receipt_path.read_bytes()
        self.assertEqual(receipt.name, "FINAL_CLOSURE_RECEIPT.md")
        prepare.assert_called_once_with(
            root.resolve(),
            "Fixture",
            allow_lean_semantic_recovery=False,
        )
        store.assert_called_once_with(
            root.resolve(),
            "Fixture",
            paper_index,
            semantic_graph,
            preflight=preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=final_audit_sha,
            source_assurance_sha256=v2_sha,
        )
        self.assertIn(migrated.graph_sha256.encode("ascii"), migrated_receipt_bytes)
        self.assertEqual(finalize.call_args_list, [mock.call(controls)] * 2)

    def test_terminal_v1_to_v2_migration_rejects_invalid_v1_digest(self) -> None:
        preflight = SimpleNamespace()
        loaded = SimpleNamespace(
            graph_sha256=sha("f"),
            graph=SimpleNamespace(leaves={}, graph_sha256=sha("d")),
            paper_index=SimpleNamespace(index_sha256=sha("e")),
            closure_leaf=SimpleNamespace(
                contract_sha256=(
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
                ),
                semantic_payload={
                    "source_assurance_sha256": sha("a"),
                },
            ),
        )
        controls = SimpleNamespace(
            loaded=loaded,
            preflight=preflight,
            terminal_validation_route="exact_import_closure",
        )
        with (
            mock.patch.object(
                credential,
                "_terminal_selection_lock",
                return_value=nullcontext(),
            ),
            mock.patch.object(
                credential,
                "_current_preflight",
                return_value=(preflight, (), {}),
            ),
            mock.patch.object(
                credential,
                "_prepare_accepted_graph_controls",
                return_value=controls,
            ) as prepare,
            mock.patch.object(
                credential,
                "current_reviewed_source_item_ids",
                return_value={"theorem1"},
            ),
            mock.patch.object(
                credential,
                "build_current_final_holistic_source_assurance_projection",
                return_value={"schema": 3},
            ),
            mock.patch.object(
                credential,
                "final_holistic_source_assurance_projection_sha256",
                return_value=sha("b"),
            ),
            mock.patch.object(
                credential, "store_accepted_obligation_graph"
            ) as store,
        ):
            with self.assertRaisesRegex(
                credential.ObligationClosureCredentialError,
                "exact current v1 digest",
            ):
                credential.migrate_accepted_terminal_source_assurance_v1_to_v2(
                    Path("/repo"), "Fixture"
                )
        prepare.assert_called_once_with(
            Path("/repo"),
            "Fixture",
            allow_lean_semantic_recovery=False,
        )
        store.assert_not_called()

    def test_terminal_migration_rolls_back_tamper_and_watched_input_drift(
        self,
    ) -> None:
        authority = strict_authority()
        preflight = SimpleNamespace()
        semantic_graph = SimpleNamespace(
            leaves={"semantic-leaf": object()},
            graph_sha256=sha("d"),
        )
        paper_index = SimpleNamespace(index_sha256=sha("e"))
        v1_sha = sha("a")
        v2_sha = sha("b")
        final_audit_sha = sha("c")
        old = SimpleNamespace(
            graph_sha256=sha("f"),
            graph=semantic_graph,
            paper_index=paper_index,
            closure_leaf=SimpleNamespace(
                contract_sha256=(
                    STRICT_SEMANTIC_PAPER_CLOSURE_CONTRACT.contract_sha256
                ),
                semantic_payload={
                    "source_assurance_sha256": v1_sha,
                    "final_holistic_audit_surface_sha256": final_audit_sha,
                    "strict_closeout_authority": authority.projection(),
                },
            ),
        )

        cases = (
            ("authority tamper", {"paper": "tampered"}, False),
            (
                "watched input drift",
                authority.projection(),
                True,
            ),
        )
        for label, migrated_authority, mutate_watched_input in cases:
            with self.subTest(failure=label), tempfile.TemporaryDirectory() as temp_dir:
                root = Path(temp_dir)
                (root / "papers" / "Fixture").mkdir(parents=True)
                pointer = credential.current_accepted_graph_path(root, "Fixture")
                pointer.parent.mkdir(parents=True)
                old_pointer_bytes = credential.canonical_json_bytes(
                    {"schema": 2, "graph_sha256": old.graph_sha256}
                ) + b"\n"
                pointer.write_bytes(old_pointer_bytes)
                receipt_path = (
                    root / "papers" / "Fixture" / "FINAL_CLOSURE_RECEIPT.md"
                )
                self.assertFalse(receipt_path.exists())
                watched_path = root / "papers" / "Fixture" / "watched-input.json"
                watched_path.write_bytes(b"stable watched input\n")
                migrated = SimpleNamespace(
                    graph_sha256=sha("9"),
                    graph=semantic_graph,
                    paper_index=paper_index,
                    closure_leaf=SimpleNamespace(
                        semantic_payload={
                            "source_assurance_sha256": v2_sha,
                            "final_holistic_audit_surface_sha256": final_audit_sha,
                            "strict_closeout_authority": migrated_authority,
                        }
                    ),
                )
                controls = SimpleNamespace(
                    loaded=old,
                    preflight=preflight,
                    authority_sha256s=(authority.engine_tree_sha256,),
                    terminal_validation_route="exact_import_closure",
                    input_guard=SimpleNamespace(finalize_unchanged=lambda: True),
                    watched_input_sha256s={
                        watched_path.resolve().as_posix(): (
                            credential._sha256_file(watched_path)
                        )
                    },
                )

                def select_migrated(*_args, **_kwargs):
                    credential._atomic_write(
                        pointer,
                        credential.canonical_json_bytes(
                            {"schema": 2, "graph_sha256": migrated.graph_sha256}
                        )
                        + b"\n",
                    )
                    if mutate_watched_input:
                        watched_path.write_bytes(b"changed watched input\n")
                    return pointer
                with (
                    mock.patch.object(
                        credential,
                        "_current_preflight",
                        return_value=(preflight, (), {}),
                    ),
                    mock.patch.object(
                        credential,
                        "_prepare_accepted_graph_controls",
                        return_value=controls,
                    ) as prepare,
                    mock.patch.object(
                        credential,
                        "current_reviewed_source_item_ids",
                        return_value={"theorem1"},
                    ),
                    mock.patch.object(
                        credential,
                        "build_current_final_holistic_source_assurance_projection",
                        return_value={"schema": 3},
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_source_assurance_projection_sha256",
                        return_value=v1_sha,
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_source_assurance_v2_projection",
                        return_value={"schema": 2},
                    ),
                    mock.patch.object(
                        credential,
                        "final_holistic_source_assurance_v2_projection_sha256",
                        return_value=v2_sha,
                    ),
                    mock.patch.object(
                        credential,
                        "build_accepted_obligation_graph",
                        return_value=SimpleNamespace(
                            graph_sha256=migrated.graph_sha256
                        ),
                    ),
                    mock.patch.object(
                        credential,
                        "store_accepted_obligation_graph",
                        side_effect=select_migrated,
                    ) as store,
                    mock.patch.object(
                        credential,
                        "load_accepted_obligation_graph",
                        return_value=migrated,
                    ),
                    mock.patch.object(
                        credential, "_selected_accepted_graph_from_receipt"
                    ),
                    mock.patch.object(
                        credential,
                        "_finalize_controls",
                        wraps=credential._finalize_controls,
                    ) as finalize,
                    mock.patch.object(
                        credential,
                        "revalidate_terminal_lean_semantics",
                        side_effect=AssertionError(
                            "terminal migration must never run native recovery"
                        ),
                    ) as revalidate,
                ):
                    with self.assertRaises(credential.ObligationClosureCredentialError):
                        credential.migrate_accepted_terminal_source_assurance_v1_to_v2(
                            root, "Fixture"
                        )
                prepare.assert_called_once_with(
                    root.resolve(),
                    "Fixture",
                    allow_lean_semantic_recovery=False,
                )
                store.assert_called_once()
                revalidate.assert_not_called()
                self.assertEqual(
                    finalize.call_count,
                    2 if mutate_watched_input else 1,
                )
                self.assertEqual(pointer.read_bytes(), old_pointer_bytes)
                self.assertFalse(receipt_path.exists())

    def test_terminal_migration_rollback_preserves_concurrent_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            pointer = root / "current_accepted_graph.json"
            receipt = root / "FINAL_CLOSURE_RECEIPT.md"
            old_pointer = b"old pointer\n"
            old_receipt = b"old receipt\n"
            migration_pointer = b"migration pointer\n"
            migration_receipt = b"migration receipt\n"
            concurrent_pointer = b"concurrent pointer\n"
            concurrent_receipt = b"concurrent receipt\n"
            pointer.write_bytes(concurrent_pointer)
            receipt.write_bytes(concurrent_receipt)

            credential._restore_terminal_migration_selection(
                pointer_path=pointer,
                receipt_path=receipt,
                old_pointer_bytes=old_pointer,
                old_receipt_bytes=old_receipt,
                new_pointer_bytes=migration_pointer,
                new_receipt_bytes=migration_receipt,
            )

            self.assertEqual(pointer.read_bytes(), concurrent_pointer)
            self.assertEqual(receipt.read_bytes(), concurrent_receipt)


if __name__ == "__main__":
    unittest.main()
