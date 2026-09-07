#!/usr/bin/env python3
"""Tests for the advisory, fail-closed paper closeout reuse planner."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import types
import unittest
from collections.abc import Mapping
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as integrity
from scripts import closeout_intake_freeze as intake_freeze
from scripts import source_manifest_validation as source_validation
from scripts import closeout_reuse_plan as planner_cli
from scripts import reissue_v11_raw_source_spec_screening as screening_reissue
from scripts.current_closeout import (
    evidence_transaction,
    graph_preparation,
    lean_review_graph,
    plan_publication,
    planner,
    primary_gate_transaction,
)
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    V11EvidenceRunContext,
    load_json_snapshot,
)
from scripts.v11_screening_contract import V11_SCREENING_PROMPT_VERSION


class CloseoutReusePlanTests(unittest.TestCase):
    def _issued_v11_context(
        self,
        folder: Path,
        *,
        sidecar_paths: tuple[Path, ...] = (),
    ) -> V11EvidenceRunContext:
        """Issue the nominal current context required by planner boundaries."""

        status_path = folder / "status.json"
        statement_map_path = folder / "audit" / "paper_statement_map.json"
        audit_config_path = folder.parent / "audit_config.json"
        statement_map_path.parent.mkdir(parents=True, exist_ok=True)
        if not statement_map_path.exists():
            statement_map_path.write_text('{"items": {}}\n', encoding="utf-8")
        if not audit_config_path.exists():
            audit_config_path.write_text("{}\n", encoding="utf-8")
        status_snapshot = load_json_snapshot(status_path)
        status_payload = status_snapshot.payload or {}
        inputs = CommonEvidenceRunContextInputs(
            folder=folder,
            status=str(status_payload.get("status") or ""),
            audit_config_snapshot=load_json_snapshot(audit_config_path),
            status_snapshot=status_snapshot,
            statement_map_snapshot=load_json_snapshot(statement_map_path),
            source_proof_fidelity_snapshot=None,
            sidecar_snapshots=tuple(
                load_json_snapshot(path) for path in sidecar_paths
            ),
            source_proof_fidelity_path_error="",
        )
        return inputs.issue_v11(None)

    def test_stable_cli_uses_package_planner_service(self) -> None:
        self.assertIs(planner_cli.main, planner.main)

    def test_document_semantic_basis_reuses_current_checkpoint_without_writes(self) -> None:
        folder = Path("/tmp/papers/Fixture")
        context = types.SimpleNamespace(
            v11_lean_review_graph_payload={"paper": "Fixture"}
        )
        result = mock.sentinel.semantic_result
        output = io.StringIO()
        with (
            mock.patch(
                "scripts.current_closeout.evidence_transaction."
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ) as build_context,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "current_v11_semantic_review_result",
                return_value=result,
            ) as current_review,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "all_selected_semantic_review_material_sha256",
                return_value="d" * 64,
            ) as project,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "accepted_graph_all_selected_semantic_review_material_sha256",
                side_effect=AssertionError("accepted-graph fallback was unnecessary"),
            ) as accepted_project,
            contextlib.redirect_stdout(output),
        ):
            code = planner.execute_document_semantic_basis(folder)

        self.assertEqual(code, 0)
        payload = json.loads(output.getvalue())
        self.assertEqual(payload["all_selected_semantic_review_sha256"], "d" * 64)
        self.assertFalse(payload["acceptance_credential"])
        self.assertTrue(payload["document_basis_only"])
        build_context.assert_called_once_with(folder, repository_root=planner.ROOT)
        current_review.assert_called_once_with(
            planner.ROOT,
            folder,
            context=context,
            require_graph_checkpoint=True,
        )
        project.assert_called_once_with(result)
        accepted_project.assert_not_called()

    def test_document_semantic_basis_missing_checkpoint_reuses_accepted_graph(self) -> None:
        folder = Path("/tmp/papers/Fixture")
        context = types.SimpleNamespace(v11_lean_review_graph_payload=None)
        snapshot_root = mock.Mock(v11_selected=True)
        snapshot_root.build_v11.return_value = context
        snapshot_root.build_v11_with_graph_checkpoint.side_effect = lambda: (
            evidence_transaction.CurrentV11EvidenceSnapshotRoot.build_v11_with_graph_checkpoint(
                snapshot_root
            )
        )
        output = io.StringIO()
        with (
            mock.patch.object(
                evidence_transaction.CurrentV11EvidenceSnapshotRoot,
                "acquire",
                return_value=snapshot_root,
            ) as acquire,
            mock.patch.object(
                lean_review_graph,
                "current_v11_lean_review_graph_checkpoint_reference",
                return_value=None,
            ) as checkpoint,
            mock.patch.object(
                lean_review_graph,
                "build_v11_lean_review_graph_material",
                side_effect=AssertionError("native Lean graph acquisition attempted"),
            ) as graph_builder,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "current_v11_semantic_review_result",
                side_effect=AssertionError("semantic graph acquisition attempted"),
            ) as current_review,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "accepted_graph_all_selected_semantic_review_material_sha256",
                return_value="e" * 64,
            ) as accepted_project,
            contextlib.redirect_stdout(output),
        ):
            code = planner.execute_document_semantic_basis(folder)

        self.assertEqual(code, 0)
        payload = json.loads(output.getvalue())
        self.assertTrue(payload["current"])
        self.assertEqual(payload["all_selected_semantic_review_sha256"], "e" * 64)
        self.assertFalse(payload["acceptance_credential"])
        self.assertTrue(payload["document_basis_only"])
        acquire.assert_called_once_with(folder, repository_root=planner.ROOT)
        checkpoint.assert_called_once_with(
            snapshot_root.folder,
            context,
            repository_root=snapshot_root.repository_root,
        )
        graph_builder.assert_not_called()
        current_review.assert_not_called()
        accepted_project.assert_called_once_with(
            planner.ROOT,
            folder,
            context=context,
        )

    def test_document_semantic_basis_accepted_graph_failure_does_not_run_lean(
        self,
    ) -> None:
        folder = Path("/tmp/papers/Fixture")
        context = types.SimpleNamespace(v11_lean_review_graph_payload=None)
        output = io.StringIO()
        with (
            mock.patch(
                "scripts.current_closeout.evidence_transaction."
                "build_current_v11_context_with_graph_checkpoint",
                return_value=context,
            ),
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "accepted_graph_all_selected_semantic_review_material_sha256",
                side_effect=ValueError(
                    "current accepted graph cannot supply document semantics: "
                    "build leaf Lean import closure is stale"
                ),
            ),
            mock.patch.object(
                lean_review_graph,
                "build_v11_lean_review_graph_material",
                side_effect=AssertionError("native Lean graph acquisition attempted"),
            ) as graph_builder,
            mock.patch(
                "scripts.current_closeout.semantic_review."
                "current_v11_semantic_review_result",
                side_effect=AssertionError("semantic graph acquisition attempted"),
            ) as current_review,
            contextlib.redirect_stdout(output),
        ):
            code = planner.execute_document_semantic_basis(folder)

        self.assertEqual(code, 2)
        payload = json.loads(output.getvalue())
        self.assertFalse(payload["current"])
        self.assertIn("Lean import closure is stale", payload["error"])
        graph_builder.assert_not_called()
        current_review.assert_not_called()

    def test_closeout_schedules_settled_review_context_projection_first(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            config_path = audit / "v11_source_map_preparation_config.json"
            config_path.write_text('{"paper": "Fixture"}\n', encoding="utf-8")
            current = {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "model_convention_ids": ["decision-1"],
                    }
                },
            }
            prepared = {
                "approved_review_context_schema": 1,
                "items": {
                    "claim": {
                        "model_convention_ids": ["decision-1"],
                        "approved_review_context_schema": 1,
                        "approved_review_contexts": [
                            {
                                "kind": "source_model_convention",
                                "id": "decision-1",
                                "record_sha256": "a" * 64,
                            }
                        ],
                    }
                },
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "expected_approved_review_context_projection",
                    return_value=(prepared, ""),
                ),
            ):
                action = planner.current_approved_review_context_projection_action(
                    folder,
                    current,
                )

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "sync_approved_review_contexts")
            self.assertEqual(
                action["commands"],
                [
                    (
                        "python3 scripts/sync_approved_review_contexts.py --paper "
                        "Fixture --write"
                    )
                ],
            )

    def test_closeout_accepts_current_settled_review_context_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "v11_source_map_preparation_config.json").write_text(
                '{"paper": "Fixture"}\n', encoding="utf-8"
            )
            current = {
                "paper": "Fixture",
                "approved_review_context_schema": 1,
                "items": {},
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "expected_approved_review_context_projection",
                    return_value=(
                        {
                            "approved_review_context_schema": 1,
                            "items": {},
                        },
                        "",
                    ),
                ),
            ):
                action = planner.current_approved_review_context_projection_action(
                    folder,
                    current,
                )

            self.assertIsNone(action)

    def test_closeout_checks_embedded_authority_without_preparation_config(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            current = {
                "paper": "Fixture",
                "items": {
                    "claim": {"model_convention_ids": ["decision-1"]}
                },
            }
            expected = {
                "approved_review_context_schema": 1,
                "items": {
                    "claim": {
                        "model_convention_ids": ["decision-1"],
                        "approved_review_context_schema": 1,
                        "approved_review_contexts": [{"id": "decision-1"}],
                    }
                },
            }
            with mock.patch.object(
                planner,
                "expected_approved_review_context_projection",
                return_value=(expected, ""),
            ):
                action = planner.current_approved_review_context_projection_action(
                    folder,
                    current,
                )

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "sync_approved_review_contexts")

    def test_import_closure_currentness_uses_nonaccepting_source_projection(
        self,
    ) -> None:
        """A stale-source probe never adopts build or external-artifact authority."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            closure = {
                "entry_module": "Fixture.ProofInterface",
                "repository_sources": [{"module": "Fixture.ProofInterface"}],
            }
            receipt = {"lean_import_closure": closure}
            provider = mock.Mock()
            provider.validated_repository_source_snapshot.return_value = (
                ("Fixture.ProofInterface", folder / "ProofInterface.lean", b"x", "a"),
            )
            provider_type = mock.Mock(return_value=provider)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch(
                    "scripts.lean_import_closure.validated_lean_import_closure_receipt_payload",
                    return_value=receipt,
                ),
                mock.patch(
                    "scripts.lean_signature_manifest.RepositoryBuildInputSnapshotProvider",
                    provider_type,
                ),
            ):
                error = planner._v11_lean_import_closure_current_error(
                    folder, receipt
                )

            self.assertEqual(error, "")
            provider_type.assert_called_once_with(root)
            provider.validated_repository_source_snapshot.assert_called_once_with(
                closure
            )
            provider.adopt_lean_import_closure_payload.assert_not_called()
            provider.finalize_unchanged.assert_not_called()

    def test_canonical_validator_owns_semantic_recovery_before_replanning(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            terminal_plan = {
                "schema": 2,
                "paper": "Fixture",
                "canonical_receipt_current": True,
            }
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "current_canonical_receipt_terminal_plan",
                    return_value=terminal_plan,
                ) as terminal,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            terminal.assert_called_once_with(folder)
            self.assertEqual(json.loads(output.getvalue()), terminal_plan)

    def test_import_avoids_presentation_and_historical_scheduler_modules(
        self,
    ) -> None:
        root = Path(__file__).resolve().parents[2]
        process = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import json, sys; "
                    "import scripts.closeout_reuse_plan; "
                    "print(json.dumps([name for name in ("
                    "'scripts.lean_signature_manifest', "
                    "'scripts.review_dashboard', "
                    "'scripts.review_dashboard_packet', "
                    "'scripts.semantic_audit_reuse', "
                    "'scripts.closeout_legacy_adoption', "
                    "'scripts.closeout_wave_engine') if name in sys.modules]))"
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

    def test_v11_preplan_adapter_schedules_only_typed_reducer_actions(self) -> None:
        build = planner._v11_preplan_action_schedule(
            "Fixture",
            semantic_review_current=True,
            compiled_inputs_current=False,
        )
        self.assertEqual(
            [action["id"] for action in build["actions"]],
            ["paper_build", "replan_after_build"],
        )
        self.assertFalse(build["v11_reducer"]["legacy_scheduler_consulted"])

        realization_repair = planner._v11_preplan_action_schedule(
            "Fixture",
            semantic_review_current=True,
            compiled_inputs_current=True,
            realization_receipt_preflight={
                "state": "blocked",
                "current": False,
                "errors": ["the graph omitted theorem_one"],
            },
        )
        self.assertEqual(
            [action["id"] for action in realization_repair["actions"]],
            ["resolve_realization_receipt_preflight"],
        )

        repair = planner._v11_preplan_action_schedule(
            "Fixture",
            semantic_review_current=False,
            compiled_inputs_current=True,
            semantic_errors=["one source claim needs review"],
        )
        self.assertEqual(repair["next_action"]["id"], "repair_current_v11_audit")

    def test_unclosed_legacy_paper_has_one_current_protocol_migration(self) -> None:
        plan = planner.current_protocol_migration_plan(
            "Fixture", {"ready": True, "blockers": []}
        )
        self.assertEqual(plan["next_action"]["id"], "upgrade_to_current_protocol")
        self.assertFalse(plan["historical_runtime_consulted"])
        self.assertFalse(plan["acceptance_credential"])
        self.assertTrue(
            plan["next_action"]["migration_preserves_historical_status"]
        )

    @staticmethod
    def _write_current_v11_screening(audit: Path, paper: str) -> None:
        (audit / "v11_raw_source_spec_screening.json").write_text(
            json.dumps(
                {
                    "schema": 3,
                    "paper": paper,
                    "prompt_version": V11_SCREENING_PROMPT_VERSION,
                    "validator": "fixture-reviewer",
                    "validated_at": "2026-08-27T00:00:00Z",
                    "items": {},
                }
            ),
            encoding="utf-8",
        )

    @staticmethod
    def _graph_projection(
        target_material: Mapping[str, object],
        *,
        context: object | None = None,
    ) -> object:
        retained_context = context or types.SimpleNamespace(
            v11_lean_claim_graph_selected=True
        )
        return types.SimpleNamespace(
            context=retained_context,
            target_material=lambda: target_material,
        )

    def test_fresh_v11_planner_records_lean_closure_before_review(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )

            action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "record_current_lean_import_closure")
            self.assertIn("not an acceptance credential", action["reason"])
            self.assertEqual(
                action["commands"],
                [
                    "python3 scripts/final_closure_receipt.py --paper Fixture "
                    "--record-current-lean-import-closure"
                ],
            )

    def test_fresh_v11_planner_replaces_review_only_closure_before_plan(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps(
                    {"entrypoint": "papers/Fixture/ProofInterface.lean"}
                ),
                encoding="utf-8",
            )

            action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "record_current_lean_import_closure")
            self.assertIn("paper-build closure", action["reason"])

    def test_fresh_v11_planner_replaces_stale_paper_closure_before_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}) + "\n",
                encoding="utf-8",
            )

            with mock.patch.object(
                planner,
                "_v11_lean_import_closure_current_error",
                return_value="papers/Fixture.lean changed",
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "record_current_lean_import_closure")
            self.assertIn("saved carrier is not current", action["reason"])
            self.assertIn("papers/Fixture.lean changed", action["reason"])

    def test_fresh_v11_planner_stops_before_missing_prerequisite_ledgers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "library_semantic_review.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}) + "\n", encoding="utf-8"
            )
            (folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}) + "\n",
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=None,
                ),
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(
                action["id"], "prepare_v11_lean_review_graph"
            )
            self.assertIn("claim and prerequisite surfaces", action["reason"])
            self.assertEqual(len(action["commands"]), 1)
            self.assertIn(
                "--prepare-v11-lean-review-graph",
                action["commands"][0],
            )

            (folder / "audit" / "paper_semantic_prerequisites.json").write_text(
                "{}\n", encoding="utf-8"
            )
            with (
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection(
                        {"paper_prerequisite_targets": {}}
                    ),
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_structural_refresh_required",
                    return_value=False,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_structural_refresh_required",
                    return_value=False,
                ),
            ):
                self.assertIsNone(
                    planner.current_v11_prerequisite_stage(folder).action
                )

    def test_fresh_v11_planner_separates_cache_from_reviewer_queues(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            source_map = {"items": {}}
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            (folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}) + "\n",
                encoding="utf-8",
            )
            cache = {"paper_prerequisite_targets": {"Fixture.Model": {}}}
            paper_queue = folder / "audit" / "paper_delta.json"
            library_queue = folder / "audit" / "library_delta.json"
            with (
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection(cache),
                ),
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_changed_decision_template_and_path",
                    return_value=({"items": {"Fixture.Model": {}}}, paper_queue),
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_changed_decision_template_and_path",
                    return_value=(
                        {"items": {"AppliedModelingLib.Model": {}}},
                        library_queue,
                    ),
                ),
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(
                action["id"], "emit_semantic_prerequisite_review_queues"
            )
            self.assertEqual(len(action["commands"]), 2)
            self.assertTrue(
                all("--emit-template" in command for command in action["commands"])
            )
            self.assertTrue(
                all("--changed-only" in command for command in action["commands"])
            )

    def test_existing_ledgers_do_not_bypass_changed_unified_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}),
                encoding="utf-8",
            )
            (audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}),
                encoding="utf-8",
            )
            for name in (
                "paper_semantic_prerequisites.json",
                "library_semantic_review.json",
            ):
                (audit / name).write_text("{}\n", encoding="utf-8")

            with (
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=None,
                ),
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "prepare_v11_lean_review_graph")
            self.assertEqual(len(action["commands"]), 1)

    def test_changed_graph_schedules_content_addressed_prerequisite_delta(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}),
                encoding="utf-8",
            )
            for name in (
                "paper_semantic_prerequisites.json",
                "library_semantic_review.json",
            ):
                (audit / name).write_text('{"items": {}}\n', encoding="utf-8")
            cache = {"paper_prerequisite_targets": {"Fixture.NewRoot": {}}}
            queue = audit / ("paper_semantic_prerequisite_reissue_decisions_" + "a" * 64 + ".json")

            def action() -> dict[str, object] | None:
                with (
                    mock.patch.object(
                        planner,
                        "_v11_lean_import_closure_current_error",
                        return_value="",
                    ),
                    mock.patch.object(
                        planner,
                        "load_current_v11_review_graph_projection",
                        return_value=self._graph_projection(cache),
                    ),
                    mock.patch(
                        "scripts.reissue_paper_semantic_prerequisites.current_changed_decision_template_and_path",
                        return_value=({"items": {"Fixture.NewRoot": {}}}, queue),
                    ),
                    mock.patch(
                        "scripts.reissue_library_semantic_review.current_changed_decision_template_and_path",
                        return_value=None,
                    ),
                    mock.patch(
                        "scripts.reissue_library_semantic_review.current_structural_refresh_required",
                        return_value=False,
                    ),
                ):
                    return planner.current_v11_prerequisite_stage(folder).action

            emitted = action()
            self.assertIsNotNone(emitted)
            assert emitted is not None
            self.assertEqual(emitted["id"], "emit_semantic_prerequisite_review_queues")
            self.assertEqual(len(emitted["commands"]), 1)
            self.assertIn(queue.name, emitted["commands"][0])
            self.assertIn("--changed-only", emitted["commands"][0])

            queue.write_text('{"items": {}}\n', encoding="utf-8")
            review = action()
            self.assertIsNotNone(review)
            assert review is not None
            self.assertEqual(review["id"], "review_semantic_prerequisites")
            self.assertEqual(len(review["commands"]), 1)
            self.assertIn(queue.name, review["commands"][0])

    def test_nonempty_dependency_closure_with_no_selected_paper_prerequisites_records_empty_ledger(
        self,
    ) -> None:
        """A zero selected source surface must not fall through to no-op review."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}),
                encoding="utf-8",
            )
            (audit / "library_semantic_review.json").write_text(
                '{"items": {}}\n', encoding="utf-8"
            )

            with (
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection(
                        {"paper_prerequisite_targets": {"Fixture.Internal": {}}}
                    ),
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_structural_refresh_required",
                    return_value=False,
                ),
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "record_empty_paper_prerequisite_surface")
            self.assertEqual(action["state"], "ready_now")
            self.assertEqual(len(action["commands"]), 1)
            self.assertIn("--refresh-current", action["commands"][0])

    def test_unchanged_prerequisite_rename_schedules_only_structural_refresh(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (audit / "LEAN_IMPORT_CLOSURE_RECEIPT.json").write_text(
                json.dumps({"entrypoint": "papers/Fixture.lean"}),
                encoding="utf-8",
            )
            for name in (
                "paper_semantic_prerequisites.json",
                "library_semantic_review.json",
            ):
                (audit / name).write_text('{"items": {}}\n', encoding="utf-8")
            with (
                mock.patch.object(
                    planner,
                    "_v11_lean_import_closure_current_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection({}),
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch(
                    "scripts.reissue_paper_semantic_prerequisites.current_structural_refresh_required",
                    return_value=True,
                ),
                mock.patch(
                    "scripts.reissue_library_semantic_review.current_structural_refresh_required",
                    return_value=False,
                ),
            ):
                action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "refresh_semantic_prerequisite_metadata")
            self.assertEqual(action["state"], "ready_now")
            self.assertEqual(len(action["commands"]), 1)
            self.assertIn(
                "reissue_paper_semantic_prerequisites.py", action["commands"][0]
            )
            self.assertIn("--refresh-current", action["commands"][0])

    def test_screening_repair_emits_content_addressed_queue_without_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            queue = folder / "audit" / ("v11_queue_" + "a" * 64 + ".json")
            template = {"review_material_sha256": "a" * 64, "items": {}}
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    screening_reissue,
                    "current_changed_decision_template_and_path",
                    return_value=(template, queue),
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection({"semantic_targets": {}}),
                ),
            ):
                action = planner.current_v11_screening_repair_action(
                    folder,
                    ["missing screening"],
                )

            self.assertEqual(
                action["id"], "emit_current_v11_source_spec_review_queue"
            )
            self.assertEqual(len(action["commands"]), 1)
            self.assertIn("--emit-current-template", action["commands"][0])
            self.assertIn("--v11-review-graph", action["commands"][0])

    def test_screening_repair_runs_draft_preflight_before_graph_acquisition(
        self,
    ) -> None:
        """A missing graph cannot justify skipping source/interface preflight."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=None,
                ),
            ):
                action = planner.current_v11_screening_repair_action(
                    folder,
                    ["missing raw-source prompt version"],
                )

        self.assertEqual(action["id"], "run_draft_semantic_preflight")
        self.assertEqual(action["state"], "review_required")
        self.assertEqual(len(action["commands"]), 1)
        self.assertIn("draft_semantic_preflight.py", action["commands"][0])
        self.assertNotIn("prepare-v11-lean-review-graph", action["commands"][0])

    def test_screening_repair_uses_existing_current_queue_for_review(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            queue = folder / "audit" / ("v11_queue_" + "a" * 64 + ".json")
            queue.parent.mkdir(parents=True)
            queue.write_text("{}\n", encoding="utf-8")
            template = {"review_material_sha256": "a" * 64, "items": {}}
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    screening_reissue,
                    "current_changed_decision_template_and_path",
                    return_value=(template, queue),
                ),
                mock.patch.object(
                    screening_reissue,
                    "current_decision_queue_error",
                    return_value="",
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection({"semantic_targets": {}}),
                ),
            ):
                action = planner.current_v11_screening_repair_action(
                    folder,
                    ["stale screening"],
                )

            self.assertEqual(
                action["id"], "review_current_v11_source_spec_matches"
            )
            self.assertEqual(action["state"], "review_required")
            self.assertIn(queue.name, action["commands"][0])
            self.assertNotIn("--replace-current-surface", action["commands"][0])
            self.assertIn("--v11-review-graph", action["commands"][0])

    def test_screening_repair_refreshes_only_structural_metadata_when_reusable(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    screening_reissue,
                    "current_changed_decision_template_and_path",
                    return_value=None,
                ),
                mock.patch.object(
                    planner,
                    "load_current_v11_review_graph_projection",
                    return_value=self._graph_projection({"semantic_targets": {}}),
                ),
            ):
                action = planner.current_v11_screening_repair_action(
                    folder,
                    ["stale declaration routing"],
                )

            self.assertEqual(action["id"], "repair_current_v11_screening_metadata")
            self.assertEqual(action["state"], "ready_now")
            self.assertEqual(len(action["commands"]), 1)
            self.assertIn("--refresh-current", action["commands"][0])
            self.assertIn("--v11-review-graph", action["commands"][0])

    def test_prepare_graph_command_stops_before_producer_on_failed_preflight(
        self,
    ) -> None:
        folder = Path("/tmp/papers/Fixture")
        with (
            mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
            mock.patch.object(
                planner,
                "v11_structural_graph_input_preflight",
                return_value={"current": False, "errors": ["bad route"]},
            ),
            mock.patch.object(
                planner,
                "prepare_v11_lean_review_graph",
            ) as prepare,
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            result = planner.execute_prepare_v11_lean_review_graph(folder)

        self.assertEqual(result, 2)
        prepare.assert_not_called()
        payload = json.loads(output.getvalue())
        self.assertFalse(payload["prepared"])
        self.assertIn("not ready", payload["error"])

    def test_v11_graph_preflight_requires_role_typed_source_routes(self) -> None:
        """A legacy map must stop before it can invent closure-wide review rows."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"semantic_route_schema": None}), encoding="utf-8"
            )
            with mock.patch.object(
                planner,
                "structural_obligation_preflight",
                return_value=types.SimpleNamespace(
                    projection=lambda: {
                        "acceptance_credential": False,
                        "current": True,
                        "errors": [],
                    }
                ),
            ):
                result = planner.v11_structural_graph_input_preflight(folder)

        self.assertIsNotNone(result)
        assert result is not None
        self.assertFalse(result["current"])
        self.assertIn("semantic_route_schema 2", result["errors"][0])

    def test_v11_graph_preflight_preserves_a_role_typed_route_surface(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"semantic_route_schema": 2}), encoding="utf-8"
            )
            with mock.patch.object(
                planner,
                "structural_obligation_preflight",
                return_value=types.SimpleNamespace(
                    projection=lambda: {
                        "acceptance_credential": False,
                        "current": True,
                        "errors": [],
                    }
                ),
            ):
                result = planner.v11_structural_graph_input_preflight(folder)

        self.assertIsNotNone(result)
        assert result is not None
        self.assertTrue(result["current"])
        self.assertEqual(result["errors"], [])

    def test_prepare_graph_command_invokes_one_producer_after_preflight(self) -> None:
        folder = Path("/tmp/papers/Fixture")
        prepared = {
            "schema": 1,
            "paper": "Fixture",
            "acceptance_credential": False,
            "semantic_judgments_issued": False,
        }
        with (
            mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
            mock.patch.object(
                planner,
                "v11_structural_graph_input_preflight",
                return_value={"current": True, "errors": []},
            ),
            mock.patch.object(
                planner,
                "prepare_v11_lean_review_graph",
                return_value=prepared,
            ) as prepare,
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            result = planner.execute_prepare_v11_lean_review_graph(folder)

        self.assertEqual(result, 0)
        prepare.assert_called_once_with(planner.ROOT, folder)
        payload = json.loads(output.getvalue())
        self.assertTrue(payload["prepared"])
        self.assertFalse(payload["acceptance_credential"])

    def test_correspondence_activation_uses_the_same_v11_planner_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "require_source_spec_correspondence": True
                        }
                    }
                ),
                encoding="utf-8",
            )
            source_map = {"source_spec_correspondence_schema": 1, "items": {}}
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )

            action = planner.current_v11_prerequisite_stage(folder).action

            self.assertIsNotNone(action)
            assert action is not None
            self.assertEqual(action["id"], "record_current_lean_import_closure")


    @staticmethod
    def wave_snapshot() -> dict[str, object]:
        return {
            "wave_id": "fixture-wave",
            "engine_registration": {
                "engine_tree_sha256": "a" * 64,
                "review_semantic_class_sha256": "b" * 64,
                "revision_sequence": 1,
                "relation_to_previous": "initial",
                "engine_file_count": 1,
            },
        }

    def semantic_contract_replay_fixture(
        self, root: Path, *, match_digest: str
    ) -> tuple[Path, types.SimpleNamespace]:
        """Create a canonical raw with a replayable producer diagnostic."""

        folder = root / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        (folder / "status.json").write_text("{}\n", encoding="utf-8")
        (audit / "paper_statement_map.json").write_text("{}\n", encoding="utf-8")
        (audit / "source_record_audit.json").write_text(
            json.dumps(
                {
                    "source_record_audit_sha256": "a" * 64,
                    "source_record_input_fingerprint": {"schema": 10},
                    "source_contract_association_errors": [
                        "structural replay candidate"
                    ],
                }
            ),
            encoding="utf-8",
        )
        (audit / "source_record_match_llm.json").write_text(
            json.dumps({"source_record_audit_sha256": match_digest}),
            encoding="utf-8",
        )
        # The gate context below authenticates its content. The planner only
        # considers this exceptional branch when the canonical artifact exists.
        (audit / "source_record_semantic_contract_revalidation.json").write_text(
            "{}\n", encoding="utf-8"
        )
        return (
            folder,
            types.SimpleNamespace(
                returncode=1,
                stdout=json.dumps(
                    {
                        "current": False,
                        "reason": "generated source-contract association diagnostics are nonempty",
                        "observed_source_record_audit_sha256": "a" * 64,
                        "observed_source_record_fingerprint_schema": 10,
                    }
                ),
                stderr="",
            ),
        )

    def signature_context(self, *, schema: int = 2) -> dict[str, object]:
        target = ("a" * 64, 10)
        helper = ("b" * 64, 20)
        modules = ("Fixture.Dependency", "Fixture.PaperInterface")
        context: dict[str, object] = {
            "schema": schema,
            "import_module": "Fixture.PaperInterface",
            "olean_fingerprint": list(target),
            "helper_fingerprint": list(helper),
            "audit_modules": list(modules),
            "semantic_module_fingerprints": [
                ["Fixture.Dependency", ["c" * 64, 30]],
                ["Fixture.PaperInterface", list(target)],
            ],
            "audit_scope_fingerprint": planner.lean_manifest._audit_scope_fingerprint(  # noqa: SLF001
                "Fixture.PaperInterface", target, modules
            ),
        }
        if schema == 3:
            context.update(
                {
                    "canonical_representation": (
                        planner.lean_manifest.CANONICAL_REPRESENTATION
                    ),
                    "semantic_hash_tool_identity": {
                        "schema": "1",
                        "resolved_path": "/usr/bin/sha256sum",
                        "executable_sha256": "d" * 64,
                    },
                }
            )
        return context
















    def test_semantic_ready_compiled_miss_stops_before_operational_receipt(
        self,
    ) -> None:
        """A build/replan transition cannot use a pre-build strict receipt."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "cache_reusable": True,
                "compiled_artifacts_ready": False,
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with mock.patch.object(
                planner,
                "_write_current_closeout_plan_receipt",
                side_effect=AssertionError("a pre-build receipt must not be published"),
            ) as write_receipt:
                finalized = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                )

            self.assertEqual(finalized["next_action"]["id"], "paper_build")
            self.assertEqual(
                [action["id"] for action in finalized["actions"]],
                ["paper_build", "replan_after_build"],
            )
            self.assertNotIn("plan_identity_sha256", finalized)
            write_receipt.assert_not_called()

    def test_source_only_acceptance_is_not_duplicated_in_the_planner(self) -> None:
        """Exact source gates stay mandatory in the strict worker, not here."""

        self.assertFalse(
            hasattr(planner, "_deterministic_source_closeout_preflight")
        )

    def test_terminal_documents_are_checked_only_after_build_and_correspondence(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            context = types.SimpleNamespace(status_payload={"status": "formalized"})
            base_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "cache_reusable": True,
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            terminal_blocked = {
                "ready": False,
                "errors": [
                    {
                        "path": "papers/Fixture/FINAL_VALIDATION_REPORT.md",
                        "message": "missing terminal closeout presentation artifact",
                    }
                ],
                "acceptance_credential": False,
            }

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    side_effect=AssertionError(
                        "terminal presentation must wait for a current build"
                    ),
                ) as terminal_before_build,
            ):
                before_build = planner.finalize_operational_plan(
                    {**base_plan, "compiled_artifacts_ready": False},
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=context,
                )
            self.assertEqual(before_build["next_action"]["id"], "paper_build")
            terminal_before_build.assert_not_called()

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "blocked",
                        "current": False,
                        "required": True,
                        "errors": ["the current graph omitted one realization"],
                    },
                ),
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    side_effect=AssertionError(
                        "terminal presentation must wait for correspondence"
                    ),
                ) as terminal_before_correspondence,
            ):
                before_correspondence = planner.finalize_operational_plan(
                    {**base_plan, "compiled_artifacts_ready": True},
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=context,
                )
            self.assertNotEqual(
                before_correspondence["next_action"]["id"],
                "complete_terminal_closeout_documents",
            )
            terminal_before_correspondence.assert_not_called()

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "current_graph_authority",
                        "current": True,
                        "required": True,
                    },
                ),
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value=terminal_blocked,
                ) as terminal_after_correspondence,
                mock.patch.object(
                    planner,
                    "_write_current_closeout_plan_receipt",
                    side_effect=AssertionError(
                        "terminal document failure cannot publish a plan"
                    ),
                ) as write_receipt,
            ):
                terminal = planner.finalize_operational_plan(
                    {**base_plan, "compiled_artifacts_ready": True},
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=context,
                )
            self.assertEqual(
                terminal["next_action"]["id"],
                "complete_terminal_closeout_documents",
            )
            self.assertTrue(terminal["next_action"]["after_semantic_review"])
            terminal_after_correspondence.assert_called_once_with(
                folder,
                context.status_payload,
            )
            write_receipt.assert_not_called()

    def test_terminal_documents_require_the_human_review_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            docs = folder / "docs"
            audit = folder / "audit"
            docs.mkdir(parents=True)
            audit.mkdir(parents=True)
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report\n", encoding="utf-8"
            )
            (docs / "DependencyDAG.tex").write_text("dag", encoding="utf-8")
            (docs / "DependencyDAG.pdf").write_bytes(b"%PDF-dag\n")
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"%PDF-packet\n")
            (audit / "human_review_packet_lean_cache.json").write_text(
                "{}\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "report_status_alignment_errors", return_value=[]
                ),
                mock.patch.object(
                    planner, "closeout_document_hard_errors", return_value=[]
                ),
            ):
                result = planner._terminal_presentation_closeout_preflight(
                    folder, {"status": "formalized"}
                )

        self.assertFalse(result["ready"])
        self.assertTrue(
            any(
                "HUMAN_REVIEW_PACKET.tex" in error
                and "missing terminal" in error
                for error in result["errors"]
            ),
            result,
        )

    def test_receipt_publication_disposition_controls_replan_retryability(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            base_plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            for disposition, retryable in (
                ("source_race", True),
                ("compiled_race", True),
                ("deterministic_input", False),
                ("publication_io", False),
            ):
                with self.subTest(disposition=disposition):
                    publication = planner.CloseoutPlanReceiptPublication(
                        receipt=None,
                        error="fixture publication failure",
                        disposition=disposition,
                        input_identity_sha256="a" * 64,
                    )
                    with (
                        mock.patch.object(
                            planner,
                            "current_graph_realization_preflight",
                            return_value={
                                "state": "not_applicable",
                                "current": True,
                                "required": False,
                            },
                        ),
                        mock.patch.object(
                            planner,
                            "_write_current_closeout_plan_receipt",
                            return_value=publication,
                        ),
                    ):
                        finalized = planner.finalize_operational_plan(
                            dict(base_plan),
                            folder=folder,
                            source_coverage_mode="named_theoretical_statements",
                            execution_path=folder / ".review_traces" / "worker.json",
                            static_readiness={"ready": True, "blockers": []},
                        )

                    action = finalized["next_action"]
                    self.assertEqual(action["id"], "replan_current_inputs")
                    self.assertEqual(action["publication_disposition"], disposition)
                    self.assertEqual(action["retryable"], retryable)
                    self.assertEqual(action["input_identity_sha256"], "a" * 64)

    def test_v11_plan_publication_revalidates_only_the_exact_transaction(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            strict_snapshot = {
                "papers/Fixture/audit/paper_statement_map.json": {
                    "state": "present",
                    "sha256": "a" * 64,
                }
            }
            publication_inputs = (
                planner.CloseoutPlanPublicationInputs.capture(
                    folder=folder,
                    source_ledger={},
                    compiled_ledger={},
                    strict_transaction_snapshot=strict_snapshot,
                    lean_closure_projection={"state": "present"},
                ).with_review_surfaces(
                    v11_lean_review_graph={"schema": 2},
                    final_holistic_audit_surface={
                    "identity_schema": "final-holistic-source-and-lean-semantic-surface-v1",
                    "paper": "Fixture",
                    },
                    all_selected_semantic_review_sha256="d" * 64,
                )
            )
            plan = {
                "audit_material_identity": publication_inputs.audit_material_identity,
                "audit_material_sha256": publication_inputs.audit_material_sha256,
            }
            original_plan = dict(plan)
            receipt = {"plan_identity_sha256": "b" * 64}
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    plan_publication,
                    "validate_content_input_snapshot",
                    return_value=(strict_snapshot, ""),
                ) as validate_transaction,
                mock.patch.object(
                    plan_publication,
                    "closeout_plan_input_paths",
                    return_value=([], []),
                ),
                mock.patch.object(
                    plan_publication,
                    "build_closeout_plan_receipt",
                    return_value=receipt,
                ),
                mock.patch.object(
                    plan_publication,
                    "validated_closeout_plan_receipt",
                    return_value=receipt,
                ),
            ):
                publication = planner._write_current_closeout_plan_receipt(
                    plan,
                    folder=folder,
                    deep_paper_prose=False,
                    publication_inputs=publication_inputs,
                )

            self.assertEqual(publication.disposition, "published")
            self.assertEqual(publication.receipt, receipt)
            self.assertEqual(plan, original_plan)
            validate_transaction.assert_called_once_with(root, strict_snapshot)

    def test_v11_plan_publication_rejects_a_legacy_material_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            publication_inputs = (
                planner.CloseoutPlanPublicationInputs.capture(
                    folder=folder,
                    source_ledger={},
                    compiled_ledger={},
                    strict_transaction_snapshot={},
                    lean_closure_projection={"state": "present"},
                ).with_review_surfaces(
                    v11_lean_review_graph={"schema": 2},
                    final_holistic_audit_surface={"paper": "Fixture"},
                    all_selected_semantic_review_sha256="d" * 64,
                )
            )
            plan = {
                "audit_material_identity": "legacy_sidecar_snapshot",
                "audit_material_sha256": publication_inputs.audit_material_sha256,
            }

            publication = planner._write_current_closeout_plan_receipt(
                plan,
                folder=folder,
                deep_paper_prose=False,
                publication_inputs=publication_inputs,
            )

        self.assertIsNone(publication.receipt)
        self.assertEqual(publication.disposition, "deterministic_input")
        self.assertIn("no selected semantic-transaction identity", publication.error)

    def test_publication_inputs_are_deeply_frozen_and_paper_bound(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            other = root / "papers" / "Other"
            source_ledger = {"/source.lean": [1, 2, 3, 4, 5]}
            strict_snapshot = {
                "papers/Fixture/status.json": {
                    "state": "present",
                    "sha256": "a" * 64,
                }
            }
            inputs = planner.CloseoutPlanPublicationInputs.capture(
                folder=folder,
                source_ledger=source_ledger,
                compiled_ledger={},
                strict_transaction_snapshot=strict_snapshot,
                lean_closure_projection={"state": "present"},
            ).with_review_surfaces(
                v11_lean_review_graph={"schema": 2, "paper": "Fixture"},
                final_holistic_audit_surface={"paper": "Fixture"},
                all_selected_semantic_review_sha256="d" * 64,
            )
            frozen_identity = planner._closeout_plan_publication_input_identity(
                folder=folder,
                publication_inputs=inputs,
            )

            source_ledger["/source.lean"][0] = 99
            strict_snapshot["papers/Fixture/status.json"]["sha256"] = "b" * 64
            decoded = inputs.payload["source_ledger"]
            decoded["/source.lean"][1] = 88

            self.assertEqual(
                inputs.payload["source_ledger"]["/source.lean"],
                [1, 2, 3, 4, 5],
            )
            self.assertEqual(
                planner._closeout_plan_publication_input_identity(
                    folder=folder,
                    publication_inputs=inputs,
                ),
                frozen_identity,
            )

            publication = planner._write_current_closeout_plan_receipt(
                {
                    "audit_material_identity": inputs.audit_material_identity,
                    "audit_material_sha256": inputs.audit_material_sha256,
                },
                folder=other,
                deep_paper_prose=False,
                publication_inputs=inputs,
            )

        self.assertIsNone(publication.receipt)
        self.assertEqual(publication.disposition, "deterministic_input")
        self.assertIn("another paper", publication.error)

    def test_publication_requires_the_separate_immutable_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            publication = planner._write_current_closeout_plan_receipt(
                {
                    "audit_material_identity": "strict_transaction_content_snapshot",
                    "audit_material_sha256": "a" * 64,
                },
                folder=folder,
                deep_paper_prose=False,
                publication_inputs=None,
            )

        self.assertIsNone(publication.receipt)
        self.assertEqual(publication.disposition, "deterministic_input")
        self.assertIn("immutable publication input snapshot", publication.error)

    def test_prospective_plan_does_not_repeat_terminal_receipt_validation(
        self,
    ) -> None:
        """A terminal miss remains false throughout one immutable plan."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            folder.mkdir(parents=True)
            plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "semantic_review_authoritative_lane": {
                    "required": True,
                    "ready": True,
                    "errors": [],
                    "lane": "current_v11_raw_source_to_expanded_spec",
                },
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            receipt = {
                "plan_identity_sha256": "a" * 64,
                "final_holistic_audit_surface_sha256": "c" * 64,
                "all_selected_semantic_review_sha256": "d" * 64,
                "content_inputs": {},
                "compiled_inputs": {},
            }
            publication = planner.CloseoutPlanReceiptPublication(
                receipt=receipt,
                error="",
                disposition="published",
                input_identity_sha256="b" * 64,
            )
            with (
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "not_applicable",
                        "current": True,
                        "required": False,
                    },
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "_write_current_closeout_plan_receipt",
                    return_value=publication,
                ),
                mock.patch.object(
                    planner,
                    "resolved_plan_final_holistic_audit_surface",
                    return_value={
                        "review_policy_assurance": {
                            "schema": 1,
                            "source_scope": "all_named_theory",
                            "repeat_final_scope": "main_primary",
                            "required_final_adversary_count": 2,
                        }
                    },
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_review_graph_carrier",
                    return_value={"schema": 2},
                ),
                mock.patch(
                    "scripts.current_closeout.semantic_review.current_v11_semantic_review_result",
                    return_value=mock.sentinel.semantic_review,
                ),
                mock.patch(
                    "scripts.current_closeout.semantic_review.all_selected_semantic_review_material_sha256",
                    return_value="d" * 64,
                ),
                mock.patch.object(
                    planner,
                    "build_final_holistic_audit_surface_from_repository",
                    return_value={
                        "identity_schema": (
                            "final-holistic-source-and-lean-semantic-surface-v1"
                        ),
                        "paper": "Fixture",
                    },
                ),
                mock.patch.object(
                    planner,
                    "paper_status_acceptance_projection",
                    return_value={"paper": "Fixture", "status": "formalized"},
                ),
                mock.patch.object(
                    planner,
                    "final_holistic_audit_hard_errors",
                    return_value=[],
                ) as holistic_gate,
                mock.patch.object(
                    planner,
                    "_current_closeout_stage_projection",
                    return_value={},
                ),
                mock.patch.object(
                    planner,
                    "validate_final_closure_receipt",
                    side_effect=AssertionError(
                        "prospective planning repeated terminal validation"
                    ),
                ) as validate_receipt,
                mock.patch.object(
                    planner,
                    "final_closure_receipt_error",
                    create=True,
                    side_effect=AssertionError(
                        "prospective planning restored a second receipt probe"
                    ),
                ) as receipt_error,
            ):
                finalized = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=types.SimpleNamespace(
                        source_semantic_lane=(
                            integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
                        ),
                        status_payload={"status": "formalized"},
                    ),
                )

            self.assertFalse(finalized["closeout_complete"])
            self.assertEqual(finalized["next_action"]["id"], "strict_closeout")
            self.assertEqual(
                holistic_gate.call_args.kwargs["review_policy_assurance"]
                ["required_final_adversary_count"],
                2,
            )
            validate_receipt.assert_not_called()
            receipt_error.assert_not_called()

    def test_current_v11_plan_publishes_retained_lean_graph_carrier(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            carrier = {
                "schema": 2,
                "acceptance_credential": False,
                "operational_scheduling_only": True,
                "paper": "Fixture",
            }
            plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "semantic_review_authoritative_lane": {
                    "required": True,
                    "ready": True,
                    "errors": [],
                    "lane": "current_v11_raw_source_to_expanded_spec",
                },
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            captured: dict[str, object] = {}
            publication_inputs = planner.CloseoutPlanPublicationInputs.capture(
                folder=folder,
                source_ledger={},
                compiled_ledger={},
                strict_transaction_snapshot={},
                lean_closure_projection={"state": "present"},
            )

            def publish(
                candidate: dict[str, object],
                **kwargs: object,
            ) -> object:
                captured["plan"] = dict(candidate)
                captured["publication_inputs"] = kwargs["publication_inputs"]
                return planner.CloseoutPlanReceiptPublication(
                    receipt=None,
                    error="fixture stop after graph handoff",
                    disposition="deterministic_input",
                    input_identity_sha256="a" * 64,
                )

            with (
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "not_applicable",
                        "current": True,
                        "required": False,
                    },
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_review_graph_carrier",
                    return_value=carrier,
                ) as graph_builder,
                mock.patch(
                    "scripts.current_closeout.semantic_review.current_v11_semantic_review_result",
                    return_value=mock.sentinel.semantic_review,
                ),
                mock.patch(
                    "scripts.current_closeout.semantic_review.all_selected_semantic_review_material_sha256",
                    return_value="d" * 64,
                ),
                mock.patch.object(
                    planner,
                    "build_final_holistic_audit_surface_from_repository",
                    return_value={
                        "identity_schema": (
                            "final-holistic-source-and-lean-semantic-surface-v1"
                        ),
                        "paper": "Fixture",
                    },
                ) as surface_builder,
                mock.patch.object(
                    planner,
                    "paper_status_acceptance_projection",
                    return_value={"paper": "Fixture", "status": "formalized"},
                ),
                mock.patch.object(
                    planner,
                    "_write_current_closeout_plan_receipt",
                    side_effect=publish,
                ),
            ):
                result = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    publication_inputs=publication_inputs,
                    evidence_context=types.SimpleNamespace(
                        source_semantic_lane=(
                            integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
                        ),
                        status_payload={"status": "formalized"},
                    ),
                )

            graph_builder.assert_called_once()
            surface_builder.assert_called_once()
            published_inputs = captured["publication_inputs"]
            self.assertIsInstance(
                published_inputs,
                planner.CloseoutPlanPublicationInputs,
            )
            self.assertEqual(
                published_inputs.payload["v11_lean_review_graph"],
                carrier,
            )
            self.assertEqual(
                published_inputs.payload["final_holistic_audit_surface"]["paper"],
                "Fixture",
            )
            self.assertEqual(
                published_inputs.payload["all_selected_semantic_review_sha256"],
                "d" * 64,
            )
            self.assertFalse(
                any(
                    key.startswith("_execution_")
                    for key in captured["plan"]
                )
            )
            self.assertEqual(result["next_action"]["id"], "replan_current_inputs")

    def test_current_v11_final_schedule_never_consults_legacy_adoption(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            plan_identity = "a" * 64
            plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "semantic_review_authoritative_lane": {
                    "required": True,
                    "ready": True,
                    "errors": [],
                    "lane": "current_v11_raw_source_to_expanded_spec",
                },
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            receipt = {
                "plan_identity_sha256": plan_identity,
                "final_holistic_audit_surface_sha256": "c" * 64,
                "all_selected_semantic_review_sha256": "d" * 64,
                "content_inputs": {},
                "compiled_inputs": {},
            }
            publication = planner.CloseoutPlanReceiptPublication(
                receipt=receipt,
                error="",
                disposition="published",
                input_identity_sha256="b" * 64,
            )
            context = types.SimpleNamespace(
                source_semantic_lane=integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
                status_payload={"status": "formalized"},
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "current_graph_authority",
                        "current": True,
                        "required": True,
                    },
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_review_graph_carrier",
                    return_value={"schema": 2},
                ),
                mock.patch(
                    "scripts.current_closeout.semantic_review.current_v11_semantic_review_result",
                    return_value=mock.sentinel.semantic_review,
                ),
                mock.patch(
                    "scripts.current_closeout.semantic_review.all_selected_semantic_review_material_sha256",
                    return_value="d" * 64,
                ),
                mock.patch.object(
                    planner,
                    "build_final_holistic_audit_surface_from_repository",
                    return_value={
                        "identity_schema": (
                            "final-holistic-source-and-lean-semantic-surface-v1"
                        ),
                        "paper": "Fixture",
                    },
                ),
                mock.patch.object(
                    planner,
                    "paper_status_acceptance_projection",
                    return_value={"paper": "Fixture", "status": "formalized"},
                ),
                mock.patch.object(
                    planner,
                    "_write_current_closeout_plan_receipt",
                    return_value=publication,
                ),
                mock.patch.object(
                    planner,
                    "final_holistic_audit_hard_errors",
                    return_value=[],
                ),
                mock.patch.object(
                    planner,
                    "_current_closeout_stage_projection",
                    return_value={},
                ),
            ):
                result = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=context,
                )

            self.assertEqual(result["next_action"]["id"], "strict_closeout")
            self.assertEqual(
                result["v11_reducer"],
                {
                    "action": "run_strict_closeout",
                    "worker_disposition": "absent",
                    "legacy_adoption_consulted": False,
                    "acceptance_credential": False,
                },
            )

    def test_completed_v11_graph_is_persisted_before_later_planner_stops(self) -> None:
        """A stale ledger cannot discard a graph acquisition that already passed."""

        folder = Path("/tmp") / "papers" / "Fixture"
        context = types.SimpleNamespace(
            source_semantic_lane=integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        )
        with (
            mock.patch.object(
                graph_preparation, "checkpoint_builder_issued_v11_lean_review_graph"
            ) as checkpoint,
        ):
            error = planner.persist_v11_operational_lean_graph(folder, context)

        self.assertEqual(error, "")
        checkpoint.assert_called_once_with(
            folder,
            context,
            repository_root=planner.ROOT,
        )

    def test_main_selects_v11_before_one_prerequisite_graph_stage(self) -> None:
        """The selected protocol and exact inputs feed one retained graph stage."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            status = {"status": "formalized", "review_surface": {}}
            source_map = {"semantic_contract_schema": 1, "items": {}}
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            self._write_current_v11_screening(folder / "audit", "Fixture")
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "worker.json"),
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner, "current_canonical_receipt_terminal_plan", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "current_v11_prerequisite_stage",
                    return_value=planner.CurrentV11PrerequisiteStage(
                        {
                            "id": "repair_current_v11_context",
                            "state": "ready_now",
                            "required": True,
                            "reason": "fixture graph acquisition failed",
                        },
                        None,
                    ),
                ) as graph_stage,
                mock.patch.object(
                    planner, "v11_structural_graph_input_preflight", return_value=None
                ),
                mock.patch.object(
                    planner, "_raw_source_spec_screening_requested", return_value=True
                ) as selected,
                mock.patch.object(
                    planner, "persist_v11_operational_lean_graph", return_value=""
                ) as persist,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

        self.assertEqual(result, 0)
        selected.assert_called_once_with(folder, status, source_map)
        graph_stage.assert_called_once_with(
            folder,
            status_payload=status,
            source_map_payload=source_map,
        )
        persist.assert_not_called()
        emitted = json.loads(output.getvalue())
        self.assertEqual(emitted["next_action"]["id"], "repair_current_v11_context")
        self.assertFalse(emitted["legacy_planner_consulted"])
        self.assertIn("fixture graph acquisition failed", emitted["next_action"]["reason"])

    def test_missing_screening_records_import_closure_before_graph_acquisition(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            status = {"status": "formalized", "review_surface": {}}
            source_map = {"semantic_contract_schema": 1, "items": {}}
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            closure_action = {
                "id": "record_current_lean_import_closure",
                "state": "ready_now",
                "required": True,
                "reason": "record the portable Lean import closure first",
                "commands": ["record-closure"],
            }
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "worker.json"),
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner, "current_canonical_receipt_terminal_plan", return_value=None
                ),
                mock.patch.object(
                    planner, "v11_structural_graph_input_preflight", return_value=None
                ),
                mock.patch.object(
                    planner, "_raw_source_spec_screening_requested", return_value=True
                ),
                mock.patch.object(
                    planner,
                    "current_v11_import_closure_action",
                    return_value=closure_action,
                ) as closure_stage,
                mock.patch.object(
                    planner,
                    "current_v11_screening_repair_action",
                    side_effect=AssertionError("screening queue opened before closure"),
                ) as repair,
                mock.patch.object(
                    planner,
                    "current_v11_prerequisite_stage",
                    side_effect=AssertionError("graph stage opened before closure"),
                ) as graph_stage,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

        self.assertEqual(result, 0)
        closure_stage.assert_called_once_with(folder)
        repair.assert_not_called()
        graph_stage.assert_not_called()
        emitted = json.loads(output.getvalue())
        self.assertEqual(
            emitted["next_action"]["id"], "record_current_lean_import_closure"
        )
        self.assertEqual(emitted["next_action"]["commands"], ["record-closure"])

    def test_invalid_v11_screening_uses_current_queue_before_graph_reacquisition(
        self,
    ) -> None:
        """A saved-container error uses the prepared graph and exact queue."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            status = {"status": "formalized", "review_surface": {}}
            source_map = {"semantic_contract_schema": 1, "items": {}}
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            (audit / "v11_raw_source_spec_screening.json").write_text(
                json.dumps({"schema": 2, "paper": "Fixture"}),
                encoding="utf-8",
            )
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "worker.json"),
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner, "current_canonical_receipt_terminal_plan", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "current_v11_prerequisite_stage",
                    side_effect=AssertionError("review graph stage ran"),
                ) as graph_stage,
                mock.patch.object(
                    planner, "v11_structural_graph_input_preflight", return_value=None
                ),
                mock.patch.object(
                    planner, "_raw_source_spec_screening_requested", return_value=True
                ),
                mock.patch.object(
                    planner,
                    "current_v11_import_closure_action",
                    return_value=None,
                ) as closure_stage,
                mock.patch.object(
                    planner,
                    "current_v11_screening_repair_action",
                    return_value={
                        "id": "emit_current_v11_source_spec_review_queue",
                        "state": "ready_now",
                        "required": True,
                        "reason": "unsupported schema or paper identity",
                        "commands": ["emit-current-queue"],
                    },
                ) as repair,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

        self.assertEqual(result, 0)
        closure_stage.assert_called_once_with(folder)
        graph_stage.assert_not_called()
        repair.assert_called_once()
        emitted = json.loads(output.getvalue())
        self.assertEqual(
            emitted["next_action"]["id"],
            "emit_current_v11_source_spec_review_queue",
        )
        self.assertFalse(emitted["legacy_planner_consulted"])
        self.assertFalse(emitted["screening_container_preflight"]["current"])
        self.assertIn(
            "unsupported schema or paper identity",
            emitted["next_action"]["reason"],
        )

    def test_selected_v11_failure_never_enters_legacy_dashboard_planner(self) -> None:
        """The current protocol reports its own repair boundary and stops."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            status = {"status": "formalized", "review_surface": {}}
            source_map = {"semantic_contract_schema": 1, "items": {}}
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            self._write_current_v11_screening(audit, "Fixture")
            context = types.SimpleNamespace(
                source_semantic_lane=integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
                v11_lean_claim_graph_selected=True,
            )
            output = io.StringIO()
            with contextlib.ExitStack() as stack:
                stack.enter_context(
                    mock.patch.object(
                        sys,
                        "argv",
                        ["closeout_reuse_plan.py", "--paper", "Fixture"],
                    )
                )
                stack.enter_context(mock.patch.object(planner, "ROOT", root))
                stack.enter_context(
                    mock.patch.object(
                        planner, "resolve_paper_folder", return_value=folder
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "running_execution_summary", return_value=None
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "effective_closeout_execution_state",
                        return_value=(None, "", "worker", folder / "worker.json"),
                    )
                )
                for name, value in {
                    "runtime_engine_registration_error": "",
                    "_paper_closeout_status_preflight": ("formalized", ""),
                    "static_closeout_readiness": {"ready": True, "blockers": []},
                    "current_canonical_receipt_terminal_plan": None,
                    "current_v11_prerequisite_stage": (
                        planner.CurrentV11PrerequisiteStage(None, context)
                    ),
                    "v11_structural_graph_input_preflight": None,
                    "_raw_source_spec_screening_requested": True,
                    "source_coverage_mode_from_map": (
                        "named_theoretical_statements",
                        "",
                    ),
                }.items():
                    stack.enter_context(
                        mock.patch.object(planner, name, return_value=value)
                    )
                migration = stack.enter_context(
                    mock.patch.object(
                        planner,
                        "current_protocol_migration_plan",
                        side_effect=AssertionError(
                            "selected v11 planning entered the migration path"
                        ),
                    )
                )
                operation_order: list[str] = []
                live_plan = stack.enter_context(
                    mock.patch.object(
                        planner,
                        "current_v11_live_lean_operational_plan",
                        side_effect=lambda *args, **kwargs: (
                            operation_order.append("audit")
                            or (
                                None,
                                ["library prerequisite judgment is stale"],
                            )
                        ),
                    )
                )
                persist = stack.enter_context(
                    mock.patch.object(
                        planner,
                        "persist_v11_operational_lean_graph",
                        side_effect=lambda *args, **kwargs: (
                            operation_order.append("persist") or ""
                        ),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "current_v11_raw_source_spec_screening_findings",
                        return_value=[],
                    )
                )
                stack.enter_context(contextlib.redirect_stdout(output))
                result = planner.main()

        self.assertEqual(result, 0)
        emitted = json.loads(output.getvalue())
        self.assertEqual(emitted["current_protocol"], "v11_graph_native")
        self.assertFalse(emitted["legacy_planner_consulted"])
        self.assertEqual(emitted["next_action"]["id"], "repair_current_v11_audit")
        self.assertEqual(
            emitted["invalidation_reasons"],
            ["library prerequisite judgment is stale"],
        )
        migration.assert_not_called()
        live_plan.assert_called_once()
        persist.assert_called_once_with(folder, context)
        self.assertEqual(operation_order, ["audit", "persist"])

    def test_v11_graph_persistence_failure_is_visible_but_nonaccepting(self) -> None:
        folder = Path("/tmp") / "papers" / "Fixture"
        context = types.SimpleNamespace(
            source_semantic_lane=integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        )
        with mock.patch.object(
            graph_preparation,
            "checkpoint_builder_issued_v11_lean_review_graph",
            side_effect=ValueError("fixture checkpoint failure"),
        ):
            error = planner.persist_v11_operational_lean_graph(folder, context)

        self.assertEqual(error, "fixture checkpoint failure")

    def test_current_v11_plan_stops_instead_of_repeating_missing_graph(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "semantic_review_authoritative_lane": {
                    "required": True,
                    "ready": True,
                    "errors": [],
                    "lane": "current_v11_raw_source_to_expanded_spec",
                },
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with (
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner,
                    "current_graph_realization_preflight",
                    return_value={
                        "state": "not_applicable",
                        "current": True,
                        "required": False,
                    },
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_review_graph_carrier",
                    side_effect=ValueError("fixture missing retained graph"),
                ),
                mock.patch.object(
                    planner,
                    "_write_current_closeout_plan_receipt",
                ) as write_receipt,
            ):
                result = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                    evidence_context=types.SimpleNamespace(
                        source_semantic_lane=(
                            integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
                        ),
                        status_payload={"status": "formalized"},
                    ),
                )

            self.assertEqual(
                result["next_action"]["id"],
                "resolve_current_v11_lean_review_graph",
            )
            self.assertIn("fixture missing retained graph", result["next_action"]["reason"])
            self.assertEqual(result["plan_identity_sha256"], "")
            write_receipt.assert_not_called()






    def test_recovery_error_stops_before_static_or_manifest_planning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            state_path = folder / ".review_traces" / "paper_closeout_worker.json"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner, "running_execution_summary", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(
                        None,
                        "abandoned worker has no correlated child",
                        "worker_recovery_required",
                        state_path,
                    ),
                ),
                mock.patch.object(planner, "static_closeout_readiness") as readiness,
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["expensive_planning_deferred"])
            self.assertEqual(emitted["next_action"]["id"], "inspect_closeout_recovery")
            readiness.assert_not_called()
            migration.assert_not_called()

    def test_unregistered_engine_stops_before_static_or_manifest_planning(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner, "running_execution_summary", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(planner, "static_closeout_readiness") as readiness,
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["expensive_planning_deferred"])
            self.assertEqual(
                emitted["next_action"]["id"], "inspect_engine_registration"
            )
            readiness.assert_not_called()
            migration.assert_not_called()

    def test_current_canonical_receipt_stops_before_semantic_replanning(self) -> None:
        """A closed paper validates its receipt and has no planner work."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            receipt_path = folder / "FINAL_CLOSURE_RECEIPT.md"
            receipt_path.write_text("current canonical receipt\n", encoding="utf-8")
            closure = types.SimpleNamespace(
                path=receipt_path,
                payload={
                    "evidence_lane": "raw-source-record",
                    "closed_at": "2026-08-23",
                },
            )
            readiness_payload = {"ready": True, "blockers": []}
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ) as engine_preflight,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner, "validate_final_closure_receipt", return_value=closure
                ) as validate_receipt,
                mock.patch.object(
                    planner, "load_final_closure_receipt", return_value=closure
                ),
                mock.patch.object(
                    planner, "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["canonical_receipt_current"])
            self.assertTrue(emitted["closeout_complete"])
            self.assertFalse(emitted["requires_fresh_strict_closeout"])
            self.assertFalse(
                emitted["terminal_receipt_fast_path"]
                ["semantic_planner_reconstructed"]
            )
            self.assertIsNone(emitted["next_action"])
            self.assertEqual(emitted["actions"], [])
            validate_receipt.assert_called_once_with(root, "Fixture")
            engine_preflight.assert_not_called()
            readiness.assert_not_called()
            migration.assert_not_called()

    def test_current_receipt_preserves_acceptance_but_schedules_missing_documents(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            receipt = folder / "FINAL_CLOSURE_RECEIPT.md"
            receipt.write_text("accepted\n", encoding="utf-8")
            (folder / "status.json").write_text('{"status":"formalized"}', encoding="utf-8")
            closure = types.SimpleNamespace(path=receipt, payload={"schema": 6})
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "load_final_closure_receipt", return_value=closure
                ),
                mock.patch.object(planner, "validate_final_closure_receipt", return_value=closure),
                mock.patch.object(
                    planner,
                    "current_document_semantic_basis_sha256",
                    return_value="d" * 64,
                ) as semantic_basis,
                mock.patch.object(
                    planner, "_terminal_presentation_closeout_preflight",
                    return_value={"ready": False, "errors": ["missing clarification memo"]},
                ) as documents,
                mock.patch.object(planner, "static_closeout_readiness") as semantic_planner,
            ):
                plan = planner.current_canonical_receipt_terminal_plan(folder)
            self.assertEqual(semantic_basis.call_count, 2)
            semantic_basis.assert_has_calls(
                [
                    mock.call(folder, accepted_graph_only=True),
                    mock.call(folder, accepted_graph_only=True),
                ]
            )
            documents.assert_called_once_with(
                folder,
                {"status": "formalized"},
                all_selected_semantic_review_sha256="d" * 64,
            )
            semantic_planner.assert_not_called()
            self.assertTrue(plan["canonical_receipt_current"])
            self.assertFalse(plan["closeout_complete"])
            self.assertFalse(plan["requires_fresh_strict_closeout"])
            self.assertFalse(plan["readiness_matrix"]["ready"])
            action = plan["next_action"]
            self.assertEqual(action["id"], "complete_terminal_closeout_documents")
            self.assertTrue(action["preserves_current_lean_graph"])
            self.assertTrue(action["preserves_current_semantic_review"])
            self.assertEqual(plan["actions"], [action])

    def test_accepted_fast_path_compares_current_document_semantic_basis(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            docs = folder / "docs"
            audit = folder / "audit"
            docs.mkdir(parents=True)
            audit.mkdir(parents=True)
            receipt = folder / "FINAL_CLOSURE_RECEIPT.md"
            receipt.write_text("accepted\n", encoding="utf-8")
            (folder / "status.json").write_text(
                '{"status":"formalized"}', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## 9. DAG Audit\n"
                "The rendered PDF was visually inspected for readability and overlap.\n",
                encoding="utf-8",
            )
            for path in (
                docs / "DependencyDAG.tex",
                docs / "HUMAN_REVIEW_PACKET.tex",
            ):
                path.write_text("reader artifact\n", encoding="utf-8")
            for path in (
                docs / "DependencyDAG.pdf",
                docs / "HUMAN_REVIEW_PACKET.pdf",
            ):
                path.write_bytes(b"%PDF-reader\n")
            (audit / "human_review_packet_lean_cache.json").write_text(
                "{}\n", encoding="utf-8"
            )
            closure = types.SimpleNamespace(path=receipt, payload={"schema": 6})
            recorded_basis = "d" * 64

            def coverage_errors(_folder, *, expected_all_selected_semantic_review_sha256):
                if expected_all_selected_semantic_review_sha256 == recorded_basis:
                    return ()
                return (
                    "report clarification inventory is stale for the current "
                    "all-selected semantic review",
                )

            for current_basis, expected_complete in (
                (recorded_basis, True),
                ("e" * 64, False),
            ):
                with (
                    self.subTest(current_basis=current_basis),
                    mock.patch.object(planner, "ROOT", root),
                    mock.patch.object(
                        planner, "load_final_closure_receipt", return_value=closure
                    ),
                    mock.patch.object(
                        planner, "validate_final_closure_receipt", return_value=closure
                    ),
                    mock.patch.object(
                        planner,
                        "current_document_semantic_basis_sha256",
                        return_value=current_basis,
                    ),
                    mock.patch.object(
                        planner, "report_status_alignment_errors", return_value=[]
                    ),
                    mock.patch(
                        "scripts.closeout_document_gates.final_report_section_errors",
                        return_value=(),
                    ),
                    mock.patch(
                        "scripts.closeout_document_gates."
                        "reader_facing_result_label_errors",
                        return_value=(),
                    ),
                    mock.patch(
                        "scripts.closeout_document_gates."
                        "current_approved_review_context_report_errors",
                        return_value=(),
                    ),
                    mock.patch(
                        "scripts.closeout_document_gates.report_memo_coverage_errors",
                        side_effect=coverage_errors,
                    ) as coverage,
                    mock.patch(
                        "scripts.closeout_document_gates."
                        "current_human_review_packet_errors",
                        return_value=(),
                    ),
                    mock.patch.object(
                        lean_review_graph,
                        "build_v11_lean_review_graph_material",
                        side_effect=AssertionError("native Lean graph acquisition attempted"),
                    ) as graph_builder,
                    mock.patch(
                        "scripts.obligation_closure_credential."
                        "revalidate_terminal_lean_semantics",
                        side_effect=AssertionError("native Lean recovery attempted"),
                    ) as recovery,
                ):
                    plan = planner.current_canonical_receipt_terminal_plan(folder)

                self.assertEqual(plan["closeout_complete"], expected_complete)
                self.assertEqual(
                    plan["readiness_matrix"]["ready"], expected_complete
                )
                coverage.assert_called_once_with(
                    folder,
                    expected_all_selected_semantic_review_sha256=current_basis,
                )
                graph_builder.assert_not_called()
                recovery.assert_not_called()
                if expected_complete:
                    self.assertIsNone(plan["next_action"])
                else:
                    self.assertEqual(
                        plan["next_action"]["id"],
                        "complete_terminal_closeout_documents",
                    )

    def test_stale_canonical_receipt_falls_through_to_normal_planning(self) -> None:
        """Receipt errors are never converted into terminal acceptance."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "load_final_closure_receipt",
                    return_value=types.SimpleNamespace(
                        path=folder / "FINAL_CLOSURE_RECEIPT.md",
                        payload={"schema": 4},
                    ),
                ),
                mock.patch.object(
                    planner,
                    "validate_final_closure_receipt",
                    side_effect=planner.FinalClosureReceiptError("stale map"),
                ),
            ):
                terminal = planner.current_canonical_receipt_terminal_plan(
                    folder,
                )
            self.assertIsNone(terminal)

    def test_accepted_fast_path_stale_exact_closure_cannot_enter_recovery(
        self,
    ) -> None:
        folder = Path("/tmp/papers/Fixture")
        candidate = types.SimpleNamespace(
            path=folder / "FINAL_CLOSURE_RECEIPT.md",
            payload={"schema": 6},
        )
        with (
            mock.patch.object(
                planner,
                "load_final_closure_receipt",
                return_value=candidate,
            ),
            mock.patch.object(
                planner,
                "current_document_semantic_basis_sha256",
                side_effect=ValueError("build leaf Lean import closure is stale"),
            ) as semantic_basis,
            mock.patch.object(
                planner,
                "validate_final_closure_receipt",
                side_effect=AssertionError("receipt recovery path was reached"),
            ) as validate_receipt,
            mock.patch(
                "scripts.obligation_closure_credential."
                "revalidate_terminal_lean_semantics",
                side_effect=AssertionError("native Lean recovery was reached"),
            ) as recovery,
        ):
            result = planner.current_canonical_receipt_terminal_plan(folder)

        self.assertIsNone(result)
        semantic_basis.assert_called_once_with(
            folder,
            accepted_graph_only=True,
        )
        validate_receipt.assert_not_called()
        recovery.assert_not_called()

    def test_receipt_schema_change_cannot_bypass_document_basis(self) -> None:
        folder = Path("/tmp/papers/Fixture")
        path = folder / "FINAL_CLOSURE_RECEIPT.md"
        candidate = types.SimpleNamespace(path=path, payload={"schema": 4})
        validated = types.SimpleNamespace(path=path, payload={"schema": 6})
        with (
            mock.patch.object(
                planner,
                "load_final_closure_receipt",
                return_value=candidate,
            ),
            mock.patch.object(
                planner,
                "validate_final_closure_receipt",
                return_value=validated,
            ),
            mock.patch.object(
                planner,
                "current_document_semantic_basis_sha256",
                side_effect=AssertionError("schema-4 candidate requested graph basis"),
            ) as semantic_basis,
            mock.patch.object(
                planner,
                "_terminal_presentation_closeout_preflight",
                side_effect=AssertionError("changed receipt reached document fast path"),
            ) as documents,
        ):
            result = planner.current_canonical_receipt_terminal_plan(folder)

        self.assertIsNone(result)
        semantic_basis.assert_not_called()
        documents.assert_not_called()

    def test_semantic_basis_change_during_document_check_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            path = folder / "FINAL_CLOSURE_RECEIPT.md"
            closure = types.SimpleNamespace(path=path, payload={"schema": 6})
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("accepted\n", encoding="utf-8")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "load_final_closure_receipt",
                    return_value=closure,
                ),
                mock.patch.object(
                    planner,
                    "validate_final_closure_receipt",
                    return_value=closure,
                ),
                mock.patch.object(
                    planner,
                    "current_document_semantic_basis_sha256",
                    side_effect=("d" * 64, "e" * 64),
                ) as semantic_basis,
                mock.patch.object(
                    planner,
                    "_terminal_presentation_closeout_preflight",
                    return_value={"ready": True, "errors": []},
                ) as documents,
                mock.patch.object(
                    lean_review_graph,
                    "build_v11_lean_review_graph_material",
                    side_effect=AssertionError(
                        "native Lean graph acquisition attempted"
                    ),
                ) as graph_builder,
                mock.patch(
                    "scripts.obligation_closure_credential."
                    "revalidate_terminal_lean_semantics",
                    side_effect=AssertionError("native Lean recovery attempted"),
                ) as recovery,
            ):
                result = planner.current_canonical_receipt_terminal_plan(folder)

            self.assertIsNone(result)
            self.assertEqual(semantic_basis.call_count, 2)
            documents.assert_called_once_with(
                folder,
                None,
                all_selected_semantic_review_sha256="d" * 64,
            )
            graph_builder.assert_not_called()
            recovery.assert_not_called()

    def test_ineligible_status_stops_before_exact_intake_readiness(self) -> None:
        """An unclosed conditional disposition stops before an intake scan."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": True, "blockers": []}
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("conditional", "not eligible"),
                ),
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["next_action"]["id"], "resolve_paper_closeout_eligibility"
            )
            readiness.assert_called_once_with(
                folder,
                include_intake=False,
                require_terminal_documents=False,
            )

    def test_diagnose_reports_static_readiness_for_unregistered_engine(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": False, "blockers": ["missing map"]}
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(
                emitted["next_action"]["id"], "commit_registered_engine_transition"
            )
            self.assertEqual(emitted["readiness_matrix"], readiness_payload)
            readiness.assert_called_once_with(
                folder,
                include_intake=False,
                require_terminal_documents=False,
            )
            migration.assert_not_called()

    def test_diagnose_aggregates_engine_and_status_blockers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["paper_status"], "partially formalized")
            self.assertEqual(
                [action["id"] for action in emitted["actions"]],
                [
                    "commit_registered_engine_transition",
                ],
            )
            migration.assert_not_called()

    def test_diagnose_keeps_execution_disposition_and_static_blockers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner,
                    "running_execution_summary",
                    return_value={"state": "running"},
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(
                        None,
                        "abandoned worker has no correlated child",
                        "worker_recovery_required",
                        folder / ".review_traces" / "worker.json",
                    ),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["closeout_start_disposition"], "already_running")
            self.assertEqual(
                [action["id"] for action in emitted["actions"]],
                [
                    "inspect_active_closeout",
                    "inspect_closeout_recovery",
                    "commit_registered_engine_transition",
                ],
            )
            migration.assert_not_called()

    def test_diagnose_never_falls_through_to_semantic_planning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": True, "blockers": []}
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "current_protocol_migration_plan"
                ) as migration,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["next_action"]["id"], "run_frozen_closeout_planner")
            readiness.assert_called_once_with(
                folder,
                include_intake=False,
                require_terminal_documents=False,
            )
            migration.assert_not_called()
































    def test_current_planner_exposes_no_legacy_raw_producer_route(self) -> None:
        retired = (
            "fast_saved_source_record_preflight",
            "source_record_preflight_action",
            "execute_freeze_then_raw_reissue",
            "reset_closeout_wave_engine_snapshot_for_paper",
            "raw_reissue_operation_status",
            "acknowledge_stale_raw_reissue_operation",
        )
        for name in retired:
            with self.subTest(name=name):
                self.assertFalse(hasattr(planner, name))

        root = Path(__file__).resolve().parents[2]
        process = subprocess.run(
            [sys.executable, "scripts/closeout_reuse_plan.py", "--help"],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        for option in (
            "--execute-freeze-raw-reissue",
            "--reset-closeout-wave-engine-snapshot",
            "--raw-reissue-status",
            "--acknowledge-stale-raw-reissue-operation",
        ):
            with self.subTest(option=option):
                self.assertNotIn(option, process.stdout)

    def test_closeout_status_preflight_rejects_unrecognized_favorable_prefix(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "status.json").write_text(
                '{"status": "formalized-but-unverified"}\n', encoding="utf-8"
            )
            status, error = planner._paper_closeout_status_preflight(folder)
        self.assertEqual(status, "formalized-but-unverified")
        self.assertIn("not eligible", error)

    def test_closeout_status_preflight_accepts_partial_boundary(self) -> None:
        """A partial proof boundary closes its reviewed scope honestly."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            status, error = planner._paper_closeout_status_preflight(folder)

        self.assertEqual(status, "partially formalized")
        self.assertEqual(error, "")
















    def test_all_items_output_never_receives_execution_snapshots(self) -> None:
        plan = {
            "paper": "Fixture",
            "statement": {"row": {"reusable": False}},
        }

        output = planner.operator_plan_for_output(
            plan, "Fixture", all_items=True
        )

        self.assertEqual(output, plan)
        self.assertFalse(any(key.startswith("_execution_") for key in plan))




    def test_current_v11_lane_requires_the_selected_transaction_verdict(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "require_source_spec_correspondence": True,
                        },
                    }
                ),
                encoding="utf-8",
            )
            context = object()
            with mock.patch.object(
                planner,
                "current_v11_direct_semantic_review_state",
                return_value=(False, "one exact source-to-Spec row is stale"),
            ) as v11_state:
                lane = planner.current_v11_source_spec_semantic_lane(
                    folder,
                    source_map={},
                    evidence_context=context,
                )

        self.assertTrue(lane["required"])
        self.assertFalse(lane["ready"])
        self.assertEqual(lane["validation_lane"], "shared_evidence_run_context")
        self.assertEqual(lane["errors"], ["one exact source-to-Spec row is stale"])
        v11_state.assert_called_once_with(planner.ROOT, folder, context=context)
    def test_current_v11_lane_reuses_strict_context_without_card_rebuild(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "require_source_spec_correspondence": True,
                        },
                    }
                ),
                encoding="utf-8",
            )
            context = object()
            with mock.patch.object(
                planner,
                "current_v11_direct_semantic_review_state",
                return_value=(True, ""),
            ) as v11_state:
                lane = planner.current_v11_source_spec_semantic_lane(
                    folder,
                    source_map={},
                    evidence_context=context,
                )

        self.assertTrue(lane["ready"])
        self.assertEqual(lane["validation_lane"], "shared_evidence_run_context")
        v11_state.assert_called_once_with(planner.ROOT, folder, context=context)

    def test_current_v11_live_plan_does_not_require_dashboard_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            provider = mock.Mock()
            provider.finalize_unchanged.return_value = True
            source = root / "papers" / "Fixture.lean"
            compiled = root / ".lake" / "Fixture.olean"
            source_guard = (1, 2, 3, 4, 5)
            compiled_guard = (6, 7, 8, 9, 10)
            lane = {
                "required": True,
                "ready": True,
                "lane": planner.V11_SOURCE_SPEC_SEMANTIC_LANE,
                "errors": [],
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "current_v11_source_spec_semantic_lane",
                    return_value=lane,
                ),
                mock.patch.object(
                    primary_gate_transaction,
                    "current_route_schema_preflight_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    planner,
                    "_strict_transaction_content_snapshot",
                    return_value=({}, ""),
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_operational_provider",
                    return_value=provider,
                ),
                mock.patch.object(
                    planner,
                    "_root_import_closure_mutation_snapshots",
                    return_value=(
                        {str(source): source_guard},
                        {str(compiled): compiled_guard},
                        [],
                        {"schema": 1},
                    ),
                ),
                mock.patch.object(
                    planner,
                    "build_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                acquisition, errors = planner.current_v11_live_lean_operational_plan(
                    folder,
                    source_map={},
                    evidence_context=object(),
                )

        self.assertEqual(errors, [])
        assert acquisition is not None
        assert acquisition.publication_inputs is not None
        plan = acquisition.plan
        self.assertTrue(plan["compiled_artifacts_ready"])
        self.assertTrue(planner._semantic_review_is_authoritatively_covered(plan))
        self.assertFalse(
            plan["planner_compatibility"]["dashboard_manifest_required"]
        )
        self.assertEqual(
            plan["audit_material_identity"],
            "strict_transaction_content_snapshot",
        )
        self.assertEqual(
            acquisition.publication_inputs.payload["source_ledger"],
            {str(source): list(source_guard)},
        )
        self.assertEqual(
            acquisition.publication_inputs.payload["compiled_ledger"],
            {str(compiled): list(compiled_guard)},
        )
        self.assertFalse(any(key.startswith("_execution_") for key in plan))

    def test_current_v11_live_plan_stops_before_closure_for_frozen_configuration(
        self,
    ) -> None:
        """Routing/configuration defects cannot consume a build or terminal audit."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            lane = {
                "required": True,
                "ready": True,
                "lane": planner.V11_SOURCE_SPEC_SEMANTIC_LANE,
                "errors": [],
            }
            finding = types.SimpleNamespace(
                severity="ERROR",
                message="`Fixture` frozen closeout configuration preflight: stale row",
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "current_v11_source_spec_semantic_lane",
                    return_value=lane,
                ),
                mock.patch.object(
                    primary_gate_transaction,
                    "current_route_schema_preflight_findings",
                    return_value=[finding],
                ),
                mock.patch.object(
                    planner,
                    "builder_issued_v11_lean_operational_provider",
                    side_effect=AssertionError("closure must not be read"),
                ),
            ):
                acquisition, errors = planner.current_v11_live_lean_operational_plan(
                    folder,
                    source_map={},
                    evidence_context=object(),
                )

        self.assertIsNone(acquisition)
        self.assertEqual(errors, [finding.message])

    def test_frozen_configuration_preflight_includes_source_fidelity_schema(
        self,
    ) -> None:
        """A malformed fidelity ledger stops planning before the build lane."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            context = self._issued_v11_context(folder)
            schema_finding = types.SimpleNamespace(
                severity="ERROR",
                path=folder / "audit" / "source_proof_fidelity.json",
                message="defects[0].defect_kind must use the controlled vocabulary",
            )
            with (
                mock.patch.object(
                    primary_gate_transaction,
                    "current_source_spec_correspondence_inventory_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    source_validation,
                    "repaired_source_defect_route_preflight_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    source_validation,
                    "source_proof_fidelity_findings",
                    return_value=[schema_finding],
                ) as fidelity,
                mock.patch.object(
                    primary_gate_transaction,
                    "current_v11_primary_gate_result",
                    return_value=types.SimpleNamespace(
                        configuration_errors=(), structure_errors=()
                    ),
                ),
            ):
                findings = primary_gate_transaction.current_route_schema_preflight_findings(
                    root, folder, context=context
                )

        self.assertEqual(len(findings), 1)
        self.assertIn("controlled vocabulary", findings[0].message)
        fidelity.assert_called_once_with(
            folder,
            "formalized",
            context.status_payload,
            require_source_bytes=False,
            context=context,
        )


    def test_current_planner_has_no_legacy_semantic_material_selector(self) -> None:
        self.assertFalse(hasattr(planner, "legacy_semantic_audit_material_paths"))
        self.assertFalse(hasattr(planner, "_file_material_snapshot"))
        self.assertFalse(hasattr(planner, "_review_dashboard_module"))
        self.assertFalse(hasattr(planner, "_review_dashboard_packet_module"))
    def test_static_readiness_never_lexes_lean_placeholders(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "FINAL_VALIDATION_REPORT.md",
                "docs/DependencyDAG.tex",
                "docs/DependencyDAG.pdf",
            ):
                (folder / relative).write_text("{}", encoding="utf-8")
            (folder / "docs" / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\n"
                "This is an independent source-first audit and does not merely "
                "summarize existing sidecars.\n"
                "It constructs a source inventory from the source itself and compares "
                "the Lean interface for omissions, hidden strengthening/weakening, "
                "and semantic mismatches.\n",
                encoding="utf-8",
            )
            (folder / "PaperInterface.lean").write_text(
                "/- sorry in a comment -/\ntheorem ready : True := by trivial\n",
                encoding="utf-8",
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    intake_freeze,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                readiness = planner.static_closeout_readiness(
                    folder,
                    require_terminal_documents=False,
                )
            self.assertTrue(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["source_intake_boundary"]["state"],
                "legacy_not_configured",
            )

            (folder / "PaperInterface.lean").write_text(
                "theorem blocked : True := by sorry\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    intake_freeze,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                readiness = planner.static_closeout_readiness(folder)
            self.assertTrue(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["paper_local_proof_surface"]["state"],
                "deferred_to_lean_graph_and_focused_build",
            )
            self.assertFalse(
                readiness["lanes"]["paper_local_proof_surface"][
                    "python_lean_source_parsing"
                ]
            )

    def test_evidence_readiness_defers_terminal_report_and_dag_products(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                '{"items": {}}\n', encoding="utf-8"
            )
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            intake_result = {
                "ready": True,
                "state": "current",
                "errors": [],
                "acceptance_credential": False,
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "source_intake_readiness",
                    return_value=intake_result,
                ) as intake,
                mock.patch.object(
                    planner, "_static_closeout_document_hard_errors"
                ) as document_gate,
            ):
                evidence_readiness = planner.static_closeout_readiness(
                    folder,
                    require_terminal_documents=False,
                )

            self.assertTrue(evidence_readiness["ready"])
            self.assertEqual(
                evidence_readiness["lanes"]["required_artifacts"]["missing"], []
            )
            terminal = evidence_readiness["lanes"][
                "terminal_presentation_artifacts"
            ]
            self.assertFalse(terminal["ready"])
            self.assertFalse(terminal["required_now"])
            self.assertEqual(
                terminal["state"], "deferred_until_terminal_closeout"
            )
            self.assertEqual(len(terminal["missing"]), 3)
            self.assertEqual(
                evidence_readiness["lanes"]["strict_closeout_documents"]["state"],
                "deferred_until_terminal_closeout",
            )
            intake.assert_called_once_with(folder, repository_root=root)
            document_gate.assert_not_called()

            with (
                mock.patch.object(planner, "ROOT", root),
            ):
                terminal_readiness = planner.static_closeout_readiness(folder)
            self.assertFalse(terminal_readiness["ready"])
            self.assertTrue(
                any(
                    "missing required closeout artifact" in blocker
                    for blocker in terminal_readiness["blockers"]
                )
            )

    def test_static_named_support_triage_is_bounded_noncertifying_and_producer_free(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "status.json").write_text('{"status": "formalized"}')
            (folder / "PaperInterface.lean").write_text("-- no Lean inspection\n")
            (root / "papers" / "Fixture.lean").write_text("-- fixture\n")
            items = {}
            for item_id, statement in (
                ("own_claim", "Lemma 1. Every feasible input has a witness."),
                ("citation", "Lemma 2 (External Author). Every input has a bound."),
                ("component", "Theorem 3. The selected result has this component."),
                ("partial_boundary", "Theorem 4. An explicitly unproved boundary."),
            ):
                items[item_id] = {
                    "source_kind": "lemma" if item_id in {"own_claim", "citation"} else "theorem",
                    "statement": statement,
                    "claim_bearing": True,
                    "inventory_role": "proof_support",
                    "scope_disposition": item_id,
                    "support_lean_declarations": ["Fixture.downstream"],
                    "source_claim_atoms": [{"reviewed_lean_route": "Fixture.recordedAtomRoute"}],
                    "source_component_of": "direct",
                    "source_anchor_evidence": [{
                        "path": "source.txt", "line_start": 10, "line_end": 12,
                        "quoted_text": "DO_NOT_DUMP_THE_SOURCE_CORPUS" * 1000,
                        "quoted_text_sha256": "a" * 64,
                    }],
                }
            items["direct"] = {
                "source_kind": "theorem", "statement": "Theorem 5. A direct claim.",
                "claim_bearing": True,
                "semantic_contract": {
                    "spec_declaration": "Fixture.directSpec",
                    "evidence_declaration": "Fixture.direct",
                },
            }
            items["unnumbered"] = {
                "source_kind": "equation", "claim_bearing": False,
                "inventory_role": "proof_support", "statement": "An intermediate equality.",
            }
            map_path = folder / "audit" / "paper_statement_map.json"
            map_path.write_text(json.dumps({"items": items}))
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "prepare_v11_lean_review_graph", side_effect=AssertionError("producer")) as producer,
                mock.patch.object(planner, "source_intake_readiness", side_effect=AssertionError("intake not requested")),
                mock.patch.object(subprocess, "Popen", side_effect=AssertionError("subprocess")) as process,
            ):
                readiness = planner.static_closeout_readiness(
                    folder, include_intake=False, require_terminal_documents=False,
                )
            self.assertTrue(readiness["ready"])
            self.assertFalse(readiness["acceptance_credential"])
            self.assertEqual(readiness["blockers"], [])
            lane = readiness["lanes"]["review_surface_structure"]
            self.assertIsNone(lane["ready"])
            self.assertEqual(lane["state"], "deferred_to_typed_route_and_lean_graph_preflight")
            self.assertEqual(lane["errors"], [])
            self.assertEqual(len(lane["findings"]), 4)
            for item_id, finding in zip(sorted(items.keys() - {"direct", "unnumbered"}), lane["findings"]):
                self.assertEqual(finding["severity"], "WARN")
                self.assertEqual(finding["path"], "papers/Fixture/audit/paper_statement_map.json")
                self.assertIn(f"items.{item_id}:", finding["message"])
                self.assertIn("source.txt:10-12", finding["message"])
                self.assertIn("Fixture.downstream", finding["message"])
                self.assertIn("Fixture.recordedAtomRoute", finding["message"])
                self.assertIn("not validated coverage or an automatic exemption", finding["message"])
                self.assertNotIn("DO_NOT_DUMP", finding["message"])
                self.assertLess(len(finding["message"]), 1500)
            producer.assert_not_called()
            process.assert_not_called()

    def test_static_readiness_delegates_review_membership_to_lean(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {
                            "include_names": ["missingSpec"],
                            "auxiliary_names": ["missingHelper"],
                            "quarantined_auxiliary_names": ["notAuxiliary"],
                        },
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## Closeout Status\n- Completion status: formalized.\n",
                encoding="utf-8",
            )
            (folder / "docs" / "DependencyDAG.tex").write_text(
                "% fixture\n", encoding="utf-8"
            )
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(b"fixture")
            (folder / "PaperInterface.lean").write_text(
                "def actualSpec : Prop := True\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "source_intake_readiness",
                    return_value={"ready": True, "errors": []},
                ),
                mock.patch.object(
                    planner, "_static_closeout_document_hard_errors", return_value=[]
                ),
            ):
                readiness = planner.static_closeout_readiness(folder)

            lane = readiness["lanes"]["review_surface_structure"]
            self.assertTrue(readiness["ready"])
            self.assertEqual(
                lane["state"],
                "deferred_to_typed_route_and_lean_graph_preflight",
            )
            self.assertEqual(lane["errors"], [])
            self.assertFalse(lane["python_lean_source_parsing"])

    def test_static_readiness_uses_one_source_intake_boundary(self) -> None:
        """A malformed reviewed inventory blocks without a dashboard preflight."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "source_inventory_review_required": True,
                        "build_target": "lake build Fixture",
                        "review_surface": {
                            "require_v11_raw_source_spec_screening": True,
                            "include_names": ["readySpec"],
                        },
                    }
                ),
                encoding="utf-8",
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## Closeout Status\n- Completion status: formalized.\n",
                encoding="utf-8",
            )
            (folder / "docs" / "DependencyDAG.tex").write_text(
                "% fixture\n", encoding="utf-8"
            )
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(b"fixture")
            (folder / "PaperInterface.lean").write_text(
                "def readySpec : Prop := True\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            intake_result = {
                "ready": False,
                "state": "incomplete",
                "errors": ["candidate presentation ledger is incomplete"],
                "acceptance_credential": False,
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "_static_closeout_document_hard_errors", return_value=[]
                ),
                mock.patch.object(
                    planner,
                    "source_intake_readiness",
                    return_value=intake_result,
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertFalse(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["source_intake_boundary"], intake_result
            )
            self.assertTrue(
                any("source intake" in blocker for blocker in readiness["blockers"])
            )
            self.assertNotIn("source_inventory_preflight", readiness["lanes"])
            intake.assert_called_once_with(folder, repository_root=root)
    def test_static_readiness_never_parses_lean_imports(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "FINAL_VALIDATION_REPORT.md",
                "docs/DependencyDAG.tex",
                "docs/DependencyDAG.pdf",
            ):
                (folder / relative).write_text("{}", encoding="utf-8")
            (folder / "PaperInterface.lean").write_text(
                "import AppliedModelingLib.Missing\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "source_intake_readiness",
                    return_value={"ready": True, "errors": []},
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(
                    folder,
                    require_terminal_documents=False,
                )

            lane = readiness["lanes"]["tracked_lean_import_closure"]
            self.assertTrue(readiness["ready"])
            self.assertEqual(lane["state"], "deferred_to_lean_owned_import_closure")
            self.assertFalse(lane["python_lean_source_parsing"])
            self.assertFalse(hasattr(planner, "_tracked_lean_import_preflight"))
            intake.assert_called_once_with(folder, repository_root=root)

    def test_static_readiness_stops_before_intake_for_strict_document_error(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "FINAL_VALIDATION_REPORT.md",
                "docs/DependencyDAG.tex",
                "docs/DependencyDAG.pdf",
            ):
                (folder / relative).write_text("{}", encoding="utf-8")
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "source_intake_readiness",
                    return_value={"ready": True, "errors": []},
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertFalse(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["source_intake_boundary"]["state"],
                "deferred_due_to_static_blocker",
            )
            self.assertTrue(
                any("AGENT_SOURCE_AUDIT.md" in blocker for blocker in readiness["blockers"])
            )
            intake.assert_not_called()

    def test_current_v11_static_preflight_defers_final_adversarial_audit(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            folder.mkdir(parents=True)
            status = {
                "status": "formalized",
                "review_surface": {
                    "require_v11_raw_source_spec_screening": True,
                },
            }

            errors = planner._static_closeout_document_hard_errors(folder, status)

        self.assertEqual(errors, [])

    def test_current_planner_has_no_legacy_source_configuration_lanes(self) -> None:
        self.assertFalse(
            hasattr(planner, "_semantic_source_configuration_errors")
        )
        self.assertFalse(hasattr(planner, "_planner_corrected_scope_current"))

    def test_static_readiness_blocks_controlled_report_status_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## 2. Closeout Status\n"
                "- Completion status: partially formalized.\n",
                encoding="utf-8",
            )
            (folder / "docs" / "DependencyDAG.tex").write_text(
                "% fixture\n", encoding="utf-8"
            )
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(b"fixture")
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "source_intake_readiness", return_value={"errors": []}
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertFalse(readiness["ready"])
            errors = readiness["lanes"]["final_validation_report_status"]["errors"]
            self.assertEqual(len(errors), 1)
            self.assertIn("declares `partially formalized`", errors[0])
            self.assertTrue(
                any(
                    "final validation report/status alignment" in blocker
                    for blocker in readiness["blockers"]
                )
            )
            intake.assert_not_called()






    def test_closeout_input_selection_excludes_ambient_and_presentation_files(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (root / "AppliedModelingLib").mkdir()
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "status.json").write_text("{}")
            (folder / "audit" / "paper_statement_map.json").write_text('{"items": {}}')
            (folder / "audit" / "source_record_audit.json").write_text("{}")
            (folder / "FINAL_VALIDATION_REPORT.md").write_text("ready\n")
            (folder / "docs" / "DependencyDAG.tex").write_text("derived\n")
            (folder / ".review_traces").mkdir()
            (folder / ".review_traces" / "paper_theorem_validations.jsonl").write_text(
                "historical\n"
            )
            unrelated = root / "AppliedModelingLib" / "Unrelated.lean"
            unrelated.write_text("def unrelated := 1\n")
            with mock.patch.object(planner, "ROOT", root):
                content_paths, stat_paths = planner._closeout_plan_input_paths(
                    folder,
                    strict_transaction_content_snapshot={
                        "papers/Fixture/audit/paper_statement_map.json": {
                            "sha256": "a" * 64
                        }
                    },
                )
            self.assertIn(folder / "status.json", content_paths)
            self.assertIn(
                folder / "audit" / "paper_statement_map.json", content_paths
            )
            self.assertNotIn(folder / "FINAL_VALIDATION_REPORT.md", content_paths)
            self.assertNotIn(folder / "docs" / "DependencyDAG.tex", content_paths)
            self.assertNotIn(
                folder / ".review_traces" / "paper_theorem_validations.jsonl",
                content_paths,
            )
            self.assertNotIn(
                folder / "audit" / "source_record_audit.json", content_paths
            )
            self.assertNotIn(unrelated, content_paths)
            self.assertNotIn(unrelated, stat_paths)

    def test_strict_input_inventory_rejects_a_legacy_shaped_context(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with mock.patch.object(planner, "ROOT", root):
                snapshot, error = planner._strict_transaction_content_snapshot(
                    folder,
                    evidence_context=types.SimpleNamespace(
                        v11_lean_claim_graph_selected=False
                    ),
                )

        self.assertIsNone(snapshot)
        self.assertIn("nominal v11 evidence context", error)

    def test_v11_strict_input_inventory_never_reopens_legacy_watch_resolvers(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source.write_text("source bytes\n", encoding="utf-8")
            statement_map = audit / "paper_statement_map.json"
            statement_map.write_text('{"items": {}}', encoding="utf-8")
            status_payload = {"id": "Fixture", "status": "formalized"}
            (folder / "status.json").write_text(
                json.dumps(status_payload), encoding="utf-8"
            )
            context = self._issued_v11_context(
                folder,
                sidecar_paths=(source,),
            )
            with mock.patch.object(planner, "ROOT", root):
                snapshot, error = planner._strict_transaction_content_snapshot(
                    folder,
                    evidence_context=context,
                )
                source.write_text("changed source bytes\n", encoding="utf-8")
                stale_snapshot, stale_error = (
                    planner._strict_transaction_content_snapshot(
                        folder,
                        evidence_context=context,
                    )
                )

            self.assertEqual(error, "")
            assert snapshot is not None
            self.assertIn("papers/Fixture/source.txt", snapshot)
            self.assertIn("papers/Fixture/audit/paper_statement_map.json", snapshot)
            self.assertIsNone(stale_snapshot)
            self.assertIn("source.txt", stale_error)

    def test_strict_input_inventory_compares_only_acceptance_status_fields(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            status_payload = {
                "id": "Fixture",
                "status": "formalized",
                "review_surface": {"include_names": ["Fixture.resultSpec"]},
            }
            status_path = folder / "status.json"
            status_path.write_text(json.dumps(status_payload), encoding="utf-8")
            context = self._issued_v11_context(folder)
            with mock.patch.object(planner, "ROOT", root):
                status_path.write_text(
                    json.dumps(
                        {
                            **status_payload,
                            "paper_interface": {"review_rows": 1},
                            "human_review": {"completed_rows": 0},
                        }
                    ),
                    encoding="utf-8",
                )
                snapshot, error = planner._strict_transaction_content_snapshot(
                    folder,
                    evidence_context=context,
                )
                status_path.write_text(
                    json.dumps({**status_payload, "status": "partial"}),
                    encoding="utf-8",
                )
                changed_snapshot, changed_error = (
                    planner._strict_transaction_content_snapshot(
                        folder,
                        evidence_context=context,
                    )
                )

            self.assertEqual(error, "")
            assert snapshot is not None
            self.assertEqual(
                set(snapshot),
                {"papers/Fixture/audit/paper_statement_map.json"},
            )
            self.assertIsNone(changed_snapshot)
            self.assertIn("acceptance configuration changed", changed_error)


if __name__ == "__main__":
    unittest.main()
