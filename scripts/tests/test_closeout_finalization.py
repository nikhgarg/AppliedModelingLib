#!/usr/bin/env python3
"""Tests for in-process current-closeout publication."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.current_closeout import finalization as finalizer


class CloseoutFinalizationTests(unittest.TestCase):
    def _accepted(self, root: Path) -> SimpleNamespace:
        plan = {
            "paper": "Fixture",
            "plan_identity_sha256": "a" * 64,
            "deep_paper_prose": False,
        }
        engine = {
            "engine_tree_sha256": "b" * 64,
            "review_semantic_class_sha256": "c" * 64,
            "revision_sequence": 1,
            "registration_kind": "independent",
            "engine_file_count": 4,
        }
        build_provider = mock.Mock()
        build_provider.finalize_unchanged.return_value = True
        return SimpleNamespace(
            repository_root=root,
            paper="Fixture",
            plan_identity="a" * 64,
            plan_receipt=lambda: dict(plan),
            engine_registration=lambda: dict(engine),
            evidence_context=mock.sentinel.evidence_context,
            build_input_provider=build_provider,
            lean_closure_projection=lambda: {
                "lean_import_closure": {"fixture": True}
            },
            lean_review_graph=lambda: {"graph": "fixture"},
            lean_review_graph_sha256="d" * 64,
        )

    def test_successful_current_pass_publishes_complete_obligation_bundle(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            build_receipt = folder / "audit" / "FOCUSED_BUILD_RECEIPT.json"
            final_receipt = folder / "FINAL_CLOSURE_RECEIPT.md"
            build_receipt.write_text("{}\n", encoding="utf-8")
            final_receipt.write_text("receipt\n", encoding="utf-8")
            accepted = self._accepted(root)
            plan = accepted.plan_receipt()
            engine = accepted.engine_registration()
            authority = mock.Mock(authority_sha256="e" * 64)
            migration = mock.Mock()
            migration.projection.return_value = {
                "schema": 1,
                "graph_sha256": "f" * 64,
            }
            with (
                mock.patch.object(
                    finalizer,
                    "validate_current_closeout_pass",
                    return_value=accepted,
                ),
                mock.patch.object(
                    finalizer,
                    "load_validated_closeout_plan_receipt",
                    return_value=(plan, ""),
                ),
                mock.patch.object(
                    finalizer,
                    "current_registered_engine_projection",
                    return_value=(engine, ""),
                ),
                mock.patch.object(
                    finalizer,
                    "current_evidence_input_mutations",
                    return_value=(),
                ),
                mock.patch.object(
                    finalizer,
                    "issue_current_strict_closeout_authority",
                    return_value=authority,
                ) as issue_authority,
                mock.patch.object(
                    finalizer,
                    "bind_current_closeout_pass_authority",
                ) as bind_authority,
                mock.patch.object(
                    finalizer,
                    "current_closeout_pass_authority",
                    return_value=authority,
                ),
                mock.patch.object(
                    finalizer,
                    "validate_strict_closeout_authority",
                    return_value=authority,
                ),
                mock.patch.object(
                    finalizer,
                    "lean_import_closure_receipt_payload",
                    return_value={"lean_import_closure": {"fixture": True}},
                ) as closure_payload,
                mock.patch.object(
                    finalizer,
                    "record_focused_build_receipt",
                    return_value=build_receipt,
                ) as record_build,
                mock.patch.object(
                    finalizer,
                    "materialize_passed_strict_closeout_to_obligation_bundle",
                    return_value=migration,
                ) as materialize,
                mock.patch.object(
                    finalizer,
                    "publish_current_obligation_bundle_as_accepted_graph",
                    return_value=final_receipt,
                ) as publish,
                mock.patch.object(
                    finalizer,
                    "refresh_derived_paper_status_metadata",
                    return_value=False,
                ),
            ):
                result = finalizer.finalize_current_closeout(mock.sentinel.current_pass)

        issue_authority.assert_called_once_with(accepted)
        bind_authority.assert_called_once_with(accepted, authority)
        closure_payload.assert_called_once_with("Fixture", {"fixture": True})
        record_build.assert_called_once_with(
            root,
            "Fixture",
            run_build=False,
            persist_saved_closure=False,
            authenticated_lean_import_closure_receipt={
                "lean_import_closure": {"fixture": True}
            },
        )
        materialize.assert_called_once_with(
            root,
            "Fixture",
            authority=authority,
            build_input_provider=accepted.build_input_provider,
            finalize_build_input_provider=False,
            authenticated_lean_import_closure_receipt={
                "lean_import_closure": {"fixture": True}
            },
            authenticated_v11_lean_review_graph={"graph": "fixture"},
            authenticated_v11_lean_review_graph_sha256="d" * 64,
        )
        publish.assert_called_once_with(
            root,
            "Fixture",
            current_closeout_pass=accepted,
        )
        self.assertEqual(result["obligation_evidence"]["graph_sha256"], "f" * 64)
        self.assertEqual(result["runtime_pass_bound_stage_count"], 10)

    def test_plan_mutation_blocks_operational_and_accepting_writes(self) -> None:
        root = Path("/repository")
        accepted = self._accepted(root)
        with (
            mock.patch.object(
                finalizer,
                "validate_current_closeout_pass",
                return_value=accepted,
            ),
            mock.patch.object(
                finalizer,
                "load_validated_closeout_plan_receipt",
                return_value=(None, "source changed"),
            ),
            mock.patch.object(
                finalizer, "issue_current_strict_closeout_authority"
            ) as issue_authority,
            mock.patch.object(
                finalizer,
                "publish_current_obligation_bundle_as_accepted_graph",
            ) as publish,self.assertRaisesRegex(
            finalizer.CloseoutFinalizationError,
            "plan changed before publication",
        )
        ):
            finalizer.finalize_current_closeout(mock.sentinel.current_pass)
        issue_authority.assert_not_called()
        publish.assert_not_called()

    def test_mutation_after_materialization_preserves_previous_selector(self) -> None:
        root = Path("/repository")
        accepted = self._accepted(root)
        accepted.build_input_provider.finalize_unchanged.side_effect = [True, False]
        plan = accepted.plan_receipt()
        engine = accepted.engine_registration()
        authority = mock.Mock(authority_sha256="e" * 64)
        with (
            mock.patch.object(
                finalizer,
                "validate_current_closeout_pass",
                return_value=accepted,
            ),
            mock.patch.object(
                finalizer,
                "load_validated_closeout_plan_receipt",
                return_value=(plan, ""),
            ),
            mock.patch.object(
                finalizer,
                "current_registered_engine_projection",
                return_value=(engine, ""),
            ),
            mock.patch.object(
                finalizer,
                "current_evidence_input_mutations",
                return_value=(),
            ),
            mock.patch.object(
                finalizer,
                "issue_current_strict_closeout_authority",
                return_value=authority,
            ),
            mock.patch.object(
                finalizer,
                "bind_current_closeout_pass_authority",
            ),
            mock.patch.object(
                finalizer,
                "current_closeout_pass_authority",
                return_value=authority,
            ),
            mock.patch.object(
                finalizer,
                "validate_strict_closeout_authority",
                return_value=authority,
            ),
            mock.patch.object(
                finalizer,
                "lean_import_closure_receipt_payload",
                return_value={},
            ),
            mock.patch.object(finalizer, "record_focused_build_receipt"),
            mock.patch.object(
                finalizer,
                "materialize_passed_strict_closeout_to_obligation_bundle",
                return_value=mock.Mock(),
            ),
            mock.patch.object(
                finalizer,
                "publish_current_obligation_bundle_as_accepted_graph",
            ) as publish,self.assertRaisesRegex(
            finalizer.CloseoutFinalizationError,
            "changed during graph materialization",
        )
        ):
            finalizer.finalize_current_closeout(mock.sentinel.current_pass)
        publish.assert_not_called()


if __name__ == "__main__":
    unittest.main()
