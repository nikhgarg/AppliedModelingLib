from __future__ import annotations

import copy
import hashlib
import json
import pickle
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.current_closeout import pass_capability as capability
from scripts.current_closeout.strict_transaction import (
    STRICT_CLOSEOUT_EXECUTION_STAGES,
)
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    EvidenceJSONSnapshot,
)


class CurrentCloseoutPassTests(unittest.TestCase):
    def _context(self, root: Path):
        folder = root / "papers" / "Fixture"
        folder.mkdir(parents=True)

        def snapshot(path: Path, payload: dict[str, object]):
            raw = json.dumps(payload, sort_keys=True).encode("utf-8")
            return EvidenceJSONSnapshot(
                path=path,
                sha256=hashlib.sha256(raw).hexdigest(),
                payload=payload,
                raw_bytes=raw,
            )

        return CommonEvidenceRunContextInputs(
            folder=folder,
            status="formalized",
            audit_config_snapshot=snapshot(
                root / "papers" / "audit_config.json", {"schema": 1}
            ),
            status_snapshot=snapshot(folder / "status.json", {"status": "formalized"}),
            statement_map_snapshot=snapshot(
                folder / "audit" / "paper_statement_map.json", {"items": {}}
            ),
            source_proof_fidelity_snapshot=None,
            sidecar_snapshots=(),
            source_proof_fidelity_path_error="",
        ).issue_v11(None)

    def _issue(self, root: Path):
        context = self._context(root)
        build_provider = mock.Mock()
        primary = SimpleNamespace(
            context=context,
            surface=SimpleNamespace(build_input_provider=build_provider),
        )
        evidence = SimpleNamespace(context=context, primary=primary)
        plan = {
            "paper": "Fixture",
            "plan_identity_sha256": "a" * 64,
            "deep_paper_prose": False,
            "final_holistic_audit_surface_sha256": "b" * 64,
            "v11_lean_review_graph": {"sha256": "c" * 64},
        }
        engine = {
            "engine_tree_sha256": "d" * 64,
            "review_semantic_class_sha256": "e" * 64,
            "revision_sequence": 1,
            "registration_kind": "independent",
            "engine_file_count": 2,
        }
        with (
            mock.patch.object(
                capability,
                "_accepted_primary",
                return_value=primary,
            ),
            mock.patch.object(
                capability,
                "_accepted_evidence",
                return_value=evidence,
            ),
            mock.patch.object(
                capability,
                "current_registered_engine_projection",
                return_value=(engine, ""),
            ),
            mock.patch.object(
                capability,
                "normalized_engine_projection",
                return_value=(engine, ""),
            ),
            mock.patch.object(
                capability,
                "resolved_plan_lean_closure_projection",
                return_value={"lean_import_closure": {"fixture": True}},
            ),
            mock.patch.object(
                capability,
                "resolved_plan_v11_lean_review_graph",
                return_value={"graph": "fixture"},
            ),
            mock.patch.object(
                capability,
                "resolved_plan_final_holistic_audit_surface",
                return_value={"paper": "Fixture", "surface": True},
            ),
            mock.patch.object(
                capability,
                "final_holistic_audit_surface_sha256",
                return_value="b" * 64,
            ),
        ):
            accepted = capability._issue_current_closeout_pass(
                root,
                "Fixture",
                plan_identity="a" * 64,
                plan_receipt=plan,
                evidence_context=context,
                completed_stages=STRICT_CLOSEOUT_EXECUTION_STAGES,
                findings=(),
            )
        return accepted, context, primary, evidence

    def test_exact_pass_is_context_bound_immutable_and_nonserializable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            accepted, context, primary, evidence = self._issue(Path(temporary))
        with (
            mock.patch.object(
                capability,
                "_accepted_primary",
                return_value=primary,
            ),
            mock.patch.object(
                capability,
                "_accepted_evidence",
                return_value=evidence,
            ),
        ):
            self.assertIs(capability.accepted_current_closeout_pass(context), accepted)
            self.assertIs(capability.validate_current_closeout_pass(accepted), accepted)
        self.assertIs(accepted.primary_acceptance, primary)
        self.assertIs(accepted.evidence_acceptance, evidence)
        with self.assertRaises(TypeError):
            copy.copy(accepted)
        with self.assertRaises(TypeError):
            copy.deepcopy(accepted)
        with self.assertRaises(TypeError):
            pickle.dumps(accepted)
        with self.assertRaises(TypeError):
            accepted._paper = "Other"  # type: ignore[misc]
        with self.assertRaises(TypeError):
            capability.CurrentCloseoutPass(  # type: ignore[call-arg]
                object(),
                repository_root=Path("/repository"),
                paper="Fixture",
                plan_identity="a" * 64,
                plan_receipt={},
                evidence_context=context,
                primary_acceptance=primary,
                evidence_acceptance=evidence,
                engine_registration={},
                lean_closure_projection={},
                lean_review_graph={},
                lean_review_graph_sha256="c" * 64,
                final_holistic_surface={},
                build_input_provider=object(),
            )

    def test_pass_cannot_move_to_a_replaced_context(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            accepted, context, primary, evidence = self._issue(Path(temporary))
        copied_context = replace(context)
        with (
            mock.patch.object(
                capability,
                "_accepted_primary",
                return_value=primary,
            ),
            mock.patch.object(
                capability,
                "_accepted_evidence",
                return_value=evidence,
            ),
        ):
            self.assertIsNone(capability.accepted_current_closeout_pass(copied_context))
            self.assertIs(capability.accepted_current_closeout_pass(context), accepted)

    def test_incomplete_stage_sequence_cannot_issue_a_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            context = self._context(root)
            with self.assertRaisesRegex(
                capability.CurrentCloseoutPassError,
                "complete error-free",
            ):
                capability._issue_current_closeout_pass(
                    root,
                    "Fixture",
                    plan_identity="a" * 64,
                    plan_receipt={
                        "paper": "Fixture",
                        "plan_identity_sha256": "a" * 64,
                    },
                    evidence_context=context,
                    completed_stages=STRICT_CLOSEOUT_EXECUTION_STAGES[:-1],
                    findings=(),
                )


if __name__ == "__main__":
    unittest.main()
