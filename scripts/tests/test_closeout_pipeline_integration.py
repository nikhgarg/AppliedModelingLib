from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity
from scripts import review_dashboard
from scripts.current_closeout import planner


class CloseoutPipelineIntegrationTests(unittest.TestCase):
    def test_dashboard_and_evidence_gate_share_typed_route_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture23Paper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = {
                "semantic_contract_schema": 1,
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Fixture23Paper.claimSpec",
                            "evidence_declaration": "Fixture23Paper.claimProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "alias_equivalence",
                        }
                    }
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            dashboard_errors = review_dashboard.paper_source_map_structural_errors(
                folder
            )
            evidence_findings = (
                audit_evidence_integrity.source_map_scope_integrity_findings(
                    folder, "formalized", map_path, payload
                )
            )
            self.assertTrue(
                any("typed_evidence_routes" in error for error in dashboard_errors)
            )
            self.assertTrue(
                any(
                    "typed_evidence_routes" in finding.message
                    for finding in evidence_findings
                )
            )

    def test_planner_does_not_precomplete_runtime_stages_from_cached_inputs(self) -> None:
        stages = planner._current_closeout_stage_projection()
        self.assertEqual(stages["current_prefix_length"], 0)
        self.assertEqual(stages["next_stage"], "closeout_artifact_preflight")
        self.assertNotIn(
            "raw_source_record", {stage["id"] for stage in stages["stages"]}
        )

    def test_planner_does_not_issue_semantic_or_lean_stage_on_manual_worklist(self) -> None:
        schedule = planner._v11_preplan_action_schedule(
            "Fixture",
            semantic_review_current=False,
            compiled_inputs_current=True,
            summary={"statement_requires_review": 1, "coverage_requires_review": 0},
        )
        self.assertEqual(
            schedule["next_action"]["id"], "repair_current_v11_audit"
        )
        self.assertNotIn(
            "strict_closeout", [action["id"] for action in schedule["actions"]]
        )

    def test_current_canonical_receipt_projects_actual_runtime_stage_set(self) -> None:
        stages = planner._current_closeout_stage_projection(
            canonical_receipt_current=True
        )
        self.assertEqual(stages["current_prefix_length"], 10)
        self.assertIsNone(stages["next_stage"])


if __name__ == "__main__":
    unittest.main()
