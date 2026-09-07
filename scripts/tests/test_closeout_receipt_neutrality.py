#!/usr/bin/env python3
"""Regression fence between operational closeout UX and semantic receipts."""

from __future__ import annotations

import unittest

from scripts.legacy_v10_trust_ledger import ENGINE_SOURCE_PATHS
from scripts.theorem_realization_transition import MATERIAL_ARTIFACT_PATHS


OPERATIONAL_WORKFLOW_PATHS = {
    "scripts/closeout_execution_state.py",
    "scripts/closeout_plan_receipt.py",
    "scripts/closeout_reuse_plan.py",
    "scripts/run_paper_closeout.py",
    "scripts/sync_paper_status.py",
    "scripts/new_paper.py",
    "scripts/paper_path_resolution.py",
    "scripts/python_import_closure.py",
}


class CloseoutReceiptNeutralityTests(unittest.TestCase):
    def test_operational_workflow_files_are_not_semantic_engine_inputs(self) -> None:
        self.assertFalse(OPERATIONAL_WORKFLOW_PATHS.intersection(ENGINE_SOURCE_PATHS))

    def test_ignored_execution_outputs_are_not_material_artifacts(self) -> None:
        material = set(MATERIAL_ARTIFACT_PATHS)
        for relative in (
            ".review_traces/paper_closeout_worker.json",
            ".review_traces/paper_closeout_worker.log",
            ".review_traces/paper_closeout_worker.0123456789abcdef.log",
            ".review_traces/paper_closeout_worker.lock",
            ".review_traces/closeout_reuse_advisory.json",
            ".review_traces/closeout_execution_plan.json",
            ".review_traces/closeout_execution_plan.aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.json",
            ".review_traces/source_record_raw_reissues/raw_reissue_operation.json",
            "README.md",
            "docs/FORMALIZATION_PLAN.md",
        ):
            self.assertNotIn(relative, material)


if __name__ == "__main__":
    unittest.main()
