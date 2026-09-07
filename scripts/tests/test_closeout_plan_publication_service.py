#!/usr/bin/env python3
"""Boundary tests for the current closeout receipt-writer service."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path
from unittest import mock

from scripts.current_closeout import plan_publication, planner


class CloseoutPlanPublicationServiceTests(unittest.TestCase):
    def test_fresh_import_has_no_semantic_or_operational_orchestrator(self) -> None:
        root = Path(__file__).resolve().parents[2]
        forbidden = (
            "scripts.current_closeout.planner",
            "scripts.current_closeout.worker",
            "scripts.current_closeout.finalization",
            "scripts.audit_evidence_integrity",
            "scripts.lean_signature_manifest",
            "scripts.review_dashboard",
            "scripts.review_dashboard_packet",
        )
        process = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import json, sys; "
                    "import scripts.current_closeout.plan_publication; "
                    f"print(json.dumps([name for name in {forbidden!r} "
                    "if name in sys.modules]))"
                ),
            ],
            cwd=root,
            text=True,
            capture_output=True,
            check=False,
        )

        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), [])

    def test_planner_wrapper_delegates_to_the_one_receipt_writer(self) -> None:
        folder = Path("/tmp/papers/Fixture")
        plan = {"paper": "Fixture"}
        expected = plan_publication.CloseoutPlanReceiptPublication(
            receipt=None,
            error="fixture",
            disposition="deterministic_input",
            input_identity_sha256="a" * 64,
        )
        with mock.patch.object(
            planner,
            "publish_closeout_plan_receipt",
            return_value=expected,
        ) as publish:
            observed = planner._write_current_closeout_plan_receipt(
                plan,
                folder=folder,
                deep_paper_prose=False,
                publication_inputs=None,
            )

        self.assertIs(observed, expected)
        publish.assert_called_once_with(
            planner.ROOT,
            plan,
            folder=folder,
            deep_paper_prose=False,
            publication_inputs=None,
        )


if __name__ == "__main__":
    unittest.main()
