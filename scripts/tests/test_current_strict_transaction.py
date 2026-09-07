from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

from scripts.current_closeout import strict_transaction as transaction


class CurrentStrictTransactionTests(unittest.TestCase):
    def test_stage_registry_imports_no_monolith_or_presentation_module(self) -> None:
        root = Path(__file__).resolve().parents[2]
        result = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import sys; "
                    "import scripts.current_closeout.strict_transaction; "
                    "assert 'scripts.audit_repository' not in sys.modules; "
                    "assert 'scripts.audit_evidence_integrity' not in sys.modules; "
                    "assert 'scripts.review_dashboard' not in sys.modules; "
                    "assert 'scripts.review_dashboard_packet' not in sys.modules; "
                    "assert 'scripts.closeout_pipeline' not in sys.modules"
                ),
            ],
            cwd=root,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, msg=result.stdout + result.stderr)

    def test_execution_projection_requires_an_exact_runtime_prefix(self) -> None:
        projection = transaction.current_closeout_execution_projection(
            transaction.STRICT_CLOSEOUT_EXECUTION_STAGES[:3]
        )
        self.assertEqual(projection["current_prefix_length"], 3)
        self.assertEqual(
            projection["next_stage"],
            transaction.STRICT_CLOSEOUT_EXECUTION_STAGES[3],
        )
        with self.assertRaisesRegex(
            transaction.StrictTransactionError, "exact execution-stage prefix"
        ):
            transaction.current_closeout_execution_projection(
                transaction.STRICT_CLOSEOUT_EXECUTION_STAGES[1:3]
            )

    def test_serialized_trace_has_no_current_acceptance_recorder(self) -> None:
        self.assertFalse(hasattr(transaction, "record_passed_strict_transaction"))
        self.assertFalse(hasattr(transaction, "RecordedPassedStrictTransaction"))


if __name__ == "__main__":
    unittest.main()
