"""Tests for typed and timed primary paper-gate phases."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts import audit_repository


class MachinePaperStatusPhaseTests(unittest.TestCase):
    def test_phase_records_one_result_and_progress_pair(self) -> None:
        finding = audit_repository.Finding("WARN", Path("status.json"), "fixture")
        timings: dict[str, float] = {}
        events: list[dict[str, object]] = []

        result = audit_repository.run_machine_paper_status_phase(
            audit_repository.MachinePaperStatusPhase.SOURCE_RECORD,
            "Fixture",
            lambda: [finding],
            timings=timings,
            progress_callback=lambda event: events.append(dict(event)),
        )

        self.assertEqual(result, [finding])
        self.assertEqual(set(timings), {"Fixture.source_record"})
        self.assertEqual([event["status"] for event in events], ["started", "finished"])
        self.assertEqual({event["phase"] for event in events}, {"source_record"})

    def test_phase_rejects_duplicate_execution_and_wrong_result_shape(self) -> None:
        timings = {"Fixture.source_record": 0.0}
        with self.assertRaisesRegex(RuntimeError, "ran twice"):
            audit_repository.run_machine_paper_status_phase(
                audit_repository.MachinePaperStatusPhase.SOURCE_RECORD,
                "Fixture",
                lambda: [],
                timings=timings,
            )
        with self.assertRaisesRegex(TypeError, "returned invalid findings"):
            audit_repository.run_machine_paper_status_phase(
                audit_repository.MachinePaperStatusPhase.STATEMENT_SIDECAR,
                "Fixture",
                lambda: [object()],  # type: ignore[list-item]
            )

    def test_progress_failure_cannot_change_audit_result(self) -> None:
        def fail_progress(_event: object) -> None:
            raise RuntimeError("display failed")

        result = audit_repository.run_machine_paper_status_phase(
            audit_repository.MachinePaperStatusPhase.INTERFACE_AXIOM_CLOSURE,
            "Fixture",
            lambda: [],
            progress_callback=fail_progress,
        )

        self.assertEqual(result, [])


if __name__ == "__main__":
    unittest.main()
