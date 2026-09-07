#!/usr/bin/env python3
"""Tests for the transport-independent source-record obligation authority."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts import source_record_obligation_groups as OBLIGATIONS


ROOT = Path(__file__).resolve().parents[2]
FIXTURE_AUDIT_DIR = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "source_record_differential_reader"
    / "papers"
    / "FixturePaper"
    / "audit"
)


class SourceRecordObligationGroupTests(unittest.TestCase):
    """The generic authority preserves exact historical descriptor identity."""

    @staticmethod
    def _load(name: str) -> dict[str, object]:
        value = json.loads((FIXTURE_AUDIT_DIR / name).read_text(encoding="utf-8"))
        assert isinstance(value, dict)
        return value

    def test_retired_writer_fixture_has_identical_descriptor_preimage(self) -> None:
        raw_audit = self._load("source_record_audit.json")
        groups, errors = OBLIGATIONS.raw_source_record_obligation_groups(raw_audit)
        self.assertEqual(errors, {})
        self.assertEqual(set(groups), {"input.h : P"})

        overlay = self._load("source_record_differential_revalidation.json")
        item = overlay["items"]["input.h : P"]
        metadata = item["source_record_differential_revalidation"]
        group = groups["input.h : P"]

        self.assertEqual(
            group["descriptor"], metadata["current_group_semantic_descriptor"]
        )
        self.assertEqual(
            group["descriptor_sha256"],
            metadata["current_group_semantic_descriptor_sha256"],
        )

    def test_generic_import_does_not_load_historical_overlay_reader(self) -> None:
        completed = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import sys; "
                    "import scripts.source_record_obligation_groups; "
                    "assert 'scripts.source_record_differential_revalidation' "
                    "not in sys.modules"
                ),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_current_revalidation_import_does_not_load_historical_reader(self) -> None:
        completed = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import sys; "
                    "import scripts.source_record_current_revalidation; "
                    "assert 'scripts.source_record_differential_revalidation' "
                    "not in sys.modules"
                ),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
