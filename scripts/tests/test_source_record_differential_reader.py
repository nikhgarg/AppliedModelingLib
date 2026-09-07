#!/usr/bin/env python3
"""Focused tests for the retained historical differential-overlay reader.

The fixture was issued by the retired writer before its archival.  Tests copy
the exact portable artifact bundle to a fresh root and exercise only current
reader behavior.  No test reconstructs or mints a differential overlay.
"""

from __future__ import annotations

import json
import shutil
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


from scripts import source_record_differential_revalidation as DIFFERENTIAL
from scripts import source_record_obligation_groups as OBLIGATIONS


PAPER = "FixturePaper"
FIXTURE_ROOT = (
    Path(__file__).resolve().parent
    / "fixtures"
    / "source_record_differential_reader"
)


class SourceRecordDifferentialReaderTests(unittest.TestCase):
    """The historical reader remains exact, portable, and capability-bound."""

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        shutil.copytree(FIXTURE_ROOT / "papers", self.root / "papers")
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.current_path = self.audit_dir / "source_record_audit.json"
        self.prior_path = self.audit_dir / "source_record_audit.prior.json"
        self.sidecar_path = self.audit_dir / "source_record_match_llm.prior.json"
        self.overlay_path = (
            self.audit_dir / "source_record_differential_revalidation.json"
        )
        root_patch = patch.object(DIFFERENTIAL, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)

    @staticmethod
    def _load_json(path: Path) -> dict[str, object]:
        value = json.loads(path.read_text(encoding="utf-8"))
        assert isinstance(value, dict)
        return value

    def _load_current(self) -> dict[str, dict[str, object]]:
        return DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            self.paper_dir,
            PAPER,
            self._load_json(self.current_path),
        )

    def test_exact_portable_bundle_loads_one_authenticated_item(self) -> None:
        loaded = self._load_current()
        self.assertEqual(set(loaded), {"input.h : P"})
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                loaded["input.h : P"]
            )
        )

    def test_serialized_marker_is_not_a_loader_capability(self) -> None:
        payload = self._load_json(self.overlay_path)
        raw_item = next(iter(payload["items"].values()))
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                raw_item
            )
        )

    def test_capability_preserving_copy_rejects_plain_source(self) -> None:
        loaded = self._load_current()["input.h : P"]
        copied = DIFFERENTIAL.copy_loaded_source_record_differential_revalidation_item(
            loaded, {"reason": "presentation-only copy"}
        )
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                copied
            )
        )
        plain = DIFFERENTIAL.copy_loaded_source_record_differential_revalidation_item(
            dict(loaded), {"reason": "plain copy"}
        )
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                plain
            )
        )

    def test_changed_overlay_bytes_fail_closed(self) -> None:
        payload = self._load_json(self.overlay_path)
        payload["paper"] = "DifferentPaper"
        self.overlay_path.write_text(json.dumps(payload), encoding="utf-8")
        self.assertEqual(self._load_current(), {})

    def test_changed_archived_raw_bytes_fail_closed(self) -> None:
        self.prior_path.write_text("{}\n", encoding="utf-8")
        self.assertEqual(self._load_current(), {})

    def test_changed_archived_sidecar_bytes_fail_closed(self) -> None:
        self.sidecar_path.write_text("{}\n", encoding="utf-8")
        self.assertEqual(self._load_current(), {})

    def test_current_serialization_only_change_remains_current(self) -> None:
        current = self._load_json(self.current_path)
        # The current raw receipt is already self-authenticating. Presentation
        # rewrites such as a derived-summary refresh must not reopen evidence.
        self.current_path.write_text(
            json.dumps(current, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self.assertEqual(set(self._load_current()), {"input.h : P"})

    def test_changed_current_receipt_identity_fails_closed(self) -> None:
        current = self._load_json(self.current_path)
        current["source_record_audit_sha256"] = "0" * 64
        self.current_path.write_text(json.dumps(current), encoding="utf-8")
        self.assertEqual(self._load_current(), {})

    def test_explicit_archive_path_requires_its_issued_provenance_path(self) -> None:
        current = self._load_json(self.current_path)
        archive_path = self.audit_dir / "source_record_audit.archive.json"
        shutil.copyfile(self.current_path, archive_path)
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                self.paper_dir,
                PAPER,
                current,
                current_raw_audit_path=archive_path,
            ),
            {},
        )
        loaded = (
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                self.paper_dir,
                PAPER,
                current,
                current_raw_audit_path=archive_path,
                current_raw_audit_provenance_path=self.current_path,
            )
        )
        self.assertEqual(set(loaded), {"input.h : P"})

    def test_current_groups_are_built_once_per_bundle(self) -> None:
        current = self._load_json(self.current_path)
        original = OBLIGATIONS.raw_source_record_obligation_groups
        with patch.object(
            OBLIGATIONS, "raw_source_record_obligation_groups", wraps=original
        ) as group_builder:
            loaded = (
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    self.paper_dir, PAPER, current
                )
            )
        self.assertEqual(set(loaded), {"input.h : P"})
        # One current projection and one archived-prior projection are enough
        # for the source-free recursive compatibility check.
        self.assertLessEqual(group_builder.call_count, 2)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
