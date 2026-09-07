#!/usr/bin/env python3
"""Fail-closed regression tests for source-record transports archived in Git."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_authenticated_overlay_union as UNION  # noqa: E402
from scripts import source_record_archived_transports as ARCHIVED  # noqa: E402


HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location("archived_transport_source_record_audit", HELPER)
assert SPEC is not None and SPEC.loader is not None
SOURCE_AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = SOURCE_AUDIT
SPEC.loader.exec_module(SOURCE_AUDIT)

PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"


def raw_audit() -> dict[str, object]:
    return {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_audit_sha256": "a" * 64,
    }


def marked_payload(field: str) -> dict[str, object]:
    return {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_audit_sha256": "a" * 64,
        "validator": "fixture reviewer",
        "validated_at": "2026-08-23T00:00:00Z",
        "items": {
            "fixture": {
                "classification": "matches",
                "prompt_version": PROMPT,
                "source_record_audit_sha256": "a" * 64,
                field: {"forged": True},
            }
        },
    }


class ArchivedSourceRecordTransportTests(unittest.TestCase):
    def test_every_current_serialized_overlay_marker_needs_loader_capability(self) -> None:
        raw = raw_audit()
        for protocol in UNION.SOURCE_RECORD_OVERLAY_PROTOCOLS:
            with self.subTest(label=protocol.label):
                payload = marked_payload(protocol.item_field)
                self.assertEqual(
                    SOURCE_AUDIT.current_source_record_judgments_from_payload(
                        payload, PAPER, raw
                    ),
                    {},
                )
                with mock.patch.object(
                    EVIDENCE, "source_record_audit_identity_error", return_value=""
                ):
                    self.assertEqual(
                        EVIDENCE._current_source_record_judgment_items_from_payload(
                            raw, payload
                        ),
                        {},
                    )
                self.assertEqual(
                    CONCLUSION._current_judgments_from_payload(PAPER, raw, payload),
                    {},
                )

    def test_every_retired_serialized_marker_is_rejected_by_current_readers(self) -> None:
        raw = raw_audit()
        for field in sorted(ARCHIVED.ARCHIVED_SOURCE_RECORD_TRANSPORT_ITEM_FIELDS):
            with self.subTest(field=field):
                payload = marked_payload(field)
                self.assertEqual(
                    SOURCE_AUDIT.current_source_record_judgments_from_payload(
                        payload, PAPER, raw
                    ),
                    {},
                )
                with mock.patch.object(
                    EVIDENCE, "source_record_audit_identity_error", return_value=""
                ):
                    self.assertEqual(
                        EVIDENCE._current_source_record_judgment_items_from_payload(
                            raw, payload
                        ),
                        {},
                    )
                self.assertEqual(
                    CONCLUSION._current_judgments_from_payload(PAPER, raw, payload),
                    {},
                )
                item = payload["items"]["fixture"]
                assert isinstance(item, dict)
                self.assertFalse(
                    REPOSITORY.source_record_judgment_current(
                        "fixture",
                        item,
                        digest="a" * 64,
                        expected_item_digests={},
                    )
                )

    def test_retired_artifact_forces_fresh_evidence_in_every_paper_reader(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / PAPER
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            sidecar = audit_dir / "source_record_match_llm.json"
            sidecar.write_text(json.dumps(marked_payload("ordinary")), encoding="utf-8")
            raw = raw_audit()
            for filename in sorted(
                ARCHIVED.ARCHIVED_SOURCE_RECORD_TRANSPORT_FILENAMES
            ):
                with self.subTest(filename=filename):
                    retired = audit_dir / filename
                    retired.write_text("{}\n", encoding="utf-8")
                    self.assertEqual(
                        SOURCE_AUDIT.current_source_record_judgments(
                            paper_dir, PAPER, raw
                        ),
                        {},
                    )
                    self.assertEqual(
                        EVIDENCE.current_source_record_judgment_items(
                            raw, {}, folder=paper_dir
                        ),
                        {},
                    )
                    self.assertEqual(
                        REPOSITORY.source_record_judgment_items(
                            sidecar,
                            PAPER,
                            current_raw_audit=raw,
                            paper_dir=paper_dir,
                        ),
                        {},
                    )
                    with mock.patch.object(CONCLUSION, "PAPERS", paper_dir.parent):
                        self.assertEqual(CONCLUSION.current_judgments(PAPER, raw), {})
                    with self.assertRaisesRegex(
                        UNION.SourceRecordAuthenticatedOverlayUnionError,
                        "retired source-record transport artifact requires fresh current evidence",
                    ):
                        UNION.load_authenticated_current_overlay_lanes(
                            paper_dir, PAPER, raw
                        )
                    retired.unlink()


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
