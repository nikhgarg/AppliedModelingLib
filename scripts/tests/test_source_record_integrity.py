"""Focused tests for source-record receipt integrity."""

from __future__ import annotations

import copy
import json
import unittest

from scripts.source_record_integrity import (
    LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
    SOURCE_RECORD_AUDIT_SURFACE_FIELD,
    SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD,
    SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
    SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD,
    source_record_archived_transport_error,
    source_record_audit_receipt_error,
    source_record_audit_surface_sha256,
    source_record_audit_surface_view,
    source_record_raw_evidence_projection,
    stamp_source_record_audit_integrity,
    stamp_source_record_audit_receipts,
)


class SourceRecordArchivedTransportTests(unittest.TestCase):
    def test_current_receipt_without_archived_transport_is_accepted(self) -> None:
        self.assertEqual(source_record_archived_transport_error({"schema": 5}), "")

    def test_archived_transport_requires_fresh_raw_receipt(self) -> None:
        error = source_record_archived_transport_error(
            {
                "source_record_direct_route_diagnostic_rebind": {"schema": 1},
                "source_record_assumption_route_diagnostic_rebind": {"schema": 1},
            }
        )

        self.assertIn("archived transport field(s)", error)
        self.assertIn("reissue the raw receipt with the current producer", error)


class SourceRecordCompactSurfaceTests(unittest.TestCase):
    def payload(self) -> dict[str, object]:
        return {
            "paper": "Fixture",
            "configured_review_rows": [
                {
                    "qualified_declaration": "Fixture.claimSpec",
                    "display": "x" * 2048,
                }
            ],
            "source_proof_fidelity": {"defects": []},
        }

    def test_current_surface_binds_raw_fields_without_copying_them(self) -> None:
        payload = self.payload()
        generator_surface = {
            "paper": "Fixture",
            "configured_review_rows": copy.deepcopy(
                payload["configured_review_rows"]
            ),
            "surface_only": {"route": "checked"},
        }

        stamp_source_record_audit_receipts(payload, generator_surface)

        compact = payload[SOURCE_RECORD_AUDIT_SURFACE_FIELD]
        self.assertEqual(
            payload[SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD],
            SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
        )
        self.assertIsInstance(compact, dict)
        self.assertNotIn(SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD, compact)
        self.assertEqual(source_record_audit_receipt_error(payload), "")
        logical_surface = source_record_audit_surface_view(payload)
        self.assertIsInstance(logical_surface, dict)
        assert isinstance(logical_surface, dict)
        self.assertEqual(
            {
                key: value
                for key, value in logical_surface.items()
                if key != SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD
            },
            generator_surface,
        )
        self.assertEqual(
            logical_surface[SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD],
            source_record_raw_evidence_projection(payload),
        )
        self.assertLess(
            len(json.dumps(compact, sort_keys=True)),
            len(
                json.dumps(
                    source_record_raw_evidence_projection(payload), sort_keys=True
                )
            ),
        )

    def test_current_surface_rejects_changed_raw_field(self) -> None:
        payload = self.payload()
        stamp_source_record_audit_receipts(
            payload,
            {
                "configured_review_rows": copy.deepcopy(
                    payload["configured_review_rows"]
                )
            },
        )

        rows = payload["configured_review_rows"]
        assert isinstance(rows, list) and isinstance(rows[0], dict)
        rows[0]["display"] = "changed"

        self.assertIn("digest is stale", source_record_audit_receipt_error(payload))

    def test_legacy_embedded_surface_remains_readable(self) -> None:
        payload = self.payload()
        surface = {"paper": "Fixture"}
        surface[SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD] = copy.deepcopy(
            source_record_raw_evidence_projection(payload)
        )
        payload["source_record_audit_sha256"] = source_record_audit_surface_sha256(
            surface
        )
        payload[SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD] = (
            LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA
        )
        payload[SOURCE_RECORD_AUDIT_SURFACE_FIELD] = surface
        stamp_source_record_audit_integrity(payload)

        self.assertEqual(source_record_audit_receipt_error(payload), "")
        self.assertEqual(source_record_audit_surface_view(payload), surface)


if __name__ == "__main__":
    unittest.main()
