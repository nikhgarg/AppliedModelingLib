#!/usr/bin/env python3
"""Regression tests for source-record producer provenance projection."""

from __future__ import annotations

import unittest

from scripts.source_record_producer_provenance import (
    fingerprint_without_raw_producer_provenance,
    raw_producer_identity_set,
)


def identities() -> list[dict[str, str]]:
    return [
        {"path": "scripts/a.py", "sha256": "a" * 64, "status": "present"},
        {"path": "scripts/b.py", "sha256": "b" * 64, "status": "present"},
    ]


class SourceRecordProducerProvenanceTests(unittest.TestCase):
    def test_projection_removes_only_complete_producer_provenance(self) -> None:
        fingerprint = {
            "schema": 10,
            "paper": "Fixture",
            "source_artifact_sha256": "c" * 64,
            "semantic_coordinate": {"nested": ["retained"]},
            "raw_producer_code_identity_schema": 1,
            "raw_producer_code_identities": identities(),
        }

        projected = fingerprint_without_raw_producer_provenance(fingerprint)

        self.assertEqual(
            projected,
            {
                "schema": 10,
                "paper": "Fixture",
                "source_artifact_sha256": "c" * 64,
                "semantic_coordinate": {"nested": ["retained"]},
            },
        )
        assert projected is not None
        projected["semantic_coordinate"]["nested"].append("changed")
        self.assertEqual(fingerprint["semantic_coordinate"], {"nested": ["retained"]})

    def test_projection_rejects_incomplete_or_malformed_provenance(self) -> None:
        valid = {
            "schema": 10,
            "raw_producer_code_identity_schema": 1,
            "raw_producer_code_identities": identities(),
        }
        cases = [
            {**valid, "schema": 9},
            {**valid, "raw_producer_code_identity_schema": 2},
            {**valid, "raw_producer_code_identities": []},
            {
                **valid,
                "raw_producer_code_identities": [
                    {"path": "scripts/a.py", "sha256": "bad", "status": "present"}
                ],
            },
            {
                **valid,
                "raw_producer_code_identities": [identities()[0], identities()[0]],
            },
        ]
        for case in cases:
            with self.subTest(case=case):
                self.assertIsNone(fingerprint_without_raw_producer_provenance(case))

    def test_identity_normalization_is_order_independent_and_exact(self) -> None:
        self.assertEqual(
            raw_producer_identity_set(identities()),
            raw_producer_identity_set(list(reversed(identities()))),
        )
        malformed = identities()
        malformed[0]["extra"] = "not-permitted"
        self.assertIsNone(raw_producer_identity_set(malformed))


if __name__ == "__main__":
    unittest.main()
