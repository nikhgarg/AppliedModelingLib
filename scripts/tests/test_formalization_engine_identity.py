#!/usr/bin/env python3
"""Tests for the closeout engine-identity boundary."""

from __future__ import annotations

import unittest

from scripts.formalization_engine_identity import normalized_engine_projection


def projection(**changes: object) -> dict[str, object]:
    value: dict[str, object] = {
        "engine_tree_sha256": "a" * 64,
        "review_semantic_class_sha256": "b" * 64,
        "revision_sequence": 1,
        "registration_kind": "independent",
        "engine_file_count": 12,
    }
    value.update(changes)
    return value


class FormalizationEngineIdentityTests(unittest.TestCase):
    def test_exact_projection_is_accepted_without_extra_fields(self) -> None:
        value = projection(unrelated="ignored")

        normalized, error = normalized_engine_projection(value)

        self.assertEqual(error, "")
        assert normalized is not None
        self.assertEqual(set(normalized), set(projection()))
        self.assertNotIn("unrelated", normalized)

    def test_semantic_protocol_identity_is_mandatory(self) -> None:
        normalized, error = normalized_engine_projection(
            projection(review_semantic_class_sha256="")
        )

        self.assertIsNone(normalized)
        self.assertIn("review_semantic_class_sha256", error)

    def test_pairwise_relation_does_not_grant_current_registration(self) -> None:
        value = projection()
        value.pop("registration_kind")
        value["relation_to_previous"] = "review_compatible"

        normalized, error = normalized_engine_projection(value)

        self.assertEqual(error, "")
        assert normalized is not None
        self.assertEqual(normalized["registration_kind"], "legacy_linked_revision")
        self.assertNotIn("relation_to_previous", normalized)


if __name__ == "__main__":
    unittest.main()
