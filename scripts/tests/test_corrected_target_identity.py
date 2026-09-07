from __future__ import annotations

import copy
import hashlib
import unittest

from scripts.corrected_target_identity import (
    CORRECTED_TARGET_APPROVAL_PROTOCOL,
    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_approval_artifact_error,
    corrected_target_historical_record_projection,
    corrected_target_original_artifact_path_error,
    corrected_target_record_digest,
    corrected_target_review_digest,
    corrected_target_screening_binding_is_current,
)


class CorrectedTargetIdentityTests(unittest.TestCase):
    def target(self) -> dict[str, object]:
        return {
            "schema": 1,
            "statement": "For every x, the corrected conclusion holds.",
            "governing_defect_ids": ["FIXTURE-1"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": "source.tex:10",
            "archival_source_quote_sha256": "a" * 64,
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-08-28",
                "reference": "Approved corrected target.",
                "target_statement_sha256": "b" * 64,
                "artifact_path": "SOURCE_RECORD.md",
                "artifact_sha256": "c" * 64,
            },
        }

    def excerpt_target(self) -> dict[str, object]:
        target = self.target()
        excerpt = (
            "The task owner approved the corrected finite mathematical target."
        )
        target["approval"] = {
            "kind": "explicit_user_instruction",
            "recorded_at": "2026-08-28",
            "reference": "Approved corrected target.",
            "target_statement_sha256": "b" * 64,
            "artifact_path": "SOURCE_RECORD.md",
            "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
            "artifact_excerpt": excerpt,
            "artifact_excerpt_sha256": hashlib.sha256(
                excerpt.encode("utf-8")
            ).hexdigest(),
        }
        return target

    def test_current_approval_binds_excerpt_not_artifact_path(self) -> None:
        target = self.excerpt_target()
        moved = copy.deepcopy(target)
        moved["approval"]["artifact_path"] = "docs/CORRECTION.md"  # type: ignore[index]
        self.assertEqual(
            corrected_target_record_digest(target),
            corrected_target_record_digest(moved),
        )

        changed = copy.deepcopy(target)
        changed_excerpt = (
            "The task owner approved a different finite mathematical target."
        )
        changed["approval"]["artifact_excerpt"] = changed_excerpt  # type: ignore[index]
        changed["approval"]["artifact_excerpt_sha256"] = hashlib.sha256(  # type: ignore[index]
            changed_excerpt.encode("utf-8")
        ).hexdigest()
        self.assertNotEqual(
            corrected_target_record_digest(target),
            corrected_target_record_digest(changed),
        )

    def test_current_approval_excerpt_must_be_unique_in_artifact(self) -> None:
        target = self.excerpt_target()
        approval = target["approval"]
        excerpt = approval["artifact_excerpt"]  # type: ignore[index]
        self.assertEqual(
            corrected_target_approval_artifact_error(
                approval,
                "Header\n\n" + str(excerpt) + "\n\nUnrelated later prose.",
            ),
            "",
        )
        self.assertIn(
            "found 2",
            corrected_target_approval_artifact_error(
                approval,
                str(excerpt) + "\n\n" + str(excerpt),
            ),
        )

    def test_original_locator_is_current_neutral_and_replays_exact_old_record(
        self,
    ) -> None:
        old = self.excerpt_target()
        old["corrected_target_review_sha256"] = corrected_target_review_digest(old)
        old["corrected_target_sha256"] = corrected_target_record_digest(old)

        current = copy.deepcopy(old)
        approval = current["approval"]
        assert isinstance(approval, dict)
        approval["artifact_path"] = "audit/SOURCE_TARGET_STATEMENTS.md"
        approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = (
            "SOURCE_RECORD.md"
        )
        current["corrected_target_sha256"] = corrected_target_record_digest(current)

        self.assertEqual(corrected_target_original_artifact_path_error(approval), "")
        self.assertEqual(
            corrected_target_record_digest(current),
            corrected_target_record_digest(old),
        )
        self.assertEqual(
            corrected_target_review_digest(current),
            corrected_target_review_digest(old),
        )
        historical, error = corrected_target_historical_record_projection(current)
        self.assertEqual(error, "")
        self.assertEqual(historical, old)

    def test_original_locator_is_exact_and_fails_closed_when_malformed(self) -> None:
        invalid_values: tuple[object, ...] = (
            None,
            "",
            " SOURCE_RECORD.md",
            "SOURCE_RECORD.md ",
            "/SOURCE_RECORD.md",
            "../SOURCE_RECORD.md",
            "docs/../SOURCE_RECORD.md",
            "docs/./SOURCE_RECORD.md",
            "docs//SOURCE_RECORD.md",
            "docs/SOURCE_RECORD.md/",
            "docs\\SOURCE_RECORD.md",
            "audit/SOURCE_TARGET_STATEMENTS.md",
        )
        for value in invalid_values:
            with self.subTest(value=value):
                target = self.excerpt_target()
                approval = target["approval"]
                assert isinstance(approval, dict)
                approval["artifact_path"] = "audit/SOURCE_TARGET_STATEMENTS.md"
                approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = value
                self.assertTrue(corrected_target_original_artifact_path_error(approval))
                _historical, error = corrected_target_historical_record_projection(
                    target
                )
                self.assertTrue(error)

        target = self.excerpt_target()
        approval = target["approval"]
        assert isinstance(approval, dict)
        approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = "docs/OLD.md"
        approval["artifact_protocol"] = "whole_artifact_sha256_v0"
        self.assertTrue(corrected_target_original_artifact_path_error(approval))

    def test_original_locator_lookalikes_remain_semantic(self) -> None:
        first = self.excerpt_target()
        second = copy.deepcopy(first)
        first_approval = first["approval"]
        second_approval = second["approval"]
        assert isinstance(first_approval, dict)
        assert isinstance(second_approval, dict)
        first_approval["Original_Artifact_Path"] = "docs/first.md"
        second_approval["Original_Artifact_Path"] = "docs/second.md"
        self.assertNotEqual(
            corrected_target_record_digest(first),
            corrected_target_record_digest(second),
        )

    def test_unrelated_approval_artifact_change_preserves_review_identity(self) -> None:
        target = self.target()
        changed = copy.deepcopy(target)
        changed["approval"]["artifact_sha256"] = "d" * 64  # type: ignore[index]

        self.assertNotEqual(
            corrected_target_record_digest(target),
            corrected_target_record_digest(changed),
        )
        self.assertEqual(
            corrected_target_review_digest(target),
            corrected_target_review_digest(changed),
        )

    def test_mathematical_statement_change_invalidates_both_identities(self) -> None:
        target = self.target()
        changed = copy.deepcopy(target)
        changed["statement"] = "For every x, a different conclusion holds."

        self.assertNotEqual(
            corrected_target_record_digest(target),
            corrected_target_record_digest(changed),
        )
        self.assertNotEqual(
            corrected_target_review_digest(target),
            corrected_target_review_digest(changed),
        )

    def test_current_and_historical_rows_use_their_recorded_identity_generation(
        self,
    ) -> None:
        target = self.target()
        target["corrected_target_sha256"] = corrected_target_record_digest(target)
        target["corrected_target_review_sha256"] = corrected_target_review_digest(
            target
        )
        current = {
            "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
            "corrected_target_review_sha256": corrected_target_review_digest(target),
        }
        historical = {
            "corrected_target_protocol": LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL,
            "corrected_target_sha256": target["corrected_target_sha256"],
        }
        self.assertTrue(corrected_target_screening_binding_is_current(current, target))
        self.assertTrue(
            corrected_target_screening_binding_is_current(historical, target)
        )

        changed = copy.deepcopy(target)
        changed["approval"]["artifact_sha256"] = "d" * 64  # type: ignore[index]
        changed["corrected_target_sha256"] = corrected_target_record_digest(changed)
        self.assertTrue(corrected_target_screening_binding_is_current(current, changed))
        self.assertFalse(
            corrected_target_screening_binding_is_current(historical, changed)
        )


if __name__ == "__main__":
    unittest.main()
