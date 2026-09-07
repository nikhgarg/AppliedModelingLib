#!/usr/bin/env python3
"""Tests for policy-aware final-adversary review panels."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.final_adversarial_review_panel import (
    final_adversarial_review_panel_errors,
    validated_final_adversarial_review_artifact_paths,
)


class FinalAdversarialReviewPanelTests(unittest.TestCase):
    target = "a" * 64

    @staticmethod
    def policy(count: int) -> dict[str, object]:
        return {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": count,
        }

    def write_audit(self, folder: Path, path: str) -> str:
        content = (
            "## Overall status: PASS\n"
            f"- Reviewed final holistic audit surface identity: `{self.target}`\n"
            "- Final audit scope: `complete_current_surface`\n"
            "I independently compared every selected source region and Lean route.\n"
        ).encode("utf-8")
        artifact = folder / path
        artifact.parent.mkdir(parents=True, exist_ok=True)
        artifact.write_bytes(content)
        return hashlib.sha256(content).hexdigest()

    def review(self, reviewer: str, path: str, digest: str) -> dict[str, object]:
        return {
            "reviewer_identity": reviewer,
            "audit_artifact_path": path,
            "audit_artifact_sha256": digest,
            "reviewed_surface_sha256": self.target,
            "judgment": "PASS",
            "scope": "complete_current_surface",
            "reviewed_at": "2026-09-05T12:00:00Z",
            "independence": {
                "did_not_author_or_repair": True,
                "did_not_issue_semantic_judgments": True,
            },
        }

    @staticmethod
    def write_panel(folder: Path, panel: dict[str, object]) -> None:
        path = folder / "docs/FINAL_ADVERSARIAL_REVIEW_PANEL.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(panel, indent=2) + "\n", encoding="utf-8")

    def panel(self, count: int, reviews: list[dict[str, object]]) -> dict[str, object]:
        return {
            "schema": 1,
            "paper": "Fixture",
            "review_material_sha256": self.target,
            "required_reviewer_count": count,
            "ineligible_reviewer_identities": ["author-session"],
            "reviews": reviews,
        }

    def test_two_distinct_reviews_of_exact_surface_pass(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            first = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.md")
            second = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.reviewer-2.md")
            self.write_panel(
                folder,
                self.panel(
                    2,
                    [
                        self.review("review-session-1", "docs/AGENT_SOURCE_AUDIT.md", first),
                        self.review(
                            "review-session-2",
                            "docs/AGENT_SOURCE_AUDIT.reviewer-2.md",
                            second,
                        ),
                    ],
                ),
            )
            self.assertEqual(
                final_adversarial_review_panel_errors(
                    folder,
                    target_surface_identity=self.target,
                    review_policy_assurance=self.policy(2),
                ),
                (),
            )
            self.assertEqual(
                {path.name for path in validated_final_adversarial_review_artifact_paths(
                    folder,
                    target_surface_identity=self.target,
                    review_policy_assurance=self.policy(2),
                )},
                {
                    "FINAL_ADVERSARIAL_REVIEW_PANEL.json",
                    "AGENT_SOURCE_AUDIT.md",
                    "AGENT_SOURCE_AUDIT.reviewer-2.md",
                },
            )

    def test_duplicate_reviewer_and_wrong_surface_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            first = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.md")
            second = self.write_audit(folder, "docs/second.md")
            rows = [
                self.review("same-reviewer", "docs/AGENT_SOURCE_AUDIT.md", first),
                self.review("same-reviewer", "docs/second.md", second),
            ]
            rows[1]["reviewed_surface_sha256"] = "b" * 64
            self.write_panel(folder, self.panel(2, rows))
            messages = [
                finding.message
                for finding in final_adversarial_review_panel_errors(
                    folder,
                    target_surface_identity=self.target,
                    review_policy_assurance=self.policy(2),
                )
            ]
        self.assertTrue(any("duplicated" in message for message in messages), messages)
        self.assertTrue(any("exact frozen" in message for message in messages), messages)

    def test_count_increase_preserves_first_review_and_requests_only_missing_one(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            first = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.md")
            first_row = self.review(
                "review-session-1", "docs/AGENT_SOURCE_AUDIT.md", first
            )
            original_panel = self.panel(1, [first_row])
            self.write_panel(folder, original_panel)
            self.assertFalse(
                final_adversarial_review_panel_errors(
                    folder,
                    target_surface_identity=self.target,
                    review_policy_assurance=self.policy(1),
                )
            )

            raised_panel = dict(original_panel)
            raised_panel["required_reviewer_count"] = 2
            self.write_panel(folder, raised_panel)
            findings = final_adversarial_review_panel_errors(
                folder,
                target_surface_identity=self.target,
                review_policy_assurance=self.policy(2),
            )
        self.assertEqual(
            [finding.message for finding in findings if "additional" in finding.message],
            [
                "final-adversary review panel needs 1 additional distinct reviewer "
                "for the unchanged review material"
            ],
        )
        self.assertNotIn("audit artifact", "; ".join(f.message for f in findings))

    def test_recorded_count_must_match_frozen_policy(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            first = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.md")
            self.write_panel(
                folder,
                self.panel(
                    1,
                    [self.review("review-session-1", "docs/AGENT_SOURCE_AUDIT.md", first)],
                ),
            )
            findings = final_adversarial_review_panel_errors(
                folder,
                target_surface_identity=self.target,
                review_policy_assurance=self.policy(2),
            )
        self.assertTrue(
            any("frozen policy requires `2`" in finding.message for finding in findings),
            findings,
        )

    def test_author_identity_and_false_independence_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            digest = self.write_audit(folder, "docs/AGENT_SOURCE_AUDIT.md")
            row = self.review("author-session", "docs/AGENT_SOURCE_AUDIT.md", digest)
            row["independence"] = {
                "did_not_author_or_repair": False,
                "did_not_issue_semantic_judgments": True,
            }
            self.write_panel(folder, self.panel(1, [row]))
            messages = [
                finding.message
                for finding in final_adversarial_review_panel_errors(
                    folder,
                    target_surface_identity=self.target,
                    review_policy_assurance=self.policy(1),
                )
            ]
        self.assertTrue(any("not independent" in message for message in messages), messages)
        self.assertTrue(any("independence must attest" in message for message in messages), messages)


if __name__ == "__main__":
    unittest.main()
