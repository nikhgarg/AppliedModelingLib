#!/usr/bin/env python3
"""Regressions for content-addressed saved-status reuse projections."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from saved_status_reuse import (  # noqa: E402
    coverage_disposition,
    statement_disposition,
    validated_coverage_source_bindings,
)
from scripts import review_dashboard  # noqa: E402
from source_coverage_scope import (  # noqa: E402
    PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    legacy_source_item_coverage_sha256_before_navigation_key_exclusion,
    source_item_coverage_sha256,
)


def digest(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


class SavedStatusReuseProjectionTests(unittest.TestCase):
    def fixture(self, root: Path) -> Path:
        folder = root / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        source_statement = "Every fixture satisfies the advertised property."
        statement_map = {
            "schema": 1,
            "paper": folder.name,
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "source-navigation": {
                    "statement": f"Theorem 1. {source_statement}",
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_status": "exact",
                    "lean_declarations": ["Fixture.reviewNavigation"],
                }
            },
        }
        statement_review = {
            "schema": 1,
            "paper": folder.name,
            "prompt_version": "statement-match-v10-semantic-fidelity-seat-stopping",
            "validator": "fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-07-31T12:00:00Z",
            "items": {
                "review-navigation": {
                    "judgment": "matches",
                    "resolution": "",
                    "reason": "The source and Lean propositions have the same semantics.",
                    "lean_signature_sha256": "1" * 64,
                    "paper_statement_sha256": digest(source_statement),
                    "tex_statement_sha256": "2" * 64,
                }
            },
        }
        status = {
            "review_surface": {
                "include_names": ["review-navigation"],
                "assumption_names": ["assumption-navigation"],
            }
        }
        assumption_review = {
            "schema": 1,
            "paper": folder.name,
            "prompt_version": "assumption-provenance-v3-semantic-exact-premise-source",
            "validator": "fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-07-31T12:00:00Z",
            "items": {
                "assumption-navigation": {
                    "judgment": "paper_condition",
                    "reason": "The source explicitly imposes this domain condition.",
                    "lean_statement_sha256": "3" * 64,
                    "paper_statement_sha256": "4" * 64,
                }
            },
        }
        coverage = {
            "schema": 1,
            "paper": folder.name,
            "audit_kind": "source_to_dashboard_agent",
            "source_grounded": True,
            "prompt_version": "paper-coverage-v5-semantic-proof-row-signature-pins",
            "validator": "fixture reviewer",
            "validator_type": "agent",
            "validated_at": "2026-07-31T12:00:00Z",
            "items": {
                "source-navigation": {
                    "coverage": "covered",
                    "review_rows": ["review-navigation"],
                    "support_declarations": [],
                    "reason": "The exact source proposition is proved by the reviewed row.",
                    "source_evidence": "The pinned source quote states the proposition.",
                }
            },
        }
        for name, payload in (
            ("paper_statement_map.json", statement_map),
            ("statement_match_llm.json", statement_review),
            ("assumption_match_llm.json", assumption_review),
        ):
            (audit / name).write_text(json.dumps(payload, indent=2), encoding="utf-8")
        (folder / "status.json").write_text(
            json.dumps(status, indent=2), encoding="utf-8"
        )
        full_inventory, selected_inventory, mode, mode_error = (
            review_dashboard.paper_coverage_inventory(folder)
        )
        if mode_error or set(selected_inventory) != {"source-navigation"}:
            raise AssertionError(mode_error or "fixture source selection changed")
        selected_item = selected_inventory["source-navigation"]
        coverage_item = coverage["items"]["source-navigation"]
        coverage_item["source_item_coverage_digest_schema"] = (
            SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        )
        coverage_item["source_item_coverage_sha256"] = source_item_coverage_sha256(
            selected_item,
            mode,
        )
        coverage["paper_statement_inventory_sha256"] = (
            review_dashboard.paper_coverage_inventory_digest(
                selected_inventory,
                mode=mode,
                statement_map_payload=statement_map,
            )
        )
        (audit / "paper_coverage_llm.json").write_text(
            json.dumps(coverage, indent=2), encoding="utf-8"
        )
        return folder

    def load(self, folder: Path, name: str) -> dict[str, object]:
        return json.loads((folder / "audit" / name).read_text(encoding="utf-8"))

    def write(self, folder: Path, name: str, payload: object) -> None:
        (folder / "audit" / name).write_text(
            json.dumps(payload, indent=2), encoding="utf-8"
        )

    def test_validated_source_bindings_are_name_free_copied_tuples(self) -> None:
        raw = [
            {
                "source_map_item_semantic_sha256": "2" * 64,
                "source_item_semantic_sha256": "4" * 64,
            },
            {
                "source_map_item_semantic_sha256": "1" * 64,
                "source_item_semantic_sha256": "3" * 64,
            },
        ]

        bindings = validated_coverage_source_bindings(raw)
        raw[0]["source_map_item_semantic_sha256"] = "f" * 64

        self.assertIsInstance(bindings, tuple)
        self.assertEqual(len(bindings), 2)
        self.assertNotIn(
            "f" * 64,
            {binding["source_map_item_semantic_sha256"] for binding in bindings},
        )
        self.assertTrue(
            all(
                set(binding)
                == {
                    "source_map_item_semantic_sha256",
                    "source_item_semantic_sha256",
                }
                for binding in bindings
            )
        )

    def test_validated_source_bindings_reject_nonbijective_receipts(self) -> None:
        duplicate = [
            {
                "source_map_item_semantic_sha256": "1" * 64,
                "source_item_semantic_sha256": "2" * 64,
            },
            {
                "source_map_item_semantic_sha256": "3" * 64,
                "source_item_semantic_sha256": "2" * 64,
            },
        ]

        with self.assertRaisesRegex(ValueError, "not bijective"):
            validated_coverage_source_bindings(duplicate)

    def test_navigation_renames_preserve_semantic_dispositions(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            statement_before, _ = statement_disposition(folder)
            coverage_before, _ = coverage_disposition(folder)

            statement_map = self.load(folder, "paper_statement_map.json")
            source = statement_map["items"].pop("source-navigation")
            source["lean_declarations"] = ["Renamed.reviewNavigation"]
            statement_map["items"]["renamed-source-navigation"] = source
            self.write(folder, "paper_statement_map.json", statement_map)

            statement_review = self.load(folder, "statement_match_llm.json")
            row = statement_review["items"].pop("review-navigation")
            statement_review["items"]["renamed-review-navigation"] = row
            self.write(folder, "statement_match_llm.json", statement_review)
            status = json.loads((folder / "status.json").read_text())
            status["review_surface"]["include_names"] = ["renamed-review-navigation"]
            (folder / "status.json").write_text(json.dumps(status, indent=2))

            coverage = self.load(folder, "paper_coverage_llm.json")
            item = coverage["items"].pop("source-navigation")
            item["review_rows"] = ["renamed-review-navigation"]
            coverage["items"]["renamed-source-navigation"] = item
            self.write(folder, "paper_coverage_llm.json", coverage)

            statement_after, statement_problem = statement_disposition(folder)
            coverage_after, coverage_problem = coverage_disposition(folder)

        self.assertIsNone(statement_problem)
        self.assertIsNone(coverage_problem)
        self.assertEqual(statement_before.sha256, statement_after.sha256)
        self.assertEqual(coverage_before.sha256, coverage_after.sha256)

    def test_keyful_schema_five_digest_migrates_only_under_its_current_key(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            statement_map = self.load(folder, "paper_statement_map.json")
            _full, selected, mode, mode_error = (
                review_dashboard.paper_coverage_inventory(folder)
            )
            self.assertFalse(mode_error)
            item = selected["source-navigation"]
            coverage = self.load(folder, "paper_coverage_llm.json")
            coverage["items"]["source-navigation"][
                "source_item_coverage_sha256"
            ] = legacy_source_item_coverage_sha256_before_navigation_key_exclusion(
                item, mode
            )
            coverage["items"]["source-navigation"][
                "source_item_coverage_digest_schema"
            ] = PREVIOUS_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            self.write(folder, "paper_coverage_llm.json", coverage)

            migrated, migrated_problem = coverage_disposition(folder)
            self.assertIsNone(migrated_problem)
            self.assertIsNotNone(migrated)

            source = statement_map["items"].pop("source-navigation")
            statement_map["items"]["renamed-source-navigation"] = source
            self.write(folder, "paper_statement_map.json", statement_map)
            row = coverage["items"].pop("source-navigation")
            coverage["items"]["renamed-source-navigation"] = row
            self.write(folder, "paper_coverage_llm.json", coverage)

            stale, stale_problem = coverage_disposition(folder)

        self.assertIsNone(stale)
        self.assertIn(
            "legacy coverage row has no current aggregate source identity",
            stale_problem.reason,
        )

    def test_only_configured_statement_rows_are_counted(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            payload = self.load(folder, "statement_match_llm.json")
            payload["items"]["auxiliary-navigation"] = {
                **payload["items"]["review-navigation"],
                "lean_signature_sha256": "5" * 64,
                "paper_statement_sha256": "6" * 64,
                "tex_statement_sha256": "7" * 64,
            }
            self.write(folder, "statement_match_llm.json", payload)

            disposition, problem = statement_disposition(folder)

        self.assertIsNone(problem)
        self.assertEqual(disposition.counts["total"], 1)
        self.assertEqual(disposition.counts["matches"], 1)
        self.assertEqual(disposition.counts["source_condition_rows"], 1)

    def test_unresolved_configured_navigation_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            status = json.loads((folder / "status.json").read_text())
            status["review_surface"]["include_names"] = ["missing-navigation"]
            (folder / "status.json").write_text(json.dumps(status, indent=2))

            disposition, problem = statement_disposition(folder)

        self.assertIsNone(disposition)
        self.assertIn("no current sidecar item", problem.reason)

    def test_statement_judgment_change_changes_disposition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            before, _ = statement_disposition(folder)
            payload = self.load(folder, "statement_match_llm.json")
            item = payload["items"]["review-navigation"]
            item["judgment"] = "mismatch"
            item["resolution"] = "conditional_boundary"
            self.write(folder, "statement_match_llm.json", payload)
            after, problem = statement_disposition(folder)

        self.assertIsNone(problem)
        self.assertNotEqual(before.sha256, after.sha256)
        self.assertEqual(after.counts["formalization_boundary"], 1)

    def test_coverage_judgment_change_changes_disposition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            before, _ = coverage_disposition(folder)
            payload = self.load(folder, "paper_coverage_llm.json")
            payload["items"]["source-navigation"]["coverage"] = "covered_with_boundary"
            self.write(folder, "paper_coverage_llm.json", payload)
            after, problem = coverage_disposition(folder)

        self.assertIsNone(problem)
        self.assertNotEqual(before.sha256, after.sha256)
        self.assertEqual(after.counts["conditional_boundary"], 1)

    def test_coverage_counts_only_selected_source_surface(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            statement_map = self.load(folder, "paper_statement_map.json")
            statement_map["items"]["figure-navigation"] = {
                "statement": "A simulation caption.",
                "source_kind": "figure",
                "claim_bearing": False,
                "source_status": "deep_audit_only",
            }
            self.write(folder, "paper_statement_map.json", statement_map)
            coverage = self.load(folder, "paper_coverage_llm.json")
            coverage["items"]["figure-navigation"] = "diagnostic-only malformed row"
            self.write(folder, "paper_coverage_llm.json", coverage)

            disposition, problem = coverage_disposition(folder)

        self.assertIsNone(problem)
        self.assertEqual(disposition.counts["total"], 1)
        self.assertEqual(disposition.counts["covered"], 1)

    def test_selected_coverage_recorded_digest_must_equal_current_map(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            coverage = self.load(folder, "paper_coverage_llm.json")
            coverage["items"]["source-navigation"]["source_item_coverage_sha256"] = (
                "f" * 64
            )
            self.write(folder, "paper_coverage_llm.json", coverage)

            disposition, problem = coverage_disposition(folder)

        self.assertIsNone(disposition)
        self.assertIn("disagrees with the current map", problem.reason)

    def test_legacy_digest_requires_current_aggregate_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            coverage = self.load(folder, "paper_coverage_llm.json")
            item = coverage["items"]["source-navigation"]
            item["source_item_coverage_digest_schema"] = 4
            item["source_item_coverage_sha256"] = "f" * 64
            self.write(folder, "paper_coverage_llm.json", coverage)

            current, current_problem = coverage_disposition(folder)
            self.assertIsNone(current_problem)
            self.assertIsNotNone(current)

            coverage["paper_statement_inventory_sha256"] = "0" * 64
            self.write(folder, "paper_coverage_llm.json", coverage)
            stale, stale_problem = coverage_disposition(folder)

        self.assertIsNone(stale)
        self.assertIn("no current aggregate", stale_problem.reason)

    def test_missing_explicit_default_mode_is_an_administrative_migration(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            before, before_problem = coverage_disposition(folder)
            self.assertIsNone(before_problem)
            statement_map = self.load(folder, "paper_statement_map.json")
            del statement_map["source_coverage_mode"]
            self.write(folder, "paper_statement_map.json", statement_map)

            after, problem = coverage_disposition(folder)

        self.assertIsNone(problem)
        self.assertEqual(before.sha256, after.sha256)

    def test_selected_coverage_requires_semantic_bijection(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            baseline, baseline_problem = coverage_disposition(folder)
            self.assertIsNone(baseline_problem)
            source_digest = baseline.source_bindings[0]["source_item_semantic_sha256"]
            coverage = self.load(folder, "paper_coverage_llm.json")
            coverage["items"]["source-navigation"]["source_item_coverage_sha256"] = (
                source_digest
            )
            duplicate = copy.deepcopy(coverage["items"]["source-navigation"])
            coverage["items"]["renamed-duplicate"] = duplicate
            self.write(folder, "paper_coverage_llm.json", coverage)

            disposition, duplicate_problem = coverage_disposition(folder)
            self.assertIsNone(disposition)
            del coverage["items"]["renamed-duplicate"]
            del coverage["items"]["source-navigation"]
            coverage["items"]["deep-diagnostic"] = {"coverage": "out_of_scope"}
            self.write(folder, "paper_coverage_llm.json", coverage)
            disposition, missing_problem = coverage_disposition(folder)

        self.assertIn("multiple coverage rows", duplicate_problem.reason)
        self.assertIsNone(disposition)
        self.assertIn("not a bijection", missing_problem.reason)

    def test_semantic_source_rename_succeeds_but_unresolved_support_fails(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            original = self.load(folder, "paper_coverage_llm.json")

            missing_source = copy.deepcopy(original)
            item = missing_source["items"].pop("source-navigation")
            missing_source["items"]["unknown-source-navigation"] = item
            self.write(folder, "paper_coverage_llm.json", missing_source)
            renamed_disposition, source_problem = coverage_disposition(folder)
            self.assertIsNone(source_problem)
            self.assertIsNotNone(renamed_disposition)

            support_only = copy.deepcopy(original)
            item = support_only["items"]["source-navigation"]
            item["coverage"] = "support_only"
            item["review_rows"] = []
            item["support_declarations"] = ["unknown-support-navigation"]
            self.write(folder, "paper_coverage_llm.json", support_only)
            disposition, support_problem = coverage_disposition(folder)

        self.assertIsNone(disposition)
        self.assertIn("configured semantic identity", support_problem.reason)

    def test_coverage_can_target_exact_configured_source_condition(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            coverage = self.load(folder, "paper_coverage_llm.json")
            coverage["items"]["source-navigation"]["review_rows"] = [
                "assumption-navigation"
            ]
            self.write(folder, "paper_coverage_llm.json", coverage)

            disposition, problem = coverage_disposition(folder)

        self.assertIsNone(problem)
        self.assertEqual(disposition.counts["covered"], 1)

    def test_coverage_targets_cannot_use_unconfigured_sidecar_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self.fixture(Path(temporary))
            statement_review = self.load(folder, "statement_match_llm.json")
            auxiliary = copy.deepcopy(statement_review["items"]["review-navigation"])
            auxiliary["lean_signature_sha256"] = "5" * 64
            auxiliary["paper_statement_sha256"] = "6" * 64
            auxiliary["tex_statement_sha256"] = "7" * 64
            statement_review["items"]["auxiliary-navigation"] = auxiliary
            self.write(folder, "statement_match_llm.json", statement_review)

            direct = self.load(folder, "paper_coverage_llm.json")
            direct["items"]["source-navigation"]["review_rows"] = [
                "auxiliary-navigation"
            ]
            self.write(folder, "paper_coverage_llm.json", direct)
            disposition, review_problem = coverage_disposition(folder)
            self.assertIsNone(disposition)

            support = self.load(folder, "paper_coverage_llm.json")
            support_item = support["items"]["source-navigation"]
            support_item["coverage"] = "support_only"
            support_item["review_rows"] = []
            support_item["support_declarations"] = ["auxiliary-navigation"]
            self.write(folder, "paper_coverage_llm.json", support)
            disposition, support_problem = coverage_disposition(folder)

        self.assertIn("configured semantic identity", review_problem.reason)
        self.assertIsNone(disposition)
        self.assertIn("configured semantic identity", support_problem.reason)


if __name__ == "__main__":
    unittest.main()
