#!/usr/bin/env python3
"""Regression tests for fail-closed paper-coverage bootstrapping."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard  # noqa: E402
from scripts import seed_paper_coverage as seed  # noqa: E402


class SeedPaperCoverageTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.papers = self.root / "papers"
        self.paper = self.papers / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        (self.paper / ".review_traces").mkdir()
        self.interface = self.paper / "PaperInterface.lean"
        self.interface.write_text(
            "namespace FixturePaper\n"
            "/-- Source-facing theorem. -/\n"
            "theorem sourceResult : True := by\n"
            "  trivial\n"
            "end FixturePaper\n",
            encoding="utf-8",
        )
        (self.paper / "status.json").write_text(
            json.dumps({"review_surface": {"paper_coverage_required": True}}),
            encoding="utf-8",
        )
        source = self.paper / "source.txt"
        source.write_text("Theorem 1. A source result.\n", encoding="utf-8")
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": "FixturePaper",
                    "source_coverage_mode": "named_theoretical_statements",
                    "source_curated": True,
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": hashlib.sha256(
                        source.read_bytes()
                    ).hexdigest(),
                    "items": {
                        "sourceResult": {
                            "statement": "Theorem 1. A source result.",
                            "source_location": "source.txt:1",
                            "source_kind": "theorem",
                            "source_url": "https://example.test/source",
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

        patches = (
            mock.patch.object(review_dashboard, "ROOT", self.root),
            mock.patch.object(review_dashboard, "PAPERS_DIR", self.papers),
            mock.patch.object(seed, "ROOT", self.root),
            mock.patch.object(seed, "PAPERS_DIR", self.papers),
        )
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

    def write_current_cache(self) -> None:
        parsed = review_dashboard.parse_review_source_declarations(self.interface)
        kind, name, full_name, signature, _comment, _line, _path = parsed[0]
        payload = {
            "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
            "paper": "FixturePaper",
            "hashes": {
                "review_source_file": "PaperInterface.lean",
                "interface_sha256": review_dashboard.statement_digest(
                    self.interface.read_text(encoding="utf-8")
                ),
            },
            "rows": [
                {
                    "name": name,
                    "kind": kind,
                    "lean_statement": signature,
                    "paper_statement": "A source result.",
                    "agent_statement": "True.",
                    "full_name": full_name,
                    "interface_source": signature,
                    "lean_signature_sha256": "a" * 64,
                }
            ],
        }
        (self.paper / ".review_traces" / "paper_interface_cache.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def test_exact_key_seed_reads_only_current_local_row_cache(self) -> None:
        self.write_current_cache()

        with mock.patch.object(
            review_dashboard,
            "review_items_for_paper",
            side_effect=AssertionError("seed must not trigger Lean extraction"),
        ):
            rows = seed._cached_review_items_for_exact_key_seed(self.paper)

        self.assertEqual([row.name for row in rows], ["sourceResult"])
        payload = seed.seed_payload(
            self.paper,
            "test",
            "script",
            cached_rows=rows,
        )
        item = payload["items"]["sourceResult"]
        self.assertEqual(payload["audit_kind"], "exact_key_scaffold")
        self.assertFalse(payload["source_grounded"])
        self.assertTrue(payload["seed_scaffold"])
        self.assertEqual(item["coverage"], "covered")
        self.assertEqual(item["review_rows"], ["sourceResult"])
        self.assertEqual(item["review_row_signature_sha256"], {"sourceResult": "a" * 64})
        (self.paper / "audit" / "paper_coverage_llm.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        summary = review_dashboard.paper_coverage_audit_summary(self.paper, rows)
        self.assertTrue(summary["audit_is_scaffold"])
        self.assertTrue(summary["missing_source_grounded_audit"])
        self.assertTrue(summary["needs_attention"])

    def test_exact_key_seed_rejects_changed_interface_without_fallback(self) -> None:
        self.write_current_cache()
        self.interface.write_text(
            self.interface.read_text(encoding="utf-8") + "\n-- changed\n",
            encoding="utf-8",
        )

        with mock.patch.object(
            review_dashboard,
            "review_items_for_paper",
            side_effect=AssertionError("seed must not trigger Lean extraction"),
        ):
            with self.assertRaisesRegex(seed.CacheOnlySeedError, "changed"):
                seed._cached_review_items_for_exact_key_seed(self.paper)

    def test_all_uncertain_bootstrap_needs_no_cache_or_row_names(self) -> None:
        with mock.patch.object(
            seed,
            "_cached_review_items_for_exact_key_seed",
            side_effect=AssertionError("all-uncertain mode must not read the row cache"),
        ), mock.patch.object(sys, "argv", ["seed_paper_coverage.py", "--paper", "FixturePaper", "--all-uncertain-bootstrap", "--write"]):
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(seed.main(), 0)

        self.assertIn("mode=all_uncertain_bootstrap", stdout.getvalue())
        payload = json.loads(
            (self.paper / "audit" / "paper_coverage_llm.json").read_text(
                encoding="utf-8"
            )
        )
        self.assertEqual(payload["audit_kind"], "all_uncertain_bootstrap")
        self.assertFalse(payload["source_grounded"])
        self.assertTrue(payload["seed_scaffold"])
        self.assertEqual(payload["review_surface_sha256"], "")
        item = payload["items"]["sourceResult"]
        self.assertEqual(item["coverage"], "uncertain")
        self.assertEqual(item["review_rows"], [])
        self.assertIn("no dashboard row cache", item["reason"])

    def test_source_inventory_precheck_keeps_missing_semantic_coverage_nonblocking(
        self,
    ) -> None:
        summary = review_dashboard.source_inventory_precheck_summary(self.paper)

        self.assertTrue(summary["needs_attention"])
        self.assertFalse(summary["pre_manifest_blocked"])
        self.assertIn(
            "missing paper_coverage_llm.json",
            summary["semantic_coverage_pending"],
        )

        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertFalse(
                review_dashboard.print_source_inventory_precheck_status(
                    "FixturePaper"
                )
            )
        rendered = stdout.getvalue()
        self.assertIn("Source-to-dashboard coverage pending", rendered)
        self.assertIn("does not block a paper-only --refresh-cache", rendered)
        self.assertNotIn("Fix these source-map blockers", rendered)

    def test_source_inventory_precheck_still_blocks_source_map_defects(self) -> None:
        map_path = self.paper / "audit" / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload["items"]["sourceResult"]["source_kind"] = "unknown_result_kind"
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        summary = review_dashboard.source_inventory_precheck_summary(self.paper)
        self.assertTrue(summary["pre_manifest_blocked"])
        self.assertTrue(summary["pre_manifest_blockers"])

        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout):
            self.assertTrue(
                review_dashboard.print_source_inventory_precheck_status(
                    "FixturePaper"
                )
            )
        self.assertIn("Source-map preflight blockers", stdout.getvalue())

    def test_source_inventory_precheck_catches_raw_producer_context_shape(self) -> None:
        map_path = self.paper / "audit" / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload["items"]["sourceResult"]["semantic_context_requirements"] = [
            {
                "semantic_role": "model",
                "source_location": "source.txt:1",
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": "Theorem 1. A source result.",
                        "quoted_text_sha256": hashlib.sha256(
                            b"Theorem 1. A source result."
                        ).hexdigest(),
                    }
                ],
            }
        ]
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        errors = review_dashboard.paper_source_map_structural_errors(self.paper)

        self.assertTrue(any(".kind must be" in error for error in errors))
        self.assertTrue(any(".explanation must be" in error for error in errors))
        summary = review_dashboard.source_inventory_precheck_summary(self.paper)
        self.assertTrue(summary["pre_manifest_blocked"])


if __name__ == "__main__":
    unittest.main()
