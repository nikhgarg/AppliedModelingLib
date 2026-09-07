#!/usr/bin/env python3
"""Focused fail-closed tests for pre-schema5 aggregate receipt reprojection."""

from __future__ import annotations

import copy
import hashlib
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path

from scripts.audit_evidence_integrity import source_record_raw_scan_completeness_error
from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
from scripts.source_record_integrity import (
    source_record_audit_receipt_error,
    source_record_raw_reusable_item_metadata_error,
)
from scripts import source_record_receipt_reprojection as REPROJECTION


PAPER = "FixturePaper"
MAP_SHA = "a" * 64
SOURCE_SHA = "b" * 64
PRIOR_SHA = "c" * 64


def route(row: str) -> REPROJECTION.CurrentReviewRoute:
    return REPROJECTION.CurrentReviewRoute(
        row=row,
        qualified_declaration=f"{PAPER}.PaperInterface.{row}",
        source_file=f"papers/{PAPER}/PaperInterface.lean",
        source_sha256=SOURCE_SHA,
    )


def identity(row: str) -> dict[str, str]:
    return {"qualified_declaration": route(row).qualified_declaration}


def raw_item(row: str, key: str) -> dict[str, object]:
    return {
        "row": row,
        "judgment_key": key,
        "kind": "fixture",
        "source_record_item_sha256": "d" * 64,
        "source_contract_association": {"schema": 1},
    }


def semantic_item(row: str) -> dict[str, object]:
    return {
        "row": row,
        "judgment_key": f"semantic-model::{row}",
        "dimensions": [],
        "source_statement_association": {
            "reviewed_declaration_identity": identity(row),
        },
        "source_record_item_sha256": "e" * 64,
    }


class SourceRecordReceiptReprojectionTests(unittest.TestCase):
    def write_current_default_mode_map(
        self, root: Path, *, source_status: str = "under_review"
    ) -> bytes:
        """Write the one exact map spelling admitted by the legacy transport."""

        path = root / "papers" / PAPER / "audit" / "paper_statement_map.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        contents = (
            "{\n"
            '  "source_coverage_mode": "named_theoretical_statements",\n'
            '  "items": {\n'
            '    "source_item": {\n'
            '      "source_kind": "theorem",\n'
            '      "title": "Theorem 1",\n'
            '      "statement": "Every input has a witness.",\n'
            f'      "source_status": "{source_status}"\n'
            "    }\n"
            "  }\n"
            "}\n"
        ).encode("utf-8")
        path.write_bytes(contents)
        return contents

    def context_for_map(self, root: Path, contents: bytes) -> REPROJECTION.CurrentReprojectionContext:
        return replace(
            self.context(root),
            paper_statement_map_sha256=hashlib.sha256(contents).hexdigest(),
        )

    def context(self, root: Path, selected: tuple[str, ...] = ("current",)) -> REPROJECTION.CurrentReprojectionContext:
        paper_dir = root / "papers" / PAPER
        paper_dir.mkdir(parents=True, exist_ok=True)
        interface = {
            "path": f"papers/{PAPER}/PaperInterface.lean",
            "sha256": SOURCE_SHA,
        }
        fingerprint = {
            "schema": 6,
            "paper": PAPER,
            "no_lean": False,
            "max_depth": 4,
            "source_record_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            "review_interface_source": interface,
        }
        selected_routes = tuple(route(row) for row in selected)
        return REPROJECTION.CurrentReprojectionContext(
            paper=PAPER,
            paper_dir=paper_dir,
            import_module=f"{PAPER}.PaperInterface",
            paper_statement_map_sha256=MAP_SHA,
            input_fingerprint=fingerprint,
            review_interface_source=interface,
            review_assumption_source=None,
            configured_review_row_count=2,
            selected_routes=selected_routes,
            source_coverage={
                "source_coverage_mode": "named_theoretical_statements",
                "source_coverage_selected_source_items": ["source_item"],
                "source_coverage_mode_error": "",
                "source_coverage_route_errors": [],
                "source_coverage_unrouted_source_items": [],
                "out_of_mode_review_surface_rows": ["old"],
            },
            semantic_selection={
                "semantic_model_source_selected_rows": list(selected),
                "semantic_model_configured_assumption_rows": [],
                "semantic_model_scope_target_declarations": [],
                "semantic_model_scope_target_rows": [],
                "semantic_model_scope_target_route_errors": [],
            },
            semantic_model_dimensions=(),
            semantic_model_configuration_errors=(),
            semantic_context_requirements=(),
            source_proof_fidelity=None,
            formalization_scope=None,
            unconfigured_review_surface_rows=(),
            unconfigured_assumption_support_rows=(),
            quarantined_auxiliary_review_rows=(),
        )

    def raw(self) -> dict[str, object]:
        routes = [route("current"), route("old")]
        checked = [
            {"row": value.row, "qualified_declaration": value.qualified_declaration}
            for value in routes
        ]
        fresh = {
            "mode": "isolated_temp_overlay",
            "returncode": 0,
            "source_file": routes[0].source_file,
            "source_sha256": routes[0].source_sha256,
        }
        return {
            "paper": PAPER,
            "paper_dir": f"papers/{PAPER}",
            "import_module": f"{PAPER}.PaperInterface",
            "prompt_version": REPROJECTION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": REPROJECTION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": "f" * 64,
            "paper_statement_map_sha256": MAP_SHA,
            "review_interface_source": {
                "path": routes[0].source_file,
                "sha256": routes[0].source_sha256,
            },
            "review_assumption_source": None,
            "source_proof_fidelity": None,
            "formalization_scope": None,
            "semantic_context_requirements": [],
            "semantic_context_requirements_sha256": "",
            "missing_configured_review_rows": [],
            "recursion_failures": [],
            "recursion_failure_count": 0,
            "source_contract_association_errors": [],
            "source_contract_association_error_count": 0,
            "source_contract_association_counts": {},
            "semantic_model_review_configuration_errors": [],
            "constructor_result_type_check_error": "",
            "source_premise_consistency_error": "",
            "source_premise_consistency_schema": 1,
            "source_premise_consistency_items": [],
            "source_premise_consistency_item_count": 0,
            "current_source_record_judgment_count": 0,
            "configured_review_rows": [
                {
                    **value.as_raw_row(),
                    "lean_source_declaration": f"theorem {value.row} : True := trivial",
                }
                for value in routes
            ],
            "configured_review_rows_count": 2,
            "configured_review_row_count": 2,
            "review_row_count": 2,
            "lean_check": {
                "returncode": 0,
                "requested_checked_rows": checked,
                "checked_rows": copy.deepcopy(checked),
                "fresh_source_elaboration": fresh,
            },
            "fresh_source_elaboration": copy.deepcopy(fresh),
            "boundary_input_items": [
                raw_item("current", "current.h : True"),
                raw_item("old", "old.h : True"),
            ],
            "conclusion_dependency_items": [raw_item("current", "current.result : True")],
            "type_valued_certificate_result_items": [],
            "recursive_field_items": [],
            "semantic_model_items": [semantic_item("current"), semantic_item("old")],
            "rows_with_record_premises": [],
            "rows_with_semantic_inputs": [
                {"row": "current", "source_record_item_sha256": "9" * 64},
                {"row": "old", "source_record_item_sha256": "9" * 64},
            ],
            "row_visible_inputs": {"current": [], "old": []},
            "row_conclusion_inputs": {},
            "expected_input_judgment_keys": ["current.h : True", "old.h : True"],
            "expected_field_judgment_keys": [],
            "expected_semantic_model_judgment_keys": [
                "semantic-model::current",
                "semantic-model::old",
            ],
            "boundary_input_count": 2,
            "conclusion_dependency_count": 1,
            "type_valued_certificate_result_count": 0,
            "recursive_field_count": 0,
            "semantic_model_item_count": 2,
            "statement_ledger_covered_boundary_input_keys": [],
            "precloseout_contract_covered_boundary_input_keys": [],
            "precloseout_exact_contract_projection": {
                "items": [],
                "covered_boundary_input_keys": [],
                "covered_boundary_input_keys_sha256": REPROJECTION._canonical_digest([]),
            },
            "resolved_conclusion_dependency_count": 0,
            "resolved_conclusion_dependency_items": [],
            "unresolved_conclusion_dependency_count": 1,
            "unresolved_conclusion_dependency_items": [raw_item("current", "current.result : True")],
            "source_record_judgment_file": "audit/source_record_match_llm.json",
            "llm_judge_prompt": "old prompt",
            "unconfigured_review_surface_rows": [],
            "unconfigured_paper_interface_rows": [],
            "unconfigured_assumption_support_rows": [],
            "quarantined_auxiliary_review_rows": [],
        }

    def build(self) -> dict[str, object]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        return REPROJECTION.build_aggregate_only_reprojection(
            self.raw(),
            context=self.context(Path(temporary.name)),
            prior_raw_reference=f"papers/{PAPER}/audit/source_record_audit.pre_schema5.json",
            prior_raw_sha256=PRIOR_SHA,
        )

    def test_deletion_only_projection_binds_current_receipts_but_no_item_reuse(self) -> None:
        payload = self.build()
        self.assertEqual(payload["review_row_count"], 1)
        self.assertEqual(payload["configured_review_rows_count"], 1)
        self.assertEqual(payload["configured_review_row_count"], 2)
        self.assertEqual(
            [item["row"] for item in payload["boundary_input_items"]], ["current"]
        )
        self.assertEqual(
            [item["row"] for item in payload["semantic_model_items"]], ["current"]
        )
        self.assertEqual(
            payload["lean_check"]["requested_checked_rows"],
            payload["lean_check"]["checked_rows"],
        )
        self.assertEqual(len(payload["lean_check"]["checked_rows"]), 1)
        self.assertEqual(source_record_audit_receipt_error(payload), "")
        self.assertEqual(
            source_record_raw_reusable_item_metadata_error(
                payload, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            ),
            "",
        )
        self.assertEqual(source_record_raw_scan_completeness_error(payload), "")
        for section in REPROJECTION.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
            for item in payload.get(section, []):
                self.assertFalse(item["source_record_item_reuse_eligibility"]["eligible"])
                self.assertNotIn("source_record_item_sha256", item)
        metadata = payload[REPROJECTION.SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD]
        self.assertEqual(
            metadata["item_reuse_mode"],
            "aggregate_only_pending_focused_signature_manifest",
        )

    def test_added_current_route_is_not_matched_by_name_or_shape(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(
                REPROJECTION.SourceRecordReceiptReprojectionError,
                "not present in the prior raw audit",
            ):
                REPROJECTION.build_aggregate_only_reprojection(
                    self.raw(),
                    context=self.context(Path(temporary), ("current", "new")),
                    prior_raw_reference="papers/FixturePaper/audit/prior.json",
                    prior_raw_sha256=PRIOR_SHA,
                )

    def test_existing_judgment_cannot_be_rebound(self) -> None:
        raw = self.raw()
        raw["current_source_record_judgment_count"] = 1
        with tempfile.TemporaryDirectory() as temporary:
            with self.assertRaisesRegex(
                REPROJECTION.SourceRecordReceiptReprojectionError,
                "judgments; judgment rebinding is forbidden",
            ):
                REPROJECTION.build_aggregate_only_reprojection(
                    raw,
                    context=self.context(Path(temporary)),
                    prior_raw_reference="papers/FixturePaper/audit/prior.json",
                    prior_raw_sha256=PRIOR_SHA,
                )

    def test_exact_default_mode_omission_reprojects_only_byte_identical_prior_map(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            current_bytes = self.write_current_default_mode_map(root)
            prior_bytes = current_bytes.replace(
                b'  "source_coverage_mode": "named_theoretical_statements",\n',
                b"",
                1,
            )
            raw = self.raw()
            raw["paper_statement_map_sha256"] = hashlib.sha256(prior_bytes).hexdigest()
            payload = REPROJECTION.build_aggregate_only_reprojection(
                raw,
                context=self.context_for_map(root, current_bytes),
                prior_raw_reference="papers/FixturePaper/audit/prior.json",
                prior_raw_sha256=PRIOR_SHA,
            )

        reprojection = payload[REPROJECTION.SOURCE_RECORD_AGGREGATE_REPROJECTION_FIELD]
        delta = reprojection["paper_statement_map_exact_default_mode_delta"]
        self.assertEqual(
            delta["kind"], "exact_top_level_default_source_coverage_mode_omission"
        )
        self.assertEqual(
            delta["prior_paper_statement_map_sha256"], raw["paper_statement_map_sha256"]
        )
        self.assertEqual(
            delta["current_paper_statement_map_sha256"],
            hashlib.sha256(current_bytes).hexdigest(),
        )
        self.assertEqual(
            delta["prior_effective_source_coverage_mode"],
            "named_theoretical_statements",
        )
        self.assertEqual(
            delta["current_effective_source_coverage_mode"],
            "named_theoretical_statements",
        )
        self.assertEqual(delta["selected_semantic_item_count"], 1)

    def test_exact_default_mode_omission_rejects_any_other_map_drift(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            current_bytes = self.write_current_default_mode_map(
                root, source_status="resolved"
            )
            prior_bytes = current_bytes.replace(
                b'  "source_coverage_mode": "named_theoretical_statements",\n',
                b"",
                1,
            ).replace(b'"source_status": "resolved"', b'"source_status": "under_review"')
            raw = self.raw()
            raw["paper_statement_map_sha256"] = hashlib.sha256(prior_bytes).hexdigest()
            with self.assertRaisesRegex(
                REPROJECTION.SourceRecordReceiptReprojectionError,
                "does not reproduce the prior statement-map bytes",
            ):
                REPROJECTION.build_aggregate_only_reprojection(
                    raw,
                    context=self.context_for_map(root, current_bytes),
                    prior_raw_reference="papers/FixturePaper/audit/prior.json",
                    prior_raw_sha256=PRIOR_SHA,
                )

    def test_exact_default_mode_omission_rejects_noncanonical_json_spelling(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            path = root / "papers" / PAPER / "audit" / "paper_statement_map.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            current_bytes = (
                "{\n"
                '"source_coverage_mode": "named_theoretical_statements",\n'
                '"items": {"source_item": {"source_kind": "theorem", "title": "Theorem 1", '
                '"statement": "Every input has a witness."}}\n'
                "}\n"
            ).encode("utf-8")
            path.write_bytes(current_bytes)
            prior_bytes = current_bytes.replace(
                b'"source_coverage_mode": "named_theoretical_statements",\n',
                b"",
                1,
            )
            raw = self.raw()
            raw["paper_statement_map_sha256"] = hashlib.sha256(prior_bytes).hexdigest()
            with self.assertRaisesRegex(
                REPROJECTION.SourceRecordReceiptReprojectionError,
                "lacks one exact top-level default coverage-mode entry",
            ):
                REPROJECTION.build_aggregate_only_reprojection(
                    raw,
                    context=self.context_for_map(root, current_bytes),
                    prior_raw_reference="papers/FixturePaper/audit/prior.json",
                    prior_raw_sha256=PRIOR_SHA,
                )

    def test_focused_manifest_is_bound_to_exact_reprojected_raw_receipt(self) -> None:
        payload = self.build()
        manifest = {
            route("current").qualified_declaration: {
                "schema": 2,
                "declaration_kind": "theorem",
                "conclusion_mode": "type_only",
                "atoms": [
                    {
                        "ref": "result",
                        "role": "conclusion",
                        "canonical": {"tag": "sort", "level": 0},
                        "display": "True",
                    }
                ],
            }
        }
        artifact = REPROJECTION._focused_signature_manifest_payload(
            payload, paper=PAPER, manifests=manifest
        )
        self.assertEqual(
            REPROJECTION.focused_signature_manifest_error(
                payload, artifact, paper=PAPER
            ),
            "",
        )
        artifact["source_record_audit_sha256"] = "0" * 64
        self.assertIn(
            "does not match raw audit",
            REPROJECTION.focused_signature_manifest_error(payload, artifact, paper=PAPER),
        )


if __name__ == "__main__":
    unittest.main()
