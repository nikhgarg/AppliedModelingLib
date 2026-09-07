#!/usr/bin/env python3
"""Focused tests for non-source-credit configured-assumption regularities."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from scripts import configured_assumption_formalization_regularities as REGULARITY
from scripts import audit_conclusion_provenance as CONCLUSION
from scripts import audit_evidence_integrity as EVIDENCE
from scripts import audit_repository as REPOSITORY
from scripts import source_record_current_revalidation as CURRENT
from scripts.source_record_obligation_groups import raw_source_record_obligation_groups
from scripts.source_record_target_disposition import (
    project_source_record_response_association_pins,
    source_input_target_disposition_errors,
)


DECLARATION = (
    "abbrev presentation_only_wrapper\n"
    "    (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) :=\n"
    "  FixtureModel Ω P"
)
DECLARATION_SHA = "a" * 64
SIGNATURE_SHA = "b" * 64
RAW_AUDIT_SHA = "c" * 64
POLICY = "source-record-v10-semantic-conclusion-boundary-contract"


def raw_item(*, judgment_key: str = "presentation.wrapper.instance", direct: bool = False) -> dict[str, object]:
    item: dict[str, object] = {
        "row": "presentation_only_row",
        "judgment_key": judgment_key,
        "kind": "semantic_unknown_nondata_premise",
        "result_relation": "",
        "expanded_input_type": "MeasurableSpace Ω",
        "input": {"names": "presentation_only_instance", "type": "MeasurableSpace Ω"},
        "effective_lean_source_declaration": DECLARATION,
        "lean_source_declaration": DECLARATION,
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.presentation_only_wrapper",
            "declaration_sha256": DECLARATION_SHA,
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.presentation_only_wrapper",
                "elaborated_signature_sha256": SIGNATURE_SHA,
            }
        ],
        "source_record_item_reuse_eligibility": {
            "eligible": False,
            "blockers": ["no source-content semantic identity"],
        },
    }
    if direct:
        item["source_contract_association"] = {"schema": 2}
    return item


def raw_audit(*, configured: bool = True, direct: bool = False) -> dict[str, object]:
    item = raw_item(direct=direct)
    return {
        "paper": "Fixture",
        "prompt_version": POLICY,
        "source_record_audit_sha256": RAW_AUDIT_SHA,
        "source_record_input_fingerprint": {"source_record_policy_version": POLICY},
        "semantic_model_configured_assumption_rows": (
            ["presentation_only_row"] if configured else []
        ),
        "rows_with_semantic_inputs": [
            {
                "row": "presentation_only_row",
                "effective_lean_source_declaration": DECLARATION,
                "reviewed_elaborated_signature_identities": [
                    {
                        "qualified_declaration": "Fixture.presentation_only_wrapper",
                        "elaborated_signature_sha256": SIGNATURE_SHA,
                    }
                ],
                "visible_inputs": [
                    {"names": "Ω", "type": "Type*"},
                    {"names": "presentation_only_instance", "type": "MeasurableSpace Ω"},
                    {"names": "P", "type": "Measure Ω"},
                ],
            }
        ],
        "boundary_input_items": [item],
        "conclusion_dependency_items": [],
        "recursive_field_items": [],
        "semantic_model_items": [],
    }


def regularity_entry(raw: dict[str, object], source_text: str) -> dict[str, object]:
    item = raw["boundary_input_items"][0]
    assert isinstance(item, dict)
    groups, errors = raw_source_record_obligation_groups(raw)
    assert not errors
    group = next(iter(groups.values()))
    sequence = REGULARITY.binder_sequence_from_declaration(DECLARATION)
    assert sequence is not None
    canonical_type = "MeasurableSpace Ω"
    quote_sha = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
    return {
        "entry_id": "FIXTURE-REGULARITY-1",
        # These fields intentionally have noncanonical navigation labels. The
        # test below proves that they do not select the raw obligation.
        "raw_judgment_key": "wrong.presentation.key",
        "raw_item_section": "boundary_input_items",
        "raw_item_kind": "semantic_unknown_nondata_premise",
        "raw_item_reuse_eligibility": deepcopy(
            item["source_record_item_reuse_eligibility"]
        ),
        "source_record_current_group_descriptor_sha256": group["descriptor_sha256"],
        "reviewed_declaration": {
            "qualified_declaration": "Wrong.Namespace.navigation_only",
            "declaration_sha256": DECLARATION_SHA,
            "elaborated_signature_sha256": SIGNATURE_SHA,
        },
        "structural_input_position": {
            "binder_sequence_sha256": REGULARITY.binder_sequence_sha256(sequence),
            "binder_position_zero_based": 1,
            "binder_info": "instanceImplicit",
            "input_name": "wrong_navigation_name",
            "expanded_input_type": canonical_type,
        },
        "canonical_type": canonical_type,
        "canonical_type_digest_schema": REGULARITY.CANONICAL_TYPE_DIGEST_SCHEMA,
        "canonical_type_sha256": hashlib.sha256(canonical_type.encode("utf-8")).hexdigest(),
        "source_anchors": [
            {
                "source_item": "wrong_navigation_source_item",
                "source_location": "source.txt:1-1",
                "anchor_path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text_sha256": quote_sha,
            }
        ],
        "meaning": "A structural Lean regularity for the source probability carrier.",
        "why_needed": "The formal model needs the typeclass to state its probability objects.",
        "scope_constraints": {
            "is_source_contract": False,
            "can_supply_direct_source_result_credit": False,
            "can_close_unrelated_boundary_inputs": False,
            "applies_only_to_exact_declaration_signature_and_binder_position": True,
            "name_matching_permitted": False,
        },
    }


class ConfiguredAssumptionFormalizationRegularityTests(unittest.TestCase):
    def write_fixture(
        self, raw: dict[str, object], entry: dict[str, object], source_text: str
    ) -> tuple[tempfile.TemporaryDirectory[str], Path, dict[str, object]]:
        temporary = tempfile.TemporaryDirectory()
        paper = Path(temporary.name) / "Fixture"
        (paper / "audit").mkdir(parents=True)
        (paper / "source.txt").write_text(source_text + "\n", encoding="utf-8")
        ledger = {
            "schema": REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_SCHEMA,
            "artifact_kind": REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_ARTIFACT_KIND,
            "status": REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS,
            "paper": "Fixture",
            "raw_receipt": {
                "source_record_audit_sha256": RAW_AUDIT_SHA,
                "source_record_policy_version": POLICY,
                "source_artifact_sha256": hashlib.sha256(
                    (source_text + "\n").encode("utf-8")
                ).hexdigest(),
            },
            "entries": [entry],
        }
        (paper / "audit" / "configured_assumption_formalization_regularities.json").write_text(
            json.dumps(ledger), encoding="utf-8"
        )
        status = {
            "review_surface": {},
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD:
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE,
        }
        (paper / "status.json").write_text(json.dumps(status), encoding="utf-8")
        return temporary, paper, status

    def context_fixture(self) -> tuple[
        tempfile.TemporaryDirectory[str],
        Path,
        dict[str, object],
        dict[str, object],
        dict[str, object],
        REGULARITY.ConfiguredAssumptionFormalizationRegularityContext,
    ]:
        source_text = "Source model regularity."
        raw = raw_audit()
        entry = regularity_entry(raw, source_text)
        temporary, paper, status = self.write_fixture(raw, entry, source_text)
        context, error = REGULARITY.load_configured_assumption_formalization_regularity_context(
            paper, raw, status_payload=status
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(context)
        assert context is not None
        return temporary, paper, status, raw, entry, context

    def response(self, entry: dict[str, object]) -> dict[str, object]:
        return {
            "classification": REGULARITY.FORMALIZATION_REGULARITY_CLASSIFICATION,
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_ID_FIELD: entry[
                "entry_id"
            ],
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_SHA256_FIELD:
            REGULARITY.configured_assumption_formalization_regularity_entry_sha256(
                entry
            ),
            "source_location": "source.txt:1-1",
        }

    def test_current_top_level_raw_policy_version_is_accepted(self) -> None:
        """Current raw receipts keep their policy at receipt level, not in the fingerprint."""

        source_text = "Source model regularity."
        raw = raw_audit()
        raw["source_record_policy_version"] = POLICY
        raw["source_record_input_fingerprint"] = {}
        entry = regularity_entry(raw, source_text)
        temporary, paper, status = self.write_fixture(raw, entry, source_text)
        self.addCleanup(temporary.cleanup)

        context, error = REGULARITY.load_configured_assumption_formalization_regularity_context(
            paper, raw, status_payload=status
        )

        self.assertEqual(error, "")
        self.assertIsNotNone(context)

    def test_structural_entry_projects_and_validates_without_navigation_names(self) -> None:
        temporary, _paper, _status, raw, entry, context = self.context_fixture()
        self.addCleanup(temporary.cleanup)
        groups, errors = raw_source_record_obligation_groups(raw)
        self.assertEqual(errors, {})
        group = next(iter(groups.values()))
        projected, error = project_source_record_response_association_pins(
            group["raw_members"],
            self.response(entry),
            configured_assumption_formalization_regularity_context=context,
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(projected)
        assert projected is not None
        self.assertIn(
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD,
            projected,
        )
        item = raw["boundary_input_items"][0]
        assert isinstance(item, dict)
        self.assertEqual(
            source_input_target_disposition_errors(
                item,
                projected,
                statement_map=None,
                source_proof_fidelity=None,
                configured_assumption_formalization_regularity_context=context,
            ),
            [],
        )

    def test_navigation_labels_do_not_stale_the_semantic_entry_or_context(self) -> None:
        temporary, _paper, _status, raw, entry, context = self.context_fixture()
        self.addCleanup(temporary.cleanup)
        renamed = deepcopy(entry)
        renamed["entry_id"] = "FIXTURE-REGULARITY-RENAMED"
        renamed["raw_judgment_key"] = "different.navigation.judgment"
        renamed["raw_group_descriptor_sha256"] = "0" * 64
        declaration = renamed["reviewed_declaration"]
        assert isinstance(declaration, dict)
        declaration["qualified_declaration"] = "Different.Namespace.navigation_only"
        position = renamed["structural_input_position"]
        assert isinstance(position, dict)
        position["input_name"] = "different_navigation_input"
        anchor = renamed["source_anchors"][0]
        assert isinstance(anchor, dict)
        anchor["source_item"] = "different_navigation_source_item"
        renamed["meaning"] = "Updated reviewer-facing prose only."
        renamed["why_needed"] = "Updated reviewer-facing explanation only."
        source_text = "Source model regularity."
        renamed_temporary, renamed_paper, renamed_status = self.write_fixture(
            raw, renamed, source_text
        )
        self.addCleanup(renamed_temporary.cleanup)
        renamed_context, error = (
            REGULARITY.load_configured_assumption_formalization_regularity_context(
                renamed_paper,
                raw,
                status_payload=renamed_status,
            )
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(renamed_context)
        assert renamed_context is not None
        self.assertEqual(
            REGULARITY.configured_assumption_formalization_regularity_entry_sha256(
                entry
            ),
            REGULARITY.configured_assumption_formalization_regularity_entry_sha256(
                renamed
            ),
        )
        original_match = next(iter(context.matches_by_structural_identity.values()))
        renamed_match = next(
            iter(renamed_context.matches_by_structural_identity.values())
        )
        self.assertEqual(original_match.entry_sha256, renamed_match.entry_sha256)
        self.assertEqual(original_match.context_sha256, renamed_match.context_sha256)

        groups, errors = raw_source_record_obligation_groups(raw)
        self.assertEqual(errors, {})
        projected, projection_error = project_source_record_response_association_pins(
            next(iter(groups.values()))["raw_members"],
            self.response(entry),
            configured_assumption_formalization_regularity_context=renamed_context,
        )
        self.assertEqual(projection_error, "")
        assert projected is not None
        self.assertEqual(
            projected[
                REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_ID_FIELD
            ],
            "FIXTURE-REGULARITY-RENAMED",
        )

    def test_ledger_anchor_tamper_fails_closed(self) -> None:
        source_text = "Source model regularity."
        raw = raw_audit()
        entry = regularity_entry(raw, source_text)
        entry["source_anchors"][0]["quoted_text_sha256"] = "0" * 64
        temporary, paper, status = self.write_fixture(raw, entry, source_text)
        self.addCleanup(temporary.cleanup)
        context, error = REGULARITY.load_configured_assumption_formalization_regularity_context(
            paper, raw, status_payload=status
        )
        self.assertIsNone(context)
        self.assertIn("quoted_text_sha256", error)

    def test_structural_entry_change_fails_closed(self) -> None:
        source_text = "Source model regularity."
        raw = raw_audit()
        entry = regularity_entry(raw, source_text)
        position = entry["structural_input_position"]
        assert isinstance(position, dict)
        position["binder_position_zero_based"] = 0
        temporary, paper, status = self.write_fixture(raw, entry, source_text)
        self.addCleanup(temporary.cleanup)
        context, error = (
            REGULARITY.load_configured_assumption_formalization_regularity_context(
                paper, raw, status_payload=status
            )
        )
        self.assertIsNone(context)
        self.assertIn("same declaration/signature/binder/type shape", error)

    def test_nonconfigured_or_direct_source_input_cannot_use_lane(self) -> None:
        source_text = "Source model regularity."
        raw = raw_audit(configured=False)
        entry = regularity_entry(raw, source_text)
        temporary, paper, status = self.write_fixture(raw, entry, source_text)
        self.addCleanup(temporary.cleanup)
        context, error = REGULARITY.load_configured_assumption_formalization_regularity_context(
            paper, raw, status_payload=status
        )
        self.assertIsNone(context)
        self.assertIn("configured-assumption rows", error)

        direct_raw = raw_audit(direct=True)
        direct_entry = regularity_entry(direct_raw, source_text)
        temporary, paper, status = self.write_fixture(direct_raw, direct_entry, source_text)
        self.addCleanup(temporary.cleanup)
        context, error = REGULARITY.load_configured_assumption_formalization_regularity_context(
            paper, direct_raw, status_payload=status
        )
        self.assertIsNone(context)
        self.assertIn("same declaration/signature/binder/type shape", error)

    def test_source_credit_fields_and_reviewer_context_pin_are_rejected(self) -> None:
        temporary, _paper, _status, raw, entry, context = self.context_fixture()
        self.addCleanup(temporary.cleanup)
        groups, _ = raw_source_record_obligation_groups(raw)
        group = next(iter(groups.values()))
        response = self.response(entry)
        response["source_target_disposition"] = "literal_source_match"
        projected, error = project_source_record_response_association_pins(
            group["raw_members"],
            response,
            configured_assumption_formalization_regularity_context=context,
        )
        self.assertEqual(error, "")
        assert projected is not None
        item = raw["boundary_input_items"][0]
        assert isinstance(item, dict)
        errors = source_input_target_disposition_errors(
            item,
            projected,
            statement_map=None,
            source_proof_fidelity=None,
            configured_assumption_formalization_regularity_context=context,
        )
        self.assertTrue(any("direct-source" in error for error in errors), errors)

        response = self.response(entry)
        response["source_contract_association"] = {"schema": 2}
        projected, error = project_source_record_response_association_pins(
            group["raw_members"],
            response,
            configured_assumption_formalization_regularity_context=context,
        )
        self.assertEqual(error, "")
        assert projected is not None
        errors = source_input_target_disposition_errors(
            item,
            projected,
            statement_map=None,
            source_proof_fidelity=None,
            configured_assumption_formalization_regularity_context=context,
        )
        self.assertTrue(any("source_contract_association" in error for error in errors), errors)

        response = self.response(entry)
        response[
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD
        ] = "0" * 64
        projected, error = project_source_record_response_association_pins(
            group["raw_members"],
            response,
            configured_assumption_formalization_regularity_context=context,
            reject_existing=True,
        )
        self.assertIsNone(projected)
        self.assertIn("reviewer-supplied", error)

    def test_consumers_project_the_lane_but_exclude_source_model_credit(self) -> None:
        temporary, paper, _status, raw, entry, _context = self.context_fixture()
        self.addCleanup(temporary.cleanup)
        key = str(raw["boundary_input_items"][0]["judgment_key"])
        response = self.response(entry)
        sidecar = {
            "schema": 1,
            "paper": "Fixture",
            "prompt_version": POLICY,
            "source_record_audit_sha256": RAW_AUDIT_SHA,
            "validator": "fixture-reviewer",
            "validated_at": "2026-07-28T00:00:00Z",
            "items": {key: response},
        }
        sidecar_path = paper / "audit" / "source_record_match_llm.json"
        sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
        judgments = REPOSITORY.source_record_judgment_items(
            sidecar_path,
            "Fixture",
            current_raw_audit=raw,
            paper_dir=paper,
        )
        self.assertIn(key, judgments)
        self.assertIn(
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD,
            judgments[key],
        )
        # The integrity loader has an independent current-response composition
        # path. The fixture is intentionally narrow, so isolate this test from
        # the unrelated full raw-audit identity predicate.
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            integrity_judgments = EVIDENCE.current_source_record_judgment_items(
                raw,
                sidecar,
                folder=paper,
            )
        self.assertIn(key, integrity_judgments)
        self.assertIn(
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD,
            integrity_judgments[key],
        )
        with patch.object(CONCLUSION, "PAPERS", paper.parent):
            conclusion_judgments = CONCLUSION.current_judgments("Fixture", raw)
        self.assertIn(key, conclusion_judgments)
        self.assertIn(
            REGULARITY.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITY_CONTEXT_SHA256_FIELD,
            conclusion_judgments[key],
        )
        self.assertEqual(
            CURRENT._target_disposition_errors(
                raw,
                {"items": {key: judgments[key]}},
                paper_dir=paper,
            ),
            [],
        )
        self.assertEqual(
            CONCLUSION.source_antecedents_with_classifications(
                conclusion_judgments,
                {"validated_source_assumption", "approved_source_convention"},
            ),
            set(),
        )

        # This helper is the only source-record path that feeds
        # `validated_assumption_premises` in the hidden-premise audit. Even an
        # exact current regularity must not enter that source/model credit set.
        (paper / "audit" / "source_record_audit.json").write_text(
            json.dumps(raw), encoding="utf-8"
        )
        with patch.object(
            REPOSITORY,
            "source_record_judgment_items",
            return_value=judgments,
        ), patch.object(
            REPOSITORY,
            "source_record_target_disposition_rebind_context",
            return_value=(None, ""),
        ):
            self.assertEqual(
                REPOSITORY.source_record_validated_boundary_premises(
                    "Fixture",
                    paper,
                    {},
                    "formalized",
                ),
                set(),
            )


if __name__ == "__main__":
    unittest.main()
