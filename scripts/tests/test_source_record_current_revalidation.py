#!/usr/bin/env python3
"""Focused tests for attested aggregate-current source-record revalidation."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_current_revalidation as REVALIDATION  # noqa: E402
from scripts import source_record_obligation_groups as OBLIGATIONS  # noqa: E402
from scripts import (  # noqa: E402
    source_record_current_revalidation_sidecar_binding as SIDECAR_BINDING,
)
from scripts import source_record_target_disposition as TARGET  # noqa: E402
from scripts.formalization_protocol import (  # noqa: E402
    FORMALIZATION_COVERAGE_PROTOCOL_FIELD,
    formalization_coverage_protocol_digest,
)
from scripts.source_record_integrity import (  # noqa: E402
    stamp_source_record_audit_receipts,
)
from scripts.source_record_projection_contract import (  # noqa: E402
    SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD,
    SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD,
)
from scripts.source_record_target_disposition import (  # noqa: E402
    recursive_field_parent_route_record_digest,
    semantic_association_record_digest,
)


PAPER = "FixturePaper"
PROMPT = OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION


def digest(char: str) -> str:
    return char * 64


def raw_item(key: str = "named_result.h : P") -> dict[str, object]:
    qualified = f"{PAPER}.PaperInterface.named_result"
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "expanded_input_type": "P",
        "expanded_lean_surface": {
            "input_type": "P",
            "result_type": "Q",
            "semantic_shape": {"is_proposition": True},
        },
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified,
            "declaration_sha256": digest("a"),
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": digest("b"),
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("c"),
        "source_record_item_context_sha256": digest("d"),
        "source_record_item_sha256": digest("e"),
    }


def raw_item_with_direct_source_contract(
    key: str = "named_result.h : P",
) -> dict[str, object]:
    """Return one direct schema-2 source-pinned boundary input."""

    item = raw_item(key)
    qualified = str(item["reviewed_declaration_identity"]["qualified_declaration"])
    signature = {
        "qualified_declaration": qualified,
        "elaborated_signature_sha256": digest("b"),
    }
    association = {
        "schema": 2,
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [
            {
                "source_key": "source_item",
                "source_location": "source.txt:1-1",
                "source_map_item_sha256": digest("c"),
                "source_semantic_sha256": digest("d"),
            }
        ],
    }
    association["semantic_association_sha256"] = semantic_association_record_digest(
        [digest("d")], signature
    )
    item["source_contract_association"] = association
    return item


def direct_routed_recursive_field_item(
    key: str = "Fixture.Record.leaf"
) -> dict[str, object]:
    """Return a generated recursive member whose parent owns classification."""

    item = raw_item(key)
    item.pop("kind")
    route: dict[str, object] = {
        "schema": 1,
        "inheritance_mode": "explicit_parent_route_and_field_scope",
        "field_chain": [{"structure": "Fixture.Record", "field": "leaf"}],
    }
    route["association_sha256"] = recursive_field_parent_route_record_digest(route)
    item["recursive_field_explicit_parent_route"] = route
    return item


def raw_audit(*, key: str = "named_result.h : P") -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": [raw_item(key)],
        "lean_check": {"returncode": 0},
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def raw_audit_with_direct_source_contract(
    *, key: str = "named_result.h : P"
) -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": [raw_item_with_direct_source_contract(key)],
        "lean_check": {"returncode": 0},
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def raw_audit_with_semantic_model(*, key: str = "named_result.h : P") -> dict[str, object]:
    """Fixture with a generated semantic-model group sharing one judgment key."""

    payload = raw_audit(key=key)
    semantic_item = copy.deepcopy(payload["boundary_input_items"][0])
    semantic_item["kind"] = "semantic_model_comparison"
    semantic_item["qualified_declaration"] = semantic_item[
        "reviewed_declaration_identity"
    ]["qualified_declaration"]
    semantic_item["dimensions"] = []
    semantic_item["semantic_contract_source_association"] = {
        "source_item_identities": [{"source_location": "source.txt:1-1"}]
    }
    payload["semantic_model_items"] = [semantic_item]
    stamp_source_record_audit_receipts(payload)
    return payload


def raw_audit_with_pinned_semantic_model(
    *, key: str = "named_result.h : P"
) -> dict[str, object]:
    """Fixture with one current schema-2 semantic association and two dimensions."""

    payload = raw_audit(key=key)
    semantic_item = copy.deepcopy(payload["boundary_input_items"][0])
    semantic_item["kind"] = "semantic_model_comparison"
    qualified = str(semantic_item["reviewed_declaration_identity"]["qualified_declaration"])
    signature = {
        "qualified_declaration": qualified,
        "elaborated_signature_sha256": digest("b"),
    }
    semantic_item["qualified_declaration"] = qualified
    semantic_item["source_statement_association"] = {
        "schema": 2,
        "source_item_identities": [
            {
                "source_key": "source_item",
                "source_location": "source.txt:1-1",
                "source_map_item_sha256": digest("c"),
                "source_semantic_sha256": digest("d"),
            }
        ],
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified,
            "declaration_sha256": digest("a"),
        },
        "reviewed_elaborated_signature_identity": signature,
        "semantic_association_sha256": semantic_association_record_digest(
            [digest("d")], signature
        ),
    }
    semantic_item["dimensions"] = [
        {"id": "carrier_and_domain", "detected_from_expanded_surface": True},
        {
            "id": "joint_law_and_state_evolution",
            "detected_from_expanded_surface": True,
        },
    ]
    payload["semantic_model_items"] = [semantic_item]
    stamp_source_record_audit_receipts(payload)
    return payload


def prior_sidecar(raw: dict[str, object]) -> dict[str, object]:
    key = raw["boundary_input_items"][0]["judgment_key"]  # type: ignore[index]
    return {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_audit_sha256": digest("f"),
        "validator": "prior v10 reviewer",
        "validated_at": "2026-07-27T00:00:00Z",
        "items": {
            key: {
                "classification": "validated_source_assumption",
                "prompt_version": PROMPT,
                "source_record_audit_sha256": digest("f"),
                "source_record_item_digest_schema": 4,
                "source_record_item_semantic_id": digest("1"),
                "source_record_item_sha256": digest("2"),
                "validator": "prior v10 reviewer",
                "validated_at": "2026-07-27T00:00:00Z",
            }
        },
    }


def archived_pinned_semantic_raw() -> tuple[dict[str, object], dict[str, object]]:
    """Return one archived literal-source review with sealed source context."""

    raw = raw_audit_with_pinned_semantic_model()
    semantic_item = raw["semantic_model_items"][0]
    assert isinstance(semantic_item, dict)
    # The fixture's schema-2 association is a generated semantic-contract
    # route, rather than a source-presentation direct route.  Its receipt
    # still pins the source identity and elaborated signature without adding
    # the direct-route map-selection requirements under test elsewhere.
    semantic_item["semantic_contract_source_association"] = semantic_item.pop(
        "source_statement_association"
    )
    source_fidelity = {"model_conventions": [], "defects": []}
    raw["paper_statement_map_sha256"] = digest("f")
    raw["source_proof_fidelity"] = copy.deepcopy(source_fidelity)
    raw["source_contract_association_error_count"] = 0
    raw["source_contract_association_errors"] = []
    raw["source_coverage_route_errors"] = []
    raw["source_premise_consistency_error"] = ""
    stamp_source_record_audit_receipts(
        raw,
        surface={
            "paper_statement_map_sha256": digest("f"),
            "source_proof_fidelity": copy.deepcopy(source_fidelity),
        },
    )

    association = semantic_item["semantic_contract_source_association"]
    assert isinstance(association, dict)
    semantic_pin = association["semantic_association_sha256"]
    assert isinstance(semantic_pin, str)
    dimensions = {
        dimension: {
            "source_target_disposition": "literal_source_match",
            "verdict": "matches_literal_source",
            "semantic_association_sha256": semantic_pin,
        }
        for dimension in (
            "carrier_and_domain",
            "joint_law_and_state_evolution",
        )
    }
    key = str(semantic_item["judgment_key"])
    return raw, {
        "items": {
            key: {
                "classification": "semantic_model_review",
                "semantic_model_dimensions": dimensions,
            }
        }
    }


def stale_source_routed_semantic_response(
    raw: dict[str, object], *, stale_pin: str
) -> tuple[str, str, dict[str, object]]:
    """Attach one schema-2 route at every generated projection shape."""

    boundary = raw["boundary_input_items"][0]
    semantic_item = raw["semantic_model_items"][0]
    assert isinstance(boundary, dict) and isinstance(semantic_item, dict)
    association = semantic_item["source_statement_association"]
    assert isinstance(association, dict)
    current_pin = association["semantic_association_sha256"]
    assert isinstance(current_pin, str)
    boundary["source_contract_association"] = copy.deepcopy(association)
    dimensions = semantic_item["dimensions"]
    assert isinstance(dimensions, list) and dimensions
    first_dimension = dimensions[0]
    assert isinstance(first_dimension, dict)
    nested_association = copy.deepcopy(association)
    nested_identities = nested_association["source_item_identities"]
    assert isinstance(nested_identities, list) and len(nested_identities) == 1
    nested_identity = nested_identities[0]
    assert isinstance(nested_identity, dict)
    nested_identity["source_semantic_sha256"] = digest("e")
    signature = nested_association["reviewed_elaborated_signature_identity"]
    assert isinstance(signature, dict)
    nested_pin = semantic_association_record_digest([digest("e")], signature)
    nested_association["semantic_association_sha256"] = nested_pin
    first_dimension[SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD] = nested_association
    stamp_source_record_audit_receipts(raw)
    return current_pin, nested_pin, {
        "classification": "semantic_model_review",
        "semantic_association_sha256": stale_pin,
        "semantic_model_dimensions": {
            "carrier_and_domain": {
                "semantic_association_sha256": stale_pin,
                SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD: {
                    "semantic_association_sha256": stale_pin,
                    "verdict": "matches_literal_source",
                },
                "source_target_disposition": "literal_source_match",
                "verdict": "matches_literal_source",
            },
            "joint_law_and_state_evolution": {
                "semantic_association_sha256": stale_pin,
                "source_target_disposition": "literal_source_match",
                "verdict": "matches_literal_source",
            },
        },
    }


class SourceRecordCurrentRevalidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        (self.paper_dir / "audit").mkdir(parents=True)
        (self.paper_dir / "status.json").write_text(
            json.dumps({"status": "formalized", "review_surface": {}}),
            encoding="utf-8",
        )
        (self.paper_dir / "source.txt").write_text(
            "source-backed law bridge\n", encoding="utf-8"
        )
        (self.paper_dir / "other.txt").write_text(
            "unrelated source text\n", encoding="utf-8"
        )
        (self.paper_dir / "PaperInterface.lean").write_text(
            "-- fixture expanded route\n", encoding="utf-8"
        )
        self.raw = raw_audit()
        self.raw_path = self.paper_dir / "audit" / "source_record_audit.json"
        self.raw_path.write_text(json.dumps(self.raw), encoding="utf-8")
        self.prior = prior_sidecar(self.raw)
        self.judgment_path = self.paper_dir / "audit" / "source_record_match_llm.json"
        self.judgment_path.write_text(json.dumps(self.prior), encoding="utf-8")
        self.prior_path = (
            self.paper_dir / "audit" / "source_record_match_llm.before_revalidation.json"
        )
        self.prior_path.write_text(json.dumps(self.prior), encoding="utf-8")

    def test_deterministic_rebind_write_is_idempotent(self) -> None:
        """A rerun of the same attestation must not rewrite its sidecar."""

        rebound = {"schema": 1, "items": {"current": {"judgment": "matches"}}}
        expected = REVALIDATION._canonical_json_bytes(rebound)
        self.judgment_path.write_bytes(expected)

        self.assertFalse(
            REVALIDATION.write_rebound_sidecar_if_changed(
                self.judgment_path, rebound
            )
        )
        self.assertEqual(self.judgment_path.read_bytes(), expected)

        self.judgment_path.write_bytes(b"{\"stale\": true}\n")
        self.assertTrue(
            REVALIDATION.write_rebound_sidecar_if_changed(
                self.judgment_path, rebound
            )
        )
        self.assertEqual(self.judgment_path.read_bytes(), expected)

    def test_selected_rebind_validator_accepts_empty_authenticated_complement(
        self,
    ) -> None:
        """An overlay covering every group needs no selected response item."""

        current_digest = digest("a")
        sidecar = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": current_digest,
            REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                REVALIDATION.formalization_review_protocol_digest()
            ),
            "items": {},
            REVALIDATION.SELECTED_CURRENT_REVALIDATION_FIELD: {
                "schema": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCHEMA,
                "policy_version": (
                    REVALIDATION.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION
                ),
                "current_judgment_sidecar_path": (
                    "audit/source_record_match_llm.json"
                ),
                "selected_current_group_descriptors": {},
            },
        }
        overlay_path = (
            self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        )
        with (
            patch.object(REVALIDATION, "_raw_audit_error", return_value=""),
            patch.object(
                REVALIDATION,
                "_selected_current_overlay",
                return_value=({}, {}, overlay_path, digest("b")),
            ),
            patch.object(
                REVALIDATION,
                "_selected_current_group_descriptors",
                return_value={},
            ),
            patch.object(
                REVALIDATION,
                "_selected_rebound_attestation_errors",
                return_value=[],
            ),
            patch.object(REVALIDATION, "generated_judgment_items", return_value={}),
        ):
            self.assertEqual(
                REVALIDATION.validate_selected_rebound_sidecar(
                    {"source_record_audit_sha256": current_digest},
                    sidecar,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    include_downstream_target_disposition=False,
                ),
                [],
            )

    def completed_attestation(
        self, raw: dict[str, object] | None = None, prior: dict[str, object] | None = None
    ) -> tuple[dict[str, object], Path]:
        raw = self.raw if raw is None else raw
        prior = self.prior if prior is None else prior
        if prior is not self.prior:
            self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        template = REVALIDATION.attestation_template(
            raw,
            prior,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
        )
        template.pop("non_evidence_scaffold")
        template.update(
            {
                "reviewed_current_semantics": True,
                "reviewer": "fixture current semantic reviewer",
                "validated_at": "2026-07-27T01:00:00Z",
            }
        )
        path = self.paper_dir / "audit" / "current_semantic_revalidation.json"
        path.write_text(json.dumps(template), encoding="utf-8")
        return template, path

    def test_attestation_template_passes_paper_dir_to_raw_gate(self) -> None:
        """The public writer cannot bypass a live structural replay witness."""

        with patch.object(REVALIDATION, "_raw_audit_error", return_value="") as gate:
            REVALIDATION.attestation_template(
                self.raw,
                self.prior,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
            )
        gate.assert_called_once_with(self.raw, paper=PAPER, paper_dir=self.paper_dir)

    def test_complete_review_accepts_accumulated_historical_aggregate_receipts(
        self,
    ) -> None:
        prior = copy.deepcopy(self.prior)
        item = next(iter(prior["items"].values()))
        assert isinstance(item, dict)
        item["source_record_audit_sha256"] = digest("e")
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")

        template = REVALIDATION.attestation_template(
            self.raw,
            prior,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
        )

        self.assertEqual(template["prior_source_record_audit_sha256"], digest("f"))
        self.assertEqual(
            REVALIDATION._prior_sidecar_error(prior, prior["items"]), ""
        )

    def test_complete_review_rejects_malformed_historical_aggregate_receipt(
        self,
    ) -> None:
        prior = copy.deepcopy(self.prior)
        key, item = next(iter(prior["items"].items()))
        assert isinstance(item, dict)
        item["source_record_audit_sha256"] = "not-a-digest"

        self.assertEqual(
            REVALIDATION._prior_sidecar_error(prior, prior["items"]),
            f"prior judgment `{key}` has no valid historical aggregate digest",
        )

    def test_complete_attestation_can_correct_required_lean_derivation(self) -> None:
        """A current classification change must be able to carry its evidence."""

        key = next(iter(self.prior["items"]))
        amendments = REVALIDATION._attested_judgment_amendments(
            {
                "judgment_amendments": {
                    key: {
                        "classification": "proved_from_primitives",
                        "lean_derivation": "PaperInterface.lean:1 proves the direct route.",
                    }
                }
            },
            expected_keys={key},
        )
        self.assertEqual(
            amendments[key]["lean_derivation"],
            "PaperInterface.lean:1 proves the direct route.",
        )
        self.assertEqual(
            REVALIDATION._attested_judgment_amendment_provenance_error(
                amendments, paper_dir=self.paper_dir
            ),
            "",
        )
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "only when it explicitly classifies",
        ):
            REVALIDATION._attested_judgment_amendments(
                {
                    "judgment_amendments": {
                        key: {
                            "classification": "validated_source_assumption",
                            "lean_derivation": "PaperInterface.lean:1",
                        }
                    }
                },
                expected_keys={key},
            )
        self.assertIn(
            "names no local Lean file",
            REVALIDATION._attested_judgment_amendment_provenance_error(
                {
                    key: {
                        "classification": "proved_from_primitives",
                        "lean_derivation": "Missing.lean:1",
                    }
                },
                paper_dir=self.paper_dir,
            ),
        )

    def test_complete_rebind_handles_explicit_new_and_retired_groups(self) -> None:
        current = raw_audit()
        new_key = "new_result.h : R"
        current["boundary_input_items"].append(raw_item(new_key))
        stamp_source_record_audit_receipts(current)

        prior = copy.deepcopy(self.prior)
        retired_key = "retired_result.h : S"
        prior["items"][retired_key] = copy.deepcopy(
            next(iter(prior["items"].values()))
        )
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")

        attestation = REVALIDATION.attestation_template(
            current,
            prior,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
        )
        self.assertEqual(attestation["new_judgment_keys_required"], [new_key])
        self.assertEqual(attestation["retired_prior_judgment_keys"], [retired_key])
        attestation.pop("non_evidence_scaffold")
        attestation.update(
            {
                "reviewed_current_semantics": True,
                "reviewer": "fixture current semantic reviewer",
                "validated_at": "2026-07-27T01:00:00Z",
                "new_judgments": {
                    new_key: {
                        "classification": "validated_source_assumption",
                        "reason": "Explicitly reviewed against the current raw group.",
                    }
                },
            }
        )
        path = self.paper_dir / "audit" / "current_semantic_revalidation.json"
        path.write_text(json.dumps(attestation), encoding="utf-8")

        rebound = REVALIDATION.rebound_sidecar(
            current,
            prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )

        self.assertEqual(
            set(rebound["items"]), set(REVALIDATION.generated_judgment_items(current))
        )
        self.assertNotIn(retired_key, rebound["items"])
        self.assertEqual(
            rebound[REVALIDATION.CURRENT_REVALIDATION_FIELD]["new_judgment_keys"],
            [new_key],
        )
        self.assertEqual(
            rebound[REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD],
            REVALIDATION.formalization_review_protocol_digest(),
        )
        self.assertEqual(
            REVALIDATION.validate_rebound_sidecar(
                current,
                rebound,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                include_runtime_semantic_checks=False,
            ),
            [],
        )

        stale_protocol = copy.deepcopy(rebound)
        stale_protocol.pop(REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD)
        self.assertIn(
            "rebound sidecar has no current formalization review-protocol receipt",
            REVALIDATION.validate_rebound_sidecar(
                current,
                stale_protocol,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                include_runtime_semantic_checks=False,
            ),
        )

        tampered = copy.deepcopy(rebound)
        tampered["items"][retired_key] = copy.deepcopy(
            next(iter(tampered["items"].values()))
        )
        errors = REVALIDATION.validate_rebound_sidecar(
            current,
            tampered,
            paper=PAPER,
            paper_dir=self.paper_dir,
            output_sidecar_path=self.judgment_path,
            include_runtime_semantic_checks=False,
        )
        self.assertIn(
            "rebound sidecar no longer has exact current generated-key coverage",
            errors,
        )

    def test_complete_rebind_refuses_an_unreviewed_new_group(self) -> None:
        current = raw_audit()
        new_key = "new_result.h : R"
        current["boundary_input_items"].append(raw_item(new_key))
        stamp_source_record_audit_receipts(current)
        attestation, path = self.completed_attestation(raw=current)

        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "new_judgments does not exactly cover",
        ):
            REVALIDATION.rebound_sidecar(
                current,
                self.prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_archived_target_replay_uses_embedded_context_after_live_map_change(self) -> None:
        raw, sidecar = archived_pinned_semantic_raw()
        self.assertEqual(REVALIDATION._raw_audit_error(raw, paper=PAPER), "")

        # This is deliberately not the historical source map. A historical
        # receipt must validate its own sealed map/fidelity identities, while
        # a later descriptor-authenticated current rebind rechecks this file.
        (self.paper_dir / "audit" / "paper_statement_map.json").write_text(
            json.dumps({"items": {"different_source_item": {}}}), encoding="utf-8"
        )
        (self.paper_dir / "audit" / "source_proof_fidelity.json").write_text(
            json.dumps({"model_conventions": [{"id": "different"}], "defects": []}),
            encoding="utf-8",
        )

        archived_errors = REVALIDATION._target_disposition_errors(
            raw,
            sidecar,
            paper_dir=self.paper_dir,
            historical_receipt_only=True,
        )
        self.assertEqual(archived_errors, [])
        current_errors = REVALIDATION._target_disposition_errors(
            raw,
            sidecar,
            paper_dir=self.paper_dir,
        )
        self.assertTrue(
            any("source-map identity" in error for error in current_errors),
            current_errors,
        )

    def test_archived_target_replay_rejects_changed_response_or_raw_association(self) -> None:
        raw, sidecar = archived_pinned_semantic_raw()
        key = next(iter(sidecar["items"]))
        response = sidecar["items"][key]
        assert isinstance(response, dict)
        dimensions = response["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        first_dimension = dimensions["carrier_and_domain"]
        assert isinstance(first_dimension, dict)
        first_dimension["semantic_association_sha256"] = digest("e")
        response_errors = REVALIDATION._target_disposition_errors(
            raw,
            sidecar,
            paper_dir=self.paper_dir,
            historical_receipt_only=True,
        )
        self.assertTrue(
            any("semantic_association_sha256 must equal" in error for error in response_errors),
            response_errors,
        )

        mutated_raw, _ = archived_pinned_semantic_raw()
        semantic_item = mutated_raw["semantic_model_items"][0]
        assert isinstance(semantic_item, dict)
        association = semantic_item["semantic_contract_source_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identity = identities[0]
        assert isinstance(identity, dict)
        identity["source_semantic_sha256"] = digest("e")
        self.assertIn(
            "receipt is invalid",
            REVALIDATION._raw_audit_error(mutated_raw, paper=PAPER),
        )

    def content_amendment_provenance(
        self,
        raw: dict[str, object],
        key: str,
        updates: dict[str, str],
    ) -> dict[str, object]:
        groups, errors = OBLIGATIONS.raw_source_record_obligation_groups(raw)
        self.assertEqual(errors, {})
        group = groups[key]
        semantic_members = group["semantic_model_items"]
        assert isinstance(semantic_members, list) and len(semantic_members) == 1
        semantic_member = semantic_members[0]
        assert isinstance(semantic_member, dict)
        return {
            "content_repair_count": 1,
            "content_repairs": [
                {
                    "judgment_key": key,
                    "current_group_descriptor_sha256": group["descriptor_sha256"],
                    "source_anchor": "source.txt:1-1",
                    "expanded_lean_route": {
                        "direct_declaration": semantic_member[
                            "qualified_declaration"
                        ],
                        "transparent_spec_declaration": (
                            f"{semantic_member['qualified_declaration']}Spec"
                        ),
                        "source_location": "PaperInterface.lean:1",
                    },
                    "validator_failures_before_repair": [
                        "The archived law bridge was generic rather than source-backed."
                    ],
                    "proposed_semantic_repair": {
                        "kind": "source_backed_expanded_law_bridge_content_repair",
                        "changed_fields": updates,
                        "source_to_lean_bridge": (
                            "The current expanded endpoint proves the exact source "
                            "probability-law equality used by this review."
                        ),
                    },
                }
            ],
        }

    def test_rebind_preserves_prior_item_receipts_as_history_only(self) -> None:
        attestation, path = self.completed_attestation()
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        key = next(iter(rebound["items"]))
        entry = rebound["items"][key]
        assert isinstance(entry, dict)
        self.assertEqual(entry["source_record_item_digest_schema"], 5)
        self.assertEqual(entry["source_record_item_sha256"], digest("e"))
        self.assertEqual(
            entry[REVALIDATION.PRIOR_ITEM_RECEIPT_FIELD][
                "source_record_item_digest_schema"
            ],
            4,
        )
        self.assertEqual(
            entry["source_record_audit_sha256"],
            self.raw["source_record_audit_sha256"],
        )
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertEqual(
                REVALIDATION.validate_rebound_sidecar(
                    self.raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                ),
                [],
            )

    def test_sidecar_byte_binding_replays_complete_revalidation_contract(self) -> None:
        attestation, path = self.completed_attestation()
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        self.judgment_path.write_text(json.dumps(rebound), encoding="utf-8")
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            bound = SIDECAR_BINDING.build_sidecar_bound_current_revalidation_attestation(
                paper=PAPER,
                paper_dir=self.paper_dir,
                raw_audit=self.raw,
                sidecar=rebound,
                legacy_attestation=attestation,
                sidecar_path=self.judgment_path,
                legacy_attestation_path=path,
            )
        self.assertEqual(
            bound["current_judgment_sidecar_sha256"],
            hashlib.sha256(self.judgment_path.read_bytes()).hexdigest(),
        )

        tampered = copy.deepcopy(rebound)
        next(iter(tampered["items"].values()))[
            "source_record_audit_sha256"
        ] = digest("0")
        self.judgment_path.write_text(json.dumps(tampered), encoding="utf-8")
        with self.assertRaisesRegex(
            SIDECAR_BINDING.SourceRecordCurrentRevalidationSidecarBindingError,
            "fails complete current-revalidation replay",
        ):
            SIDECAR_BINDING.build_sidecar_bound_current_revalidation_attestation(
                paper=PAPER,
                paper_dir=self.paper_dir,
                raw_audit=self.raw,
                sidecar=tampered,
                legacy_attestation=attestation,
                sidecar_path=self.judgment_path,
                legacy_attestation_path=path,
            )

    def test_full_rebind_reprojects_all_current_generated_association_credentials(
        self,
    ) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        current_pin, nested_pin, response = stale_source_routed_semantic_response(
            raw, stale_pin=digest("f")
        )
        prior = prior_sidecar(raw)
        key = next(iter(prior["items"]))
        prior["items"][key] = response
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation, path = self.completed_attestation(raw=raw, prior=prior)

        rebound = REVALIDATION.rebound_sidecar(
            raw,
            prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        actual = rebound["items"][key]
        assert isinstance(actual, dict)
        self.assertEqual(actual["semantic_association_sha256"], current_pin)
        dimensions = actual["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        self.assertEqual(
            dimensions["carrier_and_domain"]["semantic_association_sha256"],
            current_pin,
        )
        self.assertEqual(
            dimensions["joint_law_and_state_evolution"]["semantic_association_sha256"],
            current_pin,
        )
        self.assertEqual(
            dimensions["carrier_and_domain"][SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD][
                "semantic_association_sha256"
            ],
            nested_pin,
        )
        # The association fields are raw-derived transport. Their reissue does
        # not make the archived reviewer content look like a new judgment.
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertEqual(
                REVALIDATION.validate_rebound_sidecar(
                    raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    include_runtime_semantic_checks=False,
                ),
                [],
            )
            tampered = copy.deepcopy(rebound)
            tampered_dimension = tampered["items"][key][
                "semantic_model_dimensions"
            ]["carrier_and_domain"][SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD]
            assert isinstance(tampered_dimension, dict)
            tampered_dimension["semantic_association_sha256"] = digest("f")
            errors = REVALIDATION.validate_rebound_sidecar(
                raw,
                tampered,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                include_runtime_semantic_checks=False,
            )
        self.assertTrue(
            any("semantic response ledger no longer matches" in error for error in errors),
            errors,
        )

    def test_complete_rebind_applies_compact_semantic_model_dimension_amendment(
        self,
    ) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        _, _, response = stale_source_routed_semantic_response(
            raw, stale_pin=digest("f")
        )
        prior = prior_sidecar(raw)
        key = next(iter(prior["items"]))
        dimensions = response["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        for dimension in dimensions.values():
            assert isinstance(dimension, dict)
            dimension["model_convention_ids"] = ["fixture-steady-model"]
            dimension["model_convention_sha256_by_id"] = {
                "fixture-steady-model": digest("a")
            }
        prior["items"][key] = response
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation, path = self.completed_attestation(raw=raw, prior=prior)
        self.assertIn(
            REVALIDATION.ATTESTED_SEMANTIC_MODEL_DIMENSION_AMENDMENTS_FIELD,
            attestation,
        )
        attestation[
            REVALIDATION.ATTESTED_SEMANTIC_MODEL_DIMENSION_AMENDMENTS_FIELD
        ] = {
            key: {
                "carrier_and_domain": {
                    "model_convention_sha256_by_id": {
                        "fixture-steady-model": digest("b")
                    }
                }
            }
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")

        rebound = REVALIDATION.rebound_sidecar(
            raw,
            prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        actual = rebound["items"][key]
        assert isinstance(actual, dict)
        actual_dimensions = actual["semantic_model_dimensions"]
        assert isinstance(actual_dimensions, dict)
        self.assertEqual(
            actual_dimensions["carrier_and_domain"][
                "model_convention_sha256_by_id"
            ],
            {"fixture-steady-model": digest("b")},
        )
        self.assertEqual(
            actual_dimensions["joint_law_and_state_evolution"][
                "model_convention_sha256_by_id"
            ],
            {"fixture-steady-model": digest("a")},
        )
        # Replay validates the same amendment, so a saved rebind cannot retain
        # an attestation field that materialization silently ignored.
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertEqual(
                REVALIDATION.validate_rebound_sidecar(
                    raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    include_runtime_semantic_checks=False,
                ),
                [],
            )

    def test_complete_rebind_rejects_noncompact_dimension_amendment(self) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        _, _, response = stale_source_routed_semantic_response(
            raw, stale_pin=digest("f")
        )
        prior = prior_sidecar(raw)
        key = next(iter(prior["items"]))
        dimensions = response["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        for dimension in dimensions.values():
            assert isinstance(dimension, dict)
            dimension["model_convention_ids"] = ["fixture-steady-model"]
            dimension["model_convention_sha256_by_id"] = {
                "fixture-steady-model": digest("a")
            }
        prior["items"][key] = response
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation, path = self.completed_attestation(raw=raw, prior=prior)
        attestation[
            REVALIDATION.ATTESTED_SEMANTIC_MODEL_DIMENSION_AMENDMENTS_FIELD
        ] = {
            key: {
                "carrier_and_domain": {
                    "model_convention_sha256_by_id": {
                        "fixture-steady-model": digest("b")
                    },
                    "verdict": "unattested semantic rewrite",
                }
            }
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")

        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "may only re-pin model convention digests",
        ):
            REVALIDATION.rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_default_association_projection_rejects_stale_credentials(self) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        current_pin, nested_pin, response = stale_source_routed_semantic_response(
            raw, stale_pin=digest("f")
        )
        key = str(raw["boundary_input_items"][0]["judgment_key"])
        members = REVALIDATION.generated_judgment_items(raw)[key]

        rejected, error = TARGET.project_source_record_response_association_pins(
            members, response, judgment_key=key
        )
        self.assertIsNone(rejected)
        self.assertIn("conflicts with the current raw association pin", error)

        projected, error = TARGET.project_source_record_response_association_pins(
            members,
            response,
            judgment_key=key,
            replace_generated_credentials=True,
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        self.assertEqual(projected["semantic_association_sha256"], current_pin)
        projected_dimensions = projected["semantic_model_dimensions"]
        assert isinstance(projected_dimensions, dict)
        self.assertEqual(
            projected_dimensions["carrier_and_domain"][
                SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD
            ]["semantic_association_sha256"],
            nested_pin,
        )

    def test_rejects_an_incomplete_retired_key_attestation(self) -> None:
        prior = copy.deepcopy(self.prior)
        prior["items"]["extra.h : R"] = copy.deepcopy(
            next(iter(prior["items"].values()))
        )
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation = REVALIDATION.attestation_template(
            self.raw,
            prior,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
        )
        attestation.pop("non_evidence_scaffold")
        attestation.update(
            {
                "reviewed_current_semantics": True,
                "reviewer": "fixture current semantic reviewer",
                "validated_at": "2026-07-27T01:00:00Z",
                "retired_prior_judgment_keys": [],
            }
        )
        path = self.paper_dir / "audit" / "current_semantic_revalidation.json"
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "retired_prior_judgment_keys.*authenticated ledger delta",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                prior,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation=attestation,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_rejects_an_attestation_for_a_different_raw_surface(self) -> None:
        attestation, path = self.completed_attestation()
        changed = copy.deepcopy(self.raw)
        changed["generator_note"] = "different current raw surface"
        stamp_source_record_audit_receipts(changed)
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "current raw aggregate",
        ):
            REVALIDATION.rebound_sidecar(
                changed,
                self.prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_rejects_an_unaffirmed_attestation_template(self) -> None:
        template = REVALIDATION.attestation_template(
            self.raw,
            self.prior,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
        )
        path = self.paper_dir / "audit" / "unaffirmed.json"
        path.write_text(json.dumps(template), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "non-evidence scaffold",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                self.prior,
                template,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_complete_rebind_rejects_missing_or_stale_review_protocol_receipt(
        self,
    ) -> None:
        attestation, path = self.completed_attestation()
        attestation.pop(REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD)
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "review-protocol receipt",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                self.prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

        attestation[REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD] = digest("0")
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "review-protocol receipt",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                self.prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_shared_loader_rejects_missing_or_stale_review_protocol_receipt(
        self,
    ) -> None:
        current = copy.deepcopy(self.raw)
        current[FORMALIZATION_COVERAGE_PROTOCOL_FIELD] = (
            formalization_coverage_protocol_digest()
        )
        stamp_source_record_audit_receipts(current)
        attestation, path = self.completed_attestation(raw=current)
        rebound = REVALIDATION.rebound_sidecar(
            current,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertEqual(
                set(
                    REVALIDATION.EVIDENCE.current_source_record_judgment_items(
                        current, rebound
                    )
                ),
                set(REVALIDATION.generated_judgment_items(current)),
            )
            missing = copy.deepcopy(rebound)
            missing.pop(REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD)
            self.assertEqual(
                REVALIDATION.EVIDENCE.current_source_record_judgment_items(
                    current, missing
                ),
                {},
            )
            stale = copy.deepcopy(rebound)
            stale[REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD] = digest("0")
            self.assertEqual(
                REVALIDATION.EVIDENCE.current_source_record_judgment_items(
                    current, stale
                ),
                {},
            )

    def test_rejects_recursive_data_labels_on_boundary_inputs(self) -> None:
        prior = copy.deepcopy(self.prior)
        entry = next(iter(prior["items"].values()))
        entry["classification"] = "nonpropositional_witness_data"
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation, path = self.completed_attestation(prior=prior)
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            errors = REVALIDATION.validate_rebound_sidecar(
                self.raw,
                rebound,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
            )
        self.assertTrue(any("not a generated theorem-boundary input" in error for error in errors))

    def test_exact_descriptor_schema_transport_plans_only_missing_literal_disposition(
        self,
    ) -> None:
        raw = raw_audit_with_direct_source_contract()
        prior = prior_sidecar(raw)
        key = next(iter(prior["items"]))
        response = prior["items"][key]
        assert isinstance(response, dict)
        response["source_location"] = "source.txt:1-1"

        self.assertEqual(
            REVALIDATION.exact_descriptor_schema_transport_updates(raw, raw, prior["items"]),
            {key: {"source_target_disposition": "literal_source_match"}},
        )

    def test_exact_descriptor_schema_transport_rejects_any_descriptor_drift(self) -> None:
        prior_raw = raw_audit_with_direct_source_contract()
        current_raw = copy.deepcopy(prior_raw)
        item = current_raw["boundary_input_items"][0]
        assert isinstance(item, dict)
        association = item["source_contract_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identity = identities[0]
        assert isinstance(identity, dict)
        identity["source_semantic_sha256"] = digest("e")
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [digest("e")], signature
        )
        stamp_source_record_audit_receipts(current_raw)

        prior = prior_sidecar(prior_raw)
        key = next(iter(prior["items"]))
        response = prior["items"][key]
        assert isinstance(response, dict)
        response["source_location"] = "source.txt:1-1"
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "refuses semantic descriptor drift",
        ):
            REVALIDATION.exact_descriptor_schema_transport_updates(
                prior_raw, current_raw, prior["items"]
            )

    def test_exact_descriptor_schema_transport_does_not_change_existing_semantics(
        self,
    ) -> None:
        raw = raw_audit_with_direct_source_contract()
        prior = prior_sidecar(raw)
        key = next(iter(prior["items"]))
        response = prior["items"][key]
        assert isinstance(response, dict)
        response.update(
            {
                "source_location": "source.txt:1-1",
                "model_convention_ids": ["not-a-transport-field"],
                "model_convention_sha256_by_id": {"not-a-transport-field": digest("f")},
            }
        )

        self.assertEqual(
            REVALIDATION.exact_descriptor_schema_transport_updates(raw, raw, prior["items"]),
            {},
        )

    def test_attested_amendment_is_applied_and_binds_semantic_ledger(self) -> None:
        attestation, path = self.completed_attestation()
        key = next(iter(self.prior["items"]))
        attestation[REVALIDATION.ATTESTED_JUDGMENT_AMENDMENTS_FIELD] = {
            key: {"reason": "current semantic review corrected this explanation"}
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        self.assertEqual(
            rebound["items"][key]["reason"],
            "current semantic review corrected this explanation",
        )
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertEqual(
                REVALIDATION.validate_rebound_sidecar(
                    self.raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                ),
                [],
            )
            rebound["items"][key]["reason"] = "unattested post-write edit"
            errors = REVALIDATION.validate_rebound_sidecar(
                self.raw,
                rebound,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
            )
        self.assertTrue(
            any("semantic response ledger no longer matches" in error for error in errors)
        )

    def test_narrow_semantic_model_content_amendment_preserves_the_rest_of_review(self) -> None:
        raw = raw_audit_with_semantic_model()
        prior = prior_sidecar(raw)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        key = next(iter(prior["items"]))
        entry = prior["items"][key]
        assert isinstance(entry, dict)
        entry["semantic_model_dimensions"] = {
            "joint_law_and_state_evolution": {
                "distribution_parameterization_analysis": {
                    "law_equivalence_evidence": "archived generic evidence",
                    "parameter_translation": "source theta = Lean theta",
                },
                "transformed_law_analysis": {
                    "verdict": "no_transform_or_canonicalization"
                },
            }
        }
        attestation, path = self.completed_attestation(raw=raw, prior=prior)
        updates = {
            key: {
                "joint_law_and_state_evolution.distribution_parameterization_analysis.law_equivalence_evidence": (
                    "The source PMF equality is proved by the expanded Lean endpoint."
                )
            }
        }
        attestation[REVALIDATION.ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD] = updates
        attestation["judgment_amendment_provenance"] = (
            self.content_amendment_provenance(raw, key, updates[key])
        )
        path.write_text(json.dumps(attestation), encoding="utf-8")
        rebound = REVALIDATION.rebound_sidecar(
            raw,
            prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        dimension = rebound["items"][key]["semantic_model_dimensions"][
            "joint_law_and_state_evolution"
        ]
        self.assertEqual(
            dimension["distribution_parameterization_analysis"][
                "law_equivalence_evidence"
            ],
            "The source PMF equality is proved by the expanded Lean endpoint.",
        )
        self.assertEqual(
            dimension["distribution_parameterization_analysis"][
                "parameter_translation"
            ],
            "source theta = Lean theta",
        )
        metadata = rebound[REVALIDATION.CURRENT_REVALIDATION_FIELD]
        assert isinstance(metadata, dict)
        self.assertEqual(
            REVALIDATION._rebound_attestation_errors(
                metadata,
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                sidecar_items=rebound["items"],
            ),
            [],
        )

    def test_rejects_unsupported_narrow_semantic_model_content_path(self) -> None:
        raw = raw_audit_with_semantic_model()
        prior = prior_sidecar(raw)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        key = next(iter(prior["items"]))
        entry = prior["items"][key]
        assert isinstance(entry, dict)
        entry["semantic_model_dimensions"] = {
            "joint_law_and_state_evolution": {
                "distribution_parameterization_analysis": {
                    "law_equivalence_evidence": "archived generic evidence",
                    "parameter_translation": "source theta = Lean theta",
                },
                "transformed_law_analysis": {
                    "verdict": "no_transform_or_canonicalization"
                },
            }
        }
        attestation, path = self.completed_attestation(raw=raw, prior=prior)
        attestation[REVALIDATION.ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD] = {
            key: {
                "joint_law_and_state_evolution.distribution_parameterization_analysis.family_coupling_scope": (
                    "unattested broad rewrite"
                )
            }
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "changes unsupported path",
        ):
            REVALIDATION.rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_narrow_content_amendment_requires_current_source_and_lean_provenance(self) -> None:
        raw = raw_audit_with_semantic_model()
        prior = prior_sidecar(raw)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        key = next(iter(prior["items"]))
        entry = prior["items"][key]
        assert isinstance(entry, dict)
        entry["semantic_model_dimensions"] = {
            "joint_law_and_state_evolution": {
                "distribution_parameterization_analysis": {
                    "law_equivalence_evidence": "archived generic evidence",
                    "parameter_translation": "source theta = Lean theta",
                },
                "transformed_law_analysis": {
                    "verdict": "no_transform_or_canonicalization"
                },
            }
        }
        updates = {
            "joint_law_and_state_evolution.distribution_parameterization_analysis.law_equivalence_evidence": (
                "The source PMF equality is proved by the expanded Lean endpoint."
            )
        }

        def build_attestation() -> tuple[dict[str, object], Path]:
            attestation, path = self.completed_attestation(raw=raw, prior=prior)
            attestation[
                REVALIDATION.ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD
            ] = {key: updates}
            attestation["judgment_amendment_provenance"] = (
                self.content_amendment_provenance(raw, key, updates)
            )
            return attestation, path

        mutations = {
            "descriptor": (
                lambda repair: repair.__setitem__(
                    "current_group_descriptor_sha256", digest("9")
                ),
                "descriptor does not match",
            ),
            "source-association": (
                lambda repair: repair.__setitem__("source_anchor", "other.txt:1-1"),
                "does not overlap a current generated source association",
            ),
            "lean-route": (
                lambda repair: repair["expanded_lean_route"].__setitem__(
                    "direct_declaration", "FixturePaper.PaperInterface.other_result"
                ),
                "does not locate the generated endpoint",
            ),
            "patch-fields": (
                lambda repair: repair["proposed_semantic_repair"].__setitem__(
                    "changed_fields", {"unattested.path": "replacement"}
                ),
                "repair fields differ",
            ),
        }
        for label, (mutate, expected_error) in mutations.items():
            with self.subTest(label=label):
                attestation, path = build_attestation()
                repair = attestation["judgment_amendment_provenance"][
                    "content_repairs"
                ][0]
                mutate(repair)
                path.write_text(json.dumps(attestation), encoding="utf-8")
                with self.assertRaisesRegex(
                    REVALIDATION.SourceRecordCurrentRevalidationError, expected_error
                ):
                    REVALIDATION.rebound_sidecar(
                        raw,
                        prior,
                        attestation,
                        paper=PAPER,
                        paper_dir=self.paper_dir,
                        prior_sidecar_path=self.prior_path,
                        attestation_path=path,
                        output_sidecar_path=self.judgment_path,
                    )

    def test_rejects_narrow_content_amendment_without_semantic_model_group(self) -> None:
        prior = copy.deepcopy(self.prior)
        key = next(iter(prior["items"]))
        entry = prior["items"][key]
        assert isinstance(entry, dict)
        entry["semantic_model_dimensions"] = {
            "joint_law_and_state_evolution": {
                "distribution_parameterization_analysis": {
                    "law_equivalence_evidence": "archived generic evidence",
                    "parameter_translation": "source theta = Lean theta",
                },
                "transformed_law_analysis": {
                    "verdict": "no_transform_or_canonicalization"
                },
            }
        }
        attestation, path = self.completed_attestation(prior=prior)
        attestation[REVALIDATION.ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD] = {
            key: {
                "joint_law_and_state_evolution.distribution_parameterization_analysis.law_equivalence_evidence": (
                    "The source PMF equality is proved by the expanded Lean endpoint."
                )
            }
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "has no generated semantic-model obligation",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_selected_dimension_association_amendment_rebinds_only_exact_current_pins(
        self,
    ) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        prior = prior_sidecar(raw)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        key = next(iter(prior["items"]))
        prior_item = prior["items"][key]
        assert isinstance(prior_item, dict)
        prior_item["classification"] = "semantic_model_review"
        prior_item["semantic_model_dimensions"] = {
            "carrier_and_domain": {
                "semantic_association_sha256": digest("f"),
                "source_locator": "source.txt:1-1",
                "semantic_comparison": "archived carrier comparison",
                "lean_evidence": "archived carrier evidence",
                "verdict": "matches_literal_source",
            },
            "joint_law_and_state_evolution": {
                "semantic_association_sha256": digest("f"),
                "source_locator": "source.txt:1-1",
                "semantic_comparison": "archived joint-law comparison",
                "lean_evidence": "archived joint-law evidence",
                "verdict": "matches_literal_source",
            },
        }
        groups, group_errors = OBLIGATIONS.raw_source_record_obligation_groups(raw)
        self.assertEqual(group_errors, {})
        descriptor = groups[key]["descriptor_sha256"]
        assert isinstance(descriptor, str)
        association = raw["semantic_model_items"][0]["source_statement_association"]
        assert isinstance(association, dict)
        current_pin = association["semantic_association_sha256"]
        assert isinstance(current_pin, str)
        attestation = {
            REVALIDATION.ATTESTED_SEMANTIC_MODEL_DIMENSION_ASSOCIATION_AMENDMENTS_FIELD: {
                key: {
                    "current_group_semantic_descriptor_sha256": descriptor,
                    "dimensions": {
                        "carrier_and_domain": current_pin,
                        "joint_law_and_state_evolution": current_pin,
                    },
                }
            }
        }
        expected = REVALIDATION._selected_expected_semantic_items(
            {key: prior_item},
            attestation,
            selected_keys={key},
            current_raw_audit=raw,
            selected_descriptors={key: descriptor},
        )
        actual = expected[key]["semantic_model_dimensions"]
        assert isinstance(actual, dict)
        self.assertEqual(
            actual["carrier_and_domain"]["semantic_association_sha256"], current_pin
        )
        self.assertEqual(
            actual["joint_law_and_state_evolution"]["semantic_association_sha256"],
            current_pin,
        )
        self.assertEqual(
            actual["carrier_and_domain"]["verdict"], "matches_literal_source"
        )
        self.assertEqual(
            actual["joint_law_and_state_evolution"]["source_locator"],
            "source.txt:1-1",
        )

        mutations = {
            "omitted-dimension": (
                lambda value: value["dimensions"].pop("carrier_and_domain"),
                "must enumerate exactly every existing source-pinned dimension",
            ),
            "extra-dimension": (
                lambda value: value["dimensions"].__setitem__(
                    "not_a_current_dimension", current_pin
                ),
                "must enumerate exactly every existing source-pinned dimension",
            ),
            "stale-pin": (
                lambda value: value["dimensions"].__setitem__(
                    "carrier_and_domain", digest("e")
                ),
                "has a noncurrent association pin",
            ),
            "stale-descriptor": (
                lambda value: value.__setitem__(
                    "current_group_semantic_descriptor_sha256", digest("9")
                ),
                "has a stale current descriptor",
            ),
        }
        for label, (mutate, expected_error) in mutations.items():
            with self.subTest(label=label):
                changed = copy.deepcopy(attestation)
                entry = changed[
                    REVALIDATION.ATTESTED_SEMANTIC_MODEL_DIMENSION_ASSOCIATION_AMENDMENTS_FIELD
                ][key]
                assert isinstance(entry, dict)
                mutate(entry)
                with self.assertRaisesRegex(
                    REVALIDATION.SourceRecordCurrentRevalidationError,
                    expected_error,
                ):
                    REVALIDATION._selected_expected_semantic_items(
                        {key: prior_item},
                        changed,
                        selected_keys={key},
                        current_raw_audit=raw,
                        selected_descriptors={key: descriptor},
                    )

        conflicting = copy.deepcopy(attestation)
        conflicting["judgment_amendments"] = {
            key: {"semantic_model_dimensions": {"unattested": "rewrite"}}
        }
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "cannot accompany a full dimension rewrite",
        ):
            REVALIDATION._selected_expected_semantic_items(
                {key: prior_item},
                conflicting,
                selected_keys={key},
                current_raw_audit=raw,
                selected_descriptors={key: descriptor},
            )

    def test_validation_rejects_mutated_saved_attestation(self) -> None:
        attestation, path = self.completed_attestation()
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        attestation["review_notes"] = "mutated after the rebind"
        path.write_text(json.dumps(attestation), encoding="utf-8")
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            self.assertIn(
                "rebound sidecar attestation bytes no longer match its recorded hash",
                REVALIDATION.validate_rebound_sidecar(
                    self.raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                ),
            )

    def test_validation_rejects_mutated_prior_snapshot(self) -> None:
        attestation, path = self.completed_attestation()
        rebound = REVALIDATION.rebound_sidecar(
            self.raw,
            self.prior,
            attestation,
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_sidecar_path=self.prior_path,
            attestation_path=path,
            output_sidecar_path=self.judgment_path,
        )
        snapshot = json.loads(self.prior_path.read_text(encoding="utf-8"))
        entry = next(iter(snapshot["items"].values()))
        entry["reason"] = "mutated after the rebind"
        self.prior_path.write_text(json.dumps(snapshot), encoding="utf-8")
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_audit_identity_error",
            return_value="",
        ):
            errors = REVALIDATION.validate_rebound_sidecar(
                self.raw,
                rebound,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
            )
        self.assertTrue(
            any("prior-sidecar snapshot bytes no longer match" in error for error in errors)
        )

    def test_rejects_divergent_in_memory_prior_or_attestation(self) -> None:
        attestation, path = self.completed_attestation()
        altered_prior = copy.deepcopy(self.prior)
        entry = next(iter(altered_prior["items"].values()))
        entry["reason"] = "not the archived prior review"
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "supplied prior sidecar does not match",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                altered_prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )
        altered_attestation = copy.deepcopy(attestation)
        altered_attestation["review_notes"] = "not the saved attestation"
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "in-memory attestation does not match",
        ):
            REVALIDATION.rebound_sidecar(
                self.raw,
                self.prior,
                altered_attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_duplicate_or_aggregate_only_group_has_no_narrow_current_pin(self) -> None:
        for aggregate_only in (False, True):
            with self.subTest(aggregate_only=aggregate_only):
                raw = raw_audit()
                sibling = copy.deepcopy(raw["boundary_input_items"][0])
                if aggregate_only:
                    for field in list(sibling):
                        if field.startswith("source_record_item_"):
                            sibling.pop(field)
                    sibling["source_record_item_reuse_eligibility"] = {
                        "eligible": False,
                        "blockers": ["fixture aggregate-only sibling"],
                    }
                raw["conclusion_dependency_items"] = [sibling]
                stamp_source_record_audit_receipts(raw)
                prior = prior_sidecar(raw)
                self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
                attestation, path = self.completed_attestation(raw=raw, prior=prior)
                rebound = REVALIDATION.rebound_sidecar(
                    raw,
                    prior,
                    attestation,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    prior_sidecar_path=self.prior_path,
                    attestation_path=path,
                    output_sidecar_path=self.judgment_path,
                )
                entry = next(iter(rebound["items"].values()))
                assert isinstance(entry, dict)
                self.assertNotIn("source_record_item_sha256", entry)
                self.assertNotIn("source_record_item_sha256s", entry)
                self.assertNotIn("source_record_item_digest_schema", entry)
                with patch.object(
                    REVALIDATION.EVIDENCE,
                    "source_record_audit_identity_error",
                    return_value="",
                ):
                    self.assertEqual(
                        REVALIDATION.validate_rebound_sidecar(
                            raw,
                            rebound,
                            paper=PAPER,
                            paper_dir=self.paper_dir,
                            output_sidecar_path=self.judgment_path,
                        ),
                        [],
                    )

    def test_eligible_direct_routed_unkinded_recursive_field_is_aggregate_bound(
        self,
    ) -> None:
        raw = raw_audit()
        field = direct_routed_recursive_field_item()
        raw["boundary_input_items"] = []
        raw["recursive_field_items"] = [field]
        stamp_source_record_audit_receipts(raw)

        self.assertEqual(REVALIDATION._raw_audit_error(raw, paper=PAPER), "")
        key = str(field["judgment_key"])
        members = REVALIDATION.generated_judgment_items(raw)[key]
        self.assertEqual(members[0][0], "recursive_field_items")
        self.assertEqual(REVALIDATION._current_item_pins(members), [])

    def test_current_raw_revalidation_rejects_source_contract_association_count(
        self,
    ) -> None:
        raw = raw_audit()
        raw["source_contract_association_error_count"] = 1
        raw["source_contract_association_errors"] = []
        stamp_source_record_audit_receipts(raw)

        self.assertEqual(
            REVALIDATION._raw_audit_error(raw, paper=PAPER),
            "current raw audit recorded source-contract association errors",
        )

    def test_current_raw_revalidation_rejects_source_contract_association_errors(
        self,
    ) -> None:
        raw = raw_audit()
        raw["source_contract_association_error_count"] = 0
        raw["source_contract_association_errors"] = [
            "fixture direct route has no semantic-contract association"
        ]
        stamp_source_record_audit_receipts(raw)

        self.assertEqual(
            REVALIDATION._raw_audit_error(raw, paper=PAPER),
            "current raw audit has nonempty source-contract association errors",
        )

    def test_current_raw_revalidation_uses_authenticated_effective_semantic_surface(
        self,
    ) -> None:
        """A byte-pinned structural replay is available to every rebind route."""

        raw = raw_audit()
        raw["source_contract_association_error_count"] = 1
        raw["source_contract_association_errors"] = [
            "fixture representation-only association diagnostic"
        ]
        stamp_source_record_audit_receipts(raw)
        projection = object()
        with (
            patch.object(
                REVALIDATION.EVIDENCE,
                "source_record_semantic_contract_revalidation_context",
                return_value=(projection, ""),
            ) as context,
            patch.object(
                REVALIDATION.EVIDENCE,
                "source_record_effective_semantic_surface_error",
                return_value="",
            ) as effective_surface,
        ):
            self.assertEqual(
                REVALIDATION._raw_audit_error(
                    raw, paper=PAPER, paper_dir=self.paper_dir
                ),
                "",
            )
        context.assert_called_once_with(self.paper_dir, raw)
        effective_surface.assert_called_once_with(
            raw, semantic_contract_revalidation=projection
        )

    def test_current_raw_revalidation_rejects_invalid_structural_replay(
        self,
    ) -> None:
        """A stale replay cannot make an errored raw receipt reusable."""

        raw = raw_audit()
        raw["source_contract_association_error_count"] = 1
        raw["source_contract_association_errors"] = [
            "fixture representation-only association diagnostic"
        ]
        stamp_source_record_audit_receipts(raw)
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_semantic_contract_revalidation_context",
            return_value=(None, "artifact is stale for the raw receipt"),
        ):
            self.assertEqual(
                REVALIDATION._raw_audit_error(
                    raw, paper=PAPER, paper_dir=self.paper_dir
                ),
                "current raw semantic-contract replay is invalid: "
                "artifact is stale for the raw receipt",
            )

    def test_current_clean_raw_does_not_launch_structural_replay(self) -> None:
        """A clean authenticated surface needs no correction transaction."""

        raw = raw_audit()
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_semantic_contract_revalidation_context",
        ) as context:
            self.assertEqual(
                REVALIDATION._raw_audit_error(
                    raw, paper=PAPER, paper_dir=self.paper_dir
                ),
                "",
            )
        context.assert_not_called()

    def test_archived_clean_raw_does_not_read_live_semantic_replay(self) -> None:
        """An archived clean receipt is validated from its own bytes only."""

        raw = raw_audit()
        with patch.object(
            REVALIDATION.EVIDENCE,
            "source_record_semantic_contract_revalidation_context",
        ) as context:
            self.assertEqual(
                REVALIDATION._raw_audit_error(
                    raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    use_paper_local_semantic_contract_revalidation=False,
                ),
                "",
            )
        context.assert_not_called()

        raw["source_contract_association_error_count"] = 1
        raw["source_contract_association_errors"] = ["unresolved archived route"]
        stamp_source_record_audit_receipts(raw)
        self.assertEqual(
            REVALIDATION._raw_audit_error(
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                use_paper_local_semantic_contract_revalidation=False,
            ),
            "current raw audit recorded source-contract association errors",
        )

    def test_current_raw_revalidation_rejects_inconsistent_suppressed_error_count(
        self,
    ) -> None:
        """Replay may remove diagnostics, never malformed generator bookkeeping."""

        raw = raw_audit()
        raw["source_contract_association_error_count"] = 2
        raw["source_contract_association_errors"] = ["one diagnostic"]
        stamp_source_record_audit_receipts(raw)
        with (
            patch.object(
                REVALIDATION.EVIDENCE,
                "source_record_semantic_contract_revalidation_context",
                return_value=(object(), ""),
            ),
            patch.object(
                REVALIDATION.EVIDENCE,
                "source_record_effective_semantic_surface_error",
                return_value="",
            ),
        ):
            self.assertEqual(
                REVALIDATION._raw_audit_error(
                    raw, paper=PAPER, paper_dir=self.paper_dir
                ),
                "current raw audit has inconsistent source-contract association "
                "error bookkeeping",
            )

    def test_eligible_unkinded_nonrecursive_item_remains_fail_closed(self) -> None:
        raw = raw_audit()
        item = raw["boundary_input_items"][0]
        assert isinstance(item, dict)
        item.pop("kind")
        stamp_source_record_audit_receipts(raw)

        self.assertEqual(REVALIDATION._raw_audit_error(raw, paper=PAPER), "")
        key = str(item["judgment_key"])
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "reusable judgment item without kind",
        ):
            REVALIDATION._current_item_pins(
                REVALIDATION.generated_judgment_items(raw)[key]
            )

    def test_unkinded_ineligible_recursive_field_cannot_use_the_special_case(
        self,
    ) -> None:
        raw = raw_audit()
        field = direct_routed_recursive_field_item()
        for name in list(field):
            if name.startswith("source_record_item_") and name != (
                "source_record_item_reuse_eligibility"
            ):
                field.pop(name)
        field["source_record_item_reuse_eligibility"] = {
            "eligible": False,
            "blockers": ["fixture aggregate-only recursive field"],
        }
        raw["boundary_input_items"] = []
        raw["recursive_field_items"] = [field]
        stamp_source_record_audit_receipts(raw)

        self.assertEqual(REVALIDATION._raw_audit_error(raw, paper=PAPER), "")
        key = str(field["judgment_key"])
        members = REVALIDATION.generated_judgment_items(raw)[key]
        self.assertFalse(
            REVALIDATION._aggregate_bound_unkinded_recursive_field(*members[0])
        )
        self.assertEqual(REVALIDATION._current_item_pins(members), [])

    def test_unkinded_recursive_field_rejects_stale_route_or_raw_receipt(self) -> None:
        raw = raw_audit()
        field = direct_routed_recursive_field_item()
        raw["boundary_input_items"] = []
        raw["recursive_field_items"] = [field]
        stamp_source_record_audit_receipts(raw)
        route = field["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["field_chain"] = [
            {"structure": "Fixture.Record", "field": "different_leaf"}
        ]

        self.assertIn(
            "receipt is invalid", REVALIDATION._raw_audit_error(raw, paper=PAPER)
        )
        key = str(field["judgment_key"])
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "reusable judgment item without kind",
        ):
            REVALIDATION._current_item_pins(
                REVALIDATION.generated_judgment_items(raw)[key]
            )

        # Restamping cannot turn a stale parent-route receipt into the special
        # aggregate-bound structural case.
        stamp_source_record_audit_receipts(raw)
        self.assertEqual(REVALIDATION._raw_audit_error(raw, paper=PAPER), "")
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "reusable judgment item without kind",
        ):
            REVALIDATION._current_item_pins(
                REVALIDATION.generated_judgment_items(raw)[key]
            )

    def selected_revalidation_fixture(
        self,
    ) -> tuple[
        dict[str, object],
        dict[str, object],
        dict[str, object],
        Path,
        str,
        str,
    ]:
        """Prepare two current semantic groups and one historical extra item."""

        raw = raw_audit()
        selected_key = str(raw["boundary_input_items"][0]["judgment_key"])
        overlay_key = "other_result.h : R"
        raw["boundary_input_items"].append(raw_item(overlay_key))
        stamp_source_record_audit_receipts(raw)
        prior = prior_sidecar(raw)
        selected_response = prior["items"][selected_key]
        prior["items"][overlay_key] = copy.deepcopy(selected_response)
        prior["items"]["historical-only.h : S"] = copy.deepcopy(selected_response)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        overlay_path.write_text(json.dumps({"fixture": "overlay"}), encoding="utf-8")
        selected_descriptor = digest("8")
        overlay_descriptor = digest("9")
        attestation = {
            "schema": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "artifact_kind": REVALIDATION.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND,
            "policy_version": REVALIDATION.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                REVALIDATION.formalization_review_protocol_digest()
            ),
            "paper": PAPER,
            "prior_judgment_sidecar_path": "audit/source_record_match_llm.before_revalidation.json",
            "prior_judgment_sidecar_sha256": hashlib.sha256(self.prior_path.read_bytes()).hexdigest(),
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "generated_judgment_keys_sha256": REVALIDATION.generated_judgment_keys_sha256(raw),
            "generated_judgment_surface_sha256": REVALIDATION.generated_judgment_surface_sha256(raw),
            "differential_overlay_path": "audit/source_record_differential_revalidation.json",
            "differential_overlay_sha256": hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
            "differential_overlay_current_group_descriptors": {
                overlay_key: overlay_descriptor
            },
            "differential_overlay_current_group_descriptors_sha256": REVALIDATION._canonical_digest(
                {overlay_key: overlay_descriptor}
            ),
            "selected_current_group_descriptors": {selected_key: selected_descriptor},
            "selected_current_group_descriptors_sha256": REVALIDATION._canonical_digest(
                {selected_key: selected_descriptor}
            ),
            "new_judgment_keys_required": [],
            "new_judgments": {},
            "judgment_amendments": {},
            "review_scope": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCOPE,
            "reviewed_current_semantics": True,
            "reviewer": "fixture selected semantic reviewer",
            "validated_at": "2026-07-27T02:00:00Z",
        }
        path = self.paper_dir / "audit" / "selected_current_semantic_revalidation.json"
        path.write_text(json.dumps(attestation), encoding="utf-8")
        return raw, prior, attestation, path, selected_key, overlay_key

    def selected_replacement_fixture(
        self,
    ) -> tuple[
        dict[str, object],
        dict[str, object],
        dict[str, object],
        Path,
        str,
        str,
        dict[str, str],
    ]:
        """Return a selected fixture whose descriptors are the actual raw receipts."""

        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        groups, group_errors = OBLIGATIONS.raw_source_record_obligation_groups(raw)
        self.assertEqual(group_errors, {})
        descriptors = {
            key: str(group["descriptor_sha256"])
            for key, group in groups.items()
        }
        attestation["differential_overlay_current_group_descriptors"] = {
            overlay_key: descriptors[overlay_key]
        }
        attestation["differential_overlay_current_group_descriptors_sha256"] = (
            REVALIDATION._canonical_digest(
                attestation["differential_overlay_current_group_descriptors"]
            )
        )
        attestation["selected_current_group_descriptors"] = {
            selected_key: descriptors[selected_key]
        }
        attestation["selected_current_group_descriptors_sha256"] = (
            REVALIDATION._canonical_digest(
                attestation["selected_current_group_descriptors"]
            )
        )
        path.write_text(json.dumps(attestation), encoding="utf-8")
        return raw, prior, attestation, path, selected_key, overlay_key, descriptors

    def test_v3_selected_rebind_requires_replacement_for_same_key_descriptor_drift(
        self,
    ) -> None:
        """A v3 manual ledger cannot inherit a drifted same-key response."""

        raw = raw_audit()
        differential_key = str(raw["boundary_input_items"][0]["judgment_key"])
        semantic_rebind_key = "semantic transport group : Q"
        manual_key = "manual current group : R"
        raw["boundary_input_items"].extend(
            [raw_item(semantic_rebind_key), raw_item(manual_key)]
        )
        stamp_source_record_audit_receipts(raw)
        prior = prior_sidecar(raw)
        prior["items"][manual_key] = copy.deepcopy(
            prior["items"][differential_key]
        )
        # This is the historical shape that prompted v3: storage address is
        # unchanged, but its previous selected rebind was issued against a
        # different generated semantic descriptor.  v3 must not inherit it
        # merely because `manual_key` still exists.
        prior["items"][manual_key][
            REVALIDATION.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD
        ] = {
            "schema": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "attestation_sha256": digest("0"),
            "current_group_semantic_descriptor_sha256": digest("0"),
        }
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        descriptors = REVALIDATION._selected_current_group_descriptors(raw)
        self.assertNotEqual(
            prior["items"][manual_key][
                REVALIDATION.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD
            ]["current_group_semantic_descriptor_sha256"],
            descriptors[manual_key],
        )
        lanes = (
            # Schema-2 rebind is a distinct stronger registry lane; the
            # selected workflow records that transport label rather than
            # treating it as an implementation detail of historical reuse.
            SimpleNamespace(
                label="semantic_rebind",
                items={semantic_rebind_key: {"transport": "semantic-rebind"}},
            ),
            SimpleNamespace(
                label="differential",
                items={differential_key: {"transport": "differential"}},
            ),
        )
        union = {
            differential_key: lanes[1].items[differential_key],
            semantic_rebind_key: lanes[0].items[semantic_rebind_key],
        }
        registry = SimpleNamespace(
            load_authenticated_current_overlay_lanes=lambda *_args, **_kwargs: lanes,
            strict_authenticated_current_overlay_union=lambda _lanes: union,
        )
        with patch.object(
            REVALIDATION,
            "_authenticated_overlay_union_module",
            return_value=registry,
        ):
            template = REVALIDATION.selected_attestation_template(
                raw,
                prior,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
            )
        self.assertEqual(
            template["policy_version"],
            REVALIDATION.SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION,
        )
        self.assertEqual(
            template["selected_current_group_descriptors"],
            {manual_key: descriptors[manual_key]},
        )
        self.assertEqual(
            template[REVALIDATION.ATTESTED_JUDGMENT_REPLACEMENT_KEYS_FIELD],
            [manual_key],
        )
        union_metadata = template[
            REVALIDATION.SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD
        ]
        assert isinstance(union_metadata, dict)
        self.assertEqual(
            union_metadata["current_group_descriptors"],
            {
                differential_key: descriptors[differential_key],
                semantic_rebind_key: descriptors[semantic_rebind_key],
            },
        )
        lane_ledger = union_metadata["lane_current_group_descriptors"]
        assert isinstance(lane_ledger, dict)
        self.assertEqual(
            lane_ledger["semantic_rebind"],
            {semantic_rebind_key: descriptors[semantic_rebind_key]},
        )
        template.pop("non_evidence_scaffold")
        template.update(
            {
                "reviewed_current_semantics": True,
                "reviewer": "fixture union reviewer",
                "validated_at": "2026-08-14T00:00:00Z",
            }
        )
        attestation_path = self.paper_dir / "audit" / "selected_union.json"
        attestation_path.write_text(json.dumps(template), encoding="utf-8")
        with patch.object(
            REVALIDATION,
            "_authenticated_overlay_union_module",
            return_value=registry,
        ):
            with self.assertRaisesRegex(
                REVALIDATION.SourceRecordCurrentRevalidationError,
                "complete explicit current replacement",
            ):
                REVALIDATION.selected_rebound_sidecar(
                    raw,
                    prior,
                    template,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    prior_sidecar_path=self.prior_path,
                    attestation_path=attestation_path,
                    output_sidecar_path=self.judgment_path,
                )

            template["judgment_replacements"] = {
                manual_key: self.selected_replacement_entry(
                    prior_response=prior["items"][manual_key],
                    current_descriptor=descriptors[manual_key],
                    response={
                        "classification": "validated_source_assumption",
                        "reason": "Current review of the generated semantic group.",
                    },
                )
            }
            attestation_path.write_text(json.dumps(template), encoding="utf-8")
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                template,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=attestation_path,
                output_sidecar_path=self.judgment_path,
            )
            self.assertEqual(
                REVALIDATION.validate_selected_rebound_sidecar(
                    raw,
                    rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    include_downstream_target_disposition=False,
                ),
                [],
            )
        self.assertEqual(set(rebound["items"]), {manual_key})
        rebound_metadata = rebound[
            REVALIDATION.SELECTED_CURRENT_REVALIDATION_FIELD
        ]
        assert isinstance(rebound_metadata, dict)
        self.assertIn(
            REVALIDATION.SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD,
            rebound_metadata,
        )
        self.assertNotIn("differential_overlay_path", rebound_metadata)

        # v2 remains a frozen historical transport policy.  Its existing
        # selected response may still be replayed after the same union check;
        # only newly issued v3 evidence requires an explicit replacement.
        legacy_v2 = copy.deepcopy(template)
        legacy_v2["policy_version"] = (
            REVALIDATION.SELECTED_CURRENT_REVALIDATION_UNION_POLICY_VERSION
        )
        legacy_v2["review_scope"] = REVALIDATION.SELECTED_CURRENT_REVALIDATION_UNION_SCOPE
        legacy_v2.pop(REVALIDATION.ATTESTED_JUDGMENT_REPLACEMENT_KEYS_FIELD)
        legacy_v2["judgment_replacements"] = {}
        legacy_path = self.paper_dir / "audit" / "selected_union_v2.json"
        legacy_path.write_text(json.dumps(legacy_v2), encoding="utf-8")
        with patch.object(
            REVALIDATION,
            "_authenticated_overlay_union_module",
            return_value=registry,
        ):
            legacy_rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                legacy_v2,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=legacy_path,
                output_sidecar_path=self.judgment_path,
            )
            self.assertEqual(
                REVALIDATION.validate_selected_rebound_sidecar(
                    raw,
                    legacy_rebound,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    include_downstream_target_disposition=False,
                ),
                [],
            )
        legacy_entry = legacy_rebound["items"][manual_key]
        assert isinstance(legacy_entry, dict)
        self.assertIn(REVALIDATION.PRIOR_ITEM_RECEIPT_FIELD, legacy_entry)

    def selected_replacement_entry(
        self,
        *,
        prior_response: dict[str, object],
        current_descriptor: str,
        response: dict[str, object],
        rationale: str = "The current source review corrects an invalid archived route.",
    ) -> dict[str, object]:
        return {
            "schema": REVALIDATION.SELECTED_JUDGMENT_REPLACEMENT_SCHEMA,
            "current_group_semantic_descriptor_sha256": current_descriptor,
            "prior_response_semantic_sha256": (
                REVALIDATION._selected_response_semantic_sha256(prior_response)
            ),
            "replacement_rationale": rationale,
            "response": response,
        }

    def test_selected_rebind_rejects_missing_or_stale_review_protocol_receipt(
        self,
    ) -> None:
        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        overlay_path = (
            self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        )
        descriptors = {selected_key: digest("8"), overlay_key: digest("9")}
        overlay = (
            {overlay_key: {"classification": "validated_source_assumption"}},
            {overlay_key: descriptors[overlay_key]},
            overlay_path,
            hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
        )
        for label, supplied in (("missing", None), ("stale", digest("0"))):
            candidate = copy.deepcopy(attestation)
            if supplied is None:
                candidate.pop(REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD)
            else:
                candidate[REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD] = supplied
            path.write_text(json.dumps(candidate), encoding="utf-8")
            with self.subTest(label=label), patch.object(
                REVALIDATION,
                "_selected_current_group_descriptors",
                return_value=descriptors,
            ), patch.object(
                REVALIDATION,
                "_selected_current_overlay",
                return_value=overlay,
            ), self.assertRaisesRegex(
                REVALIDATION.SourceRecordCurrentRevalidationError,
                "review-protocol receipt",
            ):
                REVALIDATION.selected_rebound_sidecar(
                    raw,
                    prior,
                    candidate,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    prior_sidecar_path=self.prior_path,
                    attestation_path=path,
                    output_sidecar_path=self.judgment_path,
                )

    def test_selected_rebind_replaces_stale_checked_projection_response(self) -> None:
        (
            raw,
            prior,
            attestation,
            path,
            selected_key,
            overlay_key,
            descriptors,
        ) = self.selected_replacement_fixture()
        old_response = prior["items"][selected_key]
        assert isinstance(old_response, dict)
        old_response.update(
            {
                "classification": "proved_from_primitives",
                "checked_projection": {
                    "constructor_declaration": "Fixture.invalid_candidate",
                    "source_antecedent_keys": ["synthetic.antecedent"],
                },
                "lean_derivation": "The archived response incorrectly claimed a constructor route.",
            }
        )
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation["prior_judgment_sidecar_sha256"] = hashlib.sha256(
            self.prior_path.read_bytes()
        ).hexdigest()
        attestation["judgment_replacements"] = {
            selected_key: self.selected_replacement_entry(
                prior_response=old_response,
                current_descriptor=descriptors[selected_key],
                response={
                    "classification": "validated_source_assumption",
                    "reason": "The displayed premise is reviewed directly against the source.",
                    "source_location": "source.txt:1-1",
                },
            )
        }
        path.write_text(json.dumps(attestation), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        overlay = (
            {overlay_key: {"classification": "validated_source_assumption"}},
            {overlay_key: descriptors[overlay_key]},
            overlay_path,
            hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
        )
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value=descriptors,
        ), patch.object(REVALIDATION, "_selected_current_overlay", return_value=overlay):
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )
            entry = rebound["items"][selected_key]
            assert isinstance(entry, dict)
            self.assertEqual(entry["classification"], "validated_source_assumption")
            self.assertNotIn("checked_projection", entry)
            self.assertNotIn("lean_derivation", entry)
            self.assertNotIn(REVALIDATION.PRIOR_ITEM_RECEIPT_FIELD, entry)

            metadata = rebound[REVALIDATION.SELECTED_CURRENT_REVALIDATION_FIELD]
            assert isinstance(metadata, dict)
            self.assertEqual(
                REVALIDATION._selected_rebound_attestation_errors(
                    metadata,
                    raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    sidecar_items=rebound["items"],
                ),
                [],
            )
            tampered = copy.deepcopy(rebound)
            tampered_entry = tampered["items"][selected_key]
            assert isinstance(tampered_entry, dict)
            tampered_entry["checked_projection"] = {"forged": True}
            errors = REVALIDATION._selected_rebound_attestation_errors(
                metadata,
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                sidecar_items=tampered["items"],
            )
        self.assertTrue(
            any("semantic response ledger no longer matches" in error for error in errors),
            errors,
        )

    def test_selected_replacement_rejects_invalid_binding_transport_and_overlap(self) -> None:
        (
            raw,
            prior,
            attestation,
            _path,
            selected_key,
            _overlay_key,
            descriptors,
        ) = self.selected_replacement_fixture()
        prior_response = prior["items"][selected_key]
        assert isinstance(prior_response, dict)

        def replacement() -> dict[str, object]:
            return self.selected_replacement_entry(
                prior_response=prior_response,
                current_descriptor=descriptors[selected_key],
                response={"classification": "validated_source_assumption"},
            )

        mutations = {
            "current-descriptor": (
                lambda value: value.__setitem__(
                    "current_group_semantic_descriptor_sha256", digest("f")
                ),
                "exact current semantic group",
            ),
            "prior-response": (
                lambda value: value.__setitem__(
                    "prior_response_semantic_sha256", digest("f")
                ),
                "archived response",
            ),
            "blank-rationale": (
                lambda value: value.__setitem__("replacement_rationale", ""),
                "lacks a replacement rationale",
            ),
            "freshness-transport": (
                lambda value: value["response"].__setitem__(
                    "source_record_audit_sha256", digest("f")
                ),
                "generated revalidation transport",
            ),
            "source-association-pin": (
                lambda value: value["response"].__setitem__(
                    "semantic_association_sha256", digest("f")
                ),
                "generated source-association credential",
            ),
        }
        for label, (mutate, expected_error) in mutations.items():
            with self.subTest(label=label):
                entry = replacement()
                mutate(entry)
                candidate = {
                    REVALIDATION.ATTESTED_JUDGMENT_REPLACEMENTS_FIELD: {
                        selected_key: entry
                    }
                }
                with self.assertRaisesRegex(
                    REVALIDATION.SourceRecordCurrentRevalidationError, expected_error
                ):
                    REVALIDATION._attested_selected_judgment_replacements(
                        candidate,
                        {selected_key: prior_response},
                        expected_keys={selected_key},
                        current_raw_audit=raw,
                        selected_descriptors={selected_key: descriptors[selected_key]},
                    )

        entry = replacement()
        candidate = {
            REVALIDATION.ATTESTED_JUDGMENT_REPLACEMENTS_FIELD: {
                selected_key: entry
            },
            "judgment_amendments": {selected_key: {"reason": "ambiguous merge"}},
        }
        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "cannot accompany another amendment",
        ):
            REVALIDATION._selected_expected_semantic_items(
                {selected_key: prior_response},
                candidate,
                selected_keys={selected_key},
                current_raw_audit=raw,
                selected_descriptors={selected_key: descriptors[selected_key]},
                paper_dir=self.paper_dir,
            )

        with self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "non-prior selected response",
        ):
            REVALIDATION._attested_selected_judgment_replacements(
                {
                    REVALIDATION.ATTESTED_JUDGMENT_REPLACEMENTS_FIELD: {
                        "other_result.h : R": replacement()
                    }
                },
                {selected_key: prior_response},
                expected_keys={selected_key},
                current_raw_audit=raw,
                selected_descriptors={selected_key: descriptors[selected_key]},
            )

    def test_selected_rebind_writes_only_the_authenticated_overlay_complement(self) -> None:
        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        prior["manual_current_complement"] = {
            "current_source_record_audit_sha256": digest("f")
        }
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation["prior_judgment_sidecar_sha256"] = hashlib.sha256(
            self.prior_path.read_bytes()
        ).hexdigest()
        path.write_text(json.dumps(attestation), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value={selected_key: digest("8"), overlay_key: digest("9")},
        ), patch.object(
            REVALIDATION,
            "_selected_current_overlay",
            return_value=(
                {overlay_key: {"classification": "validated_source_assumption"}},
                {overlay_key: digest("9")},
                overlay_path,
                hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
            ),
        ):
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )
        self.assertEqual(set(rebound["items"]), {selected_key})
        self.assertNotIn("manual_current_complement", rebound)
        self.assertEqual(
            rebound[REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD],
            REVALIDATION.formalization_review_protocol_digest(),
        )
        entry = rebound["items"][selected_key]
        assert isinstance(entry, dict)
        self.assertEqual(entry["source_record_audit_sha256"], raw["source_record_audit_sha256"])
        self.assertIn(REVALIDATION.PRIOR_ITEM_RECEIPT_FIELD, entry)
        self.assertEqual(
            entry[REVALIDATION.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD][
                "current_group_semantic_descriptor_sha256"
            ],
            digest("8"),
        )

    def test_selected_rebind_reprojects_current_association_credentials(self) -> None:
        raw = raw_audit_with_pinned_semantic_model()
        current_pin, nested_pin, selected_response = stale_source_routed_semantic_response(
            raw, stale_pin=digest("f")
        )
        selected_key = str(raw["boundary_input_items"][0]["judgment_key"])
        overlay_key = "other_result.h : R"
        raw["boundary_input_items"].append(raw_item(overlay_key))
        stamp_source_record_audit_receipts(raw)
        prior = prior_sidecar(raw)
        prior["items"][selected_key] = selected_response
        prior["items"][overlay_key] = copy.deepcopy(selected_response)
        prior["items"]["historical-only.h : S"] = copy.deepcopy(selected_response)
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        overlay_path.write_text(json.dumps({"fixture": "overlay"}), encoding="utf-8")
        selected_descriptor = digest("8")
        overlay_descriptor = digest("9")
        attestation = {
            "schema": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "artifact_kind": REVALIDATION.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND,
            "policy_version": REVALIDATION.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            REVALIDATION.FORMALIZATION_REVIEW_PROTOCOL_FIELD: (
                REVALIDATION.formalization_review_protocol_digest()
            ),
            "paper": PAPER,
            "prior_judgment_sidecar_path": "audit/source_record_match_llm.before_revalidation.json",
            "prior_judgment_sidecar_sha256": hashlib.sha256(
                self.prior_path.read_bytes()
            ).hexdigest(),
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "generated_judgment_keys_sha256": REVALIDATION.generated_judgment_keys_sha256(
                raw
            ),
            "generated_judgment_surface_sha256": REVALIDATION.generated_judgment_surface_sha256(
                raw
            ),
            "differential_overlay_path": "audit/source_record_differential_revalidation.json",
            "differential_overlay_sha256": hashlib.sha256(
                overlay_path.read_bytes()
            ).hexdigest(),
            "differential_overlay_current_group_descriptors": {
                overlay_key: overlay_descriptor
            },
            "differential_overlay_current_group_descriptors_sha256": REVALIDATION._canonical_digest(
                {overlay_key: overlay_descriptor}
            ),
            "selected_current_group_descriptors": {selected_key: selected_descriptor},
            "selected_current_group_descriptors_sha256": REVALIDATION._canonical_digest(
                {selected_key: selected_descriptor}
            ),
            "new_judgment_keys_required": [],
            "new_judgments": {},
            "judgment_amendments": {},
            "review_scope": REVALIDATION.SELECTED_CURRENT_REVALIDATION_SCOPE,
            "reviewed_current_semantics": True,
            "reviewer": "fixture selected semantic reviewer",
            "validated_at": "2026-07-27T02:00:00Z",
        }
        path = self.paper_dir / "audit" / "selected_current_semantic_revalidation.json"
        path.write_text(json.dumps(attestation), encoding="utf-8")
        overlay = (
            {overlay_key: {"classification": "validated_source_assumption"}},
            {overlay_key: overlay_descriptor},
            overlay_path,
            hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
        )
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value={
                selected_key: selected_descriptor,
                overlay_key: overlay_descriptor,
            },
        ), patch.object(REVALIDATION, "_selected_current_overlay", return_value=overlay):
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )
            actual = rebound["items"][selected_key]
            assert isinstance(actual, dict)
            self.assertEqual(actual["semantic_association_sha256"], current_pin)
            dimensions = actual["semantic_model_dimensions"]
            assert isinstance(dimensions, dict)
            self.assertEqual(
                dimensions["carrier_and_domain"]["semantic_association_sha256"],
                current_pin,
            )
            self.assertEqual(
                dimensions["joint_law_and_state_evolution"][
                    "semantic_association_sha256"
                ],
                current_pin,
            )
            self.assertEqual(
                dimensions["carrier_and_domain"][
                    SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD
                ]["semantic_association_sha256"],
                nested_pin,
            )
            metadata = rebound[REVALIDATION.SELECTED_CURRENT_REVALIDATION_FIELD]
            assert isinstance(metadata, dict)
            self.assertEqual(
                REVALIDATION._selected_rebound_attestation_errors(
                    metadata,
                    raw,
                    paper=PAPER,
                    paper_dir=self.paper_dir,
                    output_sidecar_path=self.judgment_path,
                    sidecar_items=rebound["items"],
                ),
                [],
            )
            tampered = copy.deepcopy(rebound)
            tampered_dimension = tampered["items"][selected_key][
                "semantic_model_dimensions"
            ]["carrier_and_domain"][SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD]
            assert isinstance(tampered_dimension, dict)
            tampered_dimension["semantic_association_sha256"] = digest("f")
            errors = REVALIDATION._selected_rebound_attestation_errors(
                metadata,
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                sidecar_items=tampered["items"],
            )
        self.assertTrue(
            any("semantic response ledger no longer matches" in error for error in errors),
            errors,
        )

    def test_selected_rebind_archives_stale_overlay_transport_before_current_load(
        self,
    ) -> None:
        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        stale_transport = {
            "schema": 1,
            "current_judgment_key": selected_key,
            "prior_judgment_key": selected_key,
        }
        selected_response = prior["items"][selected_key]
        assert isinstance(selected_response, dict)
        selected_response["source_record_differential_revalidation"] = (
            copy.deepcopy(stale_transport)
        )
        selected_response[
            REVALIDATION.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD
        ] = {"schema": 1}
        self.prior_path.write_text(json.dumps(prior), encoding="utf-8")
        attestation["prior_judgment_sidecar_sha256"] = hashlib.sha256(
            self.prior_path.read_bytes()
        ).hexdigest()
        path.write_text(json.dumps(attestation), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        overlay = (
            {overlay_key: {"classification": "validated_source_assumption"}},
            {overlay_key: digest("9")},
            overlay_path,
            hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
        )
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value={selected_key: digest("8"), overlay_key: digest("9")},
        ), patch.object(REVALIDATION, "_selected_current_overlay", return_value=overlay):
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

        entry = rebound["items"][selected_key]
        assert isinstance(entry, dict)
        self.assertNotIn("source_record_differential_revalidation", entry)
        self.assertNotIn(
            REVALIDATION.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD, entry
        )
        archived = entry[REVALIDATION.PRIOR_ITEM_RECEIPT_FIELD]
        assert isinstance(archived, dict)
        self.assertEqual(
            archived["source_record_differential_revalidation"], stale_transport
        )
        self.assertIn(
            REVALIDATION.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD, archived
        )
        with patch.object(
            REVALIDATION.EVIDENCE, "source_record_audit_identity_error", return_value=""
        ):
            self.assertEqual(
                set(
                    REVALIDATION.EVIDENCE.current_source_record_judgment_items(
                        raw, rebound
                    )
                ),
                {selected_key},
            )

        # Reintroducing the old transport at the active response level is
        # rejected by the shared loader: it is not current selected evidence.
        forged = copy.deepcopy(rebound)
        forged_entry = forged["items"][selected_key]
        assert isinstance(forged_entry, dict)
        forged_entry["source_record_differential_revalidation"] = stale_transport
        with patch.object(
            REVALIDATION.EVIDENCE, "source_record_audit_identity_error", return_value=""
        ):
            self.assertEqual(
                REVALIDATION.EVIDENCE.current_source_record_judgment_items(
                    raw, forged
                ),
                {},
            )

    def test_selected_rebind_rejects_descriptor_ledger_that_omits_a_current_group(self) -> None:
        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        attestation["selected_current_group_descriptors"] = {overlay_key: digest("9")}
        attestation["selected_current_group_descriptors_sha256"] = REVALIDATION._canonical_digest(
            attestation["selected_current_group_descriptors"]
        )
        path.write_text(json.dumps(attestation), encoding="utf-8")
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value={selected_key: digest("8"), overlay_key: digest("9")},
        ), patch.object(
            REVALIDATION,
            "_selected_current_overlay",
            return_value=(
                {overlay_key: {"classification": "validated_source_assumption"}},
                {overlay_key: digest("9")},
                overlay_path,
                hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
            ),
        ), self.assertRaisesRegex(
            REVALIDATION.SourceRecordCurrentRevalidationError,
            "does not cover exactly every current group outside the authenticated overlay",
        ):
            REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )

    def test_selected_rebind_reports_malformed_persisted_descriptor_metadata(self) -> None:
        raw, prior, attestation, path, selected_key, overlay_key = (
            self.selected_revalidation_fixture()
        )
        overlay_path = self.paper_dir / "audit" / "source_record_differential_revalidation.json"
        overlay = (
            {overlay_key: {"classification": "validated_source_assumption"}},
            {overlay_key: digest("9")},
            overlay_path,
            hashlib.sha256(overlay_path.read_bytes()).hexdigest(),
        )
        with patch.object(
            REVALIDATION,
            "_selected_current_group_descriptors",
            return_value={selected_key: digest("8"), overlay_key: digest("9")},
        ), patch.object(REVALIDATION, "_selected_current_overlay", return_value=overlay):
            rebound = REVALIDATION.selected_rebound_sidecar(
                raw,
                prior,
                attestation,
                paper=PAPER,
                paper_dir=self.paper_dir,
                prior_sidecar_path=self.prior_path,
                attestation_path=path,
                output_sidecar_path=self.judgment_path,
            )
            metadata = rebound[REVALIDATION.SELECTED_CURRENT_REVALIDATION_FIELD]
            assert isinstance(metadata, dict)
            metadata["differential_overlay_current_group_descriptors"] = []
            errors = REVALIDATION._selected_rebound_attestation_errors(
                metadata,
                raw,
                paper=PAPER,
                paper_dir=self.paper_dir,
                output_sidecar_path=self.judgment_path,
                sidecar_items=rebound["items"],
            )
        self.assertTrue(
            any("must be an object-valued descriptor ledger" in error for error in errors),
            errors,
        )


if __name__ == "__main__":
    unittest.main()
