#!/usr/bin/env python3
"""Adversarial tests for archived direct-source-status descriptor bridging."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_archived_source_status_projection_bridge as BRIDGE
from scripts import source_record_differential_revalidation as DIFFERENTIAL
from scripts import source_record_obligation_groups as OBLIGATIONS
from scripts.source_coverage_scope import (
    legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
    legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
    source_item_coverage_sha256,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts
from scripts.source_record_target_disposition import (
    semantic_association_record_digest,
    source_contract_association_record_digest,
    source_map_item_record_digest,
)


PAPER = "FixturePaper"


def digest(char: str) -> str:
    return char * 64


def write_json(path: Path, payload: object) -> bytes:
    contents = json_bytes(payload)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(contents)
    return contents


def json_bytes(payload: object) -> bytes:
    return json.dumps(payload, sort_keys=True, indent=2).encode("utf-8") + b"\n"


def statement_map_sha256(payload: object) -> str:
    return hashlib.sha256(json_bytes(payload)).hexdigest()


def source_item(*, status: str = "reviewed") -> dict[str, object]:
    return {
        "source_location": "source.txt:10-12",
        "source_kind": "lemma",
        "source_status": status,
        "source_text": "Lemma. The requested source condition holds.",
        "source_quote": "The requested source condition holds.",
    }


def association(
    item: dict[str, object],
    *,
    semantic: str,
    signature: str = digest("d"),
    role: str = "direct_source_route",
) -> dict[str, object]:
    signature_identity = {
        "qualified_declaration": "Fixture.PaperInterface.checked_result",
        "elaborated_signature_sha256": signature,
    }
    result: dict[str, object] = {
        "schema": 2,
        "association_mode": "explicit_source_map_direct_route",
        "semantic_contract_member_role": role,
        "semantic_model_judgment_key": "semantic-model::opaque-result",
        "source_item_identities": [
            {
                "source_key": "opaque-source-identity",
                "source_location": item["source_location"],
                "source_map_item_sha256": source_map_item_record_digest(item),
                "source_semantic_sha256": semantic,
            }
        ],
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.PaperInterface.checked_result",
            "declaration_sha256": digest("c"),
        },
        "reviewed_elaborated_signature_identity": signature_identity,
        "semantic_association_sha256": semantic_association_record_digest(
            [semantic], signature_identity
        ),
    }
    result["association_sha256"] = source_contract_association_record_digest(result)
    return result


def raw_item(key: str, source_association: dict[str, object]) -> dict[str, object]:
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "row": "opaque-result",
        "binder": "x",
        "expanded_input_type": "P x",
        "row_result_type": "R",
        "expanded_lean_surface": {"input_type": "P x", "result_type": "R"},
        "source_contract_association": source_association,
        "reviewed_elaborated_signature_identities": [
            source_association["reviewed_elaborated_signature_identity"]
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("1"),
        "source_record_item_context_sha256": digest("2"),
        "source_record_item_sha256": digest("3"),
    }


def raw_audit(
    item: dict[str, object],
    fidelity: dict[str, object],
    *,
    paper_statement_map_sha256: str,
) -> dict[str, object]:
    raw: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "paper_statement_map_sha256": paper_statement_map_sha256,
        "boundary_input_items": [item],
        "conclusion_dependency_items": [],
        "recursive_field_items": [],
        "semantic_model_items": [],
        "source_proof_fidelity": copy.deepcopy(fidelity),
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(raw)
    return raw


def sidecar(raw: dict[str, object], key: str, prior_semantic_pin: str) -> dict[str, object]:
    response = {
        "classification": "validated_source_assumption",
        "reason": "fixture source review",
        "prompt_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_audit_sha256": raw["source_record_audit_sha256"],
        "validator": "fixture auditor",
        "validated_at": "2026-07-28T00:00:00Z",
        "semantic_association_sha256": prior_semantic_pin,
    }
    return {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_audit_sha256": raw["source_record_audit_sha256"],
        "validator": "fixture auditor",
        "validated_at": "2026-07-28T00:00:00Z",
        "items": {key: response},
    }


class ArchivedSourceStatusProjectionBridgeTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.fidelity = {
            "schema": 2,
            "paper": PAPER,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": digest("f"),
            "defects": [],
            "model_conventions": [],
        }
        self.map_item = source_item()
        self.statement_map = {"paper": PAPER, "items": {"opaque-source-identity": self.map_item}}
        self.prior_semantic = (
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                self.map_item, ""
            )
        )
        self.current_semantic = source_item_coverage_sha256(self.map_item, "")
        self.assertNotEqual(self.prior_semantic, self.current_semantic)
        self.prior_association = association(
            self.map_item, semantic=self.prior_semantic
        )
        self.current_association = association(
            self.map_item, semantic=self.current_semantic
        )
        self.prior_key = "archive-address-that-must-not-match"
        self.current_key = "current-address-that-must-not-match"
        self.prior_raw = raw_audit(
            raw_item(self.prior_key, self.prior_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.current_raw = raw_audit(
            raw_item(self.current_key, self.current_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.prior_judgments = sidecar(
            self.prior_raw,
            self.prior_key,
            self.prior_association["semantic_association_sha256"],
        )
        self.paths = {
            "prior_raw": self.audit_dir / "source_record_audit.before_schema5.json",
            "prior_judgments": self.audit_dir / "source_record_match_llm.before_schema5.json",
            "prior_map": self.audit_dir / "paper_statement_map.before_schema5.json",
            "prior_fidelity": self.audit_dir / "source_proof_fidelity.before_schema5.json",
            "current_raw": self.audit_dir / "source_record_audit.json",
            "current_map": self.audit_dir / "paper_statement_map.json",
            "current_fidelity": self.audit_dir / "source_proof_fidelity.json",
            "bridge": self.audit_dir / "source_record_archived_source_status_projection_bridge.json",
            "overlay": self.audit_dir / "source_record_differential_revalidation.json",
        }
        self._write_inputs()

    def _write_inputs(self) -> None:
        write_json(self.paths["prior_raw"], self.prior_raw)
        write_json(self.paths["prior_judgments"], self.prior_judgments)
        write_json(self.paths["prior_map"], self.statement_map)
        write_json(self.paths["prior_fidelity"], self.fidelity)
        write_json(self.paths["current_raw"], self.current_raw)
        write_json(self.paths["current_map"], self.statement_map)
        write_json(self.paths["current_fidelity"], self.fidelity)

    def _payload_and_bytes(self, path_key: str) -> tuple[dict[str, object], bytes]:
        path = self.paths[path_key]
        return json.loads(path.read_text(encoding="utf-8")), path.read_bytes()

    def _build_bridge_result(self) -> tuple[dict[str, object] | None, str]:
        prior_raw, prior_raw_bytes = self._payload_and_bytes("prior_raw")
        prior_judgments, prior_judgments_bytes = self._payload_and_bytes("prior_judgments")
        prior_map, prior_map_bytes = self._payload_and_bytes("prior_map")
        prior_fidelity, prior_fidelity_bytes = self._payload_and_bytes("prior_fidelity")
        current_raw, current_raw_bytes = self._payload_and_bytes("current_raw")
        current_map, current_map_bytes = self._payload_and_bytes("current_map")
        current_fidelity, current_fidelity_bytes = self._payload_and_bytes("current_fidelity")
        return BRIDGE.build_archived_source_status_projection_bridge(
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_raw_audit=prior_raw,
            prior_raw_audit_bytes=prior_raw_bytes,
            prior_raw_audit_path=self.paths["prior_raw"],
            prior_judgments=prior_judgments,
            prior_judgments_bytes=prior_judgments_bytes,
            prior_judgments_path=self.paths["prior_judgments"],
            prior_statement_map=prior_map,
            prior_statement_map_bytes=prior_map_bytes,
            prior_statement_map_path=self.paths["prior_map"],
            prior_source_proof_fidelity=prior_fidelity,
            prior_source_proof_fidelity_bytes=prior_fidelity_bytes,
            prior_source_proof_fidelity_path=self.paths["prior_fidelity"],
            current_raw_audit=current_raw,
            current_raw_audit_bytes=current_raw_bytes,
            current_raw_audit_path=self.paths["current_raw"],
            current_statement_map=current_map,
            current_statement_map_bytes=current_map_bytes,
            current_statement_map_path=self.paths["current_map"],
            current_source_proof_fidelity=current_fidelity,
            current_source_proof_fidelity_bytes=current_fidelity_bytes,
            current_source_proof_fidelity_path=self.paths["current_fidelity"],
        )

    def build_bridge(self) -> dict[str, object]:
        receipt, error = self._build_bridge_result()
        self.assertEqual(error, "")
        assert receipt is not None
        return receipt

    def save_bridge(self) -> dict[str, object]:
        receipt = self.build_bridge()
        write_json(self.paths["bridge"], receipt)
        return receipt

    def test_exact_bridge_replays_and_rebinds_only_complete_association(self) -> None:
        receipt = self.save_bridge()
        context, loaded_receipt, evidence, error = (
            BRIDGE.load_archived_source_status_projection_bridge_context(
                paper=PAPER, paper_dir=self.paper_dir, receipt_path=self.paths["bridge"]
            )
        )
        self.assertEqual(error, "")
        self.assertEqual(receipt, loaded_receipt)
        self.assertIsNotNone(evidence)
        assert context is not None
        rebound = BRIDGE.normalized_archived_source_status_association(
            self.prior_association, context
        )
        self.assertEqual(rebound, self.current_association)
        self.assertTrue(
            BRIDGE.archived_source_status_association_is_rebound(
                self.prior_association, context
            )
        )
        changed_role = copy.deepcopy(self.prior_association)
        changed_role["semantic_contract_member_role"] = "unrelated-route-role"
        changed_role["association_sha256"] = source_contract_association_record_digest(
            changed_role
        )
        self.assertEqual(
            BRIDGE.normalized_archived_source_status_association(changed_role, context),
            changed_role,
        )

    def _configure_schema_only_transition(self) -> None:
        self.map_item = source_item()
        self.map_item.pop("source_status")
        self.statement_map = {
            "paper": PAPER,
            "items": {"opaque-source-identity": self.map_item},
        }
        self.prior_semantic = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                self.map_item, ""
            )
        )
        self.current_semantic = source_item_coverage_sha256(self.map_item, "")
        self.assertNotEqual(self.prior_semantic, self.current_semantic)
        self.prior_association = association(
            self.map_item, semantic=self.prior_semantic
        )
        self.current_association = association(
            self.map_item, semantic=self.current_semantic
        )
        self.prior_raw = raw_audit(
            raw_item(self.prior_key, self.prior_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.current_raw = raw_audit(
            raw_item(self.current_key, self.current_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.prior_judgments = sidecar(
            self.prior_raw,
            self.prior_key,
            self.prior_association["semantic_association_sha256"],
        )

    def test_bridge_allows_schema_only_transition_without_source_status(self) -> None:
        """Schema-4 items that already excluded status need no fake status field."""

        self._configure_schema_only_transition()
        self._write_inputs()

        receipt = self.build_bridge()
        binding = receipt["association_rebinds"][0]
        self.assertEqual(
            binding["source_identity_rebinds"][0]["transition_kind"],
            "schema4_direct_source_status_excluded_to_schema5_excluded",
        )

    def test_schema_only_transition_rejects_unbound_prior_or_current_map_bytes(self) -> None:
        """The no-status branch cannot substitute a same-item map snapshot."""

        self._configure_schema_only_transition()
        for path_key, label in (("prior_map", "prior"), ("current_map", "current")):
            self._write_inputs()
            substituted_map = copy.deepcopy(self.statement_map)
            # This preserves the associated item exactly. Before the receipt
            # check, the bridge accepted it despite the raw audit naming
            # different map bytes.
            substituted_map["unrelated_snapshot_metadata"] = {
                "not_the_map_used_by_raw": True
            }
            write_json(self.paths[path_key], substituted_map)

            receipt, error = self._build_bridge_result()

            self.assertIsNone(receipt)
            self.assertIn(
                f"{label} raw audit statement-map receipt differs from supplied statement-map bytes",
                error,
            )

    def test_bridge_rejects_source_status_or_map_content_change(self) -> None:
        self.save_bridge()
        changed_map = copy.deepcopy(self.statement_map)
        changed_map["items"]["opaque-source-identity"]["source_status"] = "changed"
        write_json(self.paths["current_map"], changed_map)
        context, _receipt, _evidence, error = (
            BRIDGE.load_archived_source_status_projection_bridge_context(
                paper=PAPER, paper_dir=self.paper_dir, receipt_path=self.paths["bridge"]
            )
        )
        self.assertIsNone(context)
        self.assertIn("differ", error)

    def test_bridge_refuses_noncanonical_source_status_lookalike(self) -> None:
        """A semantic lookalike cannot enter the direct-status receipt lane."""

        self.map_item = source_item()
        self.map_item[" Source_Status "] = self.map_item.pop("source_status")
        self.statement_map = {
            "paper": PAPER,
            "items": {"opaque-source-identity": self.map_item},
        }

        # This recreates the prior schema-4 projection that would have
        # normalized a lookalike.  Schema 5 retains that unknown field, so a
        # receipt must refuse rather than transport the changed identity.
        self.prior_semantic = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                self.map_item, ""
            )
        )
        self.current_semantic = source_item_coverage_sha256(self.map_item, "")
        self.assertNotEqual(self.prior_semantic, self.current_semantic)
        self.prior_association = association(
            self.map_item, semantic=self.prior_semantic
        )
        self.current_association = association(
            self.map_item, semantic=self.current_semantic
        )
        self.prior_raw = raw_audit(
            raw_item(self.prior_key, self.prior_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.current_raw = raw_audit(
            raw_item(self.current_key, self.current_association),
            self.fidelity,
            paper_statement_map_sha256=statement_map_sha256(self.statement_map),
        )
        self.prior_judgments = sidecar(
            self.prior_raw,
            self.prior_key,
            self.prior_association["semantic_association_sha256"],
        )
        self._write_inputs()

        receipt, error = self._build_bridge_result()
        self.assertIsNone(receipt)
        self.assertIn("exactly one top-level source_status", error)

    def test_bridge_rejects_source_fidelity_or_archived_sidecar_substitution(self) -> None:
        self.save_bridge()
        changed_fidelity = copy.deepcopy(self.fidelity)
        changed_fidelity["model_conventions"] = [{"id": "new", "sha": digest("9")}]
        write_json(self.paths["current_fidelity"], changed_fidelity)
        context, _receipt, _evidence, error = (
            BRIDGE.load_archived_source_status_projection_bridge_context(
                paper=PAPER, paper_dir=self.paper_dir, receipt_path=self.paths["bridge"]
            )
        )
        self.assertIsNone(context)
        self.assertIn("differs", error)

        self._write_inputs()
        altered_sidecar = copy.deepcopy(self.prior_judgments)
        altered_sidecar["items"][self.prior_key]["reason"] = "substituted"
        write_json(self.paths["prior_judgments"], altered_sidecar)
        context, _receipt, _evidence, error = (
            BRIDGE.load_archived_source_status_projection_bridge_context(
                paper=PAPER, paper_dir=self.paper_dir, receipt_path=self.paths["bridge"]
            )
        )
        self.assertIsNone(context)
        self.assertIn("differs", error)

    def test_bridge_rejects_nonadministrative_current_association_change(self) -> None:
        altered = copy.deepcopy(self.current_raw)
        association_value = altered["boundary_input_items"][0]["source_contract_association"]
        assert isinstance(association_value, dict)
        association_value["semantic_contract_member_role"] = "different-role"
        association_value["association_sha256"] = source_contract_association_record_digest(
            association_value
        )
        stamp_source_record_audit_receipts(altered)
        self.current_raw = altered
        write_json(self.paths["current_raw"], altered)
        # Call the lower-level routine directly to make the refusal condition
        # explicit rather than treating a build exception as evidence.
        current_raw, current_raw_bytes = self._payload_and_bytes("current_raw")
        prior_raw, prior_raw_bytes = self._payload_and_bytes("prior_raw")
        prior_sidecar, prior_sidecar_bytes = self._payload_and_bytes("prior_judgments")
        prior_map, prior_map_bytes = self._payload_and_bytes("prior_map")
        prior_fidelity, prior_fidelity_bytes = self._payload_and_bytes("prior_fidelity")
        current_map, current_map_bytes = self._payload_and_bytes("current_map")
        current_fidelity, current_fidelity_bytes = self._payload_and_bytes("current_fidelity")
        result, refusal = BRIDGE.build_archived_source_status_projection_bridge(
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_raw_audit=prior_raw,
            prior_raw_audit_bytes=prior_raw_bytes,
            prior_raw_audit_path=self.paths["prior_raw"],
            prior_judgments=prior_sidecar,
            prior_judgments_bytes=prior_sidecar_bytes,
            prior_judgments_path=self.paths["prior_judgments"],
            prior_statement_map=prior_map,
            prior_statement_map_bytes=prior_map_bytes,
            prior_statement_map_path=self.paths["prior_map"],
            prior_source_proof_fidelity=prior_fidelity,
            prior_source_proof_fidelity_bytes=prior_fidelity_bytes,
            prior_source_proof_fidelity_path=self.paths["prior_fidelity"],
            current_raw_audit=current_raw,
            current_raw_audit_bytes=current_raw_bytes,
            current_raw_audit_path=self.paths["current_raw"],
            current_statement_map=current_map,
            current_statement_map_bytes=current_map_bytes,
            current_statement_map_path=self.paths["current_map"],
            current_source_proof_fidelity=current_fidelity,
            current_source_proof_fidelity_bytes=current_fidelity_bytes,
            current_source_proof_fidelity_path=self.paths["current_fidelity"],
        )
        self.assertIsNone(result)
        self.assertIn("absent or differs", refusal)




if __name__ == "__main__":  # pragma: no cover
    unittest.main()
