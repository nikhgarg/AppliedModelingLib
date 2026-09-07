#!/usr/bin/env python3
"""Focused tests for historical source-association snapshot reconciliation."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import (  # noqa: E402
    source_record_historical_association_snapshot_reconciliation as RECONCILIATION,
)
from scripts.source_coverage_scope import (  # noqa: E402
    source_record_source_item_record_sha256,
    source_record_source_item_semantic_sha256,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402
from scripts.source_record_target_disposition import (  # noqa: E402
    source_contract_association_record_digest,
)


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _map_item(*, evidence: str = "Fixture.Proofs.main") -> dict[str, object]:
    return {
        "statement": "The source theorem says P.",
        "source_location": "sources/fixture.txt:10-12",
        "source_kind": "theorem",
        "coverage_status": "covered",
        "claim_bearing": True,
        "source_anchor_evidence": [
            {
                "path": "sources/fixture.txt",
                "line_start": 10,
                "line_end": 12,
                "quoted_text": "Theorem 1. P.",
                "quoted_text_sha256": _sha("Theorem 1. P."),
            }
        ],
        "semantic_contract": {
            "evidence_declaration": evidence,
            "spec_declaration": evidence + "Spec",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
    }


def _association(
    item: dict[str, object],
    *,
    source_key: str,
    include_by_key: bool = True,
) -> dict[str, object]:
    item_digest = source_record_source_item_record_sha256(item)
    identity: dict[str, object] = {
        "source_key": source_key,
        "source_location": item["source_location"],
        "source_kind": item["source_kind"],
        "semantic_contract": copy.deepcopy(item["semantic_contract"]),
        "source_map_item_sha256": item_digest,
        "source_semantic_sha256": source_record_source_item_semantic_sha256(item, ""),
    }
    association: dict[str, object] = {
        "schema": 2,
        "source_item_identities": [identity],
    }
    if include_by_key:
        association["source_map_item_keys"] = [source_key]
        association["source_map_item_sha256_by_key"] = {source_key: item_digest}
    association["association_sha256"] = source_contract_association_record_digest(
        association
    )
    return association


def _raw(
    item: dict[str, object],
    *,
    source_key: str = "archived_storage_key",
    reported_map_sha: str = "0" * 64,
    section_associations: dict[str, list[dict[str, object]]] | None = None,
) -> dict[str, object]:
    if section_associations is None:
        section_associations = {
            "boundary_input_items": [
                {"source_contract_association": _association(item, source_key=source_key)}
            ]
        }
    raw: dict[str, object] = {
        "paper": "FixturePaper",
        "prompt_version": "source-record-v10-semantic-conclusion-boundary-contract",
        "source_record_policy_version": "source-record-v10-semantic-conclusion-boundary-contract",
        "paper_statement_map_sha256": reported_map_sha,
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    for section in RECONCILIATION.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw[section] = section_associations.get(section, [])
    stamp_source_record_audit_receipts(raw)
    return raw


class HistoricalAssociationSnapshotReconciliationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.paper_dir = Path(self.temporary.name) / "papers" / "FixturePaper"
        (self.paper_dir / "audit").mkdir(parents=True)
        self.raw_path = self.paper_dir / "audit" / "source_record_audit.archived.json"
        self.map_path = self.paper_dir / "audit" / "paper_statement_map.witness.json"
        self.artifact_path = (
            self.paper_dir
            / "audit"
            / RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        )

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def _write_json(self, path: Path, value: object) -> None:
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    def _write_fixture(
        self,
        *,
        item: dict[str, object] | None = None,
        raw: dict[str, object] | None = None,
        witness_items: dict[str, object] | None = None,
    ) -> tuple[dict[str, object], dict[str, object]]:
        item = _map_item() if item is None else item
        witness = {
            "schema": 1,
            "paper": "FixturePaper",
            "items": (
                {"witness_storage_key": item}
                if witness_items is None
                else witness_items
            ),
        }
        raw = _raw(item) if raw is None else raw
        self._write_json(self.map_path, witness)
        self._write_json(self.raw_path, raw)
        return raw, witness

    def _create(self) -> dict[str, object]:
        return RECONCILIATION.create_historical_association_snapshot_reconciliation(
            paper_dir=self.paper_dir,
            paper="FixturePaper",
            raw_audit_path=self.raw_path,
            witness_map_path=self.map_path,
        )

    def _write_artifact(self) -> dict[str, object]:
        return RECONCILIATION.write_historical_association_snapshot_reconciliation(
            paper_dir=self.paper_dir,
            paper="FixturePaper",
            raw_audit_path=self.raw_path,
            witness_map_path=self.map_path,
            output_path=self.artifact_path,
        )

    def test_successful_mismatch_uses_exact_full_item_digest_not_storage_key(self) -> None:
        self._write_fixture()
        artifact = self._write_artifact()

        self.assertTrue(artifact["does_not_repair_archived_raw_aggregate_receipt"])
        self.assertNotEqual(
            artifact["archived_raw_audit"]["reported_paper_statement_map_sha256"],
            artifact["immutable_witness_statement_map"]["actual_paper_statement_map_sha256"],
        )
        ledger = artifact["association_identity_ledger"]
        self.assertEqual(ledger["identity_count"], 1)
        self.assertEqual(
            ledger["identity_rows"][0]["source_map_item_sha256"],
            source_record_source_item_record_sha256(_map_item()),
        )

        loaded = RECONCILIATION.load_historical_association_snapshot_reconciliation(
            paper_dir=self.paper_dir,
            paper="FixturePaper",
            artifact_path=self.artifact_path,
        )
        self.assertTrue(
            RECONCILIATION.is_loaded_historical_association_snapshot_reconciliation(
                loaded
            )
        )

    def test_reconciles_a_raw_pin_across_refreshable_correspondence_receipts(self) -> None:
        item = _map_item()
        item["source_spec_correspondence"] = {
            "schema": 1,
            "source_atoms_sha256": "a" * 64,
            "spec_closure_sha256": "b" * 64,
            "spec_surface_sha256": "c" * 64,
            "closure_environment_sha256": "d" * 64,
            "item_identity_sha256": "e" * 64,
            "source_atom_bindings": [],
            "closure_node_dispositions": [],
        }
        self._write_fixture(item=item)

        artifact = self._create()
        self.assertEqual(
            artifact["association_identity_ledger"]["identity_rows"][0][
                "source_map_item_sha256"
            ],
            source_record_source_item_record_sha256(item),
        )

    def test_reconciles_every_generator_owned_section_not_only_judgment_responses(self) -> None:
        item = _map_item()
        section_associations: dict[str, list[dict[str, object]]] = {}
        for index, section in enumerate(
            RECONCILIATION.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS
        ):
            association = _association(
                item,
                source_key=f"archived_key_{index}",
                # Semantic-model-style association structures have only their
                # per-identity full pins.  Those pins are still complete.
                include_by_key=section != "semantic_model_items",
            )
            field = (
                "semantic_contract_source_association"
                if section == "semantic_model_items"
                else "source_contract_association"
            )
            section_associations[section] = [{field: association}]
        self._write_fixture(item=item, raw=_raw(item, section_associations=section_associations))

        artifact = self._create()
        ledger = artifact["association_identity_ledger"]
        self.assertEqual(
            ledger["identity_count"],
            len(RECONCILIATION.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS),
        )
        self.assertEqual(
            ledger["covered_raw_sections"],
            list(RECONCILIATION.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS),
        )

    def test_loader_rejects_mutated_raw_bytes(self) -> None:
        self._write_fixture()
        self._write_artifact()
        self.raw_path.write_text("{}\n", encoding="utf-8")

        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "raw-audit bytes differ",
        ):
            RECONCILIATION.load_historical_association_snapshot_reconciliation(
                paper_dir=self.paper_dir,
                paper="FixturePaper",
                artifact_path=self.artifact_path,
            )

    def test_loader_rejects_mutated_witness_bytes(self) -> None:
        self._write_fixture()
        self._write_artifact()
        self.map_path.write_text("{}\n", encoding="utf-8")

        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "witness statement-map bytes differ",
        ):
            RECONCILIATION.load_historical_association_snapshot_reconciliation(
                paper_dir=self.paper_dir,
                paper="FixturePaper",
                artifact_path=self.artifact_path,
            )

    def test_rejects_a_reported_map_hash_that_already_matches_witness(self) -> None:
        item = _map_item()
        witness = {"schema": 1, "paper": "FixturePaper", "items": {"current": item}}
        self._write_json(self.map_path, witness)
        current_map_sha = hashlib.sha256(self.map_path.read_bytes()).hexdigest()
        self._write_json(self.raw_path, _raw(item, reported_map_sha=current_map_sha))

        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "inapplicable",
        ):
            self._create()

    def test_rejects_absent_and_mismatched_full_item_pins(self) -> None:
        item = _map_item()
        raw = _raw(item)
        association = raw["boundary_input_items"][0]["source_contract_association"]
        assert isinstance(association, dict)
        identity = association["source_item_identities"][0]
        assert isinstance(identity, dict)
        identity.pop("source_map_item_sha256")
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        # The raw receipt must remain internally valid to prove this is the
        # reconciliation's pin check rather than a raw-receipt shortcut.
        stamp_source_record_audit_receipts(raw)
        self._write_fixture(item=item, raw=raw)
        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "complete source-map item SHA-256",
        ):
            self._create()

        raw = _raw(item)
        association = raw["boundary_input_items"][0]["source_contract_association"]
        assert isinstance(association, dict)
        identity = association["source_item_identities"][0]
        assert isinstance(identity, dict)
        identity["source_map_item_sha256"] = "f" * 64
        association["source_map_item_sha256_by_key"] = {
            "archived_storage_key": "f" * 64
        }
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        stamp_source_record_audit_receipts(raw)
        self._write_fixture(item=item, raw=raw)
        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "no witness items",
        ):
            self._create()

    def test_rejects_ambiguous_full_item_digest(self) -> None:
        item = _map_item()
        self._write_fixture(
            item=item,
            witness_items={"first": item, "second": copy.deepcopy(item)},
        )

        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "multiple witness items",
        ):
            self._create()

    def test_source_key_is_not_a_match_key_but_contract_fqn_mismatch_is_rejected(self) -> None:
        item = _map_item()
        # The witness uses a different storage key.  The exact item digest is
        # unchanged, so a key-independent reconciliation is admissible.
        self._write_fixture(item=item)
        self.assertEqual(self._create()["association_identity_ledger"]["identity_count"], 1)

        raw = _raw(item)
        association = raw["boundary_input_items"][0]["source_contract_association"]
        assert isinstance(association, dict)
        identity = association["source_item_identities"][0]
        assert isinstance(identity, dict)
        contract = identity["semantic_contract"]
        assert isinstance(contract, dict)
        contract["evidence_declaration"] = "Fixture.Renamed.notTheWitness"
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        # Keep the full map digest pin unchanged deliberately.  A name-driven
        # matcher could accept this through the storage key; the reconciliation
        # must compare the full semantic contract of the digest-selected item.
        stamp_source_record_audit_receipts(raw)
        self._write_fixture(item=item, raw=raw)
        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "semantic contract differs",
        ):
            self._create()

    def test_rejects_explicit_candidate_raw_even_with_valid_receipts(self) -> None:
        item = _map_item()
        raw = _raw(item)
        raw["candidate_only"] = True
        stamp_source_record_audit_receipts(raw)
        self._write_fixture(item=item, raw=raw)

        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "explicitly marked non-evidence",
        ):
            self._create()

    def test_serialized_loader_marker_cannot_forge_loaded_authority(self) -> None:
        self._write_fixture()
        self._write_artifact()
        parsed = json.loads(self.artifact_path.read_text(encoding="utf-8"))
        parsed["loader_replay_required"] = True
        parsed["loaded_by_reconciliation_loader"] = True
        self.assertFalse(
            RECONCILIATION.is_loaded_historical_association_snapshot_reconciliation(
                parsed
            )
        )

        loaded = RECONCILIATION.load_historical_association_snapshot_reconciliation(
            paper_dir=self.paper_dir,
            paper="FixturePaper",
            artifact_path=self.artifact_path,
        )
        self.assertTrue(
            RECONCILIATION.is_loaded_historical_association_snapshot_reconciliation(
                loaded
            )
        )

        # A digest is content integrity, not a secret.  Even an attacker that
        # recomputes it after adding a purported loader marker cannot obtain
        # authority: the replayed immutable-input payload differs.
        parsed[
            RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD
        ] = RECONCILIATION._canonical_digest(
            {
                key: value
                for key, value in parsed.items()
                if key
                != RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_INTEGRITY_FIELD
            }
        )
        self._write_json(self.artifact_path, parsed)
        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "does not equal replayed immutable inputs",
        ):
            RECONCILIATION.load_historical_association_snapshot_reconciliation(
                paper_dir=self.paper_dir,
                paper="FixturePaper",
                artifact_path=self.artifact_path,
            )

    def test_writer_refuses_reserved_raw_map_and_ordinary_sidecar_paths(self) -> None:
        self._write_fixture()
        for relative in (
            "audit/source_record_audit.json",
            "audit/paper_statement_map.json",
            # This one deliberately does not exist; path reservation must not
            # rely on the ordinary existing-file refusal.
            "audit/source_record_match_llm.json",
        ):
            with self.subTest(relative=relative), self.assertRaisesRegex(
                RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
                "reserved evidence path",
            ):
                RECONCILIATION.write_historical_association_snapshot_reconciliation(
                    paper_dir=self.paper_dir,
                    paper="FixturePaper",
                    raw_audit_path=self.raw_path,
                    witness_map_path=self.map_path,
                    output_path=self.paper_dir / relative,
                )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
