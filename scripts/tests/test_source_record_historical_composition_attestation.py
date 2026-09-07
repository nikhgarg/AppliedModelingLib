#!/usr/bin/env python3
"""Focused tests for historical selected-plus-overlay composition recovery."""

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

from scripts import source_record_current_revalidation as CURRENT  # noqa: E402
from scripts import source_record_obligation_groups as OBLIGATIONS  # noqa: E402
from scripts import (  # noqa: E402
    source_record_historical_composition_attestation as COMPOSITION,
)
from scripts import source_record_semantic_rebind as REBIND  # noqa: E402
from scripts.formalization_protocol import (  # noqa: E402
    FORMALIZATION_REVIEW_PROTOCOL_FIELD,
    formalization_review_protocol_digest,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "FixtureHistoricalComposition"
PROMPT = OBLIGATIONS.SOURCE_RECORD_V10_PROMPT_VERSION


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _raw_item(
    key: str,
    *,
    input_type: str = "P",
    qualified_declaration: str | None = None,
) -> dict[str, object]:
    """Two differently named storage slots can have one identical descriptor."""

    qualified = qualified_declaration or f"{PAPER}.PaperInterface.proposition"
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "expanded_input_type": input_type,
        "expanded_lean_surface": {
            "input_type": input_type,
            "result_type": "Q",
            "semantic_shape": {"is_proposition": True},
        },
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified,
            "declaration_sha256": "a" * 64,
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": "b" * 64,
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        "source_record_item_semantic_id": "c" * 64,
        "source_record_item_context_sha256": "d" * 64,
        "source_record_item_sha256": "e" * 64,
    }


class HistoricalCompositionAttestationTests(unittest.TestCase):
    def _fixture(
        self,
        *,
        selected_key: str = "arbitrary_storage_slot_one",
        overlay_key: str = "unrelated_storage_slot_two",
        duplicate_descriptors: bool = True,
        qualified_declaration: str | None = None,
    ) -> dict[str, object]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        paper_dir = Path(temporary.name) / PAPER
        audit = paper_dir / "audit"
        audit.mkdir(parents=True)

        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_policy_version": PROMPT,
            "boundary_input_items": [
                _raw_item(selected_key, qualified_declaration=qualified_declaration),
                _raw_item(
                    overlay_key,
                    input_type="P" if duplicate_descriptors else "R",
                    qualified_declaration=qualified_declaration,
                ),
            ],
            "lean_check": {"returncode": 0},
        }
        stamp_source_record_audit_receipts(raw)
        raw_path = audit / "source_record_audit.archived.json"
        _write(raw_path, raw)

        groups, group_errors = OBLIGATIONS.raw_source_record_obligation_groups(raw)
        self.assertEqual(group_errors, {})
        descriptors = {
            key: str(group["descriptor_sha256"]) for key, group in groups.items()
        }
        if duplicate_descriptors:
            self.assertEqual(descriptors[selected_key], descriptors[overlay_key])

        base = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": "f" * 64,
            "validator": "base reviewer",
            "validated_at": "2026-07-01T00:00:00Z",
            "items": {
                selected_key: {
                    "classification": "validated_source_assumption",
                    "reason": "The selected source input is reviewed directly.",
                }
            },
        }
        base_path = audit / "base_sidecar.json"
        _write(base_path, base)
        base_sha = hashlib.sha256(base_path.read_bytes()).hexdigest()

        overlay_payload = {"fixture": "overlay bytes"}
        overlay_path = audit / "overlay.json"
        _write(overlay_path, overlay_payload)
        overlay_sha = hashlib.sha256(overlay_path.read_bytes()).hexdigest()

        selected_attestation = {
            "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "artifact_kind": CURRENT.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND,
            "policy_version": CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            "paper": PAPER,
            "prior_judgment_sidecar_path": "audit/base_sidecar.json",
            "prior_judgment_sidecar_sha256": base_sha,
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(raw),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(raw),
            "differential_overlay_path": "audit/overlay.json",
            "differential_overlay_sha256": overlay_sha,
            "differential_overlay_current_group_descriptors": {
                overlay_key: descriptors[overlay_key]
            },
            "differential_overlay_current_group_descriptors_sha256": CURRENT._canonical_digest(
                {overlay_key: descriptors[overlay_key]}
            ),
            "selected_current_group_descriptors": {
                selected_key: descriptors[selected_key]
            },
            "selected_current_group_descriptors_sha256": CURRENT._canonical_digest(
                {selected_key: descriptors[selected_key]}
            ),
            "new_judgment_keys_required": [],
            "new_judgments": {},
            "judgment_amendments": {},
            "review_scope": CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE,
            "reviewed_current_semantics": True,
            "reviewer": "historical selected reviewer",
            "validated_at": "2026-07-02T00:00:00Z",
        }
        # Intentionally no scoped protocol receipt: the special adapter may
        # recover it only below the new current-protocol parent attestation.
        selected_attestation_path = audit / "selected_attestation.json"
        _write(selected_attestation_path, selected_attestation)
        selected_attestation_sha = hashlib.sha256(selected_attestation_path.read_bytes()).hexdigest()

        current_groups = CURRENT.generated_judgment_items(raw)
        selected_response = copy.deepcopy(base["items"][selected_key])
        assert isinstance(selected_response, dict)
        selected_response.update(
            {
                "prompt_version": PROMPT,
                "validator": selected_attestation["reviewer"],
                "validated_at": selected_attestation["validated_at"],
                "source_record_audit_sha256": raw["source_record_audit_sha256"],
            }
        )
        selected_pins = CURRENT._current_item_pins(current_groups[selected_key])
        selected_response["source_record_item_digest_schema"] = CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        selected_response["source_record_item_sha256s"] = selected_pins
        selected_response["source_record_item_sha256"] = selected_pins[0][
            "source_record_item_sha256"
        ]
        selected_response[CURRENT.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD] = {
            "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "attestation_sha256": selected_attestation_sha,
            "current_group_semantic_descriptor_sha256": descriptors[selected_key],
        }

        loaded_overlay = {
            overlay_key: {
                "classification": "validated_source_assumption",
                "reason": "The overlay route was independently checked.",
                "validator": "overlay reviewer",
                "validated_at": "2026-07-02T00:01:00Z",
                "source_record_audit_sha256": "9" * 64,
            }
        }
        overlay_response = copy.deepcopy(loaded_overlay[overlay_key])
        historical_receipt = {
            field: overlay_response.pop(field)
            for field in list(overlay_response)
            if field.startswith("source_record_item_")
            or field in CURRENT._HISTORICAL_SELECTED_REBIND_TRANSPORT_FIELDS
        }
        if historical_receipt:
            overlay_response[CURRENT.PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        overlay_response["source_record_audit_sha256"] = raw["source_record_audit_sha256"]
        overlay_pins = CURRENT._current_item_pins(current_groups[overlay_key])
        overlay_response["source_record_item_digest_schema"] = CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        overlay_response["source_record_item_sha256s"] = overlay_pins
        overlay_response["source_record_item_sha256"] = overlay_pins[0][
            "source_record_item_sha256"
        ]
        overlay_response[CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD] = {
            "schema": CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA,
            "prior_source_record_audit_sha256": "9" * 64,
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "current_group_semantic_descriptor_sha256": descriptors[overlay_key],
            "differential_overlay_sha256": overlay_sha,
        }

        selected_ledger = {selected_key: descriptors[selected_key]}
        overlay_ledger = {overlay_key: descriptors[overlay_key]}
        selected_metadata = {
            "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "policy_version": CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            "attestation_path": "audit/selected_attestation.json",
            "attestation_sha256": selected_attestation_sha,
            "prior_judgment_sidecar_path": "audit/base_sidecar.json",
            "prior_judgment_sidecar_sha256": base_sha,
            "current_judgment_sidecar_path": "audit/source_record_match_llm.json",
            "differential_overlay_path": "audit/overlay.json",
            "differential_overlay_sha256": overlay_sha,
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(raw),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(raw),
            "differential_overlay_current_group_descriptors": overlay_ledger,
            "differential_overlay_current_group_descriptors_sha256": CURRENT._canonical_digest(overlay_ledger),
            "selected_current_group_descriptors": selected_ledger,
            "selected_current_group_descriptors_sha256": CURRENT._canonical_digest(selected_ledger),
            "review_scope": CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE,
            "response_semantic_ledger_sha256": CURRENT._canonical_digest(
                CURRENT._selected_semantic_judgment_ledger({selected_key: selected_response})
            ),
        }
        sidecar_items = {selected_key: selected_response, overlay_key: overlay_response}
        composition_metadata = {
            "schema": CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA,
            "policy_version": CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_POLICY_VERSION,
            "historical_raw_audit_path": "audit/source_record_audit.json",
            "historical_raw_audit_sha256": raw["source_record_audit_sha256"],
            # This intentionally need not equal the archived copy used below.
            "historical_raw_audit_file_sha256": "1" * 64,
            "selected_current_sidecar_path": "audit/source_record_match_llm.json",
            "selected_current_sidecar_sha256": "2" * 64,
            "differential_overlay_path": "audit/overlay.json",
            "differential_overlay_archive_path": "audit/overlay.json",
            "differential_overlay_sha256": overlay_sha,
            "differential_overlay_current_group_descriptors": overlay_ledger,
            "selected_current_group_descriptors": selected_ledger,
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(raw),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(raw),
            "response_semantic_ledger_sha256": CURRENT._canonical_digest(
                CURRENT._semantic_judgment_ledger(sidecar_items)
            ),
        }
        composed = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": raw["source_record_audit_sha256"],
            "validator": selected_attestation["reviewer"],
            "validated_at": selected_attestation["validated_at"],
            "items": sidecar_items,
            CURRENT.SELECTED_CURRENT_REVALIDATION_FIELD: selected_metadata,
            CURRENT.AUTHENTICATED_EVIDENCE_COMPOSITION_FIELD: composition_metadata,
        }
        composed_path = audit / "composed_sidecar.json"
        _write(composed_path, composed)
        composed_sha = hashlib.sha256(composed_path.read_bytes()).hexdigest()

        selected_multiset = tuple(sorted(selected_ledger.values()))
        overlay_multiset = tuple(sorted(overlay_ledger.values()))
        complete_multiset = tuple(sorted(descriptors.values()))
        parent_composition = {
            "schema": COMPOSITION.COMPOSITION_SCHEMA,
            "policy_version": COMPOSITION.COMPOSITION_POLICY_VERSION,
            "archived_raw_replay_mode": COMPOSITION.ARCHIVED_RAW_REPLAY_MODE,
            "selected_sidecar_replay_mode": COMPOSITION.SELECTED_SIDECAR_REPLAY_MODE,
            "archived_raw_audit": {
                "path": "audit/source_record_audit.archived.json",
                "file_sha256": hashlib.sha256(raw_path.read_bytes()).hexdigest(),
                "source_record_audit_sha256": raw["source_record_audit_sha256"],
                "source_record_audit_integrity_sha256": raw[
                    "source_record_audit_integrity_sha256"
                ],
            },
            "composed_sidecar": {
                "path": "audit/composed_sidecar.json",
                "file_sha256": composed_sha,
            },
            "selected_attestation": {
                "path": "audit/selected_attestation.json",
                "file_sha256": selected_attestation_sha,
            },
            "base_sidecar": {"path": "audit/base_sidecar.json", "file_sha256": base_sha},
            "differential_overlay": {"path": "audit/overlay.json", "file_sha256": overlay_sha},
            "reported_historical_raw_audit_file_sha256": composition_metadata[
                "historical_raw_audit_file_sha256"
            ],
            "reported_selected_current_sidecar_sha256": composition_metadata[
                "selected_current_sidecar_sha256"
            ],
            "selected_descriptor_count": len(selected_multiset),
            "overlay_descriptor_count": len(overlay_multiset),
            "complete_descriptor_count": len(complete_multiset),
            "selected_descriptor_multiset_sha256": COMPOSITION.descriptor_multiset_sha256(
                selected_ledger
            ),
            "overlay_descriptor_multiset_sha256": COMPOSITION.descriptor_multiset_sha256(
                overlay_ledger
            ),
            "complete_descriptor_multiset_sha256": COMPOSITION._canonical_digest(
                list(complete_multiset)
            ),
            "full_response_semantic_ledger_sha256": composition_metadata[
                "response_semantic_ledger_sha256"
            ],
        }
        parent = {
            "schema": COMPOSITION.SCHEMA,
            "artifact_kind": COMPOSITION.ARTIFACT_KIND,
            "policy_version": COMPOSITION.POLICY_VERSION,
            "paper": PAPER,
            FORMALIZATION_REVIEW_PROTOCOL_FIELD: formalization_review_protocol_digest(),
            "review_scope": COMPOSITION.REVIEW_SCOPE,
            "scope": COMPOSITION.SEMANTIC_SCOPE,
            "reviewed_current_semantics": True,
            "reviewer": "new full-composition reviewer",
            "validated_at": "2026-08-14T00:00:00Z",
            "review_notes": "The complete archived selected-plus-overlay ledger was replayed.",
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(raw),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(raw),
            "prior_judgment_sidecar_path": "audit/composed_sidecar.json",
            "prior_judgment_sidecar_sha256": composed_sha,
            COMPOSITION.COMPOSITION_FIELD: parent_composition,
        }
        COMPOSITION.stamp_historical_composition_attestation(parent)
        parent_path = audit / "parent_attestation.json"
        _write(parent_path, parent)
        return {
            "paper_dir": paper_dir,
            "raw": raw,
            "raw_path": raw_path,
            "composed": composed,
            "composed_path": composed_path,
            "parent": parent,
            "parent_path": parent_path,
            "loaded_overlay": loaded_overlay,
            "descriptors": descriptors,
        }

    def _validate(
        self,
        fixture: dict[str, object],
        *,
        loader_calls: list[tuple[tuple[object, ...], dict[str, object]]] | None = None,
        projection_calls: list[tuple[tuple[object, ...], dict[str, object]]] | None = None,
    ) -> COMPOSITION.ValidatedHistoricalCompositionAttestation:
        paper_dir = fixture["paper_dir"]
        raw = fixture["raw"]
        raw_path = fixture["raw_path"]
        composed = fixture["composed"]
        composed_path = fixture["composed_path"]
        parent = fixture["parent"]
        parent_path = fixture["parent_path"]
        loaded_overlay = fixture["loaded_overlay"]
        assert isinstance(paper_dir, Path)
        assert isinstance(raw, dict)
        assert isinstance(raw_path, Path)
        assert isinstance(composed, dict)
        assert isinstance(composed_path, Path)
        assert isinstance(parent, dict)
        assert isinstance(parent_path, Path)
        assert isinstance(loaded_overlay, dict)
        def load_overlay(*args: object, **kwargs: object) -> dict[str, object]:
            if loader_calls is not None:
                loader_calls.append((args, kwargs))
            return loaded_overlay

        def reproject(*args: object, **kwargs: object) -> None:
            if projection_calls is not None:
                projection_calls.append((args, kwargs))

        with (
            patch.object(
                COMPOSITION.CURRENT,
                "_reproject_current_generated_association_credentials",
                side_effect=reproject,
            ),
            patch.object(
                COMPOSITION.DIFFERENTIAL,
                "load_current_source_record_differential_revalidation_items",
                side_effect=load_overlay,
            ),
            patch.object(COMPOSITION.CURRENT, "_target_disposition_errors", return_value=[]),
            patch.object(COMPOSITION.CURRENT, "_boundary_classification_errors", return_value=[]),
        ):
            return COMPOSITION.validate_historical_composition_attestation(
                paper=PAPER,
                paper_dir=paper_dir,
                archived_raw_audit=raw,
                archived_raw_audit_path=raw_path,
                composed_sidecar=composed,
                composed_sidecar_path=composed_path,
                parent_attestation=parent,
                parent_attestation_path=parent_path,
            )

    def test_overlay_loader_uses_historical_raw_logical_provenance(self) -> None:
        fixture = self._fixture()
        calls: list[tuple[tuple[object, ...], dict[str, object]]] = []
        self._validate(fixture, loader_calls=calls)
        self.assertEqual(len(calls), 1)
        _args, kwargs = calls[0]
        paper_dir = fixture["paper_dir"]
        assert isinstance(paper_dir, Path)
        self.assertEqual(
            kwargs["current_raw_audit_provenance_path"],
            paper_dir / "audit/source_record_audit.json",
        )

    def test_selected_replay_never_falls_back_to_live_statement_map(self) -> None:
        fixture = self._fixture()
        calls: list[tuple[tuple[object, ...], dict[str, object]]] = []
        self._validate(fixture, projection_calls=calls)
        self.assertEqual(len(calls), 1)
        _args, kwargs = calls[0]
        # This fixture has no archived-map snapshot.  Passing explicit None is
        # intentional: it proves the replay does not silently load a live map.
        self.assertIn("source_target_statement_map", kwargs)
        self.assertIsNone(kwargs["source_target_statement_map"])

    def test_archived_statement_map_snapshot_is_byte_pinned_to_raw_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / PAPER
            audit = paper_dir / "audit"
            audit.mkdir(parents=True)
            snapshot = {"schema": 1, "paper": PAPER, "items": {}}
            snapshot_path = audit / "paper_statement_map.archived.json"
            _write(snapshot_path, snapshot)
            digest = hashlib.sha256(snapshot_path.read_bytes()).hexdigest()
            loaded = COMPOSITION._archived_statement_map_snapshot(
                {
                    "archived_statement_map": {
                        "path": "audit/paper_statement_map.archived.json",
                        "file_sha256": digest,
                        "paper_statement_map_sha256": digest,
                    }
                },
                raw_audit={"paper_statement_map_sha256": digest},
                paper=PAPER,
                paper_dir=paper_dir,
            )
            self.assertEqual(loaded, snapshot)
            with self.assertRaisesRegex(
                COMPOSITION.SourceRecordHistoricalCompositionAttestationError,
                "do not match",
            ):
                COMPOSITION._archived_statement_map_snapshot(
                    {
                        "archived_statement_map": {
                            "path": "audit/paper_statement_map.archived.json",
                            "file_sha256": "0" * 64,
                            "paper_statement_map_sha256": digest,
                        }
                    },
                    raw_audit={"paper_statement_map_sha256": digest},
                    paper=PAPER,
                    paper_dir=paper_dir,
                )

    def test_replays_complete_duplicate_descriptor_multiset(self) -> None:
        fixture = self._fixture(duplicate_descriptors=True)
        result = self._validate(fixture)
        self.assertEqual(len(result.selected_descriptor_multiset), 1)
        self.assertEqual(len(result.overlay_descriptor_multiset), 1)
        self.assertEqual(len(result.complete_descriptor_multiset), 2)
        self.assertEqual(len(set(result.complete_descriptor_multiset)), 1)
        self.assertEqual(
            result.normalized_full_attestation["scope"], COMPOSITION.SEMANTIC_SCOPE
        )
        self.assertEqual(
            result.normalized_full_attestation["artifact_kind"],
            "source_record_current_semantic_revalidation_attestation",
        )
        raw = fixture["raw"]
        assert isinstance(raw, dict)
        self.assertEqual(
            REBIND._prior_attestation_error(
                result.normalized_full_attestation,
                paper=PAPER,
                prior_raw=raw,
            ),
            "",
        )

    def test_storage_key_renames_do_not_change_semantic_replay(self) -> None:
        first = self._fixture(
            selected_key="first_incidental_storage_key",
            overlay_key="second_incidental_storage_key",
        )
        second = self._fixture(
            selected_key="renamed_selected_storage_key",
            overlay_key="renamed_overlay_storage_key",
        )
        first_result = self._validate(first)
        second_result = self._validate(second)
        self.assertEqual(
            first_result.complete_descriptor_multiset,
            second_result.complete_descriptor_multiset,
        )

    def test_navigation_names_do_not_match_obligations(self) -> None:
        first = self._fixture(
            selected_key="first_storage_address",
            overlay_key="second_storage_address",
            qualified_declaration=f"{PAPER}.PaperInterface.oldPresentationName",
        )
        second = self._fixture(
            selected_key="renamed_first_storage_address",
            overlay_key="renamed_second_storage_address",
            qualified_declaration=f"{PAPER}.PaperInterface.newPresentationName",
        )
        first_result = self._validate(first)
        second_result = self._validate(second)
        self.assertEqual(
            first_result.complete_descriptor_multiset,
            second_result.complete_descriptor_multiset,
        )

    def test_rejects_stale_parent_protocol_receipt(self) -> None:
        fixture = self._fixture()
        parent = fixture["parent"]
        parent_path = fixture["parent_path"]
        assert isinstance(parent, dict)
        assert isinstance(parent_path, Path)
        parent[FORMALIZATION_REVIEW_PROTOCOL_FIELD] = "0" * 64
        COMPOSITION.stamp_historical_composition_attestation(parent)
        _write(parent_path, parent)
        with self.assertRaisesRegex(
            COMPOSITION.SourceRecordHistoricalCompositionAttestationError,
            "current review-protocol",
        ):
            self._validate(fixture)

    def test_rejects_stale_complete_descriptor_multiset_receipt(self) -> None:
        fixture = self._fixture()
        parent = fixture["parent"]
        parent_path = fixture["parent_path"]
        assert isinstance(parent, dict)
        assert isinstance(parent_path, Path)
        composition = parent[COMPOSITION.COMPOSITION_FIELD]
        assert isinstance(composition, dict)
        composition["complete_descriptor_count"] = 1
        COMPOSITION.stamp_historical_composition_attestation(parent)
        _write(parent_path, parent)
        with self.assertRaisesRegex(
            COMPOSITION.SourceRecordHistoricalCompositionAttestationError,
            "complete_descriptor_count",
        ):
            self._validate(fixture)

    def test_rejects_overlay_response_not_replayed_from_authenticated_loader(self) -> None:
        fixture = self._fixture()
        loaded_overlay = fixture["loaded_overlay"]
        assert isinstance(loaded_overlay, dict)
        tampered_overlay = copy.deepcopy(loaded_overlay)
        only = next(iter(tampered_overlay.values()))
        assert isinstance(only, dict)
        only["reason"] = "different semantic response"
        fixture["loaded_overlay"] = tampered_overlay
        with self.assertRaisesRegex(
            COMPOSITION.SourceRecordHistoricalCompositionAttestationError,
            "no longer replays",
        ):
            self._validate(fixture)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
