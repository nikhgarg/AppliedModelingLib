#!/usr/bin/env python3
"""Focused fail-closed tests for v11 correspondence receipt refreshes."""

from __future__ import annotations

import copy
import hashlib
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import audit_repository as repository  # noqa: E402
from scripts import refresh_source_spec_correspondence as refresh  # noqa: E402
from scripts.source_record_semantic_reuse import (  # noqa: E402
    CurrentSemanticReuseAuthority,
)


def digest(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def legacy_evidence_state(
    *,
    audit_payload: object,
    authority: object = None,
    identity_context: object = None,
    identity_error: str = "",
    pair_projection: object = None,
) -> SimpleNamespace:
    """Build the one typed legacy lane used by correspondence fixtures."""

    return SimpleNamespace(
        inputs=SimpleNamespace(
            audit_snapshot=SimpleNamespace(payload=audit_payload),
        ),
        semantic_reuse_authority=authority,
        source_record_identity_context=identity_context,
        source_record_identity_error=identity_error,
        semantic_contract_revalidation=pair_projection,
    )


def atom() -> dict[str, str]:
    return {
        "id": "source_clause",
        "source_locator": "source.txt:1",
        "source_quote_sha256": digest("Theorem. Fixture result."),
        "semantic_claim": "Every admissible input has the displayed fixture outcome.",
        "reviewed_lean_route": "Fixture.Proof",
    }


def item() -> dict[str, object]:
    return {
        "claim_bearing": True,
        "source_kind": "theorem",
        "semantic_contract": {
            "spec_declaration": "Fixture.SourceSpec",
            "evidence_declaration": "Fixture.Proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
        "source_claim_atoms": [atom()],
    }


def authority_row() -> dict[str, object]:
    return {
        "qualified_declaration": "Fixture.SourceSpec",
        "elaborated_signature_sha256": digest("signature"),
        "semantic_dependency_sha256": digest("dependency"),
        "elaborated_proposition_graph_sha256": digest("graph"),
        "review_alias_expansion": {
            "complete": True,
            "structural_alpha_normalized_equal": True,
            "reviewed_declaration": "Fixture.SourceSpec",
            "effective_declaration": "Fixture.Proof",
            "source_items": ["source_claim"],
        },
    }


def closure(
    *,
    closure_label: str,
    surface_label: str,
    nodes: list[dict[str, object]] | None = None,
    failures: list[dict[str, str]] | None = None,
) -> dict[str, object]:
    return {
        "sha256": digest(closure_label),
        "surface_sha256": digest(surface_label),
        "closure_module_context_sha256": digest("context-" + closure_label),
        "surface_mode": "terminal_fallback" if failures else "closure_expanded",
        "surface": {
            "binder_domains": [],
            "body": {
                "tag": "app",
                "fn": {"tag": "const", "origin": "foundation"},
                "arg": {"tag": "lit", "value": "0"},
            },
        },
        "nodes": nodes or [],
        "failures": failures or [],
    }


def correspondence(
    source_item: dict[str, object], current: dict[str, object], *, dispositions: list[dict[str, object]] | None = None) -> dict[str, object]:
    atoms = source_item["source_claim_atoms"]
    assert isinstance(atoms, list)
    atom_sha = integrity.source_claim_atom_semantic_sha256(atoms[0])
    record: dict[str, object] = {
        "schema": 1,
        "source_atoms_sha256": integrity.source_claim_atoms_semantic_sha256(atoms),
        "spec_closure_sha256": current["sha256"],
        "spec_surface_sha256": current["surface_sha256"],
        "closure_environment_sha256": current["closure_module_context_sha256"],
        "source_atom_bindings": [
            {
                "source_atom_sha256": atom_sha,
                "spec_component_sha256s": [current["surface_sha256"]],
                "semantic_bridge": "The complete canonical Spec surface represents the fixture source clause.",
            }
        ],
        "closure_node_dispositions": dispositions or [],
    }
    record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
        source_item["semantic_contract"], record
    )
    return record


def workspace_node(label: str) -> dict[str, object]:
    return {
        "structural_path": "body/fn",
        "node_role": "terminal",
        "origin_class": "workspace",
        "canonical_identity": {
            "tag": "declaration",
            "declaration_type_hash": digest("type-" + label),
        },
        "pinned_declaration_identity_sha256": digest("pin-" + label),
    }


def disposition_for(node: dict[str, object], source_item: dict[str, object]) -> dict[str, object]:
    atoms = source_item["source_claim_atoms"]
    assert isinstance(atoms, list)
    return {
        "closure_component_sha256": repository.semantic_contract_closure_node_component_sha256(node),
        "source_atom_sha256": integrity.source_claim_atom_semantic_sha256(atoms[0]),
        "semantic_basis": {
            "artifact_path": "source.txt",
            "artifact_sha256": digest("source artifact"),
            "source_locator": "source.txt:1",
            "semantic_statement": "The source clause explicitly supplies the fixture terminal meaning.",
        },
        "pinned_declaration_identity_sha256": node[
            "pinned_declaration_identity_sha256"
        ],
    }


class SourceSpecCorrespondenceRefreshTests(unittest.TestCase):
    def test_refresh_updates_only_derived_receipt_fields_when_mapping_survives(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="same")
        current = closure(closure_label="current", surface_label="same")
        record = correspondence(source_item, old)
        # A malformed derived aggregate must be recomputed, not treated as a
        # source-mapping change when all individual atom bindings still match.
        record["source_atoms_sha256"] = digest("stale aggregate")
        record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
            source_item["semantic_contract"], record
        )
        source_item["source_spec_correspondence"] = record
        original = copy.deepcopy(record)

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertEqual(errors, [])
        assert candidate is not None
        updated = candidate.correspondence
        changed_fields = {
            key for key in set(updated) | set(original) if updated.get(key) != original.get(key)
        }
        self.assertTrue(changed_fields)
        self.assertTrue(changed_fields <= refresh.DERIVED_RECEIPT_FIELDS)
        self.assertEqual(updated["source_atom_bindings"], original["source_atom_bindings"])
        self.assertEqual(
            updated["closure_node_dispositions"], original["closure_node_dispositions"]
        )
        self.assertEqual(updated["spec_closure_sha256"], current["sha256"])
        self.assertEqual(
            updated["closure_environment_sha256"], current["closure_module_context_sha256"]
        )
        self.assertEqual(
            updated["item_identity_sha256"],
            integrity.source_spec_correspondence_item_identity_sha256(
                source_item["semantic_contract"], updated
            ),
        )
        proposed = copy.deepcopy(source_item)
        proposed["source_spec_correspondence"] = updated
        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(proposed, current), []
        )

    def test_refresh_refuses_a_changed_bound_spec_component(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("absent from the current canonical surface" in error for error in errors),
            errors,
        )

    def test_refresh_rebinds_only_a_whole_surface_root_after_direct_review(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        original = copy.deepcopy(source_item["source_spec_correspondence"])

        candidate, errors = refresh.refresh_existing_correspondence(
            source_item,
            current,
            allow_whole_surface_rebind=True,
        )

        self.assertEqual(errors, [])
        assert candidate is not None
        updated = candidate.correspondence
        self.assertEqual(
            updated["source_atom_bindings"][0]["spec_component_sha256s"],
            [current["surface_sha256"]],
        )
        self.assertEqual(
            updated["source_atom_bindings"][0]["semantic_bridge"],
            original["source_atom_bindings"][0]["semantic_bridge"],
        )
        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(
                {**source_item, "source_spec_correspondence": updated}, current
            ),
            [],
        )

    def test_direct_review_rebinds_only_an_exact_quote_atom_identity_upgrade(
        self,
    ) -> None:
        source_item = item()
        current = closure(closure_label="same", surface_label="same")
        source_item["source_spec_correspondence"] = correspondence(
            source_item, current
        )
        original = copy.deepcopy(source_item["source_spec_correspondence"])
        raw_atoms = source_item["source_claim_atoms"]
        assert isinstance(raw_atoms, list) and isinstance(raw_atoms[0], dict)
        raw_atoms[0]["identity_schema"] = 2

        rejected, rejected_errors = refresh.refresh_existing_correspondence(
            source_item, current
        )
        candidate, errors = refresh.refresh_existing_correspondence(
            source_item,
            current,
            allow_whole_surface_rebind=True,
        )

        self.assertIsNone(rejected)
        self.assertTrue(rejected_errors)
        self.assertEqual(errors, [])
        assert candidate is not None
        updated = candidate.correspondence
        self.assertEqual(
            updated["source_atom_bindings"][0]["source_atom_sha256"],
            integrity.source_claim_atom_semantic_sha256(raw_atoms[0]),
        )
        self.assertEqual(
            updated["source_atom_bindings"][0]["semantic_bridge"],
            original["source_atom_bindings"][0]["semantic_bridge"],
        )
        self.assertEqual(
            updated["source_atom_bindings"][0]["spec_component_sha256s"],
            original["source_atom_bindings"][0]["spec_component_sha256s"],
        )
        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(
                {**source_item, "source_spec_correspondence": updated}, current
            ),
            [],
        )

    def test_exact_quote_upgrade_rebinds_a_preserved_terminal_disposition(self) -> None:
        source_item = item()
        node = workspace_node("same")
        current = closure(
            closure_label="same",
            surface_label="same",
            nodes=[node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Fixture.Terminal",
                }
            ],
        )
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            current,
            dispositions=[disposition_for(node, source_item)],
        )
        original = copy.deepcopy(source_item["source_spec_correspondence"])
        raw_atoms = source_item["source_claim_atoms"]
        assert isinstance(raw_atoms, list) and isinstance(raw_atoms[0], dict)
        raw_atoms[0]["identity_schema"] = 2

        candidate, errors = refresh.refresh_existing_correspondence(
            source_item,
            current,
            allow_whole_surface_rebind=True,
        )

        self.assertEqual(errors, [])
        assert candidate is not None
        updated = candidate.correspondence
        self.assertEqual(
            updated["closure_node_dispositions"][0]["source_atom_sha256"],
            integrity.source_claim_atom_semantic_sha256(raw_atoms[0]),
        )
        for field in (
            "semantic_basis",
            "closure_component_sha256",
            "pinned_declaration_identity_sha256",
        ):
            self.assertEqual(
                updated["closure_node_dispositions"][0][field],
                original["closure_node_dispositions"][0][field],
            )

    def test_review_authority_does_not_rebind_a_selected_subcomponent(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        record = correspondence(source_item, old)
        record["source_atom_bindings"][0]["spec_component_sha256s"] = [
            digest("selected-subcomponent")
        ]
        record["item_identity_sha256"] = (
            integrity.source_spec_correspondence_item_identity_sha256(
                source_item["semantic_contract"], record
            )
        )
        source_item["source_spec_correspondence"] = record

        candidate, errors = refresh.refresh_existing_correspondence(
            source_item,
            current,
            allow_whole_surface_rebind=True,
        )

        self.assertIsNone(candidate)
        self.assertTrue(
            any("absent from the current canonical surface" in error for error in errors),
            errors,
        )

    def test_refresh_refuses_a_changed_material_terminal_disposition(self) -> None:
        source_item = item()
        old_node = workspace_node("old")
        old = closure(
            closure_label="old",
            surface_label="same",
            nodes=[old_node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Fixture.OldTerminal",
                }
            ],
        )
        current_node = workspace_node("new")
        current = closure(
            closure_label="current",
            surface_label="same",
            nodes=[current_node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Fixture.NewTerminal",
                }
            ],
        )
        source_item["source_spec_correspondence"] = correspondence(
            source_item, old, dispositions=[disposition_for(old_node, source_item)]
        )

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("material closure node" in error for error in errors), errors
        )

    def test_refresh_never_synthesizes_a_missing_correspondence_record(self) -> None:
        source_item = item()
        current = closure(closure_label="current", surface_label="same")

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertEqual(errors, ["no established source_spec_correspondence record to refresh"])

    def test_refresh_refuses_a_changed_theorem_to_spec_relationship(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="same")
        current = closure(closure_label="current", surface_label="same")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        source_item["semantic_contract"] = dict(source_item["semantic_contract"])
        source_item["semantic_contract"]["evidence_mode"] = "refutes"

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("changed evidence relationship" in error for error in errors), errors
        )

    def test_map_refresh_is_all_or_nothing_after_one_semantic_mapping_refusal(self) -> None:
        accepted = item()
        accepted_old = closure(closure_label="accepted-old", surface_label="shared")
        accepted_current = closure(closure_label="accepted-current", surface_label="shared")
        accepted["source_spec_correspondence"] = correspondence(accepted, accepted_old)
        rejected = item()
        rejected["semantic_contract"] = dict(rejected["semantic_contract"])
        rejected["semantic_contract"]["spec_declaration"] = "Fixture.OtherSpec"
        rejected_old = closure(closure_label="rejected-old", surface_label="old")
        rejected_current = closure(closure_label="rejected-current", surface_label="new")
        rejected["source_spec_correspondence"] = correspondence(rejected, rejected_old)
        payload: dict[str, object] = {
            "source_spec_correspondence_schema": 1,
            "items": {"accepted_navigation_key": accepted, "rejected_navigation_key": rejected},
        }

        updated, refreshed, skipped, errors = refresh.refreshed_payload(
            payload,
            {
                "Fixture.SourceSpec": accepted_current,
                "Fixture.OtherSpec": rejected_current,
            },
        )

        self.assertIsNone(updated)
        self.assertEqual(refreshed, [])
        self.assertEqual(skipped, [])
        self.assertTrue(any("rejected_navigation_key" in error for error in errors), errors)

    def test_preflight_identifies_only_safe_hash_refreshes(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="same")
        current = closure(closure_label="current", surface_label="same")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }

        with mock.patch.object(
            refresh,
            "current_lean_closures",
            return_value=({"Fixture.SourceSpec": current}, []),
        ):
            preflight = refresh.source_spec_correspondence_refresh_preflight(
                ROOT, ROOT / "papers" / "Fixture", payload=payload
            )

        self.assertEqual(preflight["state"], "refresh_required")
        self.assertTrue(preflight["safe_refresh"])
        self.assertFalse(preflight["current"])
        self.assertEqual(preflight["refreshed_items"], ["source_claim"])
        self.assertFalse(preflight["acceptance_credential"])

    def test_preflight_blocks_changed_semantic_mapping(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }

        with mock.patch.object(
            refresh,
            "current_lean_closures",
            return_value=({"Fixture.SourceSpec": current}, []),
        ):
            preflight = refresh.source_spec_correspondence_refresh_preflight(
                ROOT, ROOT / "papers" / "Fixture", payload=payload
            )

        self.assertEqual(preflight["state"], "blocked")
        self.assertFalse(preflight["safe_refresh"])
        self.assertTrue(preflight["errors"])

    def test_preflight_accepts_reviewed_whole_surface_root_rebind(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }

        with mock.patch.object(
            refresh,
            "current_lean_closures",
            return_value=({"Fixture.SourceSpec": current}, []),
        ):
            preflight = refresh.source_spec_correspondence_refresh_preflight(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload=payload,
                whole_surface_rebind_authorized=True,
            )

        self.assertEqual(preflight["state"], "refresh_required")
        self.assertTrue(preflight["safe_refresh"])
        self.assertEqual(preflight["refreshed_items"], ["source_claim"])

    def test_preflight_reuses_builder_issued_current_semantic_authority(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        row = authority_row()
        map_sha256 = digest("current-map")
        authority = CurrentSemanticReuseAuthority(
            paper="Fixture",
            raw_audit_file_sha256=digest("raw"),
            semantic_identity_sha256=digest("semantic"),
            reviewed_declarations=("Fixture.SourceSpec",),
            watched_repository_material=(
                (
                    "papers/Fixture/audit/paper_statement_map.json",
                    "present",
                    map_sha256,
                ),
            ),
            result={"current": True},
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = map_sha256
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": [row]},
                authority=authority,
            )

        with (
            mock.patch.object(
                refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
            ),
            mock.patch.object(refresh, "current_lean_closures") as lean_closures,
        ):
            preflight = refresh.source_spec_correspondence_refresh_preflight(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload=payload,
                evidence_context=FakeEvidenceContext(),
            )

        self.assertEqual(preflight["state"], "current_semantic_authority")
        self.assertTrue(preflight["current"])
        self.assertFalse(preflight["safe_refresh"])
        self.assertEqual(preflight["errors"], [])
        lean_closures.assert_not_called()

    def test_fresh_v11_graph_needs_no_second_correspondence_worksheet(self) -> None:
        payload = {"items": {"source_claim": item()}}
        graph_receipt = {
            "source_claim": {
                "authority": "v11_graph_native_v1",
                "source_item_key": "source_claim",
                "spec_declaration": "Fixture.SourceSpec",
                "evidence_declaration": "Fixture.Proof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
                "source_atoms_sha256": digest("atoms"),
                "item_identity_sha256": digest("identity"),
                "spec_closure_sha256": digest("closure"),
                "spec_surface_sha256": digest("surface"),
                "closure_environment_sha256": digest("environment"),
            }
        }
        with (
            mock.patch.object(
                refresh.integrity,
                "graph_native_source_spec_realization_receipts",
                return_value=(graph_receipt, []),
            ),
            mock.patch.object(refresh, "current_lean_closures") as lean_closures,
        ):
            preflight = refresh.source_spec_correspondence_refresh_preflight(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload=payload,
                evidence_context=object(),
            )

        self.assertEqual(preflight["state"], "current_graph_authority")
        self.assertTrue(preflight["current"])
        self.assertEqual(preflight["graph_native_items"], ["source_claim"])
        self.assertEqual(preflight["errors"], [])
        lean_closures.assert_not_called()

    def test_semantic_authority_rejects_changed_correspondence_atoms(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        source_item["source_claim_atoms"] = [
            {**atom(), "semantic_claim": "A changed source meaning."}
        ]
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        map_sha256 = digest("current-map")
        authority = CurrentSemanticReuseAuthority(
            paper="Fixture",
            raw_audit_file_sha256=digest("raw"),
            semantic_identity_sha256=digest("semantic"),
            reviewed_declarations=("Fixture.SourceSpec",),
            watched_repository_material=(
                (
                    "papers/Fixture/audit/paper_statement_map.json",
                    "present",
                    map_sha256,
                ),
            ),
            result={"current": True},
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = map_sha256
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": [authority_row()]},
                authority=authority,
            )

        with mock.patch.object(
            refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
        ):
            errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertIsNotNone(errors)
        self.assertTrue(any("source atoms changed" in error for error in errors or []))

    def test_semantic_authority_falls_back_for_an_unauthenticated_pair(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        row = authority_row()
        alias = row["review_alias_expansion"]
        assert isinstance(alias, dict)
        alias["effective_declaration"] = "Fixture.DifferentProof"
        map_sha256 = digest("current-map")
        authority = CurrentSemanticReuseAuthority(
            paper="Fixture",
            raw_audit_file_sha256=digest("raw"),
            semantic_identity_sha256=digest("semantic"),
            reviewed_declarations=("Fixture.SourceSpec",),
            watched_repository_material=(
                (
                    "papers/Fixture/audit/paper_statement_map.json",
                    "present",
                    map_sha256,
                ),
            ),
            result={"current": True},
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = map_sha256
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": [row]},
                authority=authority,
            )

        with mock.patch.object(
            refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
        ):
            errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertIsNone(errors)

    def test_semantic_authority_accepts_an_authenticated_structural_pair(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        spec_row = authority_row()
        spec_row["review_alias_expansion"] = {
            "alias_present": False,
            "blocked_routes": [],
            "complete": True,
            "effective_declaration": "Fixture.SourceSpec",
            "effective_kind": "def",
            "reviewed_declaration": "Fixture.SourceSpec",
            "schema": 1,
            "steps": [],
        }
        proof_row = {
            **authority_row(),
            "qualified_declaration": "Fixture.Proof",
            "review_alias_expansion": {
                "alias_present": False,
                "blocked_routes": [],
                "complete": True,
                "effective_declaration": "Fixture.Proof",
                "effective_kind": "theorem",
                "reviewed_declaration": "Fixture.Proof",
                "schema": 1,
                "steps": [],
            },
        }
        map_sha256 = digest("current-map")
        authority = CurrentSemanticReuseAuthority(
            paper="Fixture",
            raw_audit_file_sha256=digest("raw"),
            semantic_identity_sha256=digest("semantic"),
            reviewed_declarations=("Fixture.Proof", "Fixture.SourceSpec"),
            watched_repository_material=(
                (
                    "papers/Fixture/audit/paper_statement_map.json",
                    "present",
                    map_sha256,
                ),
            ),
            result={"current": True},
        )
        companion_error = (
            "semantic-contract companion is not an exact transparent "
            "evidence/Spec structural pair: Fixture.Proof / Fixture.SourceSpec"
        )
        pair_projection = mock.Mock(
            suppressed_source_contract_association_errors=(companion_error,),
            suppressed_source_coverage_route_errors=(companion_error,),
            typed_route_reconciliation_sha256=digest("typed graph"),
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = map_sha256
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": [spec_row, proof_row]},
                authority=authority,
                pair_projection=pair_projection,
            )

        with (
            mock.patch.object(
                refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
            ),
            mock.patch.object(
                refresh.integrity,
                "_trusted_semantic_contract_revalidation_projection",
                return_value=pair_projection,
            ),
        ):
            errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertEqual(errors, [])

    def test_current_typed_graph_accepts_correspondence_without_optional_authority(
        self,
    ) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        companion_error = (
            "semantic-contract companion is not an exact transparent "
            "evidence/Spec structural pair: Fixture.Proof / Fixture.SourceSpec"
        )
        pair_projection = mock.Mock(
            suppressed_source_contract_association_errors=(companion_error,),
            suppressed_source_coverage_route_errors=(companion_error,),
            typed_route_reconciliation_sha256=digest("typed graph"),
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = digest("current-map")
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": []},
                identity_context=object(),
                pair_projection=pair_projection,
            )

        with (
            mock.patch.object(
                refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
            ),
            mock.patch.object(
                refresh.integrity,
                "_trusted_semantic_contract_revalidation_projection",
                return_value=pair_projection,
            ),
            mock.patch.object(
                refresh.integrity,
                "current_source_record_identity_context_error",
                return_value="",
            ) as identity_check,
        ):
            proof_pair_errors = (
                integrity.semantic_authority_source_spec_correspondence_errors(
                    ROOT,
                    ROOT / "papers" / "Fixture",
                    payload,
                    [("source_claim", source_item)],
                    evidence_context=FakeEvidenceContext(),
                )
            )
            errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertIsNone(proof_pair_errors)
        self.assertEqual(errors, [])
        identity_check.assert_called_once()

    def test_current_v11_graph_owns_correspondence_and_exact_proof_pair(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        graph_surface = mock.Mock(
            semantic_contracts={
                ("Fixture.SourceSpec", "Fixture.Proof", "proves"): {
                    "matches": True,
                    "evidence_is_unsafe": False,
                    "evidence_value_has_sorry": False,
                    "evidence_axiom_closure_checked": True,
                }
            },
            semantic_targets={"Fixture.SourceSpec": {}},
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            source_semantic_lane = (
                integrity.V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
            )
            statement_map = payload
            paper_statement_map_sha256 = digest("current-map")
            legacy_source_record_state = None

        with (
            mock.patch.object(
                refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
            ),
            mock.patch.object(
                refresh.integrity,
                "builder_issued_v11_lean_review_surface",
                return_value=graph_surface,
            ),
        ):
            proof_pair_errors = (
                integrity.semantic_authority_source_spec_correspondence_errors(
                    ROOT,
                    ROOT / "papers" / "Fixture",
                    payload,
                    [("source_claim", source_item)],
                    evidence_context=FakeEvidenceContext(),
                )
            )
            refresh_errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertEqual(proof_pair_errors, [])
        self.assertEqual(refresh_errors, [])

    def test_structural_pair_requires_both_authenticated_error_projections(self) -> None:
        source_item = item()
        source_item["source_spec_correspondence"] = correspondence(
            source_item,
            closure(closure_label="current", surface_label="current-surface"),
        )
        payload = {
            "source_spec_correspondence_schema": 1,
            "items": {"source_claim": source_item},
        }
        spec_row = authority_row()
        spec_row["review_alias_expansion"] = {
            "complete": True,
            "reviewed_declaration": "Fixture.SourceSpec",
            "effective_declaration": "Fixture.SourceSpec",
        }
        proof_row = {
            **authority_row(),
            "qualified_declaration": "Fixture.Proof",
        }
        map_sha256 = digest("current-map")
        authority = CurrentSemanticReuseAuthority(
            paper="Fixture",
            raw_audit_file_sha256=digest("raw"),
            semantic_identity_sha256=digest("semantic"),
            reviewed_declarations=("Fixture.Proof", "Fixture.SourceSpec"),
            watched_repository_material=(
                (
                    "papers/Fixture/audit/paper_statement_map.json",
                    "present",
                    map_sha256,
                ),
            ),
            result={"current": True},
        )
        companion_error = (
            "semantic-contract companion is not an exact transparent "
            "evidence/Spec structural pair: Fixture.Proof / Fixture.SourceSpec"
        )
        pair_projection = mock.Mock(
            suppressed_source_contract_association_errors=(companion_error,),
            suppressed_source_coverage_route_errors=(),
        )

        class FakeEvidenceContext:
            issued_by_builder = True
            folder = ROOT / "papers" / "Fixture"
            statement_map = payload
            paper_statement_map_sha256 = map_sha256
            legacy_source_record_state = legacy_evidence_state(
                audit_payload={"configured_review_rows": [spec_row, proof_row]},
                authority=authority,
                pair_projection=pair_projection,
            )

        with (
            mock.patch.object(
                refresh.integrity, "EvidenceRunContext", FakeEvidenceContext
            ),
            mock.patch.object(
                refresh.integrity,
                "_trusted_semantic_contract_revalidation_projection",
                return_value=pair_projection,
            ),
        ):
            errors = refresh._semantic_authority_correspondence_errors(
                ROOT,
                ROOT / "papers" / "Fixture",
                payload,
                [("source_claim", source_item)],
                evidence_context=FakeEvidenceContext(),
            )

        self.assertIsNone(errors)


if __name__ == "__main__":
    unittest.main()
