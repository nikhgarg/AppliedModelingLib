#!/usr/bin/env python3
"""Focused regression tests for authenticated item-level sidecar rebinds."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import source_record_semantic_rebind as REBIND  # noqa: E402
from scripts import (  # noqa: E402
    source_record_historical_association_snapshot_reconciliation as RECONCILIATION,
)
from scripts import source_record_obligation_groups as OBLIGATIONS  # noqa: E402
from scripts import (  # noqa: E402
    source_record_historical_composition_attestation as COMPOSITION,
)
from scripts.source_record_target_disposition import (  # noqa: E402
    semantic_association_record_digest,
    source_contract_association_record_digest,
    source_map_item_record_digest,
)
from scripts.source_record_integrity import (  # noqa: E402
    LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA,
    SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD,
    SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA,
    SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD,
    SOURCE_RECORD_AUDIT_SURFACE_FIELD,
    SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD,
    SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD,
    _source_record_legacy_prompt_integrity_sha256,
    source_record_audit_receipt_error,
    source_record_audit_surface_sha256,
    stamp_source_record_audit_receipts,
)


SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def _load_source_record_audit_helper() -> object:
    spec = importlib.util.spec_from_file_location(
        "semantic_rebind_source_record_audit_helper", SOURCE_RECORD_AUDIT_HELPER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def _sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _map_item(*, presentation_timestamp: str = "first") -> dict[str, object]:
    return {
        "statement": "A literal source theorem says P.",
        "source_location": "sources/paper.txt:10-12",
        "source_kind": "theorem",
        "coverage_status": "covered",
        "claim_bearing": True,
        "source_anchor_evidence": [
            {
                "path": "sources/paper.txt",
                "line_start": 10,
                "line_end": 12,
                "quoted_text": "Theorem A. P.",
                "quoted_text_sha256": _sha("Theorem A. P."),
            }
        ],
        "semantic_contract": {
            "evidence_declaration": "Fixture.Paper.evidence",
            "spec_declaration": "Fixture.Paper.spec",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
        # This direct field is explicitly administrative in the source-item
        # semantic projection, while it remains in the full map record digest.
        "source_presentation_reconciliation": {
            "schema": 1,
            "presentation_label": "Theorem A",
            "validated_at": presentation_timestamp,
        },
    }


def _association(
    item: dict[str, object], *, source_key: str, current: bool
) -> dict[str, object]:
    contract = copy.deepcopy(item["semantic_contract"])
    identity: dict[str, object] = {
        "source_key": source_key,
        "source_location": item["source_location"],
        "source_kind": item["source_kind"],
        "source_map_item_sha256": source_map_item_record_digest(item),
        "semantic_contract": contract,
    }
    signature = {
        "qualified_declaration": "Fixture.Paper.evidence",
        "elaborated_signature_sha256": "a" * 64,
    }
    if current:
        # The source semantic identity is a source-content, not map-key,
        # receipt.  It survives a presentation-only record metadata change.
        identity["source_semantic_sha256"] = REBIND.source_item_coverage_sha256(
            item, ""
        )
    association: dict[str, object] = {
        "schema": 2 if current else 1,
        "association_mode": "semantic_contract_group_member",
        "semantic_contract_member_role": "direct_evidence",
        "semantic_model_judgment_key": "semantic-model::storage-address-only",
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.Paper.evidence",
            "declaration_sha256": "b" * 64,
        },
        "source_item_identities": [identity],
    }
    if current:
        association["reviewed_elaborated_signature_identity"] = signature
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [str(identity["source_semantic_sha256"])], signature
        )
    association["association_sha256"] = source_contract_association_record_digest(
        association
    )
    return association


def _row(item: dict[str, object], *, source_key: str, current: bool) -> dict[str, object]:
    row: dict[str, object] = {
        "kind": "boundary_input",
        "judgment_key": "storage-address-is-not-a-match-key",
        "input": "hP",
        "lean_source_declaration": "theorem evidence (hP : P) : P := hP",
        "expanded_input_type": "P",
        "result_relation": "P",
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.Paper.evidence",
            "declaration_sha256": "b" * 64,
        },
        "source_contract_association": _association(
            item, source_key=source_key, current=current
        ),
    }
    if current:
        row.update(
            {
                "effective_lean_source_declaration": row["lean_source_declaration"],
                "effective_qualified_declaration": "Fixture.Paper.evidence",
                "review_alias_expansion": {
                    "schema": 1,
                    "reviewed_declaration": "Fixture.Paper.evidence",
                    "effective_declaration": "Fixture.Paper.evidence",
                    "effective_kind": "theorem",
                    "alias_present": False,
                    "complete": True,
                    "steps": [],
                    "blocked_routes": [],
                },
                "reviewed_elaborated_signature_identities": [
                    {
                        "qualified_declaration": "Fixture.Paper.evidence",
                        "elaborated_signature_sha256": "a" * 64,
                    }
                ],
            }
        )
    return row


def _generated_taxonomy() -> dict[str, object]:
    """Fixture for the closed v2 generated-classification compatibility set."""

    return {
        "proposition_sort": "true",
        "proposition_sort_evidence": "fixture_generated_sort",
        "theorem_facing_semantic_role": "proof_bearing",
        "semantic_restriction_role": "requires_source_or_lean_closure",
        "semantic_restriction_candidates": ["fixture_generated_candidate"],
        "structural_type_sha256": "f" * 64,
    }


class SemanticRebindDescriptorTests(unittest.TestCase):
    def _descriptor(
        self,
        prior_item: dict[str, object],
        current_item: dict[str, object],
        *,
        prior_key: str = "prior_key",
        current_key: str = "current_key",
    ) -> tuple[dict[str, object], dict[str, object]]:
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            prior, _ = REBIND._normalized_generated_item(
                _row(prior_item, source_key=prior_key, current=False),
                section="boundary_input_items",
                map_items={prior_key: prior_item},
                current=False,
            )
            current, _ = REBIND._normalized_generated_item(
                _row(current_item, source_key=current_key, current=True),
                section="boundary_input_items",
                map_items={current_key: current_item},
                current=True,
            )
        return prior, current

    def test_presentation_only_map_metadata_and_key_rename_are_semantically_equal(self) -> None:
        prior_item = _map_item(presentation_timestamp="first")
        current_item = _map_item(presentation_timestamp="refreshed")
        prior, current = self._descriptor(
            prior_item, current_item, prior_key="old_map_key", current_key="new_map_key"
        )
        self.assertEqual(
            REBIND._canonical_digest(prior), REBIND._canonical_digest(current)
        )

    def test_correspondence_refresh_does_not_reopen_source_premise_review(self) -> None:
        def correspondence(bridge: str, digest: str) -> dict[str, object]:
            return {
                "schema": 1,
                "source_atoms_sha256": digest,
                "spec_closure_sha256": "b" * 64,
                "spec_surface_sha256": "c" * 64,
                "closure_environment_sha256": "d" * 64,
                "item_identity_sha256": "e" * 64,
                "source_atom_bindings": [
                    {
                        "source_atom_sha256": "f" * 64,
                        "spec_component_sha256s": ["1" * 64],
                        "semantic_bridge": bridge,
                    }
                ],
                "closure_node_dispositions": [],
            }

        prior_item = _map_item()
        prior_item["source_spec_correspondence"] = correspondence(
            "Original exact source-to-Spec explanation.", "a" * 64
        )
        current_item = _map_item()
        current_item["source_spec_correspondence"] = correspondence(
            "Refreshed exact source-to-Spec explanation.", "9" * 64
        )
        prior, current = self._descriptor(prior_item, current_item)
        self.assertEqual(
            REBIND._canonical_digest(prior), REBIND._canonical_digest(current)
        )

        changed_source = copy.deepcopy(current_item)
        changed_source["statement"] = "A different literal source theorem says Q."
        _, changed = self._descriptor(prior_item, changed_source)
        self.assertNotEqual(
            REBIND._canonical_digest(prior), REBIND._canonical_digest(changed)
        )

        unknown_correspondence = copy.deepcopy(current_item)
        unknown = unknown_correspondence["source_spec_correspondence"]
        assert isinstance(unknown, dict)
        unknown["future_semantic_field"] = "fail closed"
        _, unknown_descriptor = self._descriptor(prior_item, unknown_correspondence)
        self.assertNotEqual(
            REBIND._canonical_digest(prior),
            REBIND._canonical_digest(unknown_descriptor),
        )

    def test_v2_generated_taxonomy_adapter_preserves_the_semantic_core(self) -> None:
        """Only the closed generated taxonomy may bridge legacy absence.

        The comparison still changes for either the expanded Lean proposition
        or source-route role.  It therefore cannot use a theorem name, a
        judgment key, or a taxonomy label as the matching identity.
        """

        prior_item = _map_item()
        current_item = _map_item()
        prior_row = _row(prior_item, source_key="prior_key", current=False)
        current_row = _row(current_item, source_key="current_key", current=True)
        prior_row["input"] = {"type": "P"}
        current_row["input"] = {"type": "P"}
        current_row.update(_generated_taxonomy())
        current_input = current_row["input"]
        assert isinstance(current_input, dict)
        current_input["input_origin"] = "instance_binder"

        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            prior, _ = REBIND._normalized_generated_item(
                prior_row,
                section="boundary_input_items",
                map_items={"prior_key": prior_item},
                current=False,
            )
            current, _ = REBIND._normalized_generated_item(
                current_row,
                section="boundary_input_items",
                map_items={"current_key": current_item},
                current=True,
            )
            legacy_current, _ = REBIND._normalized_generated_item(
                current_row,
                section="boundary_input_items",
                map_items={"current_key": current_item},
                current=True,
                generated_taxonomy_core_adapter=False,
            )
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(current))
        self.assertNotEqual(
            REBIND._canonical_digest(prior), REBIND._canonical_digest(legacy_current)
        )

        changed_surface = copy.deepcopy(current_row)
        changed_surface["expanded_input_type"] = "Q"
        changed_surface["result_relation"] = "Q"
        changed_route = copy.deepcopy(current_row)
        association = changed_route["source_contract_association"]
        assert isinstance(association, dict)
        association["semantic_contract_member_role"] = "different_route_role"
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            changed_surface_descriptor, _ = REBIND._normalized_generated_item(
                changed_surface,
                section="boundary_input_items",
                map_items={"current_key": current_item},
                current=True,
            )
            changed_route_descriptor, _ = REBIND._normalized_generated_item(
                changed_route,
                section="boundary_input_items",
                map_items={"current_key": current_item},
                current=True,
            )
        self.assertNotEqual(
            REBIND._canonical_digest(prior),
            REBIND._canonical_digest(changed_surface_descriptor),
        )
        self.assertNotEqual(
            REBIND._canonical_digest(prior),
            REBIND._canonical_digest(changed_route_descriptor),
        )

    def test_v2_generated_taxonomy_adapter_rejects_partial_or_unknown_surface(self) -> None:
        item = _map_item()
        row = _row(item, source_key="current_key", current=True)
        partial = _generated_taxonomy()
        partial.pop("structural_type_sha256")
        row.update(partial)
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "partial"):
                REBIND._normalized_generated_item(
                    row,
                    section="boundary_input_items",
                    map_items={"current_key": item},
                    current=True,
                )

        complete = _row(item, source_key="current_key", current=True)
        complete.update(_generated_taxonomy())
        complete["unrecognized_generated_surface"] = "not an adapter field"
        prior = _row(item, source_key="prior_key", current=False)
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            prior_descriptor, _ = REBIND._normalized_generated_item(
                prior,
                section="boundary_input_items",
                map_items={"prior_key": item},
                current=False,
            )
            complete_descriptor, _ = REBIND._normalized_generated_item(
                complete,
                section="boundary_input_items",
                map_items={"current_key": item},
                current=True,
            )
        self.assertNotEqual(
            REBIND._canonical_digest(prior_descriptor),
            REBIND._canonical_digest(complete_descriptor),
        )

    def test_declared_provenance_paths_require_local_byte_pins(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            audit = paper_dir / "audit"
            audit.mkdir(parents=True)
            payload = {
                "opaque_reference": {
                    "path": "audit/archive.json",
                    "file_sha256": "a" * 64,
                },
                # A source anchor is not a provenance file record merely
                # because it contains a path and a different digest kind.
                "source_anchor": {
                    "path": "sources/paper.txt",
                    "quoted_text_sha256": "b" * 64,
                },
            }
            self.assertEqual(
                REBIND.source_record_semantic_rebind_declared_provenance_paths(
                    payload,
                    paper_dir=paper_dir,
                ),
                ((audit / "archive.json").resolve(),),
            )
            with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "relative"):
                REBIND.source_record_semantic_rebind_declared_provenance_paths(
                    {
                        "path": "../outside.json",
                        "bytes_sha256": "c" * 64,
                    },
                    paper_dir=paper_dir,
                )
            with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "malformed"):
                REBIND.source_record_semantic_rebind_declared_provenance_paths(
                    {
                        "path": "audit/archive.json",
                        "file_sha256": "not-a-digest",
                    },
                    paper_dir=paper_dir,
                )

    def test_quote_semantic_contract_formula_and_unknown_map_changes_do_not_match(self) -> None:
        prior_item = _map_item()
        current_item = _map_item()
        prior, current = self._descriptor(prior_item, current_item)
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(current))

        changed_quote = copy.deepcopy(current_item)
        anchor = changed_quote["source_anchor_evidence"][0]
        assert isinstance(anchor, dict)
        anchor["quoted_text"] = "Theorem A. Q."
        anchor["quoted_text_sha256"] = _sha("Theorem A. Q.")
        prior, changed = self._descriptor(prior_item, changed_quote)
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed))
        renamed_route = copy.deepcopy(current_item)
        contract = renamed_route["semantic_contract"]
        assert isinstance(contract, dict)
        contract["spec_declaration"] = "Fixture.Paper.otherSpec"
        prior, changed = self._descriptor(prior_item, renamed_route)
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed))

        changed_contract = copy.deepcopy(current_item)
        contract = changed_contract["semantic_contract"]
        assert isinstance(contract, dict)
        contract["semantic_shape"] = "different_source_contract"
        prior, changed = self._descriptor(prior_item, changed_contract)
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed))

        changed_unknown = copy.deepcopy(current_item)
        changed_unknown["new_unclassified_source_metadata"] = "must fail closed"
        prior, changed = self._descriptor(prior_item, changed_unknown)
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed))

        changed_row = _row(current_item, source_key="current_key", current=True)
        changed_row["expanded_input_type"] = "Q"
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            changed, _ = REBIND._normalized_generated_item(
                changed_row,
                section="boundary_input_items",
                map_items={"current_key": current_item},
                current=True,
            )
        prior, _ = self._descriptor(prior_item, current_item)
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed))

    def test_lean_and_contract_fqn_renames_are_semantically_equal(self) -> None:
        """A theorem/helper spelling is not the identity of an obligation."""

        prior_item = _map_item()
        renamed_item = _map_item()
        contract = renamed_item["semantic_contract"]
        assert isinstance(contract, dict)
        contract["evidence_declaration"] = "Fixture.Renamed.renamedEvidence"
        contract["spec_declaration"] = "Fixture.Renamed.renamedSpec"

        prior_row = _row(prior_item, source_key="prior_key", current=False)
        renamed_row = _row(renamed_item, source_key="current_key", current=True)
        renamed_qualified = "Fixture.Renamed.renamedEvidence"
        renamed_row["lean_source_declaration"] = (
            "theorem renamedEvidence (hP : P) : P := hP"
        )
        renamed_row["effective_lean_source_declaration"] = renamed_row[
            "lean_source_declaration"
        ]
        renamed_row["effective_qualified_declaration"] = renamed_qualified
        identity = renamed_row["reviewed_declaration_identity"]
        assert isinstance(identity, dict)
        identity["qualified_declaration"] = renamed_qualified
        aliases = renamed_row["review_alias_expansion"]
        assert isinstance(aliases, dict)
        aliases["reviewed_declaration"] = renamed_qualified
        aliases["effective_declaration"] = renamed_qualified
        signatures = renamed_row["reviewed_elaborated_signature_identities"]
        assert isinstance(signatures, list) and len(signatures) == 1
        signature = signatures[0]
        assert isinstance(signature, dict)
        signature["qualified_declaration"] = renamed_qualified
        association = renamed_row["source_contract_association"]
        assert isinstance(association, dict)
        association_identity = association["reviewed_declaration_identity"]
        association_signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(association_identity, dict)
        assert isinstance(association_signature, dict)
        association_identity["qualified_declaration"] = renamed_qualified
        association_signature["qualified_declaration"] = renamed_qualified
        association["semantic_model_judgment_key"] = "semantic-model::renamedEvidence"
        source_identities = association["source_item_identities"]
        assert isinstance(source_identities, list) and len(source_identities) == 1
        source_identity = source_identities[0]
        assert isinstance(source_identity, dict)
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [str(source_identity["source_semantic_sha256"])], association_signature
        )
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )

        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            prior, _ = REBIND._normalized_generated_item(
                prior_row,
                section="boundary_input_items",
                map_items={"prior_key": prior_item},
                current=False,
            )
            renamed, _ = REBIND._normalized_generated_item(
                renamed_row,
                section="boundary_input_items",
                map_items={"current_key": renamed_item},
                current=True,
            )
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(renamed))

    def test_complete_proposition_alias_routes_ignore_fqns_and_locations(self) -> None:
        """Expanded alias routes use the same name-free complete projection."""

        prior_item = _map_item()
        current_item = _map_item()
        prior_row = _row(prior_item, source_key="prior_key", current=False)
        current_row = _row(current_item, source_key="current_key", current=True)

        def alias_route(
            declaration: str, source_file: str, line: int, *, expanded: str = "P", blocked: list[str] | None = None
        ) -> dict[str, object]:
            return {
                "expanded_type": expanded,
                "transparent_steps": [
                    {
                        "declaration": declaration,
                        "kind": "def",
                        "source_file": source_file,
                        "line": line,
                    }
                ],
                "blocked_routes": [] if blocked is None else blocked,
            }

        prior_row["proposition_alias_expansion"] = alias_route(
            "Fixture.Old.sourcePredicate", "Fixture/Old.lean", 10
        )
        prior_row["subtype_predicate_proposition_alias_expansion"] = alias_route(
            "Fixture.Old.subtypePredicate", "Fixture/Old.lean", 20
        )
        current_row["proposition_alias_expansion"] = alias_route(
            "Fixture.Renamed.sourcePredicate", "Fixture/Renamed.lean", 110
        )
        current_row["subtype_predicate_proposition_alias_expansion"] = alias_route(
            "Fixture.Renamed.subtypePredicate", "Fixture/Renamed.lean", 120
        )

        def descriptor(
            row: dict[str, object], *, item: dict[str, object], source_key: str, current: bool
        ) -> dict[str, object]:
            with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
                result, _ = REBIND._normalized_generated_item(
                    row,
                    section="boundary_input_items",
                    map_items={source_key: item},
                    current=current,
                )
            return result

        prior = descriptor(
            prior_row, item=prior_item, source_key="prior_key", current=False
        )
        current = descriptor(
            current_row, item=current_item, source_key="current_key", current=True
        )
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(current))

        changed = copy.deepcopy(current_row)
        changed_alias = changed["proposition_alias_expansion"]
        assert isinstance(changed_alias, dict)
        changed_alias["expanded_type"] = "Q"
        self.assertNotEqual(
            REBIND._canonical_digest(prior),
            REBIND._canonical_digest(
                descriptor(
                    changed, item=current_item, source_key="current_key", current=True
                )
            ),
        )

        incomplete_prior = copy.deepcopy(prior_row)
        incomplete_current = copy.deepcopy(current_row)
        for row in (incomplete_prior, incomplete_current):
            for field in (
                "proposition_alias_expansion",
                "subtype_predicate_proposition_alias_expansion",
            ):
                alias = row[field]
                assert isinstance(alias, dict)
                alias["blocked_routes"] = ["unresolved transparent route"]
        incomplete_prior_descriptor = descriptor(
            incomplete_prior, item=prior_item, source_key="prior_key", current=False
        )
        incomplete_current_descriptor = descriptor(
            incomplete_current, item=current_item, source_key="current_key", current=True
        )
        self.assertNotEqual(
            REBIND._canonical_digest(incomplete_prior_descriptor),
            REBIND._canonical_digest(incomplete_current_descriptor),
        )

    def test_alias_route_metadata_only_change_is_semantically_equal(self) -> None:
        """Alias FQNs and source coordinates alone never change a descriptor.

        This deliberately holds every other generated field fixed.  It covers
        both expanded proposition-alias fields rather than relying on a
        broader theorem/declaration rename to happen to exercise them.
        """

        item = _map_item()
        base = _row(item, source_key="stable_key", current=True)
        base["proposition_alias_expansion"] = {
            "expanded_type": "forall x : Nat, P x",
            "transparent_steps": [
                {
                    "declaration": "Fixture.Original.propositionAlias",
                    "kind": "def",
                    "source_file": "Fixture/Original.lean",
                    "line": 41,
                }
            ],
            "blocked_routes": [],
        }
        base["subtype_predicate_proposition_alias_expansion"] = {
            "expanded_type": "fun x : Nat => P x",
            "transparent_steps": [
                {
                    "declaration": "Fixture.Original.subtypePredicate",
                    "kind": "def",
                    "source_file": "Fixture/Original.lean",
                    "line": 57,
                }
            ],
            "blocked_routes": [],
        }
        renamed = copy.deepcopy(base)
        for field, declaration, source_file, line in (
            (
                "proposition_alias_expansion",
                "Fixture.Renamed.propositionAlias",
                "Fixture/Renamed.lean",
                141,
            ),
            (
                "subtype_predicate_proposition_alias_expansion",
                "Fixture.Renamed.subtypePredicate",
                "Fixture/Renamed.lean",
                157,
            ),
        ):
            expansion = renamed[field]
            assert isinstance(expansion, dict)
            steps = expansion["transparent_steps"]
            assert isinstance(steps, list) and len(steps) == 1
            step = steps[0]
            assert isinstance(step, dict)
            step.update(
                {
                    "declaration": declaration,
                    "source_file": source_file,
                    "line": line,
                }
            )

        def normalized(row: dict[str, object]) -> dict[str, object]:
            with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
                descriptor, _ = REBIND._normalized_generated_item(
                    row,
                    section="boundary_input_items",
                    map_items={"stable_key": item},
                    current=True,
                )
            return descriptor

        self.assertEqual(
            REBIND._canonical_digest(normalized(base)),
            REBIND._canonical_digest(normalized(renamed)),
        )
        self.assertEqual(
            OBLIGATIONS.source_record_obligation_descriptor(base, section="boundary_input_items"),
            OBLIGATIONS.source_record_obligation_descriptor(
                renamed, section="boundary_input_items"
            ),
        )

    def test_alias_route_context_and_fidelity_remain_semantic(self) -> None:
        """Current-only generated receipts cannot erase review semantics.

        A v1 row did not always carry an alias resolver receipt, so a current
        nontrivial route must not equal a legacy row merely because the Lean
        source declaration string is unchanged.  The two context/fidelity
        digests are likewise semantic obligations, not freshness credentials.
        """

        prior_item = _map_item()
        current_item = _map_item()
        prior_row = _row(prior_item, source_key="prior_key", current=False)
        current_row = _row(current_item, source_key="current_key", current=True)
        for row in (prior_row, current_row):
            row["source_record_item_semantic_context_requirements_sha256"] = "c" * 64
            row["source_record_item_source_proof_fidelity_records_sha256"] = "d" * 64

        def descriptor(
            row: dict[str, object], *, map_item: dict[str, object], source_key: str, current: bool
        ) -> dict[str, object]:
            with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
                result, _ = REBIND._normalized_generated_item(
                    row,
                    section="boundary_input_items",
                    map_items={source_key: map_item},
                    current=current,
                )
            return result

        prior = descriptor(
            prior_row, map_item=prior_item, source_key="prior_key", current=False
        )
        current = descriptor(
            current_row, map_item=current_item, source_key="current_key", current=True
        )
        self.assertEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(current))

        changed_alias_row = copy.deepcopy(current_row)
        changed_alias_row["review_alias_expansion"] = {
            "schema": 1,
            "reviewed_declaration": "Fixture.Paper.evidence",
            "effective_declaration": "Fixture.Paper.aliasTarget",
            "effective_kind": "theorem",
            "alias_present": True,
            "complete": True,
            "steps": [
                {
                    "from": "Fixture.Paper.evidence",
                    "reference": "aliasTarget",
                    "to": "Fixture.Paper.aliasTarget",
                    "target_kind": "theorem",
                    "source_file": "Fixture/Paper.lean",
                    "line": 42,
                }
            ],
            "blocked_routes": [],
        }
        changed_alias = descriptor(
            changed_alias_row,
            map_item=current_item,
            source_key="current_key",
            current=True,
        )
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed_alias))

        changed_context_row = copy.deepcopy(current_row)
        changed_context_row[
            "source_record_item_semantic_context_requirements_sha256"
        ] = "e" * 64
        changed_context = descriptor(
            changed_context_row,
            map_item=current_item,
            source_key="current_key",
            current=True,
        )
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed_context))

        changed_fidelity_row = copy.deepcopy(current_row)
        changed_fidelity_row[
            "source_record_item_source_proof_fidelity_records_sha256"
        ] = "f" * 64
        changed_fidelity = descriptor(
            changed_fidelity_row,
            map_item=current_item,
            source_key="current_key",
            current=True,
        )
        self.assertNotEqual(REBIND._canonical_digest(prior), REBIND._canonical_digest(changed_fidelity))

    def test_current_signature_and_association_pin_are_revalidated(self) -> None:
        item = _map_item()
        row = _row(item, source_key="current_key", current=True)
        association = row["source_contract_association"]
        assert isinstance(association, dict)
        association["semantic_association_sha256"] = "0" * 64
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            with self.assertRaisesRegex(
                REBIND.SourceRecordSemanticRebindError,
                "semantic association digest",
            ):
                REBIND._normalized_generated_item(
                    row,
                    section="boundary_input_items",
                    map_items={"current_key": item},
                    current=True,
                )

    def test_schema2_historical_association_is_authenticated_not_rejected(self) -> None:
        """A prior v10 raw receipt may already use association schema 2."""

        item = _map_item()
        row = _row(item, source_key="archived_key", current=True)
        # This fixture models a schema-2 archived row while retaining only
        # fields that an archived source-record receipt is allowed to carry.
        row.pop("review_alias_expansion", None)
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            descriptor, receipt = REBIND._normalized_generated_item(
                row,
                section="boundary_input_items",
                map_items={"archived_key": item},
                current=False,
            )
        self.assertIsNone(receipt)
        self.assertEqual(descriptor["section"], "boundary_input_items")

    def test_direct_route_absent_map_contract_equals_generated_empty_contract(self) -> None:
        """Direct source routes serialize an omitted map contract canonically."""

        item = _map_item()
        item.pop("semantic_contract")
        row = _row(_map_item(), source_key="direct_key", current=True)
        association = row["source_contract_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identity = identities[0]
        assert isinstance(identity, dict)
        identity["source_map_item_sha256"] = source_map_item_record_digest(item)
        identity["semantic_contract"] = {
            "evidence_declaration": "",
            "spec_declaration": "",
            "evidence_mode": "",
            "semantic_shape": "",
        }
        identity["source_semantic_sha256"] = REBIND.source_item_coverage_sha256(item, "")
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [str(identity["source_semantic_sha256"])], signature
        )
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        with patch.object(REBIND, "source_record_item_reuse_eligible", return_value=True):
            descriptor, _receipt = REBIND._normalized_generated_item(
                row,
                section="boundary_input_items",
                map_items={"direct_key": item},
                current=True,
            )
        self.assertEqual(descriptor["section"], "boundary_input_items")

    def test_changed_map_record_requires_an_exact_archived_map_snapshot(self) -> None:
        prior_item = _map_item(presentation_timestamp="archived")
        current_item = _map_item(presentation_timestamp="current")
        with tempfile.TemporaryDirectory() as temporary:
            paper_dir = Path(temporary) / "Fixture"
            audit = paper_dir / "audit"
            audit.mkdir(parents=True)
            prior_map_path = audit / "paper_statement_map.prior.json"
            current_map_path = audit / "paper_statement_map.current.json"
            prior_map = {"items": {"old_key": prior_item}}
            # Keep the storage key stable here so this assertion isolates the
            # full-record digest mismatch.  A key rename is separately tested
            # as a valid semantic rebind when the underlying source identity
            # is unchanged.
            current_map = {"items": {"old_key": current_item}}
            prior_map_path.write_text(json.dumps(prior_map, sort_keys=True))
            current_map_path.write_text(json.dumps(current_map, sort_keys=True))
            prior_raw = {
                "paper_statement_map_sha256": hashlib.sha256(
                    prior_map_path.read_bytes()
                ).hexdigest()
            }
            selected, validation = REBIND._maps_for_prior(
                paper="Fixture",
                prior_raw=prior_raw,
                prior_raw_path=audit / "source_record_audit.prior.json",
                current_map=current_map,
                current_map_path=current_map_path,
                paper_dir=paper_dir,
                prior_statement_map=prior_map,
                prior_statement_map_path=prior_map_path,
                prior_association_snapshot_reconciliation_path=None,
            )
            self.assertEqual(selected, prior_map)
            self.assertEqual(validation.get("mode"), "archived_exact_map")

            prior_identity = _association(
                prior_item, source_key="old_key", current=False
            )["source_item_identities"][0]
            assert isinstance(prior_identity, dict)
            with self.assertRaisesRegex(
                REBIND.SourceRecordSemanticRebindError, "source-map item digest is stale"
            ):
                REBIND._identity_from_map(
                    prior_identity,
                    map_items=current_map["items"],
                    current=False,
                    label="fixture archived identity",
                )

    def test_semantic_and_recursive_groups_are_never_legacy_rebound(self) -> None:
        item = _map_item()
        for section in ("semantic_model_items", "recursive_field_items"):
            with self.assertRaises(REBIND.SourceRecordSemanticRebindError):
                REBIND._normalized_generated_item(
                    _row(item, source_key="source", current=False),
                    section=section,
                    map_items={"source": item},
                    current=False,
                )

    def test_forged_marker_has_no_loader_authority(self) -> None:
        forged = {
            REBIND.SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD: {
                "schema": REBIND.SOURCE_RECORD_SEMANTIC_REBIND_SCHEMA
            }
        }
        self.assertTrue(REBIND.source_record_semantic_rebind_item_has_provenance(forged))
        self.assertFalse(REBIND.is_loaded_source_record_semantic_rebind_item(forged))


class LegacyPromptReceiptCompatibilityTests(unittest.TestCase):
    def test_legacy_prompt_authenticated_receipt_remains_fail_closed(self) -> None:
        payload: dict[str, object] = {
            "semantic_evidence": {"result": "proved"},
            "llm_judge_prompt": "legacy presentation wording",
        }
        projection = {
            "semantic_evidence": {"result": "proved"},
            "llm_judge_prompt": payload["llm_judge_prompt"],
        }
        surface = {
            SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD: projection,
        }
        payload[SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD] = (
            LEGACY_SOURCE_RECORD_AUDIT_SURFACE_SCHEMA
        )
        payload[SOURCE_RECORD_AUDIT_SURFACE_FIELD] = surface
        payload["source_record_audit_sha256"] = source_record_audit_surface_sha256(
            surface
        )
        payload[SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD] = (
            SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA
        )
        payload[SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD] = (
            _source_record_legacy_prompt_integrity_sha256(payload)
        )

        self.assertEqual(source_record_audit_receipt_error(payload), "")
        payload["semantic_evidence"] = {"result": "assumed"}
        self.assertTrue(source_record_audit_receipt_error(payload))


class SemanticRebindReaderOnlyTests(unittest.TestCase):
    def test_production_module_has_no_issuer_or_cli(self) -> None:
        self.assertFalse(hasattr(REBIND, "build_source_record_semantic_rebind"))
        self.assertFalse(hasattr(REBIND, "parse_args"))
        self.assertFalse(hasattr(REBIND, "main"))
        self.assertTrue(
            hasattr(REBIND, "_reconstruct_source_record_semantic_rebind")
        )


class SemanticRebindHistoricalAssociationIntegrationTests(unittest.TestCase):
    """Exercise the historical map exception through the real replay loader."""

    PAPER = "FixturePaper"
    JUDGMENT_KEY = "storage-address-is-not-a-match-key"

    def _write_json(self, path: Path, value: object) -> None:
        path.write_text(
            json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def _raw_audit(
        self, *, row: dict[str, object], paper_statement_map_sha256: str
    ) -> dict[str, object]:
        raw: dict[str, object] = {
            "paper": self.PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "paper_statement_map_sha256": paper_statement_map_sha256,
            "lean_check": {"returncode": 0},
            "recursion_failure_count": 0,
            "boundary_input_items": [row],
        }
        stamp_source_record_audit_receipts(raw)
        return raw

    def _current_row(self, item: dict[str, object]) -> dict[str, object]:
        row = _row(item, source_key="current_storage_key", current=True)
        row.update(
            {
                "source_record_item_reuse_eligibility": {
                    "eligible": True,
                    "blockers": [],
                },
                "source_record_item_digest_schema": REBIND.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                "source_record_item_semantic_id": "c" * 64,
                "source_record_item_context_sha256": "d" * 64,
                "source_record_item_sha256": "e" * 64,
            }
        )
        return row

    def _fixture(self) -> dict[str, object]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        paper_dir = Path(temporary.name) / self.PAPER
        audit = paper_dir / "audit"
        audit.mkdir(parents=True)

        archived_item = _map_item(presentation_timestamp="archived")
        current_item = _map_item(presentation_timestamp="current")
        witness_map_path = audit / "paper_statement_map.archived_witness.json"
        current_map_path = audit / "paper_statement_map.json"
        self._write_json(
            witness_map_path,
            {
                "schema": 1,
                "paper": self.PAPER,
                # This is deliberately not the raw association's storage key.
                "items": {"witness_storage_key": archived_item},
            },
        )
        self._write_json(
            current_map_path,
            {
                "schema": 1,
                "paper": self.PAPER,
                "items": {"current_storage_key": current_item},
            },
        )

        prior_raw_path = audit / "source_record_audit.archived.json"
        current_raw_path = audit / "source_record_audit.json"
        prior_raw = self._raw_audit(
            row=_row(
                archived_item, source_key="archived_storage_key", current=False
            ),
            # The historical lane is available only for a genuine aggregate
            # receipt mismatch; the exact item pin above remains the witness.
            paper_statement_map_sha256="0" * 64,
        )
        current_raw = self._raw_audit(
            row=self._current_row(current_item),
            paper_statement_map_sha256=hashlib.sha256(
                current_map_path.read_bytes()
            ).hexdigest(),
        )
        self._write_json(prior_raw_path, prior_raw)
        self._write_json(current_raw_path, current_raw)

        prior_judgments_path = audit / "prior_judgments.json"
        prior_judgments = {
            "schema": 1,
            "paper": self.PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": prior_raw["source_record_audit_sha256"],
            "items": {
                self.JUDGMENT_KEY: {
                    "classification": "validated_source_assumption",
                    "validator": "fixture reviewer",
                    "validated_at": "2026-07-28",
                }
            },
        }
        self._write_json(prior_judgments_path, prior_judgments)

        attestation_path = audit / "prior_attestation.json"
        prior_attestation = {
            "schema": 1,
            "artifact_kind": "source_record_current_semantic_revalidation_attestation",
            "paper": self.PAPER,
            "review_scope": "all_current_generated_judgment_keys",
            "scope": "all_current_semantic_model_judgment_groups",
            "reviewed_current_semantics": True,
            "current_source_record_audit_sha256": prior_raw[
                "source_record_audit_sha256"
            ],
            "generated_judgment_keys_sha256": REBIND.generated_judgment_keys_sha256(
                prior_raw
            ),
            "generated_judgment_surface_sha256": REBIND.generated_judgment_surface_sha256(
                prior_raw
            ),
            "reviewer": "fixture reviewer",
            "validated_at": "2026-07-28",
        }
        self._write_json(attestation_path, prior_attestation)

        reconciliation_path = (
            audit / RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        )
        RECONCILIATION.write_historical_association_snapshot_reconciliation(
            paper_dir=paper_dir,
            paper=self.PAPER,
            raw_audit_path=prior_raw_path,
            witness_map_path=witness_map_path,
            output_path=reconciliation_path,
        )

        payload = REBIND._reconstruct_source_record_semantic_rebind(
            paper=self.PAPER,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            current_raw_audit=current_raw,
            prior_judgments=prior_judgments,
            prior_attestation=prior_attestation,
            prior_raw_audit_path=prior_raw_path,
            current_raw_audit_path=current_raw_path,
            prior_judgments_path=prior_judgments_path,
            prior_attestation_path=attestation_path,
            current_statement_map=json.loads(current_map_path.read_text()),
            current_statement_map_path=current_map_path,
            prior_association_snapshot_reconciliation_path=reconciliation_path,
        )
        overlay_path = REBIND.source_record_semantic_rebind_overlay_path(paper_dir)
        self._write_json(overlay_path, payload)
        return {
            "paper_dir": paper_dir,
            "prior_raw_path": prior_raw_path,
            "witness_map_path": witness_map_path,
            "current_raw": current_raw,
            "payload": payload,
        }

    def test_reconciliation_replays_renamed_witness_key_and_rejects_input_mutation(
        self,
    ) -> None:
        fixture = self._fixture()
        paper_dir = fixture["paper_dir"]
        prior_raw_path = fixture["prior_raw_path"]
        witness_map_path = fixture["witness_map_path"]
        current_raw = fixture["current_raw"]
        payload = fixture["payload"]
        assert isinstance(paper_dir, Path)
        assert isinstance(prior_raw_path, Path)
        assert isinstance(witness_map_path, Path)
        assert isinstance(current_raw, dict)
        assert isinstance(payload, dict)

        validation = payload["prior_statement_map_validation"]
        assert isinstance(validation, dict)
        self.assertEqual(
            validation.get("mode"), "historical_association_snapshot_reconciliation"
        )
        with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
            loaded = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, self.PAPER, current_raw
            )
        self.assertEqual(set(loaded), {self.JUDGMENT_KEY})
        self.assertTrue(
            REBIND.is_loaded_source_record_semantic_rebind_item(
                loaded[self.JUDGMENT_KEY]
            )
        )

        original_raw_bytes = prior_raw_path.read_bytes()
        original_witness_bytes = witness_map_path.read_bytes()
        prior_raw_path.write_text('{"tampered": true}\n', encoding="utf-8")
        self.assertIn(
            "prior raw audit bytes changed",
            REBIND.source_record_semantic_rebind_overlay_error(
                payload, paper=self.PAPER, paper_dir=paper_dir
            ),
        )
        with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
            self.assertEqual(
                REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, self.PAPER, current_raw
                ),
                {},
            )
        prior_raw_path.write_bytes(original_raw_bytes)

        witness_map_path.write_bytes(original_witness_bytes + b"\n")
        self.assertIn(
            "witness",
            REBIND.source_record_semantic_rebind_overlay_error(
                payload, paper=self.PAPER, paper_dir=paper_dir
            ),
        )
        with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
            self.assertEqual(
                REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, self.PAPER, current_raw
                ),
                {},
            )


class SemanticRebindLoaderTests(unittest.TestCase):
    """Exercise immutable replay and the live-currentness gate."""

    PAPER = "KR21Monoculture"
    JUDGMENT_KEY = "storage-address-is-not-a-match-key"

    def _temporary_paper(self) -> tuple[tempfile.TemporaryDirectory[str], Path]:
        temporary = tempfile.TemporaryDirectory()
        paper_dir = Path(temporary.name) / "KR21Monoculture"
        audit = paper_dir / "audit"
        audit.mkdir(parents=True)
        prior_raw_name = (
            "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
        )
        prior_sidecar_name = (
            "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
        )
        prior_attestation_name = (
            "source_record_current_revalidation_default_mode_candidate_18_semantic_groups."
            "sidecar_bound_v4_2026-07-28.json"
        )

        # Keep this fixture small and self-contained. Historical paper-working
        # snapshots are intentionally not repository inputs, and copying a
        # many-megabyte canonical audit into every test obscures the replay
        # policy under test while making the suite needlessly expensive.
        source_key = "current_storage_key"
        map_item = _map_item()
        statement_map_path = audit / "paper_statement_map.json"
        statement_map_path.write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": self.PAPER,
                    "items": {source_key: map_item},
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        statement_map_sha = hashlib.sha256(
            statement_map_path.read_bytes()
        ).hexdigest()

        prior_row = _row(map_item, source_key=source_key, current=False)
        current_row = _row(map_item, source_key=source_key, current=True)
        current_row.update(
            {
                "source_record_item_reuse_eligibility": {
                    "eligible": True,
                    "blockers": [],
                },
                "source_record_item_digest_schema": (
                    REBIND.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                ),
                "source_record_item_semantic_id": "c" * 64,
                "source_record_item_context_sha256": "d" * 64,
                "source_record_item_sha256": "e" * 64,
            }
        )

        def raw_audit(row: dict[str, object]) -> dict[str, object]:
            raw: dict[str, object] = {
                "paper": self.PAPER,
                "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
                "source_record_policy_version": (
                    REBIND.SOURCE_RECORD_V10_PROMPT_VERSION
                ),
                "paper_statement_map_sha256": statement_map_sha,
                "lean_check": {"returncode": 0},
                "recursion_failure_count": 0,
                "boundary_input_items": [row],
            }
            stamp_source_record_audit_receipts(raw)
            return raw

        prior_raw = raw_audit(prior_row)
        current_raw = raw_audit(current_row)
        (audit / prior_raw_name).write_text(
            json.dumps(prior_raw, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (audit / "source_record_audit.json").write_text(
            json.dumps(current_raw, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        prior_sidecar = {
            "schema": 1,
            "paper": self.PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": prior_raw[
                "source_record_audit_sha256"
            ],
            "validator": "semantic rebind fixture",
            "validated_at": "2026-07-28",
            "items": {
                self.JUDGMENT_KEY: {
                    "classification": "validated_source_assumption",
                }
            },
        }
        (audit / prior_sidecar_name).write_text(
            json.dumps(prior_sidecar, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        prior_attestation = {
            "schema": 1,
            "artifact_kind": (
                "source_record_current_semantic_revalidation_attestation"
            ),
            "paper": self.PAPER,
            "review_scope": "all_current_generated_judgment_keys",
            "scope": "all_current_semantic_model_judgment_groups",
            "reviewed_current_semantics": True,
            "current_source_record_audit_sha256": prior_raw[
                "source_record_audit_sha256"
            ],
            "generated_judgment_keys_sha256": (
                REBIND.generated_judgment_keys_sha256(prior_raw)
            ),
            "generated_judgment_surface_sha256": (
                REBIND.generated_judgment_surface_sha256(prior_raw)
            ),
            "reviewer": "semantic rebind fixture",
            "validated_at": "2026-07-28",
        }
        (audit / prior_attestation_name).write_text(
            json.dumps(prior_attestation, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        return temporary, paper_dir

    def _build(
        self,
        paper_dir: Path,
        *,
        prior_raw_override: dict[str, object] | None = None,
        current_raw_override: dict[str, object] | None = None,
        prior_judgments_override: dict[str, object] | None = None,
        prior_attestation_override: dict[str, object] | None = None,
        prior_association_snapshot_reconciliation_path: Path | None = None,
        historical_composition_parent: dict[str, object] | None = None,
        historical_composition_parent_path: Path | None = None,
        policy_version: str = REBIND.SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
    ) -> dict[str, object]:
        audit = paper_dir / "audit"
        prior_raw_path = audit / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
        current_raw_path = audit / "source_record_audit.json"
        prior_judgments_path = audit / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
        attestation_path = audit / "source_record_current_revalidation_default_mode_candidate_18_semantic_groups.sidecar_bound_v4_2026-07-28.json"
        return REBIND._reconstruct_source_record_semantic_rebind(
            paper="KR21Monoculture",
            paper_dir=paper_dir,
            prior_raw_audit=(
                prior_raw_override
                if prior_raw_override is not None
                else json.loads(prior_raw_path.read_text())
            ),
            current_raw_audit=(
                current_raw_override
                if current_raw_override is not None
                else json.loads(current_raw_path.read_text())
            ),
            prior_judgments=(
                prior_judgments_override
                if prior_judgments_override is not None
                else json.loads(prior_judgments_path.read_text())
            ),
            prior_attestation=(
                None
                if historical_composition_parent is not None
                else (
                    prior_attestation_override
                    if prior_attestation_override is not None
                    else json.loads(attestation_path.read_text())
                )
            ),
            prior_raw_audit_path=prior_raw_path,
            current_raw_audit_path=current_raw_path,
            prior_judgments_path=prior_judgments_path,
            prior_attestation_path=(
                None if historical_composition_parent is not None else attestation_path
            ),
            current_statement_map=json.loads((audit / "paper_statement_map.json").read_text()),
            current_statement_map_path=audit / "paper_statement_map.json",
            prior_association_snapshot_reconciliation_path=(
                prior_association_snapshot_reconciliation_path
            ),
            historical_composition_parent=historical_composition_parent,
            historical_composition_parent_path=historical_composition_parent_path,
            policy_version=policy_version,
        )

    def test_legacy_v1_overlay_replays_under_its_original_projection(self) -> None:
        """A new taxonomy adapter never makes an old receipt stale by itself."""

        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(
            paper_dir,
            policy_version=REBIND.LEGACY_SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
        )
        self.assertEqual(
            payload["policy_version"],
            REBIND.LEGACY_SOURCE_RECORD_SEMANTIC_REBIND_POLICY_VERSION,
        )
        self.assertNotIn(REBIND.GENERATED_TAXONOMY_CORE_ADAPTER_FIELD, payload)
        REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        self.assertEqual(
            REBIND.source_record_semantic_rebind_overlay_error(
                payload,
                paper=self.PAPER,
                paper_dir=paper_dir,
            ),
            "",
        )

    def test_historical_composition_parent_is_replayed_before_transport_acceptance(
        self,
    ) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        audit = paper_dir / "audit"
        prior_raw_path = (
            audit
            / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
        )
        prior_judgments_path = (
            audit
            / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
        )
        prior_attestation_path = (
            audit
            / "source_record_current_revalidation_default_mode_candidate_18_semantic_groups.sidecar_bound_v4_2026-07-28.json"
        )
        prior_raw = json.loads(prior_raw_path.read_text())
        prior_judgments = json.loads(prior_judgments_path.read_text())
        prior_judgments["current_selected_semantic_revalidation"] = {"schema": 1}
        prior_judgments["source_record_authenticated_evidence_composition"] = {
            "schema": 1
        }
        response = prior_judgments["items"][self.JUDGMENT_KEY]
        assert isinstance(response, dict)
        response[REBIND.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD] = {"schema": 1}
        response[REBIND.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD] = {"schema": 1}
        prior_judgments_path.write_text(
            json.dumps(prior_judgments, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

        groups, errors = OBLIGATIONS.raw_source_record_obligation_groups(prior_raw)
        self.assertEqual(errors, {})
        self.assertIn(
            "without a validated composition parent",
            REBIND._prior_sidecar_error(
                prior_judgments,
                paper=self.PAPER,
                prior_raw=prior_raw,
                prior_groups=groups,
            ),
        )
        self.assertEqual(
            REBIND._prior_sidecar_error(
                prior_judgments,
                paper=self.PAPER,
                prior_raw=prior_raw,
                prior_groups=groups,
                validated_historical_composition=True,
            ),
            "",
        )
        legacy_transport = copy.deepcopy(prior_judgments)
        legacy_response = legacy_transport["items"][self.JUDGMENT_KEY]
        assert isinstance(legacy_response, dict)
        legacy_response["source_record_differential_revalidation"] = {"schema": 1}
        self.assertIn(
            "already carries an overlay transport",
            REBIND._prior_sidecar_error(
                legacy_transport,
                paper=self.PAPER,
                prior_raw=prior_raw,
                prior_groups=groups,
                validated_historical_composition=True,
            ),
        )
        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError,
            "historical selected-overlay transport",
        ):
            self._build(
                paper_dir,
                prior_judgments_override=prior_judgments,
            )

        parent_path = audit / "historical_composition_parent.json"
        parent = {"fixture": "historical composition parent"}
        parent_path.write_text(
            json.dumps(parent, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        normal_attestation = json.loads(prior_attestation_path.read_text())
        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError, "exactly one"
        ):
            REBIND._effective_prior_attestation(
                paper=self.PAPER,
                paper_dir=paper_dir,
                prior_raw_audit=prior_raw,
                prior_raw_audit_path=prior_raw_path,
                prior_judgments=prior_judgments,
                prior_judgments_path=prior_judgments_path,
                prior_attestation=normal_attestation,
                prior_attestation_path=prior_attestation_path,
                historical_composition_parent=parent,
                historical_composition_parent_path=parent_path,
            )
        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError, "exactly one"
        ):
            REBIND._effective_prior_attestation(
                paper=self.PAPER,
                paper_dir=paper_dir,
                prior_raw_audit=prior_raw,
                prior_raw_audit_path=prior_raw_path,
                prior_judgments=prior_judgments,
                prior_judgments_path=prior_judgments_path,
                prior_attestation=None,
                prior_attestation_path=None,
                historical_composition_parent=None,
                historical_composition_parent_path=None,
            )
        validated = COMPOSITION.ValidatedHistoricalCompositionAttestation(
            normalized_full_attestation=normal_attestation,
            archived_raw_audit={},
            composed_sidecar={},
            selected_descriptor_multiset=(),
            overlay_descriptor_multiset=(),
            complete_descriptor_multiset=(),
        )
        with patch.object(
            COMPOSITION,
            "validate_historical_composition_attestation",
            return_value=validated,
        ) as validate:
            payload = self._build(
                paper_dir,
                prior_judgments_override=prior_judgments,
                historical_composition_parent=parent,
                historical_composition_parent_path=parent_path,
            )
            self.assertIn(REBIND.HISTORICAL_COMPOSITION_PARENT_FIELD, payload)
            self.assertNotIn("prior_semantic_attestation", payload)
            self.assertEqual(validate.call_count, 1)
            REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
                json.dumps(payload, indent=2, sort_keys=True) + "\n",
                encoding="utf-8",
            )

            self.assertEqual(
                REBIND.source_record_semantic_rebind_overlay_error(
                    payload, paper=self.PAPER, paper_dir=paper_dir
                ),
                "",
            )
            self.assertEqual(validate.call_count, 2)
            current_raw = json.loads((audit / "source_record_audit.json").read_text())
            with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
                loaded = REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, self.PAPER, current_raw
                )
            self.assertEqual(validate.call_count, 3)
            self.assertIn(self.JUDGMENT_KEY, loaded)
            self.assertNotIn(
                REBIND.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
                loaded[self.JUDGMENT_KEY],
            )
            self.assertNotIn(
                REBIND.AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD,
                loaded[self.JUDGMENT_KEY],
            )
            parent_path.write_text(
                parent_path.read_text(encoding="utf-8") + "\n", encoding="utf-8"
            )
            self.assertIn(
                "historical composition parent bytes changed",
                REBIND.source_record_semantic_rebind_overlay_error(
                    payload, paper=self.PAPER, paper_dir=paper_dir
                ),
            )
            with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
                self.assertEqual(
                    REBIND.load_current_source_record_semantic_rebind_items(
                        paper_dir, self.PAPER, current_raw
                    ),
                    {},
                )

    def test_reconciliation_map_lane_requires_the_authenticated_exception(self) -> None:
        """A map witness enters only through the replayed reconciliation lane."""

        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        audit = paper_dir / "audit"
        reconciliation_path = audit / "historical_association_reconciliation.json"
        reconciliation_path.write_text("{}\n", encoding="utf-8")
        current_map = json.loads((audit / "paper_statement_map.json").read_text())
        expected_validation = {
            "mode": "historical_association_snapshot_reconciliation",
            "reconciliation": {
                "path": "audit/historical_association_reconciliation.json",
                "file_sha256": hashlib.sha256(
                    reconciliation_path.read_bytes()
                ).hexdigest(),
                "integrity_sha256": "c" * 64,
            },
            "witness_statement_map": {
                "path": "audit/paper_statement_map.json",
                "file_sha256": hashlib.sha256(
                    (audit / "paper_statement_map.json").read_bytes()
                ).hexdigest(),
            },
            "archived_reported_paper_statement_map_sha256": json.loads(
                (
                    audit
                    / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
                ).read_text()
            )["paper_statement_map_sha256"],
        }
        with patch.object(
            REBIND,
            "_reconciled_prior_map",
            return_value=(current_map, expected_validation),
        ) as reconciled:
            payload = self._build(
                paper_dir,
                prior_association_snapshot_reconciliation_path=reconciliation_path,
            )
        self.assertEqual(
            payload["prior_statement_map_validation"], expected_validation
        )
        self.assertEqual(reconciled.call_count, 1)
        self.assertEqual(
            reconciled.call_args.kwargs["prior_raw_path"],
            audit
            / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json",
        )

        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError, "mutually exclusive"
        ):
            REBIND._reconstruct_source_record_semantic_rebind(
                paper="KR21Monoculture",
                paper_dir=paper_dir,
                prior_raw_audit=json.loads(
                    (
                        audit
                        / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
                    ).read_text()
                ),
                current_raw_audit=json.loads(
                    (audit / "source_record_audit.json").read_text()
                ),
                prior_judgments=json.loads(
                    (
                        audit
                        / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
                    ).read_text()
                ),
                prior_attestation=json.loads(
                    (
                        audit
                        / "source_record_current_revalidation_default_mode_candidate_18_semantic_groups.sidecar_bound_v4_2026-07-28.json"
                    ).read_text()
                ),
                prior_raw_audit_path=(
                    audit
                    / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
                ),
                current_raw_audit_path=audit / "source_record_audit.json",
                prior_judgments_path=(
                    audit
                    / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
                ),
                prior_attestation_path=(
                    audit
                    / "source_record_current_revalidation_default_mode_candidate_18_semantic_groups.sidecar_bound_v4_2026-07-28.json"
                ),
                current_statement_map=current_map,
                current_statement_map_path=audit / "paper_statement_map.json",
                prior_statement_map=current_map,
                prior_statement_map_path=audit / "paper_statement_map.json",
                prior_association_snapshot_reconciliation_path=reconciliation_path,
            )

    def test_build_rejects_explicit_non_evidence_prior_inputs(self) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        audit = paper_dir / "audit"
        prior_judgments = json.loads(
            (
                audit
                / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
            ).read_text()
        )
        prior_attestation = json.loads(
            (
                audit
                / "source_record_current_revalidation_default_mode_candidate_18_semantic_groups.sidecar_bound_v4_2026-07-28.json"
            ).read_text()
        )

        for payload in (
            {"artifact_kind": "candidate_receipt"},
            {"artifact_kind": "proposal_receipt"},
            {"validator_type": "candidate_reviewer"},
            {"validator_type": "proposal_reviewer"},
        ):
            self.assertTrue(REBIND._payload_is_non_evidence(payload))

        candidate_sidecar = copy.deepcopy(prior_judgments)
        candidate_sidecar["candidate_only"] = True
        with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "non-evidence"):
            self._build(paper_dir, prior_judgments_override=candidate_sidecar)

        candidate_response = copy.deepcopy(prior_judgments)
        response = next(iter(candidate_response["items"].values()))
        assert isinstance(response, dict)
        response["artifact_kind"] = "proposal_response"
        with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "non-evidence"):
            self._build(paper_dir, prior_judgments_override=candidate_response)

        candidate_attestation = copy.deepcopy(prior_attestation)
        candidate_attestation["validator_type"] = "candidate_attestation"
        with self.assertRaisesRegex(REBIND.SourceRecordSemanticRebindError, "non-evidence"):
            self._build(
                paper_dir, prior_attestation_override=candidate_attestation
            )

    def test_build_rejects_explicit_non_evidence_prior_and_current_raw_audits(self) -> None:
        """Raw candidate markers cannot enter either side of the replay."""

        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        audit = paper_dir / "audit"
        prior_raw = json.loads(
            (
                audit
                / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
            ).read_text()
        )
        current_raw = json.loads((audit / "source_record_audit.json").read_text())
        markers = (
            {"candidate_only": True},
            {"not_evidence": True},
            {"artifact_kind": "candidate_raw_audit"},
        )
        for marker in markers:
            with self.subTest(side="prior", marker=marker):
                candidate = copy.deepcopy(prior_raw)
                candidate.update(marker)
                stamp_source_record_audit_receipts(candidate)
                with self.assertRaisesRegex(
                    REBIND.SourceRecordSemanticRebindError,
                    "prior raw audit is explicitly marked non-evidence",
                ):
                    self._build(paper_dir, prior_raw_override=candidate)
            with self.subTest(side="current", marker=marker):
                candidate = copy.deepcopy(current_raw)
                candidate.update(marker)
                stamp_source_record_audit_receipts(candidate)
                with self.assertRaisesRegex(
                    REBIND.SourceRecordSemanticRebindError,
                    "current raw audit is explicitly marked non-evidence",
                ):
                    self._build(paper_dir, current_raw_override=candidate)

    def test_build_requires_successful_prior_lean_and_zero_recursion_failures(self) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        prior_raw_path = (
            paper_dir
            / "audit"
            / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
        )
        failed_lean = json.loads(prior_raw_path.read_text())
        lean_check = failed_lean.get("lean_check")
        assert isinstance(lean_check, dict)
        lean_check["returncode"] = 1
        stamp_source_record_audit_receipts(failed_lean)
        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError,
            "prior raw audit lacks a successful Lean check",
        ):
            self._build(paper_dir, prior_raw_override=failed_lean)

        recursive = json.loads(prior_raw_path.read_text())
        recursive["recursion_failure_count"] = 1
        stamp_source_record_audit_receipts(recursive)
        with self.assertRaisesRegex(
            REBIND.SourceRecordSemanticRebindError,
            "prior raw audit has recursion failures",
        ):
            self._build(paper_dir, prior_raw_override=recursive)

    def test_loader_rejects_stale_live_inputs_and_archive_mutation(self) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(paper_dir)
        overlay = REBIND.source_record_semantic_rebind_overlay_path(paper_dir)
        overlay.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
        current = json.loads((paper_dir / "audit" / "source_record_audit.json").read_text())
        with patch.object(REBIND, "_live_raw_identity_error", return_value="stale fingerprint"):
            self.assertEqual(
                REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, "KR21Monoculture", current
                ),
                {},
            )

        # With a live-current identity the loader materializes from the
        # archived sidecar but derives the association pin from current raw
        # members. It never trusts an old response's pin.
        with (
            patch.object(REBIND, "_live_raw_identity_error", return_value=""),
            patch.object(
                EVIDENCE, "source_record_audit_identity_error", return_value=""
            ),
            patch.object(
                EVIDENCE, "_source_record_audit_identity_error", return_value=""
            ),
        ):
            loaded = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, "KR21Monoculture", current
            )
        self.assertTrue(loaded)
        groups, errors = OBLIGATIONS.raw_source_record_obligation_groups(current)
        self.assertEqual(errors, {})
        selected = next(
            key
            for key, value in loaded.items()
            if "semantic_association_sha256" in value and key in groups
        )
        group = groups[selected]
        members = group.get("raw_members")
        assert isinstance(members, list)
        association = next(
            item.get("source_contract_association")
            for section, item in members
            if section == "boundary_input_items"
            and isinstance(item, dict)
            and isinstance(item.get("source_contract_association"), dict)
        )
        assert isinstance(association, dict)
        self.assertEqual(
            loaded[selected].get("semantic_association_sha256"),
            association.get("semantic_association_sha256"),
        )
        self.assertEqual(
            loaded[selected].get("source_record_audit_sha256"),
            current.get("source_record_audit_sha256"),
        )

        # A self-consistent in-memory object is not the live receiving audit.
        # The loader must bind it to the canonical raw file before descriptor
        # matching, even when a caller bypasses the ordinary receipt gate.
        substituted = copy.deepcopy(current)
        substituted["current_source_record_judgment_count"] = 999
        with (
            patch.object(REBIND, "_current_raw_error", return_value=""),
            patch.object(REBIND, "_live_raw_identity_error", return_value=""),
        ):
            self.assertEqual(
                REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, "KR21Monoculture", substituted
                ),
                {},
            )

        prior_sidecar = (
            paper_dir
            / "audit"
            / "source_record_match_llm.current_revalidation_default_mode_candidate_18_semantic_groups.json"
        )
        prior_sidecar.write_text(prior_sidecar.read_text() + "\n")
        self.assertTrue(
            REBIND.source_record_semantic_rebind_overlay_error(
                payload, paper="KR21Monoculture", paper_dir=paper_dir
            )
        )

    def test_identity_context_is_process_local_and_reuses_one_live_identity_check(
        self,
    ) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(paper_dir)
        REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n"
        )
        current = json.loads((paper_dir / "audit" / "source_record_audit.json").read_text())
        with patch.object(REBIND, "_live_raw_identity_error", return_value="") as gate:
            context = REBIND.prepare_current_source_record_semantic_rebind_identity_context(
                paper_dir, self.PAPER, current
            )
            self.assertIsNotNone(context)
            self.assertFalse(isinstance(context, dict))
            first = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, self.PAPER, current, identity_context=context
            )
            second = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, self.PAPER, current, identity_context=context
            )
        self.assertTrue(first)
        self.assertEqual(set(first), set(second))
        self.assertEqual(gate.call_count, 1)

        stale = copy.deepcopy(current)
        stale["current_source_record_judgment_count"] = 999
        self.assertEqual(
            REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, self.PAPER, stale, identity_context=context
            ),
            {},
        )

    def test_neutral_identity_context_avoids_a_second_schema2_identity_scan(
        self,
    ) -> None:
        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(paper_dir)
        REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n"
        )
        current = json.loads(
            (paper_dir / "audit" / "source_record_audit.json").read_text()
        )
        with (
            patch.object(
                EVIDENCE,
                "source_record_audit_identity_error",
                return_value="",
            ) as strict_gate,
            patch.object(
                EVIDENCE,
                "_source_record_audit_identity_error",
                return_value="",
            ),
            patch.object(
                REBIND,
                "_live_raw_identity_error",
                side_effect=AssertionError("schema-2 must reuse the neutral context"),
            ),
        ):
            context = EVIDENCE.prepare_current_source_record_identity_context(
                paper_dir,
                self.PAPER,
                current,
            )
            self.assertIsNotNone(context)
            loaded = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir,
                self.PAPER,
                current,
                source_record_identity_context=context,
            )
        self.assertTrue(loaded)
        self.assertEqual(strict_gate.call_count, 1)

    def test_deferred_live_identity_refuses_to_empty_the_optional_lane(self) -> None:
        """A busy raw scan is transient, not evidence that a rebind is absent."""

        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(paper_dir)
        REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n"
        )
        current = json.loads(
            (paper_dir / "audit" / "source_record_audit.json").read_text()
        )
        deferred = (
            "source-record identity revalidation deferred: a fresh source-record "
            "scan currently owns the repository evidence lock"
        )
        with (
            patch.object(REBIND, "_current_raw_error", return_value=""),
            patch.object(REBIND, "_canonical_live_raw_error", return_value=""),
            patch.object(REBIND, "_live_raw_identity_error", return_value=deferred),
        ):
            with self.assertRaisesRegex(
                REBIND.SourceRecordSemanticRebindIdentityDeferred,
                "identity revalidation deferred",
            ):
                REBIND.prepare_current_source_record_semantic_rebind_identity_context(
                    paper_dir, self.PAPER, current
                )
            with self.assertRaisesRegex(
                REBIND.SourceRecordSemanticRebindIdentityDeferred,
                "identity revalidation deferred",
            ):
                REBIND.load_current_source_record_semantic_rebind_items(
                    paper_dir, self.PAPER, current
                )

    def test_source_record_audit_consumes_only_authenticated_bridge_items(self) -> None:
        """The generator's current-judgment view matches the evidence gate."""

        temporary, paper_dir = self._temporary_paper()
        self.addCleanup(temporary.cleanup)
        payload = self._build(paper_dir)
        REBIND.source_record_semantic_rebind_overlay_path(paper_dir).write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n"
        )
        current = json.loads((paper_dir / "audit" / "source_record_audit.json").read_text())
        ordinary_path = paper_dir / "audit" / "source_record_match_llm.json"
        ordinary_path.write_text(
            json.dumps({"schema": 1, "paper": "KR21Monoculture", "items": {}}),
            encoding="utf-8",
        )
        helper = _load_source_record_audit_helper()
        with (
            patch.object(REBIND, "_live_raw_identity_error", return_value=""),
            patch.object(
                EVIDENCE, "source_record_audit_identity_error", return_value=""
            ),
            patch.object(
                EVIDENCE, "_source_record_audit_identity_error", return_value=""
            ),
        ):
            loaded = REBIND.load_current_source_record_semantic_rebind_items(
                paper_dir, "KR21Monoculture", current
            )
            judgments = helper.current_source_record_judgments(
                paper_dir, "KR21Monoculture", current
            )
        self.assertEqual(set(judgments), set(loaded))
        selected = next(iter(loaded))

        # A serialized marker cannot enter the ordinary path, even if a caller
        # asks for the historical bridge explicitly.
        forged = json.loads(json.dumps(loaded[selected]))
        self.assertEqual(
            helper.current_source_record_judgments_from_payload(
                {"schema": 1, "paper": "KR21Monoculture", "items": {selected: forged}},
                "KR21Monoculture",
                current,
                paper_dir=paper_dir,
            ),
            {},
        )

        # Ordinary evidence with a current receipt is intentionally preferred
        # over an otherwise valid historical transport for the same key.
        ordinary = copy.deepcopy(loaded[selected])
        ordinary.pop(REBIND.SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD, None)
        ordinary["classification"] = "ordinary_current_preferred"
        ordinary_path.write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": "KR21Monoculture",
                    "prompt_version": current["prompt_version"],
                    "source_record_audit_sha256": current["source_record_audit_sha256"],
                    "items": {selected: ordinary},
                }
            ),
            encoding="utf-8",
        )
        with patch.object(REBIND, "_live_raw_identity_error", return_value=""):
            preferred = helper.current_source_record_judgments(
                paper_dir, "KR21Monoculture", current
            )
        self.assertEqual(
            preferred[selected].get("classification"), "ordinary_current_preferred"
        )


if __name__ == "__main__":
    unittest.main()
