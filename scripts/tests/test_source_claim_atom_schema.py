#!/usr/bin/env python3
"""Golden contracts for the portable source-claim atom schema."""

from __future__ import annotations

import json
import unittest
from copy import deepcopy
from pathlib import Path

from scripts import source_claim_atom_schema as schema


ROOT = Path(__file__).resolve().parents[2]


class SourceClaimAtomSchemaTests(unittest.TestCase):
    def legacy_atom(self) -> dict[str, object]:
        return {
            "id": "a",
            "source_locator": "source.tex:12-13",
            "semantic_claim": (
                "For every feasible allocation, total cost is at most the benchmark."
            ),
            "reviewed_lean_route": "Paper.bound",
        }

    def exact_atom(self) -> dict[str, object]:
        return {
            **self.legacy_atom(),
            "id": "b",
            "identity_schema": 2,
            "source_quote_sha256": "ab" * 32,
        }

    def clause_atom(self) -> dict[str, object]:
        return {
            **self.legacy_atom(),
            "id": "c",
            "identity_schema": 3,
            "source_quote_sha256": "cd" * 32,
            "verbatim_source_clause": "Total cost is at most the benchmark.",
        }

    def test_semantic_identity_golden_values(self) -> None:
        self.assertEqual(
            schema.source_claim_atom_semantic_sha256(self.legacy_atom()),
            "b00e6bb31c796d665cf53641513b307f192d9e01cf7f654e000e873e594b96c0",
        )
        self.assertEqual(
            schema.source_claim_atom_semantic_sha256(self.exact_atom()),
            "165530d136713cb9603514a47296aa73b3a370f6804b70cb8e6fe86de2f48223",
        )
        self.assertEqual(
            schema.source_claim_atom_semantic_sha256(self.clause_atom()),
            "da8ad91c744538874bec7604b63acbc736618754ce2dfbfb5365be6bf1887402",
        )
        self.assertEqual(
            schema.source_claim_atoms_semantic_sha256([self.exact_atom()]),
            "ef90cfebe2d158e29d1a76b9199255d46529906c2cfa2824958786d24836ddec",
        )

    def test_evidence_monolith_reexports_one_shared_authority(self) -> None:
        from scripts import audit_evidence_integrity as integrity

        self.assertIs(
            integrity.source_claim_atoms_validation_errors,
            schema.source_claim_atoms_validation_errors,
        )
        self.assertIs(
            integrity.source_claim_atom_semantic_sha256,
            schema.source_claim_atom_semantic_sha256,
        )
        self.assertIs(
            integrity.source_claim_atoms_semantic_sha256,
            schema.source_claim_atoms_semantic_sha256,
        )
        self.assertIs(
            integrity.source_spec_correspondence_item_identity_sha256,
            schema.source_spec_correspondence_item_identity_sha256,
        )

    def test_correspondence_identity_golden_value(self) -> None:
        atom = self.exact_atom()
        correspondence = {
            "schema": 1,
            "source_atoms_sha256": schema.source_claim_atoms_semantic_sha256(
                [atom]
            ),
            "spec_closure_sha256": "1" * 64,
            "spec_surface_sha256": "2" * 64,
            "closure_environment_sha256": "3" * 64,
            "source_atom_bindings": [
                {
                    "source_atom_sha256": (
                        schema.source_claim_atom_semantic_sha256(atom)
                    ),
                    "spec_component_sha256s": ["4" * 64],
                    "semantic_bridge": "x",
                }
            ],
            "closure_node_dispositions": [],
        }
        self.assertEqual(
            schema.source_spec_correspondence_item_identity_sha256(
                {"evidence_mode": "proves", "semantic_shape": "plain"},
                correspondence,
            ),
            "b3c7ed0ec15a66469656ce6aa4657e0fc471b193e7056c5c9d10d3ea391409ed",
        )

    def test_graph_native_realization_identity_is_content_only(self) -> None:
        contract = {
            "spec_declaration": "Paper.claimSpec",
            "evidence_declaration": "Paper.claim_proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        values = {
            "source_atoms_sha256": "1" * 64,
            "spec_closure_sha256": "2" * 64,
            "spec_surface_sha256": "3" * 64,
            "closure_environment_sha256": "4" * 64,
        }
        identity = schema.graph_native_source_spec_realization_identity_sha256(
            contract,
            **values,
        )
        self.assertRegex(identity, r"^[0-9a-f]{64}$")
        self.assertEqual(
            identity,
            schema.graph_native_source_spec_realization_identity_sha256(
                dict(reversed(list(contract.items()))),
                **values,
            ),
        )
        self.assertNotEqual(
            identity,
            schema.graph_native_source_spec_realization_identity_sha256(
                contract,
                **{**values, "spec_surface_sha256": "5" * 64},
            ),
        )

    def test_malformed_contract_golden_errors(self) -> None:
        malformed = [
            {
                "id": "bad space",
                "source_locator": "TBD",
                "semantic_claim": "todo",
                "reviewed_lean_route": "todo",
                "identity_schema": 2.0,
                "verbatim_source_clause": "x",
                "extra": 1,
            },
            {
                "id": "bad space",
                "source_locator": "a.tex:1 and b.tex:2",
                "semantic_claim": "Paper.Route",
                "reviewed_lean_route": "Paper.Route",
            },
        ]
        self.assertEqual(
            schema.source_claim_atoms_validation_errors(malformed),
            [
                "source_claim_atoms[0] has unsupported field(s): extra",
                "source_claim_atoms[0].id must use a nonempty stable atom identifier",
                "source_claim_atoms[0].source_locator must contain exactly one file:line source span",
                "source_claim_atoms[0].semantic_claim must contain a substantive source-facing claim",
                "source_claim_atoms[0].semantic_claim cannot be a Lean route/name in place of source semantics",
                "source_claim_atoms[0].identity_schema must be one of: 1, 2, 3",
                "source_claim_atoms[0].source_quote_sha256 is required for exact-quote atom identity or source-spec correspondence",
                "source_claim_atoms[0].verbatim_source_clause requires identity_schema 3",
                "source_claim_atoms[1].id must use a nonempty stable atom identifier",
                "source_claim_atoms[1].source_locator must contain exactly one file:line source span",
                "source_claim_atoms[1].semantic_claim cannot be a Lean route/name in place of source semantics",
            ],
        )

    def test_repository_atoms_match_existing_golden_identities(self) -> None:
        """All checked-in atoms remain readable by the standalone schema."""

        atoms_seen = 0
        for path in sorted(ROOT.glob("papers/*/audit/paper_statement_map.json")):
            try:
                payload = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            items = payload.get("items")
            if not isinstance(items, dict):
                continue
            for raw_item in items.values():
                if not isinstance(raw_item, dict):
                    continue
                raw_atoms = raw_item.get("source_claim_atoms")
                if raw_atoms is None:
                    continue
                atoms_seen += 1
                atoms_for_schema = raw_atoms
                public_projection = payload.get(
                    "publication_source_display_projection"
                )
                if public_projection is not None:
                    self.assertEqual(
                        public_projection,
                        {
                            "schema": 1,
                            "manifest": "audit/public_source_display_projection.json",
                            "raw_source_bytes_included": False,
                        },
                        path,
                    )
                    # Public maps retain publication-facing navigation labels.
                    # Exercise every other atom field under the standalone
                    # internal schema with a synthetic private locator when
                    # that display label is intentionally not a file span.
                    atoms_for_schema = deepcopy(raw_atoms)
                    if isinstance(atoms_for_schema, list):
                        for index, atom in enumerate(atoms_for_schema):
                            if not isinstance(atom, dict):
                                continue
                            atom_errors = schema.source_claim_atoms_validation_errors(
                                [atom]
                            )
                            if any(
                                ".source_locator must contain exactly one "
                                "file:line source span" in error
                                for error in atom_errors
                            ):
                                atom["source_locator"] = f"source.txt:{index + 1}"
                errors = schema.source_claim_atoms_validation_errors(atoms_for_schema)
                if errors:
                    self.fail(f"{path}: {errors}")
                self.assertTrue(
                    schema.source_claim_atoms_semantic_sha256(atoms_for_schema), path
                )
        self.assertGreater(atoms_seen, 0)

    def test_unknown_model_parameter_is_not_a_placeholder_claim(self) -> None:
        atom = self.legacy_atom()
        atom["semantic_claim"] = (
            "An unknown link function can leave the optimal policy unidentified "
            "even between two reward candidates."
        )
        self.assertEqual(schema.source_claim_atoms_validation_errors([atom]), [])
        atom["semantic_claim"] = "Unknown source claim to be supplied after review."
        self.assertTrue(any(
            "substantive source-facing claim" in error
            for error in schema.source_claim_atoms_validation_errors([atom])
        ))


if __name__ == "__main__":
    unittest.main()
