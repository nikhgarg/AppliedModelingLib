#!/usr/bin/env python3
"""Regression tests for source-first theorem-clause atom contracts."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
GATE_PATH = ROOT / "scripts" / "audit_evidence_integrity.py"
REPOSITORY_PATH = ROOT / "scripts" / "audit_repository.py"
SOURCE_RECORD_AUDIT_PATH = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
for import_root in (ROOT, ROOT / "scripts"):
    text = str(import_root)
    if text not in sys.path:
        sys.path.insert(0, text)

GATE_SPEC = importlib.util.spec_from_file_location("audit_evidence_integrity", GATE_PATH)
assert GATE_SPEC is not None and GATE_SPEC.loader is not None
GATE = importlib.util.module_from_spec(GATE_SPEC)
sys.modules[GATE_SPEC.name] = GATE
GATE_SPEC.loader.exec_module(GATE)

REPOSITORY_SPEC = importlib.util.spec_from_file_location(
    "audit_repository", REPOSITORY_PATH
)
assert REPOSITORY_SPEC is not None and REPOSITORY_SPEC.loader is not None
REPOSITORY = importlib.util.module_from_spec(REPOSITORY_SPEC)
sys.modules[REPOSITORY_SPEC.name] = REPOSITORY
REPOSITORY_SPEC.loader.exec_module(REPOSITORY)

SOURCE_RECORD_SPEC = importlib.util.spec_from_file_location(
    "source_record_audit", SOURCE_RECORD_AUDIT_PATH
)
assert SOURCE_RECORD_SPEC is not None and SOURCE_RECORD_SPEC.loader is not None
SOURCE_RECORD = importlib.util.module_from_spec(SOURCE_RECORD_SPEC)
sys.modules[SOURCE_RECORD_SPEC.name] = SOURCE_RECORD
SOURCE_RECORD_SPEC.loader.exec_module(SOURCE_RECORD)


class SourceClaimAtomsTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.source = self.paper / "source.txt"
        self.source.write_text(
            "Theorem 3. For every ordered target-rate pair, there exist structured "
            "prices and an optimal policy that accepts every surge trip and accepts "
            "non-surge trips up to a cutoff.\n"
            "The cutoff includes the zero endpoint (the empty policy) and the "
            "infinite endpoint (accept-all).\n"
            "Furthermore, when the target-rate ratio lies above C and below one, "
            "accept-all is uniquely optimal.\n",
            encoding="utf-8",
        )
        self.source_digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        (self.paper / "PaperInterface.lean").write_text(
            "namespace Fixture\n"
            "structure ConclusionRecord where\n"
            "  witness : True\n"
            "theorem proof_alpha : True := True.intro\n"
            "theorem proof_beta : True := True.intro\n"
            "end Fixture\n",
            encoding="utf-8",
        )
        self.write_status(include_names=["Fixture.proof_alpha", "Fixture.proof_beta"])

        previous_gate_root = GATE.ROOT
        GATE.ROOT = self.root
        self.addCleanup(setattr, GATE, "ROOT", previous_gate_root)
        previous_repository_root = REPOSITORY.ROOT
        REPOSITORY.ROOT = self.root
        self.addCleanup(setattr, REPOSITORY, "ROOT", previous_repository_root)

    def write_status(self, *, include_names: list[str]) -> None:
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "review_surface": {
                        "include_names": include_names,
                        "assumption_names": [],
                    }
                }
            ),
            encoding="utf-8",
        )

    def valid_atoms(self) -> list[dict[str, str]]:
        return [
            {
                "id": "general-cutoff-existence",
                "source_locator": "source.txt:1-2",
                "semantic_claim": (
                    "For every ordered target-rate pair, structured prices and an "
                    "optimal policy exist whose surge coordinate accepts all trips and "
                    "whose non-surge coordinate is a cutoff; the cutoff semantics include "
                    "the zero/empty and infinite/accept-all endpoints."
                ),
                "reviewed_lean_route": "Fixture.proof_alpha",
            },
            {
                "id": "high-ratio-acceptall-uniqueness",
                "source_locator": "source.txt:3",
                "semantic_claim": (
                    "When the target-rate ratio is strictly above C and strictly below "
                    "one, accept-all is the unique optimal policy."
                ),
                "reviewed_lean_route": "Fixture.proof_beta",
            },
        ]

    def map_payload(self, atoms: list[dict[str, str]]) -> dict[str, object]:
        return {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": self.source_digest,
            "source_coverage_mode": "named_theoretical_statements",
            "source_claim_atoms_schema": 1,
            "items": {
                "source_theorem_one": {
                    "source_kind": "theorem",
                    "title": "Theorem 3. Cutoff existence and uniqueness",
                    "source_location": "source.txt:1-3",
                    "statement": (
                        "Theorem 3 has a general cutoff/existence clause, including "
                        "the zero and infinite cutoff endpoints, and a separate "
                        "high-ratio accept-all uniqueness clause."
                    ),
                    "lean_declarations": ["Fixture.proof_alpha", "Fixture.proof_beta"],
                    "source_claim_atoms": atoms,
                }
            },
        }

    def write_map(self, payload: dict[str, object]) -> None:
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def route_findings(self) -> list[object]:
        with mock.patch.object(
            REPOSITORY, "library_lean_declaration_index", return_value={}
        ):
            return REPOSITORY.paper_statement_map_declaration_findings(
                "FixturePaper", self.paper, "formalized"
            )

    def test_compound_theorem_passes_with_general_cutoff_and_high_ratio_atoms(self) -> None:
        self.write_map(self.map_payload(self.valid_atoms()))

        self.assertEqual(
            GATE.source_claim_atom_inventory_findings(self.paper, "formalized"),
            [],
        )
        self.assertEqual(self.route_findings(), [])

    def test_exact_quote_identity_ignores_locator_and_curator_wording(self) -> None:
        first = self.valid_atoms()[0]
        first["identity_schema"] = 2
        first["source_quote_sha256"] = "a" * 64
        moved = dict(first)
        moved["source_locator"] = "renamed-source.txt:40-41"
        moved["semantic_claim"] = (
            "A clearer human annotation for the same exact verbatim source component."
        )

        self.assertEqual(
            GATE.source_claim_atom_semantic_sha256(first),
            GATE.source_claim_atom_semantic_sha256(moved),
        )
        changed_quote = dict(moved)
        changed_quote["source_quote_sha256"] = "b" * 64
        self.assertNotEqual(
            GATE.source_claim_atom_semantic_sha256(first),
            GATE.source_claim_atom_semantic_sha256(changed_quote),
        )

    def test_exact_quote_identity_requires_quote_and_rejects_mixed_schema(self) -> None:
        exact = self.valid_atoms()[0]
        exact["identity_schema"] = 2
        missing_quote = GATE.source_claim_atoms_validation_errors([exact])
        self.assertTrue(
            any("exact-quote atom identity" in error for error in missing_quote),
            missing_quote,
        )

        exact["source_quote_sha256"] = "a" * 64
        legacy = self.valid_atoms()[1]
        mixed = GATE.source_claim_atoms_validation_errors([exact, legacy])
        self.assertIn(
            "source_claim_atoms in one source item must use one identity schema",
            mixed,
        )

    def test_exact_clause_identity_distinguishes_atoms_in_one_source_quote(self) -> None:
        first = self.valid_atoms()[0]
        first.update(
            {
                "identity_schema": 3,
                "source_quote_sha256": "a" * 64,
                "verbatim_source_clause": "The general cutoff conclusion.",
            }
        )
        second = self.valid_atoms()[1]
        second.update(
            {
                "identity_schema": 3,
                "source_quote_sha256": "a" * 64,
                "verbatim_source_clause": "The high-ratio uniqueness conclusion.",
            }
        )

        first_sha = GATE.source_claim_atom_semantic_sha256(first)
        second_sha = GATE.source_claim_atom_semantic_sha256(second)
        self.assertTrue(first_sha)
        self.assertTrue(second_sha)
        self.assertNotEqual(first_sha, second_sha)
        self.assertTrue(GATE.source_claim_atoms_semantic_sha256([first, second]))

        renamed = dict(first)
        renamed.update(
            {
                "id": "renamed-navigation-id",
                "source_locator": "renamed-source.txt:40-41",
                "semantic_claim": "Different curator wording for the same exact clause.",
                "reviewed_lean_route": "Renamed.Namespace.Proof",
            }
        )
        self.assertEqual(
            first_sha,
            GATE.source_claim_atom_semantic_sha256(renamed),
        )

        changed_clause = dict(first)
        changed_clause["verbatim_source_clause"] = "A materially different clause."
        self.assertNotEqual(
            first_sha,
            GATE.source_claim_atom_semantic_sha256(changed_clause),
        )

    def test_exact_clause_identity_requires_clause_and_forbids_it_in_schema_two(
        self,
    ) -> None:
        exact_clause = self.valid_atoms()[0]
        exact_clause.update(
            {
                "identity_schema": 3,
                "source_quote_sha256": "a" * 64,
            }
        )
        missing_clause = GATE.source_claim_atoms_validation_errors([exact_clause])
        self.assertTrue(
            any(
                "verbatim_source_clause is required for exact-clause atom identity"
                in error
                for error in missing_clause
            ),
            missing_clause,
        )

        whole_quote = dict(exact_clause)
        whole_quote["identity_schema"] = 2
        whole_quote["verbatim_source_clause"] = "A clause is not valid in schema two."
        wrong_schema = GATE.source_claim_atoms_validation_errors([whole_quote])
        self.assertTrue(
            any(
                "verbatim_source_clause requires identity_schema 3" in error
                for error in wrong_schema
            ),
            wrong_schema,
        )

    def test_compound_theorem_fails_when_general_cutoff_atom_omits_route(self) -> None:
        atoms = self.valid_atoms()
        atoms[0].pop("reviewed_lean_route")
        self.write_map(self.map_payload(atoms))

        atom_messages = [
            finding.message
            for finding in GATE.source_claim_atom_inventory_findings(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any(
                "source_claim_atoms[0].reviewed_lean_route must be a nonempty string"
                in message
                for message in atom_messages
            ),
            atom_messages,
        )
        route_messages = [finding.message for finding in self.route_findings()]
        self.assertTrue(
            any("source-claim atom contract is malformed" in message for message in route_messages),
            route_messages,
        )

    def test_v10_rejects_historical_high_ratio_only_row_without_cutoff_inventory(self) -> None:
        """A compound source theorem cannot retain only its convenient subclause.

        This is the GN21 Theorem 3 regression shape: the old row gave credit to
        the high-ratio accept-all conclusion while omitting the general
        existential cutoff conclusion.  The source claim in this fixture names
        the existential quantifier and both cutoff endpoints, whereas the
        reviewed Lean route names are intentionally opaque.
        """

        payload = self.map_payload(self.valid_atoms())
        item = payload["items"]["source_theorem_one"]
        assert isinstance(item, dict)
        del item["source_claim_atoms"]
        item["lean_declarations"] = ["Fixture.proof_beta"]
        self.write_map(payload)

        atom_messages = [
            finding.message
            for finding in GATE.source_claim_atom_inventory_findings(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any(
                "theorem-like source item must enumerate source_claim_atoms"
                in message
                for message in atom_messages
            ),
            atom_messages,
        )

    def test_atom_inventory_follows_normal_deep_and_corrected_scope(self) -> None:
        def messages_for(
            mode: str,
            *,
            title: str | None = None,
            corrected: bool = False,
            legacy_corrected: bool = False,
            excluded: bool = False,
            source_kind: str = "claim",
        ) -> list[str]:
            item: dict[str, object] = {
                "source_kind": source_kind,
                "statement": (
                    "The proof next records an intermediate inequality used only "
                    "inside the named theorem."
                ),
            }
            if title is not None:
                item["title"] = title
            if corrected:
                item["coverage_status"] = "corrected_source_statement"
            if legacy_corrected:
                item["source_status"] = "corrected_source_statement"
            if excluded:
                item["user_approved_scope_exclusion"] = {
                    "schema": 1,
                    "approval_kind": "explicit_user_instruction",
                }
            self.write_map(
                {
                    "source_coverage_mode": mode,
                    "source_claim_atoms_schema": 1,
                    "items": {"opaque_navigation_key": item},
                }
            )
            return [
                finding.message
                for finding in GATE.source_claim_atom_inventory_findings(
                    self.paper, "formalized"
                )
            ]

        ordinary = messages_for("named_theoretical_statements")
        self.assertFalse(
            any("must enumerate source_claim_atoms" in message for message in ordinary),
            ordinary,
        )

        deep = messages_for("deep_paper_with_all_prose_claims")
        self.assertTrue(
            any("must enumerate source_claim_atoms" in message for message in deep),
            deep,
        )

        named = messages_for(
            "named_theoretical_statements", title="Claim 4. Intermediate inequality"
        )
        self.assertTrue(
            any("must enumerate source_claim_atoms" in message for message in named),
            named,
        )

        corrected = messages_for("named_theoretical_statements", corrected=True)
        self.assertTrue(
            any("must enumerate source_claim_atoms" in message for message in corrected),
            corrected,
        )

        legacy_corrected = messages_for(
            "named_theoretical_statements", legacy_corrected=True
        )
        self.assertTrue(
            any(
                "must enumerate source_claim_atoms" in message
                for message in legacy_corrected
            ),
            legacy_corrected,
        )

        excluded = messages_for(
            "deep_paper_with_all_prose_claims",
            excluded=True,
            source_kind="example",
        )
        self.assertFalse(
            any("must enumerate source_claim_atoms" in message for message in excluded),
            excluded,
        )

    def test_conclusion_carrying_record_cannot_satisfy_an_atom_route(self) -> None:
        atoms = self.valid_atoms()
        atoms[1]["reviewed_lean_route"] = "Fixture.ConclusionRecord"
        self.write_status(
            include_names=[
                "Fixture.proof_alpha",
                "Fixture.proof_beta",
                "Fixture.ConclusionRecord",
            ]
        )
        self.write_map(self.map_payload(atoms))

        messages = [finding.message for finding in self.route_findings()]
        self.assertTrue(
            any(
                "must be configured Spec-paired theorem/lemma result endpoints"
                in message
                for message in messages
            ),
            messages,
        )

    def test_v10_atom_requirement_needs_the_versioned_source_contract(self) -> None:
        self.write_map(self.map_payload(self.valid_atoms()))
        status = {
            "review_surface": {
                "llm_statement_review": {
                    "require_explicit_source_routes": True,
                }
            }
        }

        errors = GATE.current_v10_semantic_source_lane_errors(self.paper, status)
        self.assertIn(
            "review_surface.llm_statement_review.require_source_claim_atoms "
            "must be true when the source map opts into source_claim_atoms",
            errors,
        )

        status["review_surface"]["llm_statement_review"][
            "require_source_claim_atoms"
        ] = True
        errors = GATE.current_v10_semantic_source_lane_errors(self.paper, status)
        self.assertNotIn(
            "review_surface.llm_statement_review.require_source_claim_atoms "
            "must be true when the source map opts into source_claim_atoms",
            errors,
        )

    def test_explicit_definition_atom_participates_in_the_strict_route(self) -> None:
        """Definitions stay optional unless the map explicitly atomizes one.

        This keeps the normal theorem-like inventory narrow while allowing a
        source definition with a complete atom/Spec binding to furnish the
        source-first context needed by a strict occurrence closure.
        """

        statement_map = {"source_claim_atoms_schema": 1}
        self.assertFalse(
            SOURCE_RECORD.source_claim_atom_authoritative_for_item(
                statement_map,
                {"source_kind": "definition"},
            )
        )
        self.assertTrue(
            SOURCE_RECORD.source_claim_atom_authoritative_for_item(
                statement_map,
                {
                    "source_kind": "definition",
                    "source_claim_atoms": self.valid_atoms()[:1],
                },
            )
        )
        self.assertFalse(
            SOURCE_RECORD.source_claim_atom_authoritative_for_item(
                statement_map,
                {
                    "source_kind": "theorem",
                    "source_status": "support_only",
                },
            )
        )

    def test_support_only_theorem_is_not_forced_into_a_direct_claim_route(self) -> None:
        """Support inventory is provenance, not a second source result endpoint."""

        payload = self.map_payload(self.valid_atoms())
        items = payload["items"]
        assert isinstance(items, dict)
        items["proof_support"] = {
            "source_kind": "proposition",
            "source_status": "support_only",
            "source_location": "source.txt:1",
            "statement": "An intermediate source proposition used only in the proof route.",
            # Historic navigation must not become a direct theorem/Spec
            # obligation simply because the source passage is byte-pinned.
            "support_lean_declarations": ["Fixture.historic_support_name"],
        }
        self.write_map(payload)

        messages = [finding.message for finding in self.route_findings()]
        self.assertFalse(
            any(
                "proof_support" in message
                and (
                    "source inventory names" in message
                    or "source-claim atom contract is malformed" in message
                )
                for message in messages
            ),
            messages,
        )


if __name__ == "__main__":
    unittest.main()
