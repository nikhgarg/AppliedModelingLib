#!/usr/bin/env python3
"""Regressions for the location-neutral final holistic audit surface."""

from __future__ import annotations

import copy
import hashlib
import unittest
from pathlib import Path
from unittest import mock

from scripts import final_holistic_audit_surface as holistic_surface
from scripts import lean_signature_manifest as lean_manifest
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_APPROVAL_PROTOCOL,
    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD,
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_record_digest,
    corrected_target_review_digest,
)
from scripts.final_holistic_audit_surface import (
    build_final_holistic_audit_surface,
    final_holistic_audit_surface_sha256,
)
from scripts.semantic_prerequisite_projection import (
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
)
from scripts.source_review_input import source_semantic_input_bundle
from scripts.v11_screening_contract import V11_SCREENING_PROMPT_VERSION


def sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def anchor(text: str, line: int) -> dict[str, object]:
    return {
        "path": "sources/Fixture.txt",
        "line_start": line,
        "line_end": line,
        "quoted_text": text,
        "quoted_text_sha256": sha(text),
    }


class FinalHolisticAuditSurfaceTests(unittest.TestCase):
    @staticmethod
    def approved_corrected_target(
        artifact_path: str = "docs/SOURCE_CLARIFICATIONS.md",
    ) -> dict[str, object]:
        excerpt = (
            "The task owner approved this exact corrected mathematical target "
            "for the formalization."
        )
        statement = "The corrected checked result is true."
        target: dict[str, object] = {
            "schema": 1,
            "statement": statement,
            "governing_defect_ids": ["FIXTURE-DEFECT-1"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": "sources/Fixture.txt:4",
            "archival_source_quote_sha256": sha(
                "Theorem 1. The checked result is true."
            ),
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-09-05",
                "reference": "Approved corrected target.",
                "target_statement_sha256": sha(statement),
                "artifact_path": artifact_path,
                "artifact_protocol": CORRECTED_TARGET_APPROVAL_PROTOCOL,
                "artifact_excerpt": excerpt,
                "artifact_excerpt_sha256": sha(excerpt),
            },
        }
        target["corrected_target_sha256"] = corrected_target_record_digest(target)
        target["corrected_target_review_sha256"] = corrected_target_review_digest(
            target
        )
        return target

    def test_frozen_historical_source_item_policy_preimages(self) -> None:
        item = {
            "source_kind": "definition",
            "statement": "a definition",
            "source_status": "support_only",
        }
        self.assertEqual(
            holistic_surface._historical_source_item_coverage_sha256(item),
            "4e977739ca2ec88950ee09e2fc74047226f019986f8170c11bc6a5b744698337",
        )
        item["source_status"] = "source_model_convention"
        self.assertEqual(
            holistic_surface._historical_source_item_coverage_sha256(item),
            "5aefacd4023c4b2c5fc77041dfa4d9159f0623a7e87d2fd1c01a68525db3193b",
        )

        corrected_item = {
            "source_kind": "theorem",
            "statement": "The archival statement has a documented defect.",
            "claim_bearing": True,
            "corrected_target": self.approved_corrected_target(),
        }
        self.assertEqual(
            holistic_surface._historical_source_item_coverage_sha256(
                corrected_item
            ),
            "897a264cb9cbf17c35e56002f81954c2cdc399af7228df07ee6e53ea702da8d8",
        )

    def test_historical_source_assurance_reads_only_exact_old_rows(self) -> None:
        fixture = self.fixture()
        projection = holistic_surface.final_holistic_source_assurance_projection(
            self.build(fixture)
        )
        before = copy.deepcopy(projection)
        legacy = copy.deepcopy(projection)
        legacy["schema"] = 1
        del legacy["source_inventory"]["scope_relations"]
        for row in legacy["source_inventory"]["items"]:
            del row["corrected_target_review_sha256"]
        legacy["source_inventory"]["items"].sort(key=holistic_surface._digest)
        expected = holistic_surface._digest(legacy)
        candidates = holistic_surface.historical_final_holistic_source_assurance_sha256s(
            projection, source_map=fixture["source_map"]
        )
        self.assertIn(expected, candidates)
        self.assertEqual(before, projection)
        changed = copy.deepcopy(projection)
        changed["source_inventory"]["items"][0]["future_semantic_field"] = False
        self.assertFalse(
            holistic_surface.historical_final_holistic_source_assurance_sha256s(
                changed, source_map=fixture["source_map"]
            )
        )

    def test_original_locator_authenticates_only_the_exact_old_assurance(
        self,
    ) -> None:
        fixture = self.fixture()
        projection = holistic_surface.final_holistic_source_assurance_projection(
            self.build(fixture)
        )
        mode = projection["source_coverage_mode"]
        source_map = copy.deepcopy(fixture["source_map"])
        item = source_map["items"]["theorem1"]
        original_item_sha = holistic_surface.source_item_coverage_sha256(item, mode)

        old_target = self.approved_corrected_target(
            "docs/SOURCE_CLARIFICATIONS.md"
        )
        old_item = copy.deepcopy(item)
        old_item["corrected_target"] = old_target
        current_item = copy.deepcopy(old_item)
        current_approval = current_item["corrected_target"]["approval"]
        current_approval["artifact_path"] = "audit/SOURCE_TARGET_STATEMENTS.md"
        current_approval[CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD] = (
            "docs/SOURCE_CLARIFICATIONS.md"
        )
        current_sha = holistic_surface.source_item_coverage_sha256(current_item, mode)
        self.assertEqual(
            current_sha,
            holistic_surface.source_item_coverage_sha256(old_item, mode),
        )

        for row in projection["source_inventory"]["items"]:
            if row["source_item_semantic_sha256"] == original_item_sha:
                row["source_item_semantic_sha256"] = current_sha
                row["corrected_target_review_sha256"] = old_target[
                    "corrected_target_review_sha256"
                ]
        projection["source_inventory"]["items"].sort(
            key=holistic_surface._digest
        )
        source_map["items"]["theorem1"] = current_item

        baseline_inventory = {
            key: value
            for key, value in projection["source_inventory"].items()
            if key != "scope_relations"
        }
        old_rows = copy.deepcopy(baseline_inventory["items"])
        for row in old_rows:
            if row["source_item_semantic_sha256"] == current_sha:
                row["source_item_semantic_sha256"] = (
                    holistic_surface._historical_source_item_coverage_sha256(
                        old_item
                    )
                )
        old_rows.sort(key=holistic_surface._digest)
        accepted_old_assurance = holistic_surface._digest(
            dict(
                projection,
                schema=1,
                source_inventory=dict(baseline_inventory, items=old_rows),
            )
        )
        self.assertIn(
            accepted_old_assurance,
            holistic_surface.historical_final_holistic_source_assurance_sha256s(
                projection, source_map=source_map
            ),
        )

        forged_map = copy.deepcopy(source_map)
        forged_map["items"]["theorem1"]["corrected_target"]["approval"][
            CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
        ] = "docs/FORGED_SOURCE_CLARIFICATIONS.md"
        self.assertNotIn(
            accepted_old_assurance,
            holistic_surface.historical_final_holistic_source_assurance_sha256s(
                projection, source_map=forged_map
            ),
        )

        malformed_map = copy.deepcopy(source_map)
        malformed_item = malformed_map["items"]["theorem1"]
        malformed_item["corrected_target"]["approval"][
            CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
        ] = "../docs/SOURCE_CLARIFICATIONS.md"
        malformed_projection = copy.deepcopy(projection)
        for row in malformed_projection["source_inventory"]["items"]:
            if row["source_item_semantic_sha256"] == current_sha:
                row["source_item_semantic_sha256"] = (
                    holistic_surface.source_item_coverage_sha256(
                        malformed_item, mode
                    )
                )
        with self.assertRaisesRegex(
            holistic_surface.FinalHolisticAuditSurfaceError,
            "historical corrected-target locator is malformed",
        ):
            holistic_surface.historical_final_holistic_source_assurance_sha256s(
                malformed_projection, source_map=malformed_map
            )

        for field in ("status_semantics", "source_proof_fidelity_semantics"):
            with self.subTest(mutated_assurance=field):
                changed = copy.deepcopy(projection)
                changed[field] = {"forged": True}
                self.assertNotIn(
                    accepted_old_assurance,
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        changed, source_map=source_map
                    ),
                )

    def test_frozen_schema1_assurance_preimages_never_issue_schema2(self) -> None:
        fixture = self.fixture()
        fixture["source_map"]["items"]["model"]["source_status"] = "support_only"
        projection = holistic_surface.final_holistic_source_assurance_projection(
            self.build(fixture)
        )
        candidates = holistic_surface.historical_final_holistic_source_assurance_sha256s(
            projection, source_map=fixture["source_map"]
        )
        # The baseline value was independently checked against a94ab49b's
        # producer; the other values freeze its two older data preimages.
        self.assertEqual(candidates, frozenset({
            "286d265ec78159c69dcd7bf612b596f4f224ee9ea220966ac23ab4515016cb30",
            "b487545180618f0469cea9eeee63471e3bdd8e38265aeca98bdeb69729542309",
            "f80de3f308ccc792a4228d1654c864ac102e5a92d740668d42d514e0098cc3ec",
        }))
        self.assertEqual(projection["schema"], 2)
        self.assertNotIn(
            holistic_surface.final_holistic_source_assurance_projection_sha256(projection),
            candidates,
        )
        old = copy.deepcopy(projection)
        old["schema"] = 1
        del old["source_inventory"]["scope_relations"]
        self.assertEqual(
            holistic_surface.final_holistic_source_assurance_projection_sha256(old),
            "286d265ec78159c69dcd7bf612b596f4f224ee9ea220966ac23ab4515016cb30",
        )

    def test_schema2_assurance_requires_exact_scope_shape(self) -> None:
        original = holistic_surface.final_holistic_source_assurance_projection(
            self.build(self.fixture())
        )
        for mutation in ("missing", "malformed", "future_field", "future_schema"):
            with self.subTest(mutation=mutation):
                changed = copy.deepcopy(original)
                if mutation == "missing":
                    del changed["source_inventory"]["scope_relations"]
                elif mutation == "malformed":
                    changed["source_inventory"]["scope_relations"] = None
                elif mutation == "future_field":
                    changed["source_inventory"]["scope_relations"][0]["unknown"] = False
                else:
                    changed["schema"] = 3
                with self.assertRaises(holistic_surface.FinalHolisticAuditSurfaceError):
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        changed, source_map=self.fixture()["source_map"]
                    )

    def test_historical_assurance_preserves_all_other_current_controls(self) -> None:
        fixture = self.fixture()
        projection = holistic_surface.final_holistic_source_assurance_projection(
            self.build(fixture)
        )
        accepted = holistic_surface.historical_final_holistic_source_assurance_sha256s(
            projection, source_map=fixture["source_map"]
        )
        for field in (
            "source_corpus", "status_semantics", "source_proof_fidelity_semantics"
        ):
            with self.subTest(field=field):
                changed = copy.deepcopy(projection)
                changed[field] = {"changed": True}
                self.assertTrue(accepted.isdisjoint(
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        changed, source_map=fixture["source_map"]
                    )
                ))
        for field, value in (
            ("statement", "A different mathematical statement."),
            ("corrected_target", {"statement": "A changed approved correction."}),
            ("unknown_semantic_field", "new obligation"),
            ("source_status", "support_only"),
            ("source_status", "quarantined_source_defect"),
            ("source_kind", "assumption"),
        ):
            with self.subTest(source_field=field):
                changed_map = copy.deepcopy(fixture["source_map"])
                changed_map["items"]["theorem1"][field] = value
                self.assertFalse(
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        projection, source_map=changed_map
                    )
                )
                # Also reconstruct the changed current row: rejecting only a
                # stale map/projection pair would not test historical reuse.
                changed = copy.deepcopy(projection)
                mode = projection["source_coverage_mode"]
                original_sha = holistic_surface.source_item_coverage_sha256(
                    fixture["source_map"]["items"]["theorem1"], mode
                )
                for row in changed["source_inventory"]["items"]:
                    if row["source_item_semantic_sha256"] == original_sha:
                        row["source_item_semantic_sha256"] = holistic_surface.source_item_coverage_sha256(
                            changed_map["items"]["theorem1"], mode
                        )
                changed["source_inventory"]["scope_relations"] = (
                    holistic_surface._source_scope_relations_projection(changed_map, mode)
                )
                self.assertTrue(accepted.isdisjoint(
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        changed, source_map=changed_map
                    )
                ))

    def test_historical_policy_rejects_new_true_or_unknown_policy_fields(self) -> None:
        from scripts import source_coverage_scope as scope

        item = {
            "source_kind": "open_problem", "claim_bearing": False,
            "source_scope_classification": "source_resolved_within_paper_observation",
            "coverage_status": "subsumed_by_selected_result",
            "protocol_role": "subsumed_by_selected_result",
            "subsumed_by_source_item": "theorem1",
        }
        self.assertEqual(
            holistic_surface._historical_source_item_coverage_sha256(item), ""
        )
        item = {"source_kind": "definition", "source_status": "support_only"}
        policy = scope.source_item_direct_status_policy_projection(item)
        policy["effective_route_policy"]["future_policy"] = False
        with mock.patch.object(scope, "source_item_direct_status_policy_projection", return_value=policy):
            self.assertEqual(
                holistic_surface._historical_source_item_coverage_sha256(item), ""
            )
        with mock.patch.object(scope, "SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA", 7):
            self.assertEqual(
                holistic_surface._historical_source_item_coverage_sha256(item), ""
            )

    def fixture(self) -> dict[str, object]:
        paper = "FixturePaper"
        spec = "FixturePaper.claimSpec"
        proof = "FixturePaper.claim_proof"
        paper_definition = "FixturePaper.Model"
        library_definition = "AppliedModelingLib.Shared.Primitive"
        claim_atom = {
            "ref": "result",
            "role": "conclusion",
            "canonical": {"tag": "const", "name": "True"},
            "display": "True",
        }
        claim = {
            "schema": "1",
            "signature": {
                "schema": str(lean_manifest.MANIFEST_SCHEMA),
                "declaration_kind": "definition",
                "conclusion_mode": "type_and_value",
                "atoms": [claim_atom],
            },
            "transparent_value_presentation_telescope": {
                "schema": lean_manifest.TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_SCHEMA,
                "reduction": lean_manifest.TRANSPARENT_VALUE_PRESENTATION_TELESCOPE_REDUCTION,
                "atoms": [claim_atom],
            },
        }
        claim_inventory = {
            "semantic_review_claims": {
                "schema": "1",
                "items": [{"declaration": spec, "claim": claim}],
                "errors": [],
            }
        }
        claim_surface = lean_manifest.semantic_review_claim_surfaces_from_inventory(
            claim_inventory, expected_declarations={spec}
        )[spec]

        result_text = "Theorem 1. The checked result is true."
        model_text = "Definition. A model is the fixture carrier."
        library_text = "Definition. The primitive is the fixture operation."
        result_anchor = anchor(result_text, 4)
        source_claim_atoms = [
            {
                "id": "theorem1.result",
                "source_locator": "sources/Fixture.txt:4",
                "semantic_claim": "The checked result is true.",
                "reviewed_lean_route": proof,
                "source_quote_sha256": result_anchor["quoted_text_sha256"],
                "identity_schema": 2,
            }
        ]
        source_items = {
            "theorem1": {
                "source_kind": "theorem",
                "source_location": "sources/Fixture.txt:4",
                "statement": "The checked result is true.",
                "claim_bearing": True,
                "source_anchor_evidence": [result_anchor],
                "source_claim_atoms": source_claim_atoms,
                "lean_declarations": [spec],
                "semantic_contract": {
                    "spec_declaration": spec,
                    "evidence_declaration": proof,
                    "evidence_mode": "proves",
                    "semantic_shape": "plain",
                },
            },
            "model": {
                "source_kind": "definition",
                "source_location": "sources/Fixture.txt:2",
                "statement": "A model is the fixture carrier.",
                "claim_bearing": True,
                "source_anchor_evidence": [anchor(model_text, 2)],
                "inventory_role": "source_semantic_declaration",
                "lean_declarations": [paper_definition],
            },
            "primitive": {
                "source_kind": "definition",
                "source_location": "sources/Fixture.txt:3",
                "statement": "The primitive is the fixture operation.",
                "claim_bearing": True,
                "source_anchor_evidence": [anchor(library_text, 3)],
                "inventory_role": "source_semantic_declaration",
                "lean_declarations": [library_definition],
            },
        }
        source_map = {
            "paper": paper,
            "schema": 1,
            "source_artifact_sha256": sha("complete source corpus"),
            "source_version": "fixture source v1",
            "source_coverage_mode": "named_theoretical_statements",
            "semantic_contract_schema": 2,
            "semantic_route_schema": 2,
            "source_claim_atoms_schema": 2,
            "source_spec_correspondence_schema": 2,
            "paper_semantic_prerequisite_sources": {
                paper_definition: "model",
            },
            "library_semantic_prerequisite_sources": {
                library_definition: "primitive",
            },
            "items": source_items,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "fixture reviewer",
                "method": "complete source-only read",
                "validated_at": "2026-08-29T00:00:00Z",
                "source_artifact_sha256": sha("complete source corpus"),
                "discovered_named_result_sha256": sha("named inventory"),
                "discovered_candidate_presentation_sha256": sha("candidate inventory"),
                "discovered_prose_definition_sha256": sha("definition inventory"),
                "candidate_presentations": [],
                "prose_definition_presentations": [],
            },
        }
        inventory = {
            "transparent_spec_displays": {
                "schema": "2",
                "items": [
                    {
                        "specification": spec,
                        "complete": True,
                        "expansion_count": "0",
                        "expanded_declarations": [],
                        "prerequisite_declarations": [paper_definition],
                        "library_declarations": [library_definition],
                        "erased_proof_declarations": [],
                        "blocked_declarations": [],
                        "display": "True",
                    }
                ],
            },
            "paper_prerequisite_displays": {
                "schema": "2",
                "items": [
                    {
                        "declaration": paper_definition,
                        "declaration_kind": "definition",
                        "direct_paper_declarations": [],
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                        "display": "Prop",
                        "root_expanded": True,
                    }
                ],
            },
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": library_definition,
                        "declaration_kind": "definition",
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                        "display": "Prop",
                        "review_owner_declaration": library_definition,
                        "root_expanded": True,
                        "source_module": "AppliedModelingLib.Shared",
                        "source_line_start": 10,
                        "source_column_start": 0,
                        "source_line_end": 10,
                        "source_column_end": 20,
                    }
                ],
            },
            "semantic_signatures": {
                "schema": "1",
                "items": [
                    {
                        "declaration": spec,
                        "elaborated_signature_sha256": claim_surface[
                            "manifest_sha256"
                        ],
                    },
                    {
                        "declaration": paper_definition,
                        "elaborated_signature_sha256": sha("paper definition"),
                    },
                    {
                        "declaration": library_definition,
                        "elaborated_signature_sha256": sha("library definition"),
                    },
                ],
                "errors": [],
            },
            **claim_inventory,
            "semantic_contracts": [
                {
                    "specification": spec,
                    "evidence": proof,
                    "mode": "proves",
                    "matches": True,
                    "evidence_is_unsafe": False,
                    "evidence_value_has_sorry": False,
                    "evidence_axiom_closure_checked": True,
                    "evidence_axiom_closure": ["Classical.choice"],
                }
            ],
        }
        graph = {"paper": paper, "inventory": inventory}

        def bundle(item: str) -> str:
            _text, digest, error = source_semantic_input_bundle(
                source_items[item], require_context_roles=True
            )
            self.assertFalse(error)
            return digest

        screening = {
            "schema": 3,
            "paper": paper,
            "audit_kind": "raw_source_to_expanded_spec",
            "prompt_version": V11_SCREENING_PROMPT_VERSION,
            "validator": "fixture reviewer",
            "validated_at": "2026-08-29T00:00:00Z",
            "comment": "fixture",
            "items": {
                spec: {
                    "judgment": "matches",
                    "semantic_target_declaration": spec,
                    "source_item": "theorem1",
                    "source_input_bundle_sha256": bundle("theorem1"),
                    "review_claim_manifest_sha256": claim_surface[
                        "manifest_sha256"
                    ],
                    "review_claim_atoms_sha256": claim_surface[
                        "claim_atoms_sha256"
                    ],
                    "source_review_target_sha256": sha("review target"),
                }
            },
        }
        paper_ledger = {
            "schema": 1,
            "paper": paper,
            "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
            "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
            "items": {
                paper_definition: {
                    "judgment": "matches",
                    "paper_declaration": paper_definition,
                    "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                    "elaborated_signature_sha256": sha("paper definition"),
                    "source_item": "model",
                    "source_input_bundle_sha256": bundle("model"),
                }
            },
        }
        library_ledger = {
            "schema": 1,
            "paper": paper,
            "prompt_version": REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
            "target_protocol": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
            "items": {
                library_definition: {
                    "judgment": "matches",
                    "library_declaration": library_definition,
                    "library_semantic_target_protocol": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
                    "elaborated_signature_sha256": sha("library definition"),
                    "source_item": "primitive",
                    "source_input_bundle_sha256": bundle("primitive"),
                }
            },
        }
        status_projection = {
            "schema": 1,
            "paper": paper,
            "status": {
                "status": "formalized",
                "main_caveat": "",
                "review_surface": {"assumption_policy": "strict"},
            },
        }
        return {
            "paper": paper,
            "source_map": source_map,
            "graph": graph,
            "status_projection": status_projection,
            "source_spec_screening": screening,
            "paper_prerequisite_ledger": paper_ledger,
            "library_prerequisite_ledger": library_ledger,
            "source_proof_fidelity": {
                "schema": 2,
                "paper": paper,
                "defects": [],
                "reviewed_proof_scopes": [],
            },
        }

    def build(self, fixture: dict[str, object]) -> dict[str, object]:
        return build_final_holistic_audit_surface(**fixture)  # type: ignore[arg-type]

    def policy_fixture(self) -> dict[str, object]:
        fixture = self.fixture()
        source_map = fixture["source_map"]
        review = source_map["source_named_result_inventory_review"]
        appendix_candidate = {
            "schema": 1,
            "id": "appendix_candidate",
            "presentation_label": "Lemma A",
            "visible_kind": "lemma",
            "scope_disposition": "normal_theory",
            "semantic_basis": "An unrelated appendix claim.",
            "discovery_basis": "complete source-only inventory",
            "source_anchor": anchor("Lemma A. An unrelated appendix claim.", 5),
        }
        review["candidate_presentations"] = [appendix_candidate]
        source_map["closeout_review_policy"] = {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": 1,
            "scheduling": {
                "initial_semantic_review": ["reviewer-a"],
                "final_adversarial_review": ["reviewer-b"],
            },
        }

        def region(
            region_id: str, kind: str, line_start: int, line_end: int, text: str
        ) -> dict[str, object]:
            return {
                "id": region_id,
                "kind": kind,
                "source_anchor": {
                    "path": "sources/Fixture.txt",
                    "line_start": line_start,
                    "line_end": line_end,
                    "quoted_text": text,
                    "quoted_text_sha256": sha(text),
                },
            }

        review["source_region_partition"] = {
            "schema": 1,
            "complete": True,
            "validator": "fixture source curator",
            "method": "complete line partition",
            "validated_at": "2026-09-05T12:00:00Z",
            "source_artifact_sha256": source_map["source_artifact_sha256"],
            "canonical_source_path": "sources/Fixture.txt",
            "regions": [
                region("main_model", "main_text", 1, 2, "title\nmodel"),
                region("appendix_definition", "appendix", 3, 3, "primitive"),
                region("main_result", "main_text", 4, 4, "theorem"),
                region("appendix_other", "appendix", 5, 5, "appendix"),
            ],
            "source_item_regions": {
                "model": "main_model",
                "primitive": "appendix_definition",
                "theorem1": "main_result",
            },
            "candidate_presentation_regions": {
                "appendix_candidate": "appendix_other"
            },
            "prose_definition_presentation_regions": {},
            "promoted_source_items": [],
        }
        return fixture

    def test_policy_surface_separates_full_assurance_from_primary_review(self) -> None:
        fixture = self.policy_fixture()
        surface = self.build(fixture)
        self.assertTrue(
            holistic_surface.final_holistic_audit_surface_contract_is_supported(
                surface
            )
        )
        self.assertEqual(surface["schema"], 3)
        self.assertEqual(
            len(
                surface["source_inventory"]["named_result_inventory"][
                    "candidate_presentations"
                ]
            ),
            1,
        )
        self.assertEqual(
            surface["terminal_review"]["source_inventory"][
                "named_result_inventory"
            ]["candidate_presentations"],
            [],
        )
        # The appendix definition governs the main Spec through a Lean-emitted
        # semantic edge, so it remains in the primary terminal review.
        self.assertEqual(
            {row["role"] for row in surface["terminal_review"]["semantic_review_rows"]},
            {"source_result", "paper_prerequisite", "library_prerequisite"},
        )

    def test_v2_assurance_is_stable_under_reader_prose_and_visibility(self) -> None:
        fixture = self.policy_fixture()
        original_surface = self.build(fixture)
        original_v1 = holistic_surface.final_holistic_source_assurance_projection(
            original_surface
        )
        original_v2 = holistic_surface.final_holistic_source_assurance_v2_projection(
            original_v1
        )

        changed = copy.deepcopy(fixture)
        changed_status = changed["status_projection"]["status"]
        changed_status["main_caveat"] = "New public explanation."
        changed_status["human_summary"] = "New reader summary."
        changed_status["repository_visibility"] = "public"
        changed_v1 = holistic_surface.final_holistic_source_assurance_projection(
            self.build(changed)
        )
        changed_v2 = holistic_surface.final_holistic_source_assurance_v2_projection(
            changed_v1
        )
        self.assertNotEqual(
            holistic_surface.final_holistic_source_assurance_projection_sha256(
                original_v1
            ),
            holistic_surface.final_holistic_source_assurance_projection_sha256(
                changed_v1
            ),
        )
        self.assertEqual(
            holistic_surface.final_holistic_source_assurance_v2_projection_sha256(
                original_v2
            ),
            holistic_surface.final_holistic_source_assurance_v2_projection_sha256(
                changed_v2
            ),
        )

    def test_v2_assurance_invalidates_every_semantic_control_family(self) -> None:
        v1 = holistic_surface.final_holistic_source_assurance_projection(
            self.build(self.policy_fixture())
        )
        original = holistic_surface.final_holistic_source_assurance_v2_projection(
            v1
        )
        original_sha = (
            holistic_surface.final_holistic_source_assurance_v2_projection_sha256(
                original
            )
        )

        mutations = []
        changed = copy.deepcopy(v1)
        changed["status_semantics"]["formalization_status"] = "partial"
        mutations.append(("formalization status", changed))
        changed = copy.deepcopy(v1)
        changed["status_semantics"]["assumption_policy"] = "permissive"
        mutations.append(("assumption policy", changed))
        changed = copy.deepcopy(v1)
        changed["source_corpus"]["source_artifact_sha256"] = sha("new source")
        mutations.append(("source corpus", changed))
        changed = copy.deepcopy(v1)
        changed["source_inventory"]["items"][0][
            "corrected_target_review_sha256"
        ] = sha("new correction")
        mutations.append(("correction", changed))
        changed = copy.deepcopy(v1)
        changed["source_inventory"]["items"][0]["source_defect_ids"] = [
            "NEW-DEFECT"
        ]
        mutations.append(("defect", changed))
        changed = copy.deepcopy(v1)
        changed["source_proof_fidelity_semantics"] = {"changed": True}
        mutations.append(("fidelity", changed))
        changed = copy.deepcopy(v1)
        changed["review_policy_assurance"][
            "required_final_adversary_count"
        ] = 2
        mutations.append(("review policy", changed))
        changed = copy.deepcopy(v1)
        changed["source_region_partition"]["regions"][0][
            "source_quote_sha256"
        ] = sha("new source region")
        mutations.append(("source region partition", changed))

        for label, changed_v1 in mutations:
            with self.subTest(control=label):
                changed_v2 = (
                    holistic_surface.final_holistic_source_assurance_v2_projection(
                        changed_v1
                    )
                )
                self.assertNotEqual(
                    holistic_surface.final_holistic_source_assurance_v2_projection_sha256(
                        changed_v2
                    ),
                    original_sha,
                )

    def test_panel_count_and_model_schedule_do_not_change_one_review_identity(self) -> None:
        fixture = self.policy_fixture()
        original = self.build(fixture)

        changed_count = copy.deepcopy(fixture)
        changed_count["source_map"]["closeout_review_policy"][
            "required_final_adversary_count"
        ] = 2
        count_surface = self.build(changed_count)
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(count_surface),
        )
        self.assertNotEqual(
            holistic_surface.final_holistic_source_assurance_sha256(original),
            holistic_surface.final_holistic_source_assurance_sha256(count_surface),
        )

        changed_schedule = copy.deepcopy(fixture)
        changed_schedule["source_map"]["closeout_review_policy"]["scheduling"][
            "final_adversarial_review"
        ] = ["reviewer-c"]
        schedule_surface = self.build(changed_schedule)
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(schedule_surface),
        )
        self.assertEqual(
            holistic_surface.final_holistic_source_assurance_sha256(original),
            holistic_surface.final_holistic_source_assurance_sha256(
                schedule_surface
            ),
        )

    def test_appendix_only_change_preserves_primary_review_but_not_assurance(self) -> None:
        original = self.build(self.policy_fixture())
        changed = copy.deepcopy(original)
        changed["source_region_partition"]["regions"][-1][
            "source_quote_sha256"
        ] = sha("changed appendix")
        changed["source_inventory"]["named_result_inventory"][
            "candidate_presentations"
        ][0]["semantic_basis_sha256"] = sha("changed appendix meaning")
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(changed),
        )
        self.assertNotEqual(
            holistic_surface.final_holistic_source_assurance_sha256(original),
            holistic_surface.final_holistic_source_assurance_sha256(changed),
        )

    def test_proof_only_appendix_dependency_is_not_promoted(self) -> None:
        fixture = self.policy_fixture()
        spec_display = fixture["graph"]["inventory"][
            "transparent_spec_displays"
        ]["items"][0]
        library = "AppliedModelingLib.Shared.Primitive"
        spec_display["library_declarations"] = []
        spec_display["erased_proof_declarations"] = [library]
        surface = self.build(fixture)
        roles = {
            row["role"]
            for row in surface["terminal_review"]["semantic_review_rows"]
        }
        self.assertNotIn("library_prerequisite", roles)

    def scope_fixture(self) -> dict[str, object]:
        fixture = self.fixture()
        items = fixture["source_map"]["items"]
        items["appendix_repeat"] = {
            "source_kind": "theorem", "claim_bearing": False,
            "statement": "The appendix repeats the main theorem.",
            "source_location": "sources/Fixture.txt:10",
            "source_anchor_evidence": [anchor("A repeated theorem.", 10)],
            "inventory_role": "source_presentation_alias",
            "source_presentation_alias": {
                "schema": 1, "canonical_source_item": "theorem1",
                "relation": "repeated_source_presentation",
                "semantic_basis": "The hypotheses and conclusion agree.",
                "validator": "independent reviewer",
                "validated_at": "2026-09-04T00:00:00Z",
                "label_relation": "source_explicit_renumbered_restatement",
                "source_restatement_evidence": anchor("This restates Theorem 1.", 11),
            },
        }
        items["conjecture"] = {
            "source_kind": "open_problem", "claim_bearing": False,
            "statement": "The theorem entails this conjecture.",
            "source_location": "sources/Fixture.txt:12",
            # Source-only scope review must not require a clean Lean-review bundle.
            "source_anchor_evidence": [anchor("corrupt \x0f PDF text", 12)],
            "source_scope_classification": "source_resolved_within_paper_observation",
            "coverage_status": "subsumed_by_selected_result",
            "protocol_role": "subsumed_by_selected_result",
            "scope_reason": "The source states that the theorem resolves it.",
            "subsumed_by_source_item": "theorem1",
        }
        items["other_target"] = {
            "source_kind": "theorem", "claim_bearing": False,
            "source_status": "support_only", "statement": "A different source result.",
            "source_location": "sources/Fixture.txt:13",
        }
        return fixture

    def test_unselected_scope_relations_bind_review_and_post_issuance_assurance(self) -> None:
        fixture = self.scope_fixture()
        original = self.build(fixture)
        accepted_assurance = holistic_surface.final_holistic_source_assurance_sha256(original)
        changes = (
            ("appendix_repeat", "source_presentation_alias", "semantic_basis",
             "Only the conclusion agrees; the appendix has a stronger premise."),
            ("appendix_repeat", "source_presentation_alias", "canonical_source_item", "other_target"),
            ("conjecture", None, "subsumed_by_source_item", "other_target"),
            ("conjecture", None, "scope_reason", "The resolution requires an added premise."),
            ("conjecture", None, "source_scope_classification", "source_declared_open_nonresult_observation"),
            ("conjecture", None, "unknown_semantic_annotation", "new obligation"),
            ("other_target", None, "statement", "A changed endpoint statement."),
        )
        for item_id, nested, field, value in changes:
            with self.subTest(item=item_id, field=field):
                changed = copy.deepcopy(fixture)
                item = changed["source_map"]["items"][item_id]
                (item[nested] if nested else item)[field] = value
                surface = self.build(changed)
                self.assertEqual(original["semantic_review_rows"], surface["semantic_review_rows"])
                self.assertNotEqual(
                    final_holistic_audit_surface_sha256(original),
                    final_holistic_audit_surface_sha256(surface),
                )
                projection = holistic_surface.final_holistic_source_assurance_projection(surface)
                self.assertNotEqual(
                    accepted_assurance,
                    holistic_surface.final_holistic_source_assurance_projection_sha256(projection),
                )
                self.assertNotIn(
                    accepted_assurance,
                    holistic_surface.historical_final_holistic_source_assurance_sha256s(
                        projection, source_map=changed["source_map"]
                    ),
                )

    def test_scope_relation_key_and_anchor_moves_are_navigation_only(self) -> None:
        fixture = self.scope_fixture()
        original = self.build(fixture)
        moved = copy.deepcopy(fixture)
        items = moved["source_map"]["items"]
        for key in ("theorem1", "appendix_repeat", "conjecture", "other_target"):
            items["renamed_" + key] = items.pop(key)
        alias = items["renamed_appendix_repeat"]["source_presentation_alias"]
        alias["canonical_source_item"] = "renamed_theorem1"
        items["renamed_conjecture"]["subsumed_by_source_item"] = "renamed_theorem1"
        for row in moved["source_spec_screening"]["items"].values():
            row["source_item"] = "renamed_theorem1"
        anchors = [alias["source_restatement_evidence"]]
        for item in items.values():
            item["source_location"] = "moved/source.txt:100"
            item["source_text_file"] = "moved/source.txt"
            anchors.extend(item.get("source_anchor_evidence", []))
        for source_anchor in anchors:
            source_anchor.update(path="moved/source.txt", line_start=100, line_end=100)
        self.assertEqual(original, self.build(moved))

    def test_scope_relations_reject_missing_endpoints(self) -> None:
        for item_id, nested, field in (
            ("appendix_repeat", "source_presentation_alias", "canonical_source_item"),
            ("conjecture", None, "subsumed_by_source_item"),
        ):
            with self.subTest(item=item_id):
                fixture = self.scope_fixture()
                item = fixture["source_map"]["items"][item_id]
                (item[nested] if nested else item)[field] = "missing"
                with self.assertRaises(holistic_surface.FinalHolisticAuditSurfaceError):
                    self.build(fixture)

    def test_operational_paths_ranges_and_displays_do_not_change_identity(self) -> None:
        fixture = self.fixture()
        original = self.build(fixture)
        moved = copy.deepcopy(fixture)
        library_row = moved["graph"]["inventory"]["library_prerequisite_displays"]["items"][0]  # type: ignore[index]
        library_row["source_module"] = "AppliedModeling.Shared"
        library_row["source_line_start"] = 300
        library_row["source_line_end"] = 300
        library_row["display"] = "  Prop  "
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(self.build(moved)),
        )

    def test_coherent_declaration_rename_does_not_change_identity(self) -> None:
        fixture = self.fixture()
        original = self.build(fixture)
        renamed = copy.deepcopy(fixture)
        replacements = {
            "FixturePaper.claimSpec": "Renamed.claimSpec",
            "FixturePaper.claim_proof": "Renamed.claim_proof",
            "FixturePaper.Model": "Renamed.Model",
            "AppliedModelingLib.Shared.Primitive": "AppliedModeling.Shared.Primitive",
        }

        def rewrite(value: object) -> object:
            if isinstance(value, str):
                return replacements.get(value, value)
            if isinstance(value, list):
                return [rewrite(child) for child in value]
            if isinstance(value, dict):
                return {
                    replacements.get(str(key), str(key)): rewrite(child)
                    for key, child in value.items()
                }
            return value

        renamed = rewrite(renamed)  # type: ignore[assignment]
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(self.build(renamed)),  # type: ignore[arg-type]
        )

    def test_source_routing_labels_do_not_change_identity(self) -> None:
        fixture = self.fixture()
        original = self.build(fixture)
        renamed = copy.deepcopy(fixture)
        source_map = renamed["source_map"]  # type: ignore[assignment]
        source_map["source_version"] = "a new descriptive label"
        source_map["source_named_result_inventory_review"]["schema"] = 99
        source_map["source_named_result_inventory_review"][
            "discovered_named_result_sha256"
        ] = sha("new parser-owned inventory digest")
        items = source_map["items"]
        items["renamed_theorem"] = items.pop("theorem1")
        screening_items = renamed["source_spec_screening"]["items"]
        next(iter(screening_items.values()))["source_item"] = "renamed_theorem"
        routes = renamed["source_map"]["items"]["renamed_theorem"]
        # The typed route is reconstructed from this current source-map item.
        self.assertEqual(routes["semantic_contract"]["spec_declaration"], "FixturePaper.claimSpec")
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(self.build(renamed)),
        )

    def test_whole_source_review_binds_unselected_named_candidates(self) -> None:
        fixture = self.fixture()
        original = self.build(fixture)
        changed = copy.deepcopy(original)
        inventory = changed["source_inventory"]["named_result_inventory"]
        inventory["candidate_presentations"].append(
            {
                "visible_kind": "theorem",
                "scope_disposition": "source_explicit_renumbered_restatement",
                "presentation_label_sha256": sha("Theorem 2"),
                "semantic_basis_sha256": sha("A claimed restatement of Theorem 1"),
                "discovery_basis": "source",
                "source_quote_sha256": sha("Every feasible matching is stable."),
            }
        )
        self.assertEqual(original["semantic_review_rows"], changed["semantic_review_rows"])
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(changed),
        )
        corrected = copy.deepcopy(changed)
        corrected["source_inventory"]["named_result_inventory"][
            "candidate_presentations"
        ][-1]["scope_disposition"] = "normal_theory"
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(changed),
            final_holistic_audit_surface_sha256(corrected),
        )

    def test_whole_source_review_cannot_inherit_a_different_corpus(self) -> None:
        original = self.build(self.fixture())
        changed = copy.deepcopy(original)
        changed["source_corpus"] = {
            "canonical_source_sha256": sha("New source edition"),
            "source_corpus_sha256s": [sha("New source edition")],
        }
        self.assertEqual(original["semantic_review_rows"], changed["semantic_review_rows"])
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(changed),
        )

    def test_source_semantics_and_proof_contract_change_identity(self) -> None:
        fixture = self.fixture()
        original_digest = final_holistic_audit_surface_sha256(self.build(fixture))

        source_changed = copy.deepcopy(fixture)
        source_changed["source_map"]["items"]["model"]["statement"] = (  # type: ignore[index]
            "A model is a different carrier."
        )
        self.assertNotEqual(
            original_digest,
            final_holistic_audit_surface_sha256(self.build(source_changed)),
        )

        proof_changed = copy.deepcopy(fixture)
        proof_changed["graph"]["inventory"]["semantic_contracts"][0][  # type: ignore[index]
            "evidence_axiom_closure"
        ] = ["Classical.choice", "Fixture.externalBoundary"]
        self.assertNotEqual(
            original_digest,
            final_holistic_audit_surface_sha256(self.build(proof_changed)),
        )

    def test_defect_routing_changes_review_identity_but_fidelity_controls_do_not(
        self,
    ) -> None:
        fixture = self.fixture()
        original_digest = final_holistic_audit_surface_sha256(self.build(fixture))

        routed = copy.deepcopy(fixture)
        routed["source_map"]["items"]["theorem1"]["source_defect_ids"] = [  # type: ignore[index]
            "FIXTURE-DEFECT-1"
        ]
        self.assertNotEqual(
            original_digest,
            final_holistic_audit_surface_sha256(self.build(routed)),
        )

        fidelity_changed = copy.deepcopy(fixture)
        fidelity_changed["source_proof_fidelity"]["defects"] = [  # type: ignore[index]
            {
                "id": "FIXTURE-DEFECT-1",
                "source_claim": "the printed statement is false",
                "resolution": "proved corrected target",
            }
        ]
        # Fidelity is independently bound by the terminal source-assurance
        # control.  Editing that control does not make the terminal reviewer
        # reread an unchanged selected source-to-Lean surface.
        self.assertEqual(
            original_digest,
            final_holistic_audit_surface_sha256(self.build(fidelity_changed)),
        )

    def test_corrected_target_statement_changes_identity(self) -> None:
        fixture = self.fixture()
        first = copy.deepcopy(fixture)
        first["source_map"]["items"]["theorem1"]["corrected_target"] = {  # type: ignore[index]
            "schema": 1,
            "statement": "The corrected checked result is true.",
            "governing_defect_ids": ["FIXTURE-DEFECT-1"],
        }
        first["source_map"]["items"]["theorem1"]["source_defect_ids"] = [  # type: ignore[index]
            "FIXTURE-DEFECT-1"
        ]
        _text, first_bundle, first_error = source_semantic_input_bundle(
            first["source_map"]["items"]["theorem1"],  # type: ignore[index]
            require_context_roles=True,
        )
        self.assertFalse(first_error)
        first["source_spec_screening"]["items"][  # type: ignore[index]
            "FixturePaper.claimSpec"
        ]["source_input_bundle_sha256"] = first_bundle
        second = copy.deepcopy(first)
        second["source_map"]["items"]["theorem1"]["corrected_target"][  # type: ignore[index]
            "statement"
        ] = "A materially different corrected target."
        _text, second_bundle, second_error = source_semantic_input_bundle(
            second["source_map"]["items"]["theorem1"],  # type: ignore[index]
            require_context_roles=True,
        )
        self.assertFalse(second_error)
        second["source_spec_screening"]["items"][  # type: ignore[index]
            "FixturePaper.claimSpec"
        ]["source_input_bundle_sha256"] = second_bundle
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(self.build(first)),
            final_holistic_audit_surface_sha256(self.build(second)),
        )

    def test_corrected_target_approval_move_preserves_terminal_identities(
        self,
    ) -> None:
        fixture = self.fixture()
        item = fixture["source_map"]["items"]["theorem1"]  # type: ignore[index]
        target = self.approved_corrected_target()
        item.update(  # type: ignore[union-attr]
            {
                "coverage_status": "corrected_source_statement",
                "source_defect_ids": ["FIXTURE-DEFECT-1"],
                "source_note": (
                    "The archival statement differs from the approved correction."
                ),
                "corrected_target": target,
            }
        )
        _text, source_bundle, error = source_semantic_input_bundle(
            item, require_context_roles=True  # type: ignore[arg-type]
        )
        self.assertFalse(error)
        screening = fixture["source_spec_screening"]["items"][  # type: ignore[index]
            "FixturePaper.claimSpec"
        ]
        screening.update(  # type: ignore[union-attr]
            {
                "judgment": "matches_approved_corrected_target",
                "source_input_bundle_sha256": source_bundle,
                "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
                "corrected_target_review_sha256": target[
                    "corrected_target_review_sha256"
                ],
            }
        )

        original = self.build(fixture)
        moved = copy.deepcopy(fixture)
        moved["source_map"]["items"]["theorem1"]["corrected_target"][  # type: ignore[index]
            "approval"
        ]["artifact_path"] = "audit/SOURCE_TARGET_STATEMENTS.md"
        moved_surface = self.build(moved)
        self.assertEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(moved_surface),
        )
        self.assertEqual(
            holistic_surface.final_holistic_source_assurance_sha256(original),
            holistic_surface.final_holistic_source_assurance_sha256(moved_surface),
        )

        changed_authority = copy.deepcopy(fixture)
        changed_authority["source_map"]["items"]["theorem1"][  # type: ignore[index]
            "corrected_target"
        ]["approval"]["future_semantic_condition"] = "new condition"
        changed_surface = self.build(changed_authority)
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(changed_surface),
        )
        self.assertNotEqual(
            holistic_surface.final_holistic_source_assurance_sha256(original),
            holistic_surface.final_holistic_source_assurance_sha256(
                changed_surface
            ),
        )

    def test_unselected_deep_audit_extraction_is_not_a_semantic_row(self) -> None:
        """A malformed unselected prose extract cannot block typed review.

        The full source inventory still records its disposition.  This merely
        ensures that semantic-input validation is limited to claims and
        prerequisites the final reviewer is actually asked to compare with
        Lean.
        """

        fixture = self.fixture()
        fixture["source_map"]["items"]["deep_audit_prose"] = {  # type: ignore[index]
            "source_kind": "claim",
            "source_location": "sources/Fixture.txt:99",
            "statement": "An unnumbered explanatory observation.",
            "claim_bearing": False,
            "source_anchor_evidence": [anchor("corrupt \x0f PDF text", 99)],
            "inventory_role": "deep_audit_material",
        }

        surface = self.build(fixture)
        self.assertEqual(len(surface["source_inventory"]["items"]), 3)  # type: ignore[index]

    def test_lean_dependency_closure_does_not_expand_paper_review_rows(self) -> None:
        """Only the typed source boundary, not every graph dependency, is reviewed."""

        fixture = self.fixture()
        internal = "FixturePaper.internalProofHelper"
        inventory = fixture["graph"]["inventory"]  # type: ignore[index]
        internal_display = copy.deepcopy(
            inventory["paper_prerequisite_displays"]["items"][0]  # type: ignore[index]
        )
        internal_display["declaration"] = internal
        inventory["paper_prerequisite_displays"]["items"].append(  # type: ignore[index]
            internal_display
        )
        inventory["semantic_signatures"]["items"].append(  # type: ignore[index]
            {
                "declaration": internal,
                "elaborated_signature_sha256": sha("internal helper"),
            }
        )

        surface = self.build(fixture)
        self.assertEqual(
            [
                row["lean_semantic_identity_sha256"]
                for row in surface["semantic_review_rows"]  # type: ignore[index]
                if row["role"] == "paper_prerequisite"
            ],
            [sha("paper definition")],
        )

    def test_source_assurance_rebuild_uses_graph_selected_rows_not_worksheets(self) -> None:
        """The receipt checker mirrors the full surface's selected inputs.

        This protects the lightweight post-closeout receipt check from both a
        missing helper argument and from deep-audit-only source observations.
        It reads no issuance ledgers and does not acquire a Lean graph.
        """

        fixture = self.scope_fixture()
        source_map = fixture["source_map"]  # type: ignore[assignment]
        source_map["items"]["deep_audit_prose"] = {  # type: ignore[index]
            "source_kind": "claim",
            "source_location": "sources/Fixture.txt:99",
            "statement": "An unnumbered explanatory observation.",
            "claim_bearing": False,
            "source_anchor_evidence": [anchor("corrupt \x0f PDF text", 99)],
            "inventory_role": "deep_audit_material",
        }
        payloads = {
            "canonical source map": source_map,
        }
        reviewed_source_item_ids = {
            row["source_item"]
            for key in (
                "source_spec_screening", "paper_prerequisite_ledger",
                "library_prerequisite_ledger",
            )
            for row in fixture[key]["items"].values()
        }

        def load(_path: object, *, label: str) -> object:
            return payloads[label]

        status_projection = fixture["status_projection"]
        with (
            mock.patch.object(holistic_surface, "_load_object", side_effect=load),
            mock.patch.object(
                holistic_surface,
                "_load_optional_object",
                return_value=fixture["source_proof_fidelity"],
            ),
            mock.patch(
                "scripts.closeout_status_projection.paper_status_acceptance_projection",
                return_value=status_projection,
            ),
        ):
            projection = (
                holistic_surface.build_current_final_holistic_source_assurance_projection(
                    Path("/fixture"), paper="FixturePaper",
                    reviewed_source_item_ids=reviewed_source_item_ids,
                )
            )
        self.assertEqual(len(projection["source_inventory"]["items"]), 3)  # type: ignore[index]
        self.assertEqual(len(projection["source_inventory"]["scope_relations"]), 7)
        self.assertEqual(
            projection,
            holistic_surface.final_holistic_source_assurance_projection(self.build(fixture)),
        )
        with (
            mock.patch.object(
                holistic_surface,
                "_load_object",
                side_effect=lambda path, **_kwargs: (
                    fixture["source_map"]
                    if path.name == "paper_statement_map.json"
                    else fixture["source_spec_screening"]
                ),
            ),
            mock.patch.object(
                holistic_surface,
                "_load_optional_object",
                return_value=fixture["source_proof_fidelity"],
            ),
            mock.patch(
                "scripts.closeout_status_projection.paper_status_acceptance_projection",
                return_value=status_projection,
            ),
        ):
            current_v2 = (
                holistic_surface.build_current_final_holistic_source_assurance_v2_projection(
                    Path("/fixture"),
                    paper="FixturePaper",
                    reviewed_source_item_ids=reviewed_source_item_ids,
                )
            )
        self.assertEqual(
            current_v2,
            holistic_surface.final_holistic_source_assurance_v2_projection(
                holistic_surface.final_holistic_source_assurance_projection(
                    self.build(fixture)
                )
            ),
        )

    def test_changed_inventory_disposition_requires_final_scope_review(self) -> None:
        """Intake cannot exempt its own changed classification from review."""

        fixture = self.fixture()
        candidate = {
            "schema": 1,
            "id": "holistic_1",
            "presentation_label": "An unnumbered overview.",
            "visible_kind": "holistic",
            "scope_disposition": "deep_audit_material",
            "semantic_basis": "It has no independently selected mathematical claim.",
            "discovery_basis": "holistic_full_text_review",
            "source_anchor": anchor("An unnumbered overview.", 99),
        }
        fixture["source_map"]["source_named_result_inventory_review"][  # type: ignore[index]
            "candidate_presentations"
        ] = [candidate]
        original = self.build(fixture)
        changed = copy.deepcopy(fixture)
        changed["source_map"]["source_named_result_inventory_review"][  # type: ignore[index]
            "candidate_presentations"
        ][0]["scope_disposition"] = "normal_theory"
        self.assertEqual(
            original["semantic_review_rows"], self.build(changed)["semantic_review_rows"]
        )
        self.assertNotEqual(
            final_holistic_audit_surface_sha256(original),
            final_holistic_audit_surface_sha256(self.build(changed)),
        )

    def test_approved_corrected_paper_prerequisite_needs_current_pin(self) -> None:
        fixture = self.fixture()
        corrected = {
            "statement": "The approved corrected model definition.",
            "archival_equivalence_claimed": False,
        }
        corrected["corrected_target_review_sha256"] = (
            corrected_target_review_digest(corrected)
        )
        model = fixture["source_map"]["items"]["model"]  # type: ignore[index]
        model.update(
            {
                "coverage_status": "corrected_source_statement",
                "corrected_target": corrected,
            }
        )
        name = "FixturePaper.Model"
        row = fixture["paper_prerequisite_ledger"]["items"][name]  # type: ignore[index]
        row.update(
            {
                "judgment": "matches_approved_corrected_target",
                "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
                "corrected_target_review_sha256": corrected[
                    "corrected_target_review_sha256"
                ],
            }
        )
        self.build(fixture)

        stale = copy.deepcopy(fixture)
        stale["paper_prerequisite_ledger"]["items"][name][  # type: ignore[index]
            "corrected_target_review_sha256"
        ] = sha("stale corrected target")
        with self.assertRaises(ValueError):
            self.build(stale)


if __name__ == "__main__":
    unittest.main()
