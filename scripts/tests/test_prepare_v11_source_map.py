from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import prepare_v11_source_map as preparer
from scripts import source_inventory_review
from scripts.corrected_target_identity import (
    corrected_target_record_digest,
    corrected_target_review_digest,
)
from scripts.source_coverage_scope import (
    source_item_scope_classification_errors,
    source_prose_definition_presentation_sha256,
)


class PrepareV11SourceMapTests(unittest.TestCase):
    def test_explicit_review_policy_requires_partition_and_matching_coverage(self) -> None:
        default_policy = {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": 1,
            "scheduling": {
                "initial_semantic_review": [],
                "final_adversarial_review": [],
            },
        }
        base = {"paper": "Fixture", "items": {}}
        config = {
            "paper": "Fixture",
            "namespace": "Fixture",
            "include_specs": [],
            "closeout_review_policy": default_policy,
        }
        with self.assertRaisesRegex(
            preparer.PreparationError, "complete source_region_partition"
        ):
            preparer.prepare(base, config)

        all_prose = json.loads(json.dumps(config))
        all_prose["closeout_review_policy"]["source_scope"] = "all_prose"
        all_prose["closeout_review_policy"]["repeat_final_scope"] = "all_selected"
        with self.assertRaisesRegex(
            preparer.PreparationError,
            "deep_paper_with_all_prose_claims",
        ):
            preparer.prepare(
                {
                    **base,
                    "source_named_result_inventory_review": {
                        "source_region_partition": {}
                    },
                },
                all_prose,
            )

    def test_completed_inventory_fixes_review_material_but_allows_panel_amendment(self) -> None:
        original = {
            "schema": 1,
            "source_scope": "all_named_theory",
            "repeat_final_scope": "main_primary",
            "required_final_adversary_count": 1,
            "scheduling": {
                "initial_semantic_review": [],
                "final_adversarial_review": [],
            },
        }
        changed = json.loads(json.dumps(original))
        changed["repeat_final_scope"] = "all_selected"
        source_map = {
            "paper": "Fixture",
            "items": {},
            "closeout_review_policy": original,
            "source_named_result_inventory_review": {
                "complete": True,
                "source_region_partition": {},
            },
        }
        with self.assertRaisesRegex(
            preparer.PreparationError, "already fixed the source/repeat scope"
        ):
            preparer.prepare(
                source_map,
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "closeout_review_policy": changed,
                },
            )

        amended = json.loads(json.dumps(original))
        amended["required_final_adversary_count"] = 2
        amended["scheduling"]["final_adversarial_review"] = ["reviewer-b"]
        prepared = preparer.prepare(
            source_map,
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": [],
                "closeout_review_policy": amended,
            },
        )
        self.assertIs(
            prepared["source_named_result_inventory_review"],
            source_map["source_named_result_inventory_review"],
        )
        self.assertEqual(
            prepared["closeout_review_policy"]["required_final_adversary_count"],
            2,
        )
        self.assertEqual(
            prepared["closeout_review_policy"]["scheduling"][
                "final_adversarial_review"
            ],
            ["reviewer-b"],
        )

    def test_direct_route_replaces_old_status_without_claiming_review(self) -> None:
        for semantic_definition in (False, True):
            for source_status in ("support_only", "formalization_pending", " SUPPORT_ONLY ", " Formalization_Pending ", "corrected", " CORRECTED "):
                with self.subTest(definition=semantic_definition, status=source_status):
                    prepared = preparer.prepare(
                        {"paper": "Fixture", "items": {"claim": {
                            "source_kind": "definition" if semantic_definition else "lemma",
                            "claim_bearing": True,
                            "source_status": source_status,
                            "source_location": "source.txt:1",
                            "inventory_role": "proof_support",
                        }}},
                        {
                            "paper": "Fixture", "namespace": "Fixture",
                            "semantic_route_schema": 2,
                            "include_specs": [] if semantic_definition else ["claim"],
                            "source_item_for_spec": {} if semantic_definition else {"claim": "claim"},
                            "evidence_declaration_for_spec": {} if semantic_definition else {"claim": "Fixture.proof"},
                            "source_semantic_declarations": {"claim": ["Fixture.Model"]} if semantic_definition else {},
                        },
                    )
                    item = prepared["items"]["claim"]
                    if source_status.strip().lower() in {"support_only", "formalization_pending"}:
                        self.assertNotIn("source_status", item)
                    else:
                        self.assertEqual(item["source_status"], source_status)
                    self.assertNotEqual(item.get("inventory_role"), "proof_support")
                    self.assertNotIn("source_spec_correspondence", item)

    def test_upgrades_legacy_corrected_target_with_explicit_memo_excerpt(self) -> None:
        excerpt = "This memo explicitly selects the corrected mathematical target."
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "audit").mkdir()
            (folder / "docs.md").write_text(
                "Opening context.\n" + excerpt + "\nClosing context.\n",
                encoding="utf-8",
            )
            (folder / "audit" / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "paper": folder.name,
                        "defects": [
                            {
                                "id": "FIXTURE-01",
                                "statement_impact": "source_statement",
                                "resolution": "corrected_source_statement",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            items: dict[str, dict[str, object]] = {
                "claim": {
                    "coverage_status": "corrected_source_statement",
                    "source_note": "The archival statement differs from the corrected target.",
                    "corrected_target": {
                        "statement": "Corrected proposition.",
                        "governing_defect_ids": ["FIXTURE-01"],
                        "archival_equivalence_claimed": False,
                        "approval": {
                            "kind": "documented_source_correction",
                            "recorded_at": "2026-09-02",
                            "reference": "Fixture memo.",
                            "artifact_path": "docs.md",
                            "artifact_sha256": "0" * 64,
                        },
                    },
                }
            }
            config = {
                "legacy_corrected_target_approval_artifacts": {
                    "docs.md": {"artifact_excerpt": excerpt}
                }
            }
            preparer._upgrade_legacy_corrected_target_approval_artifacts(
                items, config, folder=folder
            )
            # The migration is deterministic and safe to rerun.
            preparer._upgrade_legacy_corrected_target_approval_artifacts(
                items, config, folder=folder
            )

        target = items["claim"]["corrected_target"]
        self.assertIsInstance(target, dict)
        approval = target["approval"]
        self.assertEqual(
            approval["artifact_protocol"],
            "unique_normalized_artifact_excerpt_v1",
        )
        self.assertEqual(approval["artifact_excerpt"], excerpt)
        self.assertNotIn("artifact_sha256", approval)
        self.assertEqual(
            target["corrected_target_review_sha256"],
            corrected_target_review_digest(target),
        )
        self.assertEqual(
            target["corrected_target_sha256"],
            corrected_target_record_digest(target),
        )

    def test_assigns_explicit_roles_to_legacy_semantic_contexts(self) -> None:
        items: dict[str, dict[str, object]] = {
            "claim": {
                "semantic_context_requirements": [
                    {
                        "kind": "source_model",
                        "explanation": "The source model determines this claim.",
                    },
                    {
                        "kind": "antecedent",
                        "explanation": "The source antecedent scopes this claim.",
                    },
                ]
            }
        }
        preparer._apply_legacy_semantic_context_roles(
            items,
            {
                "legacy_semantic_context_roles": {
                    "claim": {
                        "source_model": "model",
                        "antecedent": "stated_antecedent",
                    }
                }
            },
        )
        contexts = items["claim"]["semantic_context_requirements"]
        self.assertEqual(contexts[0]["semantic_role"], "model")
        self.assertEqual(contexts[1]["semantic_role"], "stated_antecedent")
        self.assertEqual(contexts[0]["kind"], "source_model")

    def test_load_object_rejects_duplicate_json_keys(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "config.json"
            path.write_text('{"paper": "one", "paper": "two"}', encoding="utf-8")

            with self.assertRaisesRegex(
                preparer.PreparationError, "duplicate JSON object key `paper`"
            ):
                preparer.load_object(path, label="fixture config")

    def test_model_convention_routes_cover_existing_source_items(self) -> None:
        items = {"claim": {"statement": "Claim text"}}

        preparer._apply_model_convention_routes(
            items,
            {
                "model_convention_ids_by_source_item": {
                    "claim": ["decision-1"]
                }
            },
        )

        self.assertEqual(items["claim"]["statement"], "Claim text")
        self.assertEqual(
            items["claim"]["model_convention_ids"],
            ["decision-1"],
        )

    def test_source_core_projection_tracks_the_selected_typed_route(self) -> None:
        items = {
            "claim": {
                "semantic_contract": {
                    "spec_declaration": "Fixture.PaperInterface.claimSpec",
                    "evidence_declaration": "Fixture.ProofInterface.claim_proof",
                }
            }
        }

        preparer._apply_source_core_projections(
            items,
            {"source_core_projections": {"claim": "The literal result."}},
        )

        self.assertEqual(
            items["claim"]["source_core_projection"],
            {
                "classification": "literal_source_core",
                "description": "The literal result.",
                "direct_declaration": "Fixture.ProofInterface.claim_proof",
                "spec_declaration": "Fixture.PaperInterface.claimSpec",
            },
        )

    def test_selected_semantic_contract_keeps_existing_key_position(self) -> None:
        """A deterministic preparation must not create JSON ordering churn."""

        source_map = {
            "paper": "Fixture",
            "items": {
                "claim": {
                    "source_kind": "theorem",
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claim",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                    "source_spec_correspondence": {"schema": 1},
                    "lean_declarations": ["Fixture.claim"],
                }
            },
        }
        prepared = preparer.prepare(
            source_map,
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
            },
        )

        original_keys = list(source_map["items"]["claim"])
        prepared_keys = list(prepared["items"]["claim"])
        self.assertLess(
            original_keys.index("semantic_contract"),
            original_keys.index("source_spec_correspondence"),
        )
        self.assertLess(
            prepared_keys.index("semantic_contract"),
            prepared_keys.index("source_spec_correspondence"),
        )

    def test_schema2_preparation_drops_historical_source_correspondence(self) -> None:
        """A changed typed route must not retain stale pre-graph evidence."""

        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "claim_bearing": True,
                        "source_location": "source.txt:1",
                        "semantic_contract": {
                            "spec_declaration": "Fixture.oldClaimSpec",
                            "evidence_declaration": "Fixture.oldClaim",
                        },
                        "source_spec_correspondence": {
                            "schema": 1,
                            "source_atom_bindings": ["historical"],
                        },
                        "lean_declarations": ["Fixture.oldClaim"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "semantic_route_schema": 2,
                "include_specs": ["claim"],
                "source_item_for_spec": {"claim": "claim"},
                "evidence_declaration_for_spec": {"claim": "Fixture.claim"},
            },
        )

        self.assertNotIn(
            "source_spec_correspondence", prepared["items"]["claim"]
        )

    def test_reviewed_source_inventory_derives_anchors_and_hashes_once(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = "We define utility as a real-valued score.\nTheorem 1. Utility exists.\n"
            (folder / "source.txt").write_text(source, encoding="utf-8")
            source_sha = hashlib.sha256(source.encode("utf-8")).hexdigest()
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": source_sha,
                    "source_coverage_mode": "named_theoretical_statements",
                    "items": {
                        "utility": {
                            "source_kind": "definition",
                            "source_location": "source.txt:1",
                            "statement": "Utility is a real-valued score.",
                            "claim_bearing": True,
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "source.txt:1"
                            ),
                            "lean_declarations": ["Fixture.utility"],
                        },
                        "theorem1": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:2",
                            "statement": "Utility exists.",
                            "claim_bearing": True,
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "source.txt:2"
                            ),
                            "lean_declarations": ["Fixture.theorem1Spec"],
                            "checked_strengthening_declarations": [
                                {
                                    "declaration": "Fixture.theorem1",
                                    "spec_declaration": "Fixture.theorem1SpecSpec",
                                    "classification": "checked_strengthening_not_literal_source_coverage",
                                    "description": "A former direct route.",
                                },
                                {
                                    "declaration": "Fixture.theorem1Strengthening",
                                    "spec_declaration": "Fixture.theorem1StrengtheningSpec",
                                    "classification": "checked_strengthening_not_literal_source_coverage",
                                    "description": "A separately checked strengthening.",
                                }
                            ],
                        },
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "semantic_route_schema": 2,
                    "include_specs": ["theorem1Spec"],
                    "source_item_for_spec": {"theorem1Spec": "theorem1"},
                    "evidence_declaration_for_spec": {
                        "theorem1Spec": "Fixture.theorem1"
                    },
                    "source_semantic_declarations": {
                        "utility": ["Fixture.utility"]
                    },
                    "source_named_result_inventory_review": {
                        "complete": True,
                        "validator": "fixture source-only inventory",
                        "method": "Read the complete pinned fixture before consulting Lean names.",
                        "validated_at": "2026-08-28T00:00:00Z",
                        "candidate_presentations": [],
                        "prose_definition_presentations": [
                            {
                                "id": "utility_definition",
                                "source_locator": "source.txt:1",
                                "defined_entity_kind": "object",
                                "defined_object": "utility",
                                "scope_disposition": "normal_named_theory_definition",
                            }
                        ],
                    },
                    "prose_definition_reconciliations": {
                        "utility": {
                            "presentation_id": "utility_definition",
                            "semantic_basis": "The source clause and source-map item define the same real-valued utility object.",
                            "validator": "independent fixture source-to-map reviewer",
                            "validator_type": "agent",
                            "validated_at": "2026-08-28T00:01:00Z",
                        }
                    },
                },
                folder=folder,
            )
        self.assertTrue(prepared["source_anchor_evidence_required"])
        review = prepared["source_named_result_inventory_review"]
        self.assertEqual(review["source_artifact_sha256"], source_sha)
        self.assertRegex(review["discovered_named_result_sha256"], r"^[0-9a-f]{64}$")
        self.assertRegex(
            review["discovered_prose_definition_sha256"], r"^[0-9a-f]{64}$"
        )
        presentation_sha = source_prose_definition_presentation_sha256(
            review["prose_definition_presentations"][0]
        )
        self.assertEqual(
            prepared["items"]["utility"]["source_prose_definition_reconciliation"][
                "presentation_sha256"
            ],
            presentation_sha,
        )
        self.assertEqual(
            prepared["items"]["theorem1"]["support_lean_declarations"],
            [
                "Fixture.theorem1SpecSpec",
                "Fixture.theorem1Strengthening",
                "Fixture.theorem1StrengtheningSpec",
            ],
        )
        self.assertEqual(
            prepared["items"]["theorem1"]["checked_strengthening_declarations"],
            [
                {
                    "declaration": "Fixture.theorem1Strengthening",
                    "spec_declaration": "Fixture.theorem1StrengtheningSpec",
                    "classification": "checked_strengthening_not_literal_source_coverage",
                    "description": "A separately checked strengthening.",
                }
            ],
        )

    def test_source_byte_repair_refreshes_derived_pins_before_inventory_validation(
        self,
    ) -> None:
        """A writer rerun must not require hand-editing every copied quote pin."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            old_source = (
                "We define epsilon utility as a real-valued score.\n"
                "Theorem 1. Epsilon utility exists.\n"
            )
            current_source = (
                "We define ε-utility as a real-valued score.\n"
                "Theorem 1. ε-utility exists.\n"
            )
            source_path = folder / "source.txt"
            source_path.write_text(old_source, encoding="utf-8")
            stale_definition_anchor = preparer._canonical_anchor_evidence(
                folder, "source.txt:1"
            )
            stale_theorem_anchor = preparer._canonical_anchor_evidence(
                folder, "source.txt:2"
            )
            stale_digest = stale_definition_anchor[0]["quoted_text_sha256"]
            source_path.write_text(current_source, encoding="utf-8")
            current_source_sha = hashlib.sha256(
                current_source.encode("utf-8")
            ).hexdigest()

            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": current_source_sha,
                    "source_coverage_mode": "named_theoretical_statements",
                    "items": {
                        "utility": {
                            "source_kind": "definition",
                            "source_location": "source.txt:1",
                            "statement": "ε-utility is a real-valued score.",
                            "claim_bearing": True,
                            "source_anchor_evidence": stale_definition_anchor,
                            "lean_declarations": ["Fixture.utility"],
                            "source_claim_atoms": [
                                {
                                    "id": "utility.definition",
                                    "source_locator": "source.txt:1",
                                    "source_quote_sha256": stale_digest,
                                    "semantic_claim": "ε-utility is a real-valued score.",
                                    "reviewed_lean_route": "Fixture.utility",
                                }
                            ],
                        },
                        "theorem1": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:2",
                            "statement": "ε-utility exists.",
                            "claim_bearing": True,
                            "source_anchor_evidence": stale_theorem_anchor,
                            "semantic_context_requirements": [
                                {
                                    "semantic_role": "definition",
                                    "source_anchor_evidence": stale_definition_anchor,
                                }
                            ],
                            "lean_declarations": ["Fixture.theorem1Spec"],
                        },
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "semantic_route_schema": 2,
                    "include_specs": ["theorem1Spec"],
                    "source_item_for_spec": {"theorem1Spec": "theorem1"},
                    "evidence_declaration_for_spec": {
                        "theorem1Spec": "Fixture.theorem1"
                    },
                    "source_semantic_declarations": {
                        "utility": ["Fixture.utility"]
                    },
                    "source_named_result_inventory_review": {
                        "complete": True,
                        "validator": "fixture source-only inventory",
                        "method": "Read the complete pinned fixture before consulting Lean names.",
                        "validated_at": "2026-08-28T00:00:00Z",
                        "candidate_presentations": [],
                        "prose_definition_presentations": [
                            {
                                "id": "utility_definition",
                                "source_locator": "source.txt:1",
                                "defined_entity_kind": "object",
                                "defined_object": "ε-utility",
                                "scope_disposition": "normal_named_theory_definition",
                            }
                        ],
                    },
                    "prose_definition_reconciliations": {
                        "utility": {
                            "presentation_id": "utility_definition",
                            "semantic_basis": (
                                "The corrected glyph and source-map item define "
                                "the same real-valued utility object."
                            ),
                            "validator": "independent fixture source-to-map reviewer",
                            "validator_type": "agent",
                            "validated_at": "2026-08-28T00:01:00Z",
                        }
                    },
                },
                folder=folder,
            )

        current_definition = "We define ε-utility as a real-valued score."
        current_definition_sha = hashlib.sha256(
            current_definition.encode("utf-8")
        ).hexdigest()
        utility = prepared["items"]["utility"]
        theorem = prepared["items"]["theorem1"]
        self.assertEqual(
            utility["source_anchor_evidence"][0]["quoted_text"], current_definition
        )
        self.assertEqual(
            utility["source_claim_atoms"][0]["source_quote_sha256"],
            current_definition_sha,
        )
        self.assertNotEqual(
            utility["source_claim_atoms"][0]["source_quote_sha256"], stale_digest
        )
        self.assertEqual(
            theorem["semantic_context_requirements"][0]["source_anchor_evidence"][0][
                "quoted_text"
            ],
            current_definition,
        )

    def test_inventory_combines_machine_and_holistic_source_candidates(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = (
                "For every admissible input, the expected cost is at most four.\n"
                "\n"
                "Remark 1. The cutoff bound is independent of n.\n"
                "Remark 2. This paragraph is explanatory only.\n"
                "Theorem 3. The algorithm succeeds.\n"
            )
            source_path = folder / "source.txt"
            source_path.write_text(source, encoding="utf-8")
            source_sha = hashlib.sha256(source.encode("utf-8")).hexdigest()

            def item(line_start: int, line_end: int, kind: str) -> dict[str, object]:
                return {
                    "source_kind": kind,
                    "source_location": f"source.txt:{line_start}-{line_end}",
                    "claim_bearing": True,
                    "source_anchor_evidence": preparer._canonical_anchor_evidence(
                        folder,
                        f"source.txt:{line_start}-{line_end}",
                    ),
                }

            source_map = {
                "paper": "Fixture",
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": source_sha,
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    "prose_bound": item(1, 1, "claim"),
                    "remark1": item(3, 3, "claim"),
                    "theorem3": item(5, 5, "theorem"),
                },
            }
            review = source_inventory_review.materialize_source_named_result_inventory_review(
                folder,
                source_map,
                {
                    "complete": True,
                    "validator": "fixture full-source reviewer",
                    "method": "Read the complete pinned source before consulting Lean or the source map.",
                    "validated_at": "2026-08-28T00:00:00Z",
                    "candidate_presentations": [
                        {
                            "id": "remark1",
                            "source_locator": "source.txt:3",
                            "scope_disposition": "material_named_claim",
                            "semantic_basis": "This numbered remark asserts an n-independent bound.",
                        },
                        {
                            "id": "remark2",
                            "source_locator": "source.txt:4",
                            "scope_disposition": "deep_audit_material",
                            "semantic_basis": "This numbered remark is explanatory only.",
                        },
                        {
                            "id": "prose_bound",
                            "source_locator": "source.txt:1",
                            "presentation_label": "Unnumbered finite-cost claim",
                            "scope_disposition": "material_named_claim",
                            "semantic_basis": "The holistic full-text pass found an independently asserted bound.",
                        },
                    ],
                    "prose_definition_presentations": [],
                },
            )

        self.assertEqual(
            [
                (record["id"], record["discovery_basis"], record["scope_disposition"])
                for record in review["candidate_presentations"]
            ],
            [
                ("remark1", "mechanical_labelled_heading", "material_named_claim"),
                ("remark2", "mechanical_labelled_heading", "deep_audit_material"),
                ("prose_bound", "holistic_full_text_review", "material_named_claim"),
            ],
        )
        self.assertRegex(
            review["discovered_candidate_presentation_sha256"], r"^[0-9a-f]{64}$"
        )
        self.assertRegex(review["discovered_named_result_sha256"], r"^[0-9a-f]{64}$")

    def test_role_schema_routes_definitions_to_actual_prerequisite_declarations(
        self,
    ) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "model": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "claim_bearing": True,
                        "lean_declarations": ["Fixture.OldWrapper"],
                        "semantic_surface": {
                            "schema": 1,
                            "required_structural_tokens": ["∀"],
                        },
                        "source_claim_atoms": [
                            {
                                "id": "model.body",
                                "source_locator": "source.tex:1",
                                "semantic_claim": "The source defines the model.",
                                "reviewed_lean_route": "Fixture.OldWrapper",
                                "source_quote_sha256": "a" * 64,
                                "identity_schema": 2,
                            }
                        ],
                    },
                    "result": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:2",
                        "claim_bearing": True,
                        "lean_declarations": ["Fixture.resultSpec"],
                        "source_claim_atoms": [
                            {
                                "id": "result.body",
                                "source_locator": "source.tex:2",
                                "semantic_claim": "The source states the result.",
                                "reviewed_lean_route": "Fixture.resultSpec",
                                "source_quote_sha256": "b" * 64,
                                "identity_schema": 2,
                            }
                        ],
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "paper_interface_module": "",
                "semantic_route_schema": 2,
                "include_specs": ["result"],
                "source_item_for_spec": {"result": "result"},
                "evidence_declaration_for_spec": {"result": "result"},
                "source_semantic_declarations": {
                    "model": ["Fixture.ActualModel"]
                },
            },
        )
        self.assertEqual(prepared["semantic_route_schema"], 2)
        model = prepared["items"]["model"]
        self.assertEqual(model["inventory_role"], "source_semantic_declaration")
        self.assertEqual(model["lean_declarations"], ["Fixture.ActualModel"])
        self.assertNotIn("semantic_contract", model)
        self.assertNotIn("semantic_surface", model)
        self.assertEqual(
            model["source_claim_atoms"][0]["reviewed_lean_route"],
            "Fixture.ActualModel",
        )
        self.assertEqual(
            prepared["items"]["result"]["semantic_contract"]["evidence_mode"],
            "proves",
        )
        self.assertEqual(
            prepared["items"]["result"]["source_claim_atoms"][0][
                "reviewed_lean_route"
            ],
            "Fixture.result",
        )

    def test_direct_semantic_context_remains_non_claim_bearing(self) -> None:
        """A proof-side source condition is not promoted to a paper claim."""

        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "condition": {
                        "source_kind": "condition",
                        "source_location": "source.tex:1",
                        "claim_bearing": False,
                        "lean_declarations": ["Fixture.OldCondition"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "semantic_route_schema": 2,
                "include_specs": [],
                "source_semantic_declarations": {
                    "condition": ["Fixture.ActualCondition"]
                },
            },
        )

        condition = prepared["items"]["condition"]
        self.assertFalse(condition["claim_bearing"])
        self.assertEqual(condition["inventory_role"], "source_semantic_declaration")
        self.assertEqual(condition["lean_declarations"], ["Fixture.ActualCondition"])

    def test_named_algorithm_prerequisite_respects_explicit_nonclaim_scope(self) -> None:
        """A reviewed algorithm prerequisite is not silently a denominator row."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.txt").write_text(
                "ALGORITHM 4.1. Start from a matching and update it.\n",
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "algorithm": {
                            "source_kind": "algorithm",
                            "source_location": "source.txt:1",
                            "statement": "The algorithm updates the matching.",
                            "claim_bearing": False,
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "source.txt:1"
                            ),
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "source_semantic_declarations": {
                        "algorithm": ["Fixture.AlgorithmModel"]
                    },
                },
                folder=folder,
            )

        algorithm = prepared["items"]["algorithm"]
        self.assertFalse(algorithm["claim_bearing"])
        self.assertEqual(algorithm["inventory_role"], "source_semantic_declaration")

    def test_semantic_source_anchor_preserves_full_coverage_span(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.txt").write_text(
                "Theorem 1. Claim.\nProof explanation.\nFurther discussion.\n",
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "theorem": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:1-3",
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "source.txt:1-3"
                            ),
                            "claim_bearing": True,
                            "lean_declarations": ["Fixture.theorem"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "semantic_source_anchor_overrides": {
                        "theorem": {
                            "source_location": "source.txt:1",
                            "reason": "The displayed theorem ends before explanatory prose.",
                        }
                    },
                    "unselected_item_dispositions": {
                        "theorem": {
                            "inventory_role": "deep_audit_material",
                            "scope_disposition": "deep_audit_material",
                            "reason": "The fixture has no Lean interface target.",
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["theorem"]
        self.assertEqual(item["source_location"], "source.txt:1-3")
        self.assertEqual(item["source_anchor_evidence"][0]["line_end"], 3)
        self.assertEqual(
            item["semantic_source_anchor_evidence"][0]["quoted_text"],
            "Theorem 1. Claim.",
        )
        self.assertEqual(
            item["semantic_source_anchor_reason"],
            "The displayed theorem ends before explanatory prose.",
        )

    def test_role_schema_records_direct_paper_prerequisite_source_route(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "claim_bearing": True,
                        "lean_declarations": ["Fixture.Model"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "semantic_route_schema": 2,
                "include_specs": [],
                "paper_semantic_prerequisite_sources": {
                    "Fixture.Shared": "definition"
                },
                "source_semantic_declarations": {
                    "definition": ["Fixture.Model"]
                },
            },
        )
        self.assertEqual(
            prepared["paper_semantic_prerequisite_sources"],
            {"Fixture.Shared": "definition"},
        )

    def test_role_schema_rejects_unknown_paper_prerequisite_source_item(self) -> None:
        with self.assertRaisesRegex(
            preparer.PreparationError,
            "paper_semantic_prerequisite_sources names absent source items",
        ):
            preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "paper_semantic_prerequisite_sources": {
                        "Fixture.Shared": "absent"
                    },
                },
            )

    def test_role_schema_requires_explicit_result_evidence_endpoint(self) -> None:
        with self.assertRaisesRegex(
            preparer.PreparationError,
            "requires an explicit evidence_declaration_for_spec",
        ):
            preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "result": {
                            "source_kind": "theorem",
                            "source_location": "source.tex:1",
                            "claim_bearing": True,
                            "lean_declarations": ["Fixture.result"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": ["result"],
                },
            )

    def test_role_schema_allows_explicit_definition_proof_contract(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "claim_bearing": True,
                        "lean_declarations": ["Fixture.definitionSpec"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "semantic_route_schema": 2,
                "include_specs": ["definition"],
                "source_item_for_spec": {"definition": "definition"},
                "evidence_declaration_for_spec": {
                    "definition": "definitionSpec_proof"
                },
            },
        )
        self.assertNotIn("inventory_role", prepared["items"]["definition"])
        self.assertEqual(
            prepared["items"]["definition"]["semantic_contract"][
                "evidence_declaration"
            ],
            "Fixture.PaperInterface.definitionSpec_proof",
        )

    def test_anchor_replacement_uses_the_configured_exact_source_span(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text("Context.\nLemma: claim.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "lemma",
                            "source_location": "source.tex:1-2",
                            "source_presentation_reconciliation": {
                                "old": "conservative source span metadata"
                            },
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "replace_source_item_anchors": {"claim": "source.tex:2"},
                },
                folder=folder,
            )
        anchor = prepared["items"]["claim"]["source_anchor_evidence"][0]
        self.assertEqual((anchor["line_start"], anchor["line_end"]), (2, 2))
        self.assertNotIn(
            "source_presentation_reconciliation", prepared["items"]["claim"]
        )

    def test_source_kind_reclassification_is_explicit_and_idempotent(self) -> None:
        items: dict[str, dict[str, object]] = {
            "conclusion": {"source_kind": "remark", "statement": "A conclusion."}
        }
        config = {
            "reclassify_source_item_kinds": {
                "conclusion": {
                    "from_kind": "remark",
                    "to_kind": "claim",
                    "reason": "The prose records a mathematical conclusion.",
                }
            }
        }

        preparer._reclassify_source_item_kinds(items, config)
        preparer._reclassify_source_item_kinds(items, config)

        self.assertEqual(items["conclusion"]["source_kind"], "claim")

    def test_source_kind_reclassification_rejects_unexpected_prior_kind(self) -> None:
        with self.assertRaisesRegex(preparer.PreparationError, "expected 'remark' or 'claim'"):
            preparer._reclassify_source_item_kinds(
                {"conclusion": {"source_kind": "definition"}},
                {
                    "reclassify_source_item_kinds": {
                        "conclusion": {
                            "from_kind": "remark",
                            "to_kind": "claim",
                            "reason": "The prose records a mathematical conclusion.",
                        }
                    }
                },
            )

    def test_location_replacement_preserves_selected_semantic_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "raw.txt").write_text("Context.\nLemma: claim.\n", encoding="utf-8")
            (folder / "visual.txt").write_text("Lemma: claim.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "lemma",
                            "source_location": "visual.txt:1",
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "visual.txt:1"
                            ),
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "replace_source_item_locations": {"claim": "raw.txt:2"},
                },
                folder=folder,
            )
        item = prepared["items"]["claim"]
        self.assertEqual(item["source_location"], "raw.txt:2")
        self.assertEqual(item["source_anchor_evidence"][0]["path"], "visual.txt")

    def test_semantic_context_preserves_source_item_identity_and_is_idempotent(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Theorem: claim.\nModel assumption.\nPrior model context.\n",
                encoding="utf-8",
            )
            existing_context = {
                "kind": "prior_model_context",
                "semantic_role": "model",
                "source_location": "source.tex:3",
                "source_anchor_evidence": preparer._canonical_anchor_evidence(
                    folder, "source.tex:3"
                ),
            }
            source_map = {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "source_anchor_evidence": preparer._canonical_anchor_evidence(
                            folder, "source.tex:1"
                        ),
                        "lean_declarations": ["Fixture.claim"],
                        "semantic_context_requirements": [existing_context],
                    }
                },
            }
            config = {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "semantic_context_requirements": {
                    "claim": [
                        {
                            "semantic_role": "model",
                            "source_location": "source.tex:2",
                        }
                    ]
                },
            }
            first = preparer.prepare(source_map, config, folder=folder)
            second = preparer.prepare(first, config, folder=folder)
        item = first["items"]["claim"]
        self.assertEqual(item["source_location"], "source.tex:1")
        self.assertEqual(len(item["source_anchor_evidence"]), 1)
        self.assertEqual(item["semantic_context_requirements"][0], existing_context)
        self.assertEqual(len(item["semantic_context_requirements"]), 2)
        context = item["semantic_context_requirements"][1]
        self.assertEqual(context["semantic_role"], "model")
        self.assertEqual(
            context["source_anchor_evidence"][0]["quoted_text"],
            "Model assumption.",
        )
        self.assertEqual(second, first)

    def test_semantic_context_replacement_drops_obsolete_context(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Theorem: claim.\nCurrent model context.\nObsolete model context.\n",
                encoding="utf-8",
            )
            stale_context = {
                "semantic_role": "model",
                "source_anchor_evidence": preparer._canonical_anchor_evidence(
                    folder, "source.tex:3"
                ),
            }
            source_map = {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "source_anchor_evidence": preparer._canonical_anchor_evidence(
                            folder, "source.tex:1"
                        ),
                        "lean_declarations": ["Fixture.claim"],
                        "semantic_context_requirements": [stale_context],
                    }
                },
            }
            config = {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "replace_semantic_context_requirements_for": ["claim"],
                "semantic_context_requirements": {
                    "claim": [
                        {
                            "semantic_role": "model",
                            "source_location": "source.tex:2",
                        }
                    ]
                },
            }
            first = preparer.prepare(source_map, config, folder=folder)
            second = preparer.prepare(first, config, folder=folder)
        contexts = first["items"]["claim"]["semantic_context_requirements"]
        self.assertEqual(len(contexts), 1)
        self.assertEqual(
            contexts[0]["source_anchor_evidence"][0]["quoted_text"],
            "Current model context.",
        )
        self.assertEqual(second, first)

    def test_existing_item_can_record_a_reviewed_statement_core(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Definition 1. Exact definition.\n"
                "A following explanatory claim.\n",
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "definition": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.definition"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "source_semantic_declarations": {
                        "definition": ["Fixture.definition"]
                    },
                    "source_presentation_reconciliations": {
                        "definition": {
                            "presentation_kind": "definition",
                            "presentation_label": "Definition 1",
                            "core_anchor_locator": "source.tex:1",
                            "boundary_reason": "completed_statement_then_explanation",
                            "semantic_basis": "The first line contains the complete exact definition.",
                            "validator": "independent source-boundary review",
                            "validated_at": "2026-08-24T00:00:00Z",
                        }
                    },
                },
                folder=folder,
            )
        reconciliation = prepared["items"]["definition"][
            "source_presentation_reconciliation"
        ]
        self.assertEqual(reconciliation["core_anchor"]["line_start"], 1)
        self.assertEqual(
            reconciliation["boundary_reason"],
            "completed_statement_then_explanation",
        )

    def test_add_source_item_pins_the_configured_source_span(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text("Lemma: source support.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "support_lemma": {
                            "statement": "Lemma: source support.",
                            "source_kind": "lemma",
                            "source_location": "source.tex:1",
                            "source_note": "This named lemma is recorded as source proof support.",
                            "source_status": "support_only",
                            "support_lean_declarations": ["Fixture.support"],
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["support_lemma"]
        self.assertTrue(item["claim_bearing"])
        self.assertEqual(item["source_status"], "support_only")
        self.assertEqual(item["source_anchor_evidence"][0]["line_start"], 1)

    def test_add_source_item_preserves_standard_term_interpretation(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source_text = "The standard `erf` is used here.\n"
            (folder / "source.tex").write_text(source_text, encoding="utf-8")
            anchor = preparer._canonical_anchor_evidence(folder, "source.tex:1")[0]
            statement = "The source uses the standard error-function notation `erf`."
            interpretation = {
                "schema": 1,
                "relation": "source_uses_standard_term_without_source_definition",
                "source_term": "erf",
                "source_provided_definition": False,
                "source_term_use_anchor": anchor,
                "source_item_statement_sha256": hashlib.sha256(
                    statement.encode("utf-8")
                ).hexdigest(),
                "standard_interpretation": (
                    "The standard error function is the normalized Gaussian integral."
                ),
                "judgment": "standard_interpretation_matches_source_use",
                "semantic_basis": (
                    "The source uses the established term without a nonstandard definition."
                ),
                "validator": "independent standard-term reviewer",
                "validator_type": "agent",
                "validated_at": "2026-09-03T00:00:00Z",
            }
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "error_function": {
                            "statement": statement,
                            "source_kind": "predicate_vocabulary",
                            "source_location": "source.tex:1",
                            "source_note": "The source relies on standard notation.",
                            "lean_declarations": ["Fixture.erf"],
                            "source_standard_term_interpretation": interpretation,
                        }
                    },
                    "unselected_item_dispositions": {
                        "error_function": {
                            "inventory_role": "pending_v11_surface_migration",
                            "scope_disposition": "requires_dedicated_v11_spec",
                            "reason": "The fixture exercises metadata projection only.",
                        }
                    },
                },
                folder=folder,
            )
        self.assertEqual(
            prepared["items"]["error_function"]["source_standard_term_interpretation"],
            interpretation,
        )

    def test_add_pending_source_claim_without_a_false_support_route(self) -> None:
        """A missing named theorem may be retained before its Spec exists."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Lemma: visible pending claim.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "pending_lemma": {
                            "statement": "Lemma: visible pending claim.",
                            "source_kind": "lemma",
                            "source_location": "source.tex:1",
                            "source_note": "This source claim needs its own transparent Spec.",
                            "claim_bearing": True,
                            "source_status": "formalization_pending",
                        }
                    },
                    "unselected_item_dispositions": {
                        "pending_lemma": {
                            "inventory_role": "pending_v11_surface_migration",
                            "scope_disposition": "requires_dedicated_v11_spec",
                            "reason": "A transparent Spec remains required.",
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["pending_lemma"]
        self.assertTrue(item["claim_bearing"])
        self.assertEqual(item["inventory_role"], "pending_v11_surface_migration")
        self.assertNotIn("lean_declarations", item)
        self.assertNotIn("support_lean_declarations", item)

    def test_quarantined_source_defect_projects_its_fidelity_link(self) -> None:
        """A false uncredited source claim remains visibly linked to its defect."""

        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "false_lemma": {
                        "source_kind": "lemma",
                        "claim_bearing": True,
                        "source_location": "source.txt:1",
                        "statement": "The printed lemma is false.",
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": [],
                "unselected_item_dispositions": {
                    "false_lemma": {
                        "inventory_role": "quarantined_source_defect",
                        "scope_disposition": "deep_only_documented_source_defect",
                        "source_status": "quarantined_source_defect",
                        "source_defect_ids": ["FIXTURE-FALSE-LEMMA-01"],
                        "reason": "The literal result remains documented but receives no proof credit.",
                    }
                },
            },
        )

        item = prepared["items"]["false_lemma"]
        self.assertEqual(item["source_status"], "quarantined_source_defect")
        self.assertEqual(item["source_defect_ids"], ["FIXTURE-FALSE-LEMMA-01"])

    def test_add_source_item_projects_approved_model_convention_for_review(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "audit").mkdir()
            (folder / "source.tex").write_text(
                "Lemma: count events in calendar time.\n", encoding="utf-8"
            )
            (folder / "audit" / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "model_conventions": [
                            {
                                "id": "FIXTURE-CALENDAR-01",
                                "source_locator": "source.tex:1",
                                "classification": "source_text_model_convention",
                                "formal_meaning": "Count event times in the calendar window.",
                                "why_needed": "An event can begin before the window.",
                                "checked_scope": "The displayed lemma and its prerequisites.",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "source_semantic_declarations": {
                        "calendar_model": ["Fixture.CalendarModel"]
                    },
                    "add_source_items": {
                        "calendar_model": {
                            "statement": "Lemma: count events in calendar time.",
                            "source_kind": "model",
                            "source_location": "source.tex:1",
                            "source_note": "The exact calendar-event model for the lemma.",
                            "claim_bearing": True,
                            "support_lean_declarations": ["Fixture.CalendarModel"],
                            "model_convention_ids": ["FIXTURE-CALENDAR-01"],
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["calendar_model"]
        self.assertEqual(prepared["approved_review_context_schema"], 1)
        self.assertEqual(item["approved_review_context_schema"], 1)
        self.assertEqual(item["model_convention_ids"], ["FIXTURE-CALENDAR-01"])
        context = item["approved_review_contexts"][0]
        self.assertEqual(context["id"], "FIXTURE-CALENDAR-01")
        self.assertEqual(context["kind"], "source_model_convention")
        self.assertRegex(context["record_sha256"], r"^[0-9a-f]{64}$")

    def test_add_source_item_refreshes_curator_metadata_on_rerun(self) -> None:
        """Corrected curator metadata and its exact span must not stay stale."""

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Context only.\nTheorem: exact source statement.\n", encoding="utf-8"
            )
            source_map = {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "statement": "Stale summary.",
                        "source_note": "Stale note.",
                        "claim_bearing": False,
                        "source_anchor_evidence": preparer._canonical_anchor_evidence(
                            folder, "source.tex:1"
                        ),
                        "lean_declarations": ["Fixture.claim"],
                    }
                },
            }
            prepared = preparer.prepare(
                source_map,
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "claim": {
                            "statement": "Current exact-source summary.",
                            "source_kind": "theorem",
                            "source_location": "source.tex:2",
                            "source_note": "Current curator note.",
                            "claim_bearing": False,
                            "lean_declarations": ["Fixture.claim"],
                        }
                    },
                },
                folder=folder,
            )

        item = prepared["items"]["claim"]
        self.assertEqual(item["statement"], "Current exact-source summary.")
        self.assertEqual(item["source_note"], "Current curator note.")
        self.assertEqual(item["source_location"], "source.tex:2")
        self.assertEqual(
            item["source_anchor_evidence"][0]["quoted_text"],
            "Theorem: exact source statement.",
        )
        self.assertEqual(item["lean_declarations"], ["Fixture.claim"])

    def test_support_only_rerun_refreshes_curator_owned_support_route(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Theorem 1 (Informal). An informal overview.\n", encoding="utf-8"
            )
            source_map = {
                "paper": "Fixture",
                "items": {
                    "overview": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "statement": "An informal overview.",
                        "source_note": "The overview is retained as proof support.",
                        "source_status": "support_only",
                        "claim_bearing": True,
                        "support_lean_declarations": ["Fixture.staleGuess"],
                    }
                },
            }
            prepared = preparer.prepare(
                source_map,
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "overview": {
                            "statement": "An informal overview.",
                            "source_kind": "theorem",
                            "source_location": "source.tex:1",
                            "source_note": "The overview is retained as proof support.",
                            "source_status": "support_only",
                            "support_lean_declarations": ["Fixture.reviewedSupport"],
                        }
                    },
                },
                folder=folder,
            )
        self.assertEqual(
            prepared["items"]["overview"]["support_lean_declarations"],
            ["Fixture.reviewedSupport"],
        )

    def test_support_only_unnamed_context_remains_nonclaim(self) -> None:
        """A local proof observation is not promoted merely by support status."""
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "A local proof observation.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "local_observation": {
                            "statement": "A local proof observation.",
                            "source_kind": "remark",
                            "source_location": "source.tex:1",
                            "source_note": "This is local proof support rather than a source claim.",
                            "source_status": "support_only",
                            "claim_bearing": False,
                            "support_lean_declarations": ["Fixture.local_observation"],
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["local_observation"]
        self.assertFalse(item["claim_bearing"])
        self.assertEqual(item["inventory_role"], "proof_support")

    def test_merge_source_items_is_idempotent(self) -> None:
        """A rerun does not append the same merged-source note again."""
        config = {
            "paper": "Fixture",
            "namespace": "Fixture",
            "include_specs": ["claim"],
            "merge_source_items": {"claim": ["context"]},
        }
        first = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                    },
                    "context": {
                        "source_kind": "definition",
                        "source_location": "source.tex:2",
                    },
                },
            },
            config,
        )
        second = preparer.prepare(first, config)
        note = second["items"]["claim"].get("source_note", "")
        self.assertEqual(note.count("The raw source bundle also includes"), 1)

    def test_readded_merge_context_does_not_duplicate_source_anchors(self) -> None:
        """Temporary config-added context rows remain digest-idempotent."""
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Theorem: claim.\nDefinition: context.\n", encoding="utf-8"
            )
            config = {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "add_source_items": {
                    "context": {
                        "statement": "Definition: context.",
                        "source_kind": "definition",
                        "source_location": "source.tex:2",
                        "source_note": "Exact context needed to interpret the theorem.",
                        "claim_bearing": True,
                        "support_lean_declarations": ["Fixture.context"],
                    }
                },
                "merge_source_items": {"claim": ["context"]},
            }
            first = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "theorem",
                            "source_location": "source.tex:1",
                            "source_anchor_evidence": preparer._canonical_anchor_evidence(
                                folder, "source.tex:1"
                            ),
                            "lean_declarations": ["Fixture.claim"],
                        }
                    },
                },
                config,
                folder=folder,
            )
            second = preparer.prepare(first, config, folder=folder)
        self.assertEqual(
            second["items"]["claim"]["source_anchor_evidence"],
            first["items"]["claim"]["source_anchor_evidence"],
        )
        self.assertEqual(
            second["items"]["claim"]["source_location"],
            first["items"]["claim"]["source_location"],
        )

    def test_existing_duplicate_source_bundle_is_normalized(self) -> None:
        anchor = {
            "path": "source.tex",
            "line_start": 1,
            "line_end": 1,
            "quoted_text": "Theorem: claim.",
            "quoted_text_sha256": hashlib.sha256(
                b"Theorem: claim."
            ).hexdigest(),
        }
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1; source.tex:1",
                        "source_anchor_evidence": [anchor, dict(anchor)],
                        "lean_declarations": ["Fixture.claim"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
            },
        )
        self.assertEqual(
            prepared["items"]["claim"]["source_anchor_evidence"], [anchor]
        )
        self.assertEqual(
            prepared["items"]["claim"]["source_location"], "source.tex:1"
        )

    def test_retired_non_source_bridge_requires_a_retained_source_item(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "source_claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                    },
                    "implementation_bridge": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:2",
                        "lean_declarations": ["Fixture.PaperInterface.bridge"],
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "retire_non_source_items": {
                    "implementation_bridge": {
                        "kind": "formalization_bridge",
                        "replacement_source_item": "source_claim",
                        "reason": "The bridge is an implementation lemma, not a source presentation.",
                    }
                },
            },
        )
        self.assertNotIn("implementation_bridge", prepared["items"])
        self.assertIn("source_claim", prepared["items"])

    def test_unselected_source_claims_and_scope_exclusions_remain_claim_bearing(self) -> None:
        """A v11 disposition is an audit obligation, not a semantic suppression."""
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "selected": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.selected"],
                    },
                    "named_result": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:4",
                        # Simulate a previously contaminated v11 map: the
                        # source text itself still makes this a named result.
                        "statement": "Theorem 1. Every feasible input has an allocation.",
                        "claim_bearing": False,
                    },
                    "retained_source_claim": {
                        "source_kind": "prose_assertion",
                        "source_location": "source.tex:8",
                        "statement": "The source asserts a visible model conclusion.",
                        "claim_bearing": True,
                    },
                    "approved_exclusion": {
                        "source_kind": "example",
                        "source_location": "source.tex:12",
                        "statement": "The paper reports this numerical example.",
                        "claim_bearing": False,
                    },
                    "context_only": {
                        "source_kind": "remark",
                        "source_location": "source.tex:16",
                        "statement": "This is contextual background only.",
                        "claim_bearing": False,
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["selected"],
                "unselected_item_dispositions": {
                    "named_result": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A dedicated Spec remains required.",
                    },
                    "retained_source_claim": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A dedicated Spec remains required.",
                    },
                    "approved_exclusion": {
                        "inventory_role": "source_scope_exclusion",
                        "scope_disposition": "user_approved_scope_exclusion",
                        "reason": "The source claim is explicitly out of scope.",
                    },
                    "context_only": {
                        "inventory_role": "source_context_observation",
                        "scope_disposition": "not_a_paper_theorem_target",
                        "reason": "This row is context rather than a claim.",
                    },
                },
            },
        )

        items = prepared["items"]
        self.assertTrue(items["named_result"]["claim_bearing"])
        self.assertEqual(
            source_item_scope_classification_errors(items["named_result"]), []
        )
        self.assertTrue(items["retained_source_claim"]["claim_bearing"])
        self.assertTrue(items["approved_exclusion"]["claim_bearing"])
        self.assertFalse(items["context_only"]["claim_bearing"])

    def test_exclusion_preserves_correction_provenance_and_is_idempotent(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "selected": {
                    "source_kind": "theorem", "source_location": "source.tex:1",
                    "lean_declarations": ["Fixture.PaperInterface.selected"],
                },
                "deferred": {
                    "source_kind": "theorem", "source_location": "source.tex:4",
                    "statement": "Theorem 2 states the source result.",
                    "claim_bearing": True,
                    "coverage_status": "corrected_source_statement",
                    "source_status": "corrected_source_target",
                    "source_defect_ids": ["PRIOR-CLARIFICATION"],
                    "corrected_target": {"statement": "The existing clarified target."},
                    "lean_declarations": ["Fixture.oldEndpoint"],
                },
            },
        }
        config = {
            "paper": "Fixture", "namespace": "Fixture", "include_specs": ["selected"],
            "unselected_item_dispositions": {
                "deferred": {
                    "inventory_role": "source_scope_exclusion",
                    "scope_disposition": "user_approved_scope_exclusion",
                    "reason": "The maintainer deferred this source result.",
                },
            },
        }
        prepared = preparer.prepare(source_map, config)
        item = prepared["items"]["deferred"]
        self.assertEqual(item["coverage_status"], "user_approved_scope_exclusion")
        self.assertNotIn("lean_declarations", item)
        for field in ("source_status", "source_defect_ids", "corrected_target"):
            self.assertEqual(item[field], source_map["items"]["deferred"][field])
        self.assertEqual(preparer.prepare(prepared, config), prepared)

    def test_unselected_reconciled_prose_definition_remains_claim_bearing(self) -> None:
        """A source-only prose-definition record cannot disappear in v11 prep."""

        statement = "For each S, r_t(S) is the type-t count divided by |S|."
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "selected": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.selected"],
                    },
                    "prose_definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:8",
                        "statement": statement,
                        "claim_bearing": False,
                        "source_prose_definition_reconciliation": {
                            "schema": 2,
                            "relation": "source_item_represents_prose_definition",
                            "presentation_sha256": "a" * 64,
                            "source_item_statement_sha256": hashlib.sha256(
                                " ".join(statement.split()).encode("utf-8")
                            ).hexdigest(),
                            "judgment": "semantically_equivalent",
                            "semantic_basis": "The source prose defines this exact ratio.",
                            "validator": "independent source-only definition review",
                            "validator_type": "human",
                            "validated_at": "2026-08-18T00:00:00Z",
                        },
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["selected"],
                "unselected_item_dispositions": {
                    "prose_definition": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A transparent Spec remains required.",
                    }
                },
            },
        )

        self.assertTrue(prepared["items"]["prose_definition"]["claim_bearing"])

    def test_unselected_disposition_retires_legacy_navigation_fields(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "selected": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.selected"],
                    },
                    "support": {
                        "source_kind": "formula",
                        "source_location": "source.tex:4",
                        "source_status": "support_only",
                        "lean_declarations": ["Fixture.legacyFormula"],
                        "proof_lean_declarations": ["Fixture.legacyProof"],
                        "support_lean_declarations": ["Fixture.legacySupport"],
                        "support_declarations": ["Fixture.legacyAlias"],
                        "source_spec_correspondence": {"schema": 1},
                    },
                    "defect": {
                        "source_kind": "claim",
                        "source_location": "source.tex:8",
                        "lean_declarations": ["Fixture.oldDefectRoute"],
                        "support_lean_declarations": ["Fixture.oldWitness"],
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["selected"],
                "unselected_item_dispositions": {
                    "support": {
                        "inventory_role": "proof_support",
                        "scope_disposition": "component_of_selected_result",
                        "reason": "The formula is reviewed through the selected result.",
                    },
                    "defect": {
                        "inventory_role": "quarantined_source_defect",
                        "scope_disposition": "documented_source_error",
                        "reason": "The source statement is false as printed.",
                        "support_lean_declarations": ["Fixture.currentWitness"],
                    },
                },
            },
        )

        support = prepared["items"]["support"]
        for field in (
            "lean_declarations",
            "proof_lean_declarations",
            "support_lean_declarations",
            "support_declarations",
            "source_spec_correspondence",
        ):
            self.assertNotIn(field, support)
        defect = prepared["items"]["defect"]
        self.assertNotIn("lean_declarations", defect)
        self.assertEqual(
            defect["support_lean_declarations"], ["Fixture.currentWitness"]
        )

    def test_presentation_alias_drops_stale_source_spec_correspondence(self) -> None:
        """A repeated presentation cannot retain a second claim-level binding."""

        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "canonical": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                    },
                    "repeat": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:4",
                        "source_spec_correspondence": {
                            "schema": 1,
                            "source_claim_atoms": [],
                            "direct_declaration": "Fixture.PaperInterface.old_duplicateSpec",
                        },
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "presentation_aliases": {
                    "repeat": {
                        "canonical_source_item": "canonical",
                        "semantic_basis": "Both source presentations state the same theorem.",
                    }
                },
            },
        )

        self.assertNotIn(
            "source_spec_correspondence", prepared["items"]["repeat"]
        )

    def test_presentation_alias_cannot_retain_a_second_direct_route(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "canonical": {
                    "source_kind": "theorem",
                    "source_location": "source.tex:1",
                    "lean_declarations": ["Fixture.PaperInterface.claim"],
                },
                "repeat": {
                    "source_kind": "theorem",
                    "source_location": "source.tex:4",
                    "lean_declarations": ["Fixture.PaperInterface.old_duplicate"],
                    "proof_lean_declarations": ["Fixture.PaperInterface.old_duplicate"],
                    "support_lean_declarations": ["Fixture.PaperInterface.oldDuplicateSpec"],
                },
            },
        }
        prepared = preparer.prepare(
            source_map,
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "presentation_aliases": {
                    "repeat": {
                        "canonical_source_item": "canonical",
                        "semantic_basis": "Both exact source presentations state the same theorem.",
                    }
                },
            },
        )
        alias = prepared["items"]["repeat"]
        self.assertNotIn("lean_declarations", alias)
        self.assertNotIn("proof_lean_declarations", alias)
        self.assertNotIn("support_lean_declarations", alias)
        self.assertNotIn("semantic_contract", alias)
        self.assertFalse(alias["claim_bearing"])
        self.assertEqual(alias["inventory_role"], "source_presentation_alias")
        self.assertEqual(
            alias["source_presentation_alias"]["validated_at"],
            "2026-08-18T00:00:00Z",
        )
        self.assertEqual(prepared["source_spec_correspondence_schema"], 1)

    def test_renumbered_presentation_alias_pins_source_restatement_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.txt").write_text(
                "Theorem 1. First presentation.\n"
                "Theorem 2 is a restated version of Theorem 1.\n"
                "Theorem 2. Second presentation.\n",
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "canonical": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:3",
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                        },
                        "repeat": {
                            "source_kind": "theorem",
                            "source_location": "source.txt:1",
                        },
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "presentation_aliases": {
                        "repeat": {
                            "canonical_source_item": "canonical",
                            "semantic_basis": "The source expressly restates Theorem 1 as Theorem 2.",
                            "label_relation": "source_explicit_renumbered_restatement",
                            "source_restatement_evidence_location": "source.txt:2",
                        }
                    },
                },
                folder=folder,
            )
        relation = prepared["items"]["repeat"]["source_presentation_alias"]
        self.assertEqual(
            relation["label_relation"],
            "source_explicit_renumbered_restatement",
        )
        self.assertEqual(
            relation["source_restatement_evidence"]["line_start"], 2
        )

    def test_source_semantic_declaration_drops_stale_presentation_alias(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "claim_bearing": False,
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_route",
                        "scope_disposition_note": "Obsolete migration state.",
                        "source_presentation_alias": {
                            "schema": 1,
                            "canonical_source_item": "old_owner",
                            "relation": "repeated_source_presentation",
                            "semantic_basis": "An obsolete migration classified this as an alias.",
                            "validator": "old migration",
                            "validated_at": "2026-08-18T00:00:00Z",
                        },
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "semantic_route_schema": 2,
                "include_specs": [],
                "source_semantic_declarations": {
                    "definition": ["Fixture.ActualDefinition"]
                },
            },
        )
        item = prepared["items"]["definition"]
        self.assertNotIn("source_presentation_alias", item)
        self.assertNotIn("scope_disposition", item)
        self.assertNotIn("scope_disposition_note", item)
        self.assertTrue(item["claim_bearing"])
        self.assertEqual(item["inventory_role"], "source_semantic_declaration")

    def test_selected_result_drops_stale_inventory_disposition(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "result": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "claim_bearing": True,
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "scope_disposition_note": "Obsolete migration state.",
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "paper_interface_module": "",
                "semantic_route_schema": 2,
                "include_specs": ["result"],
                "source_item_for_spec": {"result": "result"},
                "evidence_declaration_for_spec": {"result": "result_provesSpec"},
            },
        )
        item = prepared["items"]["result"]
        self.assertNotIn("inventory_role", item)
        self.assertNotIn("scope_disposition", item)
        self.assertNotIn("scope_disposition_note", item)
        self.assertEqual(
            item["semantic_contract"]["evidence_declaration"],
            "Fixture.result_provesSpec",
        )

    def test_corrected_target_preserves_archival_statement_and_pins_basis(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / "source.tex"
            source.write_text("Archival proposition.\n", encoding="utf-8")
            basis = folder / "docs.md"
            basis.write_text(
                "The task owner approved this corrected mathematical target.\n",
                encoding="utf-8",
            )
            (folder / "audit").mkdir()
            (folder / "audit" / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "schema": 2,
                        "paper": folder.name,
                        "defects": [
                            {
                                "id": "FIXTURE-01",
                                "statement_impact": "source_statement",
                                "resolution": "corrected_source_statement",
                            },
                            {
                                "id": "FIXTURE-PROOF-TYPO-02",
                                "statement_impact": "proof_only",
                                "resolution": "source_typo",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "theorem",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                            "source_defect_ids": ["FIXTURE-PROOF-TYPO-02"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "corrected_targets": {
                        "claim": {
                            "statement": "Approved corrected proposition.",
                            "archival_statement": "Archival proposition.",
                            "governing_defect_ids": ["FIXTURE-01"],
                            "archival_source_locator": "source.tex:1",
                            "source_note": "The archival wording is not equivalent to the approved target.",
                            "approval": {
                                "kind": "documented_source_correction",
                                "recorded_at": "2026-08-18",
                                "reference": "Fixture correction note.",
                                "artifact_path": "docs.md",
                                "artifact_excerpt": "The task owner approved this corrected mathematical target.",
                            },
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["claim"]
        target = item["corrected_target"]
        self.assertEqual(item["statement"], "Archival proposition.")
        self.assertEqual(item["coverage_status"], "corrected_source_statement")
        self.assertEqual(
            item["source_defect_ids"],
            ["FIXTURE-PROOF-TYPO-02", "FIXTURE-01"],
        )
        self.assertIs(target["archival_equivalence_claimed"], False)
        self.assertEqual(
            target["archival_source_quote_sha256"],
            hashlib.sha256(b"Archival proposition.").hexdigest(),
        )
        self.assertEqual(
            target["approval"]["artifact_excerpt_sha256"],
            hashlib.sha256(
                b"The task owner approved this corrected mathematical target."
            ).hexdigest(),
        )
        self.assertEqual(
            target["corrected_target_review_sha256"],
            corrected_target_review_digest(target),
        )
        self.assertEqual(
            target["corrected_target_sha256"],
            corrected_target_record_digest(target),
        )

    def test_corrected_target_original_locator_is_metadata_not_a_read_fallback(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Archival proposition.\n", encoding="utf-8"
            )
            current_artifact = folder / "docs.md"
            current_artifact.write_text(
                "The task owner approved this corrected mathematical target.\n",
                encoding="utf-8",
            )
            (folder / "audit").mkdir()
            (folder / "audit" / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "defects": [
                            {
                                "id": "FIXTURE-01",
                                "statement_impact": "source_statement",
                                "resolution": "corrected_source_statement",
                            }
                        ]
                    }
                ),
                encoding="utf-8",
            )
            config = {
                "corrected_targets": {
                    "claim": {
                        "statement": "Approved corrected proposition.",
                        "archival_statement": "Archival proposition.",
                        "governing_defect_ids": ["FIXTURE-01"],
                        "archival_source_locator": "source.tex:1",
                        "source_note": "The archival wording is not equivalent.",
                        "approval": {
                            "kind": "documented_source_correction",
                            "recorded_at": "2026-09-05",
                            "reference": "Fixture correction note.",
                            "artifact_path": "docs.md",
                            "original_artifact_path": "retired/OLD_APPROVAL.md",
                            "artifact_excerpt": (
                                "The task owner approved this corrected "
                                "mathematical target."
                            ),
                        },
                    }
                }
            }
            items: dict[str, dict[str, object]] = {"claim": {}}
            preparer._apply_corrected_targets(items, config, folder=folder)
            target = items["claim"]["corrected_target"]
            self.assertEqual(
                target["approval"]["original_artifact_path"],
                "retired/OLD_APPROVAL.md",
            )
            self.assertFalse((folder / "retired" / "OLD_APPROVAL.md").exists())
            self.assertEqual(
                target["corrected_target_sha256"],
                corrected_target_record_digest(target),
            )

            malformed = json.loads(json.dumps(config))
            malformed["corrected_targets"]["claim"]["approval"][
                "original_artifact_path"
            ] = "../OLD_APPROVAL.md"
            with self.assertRaisesRegex(
                preparer.PreparationError, "original_artifact_path"
            ):
                preparer._apply_corrected_targets(
                    {"claim": {}}, malformed, folder=folder
                )

            current_artifact.unlink()
            with self.assertRaisesRegex(
                preparer.PreparationError, "readable paper-local artifact_path"
            ):
                preparer._apply_corrected_targets(
                    {"claim": {}}, config, folder=folder
                )

    def test_corrected_target_requires_current_defect_ledger_route(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text("Archival proposition.\n", encoding="utf-8")
            (folder / "docs.md").write_text(
                "The task owner approved this corrected mathematical target.\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                preparer.PreparationError, "source-proof fidelity ledger"
            ):
                preparer.prepare(
                    {
                        "paper": "Fixture",
                        "items": {
                            "claim": {
                                "source_kind": "theorem",
                                "source_location": "source.tex:1",
                                "lean_declarations": ["Fixture.PaperInterface.claim"],
                            }
                        },
                    },
                    {
                        "paper": "Fixture",
                        "namespace": "Fixture",
                        "include_specs": ["claim"],
                        "corrected_targets": {
                            "claim": {
                                "statement": "Approved corrected proposition.",
                                "archival_statement": "Archival proposition.",
                                "governing_defect_ids": ["FIXTURE-01"],
                                "archival_source_locator": "source.tex:1",
                                "source_note": "The archival wording is not equivalent.",
                                "approval": {
                                    "kind": "documented_source_correction",
                                    "recorded_at": "2026-08-18",
                                    "reference": "Fixture correction note.",
                                    "artifact_path": "docs.md",
                                    "artifact_excerpt": "The task owner approved this corrected mathematical target.",
                                },
                            }
                        },
                    },
                    folder=folder,
                )

    def test_corrected_definition_retains_direct_semantic_route(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Archival pointwise definition.\n", encoding="utf-8"
            )
            (folder / "docs.md").write_text(
                "The task owner approved this almost-everywhere definition.\n",
                encoding="utf-8",
            )
            (folder / "audit").mkdir()
            (folder / "audit" / "source_proof_fidelity.json").write_text(
                json.dumps(
                    {
                        "schema": 2,
                        "paper": folder.name,
                        "defects": [
                            {
                                "id": "FIXTURE-DEF-01",
                                "statement_impact": "source_statement",
                                "resolution": "corrected_source_statement",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "definition": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "claim_bearing": True,
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "semantic_route_schema": 2,
                    "include_specs": [],
                    "source_semantic_declarations": {
                        "definition": ["Fixture.CorrectedDefinition"]
                    },
                    "corrected_targets": {
                        "definition": {
                            "statement": "Approved almost-everywhere definition.",
                            "archival_statement": "Archival pointwise definition.",
                            "governing_defect_ids": ["FIXTURE-DEF-01"],
                            "archival_source_locator": "source.tex:1",
                            "source_note": "The archival pointwise wording is not law invariant.",
                            "approval": {
                                "kind": "documented_source_correction",
                                "recorded_at": "2026-08-30",
                                "reference": "Fixture correction note.",
                                "artifact_path": "docs.md",
                                "artifact_excerpt": "The task owner approved this almost-everywhere definition.",
                            },
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["definition"]
        self.assertEqual(item["inventory_role"], "source_semantic_declaration")
        self.assertEqual(
            item["lean_declarations"], ["Fixture.CorrectedDefinition"]
        )
        self.assertIn("corrected_target", item)
        self.assertEqual(item["coverage_status"], "corrected_source_statement")

    def test_explicit_realization_endpoint_is_recorded_in_contract(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.definition"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["definition"],
                "evidence_declaration_for_spec": {
                    "definition": "definition_realizes_spec"
                },
            },
        )
        self.assertEqual(
            prepared["items"]["definition"]["semantic_contract"]["evidence_declaration"],
            "Fixture.PaperInterface.definition_realizes_spec",
        )

    def test_fully_qualified_proof_interface_endpoint_is_preserved(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.definition"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["definition"],
                "evidence_declaration_for_spec": {
                    "definition": "Fixture.ProofInterface.definitionSpec_proof"
                },
            },
        )
        self.assertEqual(
            prepared["items"]["definition"]["semantic_contract"]["evidence_declaration"],
            "Fixture.ProofInterface.definitionSpec_proof",
        )

    def test_definition_reconciliation_is_preserved_by_preparation(self) -> None:
        statement = "The source predicate is exactly the displayed relation."
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "statement": statement,
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.definition"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["definition"],
                "prose_definition_reconciliations": {
                    "definition": {
                        "presentation_sha256": "a" * 64,
                        "semantic_basis": (
                            "The literal source definition is represented by the "
                            "selected source-map statement."
                        ),
                        "validator": "independent definition reviewer",
                        "validator_type": "agent",
                        "validated_at": "2026-08-19T00:00:00Z",
                    }
                },
            },
        )
        reconciliation = prepared["items"]["definition"][
            "source_prose_definition_reconciliation"
        ]
        self.assertEqual(reconciliation["presentation_sha256"], "a" * 64)
        self.assertEqual(
            reconciliation["source_item_statement_sha256"],
            hashlib.sha256(statement.encode("utf-8")).hexdigest(),
        )

    def test_existing_v11_proof_endpoint_is_preserved_without_reconfiguration(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.claimSpec",
                            "evidence_declaration": "Fixture.PaperInterface.claimSpec_proof",
                        },
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
            },
        )
        self.assertEqual(
            prepared["items"]["claim"]["semantic_contract"]["evidence_declaration"],
            "Fixture.PaperInterface.claimSpec_proof",
        )

    def test_root_interface_contract_and_initialized_atom_keep_the_exact_anchor(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "statement": "The source predicate is exactly the displayed relation.",
                        "source_kind": "definition",
                        "source_location": "source.txt:4-5",
                        "source_anchor_evidence": [
                            {
                                "path": "source.txt",
                                "line_start": 4,
                                "line_end": 5,
                                "quoted_text": "Source relation.",
                                "quoted_text_sha256": hashlib.sha256(
                                    b"Source relation."
                                ).hexdigest(),
                            }
                        ],
                        "lean_declarations": ["Fixture.claim"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "paper_interface_module": "",
                "include_specs": ["claim"],
                "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                "initialize_selected_source_claim_atoms": True,
            },
        )
        item = prepared["items"]["claim"]
        self.assertEqual(item["semantic_contract"]["spec_declaration"], "Fixture.claimSpec")
        self.assertEqual(
            item["semantic_contract"]["evidence_declaration"], "Fixture.claimSpec_proof"
        )
        self.assertEqual(item["source_claim_atoms"][0]["source_locator"], "source.txt:4-5")
        self.assertEqual(
            item["source_claim_atoms"][0]["reviewed_lean_route"],
            "Fixture.claimSpec_proof",
        )

    def test_initialized_atom_uses_curated_semantic_source_core(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.txt").write_text(
                "Theorem 1. Claim.\nProof explanation.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "statement": "The displayed theorem is the source claim.",
                            "source_kind": "theorem",
                            "source_location": "source.txt:1-2",
                            "source_anchor_evidence": [
                                {
                                    "path": "source.txt",
                                    "line_start": 1,
                                    "line_end": 2,
                                    "quoted_text": "Theorem 1. Claim.\nProof explanation.",
                                    "quoted_text_sha256": hashlib.sha256(
                                        b"Theorem 1. Claim.\nProof explanation."
                                    ).hexdigest(),
                                }
                            ],
                            "lean_declarations": ["Fixture.claim"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "include_specs": ["claim"],
                    "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                    "semantic_source_anchor_overrides": {
                        "claim": {
                            "source_location": "source.txt:1",
                            "reason": "The theorem statement ends before proof explanation.",
                        }
                    },
                    "initialize_selected_source_claim_atoms": True,
                },
                folder=folder,
            )
        atom = prepared["items"]["claim"]["source_claim_atoms"][0]
        self.assertEqual(atom["source_locator"], "source.txt:1-1")
        self.assertEqual(atom["source_quote_sha256"], hashlib.sha256(
            b"Theorem 1. Claim."
        ).hexdigest())

    def test_explicit_atom_selects_statement_anchor_from_multi_span_source_item(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Statement span.\nProof support span.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "statement": "The displayed statement is the source claim.",
                            "source_kind": "theorem",
                            "source_location": "source.tex:1; source.tex:2",
                            "lean_declarations": ["Fixture.claim"],
                            "source_anchor_evidence": [
                                {"path": "source.tex"},
                                {"path": "source.tex"},
                            ],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "include_specs": ["claim"],
                    "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                    "explicit_source_claim_atoms": {
                        "claim": {
                            "id": "claim",
                            "source_locator": "source.tex:1",
                            "semantic_claim": "The displayed statement is the source claim.",
                        }
                    },
                    "initialize_selected_source_claim_atoms": True,
                },
                folder=folder,
            )
        atom = prepared["items"]["claim"]["source_claim_atoms"][0]
        self.assertEqual(atom["source_locator"], "source.tex:1")
        self.assertEqual(atom["semantic_claim"], "The displayed statement is the source claim.")
        self.assertEqual(atom["reviewed_lean_route"], "Fixture.claimSpec_proof")

    def test_explicit_atomization_preserves_each_claim_in_compound_statement(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Core conclusion. Sufficient special case.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "statement": "A core conclusion and its sufficient case.",
                            "source_kind": "lemma",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.claim"],
                            "source_anchor_evidence": [{"path": "source.tex"}],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "include_specs": ["claim"],
                    "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                    "explicit_source_claim_atoms": {
                        "claim": [
                            {
                                "id": "claim.core",
                                "source_locator": "source.tex:1",
                                "semantic_claim": "The core conclusion.",
                                "verbatim_source_clause": "Core conclusion.",
                            },
                            {
                                "id": "claim.sufficient_case",
                                "source_locator": "source.tex:1",
                                "semantic_claim": "The sufficient special case.",
                                "verbatim_source_clause": "Sufficient special case.",
                            },
                        ]
                    },
                    "initialize_selected_source_claim_atoms": True,
                },
                folder=folder,
            )
        atoms = prepared["items"]["claim"]["source_claim_atoms"]
        self.assertEqual(
            [atom["id"] for atom in atoms],
            ["claim.core", "claim.sufficient_case"],
        )
        self.assertEqual(
            {atom["reviewed_lean_route"] for atom in atoms},
            {"Fixture.claimSpec_proof"},
        )
        self.assertEqual({atom["identity_schema"] for atom in atoms}, {3})
        self.assertEqual(
            [atom["verbatim_source_clause"] for atom in atoms],
            ["Core conclusion.", "Sufficient special case."],
        )

    def test_explicit_multi_atomization_requires_unique_verbatim_clauses(self) -> None:
        def prepare_with_clauses(
            first_clause: str | None,
            second_clause: str | None,
        ) -> dict[str, object]:
            with tempfile.TemporaryDirectory() as temporary:
                folder = Path(temporary)
                (folder / "source.tex").write_text(
                    "Repeated clause. Repeated clause. Distinct conclusion.\n",
                    encoding="utf-8",
                )
                atoms: list[dict[str, str]] = [
                    {
                        "id": "claim.first",
                        "source_locator": "source.tex:1",
                        "semantic_claim": "The first source clause.",
                    },
                    {
                        "id": "claim.second",
                        "source_locator": "source.tex:1",
                        "semantic_claim": "The second source clause.",
                    },
                ]
                if first_clause is not None:
                    atoms[0]["verbatim_source_clause"] = first_clause
                if second_clause is not None:
                    atoms[1]["verbatim_source_clause"] = second_clause
                return preparer.prepare(
                    {
                        "paper": "Fixture",
                        "items": {
                            "claim": {
                                "statement": "A compound source statement.",
                                "source_kind": "lemma",
                                "source_location": "source.tex:1",
                                "lean_declarations": ["Fixture.claim"],
                                "source_anchor_evidence": [{"path": "source.tex"}],
                            }
                        },
                    },
                    {
                        "paper": "Fixture",
                        "namespace": "Fixture",
                        "paper_interface_module": "",
                        "include_specs": ["claim"],
                        "evidence_declaration_for_spec": {
                            "claim": "claimSpec_proof"
                        },
                        "explicit_source_claim_atoms": {"claim": atoms},
                        "initialize_selected_source_claim_atoms": True,
                    },
                    folder=folder,
                )

        with self.assertRaisesRegex(
            preparer.PreparationError,
            "each atom in a multi-clause source presentation needs one "
            "verbatim_source_clause",
        ):
            prepare_with_clauses(None, "Distinct conclusion.")

        with self.assertRaisesRegex(
            preparer.PreparationError,
            "verbatim_source_clause must occur exactly once",
        ):
            prepare_with_clauses("Repeated clause.", "Distinct conclusion.")

        with self.assertRaisesRegex(
            preparer.PreparationError,
            "verbatim_source_clause must occur exactly once",
        ):
            prepare_with_clauses("Absent clause.", "Distinct conclusion.")

    def test_explicit_atomization_splits_a_compound_source_definition(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "compound_definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1-4",
                        "source_anchor_evidence": [{"path": "source.tex"}],
                        "lean_declarations": [
                            "Fixture.PaperInterface.first",
                            "Fixture.PaperInterface.second",
                        ],
                        "claim_bearing": True,
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["first", "second"],
                "atomize_source_items": {
                    "compound_definition": {
                        "reason": "The source defines the two model branches in one display.",
                        "items": {
                            "first_definition": {
                                "statement": "First branch.",
                                "source_note": "The first branch has its own semantic target.",
                                "source_defect_ids": ["fixture-first-branch-boundary"],
                                "lean_declarations": ["Fixture.PaperInterface.first"],
                            },
                            "second_definition": {
                                "statement": "Second branch.",
                                "source_note": "The second branch has its own semantic target.",
                                "lean_declarations": ["Fixture.PaperInterface.second"],
                            },
                        },
                    }
                },
            },
        )
        self.assertNotIn("compound_definition", prepared["items"])
        self.assertEqual(
            prepared["items"]["first_definition"]["semantic_contract"]["spec_declaration"],
            "Fixture.PaperInterface.firstSpec",
        )
        self.assertEqual(
            prepared["items"]["second_definition"]["source_atomization"]["parent_source_item"],
            "compound_definition",
        )
        self.assertEqual(
            prepared["items"]["first_definition"]["source_defect_ids"],
            ["fixture-first-branch-boundary"],
        )

    def test_atomization_rerun_clears_parent_pending_disposition(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "compound_definition": {
                    "source_kind": "definition",
                    "source_location": "source.tex:1-4",
                    "source_anchor_evidence": [{"path": "source.tex"}],
                    "lean_declarations": ["Fixture.PaperInterface.first"],
                    "claim_bearing": True,
                    "inventory_role": "compound_source_result_pending_atomization",
                    "scope_disposition": "pending_source_claim_atomization",
                    "scope_disposition_note": "Split this source row before review.",
                }
            },
        }
        config = {
            "paper": "Fixture",
            "namespace": "Fixture",
            "include_specs": ["first"],
            "atomize_source_items": {
                "compound_definition": {
                    "reason": "The source has one independently reviewable branch.",
                    "items": {
                        "first_definition": {
                            "statement": "First branch.",
                            "source_note": "The branch has its own semantic target.",
                            "lean_declarations": ["Fixture.PaperInterface.first"],
                        }
                    },
                }
            },
        }
        first = preparer.prepare(source_map, config)
        second = preparer.prepare(json.loads(json.dumps(first)), config)
        child = second["items"]["first_definition"]
        self.assertNotIn("inventory_role", child)
        self.assertNotIn("scope_disposition", child)
        self.assertNotIn("scope_disposition_note", child)
        self.assertEqual(
            child["semantic_contract"]["spec_declaration"],
            "Fixture.PaperInterface.firstSpec",
        )

    def test_atomization_rerun_refreshes_curator_owned_defect_route(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "compound_definition": {
                    "source_kind": "definition",
                    "source_location": "source.tex:1-4",
                    "source_anchor_evidence": [{"path": "source.tex"}],
                    "lean_declarations": ["Fixture.PaperInterface.first"],
                    "claim_bearing": True,
                }
            },
        }
        config = {
            "paper": "Fixture",
            "namespace": "Fixture",
            "include_specs": ["first"],
            "atomize_source_items": {
                "compound_definition": {
                    "reason": "The source has one independently reviewable branch.",
                    "items": {
                        "first_definition": {
                            "statement": "First branch.",
                            "source_note": "The branch has its own semantic target.",
                            "lean_declarations": ["Fixture.PaperInterface.first"],
                        }
                    },
                }
            },
        }
        first = preparer.prepare(source_map, config)
        config["atomize_source_items"]["compound_definition"]["items"][
            "first_definition"
        ]["source_defect_ids"] = ["fixture-corrected-branch"]
        second = preparer.prepare(json.loads(json.dumps(first)), config)
        self.assertEqual(
            second["items"]["first_definition"]["source_defect_ids"],
            ["fixture-corrected-branch"],
        )

    def test_consolidation_restores_one_source_definition_and_exact_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Definition: both branches are one claim.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "first_branch": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.first"],
                            "source_presentation_reconciliation": {
                                "stale_split_row_relation": True
                            },
                        },
                        "second_branch": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.second"],
                        },
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["definition"],
                    "evidence_declaration_for_spec": {
                        "definition": "definition_realizes_spec"
                    },
                    "evidence_mode_for_spec": {
                        "definition": "definitionally_realizes"
                    },
                    "consolidate_source_items": {
                        "definition": {
                            "source_items": ["first_branch", "second_branch"],
                            "statement": "Definition: both branches are one claim.",
                            "source_note": "The source has one definition with two semantic branches.",
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.definition"],
                            "source_claim_atom": {
                                "id": "definition.combined",
                                "source_locator": "source.tex:1",
                                "semantic_claim": "The source definition contains both branches.",
                            },
                        }
                    },
                },
                folder=folder,
            )
        self.assertNotIn("first_branch", prepared["items"])
        self.assertNotIn("second_branch", prepared["items"])
        item = prepared["items"]["definition"]
        self.assertEqual(item["semantic_contract"]["evidence_mode"], "definitionally_realizes")
        self.assertNotIn("source_presentation_reconciliation", item)
        self.assertEqual(item["source_anchor_evidence"][0]["quoted_text"], "Definition: both branches are one claim.")
        self.assertEqual(
            item["source_claim_atoms"][0]["reviewed_lean_route"],
            "Fixture.PaperInterface.definitionSpec",
        )


if __name__ == "__main__":
    unittest.main()
