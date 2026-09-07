from __future__ import annotations

import copy
import hashlib
import json
import unittest
from pathlib import Path
from unittest import mock

from scripts.audit_evidence_integrity import (
    source_claim_atom_semantic_sha256,
    source_claim_atoms_semantic_sha256,
    source_spec_correspondence_item_identity_sha256,
)
from scripts.obligation_evidence_projection import (
    LEAN_PROOF_ENDPOINT_CONTRACT_SHA256,
    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT_SHA256,
    ObligationEvidenceProjectionError,
    project_direct_v11_leaves_from_validated_inputs,
    project_focused_build_leaf_from_validated_inputs,
    project_semantic_prerequisite_leaves_from_validated_inputs,
    project_source_route_leaves_from_validated_inputs,
    validate_current_direct_v11_semantic_targets,
    validated_direct_v11_claims,
)
from scripts.obligation_evidence_graph import LeanSemanticTargetKind
from scripts.obligation_evidence_contracts import (
    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT,
)
from scripts.obligation_evidence_issuance import (
    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256,
    STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256,
)
from scripts.corrected_target_identity import (
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_review_digest,
)
from scripts.obligation_evidence_planner import plan_obligation_evidence
from scripts.obligation_paper_index import build_paper_obligation_index_from_preflight
from scripts.obligation_preflight import structural_obligation_preflight
from scripts.tests.obligation_historical_fixtures import (
    GKGMM_PAPER_DIR,
    IM05_PAPER_DIR,
    NOOTHIGATTU_PAPER_DIR,
    SESHADRI_PAPER_DIR,
    load_im05_audit_json,
    require_historical_fixture,
)


ROOT = Path(__file__).resolve().parents[2]
IM05 = IM05_PAPER_DIR
GKGMM = GKGMM_PAPER_DIR
NOOTHIGATTU = NOOTHIGATTU_PAPER_DIR
SESHADRI = SESHADRI_PAPER_DIR


def load_inputs():
    return (
        load_im05_audit_json("paper_statement_map.json"),
        load_im05_audit_json("v11_raw_source_spec_screening.json"),
        load_im05_audit_json("lean_signature_manifest_cache_authority.json"),
        hashlib.sha256((IM05 / "FINAL_CLOSURE_RECEIPT.md").read_bytes()).hexdigest(),
    )


def load_prerequisite_inputs():
    source_map, _screening, manifests, transaction = load_inputs()
    return (
        source_map,
        load_im05_audit_json("paper_semantic_prerequisites.json"),
        load_im05_audit_json("library_semantic_review.json"),
        manifests,
        transaction,
    )


class ObligationEvidenceMigrationTests(unittest.TestCase):
    def project(self, source_map, screening, manifests, transaction):
        preflight = structural_obligation_preflight(
            source_map, paper="IM05MarriageHonestyStability"
        ).require_current()
        assert preflight.route_set is not None
        return project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=screening,
            route_set=preflight.route_set,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )

    def test_proof_support_leaf_uses_claim_anchor_not_context_bundle(self) -> None:
        claim = "External theorem statement."
        context = "Definitions needed to read the theorem."
        claim_sha = hashlib.sha256(claim.encode()).hexdigest()
        context_sha = hashlib.sha256(context.encode()).hexdigest()
        source_map = {
            "schema": 1,
            "paper": "Fixture",
            "source_artifact_sha256": "f" * 64,
            "semantic_contract_schema": 1,
            "semantic_route_schema": 2,
            "items": {
                "external_theorem": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "inventory_role": "proof_support",
                    "statement": claim,
                    "source_anchor_evidence": [
                        {
                            "quoted_text": claim,
                            "quoted_text_sha256": claim_sha,
                        }
                    ],
                    "semantic_context_requirements": [
                        {
                            "source_anchor_evidence": [
                                {
                                    "quoted_text": context,
                                    "quoted_text_sha256": context_sha,
                                }
                            ]
                        }
                    ],
                }
            },
        }
        preflight = structural_obligation_preflight(
            source_map, paper="Fixture"
        ).require_current()

        projection = project_source_route_leaves_from_validated_inputs(
            source_map=source_map,
            preflight=preflight,
            issuance_authority_sha256="a" * 64,
            issuance_assurance_contract_sha256="b" * 64,
        )

        self.assertEqual(
            preflight.route_source_quote_sha256s["external_theorem"],
            (claim_sha,),
        )
        self.assertEqual(len(projection.navigation["external_theorem"]), 1)

    def test_current_closed_im05_projects_without_lean_or_llm(self) -> None:
        inputs = load_inputs()
        with mock.patch(
            "subprocess.run", side_effect=AssertionError("producer invoked")
        ):
            projection = self.project(*inputs)
        self.assertGreater(len(projection.graph.leaves), 0)
        self.assertEqual(
            len(projection.graph.root_leaf_sha256s),
            2 * len(projection.navigation),
        )
        self.assertFalse(projection.projection()["acceptance_credential"])
        self.assertFalse(projection.projection()["complete_paper_closeout_graph"])
        self.assertEqual(
            {issuance.leaf_sha256 for issuance in projection.issuances},
            set(projection.graph.leaves),
        )
        plan = plan_obligation_evidence(
            projection.graph,
            {
                digest: leaf.projection()
                for digest, leaf in projection.graph.leaves.items()
            },
            projection.issuances,
            authenticated_authority_sha256s=[projection.issuance_authority_sha256],
        )
        self.assertTrue(plan.complete)
        self.assertEqual(plan.work_queue, ())
        preflight = structural_obligation_preflight(
            inputs[0], paper="IM05MarriageHonestyStability"
        )
        partial_index = build_paper_obligation_index_from_preflight(
            projection.graph,
            preflight,
            complete_paper_surface=False,
        )
        self.assertFalse(partial_index.complete_paper_surface)

    def test_current_im05_projects_every_source_route_from_preflight(self) -> None:
        source_map, _screening, _manifests, transaction = load_inputs()
        preflight = structural_obligation_preflight(
            source_map, paper="IM05MarriageHonestyStability"
        )
        with mock.patch("subprocess.run", side_effect=AssertionError("producer invoked")):
            projection = project_source_route_leaves_from_validated_inputs(
                source_map=source_map,
                preflight=preflight,
                issuance_authority_sha256=transaction,
                issuance_assurance_contract_sha256=(
                    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
                ),
            )
        self.assertEqual(
            set(projection.navigation),
            set(preflight.route_obligation_counts),
        )
        self.assertEqual(
            set(projection.graph.leaves),
            {issuance.leaf_sha256 for issuance in projection.issuances},
        )
        for source_item_id, digests in projection.navigation.items():
            self.assertEqual(
                tuple(
                    sorted(
                        projection.graph.leaves[digest].semantic_payload[
                            "source_quote_sha256"
                        ]
                        for digest in digests
                    )
                ),
                preflight.route_source_quote_sha256s[source_item_id],
            )

    def test_current_gkgmm_projects_all_endpoints_without_endpoint_manifests(
        self,
    ) -> None:
        require_historical_fixture(GKGMM)
        audit = GKGMM / "audit"
        source_map = json.loads((audit / "paper_statement_map.json").read_text())
        preflight = structural_obligation_preflight(
            source_map,
            paper="GKGMM19IterativeLocalVoting",
            paper_prerequisites=json.loads(
                (audit / "paper_semantic_prerequisites.json").read_text()
            ),
            library_semantic_review=json.loads(
                (audit / "library_semantic_review.json").read_text()
            ),
        ).require_current()
        assert preflight.route_set is not None
        projection = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=json.loads(
                (audit / "v11_raw_source_spec_screening.json").read_text()
            ),
            route_set=preflight.route_set,
            issuance_authority_sha256="f" * 64,
            issuance_assurance_contract_sha256=(
                STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(len(projection.navigation), 11)
        self.assertEqual(
            {
                projection.graph.leaves[
                    route["proof_endpoint_leaf_sha256"]
                ].contract_sha256
                for route in projection.navigation.values()
            },
            {LEAN_PROOF_ENDPOINT_CONTRACT_SHA256},
        )

    def test_current_schema3_screening_projects_all_noothigattu_results(
        self,
    ) -> None:
        require_historical_fixture(NOOTHIGATTU)
        audit = NOOTHIGATTU / "audit"
        source_map = json.loads((audit / "paper_statement_map.json").read_text())
        screening = json.loads(
            (audit / "v11_raw_source_spec_screening.json").read_text()
        )
        preflight = structural_obligation_preflight(
            source_map,
            paper="NoothigattuEtAl2020PairwiseComparisons",
            paper_prerequisites=json.loads(
                (audit / "paper_semantic_prerequisites.json").read_text()
            ),
            library_semantic_review=json.loads(
                (audit / "library_semantic_review.json").read_text()
            ),
        ).require_current()
        assert preflight.route_set is not None

        _source_artifact, claims = validated_direct_v11_claims(
            source_map=source_map,
            v11_screening=screening,
            route_set=preflight.route_set,
        )

        self.assertEqual(screening["schema"], 3)
        self.assertEqual(len(claims), 10)

    def test_schema3_screening_source_item_binding_fails_closed(self) -> None:
        require_historical_fixture(NOOTHIGATTU)
        audit = NOOTHIGATTU / "audit"
        source_map = json.loads((audit / "paper_statement_map.json").read_text())
        screening = json.loads(
            (audit / "v11_raw_source_spec_screening.json").read_text()
        )
        first = next(iter(screening["items"].values()))
        first["source_item"] = "different_source_item"
        preflight = structural_obligation_preflight(
            source_map,
            paper="NoothigattuEtAl2020PairwiseComparisons",
            paper_prerequisites=json.loads(
                (audit / "paper_semantic_prerequisites.json").read_text()
            ),
            library_semantic_review=json.loads(
                (audit / "library_semantic_review.json").read_text()
            ),
        ).require_current()
        assert preflight.route_set is not None

        with self.assertRaisesRegex(
            ObligationEvidenceProjectionError,
            "names a different source item",
        ):
            validated_direct_v11_claims(
                source_map=source_map,
                v11_screening=screening,
                route_set=preflight.route_set,
            )

    def test_direct_projection_derives_endpoint_from_authenticated_pair(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        source_item_id, item = next(
            (key, value)
            for key, value in source_map["items"].items()
            if value.get("semantic_contract")
        )
        endpoint = item["semantic_contract"]["evidence_declaration"]
        changed_manifests = copy.deepcopy(manifests)
        changed_manifests["entries"] = [
            entry
            for entry in changed_manifests["entries"]
            if entry["qualified_declaration"] != endpoint
        ]
        projected = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=screening,
            route_set=structural_obligation_preflight(
                source_map, paper="IM05MarriageHonestyStability"
            ).require_current().route_set,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        endpoint_sha256 = projected.navigation[source_item_id][
            "proof_endpoint_leaf_sha256"
        ]
        spec_sha256 = projected.navigation[source_item_id]["spec_leaf_sha256"]
        leaf = projected.graph.leaves[endpoint_sha256]
        self.assertEqual(leaf.contract_sha256, LEAN_PROOF_ENDPOINT_CONTRACT_SHA256)
        self.assertEqual(
            leaf.semantic_payload["semantic_target_kind"],
            LeanSemanticTargetKind.PROOF_ENDPOINT.value,
        )
        self.assertEqual(leaf.depends_on, (spec_sha256,))

    def test_current_im05_focused_build_projects_to_portable_leaf(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        direct = self.project(source_map, screening, manifests, transaction)
        targets = tuple(
            sorted(
                route["proof_endpoint_leaf_sha256"]
                for route in direct.navigation.values()
            )
        )
        build = project_focused_build_leaf_from_validated_inputs(
            focused_build_receipt=json.loads(
                (IM05 / "audit" / "FOCUSED_BUILD_RECEIPT.json").read_text()
            ),
            lean_import_closure_receipt=json.loads(
                (IM05 / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").read_text()
            ),
            target_leaf_sha256s=targets,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(build.leaf.kind.value, "build")
        self.assertEqual(
            tuple(build.leaf.semantic_payload["target_declaration_sha256s"]),
            targets,
        )
        self.assertEqual(build.issuance.leaf_sha256, build.leaf.leaf_sha256)

    def test_authenticated_focused_build_must_bind_the_supplied_closure(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        direct = self.project(source_map, screening, manifests, transaction)
        targets = tuple(
            sorted(
                route["proof_endpoint_leaf_sha256"]
                for route in direct.navigation.values()
            )
        )
        closure_receipt = json.loads(
            (IM05 / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").read_text()
        )
        closure = closure_receipt["lean_import_closure"]
        focused = {
            "schema": 3,
            "paper": "IM05MarriageHonestyStability",
            "command": "lake build IM05MarriageHonestyStability",
            "target": "IM05MarriageHonestyStability",
            "result": "passed",
            "commit": "a" * 40,
            "lean_entrypoint": closure["entrypoint"],
            "lean_import_closure_sha256": closure_receipt[
                "lean_import_closure_sha256"
            ],
        }
        project_focused_build_leaf_from_validated_inputs(
            focused_build_receipt=focused,
            lean_import_closure_receipt=closure_receipt,
            target_leaf_sha256s=targets,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        changed = copy.deepcopy(focused)
        changed["lean_import_closure_sha256"] = "f" * 64
        with self.assertRaisesRegex(
            ObligationEvidenceProjectionError,
            "focused build receipt and Lean import closure disagree",
        ):
            project_focused_build_leaf_from_validated_inputs(
                focused_build_receipt=changed,
                lean_import_closure_receipt=closure_receipt,
                target_leaf_sha256s=targets,
                issuance_authority_sha256=transaction,
                issuance_assurance_contract_sha256=(
                    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
                ),
            )

    def test_explicit_lake_module_target_is_the_same_portable_build_leaf(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        direct = self.project(source_map, screening, manifests, transaction)
        targets = tuple(
            sorted(
                route["proof_endpoint_leaf_sha256"]
                for route in direct.navigation.values()
            )
        )
        receipt = json.loads(
            (IM05 / "audit" / "FOCUSED_BUILD_RECEIPT.json").read_text()
        )
        baseline = project_focused_build_leaf_from_validated_inputs(
            focused_build_receipt=receipt,
            lean_import_closure_receipt=json.loads(
                (IM05 / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").read_text()
            ),
            target_leaf_sha256s=targets,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        explicit_module = copy.deepcopy(receipt)
        explicit_module["command"] = "lake build +" + explicit_module["target"]
        projected = project_focused_build_leaf_from_validated_inputs(
            focused_build_receipt=explicit_module,
            lean_import_closure_receipt=json.loads(
                (IM05 / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json").read_text()
            ),
            target_leaf_sha256s=targets,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(projected.leaf, baseline.leaf)

    def test_prompt_reason_validator_and_recloseout_change_only_issuance(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        baseline = self.project(source_map, screening, manifests, transaction)
        changed = copy.deepcopy(screening)
        changed["prompt_version"] = "same-obligation-new-prompt-wording"
        changed["validator"] = "different accepted reviewer label"
        for row in changed["items"].values():
            row["reason"] = "A different human-facing explanation of the same match."
        projected = self.project(source_map, changed, manifests, "f" * 64)
        self.assertEqual(projected.graph.graph_sha256, baseline.graph.graph_sha256)
        self.assertEqual(set(projected.graph.leaves), set(baseline.graph.leaves))
        self.assertNotEqual(
            {item.issuance_sha256 for item in projected.issuances},
            {item.issuance_sha256 for item in baseline.issuances},
        )

    def test_native_strict_authority_uses_its_distinct_assurance_contract(self) -> None:
        source_map, screening, manifests, _transaction = load_inputs()
        projection = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=screening,
            route_set=structural_obligation_preflight(
                source_map, paper="IM05MarriageHonestyStability"
            ).require_current().route_set,
            issuance_authority_sha256="e" * 64,
            issuance_assurance_contract_sha256=(
                STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(projection.issuance_authority_sha256, "e" * 64)
        self.assertEqual(
            {
                issuance.assurance_contract_sha256
                for issuance in projection.issuances
            },
            {STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256},
        )

    def test_navigation_paths_lines_keys_and_declaration_names_do_not_change_graph(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        baseline = self.project(source_map, screening, manifests, transaction)
        moved_map = copy.deepcopy(source_map)
        moved_screening = copy.deepcopy(screening)
        moved_manifests = copy.deepcopy(manifests)

        old_item_key = next(
            key
            for key, item in moved_map["items"].items()
            if isinstance(item, dict) and item.get("semantic_contract")
        )
        item = moved_map["items"].pop(old_item_key)
        moved_map["items"]["renamed_navigation_key"] = item
        item["source_location"] = "moved/source.tex:900-901"
        item["source_status"] = "rewritten human-facing status prose"
        item["source_note"] = "rewritten navigation note"
        for anchor in item.get("source_anchor_evidence", []):
            anchor["path"] = "moved/source.tex"
            anchor["line_start"] = 900
            anchor["line_end"] = 901
        for atom in item.get("source_claim_atoms", []):
            atom["source_locator"] = "moved/source.tex:900-901"
            atom["id"] = "renamed.navigation.label"
            atom["reviewed_lean_route"] = "Renamed.Navigation.proofRoute"
            atom["semantic_claim"] = (
                "A rewritten explanatory paraphrase of the same exact source quote."
            )

        correspondence = item["source_spec_correspondence"]
        correspondence["source_atoms_sha256"] = source_claim_atoms_semantic_sha256(
            item["source_claim_atoms"]
        )
        for binding, atom in zip(
            correspondence["source_atom_bindings"], item["source_claim_atoms"]
        ):
            binding["source_atom_sha256"] = source_claim_atom_semantic_sha256(atom)

        contract = item["semantic_contract"]
        old_spec = contract["spec_declaration"]
        old_endpoint = contract["evidence_declaration"]
        new_spec = "Renamed.Navigation.claimSpec"
        new_endpoint = "Renamed.Navigation.claimProof"
        contract["spec_declaration"] = new_spec
        contract["evidence_declaration"] = new_endpoint
        for atom in item.get("source_claim_atoms", []):
            atom["reviewed_lean_route"] = new_endpoint
        correspondence["source_atoms_sha256"] = source_claim_atoms_semantic_sha256(
            item["source_claim_atoms"]
        )
        for binding, atom in zip(
            correspondence["source_atom_bindings"], item["source_claim_atoms"]
        ):
            binding["source_atom_sha256"] = source_claim_atom_semantic_sha256(atom)
        correspondence["item_identity_sha256"] = (
            source_spec_correspondence_item_identity_sha256(
                contract, correspondence
            )
        )
        row = moved_screening["items"].pop(old_spec)
        row["semantic_target_declaration"] = new_spec
        moved_screening["items"][new_spec] = row
        for entry in moved_manifests["entries"]:
            if entry["qualified_declaration"] == old_spec:
                entry["qualified_declaration"] = new_spec
            elif entry["qualified_declaration"] == old_endpoint:
                entry["qualified_declaration"] = new_endpoint

        moved = self.project(
            moved_map, moved_screening, moved_manifests, transaction
        )
        self.assertEqual(moved.graph.graph_sha256, baseline.graph.graph_sha256)
        self.assertEqual(set(moved.graph.leaves), set(baseline.graph.leaves))
        self.assertNotEqual(moved.navigation, baseline.navigation)

    def test_undivided_quote_cannot_fake_two_atoms_with_paraphrase_labels(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        changed = copy.deepcopy(source_map)
        item = next(
            value
            for value in changed["items"].values()
            if isinstance(value, dict) and value.get("semantic_contract")
        )
        duplicate = copy.deepcopy(item["source_claim_atoms"][0])
        duplicate["id"] = "different.paraphrase.label"
        duplicate["semantic_claim"] = "A purported second component."
        item["source_claim_atoms"].append(duplicate)
        with self.assertRaisesRegex(ValueError, "duplicate exact source components"):
            self.project(changed, screening, manifests, transaction)

    def test_exact_clause_atoms_project_as_distinct_leaves_from_one_quote(self) -> None:
        require_historical_fixture(SESHADRI)
        audit = SESHADRI / "audit"
        source_map = json.loads(
            (audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        preflight = structural_obligation_preflight(
            source_map,
            paper=SESHADRI.name,
            paper_prerequisites=json.loads(
                (audit / "paper_semantic_prerequisites.json").read_text(
                    encoding="utf-8"
                )
            ),
            library_semantic_review=json.loads(
                (audit / "library_semantic_review.json").read_text(
                    encoding="utf-8"
                )
            ),
            require_theorem_endpoints=True,
        ).require_current()
        projection = project_source_route_leaves_from_validated_inputs(
            source_map=source_map,
            preflight=preflight,
            issuance_authority_sha256="a" * 64,
            issuance_assurance_contract_sha256="b" * 64,
        )
        leaves = [
            projection.graph.leaves[digest]
            for digest in projection.navigation["lemma2_separation"]
        ]
        self.assertEqual(len(leaves), 2)
        self.assertEqual(
            len(
                {
                    leaf.semantic_payload["source_component_sha256"]
                    for leaf in leaves
                }
            ),
            2,
        )
        self.assertEqual(
            len(
                {
                    leaf.semantic_payload["source_quote_sha256"]
                    for leaf in leaves
                }
            ),
            1,
        )

    def test_uncertain_review_never_projects_as_accepted_leaf(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        changed = copy.deepcopy(screening)
        first = next(iter(changed["items"].values()))
        first["judgment"] = "uncertain"
        with self.assertRaisesRegex(
            ObligationEvidenceProjectionError, "not an accepted match"
        ):
            self.project(source_map, changed, manifests, transaction)

    def test_changed_verbatim_bundle_changes_only_affected_judgment_branch(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        baseline = self.project(source_map, screening, manifests, transaction)
        changed_screening = copy.deepcopy(screening)
        first_key = next(iter(changed_screening["items"]))
        changed_screening["items"][first_key]["source_input_bundle_sha256"] = "f" * 64
        changed = self.project(
            source_map, changed_screening, manifests, transaction
        )

        baseline_nav = next(
            value
            for value in baseline.navigation.values()
            if value["semantic_review_declaration"] == first_key
        )
        changed_nav = next(
            value
            for value in changed.navigation.values()
            if value["semantic_review_declaration"] == first_key
        )
        self.assertEqual(
            baseline_nav["source_atom_leaf_sha256s"],
            changed_nav["source_atom_leaf_sha256s"],
        )
        self.assertEqual(
            baseline_nav["semantic_review_leaf_sha256"],
            changed_nav["semantic_review_leaf_sha256"],
        )
        self.assertNotEqual(
            baseline_nav["judgment_leaf_sha256"],
            changed_nav["judgment_leaf_sha256"],
        )
        self.assertEqual(
            baseline_nav["realization_leaf_sha256"],
            changed_nav["realization_leaf_sha256"],
        )

    def test_current_lean_targets_use_the_shared_v11_claim_validator(self) -> None:
        source_map, screening, _manifests, _transaction = load_inputs()
        _source_artifact, claims = validated_direct_v11_claims(
            source_map=source_map,
            v11_screening=screening,
            route_set=structural_obligation_preflight(
                source_map, paper="IM05MarriageHonestyStability"
            ).require_current().route_set,
        )
        targets = {
            name: {"display_sha256": row["lean_expanded_statement_sha256"]}
            for name, row in screening["items"].items()
        }
        validate_current_direct_v11_semantic_targets(
            claims=claims,
            current_semantic_targets=targets,
        )
        targets[claims[0].review_name]["display_sha256"] = "f" * 64
        with self.assertRaisesRegex(
            ObligationEvidenceProjectionError,
            "current Lean semantic target changed",
        ):
            validate_current_direct_v11_semantic_targets(
                claims=claims,
                current_semantic_targets=targets,
            )

    def test_current_direct_projection_binds_review_to_lean_semantic_identity(self) -> None:
        source_map, screening, _manifests, transaction = load_inputs()
        preflight = structural_obligation_preflight(
            source_map, paper="IM05MarriageHonestyStability"
        ).require_current()
        assert preflight.route_set is not None
        signatures = {name: "d" * 64 for name in screening["items"]}
        projection = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=screening,
            route_set=preflight.route_set,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
            ),
            current_semantic_signature_sha256s=signatures,
        )
        for route in projection.navigation.values():
            leaf = projection.graph.leaves[
                route["semantic_review_leaf_sha256"]
            ]
            self.assertEqual(
                leaf.contract_sha256,
                LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
            )
            self.assertEqual(
                leaf.semantic_payload["elaborated_signature_sha256"],
                signatures[route["semantic_review_declaration"]],
            )

    def test_syntax_provenance_is_not_a_direct_semantic_leaf_input(self) -> None:
        source_map, screening, _manifests, transaction = load_inputs()
        baseline = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=screening,
            route_set=structural_obligation_preflight(
                source_map, paper="IM05MarriageHonestyStability"
            ).require_current().route_set,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        changed_screening = copy.deepcopy(screening)
        for row in changed_screening["items"].values():
            row["declaration_syntax_provenance_sha256"] = "f" * 64
        changed = project_direct_v11_leaves_from_validated_inputs(
            source_map=source_map,
            v11_screening=changed_screening,
            route_set=structural_obligation_preflight(
                source_map, paper="IM05MarriageHonestyStability"
            ).require_current().route_set,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(changed.graph.graph_sha256, baseline.graph.graph_sha256)
        self.assertNotEqual(
            {item.issuance_sha256 for item in changed.issuances},
            {item.issuance_sha256 for item in baseline.issuances},
        )

    def test_changed_whole_source_carrier_preserves_semantic_leaf_graph(self) -> None:
        source_map, screening, manifests, transaction = load_inputs()
        baseline = self.project(source_map, screening, manifests, transaction)
        changed_map = copy.deepcopy(source_map)
        changed_map["source_artifact_sha256"] = "f" * 64
        changed = self.project(changed_map, screening, manifests, transaction)

        self.assertEqual(baseline.graph.graph_sha256, changed.graph.graph_sha256)
        self.assertEqual(baseline.navigation, changed.navigation)

    def test_paper_and_library_prerequisites_project_through_one_schema(self) -> None:
        inputs = load_prerequisite_inputs()
        with mock.patch("subprocess.run", side_effect=AssertionError("producer invoked")):
            projection = project_semantic_prerequisite_leaves_from_validated_inputs(
                source_map=inputs[0],
                paper_prerequisites=inputs[1],
                library_semantic_review=inputs[2],
                manifest_authority=inputs[3],
                issuance_authority_sha256=inputs[4],
                issuance_assurance_contract_sha256=(
                    LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
                ),
            )
        self.assertIn(
            "IM05MarriageHonestyStability.PaperInterface.Algorithm41SourceModel",
            projection.navigation,
        )
        # This fixture is an accepted pre-rename record. Navigation retains the
        # declaration name under which that historical evidence was issued.
        self.assertIn("EconCSLib.Matching.Assignment", projection.navigation)
        for route in projection.navigation.values():
            lean_leaf = projection.graph.leaves[
                route["lean_declaration_leaf_sha256"]
            ]
            self.assertEqual(
                lean_leaf.semantic_payload["semantic_target_kind"],
                "semantic_prerequisite",
            )
        self.assertEqual(projection.unresolved_declarations, ())
        self.assertEqual(
            {issuance.leaf_sha256 for issuance in projection.issuances},
            set(projection.graph.leaves),
        )

    def test_current_prerequisite_projection_ignores_stale_manifest_store(self) -> None:
        source_map, paper, library, manifests, transaction = load_prerequisite_inputs()
        signatures = {
            *paper["items"],
            *library["items"],
        }
        signature_map = {name: "d" * 64 for name in signatures}
        projection = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=source_map,
            paper_prerequisites=paper,
            library_semantic_review=library,
            manifest_authority=manifests,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
            ),
            current_semantic_signature_sha256s=signature_map,
        )
        for declaration, route in projection.navigation.items():
            leaf = projection.graph.leaves[
                route["lean_declaration_leaf_sha256"]
            ]
            self.assertEqual(
                leaf.contract_sha256,
                LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
            )
            self.assertEqual(
                leaf.semantic_payload["elaborated_signature_sha256"],
                signature_map[declaration],
            )

    def test_current_prerequisite_projection_accepts_only_current_approved_correction(
        self,
    ) -> None:
        source_map, paper, library, manifests, transaction = load_prerequisite_inputs()
        source_map = copy.deepcopy(source_map)
        paper = copy.deepcopy(paper)
        declaration, row = next(iter(paper["items"].items()))
        source_item = source_map["items"][row["source_item"]]
        corrected_target = {
            "schema": 1,
            "statement": "The explicitly approved corrected prerequisite.",
            "governing_defect_ids": ["FIXTURE-1"],
            "archival_equivalence_claimed": False,
            "archival_source_quote_sha256": "a" * 64,
            "approval": {
                "kind": "explicit_user_instruction",
                "target_statement_sha256": "b" * 64,
                "artifact_sha256": "c" * 64,
            },
        }
        corrected_target["corrected_target_review_sha256"] = (
            corrected_target_review_digest(corrected_target)
        )
        source_item["corrected_target"] = corrected_target
        row["judgment"] = "matches_approved_corrected_target"
        row["corrected_target_protocol"] = CORRECTED_TARGET_REVIEW_PROTOCOL
        row["corrected_target_review_sha256"] = corrected_target[
            "corrected_target_review_sha256"
        ]
        projection = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=source_map,
            paper_prerequisites=paper,
            library_semantic_review=library,
            manifest_authority=manifests,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertIn(declaration, projection.navigation)

        row["corrected_target_review_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            ObligationEvidenceProjectionError, "no exact approved correction"
        ):
            project_semantic_prerequisite_leaves_from_validated_inputs(
                source_map=source_map,
                paper_prerequisites=paper,
                library_semantic_review=library,
                manifest_authority=manifests,
                issuance_authority_sha256=transaction,
                issuance_assurance_contract_sha256=(
                    STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
                ),
            )

    def test_current_gkgmm_projects_all_reviewed_prerequisites_without_replay(
        self,
    ) -> None:
        require_historical_fixture(GKGMM)
        audit = GKGMM / "audit"
        source_map = json.loads((audit / "paper_statement_map.json").read_text())
        paper_prerequisites = json.loads(
            (audit / "paper_semantic_prerequisites.json").read_text()
        )
        library_prerequisites = json.loads(
            (audit / "library_semantic_review.json").read_text()
        )
        manifest_authority = json.loads(
            (audit / "lean_signature_manifest_cache_authority.json").read_text()
        )
        with mock.patch("subprocess.run", side_effect=AssertionError("producer invoked")):
            projection = project_semantic_prerequisite_leaves_from_validated_inputs(
                source_map=source_map,
                paper_prerequisites=paper_prerequisites,
                library_semantic_review=library_prerequisites,
                manifest_authority=manifest_authority,
                issuance_authority_sha256="f" * 64,
                issuance_assurance_contract_sha256=(
                    STRICT_CLOSEOUT_TRANSACTION_ASSURANCE_SHA256
                ),
            )
        expected_declarations = set(paper_prerequisites["items"]) | set(
            library_prerequisites["items"]
        )
        self.assertEqual(set(projection.navigation), expected_declarations)
        self.assertEqual(projection.unresolved_declarations, ())
        reviewed_contract_count = sum(
            projection.graph.leaves[
                route["lean_declaration_leaf_sha256"]
            ].contract_sha256
            == LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT_SHA256
            for route in projection.navigation.values()
        )
        self.assertGreater(reviewed_contract_count, 0)

    def test_prerequisite_navigation_edits_leave_projected_graph_unchanged(self) -> None:
        source_map, paper, library, manifests, transaction = load_prerequisite_inputs()
        baseline = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=source_map,
            paper_prerequisites=paper,
            library_semantic_review=library,
            manifest_authority=manifests,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        moved_map = copy.deepcopy(source_map)
        moved_paper = copy.deepcopy(paper)
        moved_library = copy.deepcopy(library)
        for item in moved_map["items"].values():
            item["source_location"] = "moved/source.tex:700-701"
            for anchor in item.get("source_anchor_evidence", []):
                anchor["path"] = "moved/source.tex"
                anchor["line_start"] = 700
                anchor["line_end"] = 701
            for atom in item.get("source_claim_atoms", []):
                atom["source_locator"] = "moved/source.tex:700-701"
        for row in moved_paper["items"].values():
            row["paper_source_path"] = "Moved/Paper.lean"
            row["paper_line_start"] = 700
        for row in moved_library["items"].values():
            row["library_source_path"] = "Moved/Library.lean"
            row["library_line_start"] = 700
            row["library_line_end"] = 701
        moved = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=moved_map,
            paper_prerequisites=moved_paper,
            library_semantic_review=moved_library,
            manifest_authority=manifests,
            issuance_authority_sha256=transaction,
            issuance_assurance_contract_sha256=(
                LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256
            ),
        )
        self.assertEqual(moved.graph.graph_sha256, baseline.graph.graph_sha256)
        self.assertEqual(
            moved.unresolved_declarations, baseline.unresolved_declarations
        )


if __name__ == "__main__":
    unittest.main()
