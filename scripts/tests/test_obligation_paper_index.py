from __future__ import annotations

import copy
import hashlib
import unittest
from dataclasses import replace
from types import SimpleNamespace
from unittest import mock

from scripts import obligation_paper_index as paper_index_module
from scripts.obligation_evidence_contracts import (
    ALL_OBLIGATION_CONTRACTS,
    LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    LEAN_PROOF_ENDPOINT_CONTRACT,
    LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT,
    LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT,
)
from scripts.obligation_evidence_graph import (
    build_evidence_leaf,
    build_obligation_graph,
    lean_declaration_leaf,
    lean_proof_endpoint_leaf,
    lean_reviewed_semantic_target_leaf,
    legacy_artifact_bound_source_atom_leaf,
    proof_realization_leaf,
    source_atom_leaf,
    source_lean_judgment_leaf,
)
from scripts.obligation_evidence_issuance import issue_obligation_evidence_attestation
from scripts.obligation_evidence_planner import (
    ObligationEvidencePlanningError,
    plan_complete_paper_obligation_evidence,
    verify_complete_paper_obligation_evidence,
)
from scripts.obligation_paper_index import (
    PaperObligationIndexError,
    assemble_complete_paper_obligation_graph,
    build_paper_obligation_index,
    build_paper_obligation_index_from_preflight,
    current_reviewed_source_item_ids,
    prerequisite_source_judgments_by_source_item,
    validate_paper_obligation_index,
)
from scripts.obligation_preflight import structural_obligation_preflight


def sha(character: str) -> str:
    return character * 64


FIXTURE_QUOTE = "One exact source claim."
FIXTURE_QUOTE_SHA256 = hashlib.sha256(FIXTURE_QUOTE.encode()).hexdigest()


class PaperObligationIndexTests(unittest.TestCase):
    def test_legacy_schema_one_index_remains_directly_readable(self) -> None:
        graph = self.complete_graph()
        preflight = self.preflight()
        bindings = self.route_bindings(graph)
        legacy = paper_index_module._construct_paper_obligation_index(
            graph,
            schema=paper_index_module.LEGACY_PAPER_OBLIGATION_INDEX_SCHEMA,
            source_inventory_sha256=preflight.source_inventory_sha256,
            route_schema_sha256=preflight.route_schema_sha256,
            structural_preflight_sha256=preflight.structural_preflight_sha256,
            complete_paper_surface=True,
            route_leaf_sha256s_by_source_item=bindings,
            prerequisite_leaf_sha256s_by_declaration={},
            expected_route_obligation_counts=preflight.route_obligation_counts,
            expected_route_source_quotes=preflight.route_source_quote_sha256s,
            expected_source_artifact_sha256=preflight.source_artifact_sha256,
            expected_prerequisite_source_item_by_declaration=None,
        )
        self.assertEqual(legacy.schema, 1)
        self.assertNotIn("identity_scope", legacy.projection())
        self.assertEqual(
            validate_paper_obligation_index(
                legacy.projection(),
                graph=graph,
                require_complete=True,
                preflight=preflight,
            ),
            legacy,
        )

    def test_navigation_renames_preserve_semantic_index_and_current_validation(
        self,
    ) -> None:
        graph = self.complete_graph_with_prerequisite()
        original = self.preflight(include_prerequisite=True)
        index = build_paper_obligation_index_from_preflight(
            graph,
            original,
            complete_paper_surface=True,
            route_leaf_sha256s_by_source_item=self.route_bindings(graph),
            prerequisite_leaf_sha256s_by_declaration=(
                self.prerequisite_bindings(graph)
            ),
        )
        renamed = replace(
            original,
            source_inventory_sha256=sha("a"),
            route_schema_sha256=sha("b"),
            structural_preflight_sha256=sha("c"),
            route_obligation_counts={
                "renamed-source-item": dict(
                    original.route_obligation_counts["claim"]
                )
            },
            route_source_quote_sha256s={
                "renamed-source-item": original.route_source_quote_sha256s["claim"]
            },
            prerequisite_source_item_by_declaration={
                "Renamed.Model": "renamed-source-item"
            },
        )
        renamed_index = build_paper_obligation_index_from_preflight(
            graph,
            renamed,
            complete_paper_surface=True,
            route_leaf_sha256s_by_source_item={
                "renamed-source-item": self.route_bindings(graph)["claim"]
            },
            prerequisite_leaf_sha256s_by_declaration={
                "Renamed.Model": self.prerequisite_bindings(graph)["Fixture.Model"]
            },
        )
        self.assertEqual(index.index_sha256, renamed_index.index_sha256)

        def select(selected_index, selected_graph, selected_preflight):
            current_items = {
                key: {"statement": key}
                for key in selected_preflight.route_obligation_counts
            }
            atoms = tuple(graph.leaves[digest] for digest in
                          index.route_leaf_sha256s_by_source_item["claim"]["source_atom"])
            with mock.patch(
                "scripts.obligation_evidence_projection._source_atom_leaves",
                return_value=atoms,
            ):
                return current_reviewed_source_item_ids(
                    selected_index, selected_graph, selected_preflight,
                    source_map={"items": current_items},
                )

        self.assertEqual(
            select(index, graph, original),
            {"claim"},
        )
        self.assertEqual(
            select(index, graph, renamed),
            {"renamed-source-item"},
        )
        # The terminal assurance reader now receives current keys, while the
        # source-fact values and accepted graph remain unchanged by a rename.
        source_facts = {"claim": {"source_input_bundle_sha256": sha("d")}}
        renamed_facts = {"renamed-source-item": source_facts["claim"]}
        self.assertEqual(
            [source_facts[key] for key in select(index, graph, original)],
            [renamed_facts[key] for key in select(index, graph, renamed)],
        )
        duplicate_index = replace(index, route_leaf_sha256s_by_source_item={
            "first": index.route_leaf_sha256s_by_source_item["claim"],
            "second": index.route_leaf_sha256s_by_source_item["claim"],
        })
        duplicate_preflight = replace(
            renamed,
            route_obligation_counts={
                key: original.route_obligation_counts["claim"]
                for key in ("current-first", "current-second")
            },
            route_source_quote_sha256s={
                key: original.route_source_quote_sha256s["claim"]
                for key in ("current-first", "current-second")
            },
        )
        self.assertEqual(
            select(duplicate_index, graph, duplicate_preflight),
            {"current-first", "current-second"},
        )
        with self.assertRaisesRegex(PaperObligationIndexError, "disagree"):
            select(duplicate_index, graph, renamed)
        for changed in (
            replace(renamed, route_source_quote_sha256s={"renamed-source-item": (sha("f"),)}),
            replace(renamed, route_obligation_counts={"renamed-source-item": {"source_atom": 99}}),
        ):
            with self.subTest(changed=changed), self.assertRaisesRegex(
                PaperObligationIndexError, "disagree with the current source surface",
            ):
                select(index, graph, changed)
        with mock.patch(
            "scripts.obligation_evidence_projection._source_atom_leaves",
            return_value=(mock.Mock(leaf_sha256=sha("f")),),
        ), self.assertRaisesRegex(PaperObligationIndexError, "source atoms disagree"):
            current_reviewed_source_item_ids(
                index, graph, renamed,
                source_map={"items": {"renamed-source-item": {}}},
            )
        self.assertEqual(
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=renamed,
                require_current_aggregate_identity=False,
            ),
            index,
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError,
            "disagree",
        ):
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=renamed,
                require_current_aggregate_identity=True,
            )

    def complete_graph(self):
        source = source_atom_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["source_atom"].contract_sha256,
            source_artifact_sha256=sha("1"),
            source_quote_sha256=FIXTURE_QUOTE_SHA256,
            source_component_sha256=sha("3"),
            source_role_contract_sha256=sha("4"),
        )
        spec = lean_declaration_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["lean_declaration"].contract_sha256,
            semantic_target_kind="spec_proposition",
            elaborated_signature_sha256=sha("5"),
            elaborated_proposition_graph_sha256=sha("6"),
            semantic_dependency_sha256=sha("7"),
        )
        endpoint = lean_declaration_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["lean_declaration"].contract_sha256,
            semantic_target_kind="proof_endpoint",
            elaborated_signature_sha256=sha("8"),
            elaborated_proposition_graph_sha256=sha("9"),
            semantic_dependency_sha256=sha("a"),
        )
        judgment = source_lean_judgment_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["source_lean_judgment"].contract_sha256,
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=spec.leaf_sha256,
            verbatim_source_bundle_sha256=sha("b"),
            verdict="matches",
        )
        realization = proof_realization_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["proof_realization"].contract_sha256,
            spec_declaration_sha256=spec.leaf_sha256,
            proof_endpoint_sha256=endpoint.leaf_sha256,
            relation="proves",
            lean_relation_sha256=sha("c"),
        )
        build = build_evidence_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["build"].contract_sha256,
            target_declaration_sha256s=[endpoint.leaf_sha256],
            build_command_sha256=sha("d"),
            toolchain_sha256=sha("e"),
            lean_import_closure_sha256=sha("f"),
        )
        return build_obligation_graph(
            [source, spec, endpoint, judgment, realization, build],
            root_leaf_sha256s=[
                judgment.leaf_sha256,
                realization.leaf_sha256,
                build.leaf_sha256,
            ],
        )

    def complete_graph_with_prerequisite(self):
        graph = self.complete_graph()
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        model = lean_declaration_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS["lean_declaration"].contract_sha256,
            semantic_target_kind="semantic_prerequisite",
            elaborated_signature_sha256=sha("2"),
            elaborated_proposition_graph_sha256=sha("3"),
            semantic_dependency_sha256=sha("4"),
        )
        judgment = source_lean_judgment_leaf(
            contract_sha256=ALL_OBLIGATION_CONTRACTS[
                "source_lean_judgment"
            ].contract_sha256,
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=model.leaf_sha256,
            verbatim_source_bundle_sha256=sha("b"),
            verdict="matches",
        )
        return build_obligation_graph(
            [*graph.leaves.values(), model, judgment],
            root_leaf_sha256s=[*graph.root_leaf_sha256s, judgment.leaf_sha256],
        )

    def preflight(self, *, include_scope_route=False, include_prerequisite=False):
        quote = FIXTURE_QUOTE
        quote_sha256 = FIXTURE_QUOTE_SHA256
        source_map = {
            "schema": 1,
            "paper": "Fixture",
            "source_artifact_sha256": sha("1"),
            "semantic_contract_schema": 1,
            "items": {
                "claim": {
                    "source_anchor_evidence": [
                        {
                            "quoted_text": quote,
                            "quoted_text_sha256": quote_sha256,
                        }
                    ],
                    "source_claim_atoms": [
                        {
                            "id": "claim.atom",
                            "reviewed_lean_route": "Fixture.claimProof",
                            "semantic_claim": "The exact source claim.",
                            "source_locator": "source:1",
                            "source_quote_sha256": quote_sha256,
                        }
                    ],
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claimProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                    "source_spec_correspondence": {
                        "schema": 1,
                        "source_atoms_sha256": sha("2"),
                        "spec_closure_sha256": sha("3"),
                        "spec_surface_sha256": sha("4"),
                        "closure_environment_sha256": sha("5"),
                        "item_identity_sha256": sha("6"),
                        "source_atom_bindings": [{}],
                        "closure_node_dispositions": [],
                    },
                }
            },
        }
        if include_scope_route:
            scope_quote = "One separately dispositioned source item."
            scope_quote_sha256 = hashlib.sha256(scope_quote.encode()).hexdigest()
            source_map["items"]["scope_item"] = {
                "claim_bearing": False,
                "inventory_role": "deep_audit_material",
                "scope_disposition": "reviewed_outside_formalized_claim_surface",
                "source_anchor_evidence": [
                    {
                        "quoted_text": scope_quote,
                        "quoted_text_sha256": scope_quote_sha256,
                    }
                ],
            }
        paper_prerequisites = None
        library_review = None
        if include_prerequisite:
            paper_prerequisites = {
                "schema": 1,
                "items": {
                    "Fixture.Model": {
                        "judgment": "matches",
                        "paper_declaration": "Fixture.Model",
                        "paper_declaration_sha256": sha("7"),
                        "paper_semantic_target_protocol": "lean display",
                        "paper_semantic_target_sha256": sha("8"),
                        "source_input_bundle_sha256": sha("9"),
                        "source_item": "claim",
                    }
                },
            }
            library_review = {"schema": 1, "items": {}}
        preflight = structural_obligation_preflight(
            source_map,
            paper="Fixture",
            paper_prerequisites=paper_prerequisites,
            library_semantic_review=library_review,
        )
        self.assertTrue(preflight.current, preflight.errors)
        return preflight

    def test_complete_index_rejects_omitted_semantic_prerequisite_surface(self) -> None:
        graph = self.complete_graph()
        preflight = self.preflight(include_prerequisite=True)
        self.assertEqual(preflight.counts["semantic_prerequisite"], 1)
        with self.assertRaisesRegex(
            PaperObligationIndexError,
            "semantic-prerequisite bindings disagree with preflight",
        ):
            build_paper_obligation_index_from_preflight(
                graph,
                preflight,
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(graph),
            )

    def route_bindings(self, graph):
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
            and graph.leaves[
                leaf.semantic_payload["lean_declaration_sha256"]
            ].semantic_payload.get("semantic_target_kind")
            == "spec_proposition"
        )
        realization = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "proof_realization"
        )
        spec = graph.leaves[judgment.semantic_payload["lean_declaration_sha256"]]
        endpoint = next(
            graph.leaves[digest]
            for digest in realization.depends_on
            if digest != spec.leaf_sha256
        )
        return {
            "claim": {
                "source_atom": (source.leaf_sha256,),
                "semantic_review": (spec.leaf_sha256,),
                "spec": (spec.leaf_sha256,),
                "proof_endpoint": (endpoint.leaf_sha256,),
                "source_lean_judgment": (judgment.leaf_sha256,),
                "proof_realization": (realization.leaf_sha256,),
            }
        }

    def prerequisite_bindings(self, graph):
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
            and graph.leaves[
                leaf.semantic_payload["lean_declaration_sha256"]
            ].semantic_payload.get("semantic_target_kind")
            == "semantic_prerequisite"
        )
        return {
            "Fixture.Model": {
                "source_atom": tuple(
                    digest
                    for digest in judgment.depends_on
                    if graph.leaves[digest].kind.value == "source_atom"
                ),
                "lean_declaration": (
                    judgment.semantic_payload["lean_declaration_sha256"],
                ),
                "source_lean_judgment": (judgment.leaf_sha256,),
            }
        }

    def test_complete_prerequisites_survive_without_issuance_ledger(self) -> None:
        graph = self.complete_graph_with_prerequisite()
        issuance_preflight = self.preflight(include_prerequisite=True)
        index = build_paper_obligation_index_from_preflight(
            graph,
            issuance_preflight,
            complete_paper_surface=True,
            route_leaf_sha256s_by_source_item=self.route_bindings(graph),
            prerequisite_leaf_sha256s_by_declaration=(
                self.prerequisite_bindings(graph)
            ),
        )
        graph_preflight = self.preflight()

        self.assertEqual(
            issuance_preflight.structural_preflight_sha256,
            graph_preflight.structural_preflight_sha256,
        )
        self.assertEqual(
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=graph_preflight,
            ),
            index,
        )
        self.assertEqual(
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=graph_preflight,
                require_current_aggregate_identity=False,
            ),
            index,
        )
        grouped = prerequisite_source_judgments_by_source_item(
            index, graph_preflight
        )
        self.assertEqual(set(grouped), {"claim"})
        self.assertEqual(len(grouped["claim"]), 1)

    def test_authenticated_prerequisite_owners_disambiguate_shared_atoms(
        self,
    ) -> None:
        atom = sha("1")
        index = SimpleNamespace(
            route_leaf_sha256s_by_source_item={
                "first": {"source_atom": (atom,)},
                "second": {"source_atom": (atom,)},
            },
            prerequisite_leaf_sha256s_by_declaration={
                "Paper.First": {
                    "source_atom": (atom,),
                    "source_lean_judgment": ("first-judgment",),
                },
                "Paper.Second": {
                    "source_atom": (atom,),
                    "source_lean_judgment": ("second-judgment",),
                },
            },
        )
        preflight = SimpleNamespace(
            require_current=lambda: None,
            prerequisite_source_item_by_declaration={},
        )

        fallback = prerequisite_source_judgments_by_source_item(index, preflight)
        self.assertEqual(
            fallback,
            {
                "first": ("first-judgment", "second-judgment"),
                "second": ("first-judgment", "second-judgment"),
            },
        )
        selected = prerequisite_source_judgments_by_source_item(
            index,
            preflight,
            authenticated_source_items_by_declaration={
                "Paper.First": "first",
                "Paper.Second": "second",
            },
        )
        self.assertEqual(
            selected,
            {
                "first": ("first-judgment",),
                "second": ("second-judgment",),
            },
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError,
            "binds a different source route",
        ):
            prerequisite_source_judgments_by_source_item(
                index,
                preflight,
                authenticated_source_items_by_declaration={
                    "Paper.First": "missing"
                },
            )
        for malformed in ([], ""):
            with self.subTest(malformed=malformed), self.assertRaisesRegex(
                PaperObligationIndexError,
                "ownership is malformed",
            ):
                prerequisite_source_judgments_by_source_item(
                    index,
                    preflight,
                    authenticated_source_items_by_declaration=malformed,
                )

    def test_complete_assembly_joins_only_supplied_route_leaves(self) -> None:
        source_graph = self.complete_graph()
        preflight = self.preflight()
        route = self.route_bindings(source_graph)["claim"]
        build = next(
            leaf
            for leaf in source_graph.leaves.values()
            if leaf.kind.value == "build"
        )
        graph, index = assemble_complete_paper_obligation_graph(
            leaves=source_graph.leaves,
            preflight=preflight,
            source_atom_leaf_sha256s_by_source_item={
                "claim": route["source_atom"]
            },
            semantic_role_leaf_sha256s_by_source_item={
                "claim": {
                    role: digests
                    for role, digests in route.items()
                    if role != "source_atom"
                }
            },
            build_leaf_sha256=build.leaf_sha256,
        )
        self.assertEqual(graph.graph_sha256, source_graph.graph_sha256)
        self.assertTrue(index.complete_paper_surface)
        self.assertEqual(
            index.route_leaf_sha256s_by_source_item["claim"],
            route,
        )

    def complete_index(self, graph=None):
        graph = graph or self.complete_graph()
        preflight = self.preflight()
        return (
            build_paper_obligation_index_from_preflight(
                graph,
                preflight,
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(graph),
            ),
            preflight,
        )

    def test_complete_index_requires_every_family_and_exact_partition(self) -> None:
        graph = self.complete_graph()
        index, preflight = self.complete_index(graph)
        self.assertEqual(
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=preflight,
            ),
            index,
        )
        corrupt = copy.deepcopy(index.projection())
        corrupt["leaf_sha256s_by_kind"]["lean_declaration"].pop()
        with self.assertRaises(PaperObligationIndexError):
            validate_paper_obligation_index(
                corrupt,
                graph=graph,
                require_complete=True,
                preflight=preflight,
            )

    def test_complete_index_accepts_identity_bound_review_target(self) -> None:
        original = self.complete_graph()
        source = next(
            leaf
            for leaf in original.leaves.values()
            if leaf.kind.value == "source_atom"
        )
        old_judgment = next(
            leaf
            for leaf in original.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
        )
        old_realization = next(
            leaf
            for leaf in original.leaves.values()
            if leaf.kind.value == "proof_realization"
        )
        old_build = next(
            leaf for leaf in original.leaves.values() if leaf.kind.value == "build"
        )
        spec = lean_reviewed_semantic_target_leaf(
            contract_sha256=(
                LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256
            ),
            semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256=sha("4"),
            elaborated_signature_sha256=sha("5"),
        )
        endpoint = lean_proof_endpoint_leaf(
            contract_sha256=LEAN_PROOF_ENDPOINT_CONTRACT.contract_sha256,
            spec_declaration_sha256=spec.leaf_sha256,
            relation="proves",
        )
        judgment = source_lean_judgment_leaf(
            contract_sha256=old_judgment.contract_sha256,
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=spec.leaf_sha256,
            verbatim_source_bundle_sha256=old_judgment.semantic_payload[
                "verbatim_source_bundle_sha256"
            ],
            verdict="matches",
        )
        realization = proof_realization_leaf(
            contract_sha256=old_realization.contract_sha256,
            spec_declaration_sha256=spec.leaf_sha256,
            proof_endpoint_sha256=endpoint.leaf_sha256,
            relation="proves",
            lean_relation_sha256=old_realization.semantic_payload[
                "lean_relation_sha256"
            ],
        )
        build = build_evidence_leaf(
            contract_sha256=old_build.contract_sha256,
            target_declaration_sha256s=[endpoint.leaf_sha256],
            build_command_sha256=old_build.semantic_payload[
                "build_command_sha256"
            ],
            toolchain_sha256=old_build.semantic_payload["toolchain_sha256"],
            lean_import_closure_sha256=old_build.semantic_payload[
                "lean_import_closure_sha256"
            ],
        )
        graph = build_obligation_graph(
            [source, spec, endpoint, judgment, realization, build],
            root_leaf_sha256s=[
                judgment.leaf_sha256,
                realization.leaf_sha256,
                build.leaf_sha256,
            ],
        )

        index, preflight = self.complete_index(graph)

        self.assertEqual(
            validate_paper_obligation_index(
                index.projection(),
                graph=graph,
                require_complete=True,
                preflight=preflight,
            ),
            index,
        )

    def test_all_five_kinds_cannot_hide_an_omitted_preflight_route(self) -> None:
        graph = self.complete_graph()
        with self.assertRaisesRegex(
            PaperObligationIndexError, "missing: scope_item"
        ):
            build_paper_obligation_index_from_preflight(
                graph,
                self.preflight(include_scope_route=True),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(graph),
            )

    def test_route_count_cannot_hide_a_different_source_quote(self) -> None:
        graph = self.complete_graph()
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
        )
        wrong_source = source_atom_leaf(
            contract_sha256=source.contract_sha256,
            source_artifact_sha256=sha("1"),
            source_quote_sha256=sha("f"),
            source_component_sha256=source.semantic_payload[
                "source_component_sha256"
            ],
            source_role_contract_sha256=source.semantic_payload[
                "source_role_contract_sha256"
            ],
        )
        wrong_judgment = source_lean_judgment_leaf(
            contract_sha256=judgment.contract_sha256,
            source_atom_sha256s=[wrong_source.leaf_sha256],
            lean_declaration_sha256=judgment.semantic_payload[
                "lean_declaration_sha256"
            ],
            verbatim_source_bundle_sha256=judgment.semantic_payload[
                "verbatim_source_bundle_sha256"
            ],
            verdict="matches",
        )
        leaves = [
            leaf
            for leaf in graph.leaves.values()
            if leaf.leaf_sha256 not in {source.leaf_sha256, judgment.leaf_sha256}
        ] + [wrong_source, wrong_judgment]
        wrong_graph = build_obligation_graph(
            leaves,
            root_leaf_sha256s=[
                wrong_judgment.leaf_sha256
                if digest == judgment.leaf_sha256
                else digest
                for digest in graph.root_leaf_sha256s
            ],
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError, "different exact source quotes"
        ):
            build_paper_obligation_index_from_preflight(
                wrong_graph,
                self.preflight(),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(
                    wrong_graph
                ),
            )

    def test_partial_migration_graph_cannot_be_terminal(self) -> None:
        graph = self.complete_graph()
        partial_leaves = [
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value != "build"
        ]
        partial = build_obligation_graph(
            partial_leaves,
            root_leaf_sha256s=[
                digest
                for digest in graph.root_leaf_sha256s
                if graph.leaves[digest].kind.value != "build"
            ],
        )
        index = build_paper_obligation_index(
            partial,
            source_inventory_sha256=sha("1"),
            route_schema_sha256=sha("2"),
            structural_preflight_sha256=sha("3"),
            complete_paper_surface=False,
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError, "partial migration"
        ):
            validate_paper_obligation_index(
                index.projection(), graph=partial, require_complete=True
            )
        authority = sha("f")
        issuances = [
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("e"),
                authority_sha256=authority,
                evidence_record_sha256=sha("d"),
            )
            for leaf in partial.leaves.values()
        ]
        with self.assertRaisesRegex(
            ObligationEvidencePlanningError, "partial migration"
        ):
            plan_complete_paper_obligation_evidence(
                index,
                partial,
                {
                    digest: leaf.projection()
                    for digest, leaf in partial.leaves.items()
                },
                issuances,
                preflight=self.preflight(),
                authenticated_authority_sha256s=[authority],
            )
        with self.assertRaisesRegex(
            ObligationEvidencePlanningError, "partial migration"
        ):
            verify_complete_paper_obligation_evidence(
                index,
                partial,
                {
                    digest: leaf.projection()
                    for digest, leaf in partial.leaves.items()
                },
                issuances,
                preflight=self.preflight(),
                authenticated_authority_sha256s=[authority],
            )

    def test_incomplete_graph_cannot_claim_complete_surface(self) -> None:
        graph = self.complete_graph()
        no_build = [
            leaf for leaf in graph.leaves.values() if leaf.kind.value != "build"
        ]
        partial = build_obligation_graph(
            no_build,
            root_leaf_sha256s=[
                digest
                for digest in graph.root_leaf_sha256s
                if graph.leaves[digest].kind.value != "build"
            ],
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError, "omits obligation families"
        ):
            build_paper_obligation_index_from_preflight(
                partial,
                self.preflight(),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(partial),
            )

    def test_complete_index_rejects_ad_hoc_contract_hashes(self) -> None:
        graph = self.complete_graph()
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        forged_source = source_atom_leaf(
            contract_sha256=sha("f"),
            source_artifact_sha256=sha("1"),
            source_quote_sha256=source.semantic_payload["source_quote_sha256"],
            source_component_sha256=source.semantic_payload["source_component_sha256"],
            source_role_contract_sha256=source.semantic_payload[
                "source_role_contract_sha256"
            ],
        )
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
        )
        lean = graph.leaves[judgment.semantic_payload["lean_declaration_sha256"]]
        forged_judgment = source_lean_judgment_leaf(
            contract_sha256=judgment.contract_sha256,
            source_atom_sha256s=[forged_source.leaf_sha256],
            lean_declaration_sha256=lean.leaf_sha256,
            verbatim_source_bundle_sha256=judgment.semantic_payload[
                "verbatim_source_bundle_sha256"
            ],
            verdict="matches",
        )
        leaves = [
            leaf
            for leaf in graph.leaves.values()
            if leaf.leaf_sha256 not in {source.leaf_sha256, judgment.leaf_sha256}
        ] + [forged_source, forged_judgment]
        forged_graph = build_obligation_graph(
            leaves,
            root_leaf_sha256s=[
                forged_judgment.leaf_sha256
                if digest == judgment.leaf_sha256
                else digest
                for digest in graph.root_leaf_sha256s
            ],
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError, "unregistered source_atom"
        ):
            build_paper_obligation_index_from_preflight(
                forged_graph,
                self.preflight(),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(
                    forged_graph
                ),
            )

    def test_complete_index_rejects_registered_contract_with_wrong_payload(self) -> None:
        graph = self.complete_graph()
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
        )
        realization = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "proof_realization"
        )
        spec = graph.leaves[judgment.semantic_payload["lean_declaration_sha256"]]
        endpoint = graph.leaves[
            realization.semantic_payload["proof_endpoint_sha256"]
        ]
        forged_spec = lean_declaration_leaf(
            contract_sha256=LEAN_REVIEWED_SEMANTIC_TARGET_CONTRACT.contract_sha256,
            semantic_target_kind=spec.semantic_payload["semantic_target_kind"],
            elaborated_signature_sha256=spec.semantic_payload[
                "elaborated_signature_sha256"
            ],
            elaborated_proposition_graph_sha256=spec.semantic_payload[
                "elaborated_proposition_graph_sha256"
            ],
            semantic_dependency_sha256=spec.semantic_payload[
                "semantic_dependency_sha256"
            ],
        )
        forged_judgment = source_lean_judgment_leaf(
            contract_sha256=judgment.contract_sha256,
            source_atom_sha256s=judgment.semantic_payload[
                "source_atom_sha256s"
            ],
            lean_declaration_sha256=forged_spec.leaf_sha256,
            verbatim_source_bundle_sha256=judgment.semantic_payload[
                "verbatim_source_bundle_sha256"
            ],
            verdict="matches",
        )
        forged_realization = proof_realization_leaf(
            contract_sha256=realization.contract_sha256,
            spec_declaration_sha256=forged_spec.leaf_sha256,
            proof_endpoint_sha256=endpoint.leaf_sha256,
            relation=realization.semantic_payload["relation"],
            lean_relation_sha256=realization.semantic_payload[
                "lean_relation_sha256"
            ],
        )
        replaced = {spec.leaf_sha256, judgment.leaf_sha256, realization.leaf_sha256}
        leaves = [
            leaf for leaf in graph.leaves.values() if leaf.leaf_sha256 not in replaced
        ] + [forged_spec, forged_judgment, forged_realization]
        roots = [
            forged_judgment.leaf_sha256
            if digest == judgment.leaf_sha256
            else forged_realization.leaf_sha256
            if digest == realization.leaf_sha256
            else digest
            for digest in graph.root_leaf_sha256s
        ]
        forged_graph = build_obligation_graph(leaves, root_leaf_sha256s=roots)
        with self.assertRaisesRegex(
            PaperObligationIndexError,
            "Lean payload disagrees with its registered contract",
        ):
            build_paper_obligation_index_from_preflight(
                forged_graph,
                self.preflight(),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(
                    forged_graph
                ),
            )

    def test_current_atoms_bind_corpus_once_in_preflight_not_each_leaf(self) -> None:
        graph = self.complete_graph()
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        self.assertNotIn("source_artifact_sha256", source.semantic_payload)
        index, preflight = self.complete_index(graph)
        self.assertEqual(preflight.source_artifact_sha256, sha("1"))
        self.assertEqual(
            index.source_inventory_sha256, preflight.source_inventory_sha256
        )

        # Rebuild the same structural source surface with only a different
        # complete-corpus identity.  The semantic graph remains reusable, but
        # the paper index must change and therefore requires terminal
        # revalidation of the new corpus.
        changed_map = {
            "schema": 1,
            "paper": "Fixture",
            "source_artifact_sha256": sha("9"),
            "semantic_contract_schema": 1,
            "items": {
                "claim": {
                    "source_anchor_evidence": [
                        {
                            "quoted_text": FIXTURE_QUOTE,
                            "quoted_text_sha256": FIXTURE_QUOTE_SHA256,
                        }
                    ],
                    "source_claim_atoms": [
                        {
                            "id": "claim.atom",
                            "reviewed_lean_route": "Fixture.claimProof",
                            "semantic_claim": "The exact source claim.",
                            "source_locator": "source:1",
                            "source_quote_sha256": FIXTURE_QUOTE_SHA256,
                        }
                    ],
                    "semantic_contract": {
                        "spec_declaration": "Fixture.claimSpec",
                        "evidence_declaration": "Fixture.claimProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                    "source_spec_correspondence": {
                        "schema": 1,
                        "source_atoms_sha256": sha("2"),
                        "spec_closure_sha256": sha("3"),
                        "spec_surface_sha256": sha("4"),
                        "closure_environment_sha256": sha("5"),
                        "item_identity_sha256": sha("6"),
                        "source_atom_bindings": [{}],
                        "closure_node_dispositions": [],
                    },
                }
            },
        }
        changed_preflight = structural_obligation_preflight(
            changed_map, paper="Fixture"
        )
        self.assertTrue(changed_preflight.current, changed_preflight.errors)
        changed_index = build_paper_obligation_index_from_preflight(
            graph,
            changed_preflight,
            complete_paper_surface=True,
            route_leaf_sha256s_by_source_item=self.route_bindings(graph),
        )
        # The complete source corpus is bound by the terminal source-assurance
        # root.  The paper index owns only semantic leaf bindings, so a corpus
        # aggregate or navigation projection change does not churn this root.
        self.assertEqual(index.index_sha256, changed_index.index_sha256)
        self.assertNotEqual(
            index.source_inventory_sha256,
            changed_index.source_inventory_sha256,
        )
        self.assertEqual(graph.graph_sha256, self.complete_graph().graph_sha256)

    def test_historical_source_atom_still_requires_its_exact_corpus(self) -> None:
        graph = self.complete_graph()
        source = next(
            leaf for leaf in graph.leaves.values() if leaf.kind.value == "source_atom"
        )
        judgment = next(
            leaf
            for leaf in graph.leaves.values()
            if leaf.kind.value == "source_lean_judgment"
        )
        historical_source = legacy_artifact_bound_source_atom_leaf(
            contract_sha256=(
                LEGACY_ARTIFACT_BOUND_SOURCE_ATOM_CONTRACT.contract_sha256
            ),
            source_artifact_sha256=sha("9"),
            source_quote_sha256=source.semantic_payload["source_quote_sha256"],
            source_component_sha256=source.semantic_payload[
                "source_component_sha256"
            ],
            source_role_contract_sha256=source.semantic_payload[
                "source_role_contract_sha256"
            ],
        )
        historical_judgment = source_lean_judgment_leaf(
            contract_sha256=judgment.contract_sha256,
            source_atom_sha256s=[historical_source.leaf_sha256],
            lean_declaration_sha256=judgment.semantic_payload[
                "lean_declaration_sha256"
            ],
            verbatim_source_bundle_sha256=judgment.semantic_payload[
                "verbatim_source_bundle_sha256"
            ],
            verdict="matches",
        )
        leaves = [
            leaf
            for leaf in graph.leaves.values()
            if leaf.leaf_sha256 not in {source.leaf_sha256, judgment.leaf_sha256}
        ] + [historical_source, historical_judgment]
        historical_graph = build_obligation_graph(
            leaves,
            root_leaf_sha256s=[
                historical_judgment.leaf_sha256
                if digest == judgment.leaf_sha256
                else digest
                for digest in graph.root_leaf_sha256s
            ],
        )
        with self.assertRaisesRegex(
            PaperObligationIndexError, "binds a different source artifact"
        ):
            build_paper_obligation_index_from_preflight(
                historical_graph,
                self.preflight(),
                complete_paper_surface=True,
                route_leaf_sha256s_by_source_item=self.route_bindings(
                    historical_graph
                ),
            )


if __name__ == "__main__":
    unittest.main()
