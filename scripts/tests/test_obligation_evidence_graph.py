from __future__ import annotations

import ast
import copy
import unittest
from pathlib import Path

from scripts.obligation_evidence_graph import (
    ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA,
    ObligationEvidenceError,
    ObligationKind,
    ProofRealizationMode,
    SourceLeanVerdict,
    build_evidence_leaf,
    build_obligation_graph,
    diff_obligation_graph,
    legacy_artifact_bound_source_atom_leaf,
    legacy_content_bound_reviewed_semantic_target_leaf,
    lean_declaration_leaf,
    lean_reviewed_semantic_prerequisite_leaf,
    lean_reviewed_semantic_target_leaf,
    proof_realization_leaf,
    merge_obligation_graphs,
    paper_closure_leaf,
    source_atom_leaf,
    source_lean_judgment_leaf,
    validate_obligation_graph,
)
from scripts.obligation_evidence_contracts import PAPER_CLOSURE_CONTRACT


def sha(character: str) -> str:
    return character * 64


class ObligationEvidenceGraphTests(unittest.TestCase):
    def source(self, marker: str = "1"):
        return source_atom_leaf(
            contract_sha256=sha("a"),
            source_artifact_sha256=sha("b"),
            source_quote_sha256=sha("c"),
            source_component_sha256=sha(marker),
            source_role_contract_sha256=sha("d"),
        )

    def lean(self, marker: str = "2", *, kind: str = "spec_proposition"):
        return lean_declaration_leaf(
            contract_sha256=sha("e"),
            semantic_target_kind=kind,
            elaborated_signature_sha256=sha(marker),
            elaborated_proposition_graph_sha256=sha("f"),
            semantic_dependency_sha256=sha("0"),
        )

    def complete_claim(self):
        source = self.source()
        spec = self.lean()
        endpoint = self.lean("3", kind="proof_endpoint")
        judgment = source_lean_judgment_leaf(
            contract_sha256=sha("4"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=spec.leaf_sha256,
            verbatim_source_bundle_sha256=sha("c"),
            verdict=SourceLeanVerdict.MATCHES,
        )
        realization = proof_realization_leaf(
            contract_sha256=sha("6"),
            spec_declaration_sha256=spec.leaf_sha256,
            proof_endpoint_sha256=endpoint.leaf_sha256,
            relation=ProofRealizationMode.PROVES,
            lean_relation_sha256=sha("7"),
        )
        build = build_evidence_leaf(
            contract_sha256=sha("8"),
            target_declaration_sha256s=[endpoint.leaf_sha256],
            build_command_sha256=sha("9"),
            toolchain_sha256=sha("a"),
            lean_import_closure_sha256=sha("b"),
        )
        leaves = [source, spec, endpoint, judgment, realization, build]
        graph = build_obligation_graph(
            leaves,
            root_leaf_sha256s=[judgment.leaf_sha256, realization.leaf_sha256, build.leaf_sha256],
        )
        return leaves, graph

    def test_core_cannot_import_filesystem_subprocess_or_producers(self) -> None:
        path = Path(__file__).parents[1] / "obligation_evidence_graph.py"
        tree = ast.parse(path.read_text(encoding="utf-8"))
        imported = {
            alias.name.split(".")[0]
            for node in ast.walk(tree)
            if isinstance(node, ast.Import)
            for alias in node.names
        }
        imported.update(
            str(node.module or "").split(".")[0]
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
        )
        self.assertFalse(
            imported
            & {
                "subprocess",
                "pathlib",
                "review_dashboard",
                "source_record_audit",
                "audit_repository",
                "closeout_reuse_plan",
            }
        )

    def test_navigation_path_line_and_engine_are_not_leaf_fields(self) -> None:
        first = self.source()
        second = self.source()
        self.assertEqual(first.leaf_sha256, second.leaf_sha256)
        payload = first.projection()
        payload["semantic_payload"]["source_line"] = 97
        with self.assertRaisesRegex(ObligationEvidenceError, "payload fields"):
            build_obligation_graph([payload], root_leaf_sha256s=[first.leaf_sha256])

    def test_whole_source_carrier_does_not_change_current_atom_identity(self) -> None:
        first = source_atom_leaf(
            contract_sha256=sha("a"),
            source_artifact_sha256=sha("1"),
            source_quote_sha256=sha("c"),
            source_component_sha256=sha("2"),
            source_role_contract_sha256=sha("d"),
        )
        moved_or_reextracted = source_atom_leaf(
            contract_sha256=sha("a"),
            source_artifact_sha256=sha("9"),
            source_quote_sha256=sha("c"),
            source_component_sha256=sha("2"),
            source_role_contract_sha256=sha("d"),
        )
        self.assertEqual(first.leaf_sha256, moved_or_reextracted.leaf_sha256)
        self.assertNotIn("source_artifact_sha256", first.semantic_payload)

    def test_historical_artifact_bound_atom_remains_directly_verifiable(self) -> None:
        historical = legacy_artifact_bound_source_atom_leaf(
            contract_sha256=sha("a"),
            source_artifact_sha256=sha("1"),
            source_quote_sha256=sha("c"),
            source_component_sha256=sha("2"),
            source_role_contract_sha256=sha("d"),
        )
        rebuilt = build_obligation_graph(
            [historical], root_leaf_sha256s=[historical.leaf_sha256]
        )
        self.assertIn(
            "source_artifact_sha256",
            rebuilt.leaves[historical.leaf_sha256].semantic_payload,
        )

    def test_paper_and_library_declarations_use_the_same_semantic_schema(self) -> None:
        # Location and qualified name are deliberately not constructor inputs.
        paper = self.lean()
        library = self.lean()
        self.assertEqual(paper.leaf_sha256, library.leaf_sha256)
        self.assertEqual(paper.kind, ObligationKind.LEAN_DECLARATION)

    def test_reviewed_prerequisite_leaf_is_path_and_name_independent(self) -> None:
        paper = lean_reviewed_semantic_prerequisite_leaf(
            contract_sha256=sha("e"),
            reviewed_semantic_target_sha256=sha("1"),
        )
        library = lean_reviewed_semantic_prerequisite_leaf(
            contract_sha256=sha("e"),
            reviewed_semantic_target_sha256=sha("1"),
        )
        self.assertEqual(paper.leaf_sha256, library.leaf_sha256)
        self.assertEqual(paper.kind, ObligationKind.LEAN_DECLARATION)

    def test_reviewed_semantic_target_reuses_one_location_neutral_schema(self) -> None:
        spec = lean_reviewed_semantic_target_leaf(
            contract_sha256=sha("e"),
            semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256=sha("1"),
        )
        self.assertEqual(
            spec.semantic_payload["semantic_target_kind"], "spec_proposition"
        )
        with self.assertRaisesRegex(
            ObligationEvidenceError, "proof endpoint requires"
        ):
            lean_reviewed_semantic_target_leaf(
                contract_sha256=sha("e"),
                semantic_target_kind="proof_endpoint",
                reviewed_semantic_target_sha256=sha("1"),
            )

    def test_reviewed_semantic_target_can_bind_renderer_independent_lean_identity(self) -> None:
        leaf = lean_reviewed_semantic_target_leaf(
            contract_sha256=sha("e"),
            semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256=sha("1"),
            elaborated_signature_sha256=sha("2"),
        )
        self.assertEqual(
            leaf.semantic_payload,
            {
                "semantic_target_kind": "spec_proposition",
                "reviewed_semantic_target_sha256": sha("1"),
                "elaborated_signature_sha256": sha("2"),
            },
        )
        rebuilt = build_obligation_graph(
            [leaf], root_leaf_sha256s=[leaf.leaf_sha256]
        )
        self.assertEqual(rebuilt.leaves[leaf.leaf_sha256], leaf)

    def test_historical_content_bound_review_target_remains_verifiable(self) -> None:
        historical = legacy_content_bound_reviewed_semantic_target_leaf(
            contract_sha256=sha("e"),
            semantic_target_kind="spec_proposition",
            reviewed_semantic_target_sha256=sha("1"),
            declaration_content_sha256=sha("2"),
        )
        rebuilt = build_obligation_graph(
            [historical], root_leaf_sha256s=[historical.leaf_sha256]
        )
        self.assertEqual(
            rebuilt.leaves[historical.leaf_sha256].semantic_payload[
                "declaration_content_sha256"
            ],
            sha("2"),
        )

    def test_protocol_change_invalidates_only_judgment_family(self) -> None:
        source = self.source()
        lean = self.lean()
        first = source_lean_judgment_leaf(
            contract_sha256=sha("4"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=lean.leaf_sha256,
            verbatim_source_bundle_sha256=sha("c"),
            verdict="matches",
        )
        later = source_lean_judgment_leaf(
            contract_sha256=sha("6"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=lean.leaf_sha256,
            verbatim_source_bundle_sha256=sha("c"),
            verdict="matches",
        )
        self.assertEqual(source, self.source())
        self.assertEqual(lean, self.lean())
        self.assertNotEqual(first.leaf_sha256, later.leaf_sha256)

    def test_one_spec_change_preserves_unrelated_leaves(self) -> None:
        leaves, graph = self.complete_claim()
        available = {leaf.leaf_sha256: leaf.projection() for leaf in leaves}
        self.assertTrue(diff_obligation_graph(graph, available).complete)

        source = leaves[0]
        changed_spec = self.lean("4")
        endpoint = leaves[2]
        changed_judgment = source_lean_judgment_leaf(
            contract_sha256=sha("4"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=changed_spec.leaf_sha256,
            verbatim_source_bundle_sha256=sha("c"),
            verdict="matches",
        )
        changed_realization = proof_realization_leaf(
            contract_sha256=sha("6"),
            spec_declaration_sha256=changed_spec.leaf_sha256,
            proof_endpoint_sha256=endpoint.leaf_sha256,
            relation="proves",
            lean_relation_sha256=sha("8"),
        )
        build = leaves[5]
        changed_graph = build_obligation_graph(
            [source, changed_spec, endpoint, changed_judgment, changed_realization, build],
            root_leaf_sha256s=[
                changed_judgment.leaf_sha256,
                changed_realization.leaf_sha256,
                build.leaf_sha256,
            ],
        )
        diff = diff_obligation_graph(changed_graph, available)
        self.assertIn(source.leaf_sha256, diff.reusable_leaf_sha256s)
        self.assertIn(endpoint.leaf_sha256, diff.reusable_leaf_sha256s)
        self.assertIn(build.leaf_sha256, diff.reusable_leaf_sha256s)
        self.assertEqual(
            set(diff.missing_leaf_sha256s),
            {
                changed_spec.leaf_sha256,
                changed_judgment.leaf_sha256,
                changed_realization.leaf_sha256,
            },
        )

    def test_corrupt_available_leaf_does_not_erase_other_successes(self) -> None:
        leaves, graph = self.complete_claim()
        available = {leaf.leaf_sha256: leaf.projection() for leaf in leaves}
        broken_digest = leaves[1].leaf_sha256
        available[broken_digest] = copy.deepcopy(available[broken_digest])
        available[broken_digest]["semantic_payload"][
            "elaborated_signature_sha256"
        ] = sha("9")
        diff = diff_obligation_graph(graph, available)
        self.assertEqual(diff.corrupt_leaf_sha256s, (broken_digest,))
        self.assertEqual(len(diff.reusable_leaf_sha256s), len(leaves) - 1)
        self.assertIn(broken_digest, diff.blocked_by_missing[leaves[3].leaf_sha256])

    def test_persisted_graph_index_is_rebuilt_from_leaf_objects(self) -> None:
        leaves, graph = self.complete_claim()
        persisted = graph.projection()
        loaded = {
            leaf.leaf_sha256: leaf.projection() for leaf in reversed(leaves)
        }
        rebuilt = validate_obligation_graph(persisted, leaves=loaded)
        self.assertEqual(rebuilt.graph_sha256, graph.graph_sha256)

        corrupt = dict(persisted)
        corrupt["graph_sha256"] = sha("f")
        with self.assertRaisesRegex(ObligationEvidenceError, "identity is corrupt"):
            validate_obligation_graph(corrupt, leaves=loaded)

    def test_graph_rejects_missing_dependencies_and_cycles(self) -> None:
        source = self.source()
        lean = self.lean()
        judgment = source_lean_judgment_leaf(
            contract_sha256=sha("4"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=lean.leaf_sha256,
            verbatim_source_bundle_sha256=sha("c"),
            verdict="matches",
        )
        with self.assertRaisesRegex(ObligationEvidenceError, "missing dependencies"):
            build_obligation_graph(
                [judgment], root_leaf_sha256s=[judgment.leaf_sha256]
            )

        # A direct dataclass mutation cannot bypass the persisted-object parser.
        forged = copy.deepcopy(judgment.projection())
        forged["depends_on"] = [judgment.leaf_sha256]
        with self.assertRaises(ObligationEvidenceError):
            build_obligation_graph([forged], root_leaf_sha256s=[judgment.leaf_sha256])

    def test_graph_rejects_unreachable_container_only_leaves(self) -> None:
        first = self.source("1")
        second = self.source("2")
        with self.assertRaisesRegex(ObligationEvidenceError, "unreachable"):
            build_obligation_graph(
                [first, second], root_leaf_sha256s=[first.leaf_sha256]
            )

    def test_independent_subgraphs_merge_without_reissuing_shared_leaves(self) -> None:
        source = self.source()
        first_lean = self.lean("2")
        second_lean = self.lean("3")
        first = build_obligation_graph(
            [source, first_lean],
            root_leaf_sha256s=[source.leaf_sha256, first_lean.leaf_sha256],
        )
        second = build_obligation_graph(
            [source, second_lean],
            root_leaf_sha256s=[source.leaf_sha256, second_lean.leaf_sha256],
        )
        merged = merge_obligation_graphs([first, second])
        self.assertEqual(len(merged.leaves), 3)
        self.assertEqual(
            set(merged.root_leaf_sha256s),
            {source.leaf_sha256, first_lean.leaf_sha256, second_lean.leaf_sha256},
        )

    def test_terminal_root_makes_the_graph_itself_the_acceptance_credential(self) -> None:
        leaves, semantic_graph = self.complete_claim()
        closure = paper_closure_leaf(
            contract_sha256=PAPER_CLOSURE_CONTRACT.contract_sha256,
            semantic_graph_sha256=semantic_graph.graph_sha256,
            paper_index_sha256=sha("1"),
            terminal_verification_sha256=sha("2"),
            terminal_authority_sha256=sha("3"),
            semantic_root_leaf_sha256s=semantic_graph.root_leaf_sha256s,
        )
        accepted = build_obligation_graph(
            [*leaves, closure], root_leaf_sha256s=[closure.leaf_sha256]
        )
        self.assertEqual(accepted.schema, ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA)
        self.assertTrue(accepted.projection()["acceptance_credential"])
        self.assertFalse(accepted.projection()["integrity_and_planning_only"])
        self.assertEqual(accepted.root_leaf_sha256s, (closure.leaf_sha256,))
        rebuilt = validate_obligation_graph(
            accepted.projection(),
            leaves={digest: leaf.projection() for digest, leaf in accepted.leaves.items()},
        )
        self.assertEqual(rebuilt, accepted)

    def test_terminal_tooling_change_replaces_only_the_closure_root(self) -> None:
        leaves, semantic_graph = self.complete_claim()
        def accepted(authority: str):
            closure = paper_closure_leaf(
                contract_sha256=PAPER_CLOSURE_CONTRACT.contract_sha256,
                semantic_graph_sha256=semantic_graph.graph_sha256,
                paper_index_sha256=sha("1"),
                terminal_verification_sha256=sha("2"),
                terminal_authority_sha256=sha(authority),
                semantic_root_leaf_sha256s=semantic_graph.root_leaf_sha256s,
            )
            return build_obligation_graph(
                [*leaves, closure], root_leaf_sha256s=[closure.leaf_sha256]
            )

        first = accepted("3")
        later = accepted("4")
        self.assertNotEqual(first.graph_sha256, later.graph_sha256)
        self.assertEqual(
            set(first.leaves) - set(first.root_leaf_sha256s),
            set(later.leaves) - set(later.root_leaf_sha256s),
        )
        self.assertEqual(
            first.leaves[first.root_leaf_sha256s[0]].semantic_payload[
                "semantic_graph_sha256"
            ],
            semantic_graph.graph_sha256,
        )

    def test_terminal_root_cannot_name_a_different_semantic_graph(self) -> None:
        leaves, semantic_graph = self.complete_claim()
        closure = paper_closure_leaf(
            contract_sha256=PAPER_CLOSURE_CONTRACT.contract_sha256,
            semantic_graph_sha256=sha("f"),
            paper_index_sha256=sha("1"),
            terminal_verification_sha256=sha("2"),
            terminal_authority_sha256=sha("3"),
            semantic_root_leaf_sha256s=semantic_graph.root_leaf_sha256s,
        )
        with self.assertRaisesRegex(ObligationEvidenceError, "different semantic"):
            build_obligation_graph(
                [*leaves, closure], root_leaf_sha256s=[closure.leaf_sha256]
            )


if __name__ == "__main__":
    unittest.main()
