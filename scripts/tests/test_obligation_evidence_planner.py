from __future__ import annotations

import ast
import copy
import unittest
from pathlib import Path

from scripts.obligation_evidence_graph import (
    build_obligation_graph,
    lean_declaration_leaf,
    source_atom_leaf,
    source_lean_judgment_leaf,
)
from scripts.obligation_evidence_issuance import (
    issue_obligation_evidence_attestation,
)
from scripts.obligation_evidence_planner import (
    ObligationEvidencePlanningError,
    plan_obligation_evidence,
    verify_complete_obligation_evidence,
)


def sha(character: str) -> str:
    return character * 64


class ObligationEvidencePlannerTests(unittest.TestCase):
    def fixture(self):
        source = source_atom_leaf(
            contract_sha256=sha("1"),
            source_artifact_sha256=sha("2"),
            source_quote_sha256=sha("3"),
            source_component_sha256=sha("4"),
            source_role_contract_sha256=sha("5"),
        )
        lean = lean_declaration_leaf(
            contract_sha256=sha("6"),
            semantic_target_kind="spec_proposition",
            elaborated_signature_sha256=sha("7"),
            elaborated_proposition_graph_sha256=sha("8"),
            semantic_dependency_sha256=sha("9"),
        )
        judgment = source_lean_judgment_leaf(
            contract_sha256=sha("a"),
            source_atom_sha256s=[source.leaf_sha256],
            lean_declaration_sha256=lean.leaf_sha256,
            verbatim_source_bundle_sha256=sha("b"),
            verdict="matches",
        )
        leaves = (source, lean, judgment)
        graph = build_obligation_graph(
            leaves, root_leaf_sha256s=[judgment.leaf_sha256]
        )
        authority = sha("c")
        issuances = tuple(
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("d"),
                authority_sha256=authority,
                evidence_record_sha256=sha(str(index + 1)),
            )
            for index, leaf in enumerate(leaves)
        )
        available = {leaf.leaf_sha256: leaf.projection() for leaf in leaves}
        return graph, available, issuances, authority, leaves

    def test_planner_and_terminal_core_have_no_producer_imports(self) -> None:
        path = Path(__file__).parents[1] / "obligation_evidence_planner.py"
        tree = ast.parse(path.read_text(encoding="utf-8"))
        imported = {
            str(node.module or "").split(".")[0]
            for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
        }
        imported.update(
            alias.name.split(".")[0]
            for node in ast.walk(tree)
            if isinstance(node, ast.Import)
            for alias in node.names
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

    def test_complete_graph_is_reusable_and_terminal_verifies(self) -> None:
        graph, available, issuances, authority, leaves = self.fixture()
        plan = plan_obligation_evidence(
            graph,
            available,
            issuances,
            authenticated_authority_sha256s=[authority],
        )
        self.assertTrue(plan.complete)
        self.assertEqual(set(plan.reusable_leaf_sha256s), {x.leaf_sha256 for x in leaves})
        verified = verify_complete_obligation_evidence(
            graph,
            available,
            issuances,
            authenticated_authority_sha256s=[authority],
        )
        self.assertFalse(verified.projection()["acceptance_credential"])

    def test_existing_unattested_leaf_schedules_authentication_not_replay(self) -> None:
        graph, available, issuances, authority, leaves = self.fixture()
        plan = plan_obligation_evidence(
            graph,
            available,
            issuances[:-1],
            authenticated_authority_sha256s=[authority],
        )
        self.assertEqual(plan.missing_leaf_sha256s, ())
        self.assertEqual(plan.unattested_leaf_sha256s, (leaves[-1].leaf_sha256,))
        self.assertEqual(plan.work_queue[-1].action, "authenticate_existing_leaf")
        with self.assertRaisesRegex(
            ObligationEvidencePlanningError, "unattested"
        ):
            verify_complete_obligation_evidence(
                graph,
                available,
                issuances[:-1],
                authenticated_authority_sha256s=[authority],
            )

    def test_missing_leaf_reports_only_exact_leaf_and_blocked_descendant(self) -> None:
        graph, available, issuances, authority, leaves = self.fixture()
        available.pop(leaves[1].leaf_sha256)
        plan = plan_obligation_evidence(
            graph,
            available,
            issuances,
            authenticated_authority_sha256s=[authority],
        )
        self.assertEqual(plan.missing_leaf_sha256s, (leaves[1].leaf_sha256,))
        self.assertIn(leaves[1].leaf_sha256, plan.blocked_by_missing[leaves[2].leaf_sha256])
        self.assertEqual(
            [item.leaf_sha256 for item in plan.work_queue],
            [leaves[1].leaf_sha256],
        )

    def test_corrupt_issuance_does_not_trigger_semantic_producer(self) -> None:
        graph, available, issuances, authority, leaves = self.fixture()
        corrupt = copy.deepcopy(issuances[-1].projection())
        corrupt["evidence_record_sha256"] = sha("f")
        plan = plan_obligation_evidence(
            graph,
            available,
            (*issuances[:-1], corrupt),
            authenticated_authority_sha256s=[authority],
        )
        self.assertEqual(plan.missing_leaf_sha256s, ())
        self.assertEqual(plan.work_queue[-1].action, "authenticate_existing_leaf")


if __name__ == "__main__":
    unittest.main()
