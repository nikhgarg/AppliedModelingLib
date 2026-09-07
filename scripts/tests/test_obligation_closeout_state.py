from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.obligation_closeout_state import (
    ObligationCloseoutStateError,
    plan_stored_paper_obligations,
    verify_current_stored_paper_obligations,
)
from scripts.obligation_evidence_issuance import issue_obligation_evidence_attestation
from scripts.obligation_evidence_store import (
    store_issued_obligation_leaf,
    store_paper_obligation_bundle,
)
from scripts.tests.test_obligation_paper_index import PaperObligationIndexTests, sha


class ObligationCloseoutStateTests(unittest.TestCase):
    def fixture(self):
        graph = PaperObligationIndexTests().complete_graph()
        index, preflight = PaperObligationIndexTests().complete_index(graph)
        authority = sha("4")
        issuances = tuple(
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("5"),
                authority_sha256=authority,
                evidence_record_sha256=sha("6"),
            )
            for leaf in graph.leaves.values()
        )
        return graph, index, authority, issuances, preflight

    def test_plan_reuses_objects_before_bundle_publication(self) -> None:
        graph, index, authority, issuances, preflight = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            for leaf, issuance in zip(graph.leaves.values(), issuances):
                store_issued_obligation_leaf(root, "Fixture", leaf, issuance)
            plan = plan_stored_paper_obligations(
                root,
                "Fixture",
                index,
                graph,
                preflight=preflight,
                authenticated_authority_sha256s=[authority],
            )
            self.assertTrue(plan.complete)
            self.assertEqual(plan.work_queue, ())
            with self.assertRaisesRegex(
                ObligationCloseoutStateError, "current obligation bundle"
            ):
                verify_current_stored_paper_obligations(
                    root,
                    "Fixture",
                    index,
                    graph,
                    preflight=preflight,
                    authenticated_authority_sha256s=[authority],
                )

    def test_terminal_verification_requires_exact_selected_complete_bundle(self) -> None:
        graph, index, authority, issuances, preflight = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            store_paper_obligation_bundle(
                root,
                "Fixture",
                index,
                graph,
                issuances,
                preflight=preflight,
            )
            verified = verify_current_stored_paper_obligations(
                root,
                "Fixture",
                index,
                graph,
                preflight=preflight,
                authenticated_authority_sha256s=[authority],
            )
            self.assertEqual(verified.paper_index_sha256, index.index_sha256)
            self.assertFalse(verified.projection()["acceptance_credential"])
            with self.assertRaisesRegex(
                ObligationCloseoutStateError, "unattested"
            ):
                verify_current_stored_paper_obligations(
                    root,
                    "Fixture",
                    index,
                    graph,
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("7")],
                )


if __name__ == "__main__":
    unittest.main()
