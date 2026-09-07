from __future__ import annotations

import unittest
import tempfile
from pathlib import Path
from unittest.mock import patch

from scripts.obligation_evidence_issuance import (
    TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
    issue_obligation_evidence_attestation,
)
from scripts import obligation_evidence_store as evidence_store
from scripts.obligation_evidence_store import (
    current_bundle_path,
    load_paper_obligation_bundle,
    store_paper_obligation_bundle,
)
from scripts.obligation_paper_bundle import (
    PaperObligationBundleError,
    build_accepting_paper_obligation_bundle,
    build_paper_obligation_bundle,
    paper_obligation_terminal_verification_sha256,
    validate_paper_obligation_bundle,
)
from scripts.tests.test_obligation_paper_index import PaperObligationIndexTests, sha


class PaperObligationBundleTests(unittest.TestCase):
    def fixture(self):
        graph = PaperObligationIndexTests().complete_graph()
        index, preflight = PaperObligationIndexTests().complete_index(graph)
        authority = sha("4")
        issuances = [
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("5"),
                authority_sha256=authority,
                evidence_record_sha256=sha("6"),
            )
            for leaf in graph.leaves.values()
        ]
        return graph, index, issuances, preflight

    def test_complete_bundle_round_trips_exact_selected_issuances(self) -> None:
        graph, index, issuances, preflight = self.fixture()
        bundle = build_paper_obligation_bundle(
            index, graph, issuances, preflight=preflight
        )
        loaded = validate_paper_obligation_bundle(
            bundle.projection(),
            paper_index=index,
            graph=graph,
            issuances={item.issuance_sha256: item for item in issuances},
            preflight=preflight,
        )
        self.assertEqual(loaded, bundle)
        self.assertFalse(loaded.projection()["acceptance_credential"])

    def test_bundle_refuses_unattested_leaf(self) -> None:
        graph, index, issuances, preflight = self.fixture()
        with self.assertRaisesRegex(
            PaperObligationBundleError, "unattested leaves"
        ):
            build_paper_obligation_bundle(
                index, graph, issuances[:-1], preflight=preflight
            )

    def test_accepting_bundle_requires_exact_terminal_issuance_per_leaf(self) -> None:
        graph, index, _issuances, preflight = self.fixture()
        terminal = paper_obligation_terminal_verification_sha256(index, graph)
        issuances = [
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=TERMINAL_PAPER_CLOSURE_ASSURANCE_SHA256,
                authority_sha256=sha("4"),
                evidence_record_sha256=terminal,
            )
            for leaf in graph.leaves.values()
        ]
        bundle = build_accepting_paper_obligation_bundle(
            index, graph, issuances, preflight=preflight
        )
        self.assertEqual(bundle.schema, 2)
        self.assertTrue(bundle.acceptance_credential)
        self.assertEqual(bundle.terminal_verification_sha256, terminal)
        loaded = validate_paper_obligation_bundle(
            bundle.projection(),
            paper_index=index,
            graph=graph,
            issuances={item.issuance_sha256: item for item in issuances},
            preflight=preflight,
        )
        self.assertEqual(loaded, bundle)

        wrong = [
            issue_obligation_evidence_attestation(
                leaf_sha256=leaf.leaf_sha256,
                assurance_contract_sha256=sha("5"),
                authority_sha256=sha("4"),
                evidence_record_sha256=terminal,
            )
            for leaf in graph.leaves.values()
        ]
        with self.assertRaisesRegex(
            PaperObligationBundleError, "terminal verification issuance"
        ):
            build_accepting_paper_obligation_bundle(
                index, graph, wrong, preflight=preflight
            )

    def test_complete_bundle_store_is_portable_and_round_trips(self) -> None:
        graph, index, issuances, preflight = self.fixture()
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            roots = (Path(first), Path(second))
            pointers = []
            for root in roots:
                (root / "papers" / "Fixture").mkdir(parents=True)
                pointers.append(
                    store_paper_obligation_bundle(
                        root,
                        "Fixture",
                        index,
                        graph,
                        issuances,
                        preflight=preflight,
                    )
                )
                loaded = load_paper_obligation_bundle(root, "Fixture")
                self.assertEqual(loaded.graph, graph)
                self.assertEqual(loaded.paper_index, index)
                self.assertEqual(set(loaded.issuances), {
                    item.issuance_sha256 for item in issuances
                })
            self.assertEqual(pointers[0].read_bytes(), pointers[1].read_bytes())
            self.assertNotIn(str(roots[0]).encode(), pointers[0].read_bytes())

    def test_interrupted_republication_preserves_prior_current_bundle(self) -> None:
        graph, index, issuances, preflight = self.fixture()
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
            prior = load_paper_obligation_bundle(root, "Fixture").bundle
            changed_issuances = [
                issue_obligation_evidence_attestation(
                    leaf_sha256=item.leaf_sha256,
                    assurance_contract_sha256=item.assurance_contract_sha256,
                    authority_sha256=item.authority_sha256,
                    evidence_record_sha256=sha("7"),
                )
                for item in issuances
            ]
            original_atomic_write = evidence_store._atomic_write

            def fail_current_pointer(path, payload):
                if path == current_bundle_path(root, "Fixture"):
                    raise OSError("simulated interruption before pointer publication")
                return original_atomic_write(path, payload)

            with patch.object(
                evidence_store,
                "_atomic_write",
                side_effect=fail_current_pointer,
            ):
                with self.assertRaisesRegex(OSError, "simulated interruption"):
                    store_paper_obligation_bundle(
                        root,
                        "Fixture",
                        index,
                        graph,
                        changed_issuances,
                        preflight=preflight,
                    )
            self.assertEqual(
                load_paper_obligation_bundle(root, "Fixture").bundle,
                prior,
            )


if __name__ == "__main__":
    unittest.main()
