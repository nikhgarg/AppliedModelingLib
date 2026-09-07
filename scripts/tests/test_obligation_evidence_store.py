from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts.obligation_evidence_graph import (
    build_obligation_graph,
    lean_declaration_leaf,
    source_atom_leaf,
)
from scripts.obligation_evidence_store import (
    ObligationEvidenceStoreError,
    graph_index_path,
    load_lean_declaration_resolution,
    load_obligation_evidence_store_snapshot,
    load_obligation_graph,
    load_obligation_leaf,
    store_issued_obligation_leaf,
    store_lean_declaration_resolution,
    store_obligation_graph,
    store_obligation_leaf,
    store_obligation_leaves,
)
from scripts.obligation_evidence_issuance import issue_obligation_evidence_attestation
from scripts.obligation_evidence_planner import plan_obligation_evidence
from scripts.portable_evidence_identity import canonical_json_bytes


def sha(character: str) -> str:
    return character * 64


class ObligationEvidenceStoreTests(unittest.TestCase):
    def leaves(self):
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
        return source, lean

    def test_successful_leaves_survive_without_graph_publication(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            source, lean = self.leaves()
            paths = store_obligation_leaves(root, "Fixture", [source, lean])
            self.assertEqual(len(paths), 2)
            self.assertFalse(graph_index_path(root, "Fixture").exists())
            self.assertEqual(
                load_obligation_leaf(root, "Fixture", source.leaf_sha256), source
            )

            # A retry is idempotent and cannot rewrite the other successful leaf.
            before = paths[1].read_bytes()
            self.assertEqual(store_obligation_leaf(root, "Fixture", source), paths[0])
            self.assertEqual(paths[1].read_bytes(), before)

    def test_graph_publication_round_trips_every_independent_leaf(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            source, lean = self.leaves()
            graph = build_obligation_graph(
                [source, lean], root_leaf_sha256s=[source.leaf_sha256, lean.leaf_sha256]
            )
            store_obligation_graph(root, "Fixture", graph)
            self.assertEqual(load_obligation_graph(root, "Fixture"), graph)

    def test_lean_resolution_reuses_only_coordinate_bound_issuance(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            _source, lean = self.leaves()
            coordinate = sha("a")
            authority = sha("b")
            assurance = sha("c")
            context_sha256 = sha("d")
            basis = {"schema": 1, "semantic_graph": sha("e")}
            basis_sha256 = hashlib.sha256(
                canonical_json_bytes(basis)
            ).hexdigest()
            semantic = lean.semantic_payload
            record = hashlib.sha256(
                canonical_json_bytes(
                    {
                        "schema": 1,
                        "coordinate_sha256": coordinate,
                        "leaf_sha256": lean.leaf_sha256,
                        "elaborated_signature_sha256": semantic[
                            "elaborated_signature_sha256"
                        ],
                        "elaborated_proposition_graph_sha256": semantic[
                            "elaborated_proposition_graph_sha256"
                        ],
                        "semantic_dependency_sha256": semantic[
                            "semantic_dependency_sha256"
                        ],
                        "manifest_cache_context_sha256": context_sha256,
                        "manifest_revalidation_basis_sha256": basis_sha256,
                    }
                )
            ).hexdigest()
            issuance = issue_obligation_evidence_attestation(
                leaf_sha256=lean.leaf_sha256,
                assurance_contract_sha256=assurance,
                authority_sha256=authority,
                evidence_record_sha256=record,
            )
            store_lean_declaration_resolution(
                root,
                "Fixture",
                coordinate_sha256=coordinate,
                declaration="Fixture.Model",
                leaf=lean,
                issuance=issuance,
                manifest_cache_context_sha256=context_sha256,
                manifest_revalidation_basis=basis,
            )
            loaded = load_lean_declaration_resolution(
                root,
                "Fixture",
                coordinate_sha256=coordinate,
                declaration="Fixture.Model",
                authenticated_authority_sha256s=(authority,),
                assurance_contract_sha256=assurance,
            )
            assert loaded is not None
            self.assertEqual(loaded.leaf, lean)
            self.assertEqual(loaded.issuance, issuance)
            self.assertEqual(loaded.manifest_cache_context_sha256, context_sha256)
            self.assertEqual(dict(loaded.manifest_revalidation_basis), basis)
            self.assertIsNone(
                load_lean_declaration_resolution(
                    root,
                    "Fixture",
                    coordinate_sha256=coordinate,
                    declaration="Fixture.Other",
                    authenticated_authority_sha256s=(authority,),
                    assurance_contract_sha256=assurance,
                )
            )

    def test_identical_graph_bytes_are_portable_across_roots(self) -> None:
        with tempfile.TemporaryDirectory() as first_dir, tempfile.TemporaryDirectory() as second_dir:
            first_root = Path(first_dir)
            second_root = Path(second_dir)
            for root in (first_root, second_root):
                (root / "papers" / "Fixture").mkdir(parents=True)
            source, lean = self.leaves()
            graph = build_obligation_graph(
                [source, lean], root_leaf_sha256s=[source.leaf_sha256, lean.leaf_sha256]
            )
            first = store_obligation_graph(first_root, "Fixture", graph)
            second = store_obligation_graph(second_root, "Fixture", graph)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            first_leaf = load_obligation_leaf(
                first_root, "Fixture", source.leaf_sha256
            )
            second_leaf = load_obligation_leaf(
                second_root, "Fixture", source.leaf_sha256
            )
            self.assertEqual(first_leaf, second_leaf)
            self.assertNotIn(str(first_root).encode(), first.read_bytes())

    def test_conflicting_bytes_at_semantic_path_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            source, _lean = self.leaves()
            path = store_obligation_leaf(root, "Fixture", source)
            path.write_text("{}\n", encoding="utf-8")
            with self.assertRaisesRegex(
                ObligationEvidenceStoreError, "conflicting bytes"
            ):
                store_obligation_leaf(root, "Fixture", source)

    def test_exact_snapshot_reuses_independently_published_work(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            source, lean = self.leaves()
            graph = build_obligation_graph(
                [source, lean],
                root_leaf_sha256s=[source.leaf_sha256, lean.leaf_sha256],
            )
            authority = sha("a")
            for leaf in graph.leaves.values():
                issuance = issue_obligation_evidence_attestation(
                    leaf_sha256=leaf.leaf_sha256,
                    assurance_contract_sha256=sha("b"),
                    authority_sha256=authority,
                    evidence_record_sha256=sha("c"),
                )
                store_issued_obligation_leaf(root, "Fixture", leaf, issuance)

            snapshot = load_obligation_evidence_store_snapshot(
                root, "Fixture", graph
            )
            plan = plan_obligation_evidence(
                graph,
                snapshot.available_leaves,
                snapshot.issuances,
                authenticated_authority_sha256s=[authority],
            )
            self.assertTrue(plan.complete)
            self.assertEqual(plan.work_queue, ())
            self.assertFalse(graph_index_path(root, "Fixture").exists())

    def test_snapshot_distinguishes_corrupt_leaf_and_corrupt_issuance(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            source, lean = self.leaves()
            graph = build_obligation_graph(
                [source, lean],
                root_leaf_sha256s=[source.leaf_sha256, lean.leaf_sha256],
            )
            authority = sha("a")
            issuances = []
            for leaf in graph.leaves.values():
                issuance = issue_obligation_evidence_attestation(
                    leaf_sha256=leaf.leaf_sha256,
                    assurance_contract_sha256=sha("b"),
                    authority_sha256=authority,
                    evidence_record_sha256=sha("c"),
                )
                store_issued_obligation_leaf(root, "Fixture", leaf, issuance)
                issuances.append(issuance)
            source_path = store_obligation_leaf(root, "Fixture", source)
            source_path.write_text("not-json\n", encoding="utf-8")
            issuance_path = next(
                (
                    root
                    / "papers"
                    / "Fixture"
                    / "audit"
                    / "obligation_evidence"
                    / "attestations"
                    / "by_leaf"
                    / lean.leaf_sha256[:2]
                    / lean.leaf_sha256
                ).glob("*.json")
            )
            issuance_path.write_text("not-json\n", encoding="utf-8")

            snapshot = load_obligation_evidence_store_snapshot(
                root, "Fixture", graph
            )
            plan = plan_obligation_evidence(
                graph,
                snapshot.available_leaves,
                snapshot.issuances,
                authenticated_authority_sha256s=[authority],
            )
            self.assertEqual(plan.corrupt_leaf_sha256s, (source.leaf_sha256,))
            self.assertEqual(
                plan.corrupt_issuance_sha256s,
                (issuances[1].issuance_sha256,),
            )
            self.assertEqual(plan.unattested_leaf_sha256s, (lean.leaf_sha256,))


if __name__ == "__main__":
    unittest.main()
