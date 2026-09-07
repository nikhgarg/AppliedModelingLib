from __future__ import annotations

import copy
import json
import shutil
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from types import MappingProxyType
from unittest.mock import patch

from scripts import obligation_evidence_store as evidence_store
from scripts.accepted_obligation_graph import (
    AcceptedObligationGraphError,
    build_accepted_obligation_graph,
    validate_accepted_obligation_graph,
)
from scripts.obligation_evidence_graph import validate_obligation_graph
from scripts.obligation_evidence_store import (
    ObligationEvidenceStoreError,
    current_accepted_graph_path,
    load_accepted_obligation_graph,
    load_recorded_current_accepted_obligation_graph,
    store_accepted_obligation_graph,
    store_obligation_leaf,
)
from scripts.portable_evidence_identity import (
    canonical_json_bytes,
    portable_evidence_sha256,
)
from scripts.strict_closeout_authority import (
    CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND,
    CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
    CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
    STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
    CurrentStrictCloseoutAuthority,
    StrictCloseoutAuthority,
)
from scripts.tests.test_obligation_paper_index import PaperObligationIndexTests, sha


HISTORICAL_STRICT_CLOSEOUT_STAGE_NAMES = (
    "source_claim_inventory",
    "source_spec_correspondence",
    "raw_source_record",
    "semantic_materialization",
    "route_schema_preflight",
    "lean_attestation",
    "strict_integration",
    "focused_build",
)


def strict_authority(
    paper: str = "Fixture",
    *,
    engine_tree_sha256: str | None = None,
    context_sha256: str | None = None,
) -> StrictCloseoutAuthority:
    engine = engine_tree_sha256 or sha("4")
    context = context_sha256 or sha("5")
    stages = {
        stage: sha(format(index + 1, "x"))
        for index, stage in enumerate(HISTORICAL_STRICT_CLOSEOUT_STAGE_NAMES)
    }
    material = {
        "schema": STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
        "acceptance_credential": False,
        "authority_kind": "authenticated_frozen_strict_closeout",
        "paper": paper,
        "context_sha256": context,
        "engine_tree_sha256": engine,
        "stage_receipt_sha256s": stages,
    }
    return StrictCloseoutAuthority(
        paper=paper,
        context_sha256=context,
        engine_tree_sha256=engine,
        stage_receipt_sha256s=MappingProxyType(stages),
        authority_sha256=portable_evidence_sha256(material),
    )


def current_strict_authority(
    paper: str = "Fixture",
    *,
    engine_tree_sha256: str | None = None,
) -> CurrentStrictCloseoutAuthority:
    engine = engine_tree_sha256 or sha("4")
    material = {
        "schema": CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
        "acceptance_credential": False,
        "authority_kind": CURRENT_STRICT_CLOSEOUT_AUTHORITY_KIND,
        "paper": paper,
        "engine_tree_sha256": engine,
        "closeout_contract_sha256": CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
    }
    return CurrentStrictCloseoutAuthority(
        paper=paper,
        engine_tree_sha256=engine,
        closeout_contract_sha256=CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
        authority_sha256=portable_evidence_sha256(material),
    )


class AcceptedObligationGraphTests(unittest.TestCase):
    def test_current_runtime_authority_round_trips_in_accepted_root(self) -> None:
        semantic, index, preflight = self.fixture()
        authority = current_strict_authority()
        credential = build_accepted_obligation_graph(
            semantic,
            index,
            preflight=preflight,
            strict_closeout_authority=authority,  # type: ignore[arg-type]
            final_holistic_audit_surface_sha256=sha("6"),
            source_assurance_sha256=sha("7"),
        )
        self.assertEqual(
            credential.closure_leaf.semantic_payload["strict_closeout_authority"],
            authority.projection(),
        )
        self.assertEqual(
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=preflight,
                authenticated_authority_sha256s=[authority.engine_tree_sha256],
            ),
            credential,
        )

    def fixture(self):
        semantic = PaperObligationIndexTests().complete_graph()
        index, preflight = PaperObligationIndexTests().complete_index(semantic)
        return semantic, index, preflight

    def accepted(self, semantic, index, preflight, *, authority=None):
        authority = authority or strict_authority()
        return build_accepted_obligation_graph(
            semantic,
            index,
            preflight=preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=sha("6"),
            source_assurance_sha256=sha("7"),
        )

    def store_current(self, root: Path):
        semantic, index, preflight = self.fixture()
        authority = strict_authority()
        credential = self.accepted(
            semantic, index, preflight, authority=authority
        )
        pointer = store_accepted_obligation_graph(
            root,
            "Fixture",
            index,
            semantic,
            preflight=preflight,
            strict_closeout_authority=authority,
            final_holistic_audit_surface_sha256=sha("6"),
            source_assurance_sha256=sha("7"),
        )
        pack = evidence_store._accepted_graph_pack_path(
            root, "Fixture", credential.graph_sha256
        )
        return credential, preflight, pointer, pack

    def test_graph_is_the_only_accepting_object(self) -> None:
        semantic, index, preflight = self.fixture()
        authority = strict_authority()
        credential = self.accepted(
            semantic, index, preflight, authority=authority
        )
        self.assertTrue(
            credential.accepted_graph.projection()["acceptance_credential"]
        )
        self.assertFalse(semantic.projection()["acceptance_credential"])
        self.assertEqual(
            credential.semantic_graph.graph_sha256,
            semantic.graph_sha256,
        )
        self.assertEqual(
            credential.closure_leaf.semantic_payload["paper_index_sha256"],
            index.index_sha256,
        )
        self.assertEqual(
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=preflight,
                authenticated_authority_sha256s=[authority.engine_tree_sha256],
            ),
            credential,
        )
    def test_wrong_or_unregistered_terminal_authority_fails_closed(self) -> None:
        semantic, index, preflight = self.fixture()
        credential = self.accepted(semantic, index, preflight)
        with self.assertRaisesRegex(
            AcceptedObligationGraphError, "unregistered engine"
        ):
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=preflight,
                authenticated_authority_sha256s=[sha("9")],
            )

    def test_current_builder_requires_and_binds_nominal_strict_authority(self) -> None:
        semantic, index, preflight = self.fixture()
        with self.assertRaisesRegex(
            AcceptedObligationGraphError, "nominal authenticated object"
        ):
            build_accepted_obligation_graph(
                semantic,
                index,
                preflight=preflight,
                strict_closeout_authority={"authority_sha256": sha("4")},  # type: ignore[arg-type]
                final_holistic_audit_surface_sha256=sha("6"),
                source_assurance_sha256=sha("7"),
            )

        first = self.accepted(
            semantic,
            index,
            preflight,
            authority=strict_authority(context_sha256=sha("5")),
        )
        second = self.accepted(
            semantic,
            index,
            preflight,
            authority=strict_authority(context_sha256=sha("9")),
        )
        holistic_changed = build_accepted_obligation_graph(
            semantic,
            index,
            preflight=preflight,
            strict_closeout_authority=strict_authority(context_sha256=sha("5")),
            final_holistic_audit_surface_sha256=sha("a"),
            source_assurance_sha256=sha("7"),
        )
        source_changed = build_accepted_obligation_graph(
            semantic,
            index,
            preflight=preflight,
            strict_closeout_authority=strict_authority(context_sha256=sha("5")),
            final_holistic_audit_surface_sha256=sha("6"),
            source_assurance_sha256=sha("b"),
        )
        self.assertNotEqual(first.graph_sha256, second.graph_sha256)
        self.assertNotEqual(first.graph_sha256, holistic_changed.graph_sha256)
        self.assertNotEqual(first.graph_sha256, source_changed.graph_sha256)
        self.assertEqual(first.semantic_graph.graph_sha256, second.semantic_graph.graph_sha256)
        self.assertEqual(
            first.semantic_graph.graph_sha256,
            holistic_changed.semantic_graph.graph_sha256,
        )
        self.assertEqual(
            first.semantic_graph.graph_sha256,
            source_changed.semantic_graph.graph_sha256,
        )
        self.assertEqual(
            first.closure_leaf.semantic_payload["strict_closeout_authority"][
                "authority_sha256"
            ],
            strict_authority(context_sha256=sha("5")).authority_sha256,
        )

    def test_corrupt_terminal_binding_cannot_reuse_the_graph_digest(self) -> None:
        semantic, index, preflight = self.fixture()
        credential = self.accepted(semantic, index, preflight)
        leaves = {
            digest: copy.deepcopy(leaf.projection())
            for digest, leaf in credential.accepted_graph.leaves.items()
        }
        root = credential.accepted_graph.root_leaf_sha256s[0]
        leaves[root]["semantic_payload"]["paper_index_sha256"] = sha("f")
        with self.assertRaisesRegex(Exception, "identity is corrupt"):
            validate_obligation_graph(
                credential.accepted_graph.projection(), leaves=leaves
            )

    def test_selected_accepted_graph_is_portable_and_round_trips(self) -> None:
        semantic, index, preflight = self.fixture()
        roots = []
        pointers = []
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            for raw in (first, second):
                root = Path(raw)
                roots.append(root)
                (root / "papers" / "Fixture").mkdir(parents=True)
                pointers.append(
                    store_accepted_obligation_graph(
                        root,
                        "Fixture",
                        index,
                        semantic,
                        preflight=preflight,
                        strict_closeout_authority=strict_authority(),
                        final_holistic_audit_surface_sha256=sha("6"),
                        source_assurance_sha256=sha("7"),
                    )
                )
                loaded = load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                )
                self.assertTrue(
                    loaded.accepted_graph.projection()["acceptance_credential"]
                )
            self.assertEqual(pointers[0].read_bytes(), pointers[1].read_bytes())
            self.assertNotIn(str(roots[0]).encode(), pointers[0].read_bytes())

    def test_current_writer_persists_one_packed_credential_not_duplicate_objects(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            credential, preflight, pointer, pack = self.store_current(root)

            self.assertEqual(
                json.loads(pointer.read_text(encoding="utf-8")),
                {"schema": 2, "graph_sha256": credential.graph_sha256},
            )
            self.assertTrue(pack.is_file())
            evidence = root / "papers" / "Fixture" / "audit" / "obligation_evidence"
            self.assertFalse((evidence / "sha256").exists())
            self.assertFalse((evidence / "graphs").exists())
            self.assertFalse((evidence / "paper_indexes").exists())
            self.assertEqual(
                load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                ),
                credential,
            )
            self.assertEqual(
                load_recorded_current_accepted_obligation_graph(
                    root, "Fixture", credential.graph_sha256
                ),
                credential.accepted_graph,
            )

    def test_packed_credential_is_machine_and_path_portable(self) -> None:
        with tempfile.TemporaryDirectory() as first_dir, tempfile.TemporaryDirectory() as second_dir:
            first_root = Path(first_dir)
            second_root = Path(second_dir)
            (first_root / "papers" / "Fixture").mkdir(parents=True)
            credential, preflight, _pointer, first_pack = self.store_current(
                first_root
            )
            shutil.copytree(
                first_root / "papers" / "Fixture",
                second_root / "papers" / "Fixture",
            )
            second_pack = evidence_store._accepted_graph_pack_path(
                second_root, "Fixture", credential.graph_sha256
            )
            self.assertEqual(first_pack.read_bytes(), second_pack.read_bytes())
            self.assertNotIn(str(first_root).encode(), first_pack.read_bytes())
            self.assertEqual(
                load_accepted_obligation_graph(
                    second_root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                ),
                credential,
            )

    def test_every_packed_nested_mutation_or_omission_fails_closed(self) -> None:
        def mutate_leaf_value(value):
            digest = next(iter(value["leaves"]))
            value["leaves"][digest]["contract_sha256"] = sha("f")

        def miskey_leaf(value):
            digest = next(iter(value["leaves"]))
            value["leaves"][sha("0")] = value["leaves"].pop(digest)

        def remove_leaf(value):
            value["leaves"].pop(next(iter(value["leaves"])))

        def add_leaf(value):
            digest = next(iter(value["leaves"]))
            value["leaves"][sha("0")] = copy.deepcopy(value["leaves"][digest])

        def corrupt_graph_identity(value):
            value["accepted_graph"]["graph_sha256"] = sha("f")

        def change_paper(value):
            value["paper"] = "Other"

        def corrupt_index(value):
            value["paper_index"]["source_inventory_sha256"] = sha("f")

        mutations = {
            "leaf value": mutate_leaf_value,
            "leaf key": miskey_leaf,
            "missing leaf": remove_leaf,
            "extra leaf": add_leaf,
            "graph identity": corrupt_graph_identity,
            "paper": change_paper,
            "paper index": corrupt_index,
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            _credential, preflight, _pointer, pack = self.store_current(root)
            original = pack.read_bytes()
            for label, mutate in mutations.items():
                with self.subTest(label=label):
                    value = json.loads(original)
                    mutate(value)
                    pack.write_bytes(
                        canonical_json_bytes(value) + b"\n"
                    )
                    with self.assertRaises(ObligationEvidenceStoreError):
                        load_accepted_obligation_graph(
                            root,
                            "Fixture",
                            preflight=preflight,
                            authenticated_authority_sha256s=[sha("4")],
                        )
                    pack.write_bytes(original)

            # Semantically identical but noncanonical bytes are also rejected.
            pack.write_text(
                json.dumps(json.loads(original), indent=2) + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ObligationEvidenceStoreError, "not canonical JSON"
            ):
                load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                )

    def test_pointer_and_packed_object_disagreement_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            _credential, preflight, pointer, _pack = self.store_current(root)
            pointer.write_bytes(
                canonical_json_bytes(
                    {"schema": 2, "graph_sha256": sha("f")}
                )
                + b"\n"
            )
            with self.assertRaisesRegex(
                ObligationEvidenceStoreError,
                "packed accepted obligation graph is unavailable",
            ):
                load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                )

    def test_historical_directory_credential_remains_readable(self) -> None:
        semantic, index, preflight = self.fixture()
        credential = self.accepted(semantic, index, preflight)
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            for digest in credential.accepted_graph.topological_leaf_sha256s:
                store_obligation_leaf(
                    root, "Fixture", credential.accepted_graph.leaves[digest]
                )
            evidence_store._store_immutable_object(
                evidence_store._graph_object_path(
                    root, "Fixture", credential.graph_sha256
                ),
                credential.accepted_graph.projection(),
                "historical accepted obligation graph",
            )
            evidence_store._store_immutable_object(
                evidence_store._paper_index_path(
                    root, "Fixture", index.index_sha256
                ),
                index.projection(),
                "historical paper obligation index",
            )
            evidence_store._atomic_write(
                current_accepted_graph_path(root, "Fixture"),
                canonical_json_bytes(
                    {"schema": 1, "graph_sha256": credential.graph_sha256}
                )
                + b"\n",
            )
            self.assertEqual(
                load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                ),
                credential,
            )

    def test_aggregate_projection_drift_requires_explicit_terminal_lane(self) -> None:
        semantic, index, preflight = self.fixture()
        credential = self.accepted(semantic, index, preflight)
        drifted = replace(
            preflight,
            source_inventory_sha256=sha("a"),
            route_schema_sha256=sha("b"),
            structural_preflight_sha256=sha("c"),
        )
        with self.assertRaisesRegex(
            AcceptedObligationGraphError,
            "disagrees with current source_inventory_sha256",
        ):
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=drifted,
                authenticated_authority_sha256s=[sha("4")],
            )
        self.assertEqual(
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=drifted,
                authenticated_authority_sha256s=[sha("4")],
                require_current_aggregate_identity=False,
            ),
            credential,
        )

    def test_source_item_key_rename_preserves_navigation_free_acceptance(self) -> None:
        semantic, index, preflight = self.fixture()
        credential = self.accepted(semantic, index, preflight)
        renamed = replace(
            preflight,
            source_inventory_sha256=sha("a"),
            route_schema_sha256=sha("b"),
            structural_preflight_sha256=sha("c"),
            route_obligation_counts={
                "renamed-claim": dict(preflight.route_obligation_counts["claim"])
            },
            route_source_quote_sha256s={
                "renamed-claim": preflight.route_source_quote_sha256s["claim"]
            },
        )
        self.assertEqual(
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=renamed,
                authenticated_authority_sha256s=[sha("4")],
                require_current_aggregate_identity=False,
            ),
            credential,
        )
        changed_source = replace(
            renamed,
            route_source_quote_sha256s={"renamed-claim": (sha("9"),)},
        )
        with self.assertRaisesRegex(
            AcceptedObligationGraphError,
            "semantic route bindings disagree",
        ):
            validate_accepted_obligation_graph(
                credential.accepted_graph,
                index,
                preflight=changed_source,
                authenticated_authority_sha256s=[sha("4")],
                require_current_aggregate_identity=False,
            )

    def test_interrupted_graph_republication_preserves_prior_selection(self) -> None:
        semantic, index, preflight = self.fixture()
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            store_accepted_obligation_graph(
                root,
                "Fixture",
                index,
                semantic,
                preflight=preflight,
                strict_closeout_authority=strict_authority(),
                final_holistic_audit_surface_sha256=sha("6"),
                source_assurance_sha256=sha("7"),
            )
            prior = load_accepted_obligation_graph(
                root,
                "Fixture",
                preflight=preflight,
                authenticated_authority_sha256s=[sha("4")],
            )
            original_atomic_write = evidence_store._atomic_write

            def fail_pointer(path, payload):
                if path == current_accepted_graph_path(root, "Fixture"):
                    raise OSError("simulated interruption before graph selection")
                return original_atomic_write(path, payload)

            with patch.object(
                evidence_store, "_atomic_write", side_effect=fail_pointer
            ), self.assertRaisesRegex(OSError, "simulated interruption"):
                store_accepted_obligation_graph(
                    root,
                    "Fixture",
                    index,
                    semantic,
                    preflight=preflight,
                    strict_closeout_authority=strict_authority(
                        engine_tree_sha256=sha("5")
                    ),
                    final_holistic_audit_surface_sha256=sha("6"),
                    source_assurance_sha256=sha("7"),
                )
            self.assertEqual(
                load_accepted_obligation_graph(
                    root,
                    "Fixture",
                    preflight=preflight,
                    authenticated_authority_sha256s=[sha("4")],
                ),
                prior,
            )


if __name__ == "__main__":
    unittest.main()
