#!/usr/bin/env python3
"""Regressions for the isolated current-v11 graph-carrier contract."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from dataclasses import dataclass
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import lean_review_surface
from scripts import lean_signature_manifest
from scripts.current_closeout import lean_review_graph as contract
from scripts.current_closeout.realization import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
    V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA,
)
from scripts.obligation_routes import EvidenceRouteSet


@dataclass(frozen=True)
class _Snapshot:
    path: Path
    sha256: str | None
    raw_bytes: bytes | None


class _Context:
    def __init__(self, root: Path, *, raw_bytes: bytes = b"closure\n") -> None:
        self.folder = root / "papers" / "Fixture"
        self.path = self.folder / "audit" / "LEAN_IMPORT_CLOSURE_RECEIPT.json"
        self.source_semantic_lane = V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE
        self.statement_map = {"items": {}}
        self.v11_lean_review_graph_payload = None
        self.issued_by_builder = False
        self.surface = None
        self.payload = {"schema": 1}
        self.frozen_bytes: dict[Path, bytes | None] = {}
        self.snapshot = _Snapshot(
            path=self.path,
            sha256=contract.stable_json_sha256(raw_bytes.decode("utf-8")),
            raw_bytes=raw_bytes,
        )

    def canonical_sidecar_path(self, _basename: str) -> Path:
        return self.path

    def json_snapshot(self, path: Path) -> _Snapshot | None:
        return self.snapshot if path == self.path else None

    def json_payload(self, path: Path) -> dict[str, object] | None:
        return self.payload if path == self.path else None

    def file_bytes_override(self) -> dict[Path, bytes | None]:
        return dict(self.frozen_bytes)

    def retained_v11_review_surface(self) -> object | None:
        return self.surface


class CurrentV11GraphContractTests(unittest.TestCase):
    ENGINE = {
        "schema": 1,
        "sources": [],
        "semantic_hash_tool_identity": {"schema": 1, "sha256": "a" * 64},
    }

    @staticmethod
    def _route_set() -> EvidenceRouteSet:
        return EvidenceRouteSet.from_source_map(
            {
                "items": {
                    "model": {
                        "claim_bearing": True,
                        "source_kind": "definition",
                        "inventory_role": "source_semantic_declaration",
                        "lean_declarations": ["Fixture.Model"],
                    },
                    "theorem": {
                        "claim_bearing": True,
                        "source_kind": "theorem",
                        "inventory_role": "named_result",
                        "semantic_contract": {
                            "spec_declaration": "Fixture.TheoremSpec",
                            "evidence_declaration": "Fixture.theoremProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    },
                    "algorithm": {
                        "claim_bearing": True,
                        "source_kind": "algorithm",
                        "inventory_role": "named_result",
                        "semantic_contract": {
                            "spec_declaration": "Fixture.AlgorithmSpec",
                            "evidence_declaration": "Fixture.algorithmRealizes",
                            "evidence_mode": "definitionally_realizes",
                            "semantic_shape": "plain",
                        },
                        "semantic_review_target": {
                            "schema": 1,
                            "kind": "definition_declaration",
                            "declaration": "Fixture.Algorithm",
                        },
                    },
                    "defect": {
                        "claim_bearing": False,
                        "source_kind": "claim",
                        "inventory_role": "quarantined_source_defect",
                        "support_lean_declarations": ["Fixture.DefectWitness"],
                    },
                }
            }
        )

    def test_request_plan_is_one_typed_source_for_lean_and_carrier(self) -> None:
        closure = {"schema": 1, "entry_module": "Fixture.ProofInterface"}
        plan = contract.build_graph_request_plan(
            self._route_set(),
            ["Fixture.TheoremSpec", "Fixture.AlgorithmSpec"],
            entry_module="Fixture.ProofInterface",
            paper_modules=["Fixture.PaperInterface", "Fixture.ProofInterface"],
            workspace_modules=[
                "AppliedModelingLib.Foundation",
                "Fixture.PaperInterface",
                "Fixture.ProofInterface",
            ],
            lean_import_closure=closure,
        )

        self.assertEqual(
            plan.specifications,
            ("Fixture.AlgorithmSpec", "Fixture.TheoremSpec"),
        )
        self.assertEqual(
            plan.semantic_declarations,
            frozenset({"Fixture.Algorithm", "Fixture.Model"}),
        )
        self.assertEqual(
            plan.quarantined_support_declarations,
            frozenset({"Fixture.DefectWitness"}),
        )
        self.assertEqual(
            plan.semantic_review_claim_declarations,
            frozenset({"Fixture.Algorithm", "Fixture.TheoremSpec"}),
        )
        request = dict(plan.request_projection())
        self.assertEqual(
            request["specification_names"],
            list(plan.specifications),
        )
        self.assertEqual(
            request["semantic_declaration_names"],
            sorted(plan.semantic_declarations),
        )
        self.assertEqual(
            request["quarantined_support_declaration_names"],
            ["Fixture.DefectWitness"],
        )
        self.assertEqual(
            request["axiom_root_names"],
            sorted(plan.semantic_declarations | {"Fixture.DefectWitness"}),
        )
        self.assertEqual(
            request["semantic_contracts"],
            [
                {
                    "specification": specification,
                    "evidence": evidence,
                    "mode": mode,
                }
                for specification, evidence, mode in sorted(
                    plan.semantic_contracts
                )
            ],
        )
        self.assertEqual(
            request["lean_import_closure_sha256"],
            contract.stable_json_sha256(closure),
        )
        self.assertEqual(
            request["semantic_manifest_modules"],
            list(plan.workspace_modules),
        )

        # Each projection is rebuilt from immutable typed fields; mutating one
        # caller's JSON transport cannot alter the plan used for Lean.
        request["specification_names"].append("Fixture.ForeignSpec")
        self.assertEqual(
            dict(plan.request_projection())["specification_names"],
            ["Fixture.AlgorithmSpec", "Fixture.TheoremSpec"],
        )

    def test_request_plan_rejects_topology_or_route_skew(self) -> None:
        with self.assertRaisesRegex(ValueError, "absent from the workspace"):
            contract.build_graph_request_plan(
                self._route_set(),
                ["Fixture.TheoremSpec"],
                entry_module="Fixture.ProofInterface",
                paper_modules=["Fixture.PaperInterface"],
                workspace_modules=["Fixture.ProofInterface"],
                lean_import_closure={"schema": 1},
            )

    def test_one_acquisition_function_owns_every_native_graph_argument(self) -> None:
        root = Path("/repo")
        folder = root / "papers" / "Fixture"
        module_sources = {
            "Fixture.PaperInterface": (
                folder / "PaperInterface.lean",
                b"def placeholder := True\n",
            )
        }
        plan = contract.build_graph_request_plan(
            self._route_set(),
            ["Fixture.AlgorithmSpec", "Fixture.TheoremSpec"],
            entry_module="Fixture.PaperInterface",
            paper_modules=module_sources,
            workspace_modules=module_sources,
            lean_import_closure={"schema": 1},
        )
        inventory = {"schema": 1, "declarations": []}
        projection = SimpleNamespace(semantic_targets={})
        provider = object()
        with (
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_declaration_inventory",
                return_value=inventory,
            ) as acquire,
            mock.patch.object(
                contract,
                "project_validated_graph_inventory",
                return_value=projection,
            ) as project,
        ):
            result = contract.acquire_validated_graph_projection(
                root,
                folder,
                plan,
                module_sources=module_sources,
                build_input_provider=provider,
                additional_axiom_root_names={"Fixture.Assumption"},
                root_semantic_manifest_declaration_names={"Fixture.Assumption"},
            )
        self.assertTrue(result.acquired_fresh)
        self.assertIs(result.inventory, inventory)
        self.assertIs(result.projection, projection)
        kwargs = acquire.call_args.kwargs
        self.assertEqual(kwargs["specification_names"], plan.specifications)
        self.assertEqual(
            kwargs["semantic_review_claim_declaration_names"],
            plan.semantic_review_claim_declarations,
        )
        self.assertEqual(
            kwargs["axiom_root_names"],
            plan.semantic_declarations
            | plan.quarantined_support_declarations
            | {"Fixture.Assumption"},
        )
        self.assertEqual(
            kwargs["root_semantic_manifest_declaration_names"],
            frozenset({"Fixture.Assumption"}),
        )
        self.assertEqual(
            kwargs["semantic_manifest_modules"],
            plan.workspace_modules,
        )
        self.assertEqual(
            kwargs["timeout_seconds"],
            contract.V11_LEAN_DECLARATION_GRAPH_TIMEOUT_SECONDS,
        )
        self.assertEqual(kwargs["timeout_seconds"], 900)
        project.assert_called_once_with(
            root,
            folder,
            plan,
            inventory=inventory,
            module_sources=module_sources,
        )

        with (
            mock.patch.object(
                lean_signature_manifest,
                "run_lean_declaration_inventory",
                side_effect=AssertionError("Lean graph was reacquired"),
            ) as reacquire,
            mock.patch.object(
                contract,
                "project_validated_graph_inventory",
                return_value=projection,
            ),
        ):
            reused = contract.acquire_validated_graph_projection(
                root,
                folder,
                plan,
                module_sources=module_sources,
                inventory=inventory,
            )
        self.assertFalse(reused.acquired_fresh)
        reacquire.assert_not_called()

    def test_current_service_owns_the_frozen_v11_graph_input_transaction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            context = _Context(root)
            context.issued_by_builder = True
            context.status_payload = {
                "review_surface": {
                    "assumption_names": ["Fixture.RequiredAssumption"]
                }
            }
            context.statement_map = {
                "items": {
                    "claim": {
                        "claim_bearing": True,
                        "source_kind": "theorem",
                        "inventory_role": "named_result",
                        "semantic_contract": {
                            "spec_declaration": "Fixture.claimSpec",
                            "evidence_declaration": "Fixture.claimProof",
                            "evidence_mode": "proves",
                            "semantic_shape": "plain",
                        },
                    }
                }
            }
            interface = context.folder / "PaperInterface.lean"
            interface_bytes = b"def claimSpec : Prop := True\n"
            provider = SimpleNamespace(
                repository_source_snapshot=mock.Mock(
                    return_value=(
                        (
                            "Fixture.PaperInterface",
                            interface,
                            interface_bytes,
                            "a" * 64,
                        ),
                    )
                )
            )
            projection = SimpleNamespace(semantic_targets={})

            def acquire(
                _root: Path,
                _folder: Path,
                request: object,
                **_kwargs: object,
            ) -> contract.V11LeanReviewGraphAcquisition:
                return contract.V11LeanReviewGraphAcquisition(
                    inventory={"schema": 1},
                    projection=projection,
                    acquired_fresh=True,
                )

            with (
                mock.patch(
                    "scripts.lean_import_closure.validated_lean_import_closure_receipt_payload",
                    return_value={
                        "lean_import_closure": {
                            "entry_module": "Fixture.PaperInterface"
                        }
                    },
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ) as provider_factory,
                mock.patch.object(
                    contract,
                    "validated_graph_carrier_inventory",
                    return_value=None,
                ),
                mock.patch.object(
                    contract,
                    "acquire_validated_graph_projection",
                    side_effect=acquire,
                ) as graph_acquire,
            ):
                material = contract.build_v11_lean_review_graph_material(
                    root,
                    context.folder,
                    ["Fixture.claimSpec"],
                    context=context,
                )

            provider_factory.assert_called_once_with(
                root.resolve(),
                lean_import_closure_payload={
                    "entry_module": "Fixture.PaperInterface"
                },
            )
            provider.repository_source_snapshot.assert_called_once_with(
                "Fixture.PaperInterface"
            )
            self.assertEqual(
                material.request_plan.paper_modules,
                ("Fixture.PaperInterface",),
            )
            self.assertFalse(material.carrier_reused)
            self.assertIs(material.acquisition.projection, projection)
            self.assertEqual(
                material.module_sources["Fixture.PaperInterface"],
                (interface.resolve(), interface_bytes),
            )
            graph_acquire.assert_called_once()
            self.assertEqual(
                material.graph_request[
                    "root_semantic_manifest_declaration_names"
                ],
                ["Fixture.RequiredAssumption"],
            )
            graph_kwargs = graph_acquire.call_args.kwargs
            self.assertEqual(
                graph_kwargs["additional_axiom_root_names"],
                frozenset({"Fixture.RequiredAssumption"}),
            )
            self.assertEqual(
                graph_kwargs["root_semantic_manifest_declaration_names"],
                frozenset({"Fixture.RequiredAssumption"}),
            )

            context.frozen_bytes = {interface.resolve(): b"changed\n"}
            with (
                mock.patch(
                    "scripts.lean_import_closure.validated_lean_import_closure_receipt_payload",
                    return_value={
                        "lean_import_closure": {
                            "entry_module": "Fixture.PaperInterface"
                        }
                    },
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    contract,
                    "validated_graph_carrier_inventory",
                    return_value=None,
                ),
                mock.patch.object(
                    contract,
                    "acquire_validated_graph_projection",
                    side_effect=acquire,
                ),
            ):
                with self.assertRaisesRegex(
                    ValueError,
                    "evidence snapshots disagree",
                ):
                    contract.build_v11_lean_review_graph_material(
                        root,
                        context.folder,
                        ["Fixture.claimSpec"],
                        context=context,
                    )

    def test_short_status_assumption_roots_are_qualified_by_entry_module(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            context = _Context(Path(temporary))
            context.status_payload = {
                "review_surface": {
                    "assumption_names": [
                        "shortAssumption",
                        "Fixture.AlreadyQualified",
                    ]
                }
            }
            self.assertEqual(
                contract._configured_assumption_root_names(
                    context,
                    entry_module="Fixture.ProofInterface",
                ),
                frozenset(
                    {
                        "Fixture.shortAssumption",
                        "Fixture.AlreadyQualified",
                    }
                ),
            )
            self.assertEqual(
                contract._configured_assumption_root_names(
                    context,
                    entry_module="Fixture",
                ),
                frozenset(
                    {
                        "Fixture.shortAssumption",
                        "Fixture.AlreadyQualified",
                    }
                ),
            )

    def test_inventory_projection_uses_only_lean_owned_surfaces(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary).resolve()
            folder = root / "papers" / "Fixture"
            interface = (folder / "PaperInterface.lean").resolve()
            interface.parent.mkdir(parents=True)
            interface_bytes = b"namespace Fixture\ndef Model := Nat\nend Fixture\n"
            plan = contract.build_graph_request_plan(
                self._route_set(),
                ["Fixture.TheoremSpec", "Fixture.AlgorithmSpec"],
                entry_module="Fixture.ProofInterface",
                paper_modules=["Fixture.PaperInterface"],
                workspace_modules=["Fixture.PaperInterface"],
                lean_import_closure={"schema": 1},
            )
            module_sources = {
                "Fixture.PaperInterface": (interface, interface_bytes)
            }
            claim_surface = {
                "manifest_sha256": "a" * 64,
                "claim_atoms_sha256": "b" * 64,
                "claim_atoms": [{"kind": "constant", "name": "Nat"}],
            }
            definition_target = {
                "display": "def Algorithm : Nat := 1",
                "display_sha256": "c" * 64,
                "root_expanded": True,
                "direct_paper_declarations": ("Fixture.Model",),
                "direct_library_declarations": (),
            }
            model_target = {
                "display": "def Model := Nat",
                "display_sha256": "d" * 64,
                "root_expanded": True,
                "direct_paper_declarations": (),
                "direct_library_declarations": (),
            }
            spec_target = {
                "display": "def TheoremSpec : Prop := True",
                "display_sha256": "e" * 64,
                "root_expanded": True,
                "expanded_declarations": ("Fixture.TheoremSpec",),
                "prerequisite_declarations": ("Fixture.Model",),
                "library_declarations": (),
            }
            review_surface = SimpleNamespace(
                specifications={
                    "Fixture.AlgorithmSpec": {
                        **spec_target,
                        "display": "def AlgorithmSpec : Prop := True",
                    },
                    "Fixture.TheoremSpec": spec_target,
                },
                paper_declarations={
                    "Fixture.Algorithm": definition_target,
                    "Fixture.Model": model_target,
                },
                library_declarations={},
            )
            signatures = {
                "Fixture.Algorithm": "1" * 64,
                "Fixture.Model": "2" * 64,
                "Fixture.TheoremSpec": "3" * 64,
            }
            source_records = {
                name: {
                    "source_path": interface,
                    "source_range": {
                        "line_start": index,
                        "line_end": index,
                    },
                    "source": f"def {name.rsplit('.', 1)[-1]} := True",
                    "source_sha256": str(index) * 64,
                    "declaration_kind": "definition",
                }
                for index, name in enumerate(
                    (
                        "Fixture.Algorithm",
                        "Fixture.AlgorithmSpec",
                        "Fixture.Model",
                        "Fixture.TheoremSpec",
                    ),
                    start=1,
                )
            }
            contract_rows = {
                row: {"specification": row[0], "passes": True}
                for row in plan.semantic_contracts
            }

            with (
                mock.patch.object(
                    lean_signature_manifest,
                    "foundation_frontier_preview_from_inventory",
                    return_value={
                        "summary": {"unregistered_external_root_count": 0}
                    },
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "semantic_review_claim_surfaces_from_inventory",
                    return_value={
                        "Fixture.Algorithm": dict(claim_surface),
                        "Fixture.TheoremSpec": dict(claim_surface),
                    },
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "passing_semantic_contract_rows_from_inventory",
                    return_value=contract_rows,
                ),
                mock.patch.object(
                    lean_review_surface,
                    "lean_owned_semantic_review_display_surface_from_inventory",
                    return_value=review_surface,
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "semantic_signature_sha256s_from_inventory",
                    return_value=signatures,
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "lean_inventory_source_declaration_records",
                    return_value=source_records,
                ),
                mock.patch.object(
                    lean_signature_manifest,
                    "lean_inventory_library_source_declaration_records",
                    return_value={},
                ),
            ):
                projection = contract.project_validated_graph_inventory(
                    root,
                    folder,
                    plan,
                    inventory={"schema": 1, "declarations": []},
                    module_sources=module_sources,
                )

        algorithm = projection.semantic_targets["Fixture.AlgorithmSpec"]
        theorem = projection.semantic_targets["Fixture.TheoremSpec"]
        self.assertEqual(algorithm["display"], definition_target["display"])
        self.assertEqual(
            algorithm["semantic_review_declaration"],
            "Fixture.Algorithm",
        )
        self.assertEqual(theorem["display"], spec_target["display"])
        self.assertEqual(
            theorem["semantic_review_declaration"],
            "Fixture.TheoremSpec",
        )
        self.assertEqual(set(projection.semantic_contracts), set(contract_rows))
        self.assertEqual(
            projection.paper_declaration_sources["Fixture.Model"][
                "paper_source_path"
            ],
            "papers/Fixture/PaperInterface.lean",
        )
        with self.assertRaisesRegex(ValueError, "lacks typed routes"):
            contract.build_graph_request_plan(
                self._route_set(),
                ["Fixture.MissingSpec"],
                entry_module="Fixture.ProofInterface",
                paper_modules=["Fixture.PaperInterface"],
                workspace_modules=["Fixture.PaperInterface"],
                lean_import_closure={"schema": 1},
            )

    def test_current_graph_services_do_not_load_legacy_authorities(self) -> None:
        script = """
import json
import sys
import scripts.current_closeout.graph_preparation
import scripts.current_closeout.lean_review_graph
import scripts.current_closeout.review_surface
import scripts.immutable_json
blocked = sorted(
    name for name in sys.modules
    if name in {
        'scripts.audit_evidence_integrity',
        'audit_evidence_integrity',
        'scripts.legacy_source_record_authorities',
        'scripts.legacy_source_record_boundary',
        'scripts.review_dashboard',
        'scripts.review_dashboard_packet',
    }
)
print(json.dumps(blocked))
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertEqual(json.loads(result.stdout), [])

    def test_context_identity_is_checkout_path_independent(self) -> None:
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            first_context = _Context(Path(first))
            second_context = _Context(Path(second))
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                first_digest = contract.graph_context_input_sha256(
                    first_context,
                    repository_root=Path(first),
                )
                second_digest = contract.graph_context_input_sha256(
                    second_context,
                    repository_root=Path(second),
                )
            self.assertEqual(first_digest, second_digest)

    def test_changed_closure_bytes_change_context_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            first_context = _Context(root, raw_bytes=b"first\n")
            second_context = _Context(root, raw_bytes=b"second\n")
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                first_digest = contract.graph_context_input_sha256(
                    first_context,
                    repository_root=root,
                )
                second_digest = contract.graph_context_input_sha256(
                    second_context,
                    repository_root=root,
                )
            self.assertNotEqual(first_digest, second_digest)

    def test_terminal_graph_identity_is_checkout_path_independent(self) -> None:
        request = {
            "schema": 5,
            "workspace_modules": ["Fixture.PaperInterface"],
            "specification_names": ["Fixture.claimSpec"],
        }
        content = b"def claimSpec : Prop := True\n"
        with tempfile.TemporaryDirectory() as first, tempfile.TemporaryDirectory() as second:
            first_root = Path(first)
            second_root = Path(second)
            first_folder = first_root / "papers" / "Fixture"
            second_folder = second_root / "papers" / "Fixture"
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                first_digest = contract.terminal_graph_input_sha256(
                    first_root,
                    first_folder,
                    graph_request=request,
                    module_sources={
                        "Fixture.PaperInterface": (
                            first_folder / "PaperInterface.lean",
                            content,
                        )
                    },
                )
                second_digest = contract.terminal_graph_input_sha256(
                    second_root,
                    second_folder,
                    graph_request=request,
                    module_sources={
                        "Fixture.PaperInterface": (
                            second_folder / "PaperInterface.lean",
                            content,
                        )
                    },
                )
            self.assertEqual(first_digest, second_digest)

    def test_terminal_graph_checkpoint_reuses_only_exact_current_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            path = folder / "PaperInterface.lean"
            request = {
                "schema": 5,
                "workspace_modules": ["Fixture.PaperInterface"],
                "specification_names": ["Fixture.claimSpec"],
            }
            sources = {
                "Fixture.PaperInterface": (
                    path,
                    b"def claimSpec : Prop := True\n",
                )
            }
            inventory = {"schema": 1, "declarations": [{"name": "claimSpec"}]}
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                reference = contract.checkpoint_terminal_lean_graph(
                    root,
                    folder,
                    graph_request=request,
                    module_sources=sources,
                    inventory=inventory,
                )
                reused = contract.current_terminal_lean_graph_inventory(
                    root,
                    folder,
                    graph_request=request,
                    module_sources=sources,
                )
                changed = contract.current_terminal_lean_graph_inventory(
                    root,
                    folder,
                    graph_request=request,
                    module_sources={
                        "Fixture.PaperInterface": (
                            path,
                            b"def claimSpec : Prop := False\n",
                        )
                    },
                )
            self.assertFalse(reference["acceptance_credential"])
            self.assertEqual(reused, inventory)
            self.assertIsNone(changed)

    def test_carrier_requires_exact_request_and_integrity(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            context = _Context(root)
            request = {"schema": 1, "specification_names": ["Fixture.claimSpec"]}
            inventory = {"schema": 1, "declarations": []}
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                context_digest = contract.graph_context_input_sha256(
                    context,
                    repository_root=root,
                )
                material = {
                    "schema": V11_LEAN_REVIEW_GRAPH_CARRIER_SCHEMA,
                    "acceptance_credential": False,
                    "operational_scheduling_only": True,
                    "paper": "Fixture",
                    "source_semantic_lane": V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
                    "context_input_sha256": context_digest,
                    "graph_request": request,
                    "inventory": inventory,
                    "inventory_sha256": contract.stable_json_sha256(inventory),
                }
                context.v11_lean_review_graph_payload = {
                    **material,
                    "receipt_integrity_sha256": contract.stable_json_sha256(material),
                }
                self.assertEqual(
                    contract.validated_graph_carrier_inventory(
                        context.folder,
                        context,
                        graph_request=request,
                        repository_root=root,
                    ),
                    inventory,
                )
                with self.assertRaisesRegex(
                    contract.V11LeanReviewGraphCarrierMismatch,
                    "current frozen inputs",
                ):
                    contract.validated_graph_carrier_inventory(
                        context.folder,
                        context,
                        graph_request={**request, "specification_names": ["Other"]},
                        repository_root=root,
                    )

    def test_operational_carrier_requires_one_builder_retained_surface(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            context = _Context(root)
            context.surface = SimpleNamespace(
                graph_request={"schema": 5},
                declaration_inventory={"schema": 1},
                build_input_provider=object(),
                semantic_targets={},
                paper_semantic_targets={},
                library_semantic_targets={},
                library_declaration_sources={},
            )
            with mock.patch.object(
                contract,
                "graph_engine_projection",
                return_value=self.ENGINE,
            ):
                self.assertIsNone(
                    contract.builder_issued_v11_lean_review_graph_carrier(
                        context.folder,
                        context,
                        repository_root=root,
                    )
                )
                context.issued_by_builder = True
                carrier = contract.builder_issued_v11_lean_review_graph_carrier(
                    context.folder,
                    context,
                    repository_root=root,
                )
            assert carrier is not None
            self.assertFalse(carrier["acceptance_credential"])
            self.assertEqual(carrier["graph_request"], {"schema": 5})
            self.assertEqual(carrier["inventory"], {"schema": 1})


if __name__ == "__main__":
    unittest.main()
