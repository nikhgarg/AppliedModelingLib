from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.closeout_pipeline import (
    CloseoutPipelineError,
    CloseoutStage,
    EvidenceRouteSet,
    RouteKind,
    SemanticReviewTargetKind,
    build_closeout_context,
    current_stage_receipts,
    issue_observed_stage_prefix,
    stage_dag_projection,
)
from scripts.closeout_status_projection import paper_status_acceptance_projection


def anchor(text: str = "Source statement.") -> list[dict[str, object]]:
    return [
        {
            "path": "source.txt",
            "line_start": 1,
            "line_end": 1,
            "quoted_text": text,
            "quoted_text_sha256": hashlib.sha256(text.encode()).hexdigest(),
        }
    ]


def contract(spec: str, endpoint: str, mode: str = "proves") -> dict[str, str]:
    return {
        "spec_declaration": spec,
        "evidence_declaration": endpoint,
        "evidence_mode": mode,
        "semantic_shape": "plain",
    }


class TypedEvidenceRouteTests(unittest.TestCase):
    def test_supported_route_architectures_share_one_parser(self) -> None:
        source_map = {
            "items": {
                "same_file": {
                    "claim_bearing": True,
                    "semantic_contract": contract(
                        "Fixture.PaperInterface.sameSpec",
                        "Fixture.PaperInterface.sameProof",
                    ),
                    "source_anchor_evidence": anchor("Same-file result."),
                },
                "cross_file": {
                    "claim_bearing": True,
                    "semantic_contract": contract(
                        "Fixture.PaperInterface.crossSpec",
                        "Fixture.ProofInterface.crossProof",
                    ),
                    "source_anchor_evidence": anchor("Cross-file result."),
                },
                "assumption_parent": {
                    "claim_bearing": True,
                    "inventory_role": "source_premise_declaration",
                    "lean_declarations": ["Fixture.Assumptions.sourcePremise"],
                    "source_anchor_evidence": anchor("Source premise."),
                },
                "library_route": {
                    "claim_bearing": True,
                    "semantic_contract": contract(
                        "AppliedModelingLib.FairDivision.librarySpec",
                        "AppliedModelingLib.FairDivision.libraryProof",
                        "definitionally_realizes",
                    ),
                    "source_anchor_evidence": anchor("Reusable definition."),
                },
                "paper_definition_route": {
                    "claim_bearing": True,
                    "semantic_contract": contract(
                        "Fixture.PaperInterface.definitionSpec",
                        "Fixture.PaperInterface.definitionProof",
                        "definitionally_realizes",
                    ),
                    "semantic_review_target": {
                        "schema": 1,
                        "kind": "definition_declaration",
                        "declaration": "Fixture.PaperInterface.paperPredicate",
                    },
                    "source_anchor_evidence": anchor("Paper predicate definition."),
                },
                "convention": {
                    "claim_bearing": True,
                    "model_convention_ids": ["FIXTURE-CONVENTION-01"],
                    "source_anchor_evidence": anchor("Calendar-time convention."),
                },
                "proof_support": {
                    "claim_bearing": False,
                    "inventory_role": "proof_support",
                    "support_lean_declarations": ["Fixture.ProofBridge.supportLemma"],
                },
                "alias": {
                    "claim_bearing": True,
                    "inventory_role": "source_presentation_alias",
                },
            }
        }
        routes = EvidenceRouteSet.from_source_map(
            source_map
        )
        by_id = {route.source_item_id: route for route in routes.routes}
        self.assertEqual(by_id["same_file"].route_kind, RouteKind.RESULT_SEMANTIC)
        self.assertEqual(by_id["cross_file"].route_kind, RouteKind.RESULT_SEMANTIC)
        self.assertEqual(
            by_id["assumption_parent"].route_kind, RouteKind.SOURCE_ASSUMPTION
        )
        self.assertEqual(by_id["library_route"].route_kind, RouteKind.RESULT_SEMANTIC)
        self.assertEqual(
            by_id["paper_definition_route"].semantic_review_target_kind.value,
            "definition_declaration",
        )
        self.assertEqual(
            by_id["paper_definition_route"].semantic_review_declaration,
            "Fixture.PaperInterface.paperPredicate",
        )
        self.assertEqual(by_id["convention"].route_kind, RouteKind.SOURCE_CONVENTION)
        self.assertEqual(by_id["proof_support"].route_kind, RouteKind.PROOF_SUPPORT)
        self.assertEqual(
            by_id["alias"].route_kind, RouteKind.SOURCE_PRESENTATION_ALIAS
        )

    def test_semantic_contract_never_accepts_an_alias_equivalence_shape(self) -> None:
        malformed = {
            "items": {
                "claim": {
                    "semantic_contract": {
                        **contract("Fixture.claimSpec", "Fixture.claimProof"),
                        "alias_declaration": "Fixture.alias",
                    }
                }
            }
        }
        with self.assertRaises(CloseoutPipelineError):
            EvidenceRouteSet.from_source_map(malformed)

    def test_definition_review_target_can_use_a_direct_spec_proof(self) -> None:
        source_map = {
            "items": {
                "definition": {
                    "semantic_contract": contract(
                        "Fixture.definitionSpec", "Fixture.definitionProof", "proves"
                    ),
                    "semantic_review_target": {
                        "schema": 1,
                        "kind": "definition_declaration",
                        "declaration": "Fixture.paperPredicate",
                    },
                }
            }
        }
        routes = EvidenceRouteSet.from_source_map(
            source_map
        )
        route = routes.routes[0]
        self.assertEqual(route.evidence_mode, "proves")
        self.assertEqual(
            route.semantic_review_target_kind,
            SemanticReviewTargetKind.DEFINITION_DECLARATION,
        )
        self.assertEqual(
            route.semantic_review_declaration, "Fixture.paperPredicate"
        )

    def test_source_anchor_hash_is_rechecked(self) -> None:
        malformed = {
            "items": {
                "claim": {
                    "semantic_contract": contract(
                        "Fixture.claimSpec", "Fixture.claimProof"
                    ),
                    "source_anchor_evidence": [
                        {
                            "quoted_text": "actual",
                            "quoted_text_sha256": "0" * 64,
                        }
                    ],
                }
            }
        }
        with self.assertRaises(CloseoutPipelineError):
            EvidenceRouteSet.from_source_map(malformed)


class CloseoutStageDagTests(unittest.TestCase):
    def fixture_context(
        self,
        root: Path,
        *,
        engine_tree_sha256: str = "2" * 64,
        engine_revision_sequence: int = 1,
        protocol_projection: object | None = None,
    ):
        folder = root / "papers" / "Fixture23Paper"
        (folder / "audit").mkdir(parents=True, exist_ok=True)
        source_map = {
            "items": {
                "claim": {
                    "semantic_contract": contract(
                        "Fixture23Paper.PaperInterface.claimSpec",
                        "Fixture23Paper.ProofInterface.claimProof",
                    ),
                    "source_anchor_evidence": anchor(),
                }
            }
        }
        map_path = folder / "audit" / "paper_statement_map.json"
        status_path = folder / "status.json"
        map_path.write_text(json.dumps(source_map), encoding="utf-8")
        status_path.write_text('{"status":"formalized"}', encoding="utf-8")
        def identity(path: Path) -> dict[str, object]:
            data = path.read_bytes()
            return {
                "state": "present",
                "sha256": hashlib.sha256(data).hexdigest(),
            }
        receipt = {
            "paper": folder.name,
            "plan_identity_sha256": "1" * 64,
            "content_inputs": {
                "papers/Fixture23Paper/audit/paper_statement_map.json": identity(map_path),
                "papers/Fixture23Paper/status.json": identity(status_path),
            },
            "compiled_inputs": {},
            "strict_closeout_protocol_projection": (
                {"schema": 1}
                if protocol_projection is None
                else protocol_projection
            ),
        }
        context = build_closeout_context(
            root,
            folder,
            plan_receipt=receipt,
            engine_registration={
                "engine_tree_sha256": engine_tree_sha256,
                "revision_sequence": engine_revision_sequence,
            },
            lean_closure_projection={"state": "present", "sha256": "3" * 64},
        )
        return folder, context

    def test_context_identity_excludes_registered_engine_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            _folder, first = self.fixture_context(root)
            _folder, later = self.fixture_context(
                root,
                engine_tree_sha256="4" * 64,
                engine_revision_sequence=37,
            )

            self.assertEqual(first.context_sha256, later.context_sha256)
            self.assertEqual(first.projection(), later.projection())
            self.assertNotIn("engine_tree_sha256", first.projection())
            self.assertNotIn("engine_revision_sequence", first.projection())

            _folder, changed_protocol = self.fixture_context(
                root,
                engine_tree_sha256="4" * 64,
                engine_revision_sequence=37,
                protocol_projection={"schema": 2},
            )
            self.assertNotEqual(first.context_sha256, changed_protocol.context_sha256)

    def test_current_plan_uses_status_projection_without_raw_status_binding(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture23Paper"
            (folder / "audit").mkdir(parents=True)
            source_map = {
                "items": {
                    "claim": {
                        "semantic_contract": contract(
                            "Fixture23Paper.PaperInterface.claimSpec",
                            "Fixture23Paper.ProofInterface.claimProof",
                        ),
                        "source_anchor_evidence": anchor(),
                    }
                }
            }
            map_path = folder / "audit" / "paper_statement_map.json"
            status_path = folder / "status.json"
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            status = {
                "id": folder.name,
                "status": "formalized",
                "paper_interface": {"line_count": 1},
            }
            status_path.write_text(json.dumps(status), encoding="utf-8")
            map_bytes = map_path.read_bytes()
            receipt = {
                "schema": 5,
                "paper": folder.name,
                "plan_identity_sha256": "1" * 64,
                "content_inputs": {
                    "papers/Fixture23Paper/audit/paper_statement_map.json": {
                        "state": "present",
                        "sha256": hashlib.sha256(map_bytes).hexdigest(),
                    }
                },
                "compiled_inputs": {},
                "strict_closeout_protocol_projection": {"schema": 1},
                "target_paper_status_projection": paper_status_acceptance_projection(
                    root, folder.name
                ),
            }

            def context():
                return build_closeout_context(
                    root,
                    folder,
                    plan_receipt=receipt,
                    engine_registration={
                        "engine_tree_sha256": "2" * 64,
                        "revision_sequence": 1,
                    },
                    lean_closure_projection={"state": "present", "sha256": "3" * 64},
                )

            first = context()
            status["paper_interface"] = {"line_count": 999}
            status_path.write_text(json.dumps(status), encoding="utf-8")
            self.assertEqual(first, context())

            status["status"] = "partial"
            status_path.write_text(json.dumps(status), encoding="utf-8")
            with self.assertRaisesRegex(
                CloseoutPipelineError,
                "status acceptance configuration changed",
            ):
                context()

    def test_context_still_requires_valid_registered_engine_provenance(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            with self.assertRaisesRegex(
                CloseoutPipelineError,
                "registered engine tree is not a lowercase SHA-256 digest",
            ):
                self.fixture_context(root, engine_tree_sha256="not-a-digest")
            with self.assertRaisesRegex(
                CloseoutPipelineError,
                "registered engine revision sequence is invalid",
            ):
                self.fixture_context(root, engine_revision_sequence=0)

    def test_stage_prefix_is_content_addressed_and_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder, context = self.fixture_context(root)
            outputs = {
                stage: {"stage": stage.value, "passed": True}
                for stage in list(CloseoutStage)[:6]
            }
            receipts = issue_observed_stage_prefix(
                root, folder, context=context, observed_outputs=outputs
            )
            self.assertEqual(len(receipts), 6)
            projection = stage_dag_projection(receipts)
            self.assertEqual(projection["next_stage"], "strict_integration")
            current = current_stage_receipts(root, folder, context=context)
            self.assertEqual(set(current), set(receipts))

            route_receipt = (
                folder
                / ".review_traces"
                / "closeout_stages"
                / "route_schema_preflight.current.json"
            )
            payload = json.loads(route_receipt.read_text())
            payload["context_sha256"] = "f" * 64
            route_receipt.write_text(json.dumps(payload), encoding="utf-8")
            current = current_stage_receipts(root, folder, context=context)
            self.assertNotIn(CloseoutStage.ROUTE_SCHEMA_PREFLIGHT, current)
            self.assertNotIn(CloseoutStage.LEAN_ATTESTATION, current)

    def test_stage_prefix_does_not_bridge_a_missing_predecessor(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder, context = self.fixture_context(root)
            receipts = issue_observed_stage_prefix(
                root,
                folder,
                context=context,
                observed_outputs={
                    CloseoutStage.SOURCE_CLAIM_INVENTORY: {"passed": True},
                    CloseoutStage.RAW_SOURCE_RECORD: {"passed": True},
                },
            )
            self.assertEqual(set(receipts), {CloseoutStage.SOURCE_CLAIM_INVENTORY})


if __name__ == "__main__":
    unittest.main()
