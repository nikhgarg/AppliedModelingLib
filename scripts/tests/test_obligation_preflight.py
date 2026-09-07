from __future__ import annotations

import ast
import contextlib
import copy
import hashlib
import io
import json
import unittest
from pathlib import Path
from unittest import mock

from scripts.obligation_evidence_store import (
    current_accepted_graph_path,
    load_recorded_current_accepted_obligation_graph,
)
from scripts.obligation_preflight import structural_obligation_preflight


ROOT = Path(__file__).resolve().parents[2]
PAPER = "Fixture"


def current_accepted_source_map(root: Path, paper: str) -> dict[str, object]:
    """Load a real fixture through its current packed accepted graph."""

    pointer_path = current_accepted_graph_path(root, paper)
    pointer = json.loads(pointer_path.read_text(encoding="utf-8"))
    graph_sha256 = str(pointer["graph_sha256"])
    graph = load_recorded_current_accepted_obligation_graph(
        root,
        paper,
        graph_sha256,
    )
    if graph.graph_sha256 != graph_sha256:
        raise AssertionError("current accepted graph resolver returned another graph")
    map_path = root / "papers" / paper / "audit" / "paper_statement_map.json"
    return json.loads(map_path.read_text(encoding="utf-8"))


class ObligationPreflightTests(unittest.TestCase):
    def source_map(self):
        """Small structural data, not a snapshot of a mutable paper closure."""

        items = {}
        for number, key in enumerate(("claim_one", "claim_two", "paper_model", "library_model"), 1):
            is_claim = key.startswith("claim_")
            quote = f"Theorem {number}. A source claim." if is_claim else f"Definition {number}. A source model."
            quote_sha = hashlib.sha256(quote.encode()).hexdigest()
            endpoint = f"Fixture.PaperInterface.{key}"
            item = {
                "source_kind": "theorem" if is_claim else "model",
                "claim_bearing": is_claim,
                "statement": quote,
                "source_anchor_evidence": [{
                    "path": "source.txt", "line_start": number, "line_end": number,
                    "quoted_text": quote, "quoted_text_sha256": quote_sha,
                }],
                "source_claim_atoms": [{
                    "id": key, "identity_schema": 2,
                    "source_locator": f"source.txt:{number}",
                    "source_quote_sha256": quote_sha,
                    "semantic_claim": quote,
                    "reviewed_lean_route": endpoint,
                }],
            }
            if is_claim:
                item["semantic_contract"] = {
                    "spec_declaration": endpoint + "Spec",
                    "evidence_declaration": endpoint,
                    "evidence_mode": "proves", "semantic_shape": "plain",
                }
                # This unit pass checks receipt shape, not Lean issuance.
                item["source_spec_correspondence"] = {
                    "schema": 1,
                    **{field: "a" * 64 for field in (
                        "source_atoms_sha256", "spec_closure_sha256",
                        "spec_surface_sha256", "closure_environment_sha256",
                        "item_identity_sha256",
                    )},
                    "source_atom_bindings": [{}],
                    "closure_node_dispositions": [],
                }
            items[key] = item
        return {
            "schema": 1, "paper": PAPER, "semantic_contract_schema": 1,
            "semantic_route_schema": 2, "source_artifact_sha256": "b" * 64,
            "items": items,
        }

    def prerequisite_ledgers(self):
        ledgers = []
        for lane, declaration, source_item, content_field in (
            ("paper", "Fixture.Model", "paper_model", "paper_declaration_sha256"),
            ("library", "FixtureLibrary.Model", "library_model", "library_definition_sha256"),
        ):
            ledgers.append({"schema": 1, "items": {declaration: {
                f"{lane}_declaration": declaration,
                "source_item": source_item, "judgment": "matches",
                f"{lane}_semantic_target_protocol": "fixture-semantic-target/v1",
                f"{lane}_semantic_target_sha256": "c" * 64,
                "source_input_bundle_sha256": "d" * 64,
                content_field: "e" * 64,
            }}})
        return tuple(ledgers)

    def role_typed_inputs(self):
        source_map = self.source_map()
        paper, library = self.prerequisite_ledgers()
        for source_item_id, item in source_map["items"].items():
            if item["source_kind"] != "model":
                continue
            item["inventory_role"] = "source_semantic_declaration"
            roots = [
                declaration
                for declaration, row in paper["items"].items()
                if row.get("source_item") == source_item_id
            ] + [
                declaration
                for declaration, row in library["items"].items()
                if row.get("source_item") == source_item_id
            ]
            self.assertTrue(roots, source_item_id)
            item["lean_declarations"] = [roots[0]]
        return source_map, paper, library

    def test_preflight_core_has_no_filesystem_subprocess_or_producer_imports(self) -> None:
        path = Path(__file__).parents[1] / "obligation_preflight.py"
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
                "pathlib",
                "subprocess",
                "review_dashboard",
                "source_record_audit",
                "audit_repository",
                "closeout_reuse_plan",
            }
        )

    def test_complete_fixture_surface_passes_before_expensive_work(self) -> None:
        result = structural_obligation_preflight(self.source_map(), paper=PAPER)
        self.assertTrue(result.current, result.errors)
        self.assertEqual(result.counts["result_semantic"], 2)
        self.assertEqual(result.counts["source_context"], 2)
        self.assertEqual(result.counts["total"], 4)

    def test_explicit_interface_namespace_need_not_match_paper_folder(self) -> None:
        """Typed Lean routes, rather than a folder-name heuristic, own routing."""

        source_map = self.source_map()
        source_map["paper_interface_namespace"] = (
            "AppliedModelingLib.Example.MarriageHonesty"
        )
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            require_source_spec_correspondence=False,
            require_prerequisite_ledger_bindings=False,
        )
        self.assertTrue(result.current, result.errors)

    def test_exact_clauses_share_one_quote_without_collapsing(self) -> None:
        source_map = current_accepted_source_map(
            ROOT, "SeshadriUgander2020IIATesting"
        )
        result = structural_obligation_preflight(
            source_map,
            paper="SeshadriUgander2020IIATesting",
            require_theorem_endpoints=True,
            # The current accepted graph owns issued prerequisite judgments;
            # this assertion exercises source-quote multiplicity only.
            require_prerequisite_ledger_bindings=False,
        )
        self.assertTrue(result.current, result.errors)
        self.assertEqual(
            result.route_source_quote_sha256s["lemma2_separation"],
            ("e26f226d48342c592a2195577a00a50482e4667b158d6cd0279c2440824c56bd",) * 2,
        )

    def test_preflight_includes_all_fixture_semantic_prerequisites(self) -> None:
        paper, library = self.prerequisite_ledgers()
        result = structural_obligation_preflight(
            self.source_map(),
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
        )
        self.assertTrue(result.current, result.errors)
        self.assertEqual(result.counts["semantic_prerequisite"], 2)
        self.assertEqual(
            len(result.prerequisite_source_item_by_declaration),
            2,
        )

    def test_all_structural_errors_are_reported_together(self) -> None:
        changed = self.source_map()
        semantic_items = [
            item for item in changed["items"].values() if item.get("semantic_contract")
        ]
        semantic_items[0].pop("source_claim_atoms")
        semantic_items[1].pop("source_spec_correspondence")
        result = structural_obligation_preflight(changed, paper=PAPER)
        self.assertFalse(result.current)
        self.assertTrue(any("no source_claim_atoms" in error for error in result.errors))
        self.assertTrue(
            any("no source_spec_correspondence" in error for error in result.errors)
        )

    def test_raw_screening_phase_allows_only_absent_correspondence(self) -> None:
        changed = self.source_map()
        semantic_items = [
            item for item in changed["items"].values() if item.get("semantic_contract")
        ]
        semantic_items[0].pop("source_spec_correspondence")
        upstream = structural_obligation_preflight(
            changed,
            paper=PAPER,
            require_source_spec_correspondence=False,
        )
        self.assertTrue(upstream.current, upstream.errors)
        self.assertFalse(upstream.source_spec_correspondence_required)

        semantic_items[0]["source_spec_correspondence"] = {"schema": 1}
        malformed = structural_obligation_preflight(
            changed,
            paper=PAPER,
            require_source_spec_correspondence=False,
        )
        self.assertFalse(malformed.current)
        self.assertTrue(
            any("fields are malformed" in error for error in malformed.errors),
            malformed.errors,
        )

    def test_fresh_admission_rejects_definition_realization_on_result(self) -> None:
        changed = self.source_map()
        item = next(
            item for item in changed["items"].values() if item.get("semantic_contract")
        )
        item["source_kind"] = "theorem"
        item["semantic_contract"]["evidence_mode"] = "definitionally_realizes"

        historical = structural_obligation_preflight(changed, paper=PAPER)
        self.assertTrue(historical.current, historical.errors)

        fresh = structural_obligation_preflight(
            changed,
            paper=PAPER,
            require_theorem_endpoints=True,
        )
        self.assertFalse(fresh.current)
        self.assertTrue(
            any("fresh semantic contract" in error for error in fresh.errors),
            fresh.errors,
        )

    def test_fresh_admission_rejects_definition_realization_on_definition(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        item = next(
            item for item in source_map["items"].values() if item.get("semantic_contract")
        )
        item["source_kind"] = "definition"
        item["semantic_contract"]["evidence_mode"] = "definitionally_realizes"
        item.pop("semantic_review_target", None)

        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )

        self.assertFalse(result.current)
        self.assertTrue(any("full Lean semantic declaration" in error for error in result.errors), result.errors)

    def test_fresh_admission_accepts_proof_or_refutation_endpoints(self) -> None:
        source_map = self.source_map()
        proved = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            require_theorem_endpoints=True,
        )
        self.assertTrue(proved.current, proved.errors)

        refuted_map = copy.deepcopy(source_map)
        item = next(
            item
            for item in refuted_map["items"].values()
            if item.get("semantic_contract")
        )
        item["semantic_contract"]["evidence_mode"] = "refutes"
        refuted = structural_obligation_preflight(
            refuted_map,
            paper=PAPER,
            require_theorem_endpoints=True,
        )
        self.assertTrue(refuted.current, refuted.errors)

    def test_source_claim_atom_must_use_the_typed_proof_endpoint(self) -> None:
        changed = self.source_map()
        item = next(
            item for item in changed["items"].values() if item.get("semantic_contract")
        )
        item["source_claim_atoms"][0]["reviewed_lean_route"] = (
            f"{PAPER}.MissingSpecProofEndpoint"
        )
        result = structural_obligation_preflight(
            changed,
            paper=PAPER,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(
            any("must route to the typed proof endpoint" in error for error in result.errors),
            result.errors,
        )

    def test_role_typed_surface_uses_prerequisite_lane_for_source_models(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )
        self.assertTrue(result.current, result.errors)
        premise = next(
            route
            for route in result.route_set.routes
            if route.route_kind.value == "source_semantic_declaration"
        )
        self.assertEqual(
            result.route_obligation_counts[premise.source_item_id],
            {
                "source_atom": len(
                    result.route_source_quote_sha256s[premise.source_item_id]
                )
            },
        )
        self.assertIn(
            premise.source_item_id,
            result.prerequisite_source_item_by_declaration.values(),
        )

    def test_source_definition_uses_exact_claim_atoms_not_display_bundle(self) -> None:
        source_map = current_accepted_source_map(
            ROOT, "GKGMM19IterativeLocalVoting"
        )
        result = structural_obligation_preflight(
            source_map,
            paper="GKGMM19IterativeLocalVoting",
            # This integration assertion owns atom selection, not the live
            # paper's independently issued correspondence checkpoint.
            require_source_spec_correspondence=False,
            require_prerequisite_ledger_bindings=False,
        )
        self.assertTrue(result.current, result.errors)
        item = source_map["items"]["algorithm1_ilv"]
        self.assertEqual(len(item["source_anchor_evidence"]), 3)
        self.assertEqual(
            result.route_source_quote_sha256s["algorithm1_ilv"],
            (item["source_claim_atoms"][0]["source_quote_sha256"],),
        )

    def test_role_typed_surface_rejects_unbound_definition_or_premise(self) -> None:
        source_map, _paper, _library = self.role_typed_inputs()
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(
            any("requires the paper/library semantic-prerequisite ledgers" in error for error in result.errors),
            result.errors,
        )

    def test_graph_preflight_accepts_typed_roots_before_ledgers_exist(self) -> None:
        source_map, _paper, _library = self.role_typed_inputs()
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
            require_prerequisite_ledger_bindings=False,
        )

        self.assertTrue(result.current, result.errors)
        self.assertEqual(result.prerequisite_source_item_by_declaration, {})
        self.assertTrue(
            any(
                route.route_kind.value == "source_semantic_declaration"
                for route in result.route_set.routes
            )
        )

    def test_ledger_navigation_does_not_change_structural_identity(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        graph_input = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
            require_prerequisite_ledger_bindings=False,
        )
        issuance = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
        )

        self.assertTrue(graph_input.current, graph_input.errors)
        self.assertTrue(issuance.current, issuance.errors)
        self.assertFalse(graph_input.prerequisite_source_item_by_declaration)
        self.assertTrue(issuance.prerequisite_source_item_by_declaration)
        self.assertEqual(
            graph_input.structural_preflight_sha256,
            issuance.structural_preflight_sha256,
        )

    def test_graph_preflight_ignores_stale_ledgers_until_new_graph_exists(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        source_item = next(
            item
            for item in source_map["items"].values()
            if item.get("inventory_role") == "source_semantic_declaration"
        )
        source_item["lean_declarations"].append(f"{PAPER}.NewSemanticRoot")

        graph_input = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
            require_prerequisite_ledger_bindings=False,
        )
        strict = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
        )

        self.assertTrue(graph_input.current, graph_input.errors)
        self.assertFalse(strict.current)
        self.assertTrue(
            any("NewSemanticRoot is not bound" in error for error in strict.errors),
            strict.errors,
        )

    def test_role_typed_surface_rejects_legacy_source_premise_route(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        premise = next(
            item
            for item in source_map["items"].values()
            if item.get("inventory_role") == "source_semantic_declaration"
        )
        premise["inventory_role"] = "source_premise_declaration"
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(
            any("historical source-premise route" in error for error in result.errors),
            result.errors,
        )

    def test_role_typed_surface_binds_the_declared_root_not_merely_same_item(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        premise = next(
            item
            for item in source_map["items"].values()
            if item.get("inventory_role") in {
                "source_premise_declaration",
                "premise_declaration",
                "source_semantic_declaration",
            }
        )
        premise["lean_declarations"] = [f"{PAPER}.UnreviewedModel"]
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(
            any("declared semantic root" in error for error in result.errors),
            result.errors,
        )

    def test_role_typed_surface_rejects_explicit_definition_proof_contract(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        contract_items = [
            item
            for item in source_map["items"].values()
            if item.get("semantic_contract")
        ]
        contract_items[0]["source_kind"] = "definition"
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(any("full Lean semantic declaration" in error for error in result.errors), result.errors)

    def test_role_typed_surface_rejects_explicit_algorithm_proof_contract(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        contract_item = next(
            item
            for item in source_map["items"].values()
            if item.get("semantic_contract")
        )
        contract_item["source_kind"] = "algorithm"
        result = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        )
        self.assertFalse(result.current)
        self.assertTrue(any("full Lean semantic declaration" in error for error in result.errors), result.errors)

    def test_fresh_vocabulary_result_guard_preserves_historical_and_legacy_contracts(self) -> None:
        for kind in ("definition", "model", "assumption", "condition", "predicate_vocabulary", "algorithm"):
            for mode in ("proves", "refutes"):
                with self.subTest(source_kind=kind, evidence_mode=mode):
                    source_map = self.source_map()
                    item = source_map["items"]["claim_one"]
                    item["source_kind"] = kind
                    item["semantic_contract"]["evidence_mode"] = mode
                    fresh = structural_obligation_preflight(
                        source_map, paper=PAPER, require_theorem_endpoints=True,
                    )
                    self.assertFalse(fresh.current)
                    self.assertTrue(any("full Lean semantic declaration" in error for error in fresh.errors), fresh.errors)
                    historical = structural_obligation_preflight(
                        source_map, paper=PAPER, require_theorem_endpoints=False,
                    )
                    self.assertTrue(historical.current, historical.errors)
                    source_map.pop("semantic_route_schema")
                    legacy = structural_obligation_preflight(
                        source_map, paper=PAPER, require_theorem_endpoints=True,
                    )
                    self.assertTrue(legacy.current, legacy.errors)

    def test_fresh_planner_rejects_omitted_schema_before_producer(self) -> None:
        from scripts.current_closeout import planner

        source_map = self.source_map()
        source_map.pop("semantic_route_schema")
        source_map["items"]["claim_one"]["source_kind"] = "definition"
        # Historical structural contracts remain readable; the mandatory
        # current planner boundary, not this legacy reader, requires schema 2.
        legacy = structural_obligation_preflight(
            source_map, paper=PAPER, require_theorem_endpoints=True,
        )
        self.assertTrue(legacy.current, legacy.errors)

        with (
            mock.patch.object(planner, "runtime_engine_registration_error", return_value=None),
            mock.patch.object(Path, "is_file", lambda path: path.name == "paper_statement_map.json"),
            mock.patch.object(Path, "read_text", return_value=json.dumps(source_map)),
            mock.patch.object(planner, "prepare_v11_lean_review_graph", side_effect=AssertionError("producer must not run")) as producer,
            mock.patch("subprocess.Popen", side_effect=AssertionError("native process must not run")) as process,
            contextlib.redirect_stdout(io.StringIO()) as output,
        ):
            code = planner.execute_prepare_v11_lean_review_graph(
                ROOT / "papers" / PAPER,
            )
        result = json.loads(output.getvalue())
        self.assertEqual(code, 2)
        self.assertFalse(result["prepared"])
        self.assertFalse(result["acceptance_credential"])
        self.assertFalse(result["structural_preflight"]["current"])
        self.assertTrue(any(
            "current graph-native closeout requires semantic_route_schema 2" in error
            for error in result["structural_preflight"]["errors"]
        ))
        producer.assert_not_called()
        process.assert_not_called()

    def test_fresh_vocabulary_uses_actual_semantic_declaration(self) -> None:
        for kind in ("definition", "model", "assumption", "condition", "predicate_vocabulary", "algorithm"):
            with self.subTest(source_kind=kind):
                source_map, paper, library = self.role_typed_inputs()
                item = source_map["items"]["paper_model"]
                item["source_kind"] = kind
                result = structural_obligation_preflight(
                    source_map, paper=PAPER, paper_prerequisites=paper,
                    library_semantic_review=library, require_theorem_endpoints=True,
                )
                self.assertTrue(result.current, result.errors)
                self.assertEqual(result.prerequisite_source_item_by_declaration["Fixture.Model"], "paper_model")
                self.assertEqual(result.route_obligation_counts["paper_model"], {"source_atom": 1})
                self.assertEqual(result.counts["result_semantic"], 2)

    def test_fresh_mixed_definition_and_assertion_need_separate_routes(self) -> None:
        source_map, paper, library = self.role_typed_inputs()
        claim = source_map["items"]["claim_one"]
        claim["source_kind"] = "definition"
        claim["statement"] = "Definition 1. Define the model; every such model has a witness."
        mixed = structural_obligation_preflight(
            source_map, paper=PAPER, paper_prerequisites=paper,
            library_semantic_review=library, require_theorem_endpoints=True,
        )
        self.assertFalse(mixed.current)
        self.assertTrue(any("Split a mixed presentation" in error for error in mixed.errors), mixed.errors)

        # The explicit declaration item already owns Fixture.Model, while
        # this separate claim item owns its own Spec and proof endpoint.
        claim["source_kind"] = "theorem"
        claim["statement"] = "Theorem 1. Every such model has a witness."
        split = structural_obligation_preflight(
            source_map, paper=PAPER, paper_prerequisites=paper,
            library_semantic_review=library, require_theorem_endpoints=True,
        )
        self.assertTrue(split.current, split.errors)
        self.assertEqual(split.counts["result_semantic"], 2)
        self.assertEqual(split.counts["source_semantic_declaration"], 2)
        self.assertEqual(split.route_obligation_counts["claim_one"]["proof_endpoint"], 1)
        self.assertNotIn("proof_endpoint", split.route_obligation_counts["paper_model"])

    def test_fresh_formula_and_equation_propositions_keep_result_routes(self) -> None:
        for kind in ("formula", "equation"):
            for mode in ("proves", "refutes", "definitionally_realizes"):
                with self.subTest(source_kind=kind, evidence_mode=mode):
                    source_map = self.source_map()
                    item = source_map["items"]["claim_one"]
                    item["source_kind"] = kind
                    item["semantic_contract"]["evidence_mode"] = mode
                    result = structural_obligation_preflight(
                        source_map, paper=PAPER, require_theorem_endpoints=True,
                    )
                    self.assertTrue(result.current, result.errors)
                    self.assertEqual(result.route_obligation_counts["claim_one"]["proof_endpoint"], 1)

    def test_navigation_and_paraphrase_edits_do_not_change_preflight_identity(self) -> None:
        source_map = self.source_map()
        baseline = structural_obligation_preflight(source_map, paper=PAPER)
        changed = copy.deepcopy(source_map)
        for item in changed["items"].values():
            item["source_location"] = "moved/source.tex:800-801"
            item["source_status"] = "rewritten status prose"
            item["source_note"] = "rewritten navigation prose"
            for atom in item.get("source_claim_atoms", []):
                atom["source_locator"] = "moved/source.tex:800-801"
                atom["semantic_claim"] = "Rewritten explanatory paraphrase."
        updated = structural_obligation_preflight(changed, paper=PAPER)
        self.assertTrue(updated.current, updated.errors)
        self.assertEqual(
            updated.structural_preflight_sha256,
            baseline.structural_preflight_sha256,
        )

    def test_correspondence_receipt_refresh_does_not_change_source_preflight(self) -> None:
        source_map = self.source_map()
        baseline = structural_obligation_preflight(source_map, paper=PAPER)
        changed = copy.deepcopy(source_map)
        for item in changed["items"].values():
            correspondence = item.get("source_spec_correspondence")
            if not isinstance(correspondence, dict):
                continue
            for field in (
                "source_atoms_sha256",
                "spec_closure_sha256",
                "spec_surface_sha256",
                "closure_environment_sha256",
                "item_identity_sha256",
            ):
                correspondence[field] = "f" * 64
        updated = structural_obligation_preflight(changed, paper=PAPER)
        self.assertTrue(updated.current, updated.errors)
        self.assertEqual(
            updated.structural_preflight_sha256,
            baseline.structural_preflight_sha256,
        )


if __name__ == "__main__":
    unittest.main()
