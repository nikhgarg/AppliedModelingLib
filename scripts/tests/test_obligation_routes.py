from __future__ import annotations

import ast
import copy
import hashlib
import json
import unittest
from pathlib import Path

from scripts.obligation_routes import (
    EvidenceRouteSet,
    ObligationRouteError,
    RouteKind,
)


ROOT = Path(__file__).resolve().parents[2]
IM05_MAP = (
    ROOT
    / "papers"
    / "IM05MarriageHonestyStability"
    / "audit"
    / "paper_statement_map.json"
)
GKGMM_MAP = (
    ROOT
    / "papers"
    / "GKGMM19IterativeLocalVoting"
    / "audit"
    / "paper_statement_map.json"
)
LG24_MAP = (
    ROOT
    / "papers"
    / "LG24ServiceLevelAgreements"
    / "audit"
    / "paper_statement_map.json"
)


class ObligationRouteTests(unittest.TestCase):
    def source_map(self):
        if not IM05_MAP.is_file():
            self.skipTest("private paper integration input is not distributed publicly")
        return json.loads(IM05_MAP.read_text(encoding="utf-8"))

    def gkgmm_source_map(self):
        return json.loads(GKGMM_MAP.read_text(encoding="utf-8"))

    def test_route_core_has_no_filesystem_subprocess_or_producer_imports(self) -> None:
        path = Path(__file__).parents[1] / "obligation_routes.py"
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

    def test_current_im05_has_no_unrouted_claim_bearing_item(self) -> None:
        routes = EvidenceRouteSet.from_source_map(
            self.source_map()
        )
        self.assertTrue(routes.routes)
        self.assertFalse(
            [
                route.source_item_id
                for route in routes.routes
                if route.route_kind is RouteKind.PENDING_SOURCE_ROUTE
            ]
        )

    def test_navigation_and_paraphrase_edits_do_not_change_route_identity(self) -> None:
        source_map = self.source_map()
        baseline = EvidenceRouteSet.from_source_map(
            source_map
        )
        moved = copy.deepcopy(source_map)
        for item in moved["items"].values():
            item["source_location"] = "moved/source.tex:900-901"
            item["source_status"] = "rewritten human-facing status"
            item["source_note"] = "rewritten navigation note"
            for anchor in item.get("source_anchor_evidence", []):
                anchor["path"] = "moved/source.tex"
                anchor["line_start"] = 900
                anchor["line_end"] = 901
            for atom in item.get("source_claim_atoms", []):
                atom["source_locator"] = "moved/source.tex:900-901"
                atom["semantic_claim"] = "A different explanatory paraphrase."
        updated = EvidenceRouteSet.from_source_map(
            moved
        )
        self.assertEqual(updated.sha256, baseline.sha256)
        self.assertEqual(updated.projection(), baseline.projection())

    def test_exact_source_quote_change_changes_preflight_route_identity(self) -> None:
        source_map = self.source_map()
        baseline = EvidenceRouteSet.from_source_map(
            source_map
        )
        changed = copy.deepcopy(source_map)
        item = next(
            value
            for value in changed["items"].values()
            if value.get("source_anchor_evidence")
        )
        anchor = item["source_anchor_evidence"][0]
        anchor["quoted_text"] += " substantive-change"
        anchor["quoted_text_sha256"] = hashlib.sha256(
            anchor["quoted_text"].encode("utf-8")
        ).hexdigest()
        updated = EvidenceRouteSet.from_source_map(
            changed
        )
        self.assertNotEqual(updated.sha256, baseline.sha256)

    def test_role_typed_surface_has_one_authoritative_selector(self) -> None:
        source_map = self.gkgmm_source_map()
        routes = EvidenceRouteSet.from_source_map(
            source_map,
        )
        self.assertEqual(len(routes.result_specifications()), 11)
        declared_source_semantics = {
            declaration
            for item in source_map["items"].values()
            if item.get("inventory_role") == "source_semantic_declaration"
            for declaration in item.get("lean_declarations", [])
        }
        self.assertEqual(
            set(routes.source_semantic_declarations()),
            declared_source_semantics,
        )
        by_spec = routes.result_route_by_specification()
        self.assertEqual(set(by_spec), set(routes.result_specifications()))
        self.assertTrue(
            all(route.source_kind in {"lemma", "theorem", "proposition"}
                for route in by_spec.values())
        )

    def test_explicit_contract_remains_a_result_even_if_row_is_nonclaim(self) -> None:
        source_map = self.gkgmm_source_map()
        result_item = next(
            item
            for item in source_map["items"].values()
            if isinstance(item.get("semantic_contract"), dict)
        )
        result_item["claim_bearing"] = False
        excluded_spec = result_item["semantic_contract"]["spec_declaration"]

        routes = EvidenceRouteSet.from_source_map(source_map)

        self.assertIn(excluded_spec, routes.result_specifications())
        self.assertEqual(
            [
                route.spec_declaration
                for route in routes.result_routes()
                if route.claim_bearing is False
            ],
            [excluded_spec],
        )

    def test_lg24_context_classification_keeps_every_explicit_contract(self) -> None:
        source_map = json.loads(LG24_MAP.read_text(encoding="utf-8"))
        # Exercise the former nonclaim shape explicitly in memory; the current
        # paper's scope decision is not a unit-test fixture or authority here.
        for item_id in (
            "city_extreme_efficiency_context",
            "relative_price_of_equity_nonnegative_context",
        ):
            self.assertIn("semantic_contract", source_map["items"][item_id])
            source_map["items"][item_id]["claim_bearing"] = False
        routes = EvidenceRouteSet.from_source_map(source_map)
        expected_specs = {
            str(item["semantic_contract"]["spec_declaration"])
            for item in source_map["items"].values()
            if isinstance(item.get("semantic_contract"), dict)
        }

        self.assertEqual(len(expected_specs), 10)
        self.assertEqual(set(routes.result_specifications()), expected_specs)
        self.assertEqual(
            {
                route.source_item_id
                for route in routes.result_routes()
                if not route.claim_bearing
            },
            {
                "city_extreme_efficiency_context",
                "relative_price_of_equity_nonnegative_context",
            },
        )

    def test_human_review_surface_resolves_to_source_items_once(self) -> None:
        source_map = self.gkgmm_source_map()
        routes = EvidenceRouteSet.from_source_map(source_map)
        status = json.loads(
            (
                ROOT
                / "papers"
                / "GKGMM19IterativeLocalVoting"
                / "status.json"
            ).read_text(encoding="utf-8")
        )
        surface = status["review_surface"]

        selected = routes.human_review_source_items(
            tuple(surface["include_names"]),
            tuple(surface["source_condition_items"]),
        )

        self.assertEqual(len(selected), 12)
        self.assertEqual(len(selected), len(set(selected)))
        self.assertIn("conditions_c123_formula", selected)

    def test_human_review_surface_rejects_source_item_overlap(self) -> None:
        routes = EvidenceRouteSet.from_source_map(self.gkgmm_source_map())
        proposition = routes.result_routes()[0]

        with self.assertRaisesRegex(ObligationRouteError, "overlap"):
            routes.human_review_source_items(
                (proposition.semantic_review_declaration,),
                (proposition.source_item_id,),
            )

    def test_source_semantic_declaration_root_is_part_of_route_identity(self) -> None:
        source_map = self.gkgmm_source_map()
        baseline = EvidenceRouteSet.from_source_map(
            source_map
        )
        changed = copy.deepcopy(source_map)
        item = next(
            item
            for item in changed["items"].values()
            if item.get("inventory_role") == "source_semantic_declaration"
        )
        item["lean_declarations"] = [
            "GKGMM19IterativeLocalVoting.DifferentSemanticRoot"
        ]
        updated = EvidenceRouteSet.from_source_map(
            changed
        )
        self.assertNotEqual(updated.sha256, baseline.sha256)

    def test_source_semantic_declaration_rejects_invalid_lean_root(self) -> None:
        source_map = self.gkgmm_source_map()
        item = next(
            item
            for item in source_map["items"].values()
            if item.get("inventory_role") == "source_semantic_declaration"
        )
        item["lean_declarations"] = ["not a Lean name"]
        with self.assertRaisesRegex(ValueError, "not a Lean name"):
            EvidenceRouteSet.from_source_map(
                source_map
            )


if __name__ == "__main__":
    unittest.main()
