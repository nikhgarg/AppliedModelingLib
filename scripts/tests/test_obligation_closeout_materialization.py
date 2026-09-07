from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import types
import unittest
from pathlib import Path
from unittest import mock

from scripts.obligation_closeout_materialization import (
    ObligationCloseoutMaterializationError,
    _authenticated_current_semantic_signatures,
    _focused_build_target_leaf_sha256s,
    _stable_json_sha256,
    materialize_passed_strict_closeout_to_obligation_bundle,
)
from scripts.closeout_content_store import content_sha256
from scripts.obligation_preflight import structural_obligation_preflight
from scripts.current_closeout.realization import (
    V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
    current_graph_realization_preflight,
    graph_native_realization_receipts_from_inventory,
)
from scripts.obligation_evidence_projection import (
    project_direct_v11_leaves_from_validated_inputs,
    project_semantic_prerequisite_leaves_from_validated_inputs,
)
from scripts.tests.obligation_historical_fixtures import (
    IM05_PAPER as PAPER,
    IM05_PAPER_DIR,
    load_im05_audit_json,
)


ROOT = Path(__file__).resolve().parents[2]
ENGINE_SHA256 = "e" * 64
_ROWS_WITH_NON_FIXTURE_OCR_SOURCE = frozenset(
    {
        "EconCSLib.finCons",
        "EconCSLib.pmfIndicatorExp",
        "EconCSLib.pmfProb",
        "EconCSLib.uniformPMF",
    }
)


class ObligationCloseoutMaterializationTests(unittest.TestCase):
    def test_build_frontier_deduplicates_semantically_identical_endpoints(self) -> None:
        self.assertEqual(
            _focused_build_target_leaf_sha256s(
                {
                    "first": {"proof_endpoint_leaf_sha256": "a" * 64},
                    "restatement": {"proof_endpoint_leaf_sha256": "a" * 64},
                    "other": {"proof_endpoint_leaf_sha256": "b" * 64},
                }
            ),
            ("a" * 64, "b" * 64),
        )

    def _carrier_fixture(self):
        source_map = load_im05_audit_json("paper_statement_map.json")
        screening = load_im05_audit_json("v11_raw_source_spec_screening.json")
        paper = load_im05_audit_json("paper_semantic_prerequisites.json")
        library = load_im05_audit_json("library_semantic_review.json")
        # This unit test replaces every Lean target with synthetic renderer
        # bytes below.  Do not let it accidentally depend on a live IM05 OCR
        # extraction that contains a forbidden control byte.  Production must
        # continue to reject that source connection; for this synthetic
        # carrier, retain every ledger row but give the affected rows an
        # already byte-verified fixture source connection.
        fixture_source = library["items"]["EconCSLib.Matching.Assignment"]
        for name in _ROWS_WITH_NON_FIXTURE_OCR_SOURCE:
            row = library["items"][name]
            self.assertEqual(row["source_item"], "appendix_lemma_A_2")
            row["source_item"] = fixture_source["source_item"]
            row["source_input_bundle_sha256"] = fixture_source[
                "source_input_bundle_sha256"
            ]
        renderer_sha256 = hashlib.sha256(b"renderer bytes").hexdigest()
        for row in paper["items"].values():
            row["paper_semantic_target_sha256"] = renderer_sha256
        for row in library["items"].values():
            row["library_semantic_target_sha256"] = renderer_sha256
        preflight = structural_obligation_preflight(
            source_map,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
        ).require_current()
        direct_names = sorted(screening["items"])
        paper_names = sorted(paper["items"])
        library_names = sorted(library["items"])
        all_names = sorted(set(direct_names) | set(paper_names) | set(library_names))
        assert preflight.route_set is not None
        routes = preflight.route_set.result_routes()
        declaration_names = sorted(
            set(all_names)
            | {route.spec_declaration for route in routes}
            | {route.evidence_declaration for route in routes}
        )
        inventory = {
            "transparent_spec_displays": {
                "schema": "2",
                "items": [
                    {
                        "specification": name,
                        "complete": True,
                        "expansion_count": "0",
                        "expanded_declarations": [],
                        "prerequisite_declarations": [],
                        "library_declarations": [],
                        "erased_proof_declarations": [],
                        "blocked_declarations": [],
                        "display": "renderer bytes",
                    }
                    for name in direct_names
                ]
            },
            "paper_prerequisite_displays": {
                "schema": "2",
                "items": [
                    {
                        "declaration": name,
                        "declaration_kind": "definition",
                        "root_expanded": True,
                        "direct_paper_declarations": [],
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                        "display": "renderer bytes",
                    }
                    for name in paper_names
                ]
            },
            "library_prerequisite_displays": {
                "schema": "3",
                "items": [
                    {
                        "declaration": name,
                        "review_owner_declaration": name,
                        "source_module": "EconCSLib.Fixture",
                        "source_line_start": 1,
                        "source_column_start": 0,
                        "source_line_end": 1,
                        "source_column_end": 1,
                        "declaration_kind": "definition",
                        "root_expanded": True,
                        "direct_library_declarations": [],
                        "erased_proof_declarations": [],
                        "display": "renderer bytes",
                    }
                    for name in library_names
                ]
            },
            "semantic_signatures": {
                "items": [
                    {
                        "declaration": name,
                        "elaborated_signature_sha256": "d" * 64,
                    }
                    for name in all_names
                ],
                "errors": [],
            },
            "semantic_review_claims": {
                "schema": "1",
                "items": [
                    {
                        "declaration": name,
                        "claim": {
                            "schema": "1",
                            "signature": {
                                "schema": "2",
                                "declaration_kind": "definition",
                                "conclusion_mode": "type_and_value",
                                "atoms": [
                                    {
                                        "ref": "result",
                                        "role": "conclusion",
                                        "canonical": {
                                            "tag": "const",
                                            "name": "True",
                                        },
                                        "display": "True",
                                    }
                                ],
                            },
                            "transparent_value_presentation_telescope": {
                                "schema": 1,
                                "reduction": "definition_value_outer_telescope",
                                "atoms": [
                                    {
                                        "ref": "result",
                                        "role": "conclusion",
                                        "canonical": {
                                            "tag": "const",
                                            "name": "True",
                                        },
                                        "display": "True",
                                    }
                                ],
                            },
                        },
                    }
                    for name in direct_names
                ],
                "errors": [],
            },
            "semantic_contracts": [
                {
                    "specification": route.spec_declaration,
                    "evidence": route.evidence_declaration,
                    "mode": route.evidence_mode,
                    "matches": True,
                    "evidence_is_unsafe": False,
                    "evidence_value_has_sorry": False,
                    "evidence_axiom_closure_checked": True,
                    "evidence_axiom_closure": [],
                }
                for route in routes
            ],
            "declarations": [
                {"declaration": name} for name in declaration_names
            ],
        }
        carrier = {
            "schema": 3,
            "acceptance_credential": False,
            "operational_scheduling_only": True,
            "paper": PAPER,
            "source_semantic_lane": V11_LEAN_CLAIM_GRAPH_EVIDENCE_LANE,
            "context_input_sha256": "a" * 64,
            "graph_request": {
                "specification_names": sorted(
                    {route.spec_declaration for route in routes}
                )
            },
            "inventory": inventory,
            "inventory_sha256": _stable_json_sha256(inventory),
        }
        carrier["receipt_integrity_sha256"] = _stable_json_sha256(carrier)
        return source_map, screening, paper, library, preflight, carrier

    def test_current_realization_preflight_has_no_historical_refresh_lane(
        self,
    ) -> None:
        source_map, _screening, _paper, _library, _preflight, carrier = (
            self._carrier_fixture()
        )
        result = current_graph_realization_preflight(
            paper=PAPER,
            source_map=source_map,
            graph_carrier=carrier,
        )
        self.assertTrue(result["current"])
        self.assertEqual(result["state"], "current_graph_authority")
        self.assertNotIn("safe_refresh", result)
        self.assertNotIn("refreshed_items", result)

        changed_request = copy.deepcopy(carrier)
        changed_request["graph_request"]["specification_names"] = []
        changed_request["receipt_integrity_sha256"] = _stable_json_sha256(
            {
                key: value
                for key, value in changed_request.items()
                if key != "receipt_integrity_sha256"
            }
        )
        blocked = current_graph_realization_preflight(
            paper=PAPER,
            source_map=source_map,
            graph_carrier=changed_request,
        )
        self.assertFalse(blocked["current"])
        self.assertEqual(blocked["state"], "blocked")

    def test_current_realization_import_cannot_load_producer_or_historical_tools(
        self,
    ) -> None:
        process = subprocess.run(
            [
                sys.executable,
                "-c",
                (
                    "import json, sys; "
                    "import scripts.current_closeout.realization; "
                    "print(json.dumps(sorted(name for name in ("
                    "'scripts.audit_evidence_integrity', "
                    "'scripts.audit_repository', "
                    "'scripts.lean_signature_manifest', "
                    "'scripts.refresh_source_spec_correspondence', "
                    "'scripts.review_dashboard', "
                    "'scripts.review_dashboard_packet') if name in sys.modules)))"
                ),
            ],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(process.returncode, 0, process.stderr)
        self.assertEqual(json.loads(process.stdout), [])

    def test_graph_native_realization_replaces_persisted_worksheets(self) -> None:
        source_map, screening, paper, library, _preflight, carrier = (
            self._carrier_fixture()
        )
        without_worksheets = copy.deepcopy(source_map)
        for item in without_worksheets["items"].values():
            item.pop("source_spec_correspondence", None)
        preflight = structural_obligation_preflight(
            without_worksheets,
            paper=PAPER,
            paper_prerequisites=paper,
            library_semantic_review=library,
            require_theorem_endpoints=True,
            require_source_spec_correspondence=False,
        ).require_current()
        receipts, errors = graph_native_realization_receipts_from_inventory(
            source_map=without_worksheets,
            inventory=carrier["inventory"],
            context_input_sha256=carrier["context_input_sha256"],
            expected_paper_declarations=paper["items"],
            expected_library_declarations=library["items"],
        )
        self.assertEqual(errors, [])
        assert preflight.route_set is not None
        projection = project_direct_v11_leaves_from_validated_inputs(
            source_map=without_worksheets,
            v11_screening=screening,
            route_set=preflight.route_set,
            issuance_authority_sha256="a" * 64,
            issuance_assurance_contract_sha256="b" * 64,
            graph_native_realization_receipts=receipts,
        )
        self.assertEqual(set(projection.navigation), set(receipts))

    def test_current_wrapper_uses_only_typed_strict_authority(self) -> None:
        authority = types.SimpleNamespace(
            paper=PAPER,
            authority_sha256="a" * 64,
            engine_tree_sha256=ENGINE_SHA256,
        )
        expected = mock.Mock()
        with (
            mock.patch(
                "scripts.obligation_closeout_materialization.validate_strict_closeout_authority",
                return_value=authority,
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization.materialize_authenticated_closeout_to_obligation_bundle",
                return_value=expected,
            ) as materialize,
        ):
            result = materialize_passed_strict_closeout_to_obligation_bundle(
                ROOT,
                PAPER,
                authority=authority,
                authenticated_v11_lean_review_graph={"fixture": True},
                authenticated_v11_lean_review_graph_sha256="b" * 64,
            )
        self.assertIs(result, expected)
        materialize.assert_called_once()
        kwargs = materialize.call_args.kwargs
        self.assertEqual(
            kwargs["operation"], "authenticated_strict_closeout_materialization"
        )
        self.assertEqual(kwargs["issuance_authority_sha256"], "a" * 64)

    def test_current_wrapper_rejects_missing_lean_graph(self) -> None:
        authority = types.SimpleNamespace(
            paper=PAPER,
            authority_sha256="a" * 64,
            engine_tree_sha256=ENGINE_SHA256,
        )
        with mock.patch(
            "scripts.obligation_closeout_materialization.validate_strict_closeout_authority",
            return_value=authority,
        ):
            with self.assertRaisesRegex(
                ObligationCloseoutMaterializationError,
                "no authenticated v11 Lean graph",
            ):
                materialize_passed_strict_closeout_to_obligation_bundle(
                    ROOT,
                    PAPER,
                    authority=authority,
                )

    def test_current_module_has_no_legacy_receipt_authority(self) -> None:
        import scripts.obligation_closeout_materialization as materialization

        self.assertFalse(hasattr(materialization, "validate_final_closure_receipt"))
        self.assertFalse(
            hasattr(materialization, "LEGACY_ACCEPTED_TRANSACTION_ASSURANCE_SHA256")
        )
        self.assertFalse(
            hasattr(materialization, "migrate_accepted_closeout_to_obligation_bundle")
        )

    def test_authenticated_current_graph_binds_every_review_row_once(self) -> None:
        source_map, screening, paper, library, preflight, carrier = (
            self._carrier_fixture()
        )
        material = _authenticated_current_semantic_signatures(
            paper=PAPER,
            carrier=carrier,
            expected_carrier_sha256=content_sha256(carrier),
            source_map=source_map,
            screening=screening,
            paper_prerequisites=paper,
            library_review=library,
            route_set=preflight.route_set,
            paper_dir=IM05_PAPER_DIR,
        )
        self.assertEqual(
            set(material.signatures),
            set(screening["items"]) | set(paper["items"]) | set(library["items"]),
        )

        missing = copy.deepcopy(carrier)
        missing["inventory"]["semantic_signatures"]["items"].pop()
        missing["inventory_sha256"] = _stable_json_sha256(missing["inventory"])
        missing["receipt_integrity_sha256"] = _stable_json_sha256(
            {
                key: value
                for key, value in missing.items()
                if key != "receipt_integrity_sha256"
            }
        )
        with self.assertRaisesRegex(
            ObligationCloseoutMaterializationError,
            "semantic identities differ",
        ):
            _authenticated_current_semantic_signatures(
                paper=PAPER,
                carrier=missing,
                expected_carrier_sha256=content_sha256(missing),
                source_map=source_map,
                screening=screening,
                paper_prerequisites=paper,
                library_review=library,
                route_set=preflight.route_set,
                paper_dir=IM05_PAPER_DIR,
            )

    def test_current_role_typed_graph_reviews_only_explicit_library_roots(
        self,
    ) -> None:
        """Recursive reusable proof support must not become an LLM row."""

        source_map, screening, paper, library, preflight, carrier = (
            self._carrier_fixture()
        )
        selected = next(iter(library["items"]))
        source_map["semantic_route_schema"] = 2
        source_map["library_semantic_prerequisite_sources"] = {
            selected: library["items"][selected]["source_item"]
        }
        library["items"] = {selected: library["items"][selected]}
        paper["items"] = {}

        # The raw Lean inventory deliberately retains every library helper and
        # all of their stable signatures. Only the explicitly source-mapped
        # reusable root needs an LLM/source comparison or a published semantic
        # identity; the other authenticated signatures stay closure evidence.
        carrier["inventory_sha256"] = _stable_json_sha256(carrier["inventory"])
        carrier["receipt_integrity_sha256"] = _stable_json_sha256(
            {
                key: value
                for key, value in carrier.items()
                if key != "receipt_integrity_sha256"
            }
        )

        material = _authenticated_current_semantic_signatures(
            paper=PAPER,
            carrier=carrier,
            expected_carrier_sha256=content_sha256(carrier),
            source_map=source_map,
            screening=screening,
            paper_prerequisites=paper,
            library_review=library,
            route_set=preflight.route_set,
            paper_dir=IM05_PAPER_DIR,
        )

        self.assertEqual(set(material.library_prerequisites["items"]), {selected})
        self.assertEqual(
            set(material.signatures),
            set(screening["items"]) | {selected},
        )

    def test_authenticated_graph_signs_only_source_mapped_prerequisite_roots(
        self,
    ) -> None:
        """Lean retains helpers for closure without making them semantic rows."""

        source_map, screening, paper, library, preflight, carrier = (
            self._carrier_fixture()
        )
        selected_paper = next(iter(paper["items"]))
        selected_library = next(iter(library["items"]))
        paper["items"] = {selected_paper: paper["items"][selected_paper]}
        library["items"] = {
            selected_library: library["items"][selected_library]
        }
        expected_signatures = (
            set(screening["items"]) | {selected_paper, selected_library}
        )
        with (
            mock.patch(
                "scripts.obligation_closeout_materialization."
                "selected_paper_semantic_prerequisite_targets",
                side_effect=lambda _source_map, targets: {
                    selected_paper: targets[selected_paper]
                },
            ),
            mock.patch(
                "scripts.obligation_closeout_materialization."
                "selected_library_semantic_prerequisite_targets",
                side_effect=lambda _source_map, targets: {
                    selected_library: targets[selected_library]
                },
            ),
        ):
            material = _authenticated_current_semantic_signatures(
                paper=PAPER,
                carrier=carrier,
                expected_carrier_sha256=content_sha256(carrier),
                source_map=source_map,
                screening=screening,
                paper_prerequisites=paper,
                library_review=library,
                route_set=preflight.route_set,
                paper_dir=IM05_PAPER_DIR,
            )

        self.assertEqual(set(material.signatures), expected_signatures)
        self.assertEqual(
            set(material.paper_prerequisites["items"]), {selected_paper}
        )
        self.assertEqual(
            set(material.library_prerequisites["items"]), {selected_library}
        )

    def test_fresh_materialization_rejects_unreviewed_discovered_prerequisite(
        self,
    ) -> None:
        source_map, screening, paper, library, preflight, carrier = (
            self._carrier_fixture()
        )
        extra = "IM05MarriageHonestyStability.UnreviewedInput"
        carrier["inventory"]["paper_prerequisite_displays"]["items"].append(
            {
                "declaration": extra,
                "declaration_kind": "definition",
                "root_expanded": True,
                "direct_paper_declarations": [],
                "direct_library_declarations": [],
                "erased_proof_declarations": [],
                "display": "extra renderer bytes",
            }
        )
        carrier["inventory"]["semantic_signatures"]["items"].append(
            {
                "declaration": extra,
                "elaborated_signature_sha256": "f" * 64,
            }
        )
        carrier["inventory_sha256"] = _stable_json_sha256(carrier["inventory"])
        carrier["receipt_integrity_sha256"] = _stable_json_sha256(
            {
                key: value
                for key, value in carrier.items()
                if key != "receipt_integrity_sha256"
            }
        )
        with self.assertRaisesRegex(
            ObligationCloseoutMaterializationError,
            "does not form a complete one-to-one semantic binding",
        ):
            _authenticated_current_semantic_signatures(
                paper=PAPER,
                carrier=carrier,
                expected_carrier_sha256=content_sha256(carrier),
                source_map=source_map,
                screening=screening,
                paper_prerequisites=paper,
                library_review=library,
                route_set=preflight.route_set,
                paper_dir=IM05_PAPER_DIR,
            )

    def test_authenticated_graph_rebinds_a_prerequisite_rename_in_memory(
        self,
    ) -> None:
        source_map, screening, paper, library, preflight, carrier = (
            self._carrier_fixture()
        )
        old_name = next(iter(paper["items"]))
        new_name = old_name + "Renamed"
        display_rows = carrier["inventory"]["paper_prerequisite_displays"][
            "items"
        ]
        display_row = next(
            row for row in display_rows if row["declaration"] == old_name
        )
        display_row["declaration"] = new_name
        signature_rows = carrier["inventory"]["semantic_signatures"]["items"]
        signature_row = next(
            row for row in signature_rows if row["declaration"] == old_name
        )
        signature_row["declaration"] = new_name
        carrier["inventory_sha256"] = _stable_json_sha256(carrier["inventory"])
        carrier["receipt_integrity_sha256"] = _stable_json_sha256(
            {
                key: value
                for key, value in carrier.items()
                if key != "receipt_integrity_sha256"
            }
        )

        material = _authenticated_current_semantic_signatures(
            paper=PAPER,
            carrier=carrier,
            expected_carrier_sha256=content_sha256(carrier),
            source_map=source_map,
            screening=screening,
            paper_prerequisites=paper,
            library_review=library,
            route_set=preflight.route_set,
            paper_dir=IM05_PAPER_DIR,
        )

        normalized = material.paper_prerequisites["items"]
        self.assertIn(new_name, normalized)
        self.assertNotIn(old_name, normalized)
        self.assertEqual(normalized[new_name]["paper_declaration"], new_name)
        self.assertIn(old_name, paper["items"])
        projection = project_semantic_prerequisite_leaves_from_validated_inputs(
            source_map=source_map,
            paper_prerequisites=material.paper_prerequisites,
            library_semantic_review=material.library_prerequisites,
            manifest_authority={},
            issuance_authority_sha256="a" * 64,
            issuance_assurance_contract_sha256="b" * 64,
            current_semantic_signature_sha256s=material.signatures,
        )
        self.assertIn(new_name, projection.navigation)
        self.assertNotIn(old_name, projection.navigation)


if __name__ == "__main__":
    unittest.main()
