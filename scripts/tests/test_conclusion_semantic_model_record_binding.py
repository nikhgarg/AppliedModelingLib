#!/usr/bin/env python3
"""Focused regressions for semantic-model record provenance bindings."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from unittest.mock import patch

from scripts import audit_conclusion_provenance as GATE
from scripts import audit_evidence_integrity as EVIDENCE
from scripts import source_record_record_closure_completion as CLOSURE
from scripts.source_record_target_disposition import (
    model_convention_record_digest,
    semantic_association_record_digest,
    source_contract_association_record_digest,
    source_map_item_record_digest,
    statement_source_review_semantic_association_digest,
)
from scripts.source_coverage_scope import (
    source_item_coverage_sha256,
    source_record_source_item_record_sha256,
    source_record_source_item_semantic_sha256,
)


def sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def canonical_sha(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


class SemanticModelRecordBindingTests(unittest.TestCase):
    paper = "Fixture"
    declaration = "Fixture.PaperInterface.reviewed"
    record = "Fixture.SourceModel"
    association_sha = semantic_association_record_digest(
        [sha("source semantic")],
        {
            "qualified_declaration": declaration,
            "elaborated_signature_sha256": sha("signature"),
        },
    )

    def _transparent_spec_dependency(
        self, dependency: dict[str, object]
    ) -> dict[str, object]:
        """Project the fixture dependency through an exact transparent Spec."""

        projected = deepcopy(dependency)
        spec = "Fixture.PaperInterface.reviewedSpec"
        semantic_key = "semantic-model::reviewed"
        identity = {
            "qualified_declaration": spec,
            "declaration_sha256": sha("spec declaration"),
        }
        signature = {
            "qualified_declaration": spec,
            "elaborated_signature_sha256": sha("spec signature"),
        }
        projected["reviewed_declaration_identity"] = identity
        projected["reviewed_elaborated_signature_identities"] = [signature]
        source_identity = {
            "source_key": "source_theorem",
            "source_location": "source.txt:10-20",
            "source_kind": "theorem",
            "source_map_item_sha256": sha("source map"),
            "source_semantic_sha256": sha("source semantic"),
            "semantic_contract": {
                "spec_declaration": spec,
                "evidence_declaration": self.declaration,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        association: dict[str, object] = {
            "schema": GATE.SEMANTIC_ASSOCIATION_SCHEMA,
            "association_mode": "semantic_contract_group_member",
            "semantic_model_judgment_key": semantic_key,
            "semantic_contract_member_role": "transparent_spec",
            "reviewed_declaration_identity": identity,
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": [source_identity],
            "source_map_item_keys": ["source_theorem"],
            "source_map_item_sha256_by_key": {
                "source_theorem": sha("source map")
            },
            "source_map_item_keys_sha256": source_map_item_record_digest(
                ["source_theorem"]
            ),
        }
        association[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD] = (
            semantic_association_record_digest(
                [sha("source semantic")], signature
            )
        )
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        projected["source_contract_association"] = association
        return projected

    def _source_proof_fidelity(self) -> dict[str, object]:
        convention = {
            "id": "FIXTURE-CONVENTION-01",
            "source_locator": "source.txt:10-20",
            "classification": "source_text_model_convention",
            "formal_meaning": "A measurable source model carrier.",
            "why_needed": "The source condition is kernel-valued.",
            "checked_scope": "The model record only.",
        }
        return {
            "model_conventions": [
                {**convention, "sha": model_convention_record_digest(convention)}
            ]
        }

    def _payload_and_judgments(
        self,
    ) -> tuple[dict[str, object], dict[str, dict[str, object]]]:
        declaration_identity = {
            "qualified_declaration": self.declaration,
            "declaration_sha256": sha("declaration"),
        }
        signature = {
            "qualified_declaration": self.declaration,
            "elaborated_signature_sha256": sha("signature"),
        }
        binder_atoms = [
            {
                "ref": "b/0",
                "role": "parameter",
                "signature_atom_sha256": sha("record binder atom"),
            }
        ]
        association = {
            "schema": 2,
            "association_origin": "explicit_source_map_direct_route",
            "role": "direct_source_route",
            "semantic_association_sha256": self.association_sha,
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": [
                {
                    "source_key": "source_theorem",
                    "source_location": "source.txt:10-20",
                    "source_kind": "theorem",
                    "source_map_item_sha256": sha("source map"),
                    "source_semantic_sha256": sha("source semantic"),
                    "semantic_contract": {
                        "spec_declaration": (
                            "Fixture.PaperInterface.reviewedSpec"
                        ),
                        "evidence_declaration": self.declaration,
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                }
            ],
        }
        field_key = "Fixture.SourceModel.kernel_isMarkov"
        data_key = "Fixture.SourceModel.kernel"
        semantic_key = "semantic-model::reviewed"
        component_sha_by_key = {
            data_key: sha("kernel component occurrence"),
            field_key: sha("kernel isMarkov component occurrence"),
        }
        structural_sha_by_key = {
            data_key: sha("kernel structural type"),
            field_key: sha("kernel isMarkov structural type"),
        }

        def source_domain_contract(field_key: str) -> dict[str, object]:
            return {
                "schema": 1,
                "route": "source_domain_correspondence",
                "component_sha256": component_sha_by_key[field_key],
                "structural_type_sha256": structural_sha_by_key[field_key],
                "source_domain_correspondence": {
                    "component_sha256": component_sha_by_key[field_key],
                    "source_model_judgment_key": semantic_key,
                },
            }

        def field_component(field_key: str, slot: int) -> dict[str, object]:
            component_sha = component_sha_by_key[field_key]
            return {
                "judgment_key": (
                    "theorem-realization::recursive_field_items::"
                    f"recursive_record_field::{component_sha}"
                ),
                "source_judgment_key": field_key,
                "source_component_section": "recursive_field_items",
                "source_claim_component_role": "material",
                "source_claim_component_sha256": component_sha,
                "structural_type_sha256": structural_sha_by_key[field_key],
                "source_claim_component_occurrence": {
                    "schema": 1,
                    "surface": "recursive_field_items",
                    "traversal_slot": slot,
                },
                "type": "Fixture.SourceModel.Field",
            }

        payload: dict[str, object] = {
            "theorem_realization_contract_schema": 1,
            "source_record_audit_sha256": sha("raw audit"),
            "source_proof_fidelity": self._source_proof_fidelity(),
            "expected_field_judgment_keys": [data_key, field_key],
            "recursive_field_items": [
                {
                    "judgment_key": data_key,
                    "structure": self.record,
                    "nested_structures": [],
                    "type": "Fixture.Kernel",
                    "structural_type_sha256": structural_sha_by_key[data_key],
                },
                {
                    "judgment_key": field_key,
                    "structure": self.record,
                    "nested_structures": [],
                    "type": "Fixture.KernelIsMarkov",
                    "structural_type_sha256": structural_sha_by_key[field_key],
                },
            ],
            "theorem_realization_component_items": [
                field_component(data_key, 0),
                field_component(field_key, 1),
            ],
            "semantic_model_items": [
                {
                    "judgment_key": semantic_key,
                    "qualified_declaration": self.declaration,
                    "reviewed_declaration_identity": declaration_identity,
                    "reviewed_elaborated_signature_identities": [signature],
                    "source_statement_association": association,
                    "semantic_surface_origin": {
                        "kind": "transparent_spec_body",
                        "qualified_declaration": (
                            "Fixture.PaperInterface.reviewedSpec"
                        ),
                    },
                    "semantic_contract_group": {
                        "schema": 1,
                        "structural_alpha_normalized_equal": True,
                        "source_item_identities": deepcopy(
                            association["source_item_identities"]
                        ),
                        "member_rows": [
                            {
                                "role": "direct_evidence",
                                "row": "arbitrary-direct-label",
                                "qualified_declaration": self.declaration,
                                "reviewed_declaration_identity": deepcopy(
                                    declaration_identity
                                ),
                            },
                            {
                                "role": "transparent_spec",
                                "row": "arbitrary-spec-label",
                                "qualified_declaration": (
                                    "Fixture.PaperInterface.reviewedSpec"
                                ),
                                "reviewed_declaration_identity": {
                                    "qualified_declaration": (
                                        "Fixture.PaperInterface.reviewedSpec"
                                    ),
                                    "declaration_sha256": sha("spec declaration"),
                                },
                            },
                        ],
                        "direct_evidence_type": {
                            "qualified_declaration": self.declaration,
                            "structural_alpha_normalized_surface": {
                                "alpha_normalized_result": "forall _b0, P _b0",
                                "binder_domains": [],
                            },
                        },
                        "surface_root": {
                            "kind": "transparent_spec_body",
                            "qualified_declaration": (
                                "Fixture.PaperInterface.reviewedSpec"
                            ),
                            "structural_alpha_normalized_surface": {
                                "alpha_normalized_result": "forall _b0, P _b0",
                                "binder_domains": [],
                            },
                        },
                    },
                    "semantic_contract_source_association": {
                        "schema": 2,
                        "role": "direct_evidence",
                        "paired_qualified_declaration": (
                            "Fixture.PaperInterface.reviewedSpec"
                        ),
                        "review_scope": "individual_row_only",
                        "structural_pairing": (
                            "not_asserted_by_source_association"
                        ),
                        "reviewed_declaration_identity": deepcopy(
                            declaration_identity
                        ),
                        "reviewed_elaborated_signature_identity": deepcopy(
                            signature
                        ),
                        "semantic_association_sha256": self.association_sha,
                        "source_item_identities": deepcopy(
                            association["source_item_identities"]
                        ),
                    },
                    "record_input_bindings": [
                        {
                            "record_roots": [self.record],
                            "binder_names": ["M"],
                            "elaborated_outer_binder_atoms": binder_atoms,
                            "fully_qualified_expanded_type_canonical": self.record,
                        }
                    ],
                }
            ],
            "conclusion_dependency_items": [
                {
                    "kind": "record_conclusion_input",
                    "record": self.record,
                    "binder": "M",
                    "elaborated_outer_binder_atoms": binder_atoms,
                    "fully_qualified_expanded_binder_type_canonical": self.record,
                    "reviewed_declaration_identity": declaration_identity,
                    "reviewed_elaborated_signature_identities": [signature],
                    "conclusion_fields": [
                        {
                            "judgment_key": field_key,
                            "source_antecedent_eligible": True,
                            "relation_to_row_result": "",
                        }
                    ],
                    "valid_constructors": [],
                    "conditional_constructors": [],
                    "rejected_constructors": [],
                }
            ],
        }
        judgments = {
            data_key: {
                "classification": "semantic_model_review",
                "source_claim_semantic_contract": source_domain_contract(data_key),
            },
            field_key: {
                "classification": "semantic_model_review",
                "source_claim_semantic_contract": source_domain_contract(field_key),
            },
            semantic_key: {
                "classification": "semantic_model_review",
                "semantic_model_dimensions": {
                    "joint_law_and_state_evolution": {
                        "verdict": "matches_approved_source_convention",
                        "source_target_disposition": "approved_source_convention",
                        "semantic_association_sha256": self.association_sha,
                        "model_convention_ids": ["FIXTURE-CONVENTION-01"],
                    }
                },
            },
        }
        return payload, judgments

    def _resolved_alias_fixture(
        self,
        payload: dict[str, object],
    ) -> str:
        """Replace the direct record surface with a graph-owned alias route."""

        alias = "Fixture.SourceModelAlias"
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(
            semantic_items[0], dict
        )
        semantic_item = semantic_items[0]
        bindings = semantic_item["record_input_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        bindings[0].update(
            {
                "source_type_canonical": "SourceModelAlias",
                "expanded_type": "(Fixture.SourceModel)",
                "fully_qualified_expanded_type_canonical": "",
            }
        )
        semantic_item["expanded_lean_surface"] = {
            "review_alias_expansion": {
                "complete": True,
                "effective_declaration": self.declaration,
                "reviewed_declaration": self.declaration,
                "steps": [],
            },
            "terminal_term_dependency_surface": {
                "scan_complete": True,
                "incomplete_reasons": [],
                "transparent_definitions": [
                    {
                        "declaration": alias,
                        "declaration_sha256": sha("alias declaration"),
                        "body_sha256": sha("alias body"),
                        "body_surface_inspectable": True,
                        "kind": "abbrev",
                        "dependency_chain": [self.declaration, alias],
                    }
                ],
            },
        }
        payload["resolved_structure_aliases"] = {alias: self.record}

        components = payload["theorem_realization_component_items"]
        assert isinstance(components, list)
        for component in components:
            assert isinstance(component, dict)
            source_key = str(component["source_judgment_key"])
            component["selected_review_route_occurrences"] = [
                {
                    "record_root": self.record,
                    "recursive_field_path": f"{self.record} -> {source_key}",
                    "selected_route_path": {
                        "declaration_path": [self.declaration],
                        "reachability": "direct_selected_route",
                        "selected_elaborated_signature_sha256": sha(
                            "signature"
                        ),
                        "selected_qualified_declaration": self.declaration,
                        "selected_route_roles": ["selected_source_route"],
                    },
                }
            ]

        dependencies = payload["conclusion_dependency_items"]
        assert isinstance(dependencies, list) and isinstance(
            dependencies[0], dict
        )
        dependencies[0].update(
            {
                "binder_type": "SourceModelAlias",
                "fully_qualified_expanded_binder_type_canonical": "",
                "record_aliases": [alias],
            }
        )
        return alias

    def _bindings(
        self,
        payload: dict[str, object],
        judgments: dict[str, dict[str, object]],
        *,
        strict: bool = True,
    ) -> tuple[GATE.SemanticModelRecordBinding, ...]:
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit = root / self.paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            status: dict[str, object] = {"status": "formalized"}
            if strict:
                status["review_surface"] = {
                    "require_source_spec_correspondence": True
                }
            (root / self.paper / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            try:
                GATE.PAPERS = root
                with (
                    patch.object(GATE, "semantic_model_review_findings", return_value=[]),
                    patch.object(GATE, "source_record_expected_item_digests", return_value={}),
                    patch.object(
                        GATE, "source_record_expected_item_digest_pins", return_value={}
                    ),
                ):
                    return GATE.current_complete_semantic_model_record_bindings(
                        self.paper, payload, judgments
                    )
            finally:
                GATE.PAPERS = old_papers

    def test_transferred_rebind_prevents_complete_binding_live_reloads(self) -> None:
        payload, judgments = self._payload_and_judgments()
        rebind = GATE.ValidatedAdministrativeProjectionRebind(
            association_rebinds={},
            association_bindings={},
            rebound_association_bindings={},
        )
        with (
            patch.object(
                GATE,
                "load_payload",
                side_effect=AssertionError(
                    "transferred complete-binding inputs must not be reopened"
                ),
            ),
            patch.object(
                GATE,
                "current_administrative_projection_rebind_context",
                side_effect=AssertionError(
                    "transferred rebind authority must not be reconstructed"
                ),
            ),
            patch.object(
                GATE, "theorem_realization_contract_active", return_value=True
            ),
            patch.object(
                GATE, "semantic_model_review_findings", return_value=[]
            ) as semantic_review,
            patch.object(
                GATE, "source_record_expected_item_digests", return_value={}
            ),
            patch.object(
                GATE, "source_record_expected_item_digest_pins", return_value={}
            ),
        ):
            bindings = GATE.current_complete_semantic_model_record_bindings(
                self.paper,
                payload,
                judgments,
                status_payload_override={"status": "formalized"},
                paper_statement_map_override={"items": {}},
                administrative_projection_rebind_override=rebind,
            )

        self.assertEqual(len(bindings), 1)
        self.assertIs(
            semantic_review.call_args.kwargs[
                "target_disposition_administrative_projection_rebind"
            ],
            rebind,
        )

    def _direct_domain_fixture(
        self,
        source_kinds: tuple[str, ...],
        *,
        proposition_sort: str = "false",
    ) -> tuple[
        dict[str, object],
        dict[str, dict[str, object]],
        dict[str, object],
        dict[str, object],
    ]:
        """Build a generated direct route using only structural identities."""

        semantic_key = "semantic-route::alpha"
        component_key = "component-occurrence::omega"
        declaration = "Fixture.Interface.alpha"
        declaration_identity = {
            "qualified_declaration": declaration,
            "declaration_sha256": sha("direct declaration"),
        }
        signature = {
            "qualified_declaration": declaration,
            "elaborated_signature_sha256": sha("direct signature"),
        }
        source_identities = [
            {
                "source_key": f"presentation-item::{index}",
                "source_location": f"source.txt:{10 + index}-{10 + index}",
                "source_kind": source_kind,
                "source_map_item_sha256": sha(f"source map {index}"),
                "source_semantic_sha256": sha(f"source semantic {index}"),
            }
            for index, source_kind in enumerate(source_kinds)
        ]
        semantic_sha = semantic_association_record_digest(
            [str(identity["source_semantic_sha256"]) for identity in source_identities],
            signature,
        )
        parent_association: dict[str, object] = {
            "schema": GATE.SEMANTIC_ASSOCIATION_SCHEMA,
            "association_origin": "explicit_source_map_direct_route",
            "role": "direct_source_route",
            GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD: semantic_sha,
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": deepcopy(source_identities),
        }
        component_association: dict[str, object] = {
            "schema": GATE.SEMANTIC_ASSOCIATION_SCHEMA,
            "association_mode": "explicit_source_map_direct_route",
            "semantic_model_judgment_key": semantic_key,
            "semantic_contract_member_role": "direct_source_route",
            GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD: semantic_sha,
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": deepcopy(source_identities),
        }
        component_association["association_sha256"] = (
            source_contract_association_record_digest(component_association)
        )
        component: dict[str, object] = {
            "judgment_key": component_key,
            "source_judgment_key": "source-row::beta",
            "source_component_section": "theorem_facing_input_items",
            "source_claim_component_role": "material",
            "source_claim_component_sha256": sha("direct component occurrence"),
            "structural_type_sha256": sha("direct structural type"),
            "proposition_sort": proposition_sort,
            "type": "Fixture.Carrier",
            "expanded_input_type": "Fixture.Carrier",
            "lean_outer_binder_route": "outer_telescope",
            "lean_outer_binder_indices": [0],
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identities": [signature],
            "source_contract_association": component_association,
        }
        audit_payload: dict[str, object] = {
            "source_record_audit_sha256": sha("direct raw audit"),
            "source_proof_fidelity": {},
            "semantic_model_items": [
                {
                    "judgment_key": semantic_key,
                    "reviewed_declaration_identity": declaration_identity,
                    "reviewed_elaborated_signature_identities": [signature],
                    "source_statement_association": parent_association,
                }
            ],
            "theorem_realization_component_items": [component],
        }
        judgments = {
            semantic_key: {
                "classification": "semantic_model_review",
                "review": "current",
            },
            "source-row::beta": {
                "classification": "arbitrary_navigation_label",
                "source_claim_semantic_contracts": {
                    str(component["source_claim_component_sha256"]): {
                        "schema": 1,
                        "route": "source_domain_correspondence",
                        "component_sha256": component[
                            "source_claim_component_sha256"
                        ],
                        "structural_type_sha256": component[
                            "structural_type_sha256"
                        ],
                        "source_domain_correspondence": {
                            "component_sha256": component[
                                "source_claim_component_sha256"
                            ],
                            "source_model_judgment_key": semantic_key,
                        },
                    }
                },
            },
        }
        statement_map = {
            "items": {
                str(identity["source_key"]): {
                    "source_kind": identity["source_kind"],
                    "statement": f"Presentation item {index}.",
                }
                for index, identity in enumerate(source_identities)
            }
        }
        return audit_payload, judgments, statement_map, component

    def _transparent_spec_domain_fixture(
        self, *, proposition_sort: str, aggregate_type_result: bool = False
    ) -> tuple[
        dict[str, object],
        dict[str, dict[str, object]],
        dict[str, object],
        dict[str, object],
    ]:
        """Project a direct semantic parent through an unrelated Spec name."""

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",), proposition_sort=proposition_sort
        )
        semantic_item = payload["semantic_model_items"][0]
        assert isinstance(semantic_item, dict)
        direct_identity = semantic_item["reviewed_declaration_identity"]
        direct_signature = semantic_item["reviewed_elaborated_signature_identities"][0]
        parent_association = semantic_item["source_statement_association"]
        assert isinstance(direct_identity, dict)
        assert isinstance(direct_signature, dict)
        assert isinstance(parent_association, dict)

        direct_declaration = str(direct_identity["qualified_declaration"])
        spec_declaration = "Fixture.Semantics.unrelated_surface_owner_731"
        spec_identity = {
            "qualified_declaration": spec_declaration,
            "declaration_sha256": sha("transparent Spec declaration"),
        }
        spec_signature = {
            "qualified_declaration": spec_declaration,
            "elaborated_signature_sha256": sha("transparent Spec signature"),
        }
        source_identities = deepcopy(parent_association["source_item_identities"])
        assert isinstance(source_identities, list)
        for source_identity in source_identities:
            assert isinstance(source_identity, dict)
            source_identity["semantic_contract"] = {
                "evidence_declaration": direct_declaration,
                "spec_declaration": spec_declaration,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        parent_association["source_item_identities"] = deepcopy(source_identities)

        alpha_surface = {
            "alpha_normalized_result": "forall _b0, Relation _b0",
            "binder_domains": [],
        }
        semantic_item.update(
            {
                "qualified_declaration": direct_declaration,
                "semantic_surface_origin": {
                    "kind": "transparent_spec_body",
                    "qualified_declaration": spec_declaration,
                },
                "semantic_contract_group": {
                    "schema": 1,
                    "structural_alpha_normalized_equal": True,
                    "source_item_identities": deepcopy(source_identities),
                    "member_rows": [
                        {
                            "role": "direct_evidence",
                            "row": "navigation-only-direct-row",
                            "qualified_declaration": direct_declaration,
                            "reviewed_declaration_identity": deepcopy(
                                direct_identity
                            ),
                        },
                        {
                            "role": "transparent_spec",
                            "row": "navigation-only-spec-row",
                            "qualified_declaration": spec_declaration,
                            "reviewed_declaration_identity": deepcopy(spec_identity),
                        },
                    ],
                    "direct_evidence_type": {
                        "qualified_declaration": direct_declaration,
                        "structural_alpha_normalized_surface": deepcopy(
                            alpha_surface
                        ),
                    },
                    "surface_root": {
                        "kind": "transparent_spec_body",
                        "qualified_declaration": spec_declaration,
                        "structural_alpha_normalized_surface": deepcopy(
                            alpha_surface
                        ),
                    },
                },
                "semantic_contract_source_association": {
                    "schema": 2,
                    "role": "direct_evidence",
                    "paired_qualified_declaration": spec_declaration,
                    "review_scope": "individual_row_only",
                    "structural_pairing": "not_asserted_by_source_association",
                    "reviewed_declaration_identity": deepcopy(direct_identity),
                    "reviewed_elaborated_signature_identity": deepcopy(
                        direct_signature
                    ),
                    "semantic_association_sha256": parent_association[
                        "semantic_association_sha256"
                    ],
                    "source_item_identities": deepcopy(source_identities),
                },
            }
        )
        semantic_item.pop("source_statement_association")

        source_keys = sorted(
            str(identity["source_key"]) for identity in source_identities
        )
        source_semantic_sha256s = [
            str(identity["source_semantic_sha256"])
            for identity in source_identities
        ]
        spec_association: dict[str, object] = {
            "schema": GATE.SEMANTIC_ASSOCIATION_SCHEMA,
            "association_mode": "semantic_contract_group_member",
            "semantic_model_judgment_key": "semantic-route::alpha",
            "semantic_contract_member_role": "transparent_spec",
            "reviewed_declaration_identity": deepcopy(spec_identity),
            "reviewed_elaborated_signature_identity": deepcopy(spec_signature),
            "source_item_identities": deepcopy(source_identities),
            "source_map_item_keys": source_keys,
            "source_map_item_sha256_by_key": {
                str(identity["source_key"]): str(
                    identity["source_map_item_sha256"]
                )
                for identity in source_identities
            },
            "source_map_item_keys_sha256": source_map_item_record_digest(
                source_keys
            ),
            "semantic_association_sha256": semantic_association_record_digest(
                source_semantic_sha256s, spec_signature
            ),
        }
        spec_association["association_sha256"] = (
            source_contract_association_record_digest(spec_association)
        )
        component.update(
            {
                "row": "a-row-name-that-has-no-semantic-role",
                "reviewed_declaration_identity": deepcopy(spec_identity),
                "reviewed_elaborated_signature_identities": [
                    deepcopy(spec_signature)
                ],
                "source_contract_association": spec_association,
            }
        )
        if aggregate_type_result:
            component["reviewed_elaborated_signature_identities"] = [
                deepcopy(direct_signature),
                deepcopy(spec_signature),
            ]
            component["source_component_section"] = (
                "type_valued_certificate_result_items"
            )
            component["source_claim_component_kind"] = "result_type_certificate"
            component.pop("lean_outer_binder_route")
            component.pop("lean_outer_binder_indices")
            component.pop("expanded_input_type")
            component.pop("type")
            component["result_occurrence_role"] = "provided_result"
            component["elaborated_witness_path"] = "result/type_argument_0"
            component["elaborated_type_witness_payload_receipt"] = {
                "schema": 1,
                "status": "ok",
                "occurrence_role": "provided_result",
                "path": "result/type_argument_0",
                "normalized_type_sha256": component["structural_type_sha256"],
                "payload_safety": "requires_source_or_lean_closure",
            }
        if proposition_sort == "true":
            self._add_substantive_direct_correspondence(
                judgments,
                component,
                component_role=("result" if aggregate_type_result else "premise"),
                association_override=spec_association,
            )["semantic_association_sha256"] = parent_association[
                "semantic_association_sha256"
            ]
        return payload, judgments, statement_map, component

    def _strict_transparent_spec_surface_fixture(
        self,
    ) -> tuple[
        dict[str, object],
        dict[str, dict[str, object]],
        dict[str, object],
        dict[str, object],
        GATE.StrictSourceSpecCorrespondenceReceipt,
        str,
    ]:
        """Build one strict theorem root with a non-name-selected Spec child."""

        payload, judgments, _statement_map, component = (
            self._transparent_spec_domain_fixture(proposition_sort="true")
        )
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        semantic_item = semantic_items[0]
        parent_association = semantic_item["semantic_contract_source_association"]
        group = semantic_item["semantic_contract_group"]
        component_association = component["source_contract_association"]
        direct_identity = semantic_item["reviewed_declaration_identity"]
        direct_signature = semantic_item["reviewed_elaborated_signature_identities"][0]
        spec_signature = component["reviewed_elaborated_signature_identities"][0]
        assert isinstance(parent_association, dict)
        assert isinstance(group, dict)
        assert isinstance(component_association, dict)
        assert isinstance(direct_identity, dict)
        assert isinstance(direct_signature, dict)
        assert isinstance(spec_signature, dict)

        source_key = "strict-source-root"
        direct_declaration = str(direct_identity["qualified_declaration"])
        spec_declaration = str(
            component_association["reviewed_declaration_identity"][
                "qualified_declaration"
            ]
        )
        contract = {
            "spec_declaration": spec_declaration,
            "evidence_declaration": direct_declaration,
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        source_atom = {
            "id": "navigation-only-atom",
            "source_locator": "source.txt:1",
            "semantic_claim": (
                "For every admissible source input, the complete displayed "
                "theorem conclusion holds under its stated condition."
            ),
            "reviewed_lean_route": direct_declaration,
            "source_quote_sha256": sha("strict current source quote"),
        }
        source_atom_sha = EVIDENCE.source_claim_atom_semantic_sha256(source_atom)
        surface_sha = sha("strict canonical Spec root")
        correspondence: dict[str, object] = {
            "schema": 1,
            "source_atoms_sha256": EVIDENCE.source_claim_atoms_semantic_sha256(
                [source_atom]
            ),
            "spec_closure_sha256": sha("strict closure"),
            "spec_surface_sha256": surface_sha,
            "closure_environment_sha256": sha("strict closure environment"),
            "source_atom_bindings": [
                {
                    "source_atom_sha256": source_atom_sha,
                    "spec_component_sha256s": [surface_sha],
                    "semantic_bridge": (
                        "The complete canonical Spec surface realizes the full "
                        "source theorem clause."
                    ),
                }
            ],
            "closure_node_dispositions": [],
        }
        correspondence["item_identity_sha256"] = (
            EVIDENCE.source_spec_correspondence_item_identity_sha256(
                contract, correspondence
            )
        )
        source_item: dict[str, object] = {
            "claim_bearing": True,
            "source_kind": "theorem",
            "title": "Theorem 1. Fixture result",
            "source_location": "source.txt:1",
            "semantic_contract": contract,
            "source_claim_atoms": [source_atom],
            "source_spec_correspondence": correspondence,
        }
        source_identity = {
            "source_key": source_key,
            "source_location": "source.txt:1",
            "source_kind": "theorem",
            "source_map_item_sha256": source_record_source_item_record_sha256(
                source_item
            ),
            "source_semantic_sha256": source_record_source_item_semantic_sha256(
                source_item, ""
            ),
            "semantic_contract": deepcopy(contract),
        }
        source_identities = [source_identity]
        source_semantic_sha = str(source_identity["source_semantic_sha256"])
        parent_association["source_item_identities"] = deepcopy(source_identities)
        parent_association[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD] = (
            semantic_association_record_digest([source_semantic_sha], direct_signature)
        )
        group["source_item_identities"] = deepcopy(source_identities)
        component_association["source_item_identities"] = deepcopy(source_identities)
        component_association["source_map_item_keys"] = [source_key]
        component_association["source_map_item_sha256_by_key"] = {
            source_key: source_identity["source_map_item_sha256"]
        }
        component_association["source_map_item_keys_sha256"] = (
            source_map_item_record_digest([source_key])
        )
        component_association[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD] = (
            semantic_association_record_digest([source_semantic_sha], spec_signature)
        )
        component_association["association_sha256"] = (
            source_contract_association_record_digest(component_association)
        )

        # The generator-owned source-record atom pin is intentionally distinct
        # from the map's source-facing atom identity above.
        generated_atom_sha = canonical_sha(
            {
                "schema": 1,
                "semantic_claim": source_atom["semantic_claim"],
                "source_quote_sha256": source_atom["source_quote_sha256"],
            }
        )
        atom_context = {
            "schema": 1,
            "id": source_atom["id"],
            "source_locator": source_atom["source_locator"],
            "semantic_claim": source_atom["semantic_claim"],
            "source_quote_sha256": source_atom["source_quote_sha256"],
            "source_claim_atom_semantic_sha256": generated_atom_sha,
        }
        atom_semantic_association_sha = canonical_sha(
            {
                "schema": 1,
                "source_claim_atom_semantic_sha256": [generated_atom_sha],
                "elaborated_signature_sha256": direct_signature[
                    "elaborated_signature_sha256"
                ],
            }
        )
        atom_association: dict[str, object] = {
            "schema": 1,
            "association_origin": GATE.SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
            "role": GATE.SOURCE_CLAIM_ATOM_ROUTE_ROLE,
            "reviewed_declaration_identity": deepcopy(direct_identity),
            "reviewed_elaborated_signature_identity": deepcopy(direct_signature),
            "source_item_identities": deepcopy(source_identities),
            "source_claim_atom_routes": [
                {
                    "source_key": source_key,
                    "atom_id": source_atom["id"],
                    "source_claim_atom_semantic_sha256": generated_atom_sha,
                }
            ],
            "source_claim_atom_semantic_association_sha256": (
                atom_semantic_association_sha
            ),
            "review_scope": "individual_row_only",
            "structural_pairing": "not_asserted_by_source_claim_atom_route",
        }
        atom_association["association_sha256"] = source_contract_association_record_digest(
            atom_association
        )
        semantic_item["source_claim_atom_association"] = atom_association
        semantic_item["source_claim_atom_contexts"] = [atom_context]

        component["source_component_section"] = "recursive_field_items"
        component["source_claim_component_structural_type_sha256"] = component[
            "structural_type_sha256"
        ]
        # The strict receipt authorizes the component occurrence; the
        # source-record projector must additionally prove that its reusable
        # source key is an actual current field/input group.
        payload["expected_field_judgment_keys"] = [
            str(component["source_judgment_key"])
        ]
        payload["recursive_field_items"] = [
            {
                "judgment_key": str(component["source_judgment_key"]),
                "kind": "fixture_recursive_field",
            }
        ]
        statement_map = {"items": {source_key: source_item}}
        runtime_receipt = GATE.StrictSourceSpecCorrespondenceReceipt(
            source_item_key=source_key,
            spec_declaration=spec_declaration,
            evidence_declaration=direct_declaration,
            evidence_mode="proves",
            semantic_shape="plain",
            source_atoms_sha256=str(correspondence["source_atoms_sha256"]),
            item_identity_sha256=str(correspondence["item_identity_sha256"]),
            spec_closure_sha256=str(correspondence["spec_closure_sha256"]),
            spec_surface_sha256=surface_sha,
            closure_environment_sha256=str(
                correspondence["closure_environment_sha256"]
            ),
        )
        return (
            payload,
            judgments,
            statement_map,
            component,
            runtime_receipt,
            source_key,
        )

    def _statement_component_domain_fixture(
        self,
        *,
        source_kind: str = "definition",
        proposition_sort: str = "false",
    ) -> tuple[
        dict[str, object],
        dict[str, dict[str, object]],
        dict[str, object],
        dict[str, object],
        dict[str, object],
    ]:
        """Replace the component-local route with an authenticated parent."""

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            (source_kind,), proposition_sort=proposition_sort
        )
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(
            semantic_items[0], dict
        )
        semantic_item = semantic_items[0]
        declaration_identity = semantic_item["reviewed_declaration_identity"]
        signatures = semantic_item["reviewed_elaborated_signature_identities"]
        assert isinstance(declaration_identity, dict)
        assert isinstance(signatures, list) and isinstance(signatures[0], dict)
        signature = signatures[0]

        map_items = statement_map["items"]
        assert isinstance(map_items, dict)
        source_item = map_items["presentation-item::0"]
        assert isinstance(source_item, dict)
        source_item["source_location"] = "source.txt:10-10"
        source_identity = {
            "source_key": "presentation-item::0",
            "source_location": source_item["source_location"],
            "source_kind": source_kind,
            "source_map_item_sha256": source_map_item_record_digest(source_item),
            "source_semantic_sha256": source_item_coverage_sha256(source_item, ""),
            "semantic_contract": {
                "evidence_declaration": "",
                "spec_declaration": "",
                "evidence_mode": "",
                "semantic_shape": "",
            },
        }
        component_identity = {
            "schema": 1,
            "source_component_semantic_sha256": sha("definition component"),
            "source_statement_sha256": sha("definition statement"),
            "source_anchor_quote_identity_sha256": sha("definition quote"),
            "source_target_sha256": sha("definition target"),
            "source_target_disposition": {
                "kind": "ordinary_or_convention",
                "source_kind": source_kind,
                "source_status": "exact",
                "coverage_status": "",
                "protocol_role": "",
            },
            "source_definition_partition_sha256": sha("definition partition"),
            "source_definition_component_sha256": sha("definition component"),
            "source_component_anchor_sha256": sha("definition anchor"),
            "statement_manifest_structure_sha256": signature[
                "elaborated_signature_sha256"
            ],
            "statement_semantic_dependency_sha256": sha(
                "definition dependencies"
            ),
            "statement_review_validator_identity_sha256": sha(
                "definition validator"
            ),
            "statement_review_protocol_sha256": sha("definition protocol"),
            "statement_source_route_semantic_sha256": sha(
                "definition source route"
            ),
            "statement_obligation_ledger_validated": True,
            "statement_source_definition_semantics_validated": True,
        }
        component_pin = source_map_item_record_digest(
            {
                "schema": 1,
                "source_definition_component_semantic_identity": component_identity,
                "elaborated_signature_sha256": signature[
                    "elaborated_signature_sha256"
                ],
            }
        )
        association: dict[str, object] = {
            "schema": 2,
            "association_origin": (
                GATE.STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
            ),
            "role": GATE.STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
            "reviewed_declaration_identity": deepcopy(declaration_identity),
            "reviewed_elaborated_signature_identity": deepcopy(signature),
            "source_item_identities": [source_identity],
            "source_definition_component_semantic_identity": component_identity,
            "component_semantic_association_sha256": component_pin,
            "semantic_association_sha256": component_pin,
            "parent_semantic_association_sha256": (
                semantic_association_record_digest(
                    [str(source_identity["source_semantic_sha256"])], signature
                )
            ),
            "review_scope": "individual_source_definition_component_only",
            "structural_pairing": "authenticated_statement_component_equivalence",
        }
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        semantic_item.pop("source_statement_association")
        semantic_item[GATE.STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD] = association
        component.pop("source_contract_association")
        return payload, judgments, statement_map, component, association

    def _whole_definition_review_domain_fixture(
        self,
        *,
        proposition_sort: str = "false",
    ) -> tuple[
        dict[str, object],
        dict[str, dict[str, object]],
        dict[str, object],
        dict[str, object],
        dict[str, object],
    ]:
        """Build an aggregate whole-definition parent with two content pins."""

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition", "model"), proposition_sort=proposition_sort
        )
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(
            semantic_items[0], dict
        )
        semantic_item = semantic_items[0]
        ordinary_association = semantic_item["source_statement_association"]
        assert isinstance(ordinary_association, dict)
        source_identities = ordinary_association["source_item_identities"]
        signature = ordinary_association[
            "reviewed_elaborated_signature_identity"
        ]
        declaration = ordinary_association["reviewed_declaration_identity"]
        assert isinstance(source_identities, list)
        assert isinstance(signature, dict) and isinstance(declaration, dict)
        route_receipts = []
        for index, source_identity in enumerate(source_identities):
            assert isinstance(source_identity, dict)
            source_pin = {
                "schema": 2,
                "source_item_semantic_sha256": source_identity[
                    "source_semantic_sha256"
                ],
                "source_target_sha256": sha(f"whole target {index}"),
            }
            route_receipts.append(
                {
                    "route_semantic_sha256": sha(f"whole route {index}"),
                    "source_reuse_pin": source_pin,
                    "source_reuse_pin_sha256": source_map_item_record_digest(
                        source_pin
                    ),
                    "source_parent_semantic_sha256": source_identity[
                        "source_semantic_sha256"
                    ],
                }
            )
        review_identity = {
            "schema": 1,
            "declaration_content_sha256": declaration["declaration_sha256"],
            "elaborated_signature_sha256": signature[
                "elaborated_signature_sha256"
            ],
            "manifest_structure_sha256": sha("whole structure"),
            "semantic_dependency_sha256": sha("whole dependencies"),
            "review_validator_identity_sha256": sha("whole validator"),
            "review_protocol_sha256": sha("whole protocol"),
            "paper_statement_sha256": sha("whole paper statement"),
            "tex_statement_sha256": sha("whole tex statement"),
            "source_route_receipts": route_receipts,
        }
        semantic_pin = statement_source_review_semantic_association_digest(
            review_identity, source_identities, signature
        )
        association: dict[str, object] = {
            "schema": 2,
            "association_origin": GATE.STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
            "role": GATE.STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
            "reviewed_declaration_identity": deepcopy(declaration),
            "reviewed_elaborated_signature_identity": deepcopy(signature),
            "source_item_identities": deepcopy(source_identities),
            "statement_source_review_identity": review_identity,
            "semantic_association_sha256": semantic_pin,
            "review_scope": "complete_whole_definition",
            "structural_pairing": "authenticated_statement_review_equivalence",
        }
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        semantic_item["source_statement_association"] = association
        component.pop("source_contract_association")
        return payload, judgments, statement_map, component, association

    def _direct_domain_receipts(
        self,
        payload: dict[str, object],
        judgments: dict[str, dict[str, object]],
        statement_map: dict[str, object],
        *,
        semantic_review_findings: list[object] | None = None,
    ) -> set[GATE.SourceDomainCorrespondenceReceipt]:
        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / self.paper
            (folder / "audit").mkdir(parents=True)
            with (
                patch.object(
                    GATE,
                    "semantic_model_review_findings",
                    return_value=(semantic_review_findings or []),
                ),
                patch.object(GATE, "source_record_expected_item_digests", return_value={}),
                patch.object(
                    GATE, "source_record_expected_item_digest_pins", return_value={}
                ),
            ):
                return GATE._current_direct_source_domain_correspondence_receipts(
                    self.paper,
                    payload,
                    judgments,
                    folder=folder,
                    statement_map=statement_map,
                    source_proof_fidelity={},
                    administrative_projection_rebind=None,
                )

    def _add_substantive_direct_correspondence(
        self,
        judgments: dict[str, dict[str, object]],
        component: dict[str, object],
        *,
        component_role: str = "premise",
        association_override: dict[str, object] | None = None,
        semantic_key_override: str = "",
    ) -> dict[str, object]:
        association = association_override or component.get(
            "source_contract_association"
        )
        assert isinstance(association, dict)
        source_identities = association["source_item_identities"]
        assert isinstance(source_identities, list)
        assert source_identities and all(
            isinstance(source_identity, dict)
            for source_identity in source_identities
        )
        component_sha = str(component["source_claim_component_sha256"])
        structural_sha = str(component["structural_type_sha256"])
        semantic_key = semantic_key_override or str(
            association.get("semantic_model_judgment_key") or ""
        )
        assert semantic_key
        substantive = {
            "schema": 1,
            "component_sha256": component_sha,
            "structural_type_sha256": structural_sha,
            "semantic_model_judgment_key": semantic_key,
            "source_contract_association_sha256": (
                source_contract_association_record_digest(association)
            ),
            "semantic_association_sha256": association[
                "semantic_association_sha256"
            ],
            "reviewed_declaration_identity": deepcopy(
                association["reviewed_declaration_identity"]
            ),
            "reviewed_elaborated_signature_identity": deepcopy(
                association["reviewed_elaborated_signature_identity"]
            ),
            "source_item_identities": deepcopy(source_identities),
            "component_role": component_role,
            "semantic_match": (
                "The generated Lean component has exactly the reviewed source-model "
                "meaning at this occurrence."
            ),
        }
        if len(source_identities) == 1:
            source_identity = source_identities[0]
            assert isinstance(source_identity, dict)
            substantive.update(
                {
                    "source_locator": source_identity["source_location"],
                    "source_semantic_clause": (
                        "The source model explicitly supplies this complete domain clause."
                    ),
                }
            )
        else:
            substantive["source_locators"] = [
                source_identity["source_location"]
                for source_identity in source_identities
                if isinstance(source_identity, dict)
            ]
            substantive["source_semantic_clauses"] = [
                {
                    "source_semantic_sha256": source_identity[
                        "source_semantic_sha256"
                    ],
                    "source_locator": source_identity["source_location"],
                    "source_semantic_clause": (
                        "This exact source item supplies its reviewed part of the "
                        "aggregate model domain."
                    ),
                }
                for source_identity in source_identities
                if isinstance(source_identity, dict)
            ]
        literal_type = GATE._generated_component_literal_type(component)
        if literal_type:
            substantive["lean_component_type"] = literal_type
        else:
            receipt = component["elaborated_type_witness_payload_receipt"]
            substantive.update(
                {
                    "elaborated_type_witness_payload_receipt": deepcopy(receipt),
                    "elaborated_witness_path": component["elaborated_witness_path"],
                    "lean_component_semantic_clause": (
                        "Lean exposes this exact result witness occurrence and its "
                        "normalized structural type."
                    ),
                }
            )
        judgments[str(component["source_judgment_key"])] = {
            "classification": "unrelated_reviewer_label",
            "source_claim_semantic_contracts": {
                component_sha: {
                    "schema": 1,
                    "route": "source_domain_correspondence",
                    "component_sha256": component_sha,
                    "structural_type_sha256": structural_sha,
                    "source_domain_correspondence": {
                        "component_sha256": component_sha,
                        "source_model_judgment_key": semantic_key,
                        "semantic_correspondence": substantive,
                    },
                }
            },
        }
        return substantive

    def test_direct_domain_receipts_accept_only_positive_presentation_kinds(
        self,
    ) -> None:
        for source_kind in ("definition", "predicate_vocabulary", "model"):
            with self.subTest(source_kind=source_kind):
                payload, judgments, statement_map, component = (
                    self._direct_domain_fixture((source_kind,))
                )
                receipts = self._direct_domain_receipts(
                    payload, judgments, statement_map
                )
                self.assertEqual(
                    receipts,
                    {
                        GATE.SourceDomainCorrespondenceReceipt(
                            component_key=str(component["judgment_key"]),
                            component_sha256=str(
                                component["source_claim_component_sha256"]
                            ),
                            source_model_judgment_key="semantic-route::alpha",
                        )
                    },
                )

    def test_direct_domain_receipts_accept_authenticated_assumption_domains(
        self,
    ) -> None:
        """An authenticated assumption parent can own its reviewed domains."""

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        semantic_item = payload["semantic_model_items"][0]
        assert isinstance(semantic_item, dict)
        parent = semantic_item["source_statement_association"]
        assert isinstance(parent, dict)
        parent["association_origin"] = GATE.SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
        parent["role"] = GATE.SOURCE_ASSUMPTION_ASSOCIATION_ROLE
        association = component["source_contract_association"]
        assert isinstance(association, dict)
        association["association_mode"] = GATE.SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
        association["semantic_contract_member_role"] = (
            GATE.SOURCE_ASSUMPTION_ASSOCIATION_ROLE
        )
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        with patch.object(
            GATE,
            "_current_direct_semantic_model_route",
            return_value=(
                parent,
                str(parent[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD]),
            ),
        ):
            receipts = self._direct_domain_receipts(
                payload, judgments, statement_map
            )
        self.assertEqual(
            receipts,
            {
                GATE.SourceDomainCorrespondenceReceipt(
                    component_key=str(component["judgment_key"]),
                    component_sha256=str(
                        component["source_claim_component_sha256"]
                    ),
                    source_model_judgment_key="semantic-route::alpha",
                )
            },
        )

        association[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD] = sha(
            "wrong assumption component semantics"
        )
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        with patch.object(
            GATE,
            "_current_direct_semantic_model_route",
            return_value=(
                parent,
                str(parent[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD]),
            ),
        ):
            self.assertEqual(
                self._direct_domain_receipts(payload, judgments, statement_map),
                set(),
            )

    def test_direct_domain_receipts_reject_claim_assumption_and_mixed_routes(
        self,
    ) -> None:
        rejected_kind_sets = [
            (source_kind,)
            for source_kind in (
                "theorem",
                "proposition",
                "lemma",
                "corollary",
                "claim",
                "runtime_claim",
                "assumption",
            )
        ] + [
            ("definition", "theorem"),
            ("model", "assumption"),
        ]
        for source_kinds in rejected_kind_sets:
            with self.subTest(source_kinds=source_kinds):
                payload, judgments, statement_map, _component = (
                    self._direct_domain_fixture(source_kinds)
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_substantive_contract_does_not_turn_claims_into_domain_sources(
        self,
    ) -> None:
        for source_kind in ("theorem", "assumption"):
            with self.subTest(source_kind=source_kind):
                payload, judgments, statement_map, component = (
                    self._direct_domain_fixture(
                        (source_kind,), proposition_sort="true"
                    )
                )
                self._add_substantive_direct_correspondence(judgments, component)
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_direct_domain_receipts_reject_prop_and_unknown_components(self) -> None:
        for proposition_sort in ("true", "unknown"):
            with self.subTest(proposition_sort=proposition_sort):
                payload, judgments, statement_map, _component = (
                    self._direct_domain_fixture(
                        ("definition",), proposition_sort=proposition_sort
                    )
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_direct_domain_receipts_accept_substantive_prop_and_unknown_components(
        self,
    ) -> None:
        for proposition_sort in ("true", "unknown"):
            with self.subTest(proposition_sort=proposition_sort):
                payload, judgments, statement_map, component = (
                    self._direct_domain_fixture(
                        ("definition",), proposition_sort=proposition_sort
                    )
                )
                self._add_substantive_direct_correspondence(judgments, component)
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    {
                        GATE.SourceDomainCorrespondenceReceipt(
                            component_key=str(component["judgment_key"]),
                            component_sha256=str(
                                component["source_claim_component_sha256"]
                            ),
                            source_model_judgment_key="semantic-route::alpha",
                        )
                    },
                )

    def test_transparent_spec_domain_projection_accepts_exact_generated_pair(
        self,
    ) -> None:
        for proposition_sort in ("false", "true"):
            with self.subTest(proposition_sort=proposition_sort):
                payload, judgments, statement_map, component = (
                    self._transparent_spec_domain_fixture(
                        proposition_sort=proposition_sort,
                        aggregate_type_result=(proposition_sort == "true"),
                    )
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    {
                        GATE.SourceDomainCorrespondenceReceipt(
                            component_key=str(component["judgment_key"]),
                            component_sha256=str(
                                component["source_claim_component_sha256"]
                            ),
                            source_model_judgment_key="semantic-route::alpha",
                        )
                    },
                )

    def _strict_full_surface_receipts(
        self,
        payload: dict[str, object],
        judgments: dict[str, dict[str, object]],
        statement_map: dict[str, object],
        runtime_receipt: GATE.StrictSourceSpecCorrespondenceReceipt,
        source_key: str,
        *,
        inventory_keys: tuple[str, ...] | None = None,
    ) -> tuple[GATE.TransparentSpecFullSurfaceCorrespondenceReceipt, ...]:
        scope = inventory_keys if inventory_keys is not None else (source_key,)
        return GATE.current_transparent_spec_full_surface_correspondence_receipts(
            self.paper,
            payload,
            judgments,
            current_source_spec_correspondence_receipts=(runtime_receipt,),
            strict_source_scope_item_keys=scope,
            status_payload_override={"status": "formalized"},
            paper_statement_map_override=statement_map,
            administrative_projection_rebind_override=None,
        )

    def _strict_parent_keys(
        self,
        payload: dict[str, object],
        statement_map: dict[str, object],
        runtime_receipt: GATE.StrictSourceSpecCorrespondenceReceipt,
        source_key: str,
        *,
        inventory_keys: tuple[str, ...] | None = None,
    ) -> frozenset[str]:
        scope = inventory_keys if inventory_keys is not None else (source_key,)
        return GATE.current_strict_transparent_spec_semantic_parent_judgment_keys(
            self.paper,
            payload,
            current_source_spec_correspondence_receipts=(runtime_receipt,),
            strict_source_scope_item_keys=scope,
            status_payload_override={"status": "formalized"},
            paper_statement_map_override=statement_map,
            administrative_projection_rebind_override=None,
        )

    def _strict_component_source_keys(
        self,
        payload: dict[str, object],
        statement_map: dict[str, object],
        runtime_receipt: GATE.StrictSourceSpecCorrespondenceReceipt,
        source_key: str,
        *,
        inventory_keys: tuple[str, ...] | None = None,
    ) -> frozenset[str]:
        scope = inventory_keys if inventory_keys is not None else (source_key,)
        return (
            GATE.current_strict_transparent_spec_full_surface_source_record_judgment_keys(
                self.paper,
                payload,
                current_source_spec_correspondence_receipts=(runtime_receipt,),
                strict_source_scope_item_keys=scope,
                status_payload_override={"status": "formalized"},
                paper_statement_map_override=statement_map,
                administrative_projection_rebind_override=None,
            )
        )

    def test_strict_transparent_spec_full_surface_projects_associated_record_field(
        self,
    ) -> None:
        (
            payload,
            judgments,
            statement_map,
            component,
            runtime_receipt,
            source_key,
        ) = self._strict_transparent_spec_surface_fixture()
        receipts = self._strict_full_surface_receipts(
            payload,
            {},
            statement_map,
            runtime_receipt,
            source_key,
        )
        self.assertEqual(len(receipts), 1)
        receipt = receipts[0]
        self.assertEqual(receipt.component_key, component["judgment_key"])
        self.assertEqual(
            receipt.source_judgment_key, component["source_judgment_key"]
        )
        self.assertEqual(receipt.source_item_keys, (source_key,))
        self.assertEqual(
            component["source_component_section"], "recursive_field_items"
        )
        self.assertEqual(
            self._strict_parent_keys(
                payload, statement_map, runtime_receipt, source_key
            ),
            frozenset({"semantic-route::alpha"}),
        )
        self.assertEqual(
            self._strict_component_source_keys(
                payload, statement_map, runtime_receipt, source_key
            ),
            frozenset({str(component["source_judgment_key"])}),
        )

    def test_strict_transparent_spec_component_source_key_requires_exact_unique_coverage(
        self,
    ) -> None:
        (
            payload,
            _judgments,
            statement_map,
            component,
            receipt,
            source_key,
        ) = self._strict_transparent_spec_surface_fixture()
        source_judgment_key = str(component["source_judgment_key"])

        # A raw duplicate is deliberately invisible to the ordinary
        # occurrence reader's compatibility de-duplication.  The source-record
        # projection reads the explicit schema-1 ledger and therefore refuses
        # to exempt a scalar sidecar key with ambiguous occurrence coverage.
        duplicate_payload = deepcopy(payload)
        duplicate_components = duplicate_payload["theorem_realization_component_items"]
        assert isinstance(duplicate_components, list)
        duplicate_components.append(deepcopy(component))
        self.assertEqual(
            self._strict_component_source_keys(
                duplicate_payload, statement_map, receipt, source_key
            ),
            frozenset(),
        )

        # A changed generated component association cannot inherit a prior
        # receipt, even though its source-record group key remains unchanged.
        changed_payload = deepcopy(payload)
        changed_component = changed_payload["theorem_realization_component_items"][0]
        assert isinstance(changed_component, dict)
        changed_association = changed_component["source_contract_association"]
        assert isinstance(changed_association, dict)
        changed_association["association_sha256"] = sha("changed component route")
        self.assertEqual(
            self._strict_component_source_keys(
                changed_payload, statement_map, receipt, source_key
            ),
            frozenset(),
        )

        # Nonmaterial records are never evidence for a material source-record
        # group, including when they reuse its otherwise valid source key.
        nonmaterial_payload = deepcopy(payload)
        nonmaterial_component = nonmaterial_payload[
            "theorem_realization_component_items"
        ][0]
        assert isinstance(nonmaterial_component, dict)
        nonmaterial_component["source_claim_component_role"] = "support"
        self.assertEqual(
            self._strict_component_source_keys(
                nonmaterial_payload, statement_map, receipt, source_key
            ),
            frozenset(),
        )
        self.assertEqual(
            source_judgment_key,
            str(component["source_judgment_key"]),
        )

    def test_strict_transparent_spec_full_surface_fails_closed_on_root_or_receipt_drift(
        self,
    ) -> None:
        def fixture() -> tuple[
            dict[str, object],
            dict[str, dict[str, object]],
            dict[str, object],
            GATE.StrictSourceSpecCorrespondenceReceipt,
            str,
        ]:
            payload, judgments, statement_map, _component, receipt, source_key = (
                self._strict_transparent_spec_surface_fixture()
            )
            return payload, judgments, statement_map, receipt, source_key

        payload, judgments, statement_map, receipt, source_key = fixture()
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload,
                judgments,
                statement_map,
                receipt,
                source_key,
                inventory_keys=(),
            ),
            (),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        source_item = statement_map["items"][source_key]
        assert isinstance(source_item, dict)
        correspondence = source_item["source_spec_correspondence"]
        assert isinstance(correspondence, dict)
        binding = correspondence["source_atom_bindings"][0]
        assert isinstance(binding, dict)
        binding["spec_component_sha256s"] = [sha("partial Spec component")]
        correspondence["item_identity_sha256"] = (
            EVIDENCE.source_spec_correspondence_item_identity_sha256(
                source_item["semantic_contract"], correspondence
            )
        )
        receipt = replace(
            receipt,
            item_identity_sha256=str(correspondence["item_identity_sha256"]),
        )
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, judgments, statement_map, receipt, source_key
            ),
            (),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload,
                judgments,
                statement_map,
                replace(receipt, item_identity_sha256=sha("stale item receipt")),
                source_key,
            ),
            (),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        parent_association = semantic_items[0]["semantic_contract_source_association"]
        assert isinstance(parent_association, dict)
        parent_association[GATE.SEMANTIC_ASSOCIATION_SHA256_FIELD] = sha(
            "stale direct parent association"
        )
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, {}, statement_map, receipt, source_key
            ),
            (),
        )
        self.assertEqual(
            self._strict_parent_keys(payload, statement_map, receipt, source_key),
            frozenset(),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        atom_association = semantic_items[0]["source_claim_atom_association"]
        assert isinstance(atom_association, dict)
        atom_association["association_sha256"] = sha("stale atom association")
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, judgments, statement_map, receipt, source_key
            ),
            (),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        atom_contexts = semantic_items[0]["source_claim_atom_contexts"]
        assert isinstance(atom_contexts, list) and isinstance(atom_contexts[0], dict)
        atom_contexts[0]["source_claim_atom_semantic_sha256"] = sha(
            "wrong current atom context"
        )
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, {}, statement_map, receipt, source_key
            ),
            (),
        )

        payload, judgments, statement_map, receipt, source_key = fixture()
        component = payload["theorem_realization_component_items"][0]
        assert isinstance(component, dict)
        association = component["source_contract_association"]
        assert isinstance(association, dict)
        association["association_sha256"] = sha("stale component association")
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, judgments, statement_map, receipt, source_key
            ),
            (),
        )

    def test_strict_transparent_spec_full_surface_rejects_out_of_scope_formula_parent(
        self,
    ) -> None:
        """A formula-like source identity cannot inherit a theorem root receipt."""

        (
            payload,
            _judgments,
            statement_map,
            _component,
            receipt,
            source_key,
        ) = self._strict_transparent_spec_surface_fixture()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        semantic_item = semantic_items[0]
        parent_association = semantic_item["semantic_contract_source_association"]
        group = semantic_item["semantic_contract_group"]
        assert isinstance(parent_association, dict) and isinstance(group, dict)
        source_identities = parent_association["source_item_identities"]
        assert isinstance(source_identities, list) and isinstance(source_identities[0], dict)

        # Preserve a structurally valid direct/Spec parent, but point it at a
        # source formula outside the runtime strict scope. The selector must
        # reject it from exact root identity rather than source-kind spelling.
        formula_identity = deepcopy(source_identities[0])
        formula_identity["source_key"] = "formula-context-outside-strict-scope"
        formula_identity["source_kind"] = "formula"
        parent_association["source_item_identities"] = [formula_identity]
        group["source_item_identities"] = [deepcopy(formula_identity)]
        self.assertEqual(
            self._strict_parent_keys(
                payload, statement_map, receipt, source_key
            ),
            frozenset(),
        )
        self.assertEqual(
            self._strict_full_surface_receipts(
                payload, {}, statement_map, receipt, source_key
            ),
            (),
        )

    def test_transparent_spec_domain_projection_rejects_aggregate_premise_signatures(
        self,
    ) -> None:
        payload, judgments, statement_map, component = (
            self._transparent_spec_domain_fixture(proposition_sort="false")
        )
        signatures = component["reviewed_elaborated_signature_identities"]
        assert isinstance(signatures, list)
        signatures.append(
            {
                "qualified_declaration": "Fixture.Unrelated.ExtraEndpoint",
                "elaborated_signature_sha256": sha(
                    "unrelated aggregate premise signature"
                ),
            }
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map),
            set(),
        )

    def test_transparent_spec_domain_projection_fails_closed_on_pair_drift(
        self,
    ) -> None:
        def fixture() -> tuple[
            dict[str, object],
            dict[str, dict[str, object]],
            dict[str, object],
            dict[str, object],
        ]:
            return self._transparent_spec_domain_fixture(
                proposition_sort="false"
            )

        def parent_parts(payload: dict[str, object]) -> tuple[dict, dict, dict]:
            semantic_item = payload["semantic_model_items"][0]
            group = semantic_item["semantic_contract_group"]
            association = semantic_item[
                "semantic_contract_source_association"
            ]
            assert isinstance(semantic_item, dict)
            assert isinstance(group, dict)
            assert isinstance(association, dict)
            return semantic_item, group, association

        cases = (
            "direct evidence identity",
            "Spec identity",
            "alpha-normalized proposition",
            "parent source identity",
            "component source identity",
            "parent semantic digest",
            "component semantic digest",
            "component association digest",
        )
        for case in cases:
            with self.subTest(case=case):
                payload, judgments, statement_map, component = fixture()
                semantic_item, group, parent_association = parent_parts(payload)
                component_association = component["source_contract_association"]
                assert isinstance(component_association, dict)
                if case == "direct evidence identity":
                    group["member_rows"][0]["reviewed_declaration_identity"][
                        "declaration_sha256"
                    ] = sha("changed direct identity")
                elif case == "Spec identity":
                    group["member_rows"][1]["reviewed_declaration_identity"][
                        "declaration_sha256"
                    ] = sha("changed Spec identity")
                elif case == "alpha-normalized proposition":
                    group["surface_root"][
                        "structural_alpha_normalized_surface"
                    ]["alpha_normalized_result"] = "forall _b0, Other _b0"
                elif case == "parent source identity":
                    group["source_item_identities"][0][
                        "source_location"
                    ] = "source.txt:88-88"
                elif case == "component source identity":
                    component_association["source_item_identities"][0][
                        "source_location"
                    ] = "source.txt:89-89"
                    component_association["association_sha256"] = (
                        source_contract_association_record_digest(
                            component_association
                        )
                    )
                elif case == "parent semantic digest":
                    parent_association["semantic_association_sha256"] = sha(
                        "changed parent semantic digest"
                    )
                elif case == "component semantic digest":
                    component_association["semantic_association_sha256"] = sha(
                        "changed component semantic digest"
                    )
                    component_association["association_sha256"] = (
                        source_contract_association_record_digest(
                            component_association
                        )
                    )
                else:
                    component_association["association_sha256"] = sha(
                        "changed component association digest"
                    )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_substantive_direct_correspondence_accepts_explicit_result_role(
        self,
    ) -> None:
        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("model",), proposition_sort="true"
        )
        component.pop("lean_outer_binder_route")
        component.pop("lean_outer_binder_indices")
        component.pop("expanded_input_type")
        component.pop("type")
        component["result_occurrence_role"] = "provided_result"
        component["elaborated_witness_path"] = "result/type_argument_0"
        component["elaborated_type_witness_payload_receipt"] = {
            "schema": 1,
            "status": "ok",
            "occurrence_role": "provided_result",
            "path": "result/type_argument_0",
            "normalized_type_sha256": component["structural_type_sha256"],
            "payload_safety": "requires_source_or_lean_closure",
        }
        self._add_substantive_direct_correspondence(
            judgments, component, component_role="result"
        )
        self.assertEqual(
            len(self._direct_domain_receipts(payload, judgments, statement_map)), 1
        )

    def test_substantive_result_correspondence_pins_exact_type_witness(
        self,
    ) -> None:
        def fixture() -> tuple[
            dict[str, object],
            dict[str, dict[str, object]],
            dict[str, object],
            dict[str, object],
            dict[str, object],
        ]:
            payload, judgments, statement_map, component = (
                self._direct_domain_fixture(("model",), proposition_sort="true")
            )
            component.pop("lean_outer_binder_route")
            component.pop("lean_outer_binder_indices")
            component.pop("expanded_input_type")
            component.pop("type")
            component["result_occurrence_role"] = "provided_result"
            component["elaborated_witness_path"] = "result/type_argument_0"
            component["elaborated_type_witness_payload_receipt"] = {
                "schema": 1,
                "status": "ok",
                "occurrence_role": "provided_result",
                "path": "result/type_argument_0",
                "normalized_type_sha256": component["structural_type_sha256"],
                "payload_safety": "requires_source_or_lean_closure",
            }
            substantive = self._add_substantive_direct_correspondence(
                judgments, component, component_role="result"
            )
            return payload, judgments, statement_map, component, substantive

        def mutate_receipt(value: object) -> object:
            assert isinstance(value, dict)
            value["normalized_type_sha256"] = sha("stale result type")
            return value

        mutations = {
            "elaborated_type_witness_payload_receipt": mutate_receipt,
            "elaborated_witness_path": lambda _value: "result/type_argument_1",
            "component_role": lambda _value: "premise",
            "lean_component_semantic_clause": lambda _value: "too short",
        }
        for field, mutate in mutations.items():
            with self.subTest(field=field):
                payload, judgments, statement_map, _component, substantive = fixture()
                substantive[field] = mutate(substantive[field])
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

        payload, judgments, statement_map, component, _substantive = fixture()
        receipt = component["elaborated_type_witness_payload_receipt"]
        assert isinstance(receipt, dict)
        receipt["path"] = "result/type_argument_1"
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

    def test_substantive_direct_correspondence_pins_every_semantic_identity(
        self,
    ) -> None:
        def mutate_identity(value: object) -> object:
            assert isinstance(value, dict)
            value["declaration_sha256"] = sha("changed declaration")
            return value

        def mutate_signature(value: object) -> object:
            assert isinstance(value, dict)
            value["elaborated_signature_sha256"] = sha("changed signature")
            return value

        def mutate_sources(value: object) -> object:
            assert isinstance(value, list)
            assert isinstance(value[0], dict)
            value[0]["source_semantic_sha256"] = sha("changed source")
            return value

        mutations = {
            "component_sha256": lambda _value: sha("wrong component"),
            "structural_type_sha256": lambda _value: sha("wrong structure"),
            "semantic_model_judgment_key": lambda _value: "semantic-route::other",
            "source_contract_association_sha256": lambda _value: sha(
                "wrong association"
            ),
            "semantic_association_sha256": lambda _value: sha(
                "wrong semantic association"
            ),
            "reviewed_declaration_identity": mutate_identity,
            "reviewed_elaborated_signature_identity": mutate_signature,
            "source_item_identities": mutate_sources,
            "source_locator": lambda _value: "source.txt:99-99",
            "lean_component_type": lambda _value: "Fixture.OtherCarrier",
            "component_role": lambda _value: "result",
            "source_semantic_clause": lambda _value: "too short",
            "semantic_match": lambda _value: "not substantive",
        }
        for field, mutate in mutations.items():
            with self.subTest(field=field):
                payload, judgments, statement_map, component = (
                    self._direct_domain_fixture(
                        ("definition",), proposition_sort="true"
                    )
                )
                substantive = self._add_substantive_direct_correspondence(
                    judgments, component
                )
                substantive[field] = mutate(substantive[field])
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_substantive_direct_correspondence_requires_occurrence_indexed_contract(
        self,
    ) -> None:
        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",), proposition_sort="true"
        )
        self._add_substantive_direct_correspondence(judgments, component)
        source_judgment = judgments[str(component["source_judgment_key"])]
        contracts = source_judgment.pop("source_claim_semantic_contracts")
        assert isinstance(contracts, dict)
        source_judgment["source_claim_semantic_contract"] = next(
            iter(contracts.values())
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

    def test_direct_domain_receipts_fail_closed_on_stale_or_wrong_identity(
        self,
    ) -> None:
        def component_association(
            component: dict[str, object],
        ) -> dict[str, object]:
            association = component["source_contract_association"]
            assert isinstance(association, dict)
            return association

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        component_association(component)["association_sha256"] = sha(
            "stale association self digest"
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        association = component_association(component)
        association["semantic_model_judgment_key"] = "semantic-route::other"
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        signatures = component["reviewed_elaborated_signature_identities"]
        assert isinstance(signatures, list) and isinstance(signatures[0], dict)
        signatures[0]["elaborated_signature_sha256"] = sha("stale signature")
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        association = component_association(component)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and isinstance(identities[0], dict)
        identities[0]["source_semantic_sha256"] = sha("stale source identity")
        association["association_sha256"] = (
            source_contract_association_record_digest(association)
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

        payload, judgments, statement_map, _component = (
            self._direct_domain_fixture(("definition",))
        )
        current_items = statement_map["items"]
        assert isinstance(current_items, dict)
        current_item = current_items["presentation-item::0"]
        assert isinstance(current_item, dict)
        # Both kinds are independently admissible. The route still fails
        # because its generated source identity is stale relative to the map.
        current_item["source_kind"] = "model"
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )

    def test_direct_domain_receipts_ignore_reviewer_classification_names(
        self,
    ) -> None:
        payload, judgments, statement_map, _component = self._direct_domain_fixture(
            ("predicate_vocabulary",)
        )
        baseline = self._direct_domain_receipts(payload, judgments, statement_map)
        self.assertEqual(len(baseline), 1)
        parent = judgments["semantic-route::alpha"]
        for classification in (
            "renamed_reviewer_label",
            "validated_source_assumption",
            "container_recursively_audited",
            "",
        ):
            with self.subTest(classification=classification):
                parent["classification"] = classification
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    baseline,
                )

    def test_statement_component_parent_bridges_exact_nonprop_occurrence(
        self,
    ) -> None:
        payload, judgments, statement_map, component, _association = (
            self._statement_component_domain_fixture()
        )
        component["row"] = "presentation names do not select this route"
        component["binder"] = "arbitrary"
        judgments["semantic-route::alpha"]["classification"] = (
            "renamed_navigation_only"
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map),
            {
                GATE.SourceDomainCorrespondenceReceipt(
                    component_key=str(component["judgment_key"]),
                    component_sha256=str(
                        component["source_claim_component_sha256"]
                    ),
                    source_model_judgment_key="semantic-route::alpha",
                )
            },
        )

    def test_explicit_direct_whole_definition_parent_bridges_exact_endpoint(
        self,
    ) -> None:
        payload, judgments, statement_map, component = self._direct_domain_fixture(
            ("definition",)
        )
        component.pop("source_contract_association")
        self.assertEqual(
            len(self._direct_domain_receipts(payload, judgments, statement_map)),
            1,
        )

    def test_aggregate_statement_review_parent_bridges_exact_endpoint(self) -> None:
        payload, judgments, statement_map, component, _association = (
            self._whole_definition_review_domain_fixture()
        )
        component["row"] = "unrelated presentation row"
        component["binder"] = "unrelated_presentation_binder"
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map),
            {
                GATE.SourceDomainCorrespondenceReceipt(
                    component_key=str(component["judgment_key"]),
                    component_sha256=str(
                        component["source_claim_component_sha256"]
                    ),
                    source_model_judgment_key="semantic-route::alpha",
                )
            },
        )

    def test_aggregate_statement_review_parent_fails_closed_on_stale_pins(
        self,
    ) -> None:
        for defect in (
            "declaration_content",
            "signature",
            "route_pin",
            "association_pin",
            "source_kind",
        ):
            with self.subTest(defect=defect):
                payload, judgments, statement_map, _component, association = (
                    self._whole_definition_review_domain_fixture()
                )
                review_identity = association["statement_source_review_identity"]
                assert isinstance(review_identity, dict)
                if defect == "declaration_content":
                    review_identity["declaration_content_sha256"] = sha("stale")
                elif defect == "signature":
                    review_identity["elaborated_signature_sha256"] = sha("stale")
                elif defect == "route_pin":
                    routes = review_identity["source_route_receipts"]
                    assert isinstance(routes, list) and isinstance(routes[0], dict)
                    routes[0]["source_reuse_pin_sha256"] = sha("stale")
                elif defect == "association_pin":
                    association["association_sha256"] = sha("stale")
                else:
                    identities = association["source_item_identities"]
                    assert isinstance(identities, list)
                    assert isinstance(identities[0], dict)
                    identities[0]["source_kind"] = "theorem"
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_aggregate_statement_review_cannot_downgrade_to_generic_pin(
        self,
    ) -> None:
        for field, replacement in (
            ("association_origin", "ordinary_generated_association"),
            ("role", "direct_source_route"),
        ):
            with self.subTest(field=field):
                payload, judgments, statement_map, _component, association = (
                    self._whole_definition_review_domain_fixture()
                )
                association[field] = replacement
                identities = association["source_item_identities"]
                signature = association[
                    "reviewed_elaborated_signature_identity"
                ]
                assert isinstance(identities, list) and isinstance(signature, dict)
                association["semantic_association_sha256"] = (
                    semantic_association_record_digest(
                        [
                            str(identity["source_semantic_sha256"])
                            for identity in identities
                            if isinstance(identity, dict)
                        ],
                        signature,
                    )
                )
                association["association_sha256"] = (
                    source_contract_association_record_digest(association)
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_aggregate_prop_parent_needs_substantive_correspondence(self) -> None:
        payload, judgments, statement_map, component, association = (
            self._whole_definition_review_domain_fixture(
                proposition_sort="true"
            )
        )
        self.assertEqual(
            self._direct_domain_receipts(payload, judgments, statement_map), set()
        )
        self._add_substantive_direct_correspondence(
            judgments,
            component,
            association_override=association,
            semantic_key_override="semantic-route::alpha",
        )
        self.assertEqual(
            len(self._direct_domain_receipts(payload, judgments, statement_map)),
            1,
        )

    def test_statement_component_parent_requires_current_contract_and_identity(
        self,
    ) -> None:
        for defect in (
            "missing_contract",
            "stale_contract_occurrence",
            "stale_declaration",
            "stale_signature",
            "stale_parent_association",
            "ambiguous_parent",
        ):
            with self.subTest(defect=defect):
                payload, judgments, statement_map, component, association = (
                    self._statement_component_domain_fixture()
                )
                source_judgment = judgments["source-row::beta"]
                contracts = source_judgment["source_claim_semantic_contracts"]
                assert isinstance(contracts, dict)
                contract = next(iter(contracts.values()))
                assert isinstance(contract, dict)
                if defect == "missing_contract":
                    source_judgment.pop("source_claim_semantic_contracts")
                elif defect == "stale_contract_occurrence":
                    contract["component_sha256"] = sha("stale occurrence")
                elif defect == "stale_declaration":
                    identity = component["reviewed_declaration_identity"]
                    assert isinstance(identity, dict)
                    identity["declaration_sha256"] = sha("stale declaration")
                elif defect == "stale_signature":
                    signatures = component[
                        "reviewed_elaborated_signature_identities"
                    ]
                    assert isinstance(signatures, list)
                    assert isinstance(signatures[0], dict)
                    signatures[0]["elaborated_signature_sha256"] = sha(
                        "stale signature"
                    )
                elif defect == "stale_parent_association":
                    association["association_sha256"] = sha(
                        "stale parent association"
                    )
                else:
                    semantic_items = payload["semantic_model_items"]
                    assert isinstance(semantic_items, list)
                    duplicate = deepcopy(semantic_items[0])
                    assert isinstance(duplicate, dict)
                    duplicate["judgment_key"] = "semantic-route::duplicate"
                    semantic_items.append(duplicate)
                    judgments["semantic-route::duplicate"] = {
                        "classification": "unrelated_label"
                    }
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

        payload, judgments, statement_map, _component, _association = (
            self._statement_component_domain_fixture()
        )
        self.assertEqual(
            self._direct_domain_receipts(
                payload,
                judgments,
                statement_map,
                semantic_review_findings=[object()],
            ),
            set(),
        )

    def test_statement_component_parent_rejects_non_domain_source_items(
        self,
    ) -> None:
        for source_kind in ("theorem", "lemma", "assumption", "claim"):
            with self.subTest(source_kind=source_kind):
                payload, judgments, statement_map, _component, _association = (
                    self._statement_component_domain_fixture(
                        source_kind=source_kind
                    )
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )

    def test_statement_component_parent_prop_or_unknown_is_substantive_only(
        self,
    ) -> None:
        for proposition_sort in ("true", "unknown"):
            with self.subTest(proposition_sort=proposition_sort):
                payload, judgments, statement_map, component, association = (
                    self._statement_component_domain_fixture(
                        source_kind="model",
                        proposition_sort=proposition_sort,
                    )
                )
                self.assertEqual(
                    self._direct_domain_receipts(
                        payload, judgments, statement_map
                    ),
                    set(),
                )
                self._add_substantive_direct_correspondence(
                    judgments,
                    component,
                    association_override=association,
                    semantic_key_override="semantic-route::alpha",
                )
                self.assertEqual(
                    len(
                        self._direct_domain_receipts(
                            payload, judgments, statement_map
                        )
                    ),
                    1,
                )

    def test_exact_parent_binding_closes_only_matching_record_dependency(self) -> None:
        payload, judgments = self._payload_and_judgments()
        bindings = self._bindings(payload, judgments)

        self.assertEqual(len(bindings), 1)
        dependency = payload["conclusion_dependency_items"][0]
        assert isinstance(dependency, dict)
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependency, bindings
            )
        )

        other = {**dependency}
        other["reviewed_declaration_identity"] = {
            "qualified_declaration": "Fixture.PaperInterface.other",
            "declaration_sha256": sha("other declaration"),
        }
        other["reviewed_elaborated_signature_identities"] = [
            {
                "qualified_declaration": "Fixture.PaperInterface.other",
                "elaborated_signature_sha256": sha("other signature"),
            }
        ]
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(other, bindings)
        )

    def test_graph_resolved_binder_alias_uses_generated_root_type(self) -> None:
        payload, judgments = self._payload_and_judgments()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(
            semantic_items[0], dict
        )
        raw_bindings = semantic_items[0]["record_input_bindings"]
        assert isinstance(raw_bindings, list) and isinstance(raw_bindings[0], dict)
        raw_bindings[0].update(
            {
                "source_type_canonical": "LocallyPresentedCarrier Parameter",
                "expanded_type": "LocallyPresentedCarrier Parameter",
                "fully_qualified_expanded_type_canonical": (
                    self.record + " Parameter"
                ),
            }
        )
        semantic_items[0]["expanded_lean_surface"] = {
            "terminal_term_dependency_surface": {
                "scan_complete": True,
                "incomplete_reasons": [],
                "transparent_definitions": [],
            }
        }
        dependencies = payload["conclusion_dependency_items"]
        assert isinstance(dependencies, list) and isinstance(dependencies[0], dict)
        dependencies[0]["fully_qualified_expanded_binder_type_canonical"] = (
            self.record + " Parameter"
        )

        bindings = self._bindings(payload, judgments)
        self.assertEqual(len(bindings), 1)
        self.assertIsNone(bindings[0].resolved_structure_alias_identity)
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependencies[0], bindings
            )
        )

    def test_resolved_structure_alias_uses_exact_graph_and_field_routes(self) -> None:
        payload, judgments = self._payload_and_judgments()
        alias = self._resolved_alias_fixture(payload)
        bindings = self._bindings(payload, judgments)
        self.assertEqual(len(bindings), 1)
        self.assertEqual(
            bindings[0].resolved_structure_alias_identity,
            (alias, sha("alias declaration"), sha("alias body")),
        )
        dependencies = payload["conclusion_dependency_items"]
        assert isinstance(dependencies, list) and isinstance(
            dependencies[0], dict
        )
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependencies[0], bindings
            )
        )

    def test_resolved_structure_alias_fails_closed_without_exact_graph_route(
        self,
    ) -> None:
        for defect in (
            "missing_alias_ledger",
            "stale_alias_target",
            "name_only_alias",
            "ambiguous_alias",
            "missing_binder_atoms",
        ):
            with self.subTest(defect=defect):
                payload, judgments = self._payload_and_judgments()
                alias = self._resolved_alias_fixture(payload)
                semantic_items = payload["semantic_model_items"]
                assert isinstance(semantic_items, list) and isinstance(
                    semantic_items[0], dict
                )
                semantic_item = semantic_items[0]
                bindings = semantic_item["record_input_bindings"]
                assert isinstance(bindings, list) and isinstance(bindings[0], dict)
                if defect == "missing_alias_ledger":
                    payload.pop("resolved_structure_aliases")
                elif defect == "stale_alias_target":
                    payload["resolved_structure_aliases"] = {
                        alias: "Fixture.OtherModel"
                    }
                elif defect == "name_only_alias":
                    expanded = semantic_item["expanded_lean_surface"]
                    assert isinstance(expanded, dict)
                    terminal = expanded["terminal_term_dependency_surface"]
                    assert isinstance(terminal, dict)
                    terminal["transparent_definitions"] = []
                elif defect == "ambiguous_alias":
                    other_alias = "Other.SourceModelAlias"
                    aliases = payload["resolved_structure_aliases"]
                    assert isinstance(aliases, dict)
                    aliases[other_alias] = self.record
                    expanded = semantic_item["expanded_lean_surface"]
                    assert isinstance(expanded, dict)
                    terminal = expanded["terminal_term_dependency_surface"]
                    assert isinstance(terminal, dict)
                    definitions = terminal["transparent_definitions"]
                    assert isinstance(definitions, list)
                    definitions.append(
                        {
                            "declaration": other_alias,
                            "declaration_sha256": sha("other alias declaration"),
                            "body_sha256": sha("other alias body"),
                            "body_surface_inspectable": True,
                            "kind": "abbrev",
                            "dependency_chain": [self.declaration, other_alias],
                        }
                    )
                else:
                    bindings[0]["elaborated_outer_binder_atoms"] = []
                self.assertEqual(self._bindings(payload, judgments), ())

    def test_resolved_structure_alias_fails_closed_on_stale_field_route(self) -> None:
        for defect in ("missing", "stale", "ambiguous"):
            with self.subTest(defect=defect):
                payload, judgments = self._payload_and_judgments()
                self._resolved_alias_fixture(payload)
                components = payload["theorem_realization_component_items"]
                assert isinstance(components, list) and isinstance(
                    components[0], dict
                )
                routes = components[0]["selected_review_route_occurrences"]
                assert isinstance(routes, list) and isinstance(routes[0], dict)
                if defect == "missing":
                    components[0]["selected_review_route_occurrences"] = []
                elif defect == "ambiguous":
                    routes.append(deepcopy(routes[0]))
                else:
                    route_path = routes[0]["selected_route_path"]
                    assert isinstance(route_path, dict)
                    route_path["selected_elaborated_signature_sha256"] = sha(
                        "stale signature"
                    )
                self.assertEqual(self._bindings(payload, judgments), ())

    def test_resolved_structure_alias_dependency_requires_same_exact_alias(
        self,
    ) -> None:
        payload, judgments = self._payload_and_judgments()
        self._resolved_alias_fixture(payload)
        bindings = self._bindings(payload, judgments)
        dependencies = payload["conclusion_dependency_items"]
        assert isinstance(dependencies, list) and isinstance(
            dependencies[0], dict
        )
        dependencies[0]["record_aliases"] = ["Fixture.StaleAlias"]
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependencies[0], bindings
            )
        )

    def test_schema_one_record_binding_uses_atoms_not_binder_names(self) -> None:
        payload, judgments = self._payload_and_judgments()
        bindings = self._bindings(payload, judgments)
        dependency = payload["conclusion_dependency_items"][0]
        assert isinstance(dependency, dict)

        renamed = deepcopy(dependency)
        renamed["binder"] = "completelyRenamed"
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                renamed, bindings
            )
        )

        for field, replacement in (
            ("elaborated_outer_binder_atoms", []),
            ("fully_qualified_expanded_binder_type_canonical", "Fixture.Other"),
            (
                "fully_qualified_expanded_binder_type_canonical",
                self.record + " RenamedTypeParameter",
            ),
        ):
            with self.subTest(field=field):
                malformed = deepcopy(renamed)
                malformed[field] = replacement
                self.assertFalse(
                    GATE.dependency_has_complete_semantic_model_record_binding(
                        malformed, bindings
                    )
                )

    def test_same_typed_record_binder_positions_cannot_be_swapped(self) -> None:
        payload, judgments = self._payload_and_judgments()
        semantic_items = payload["semantic_model_items"]
        dependency_items = payload["conclusion_dependency_items"]
        assert isinstance(semantic_items, list)
        assert isinstance(semantic_items[0], dict)
        bindings = semantic_items[0]["record_input_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        assert isinstance(dependency_items, list)
        assert isinstance(dependency_items[0], dict)
        atoms = [
            {
                "ref": "b/0",
                "role": "parameter",
                "signature_atom_sha256": sha("first same-typed record"),
            },
            {
                "ref": "b/1",
                "role": "parameter",
                "signature_atom_sha256": sha("second same-typed record"),
            },
        ]
        bindings[0]["binder_names"] = ["first", "second"]
        bindings[0]["elaborated_outer_binder_atoms"] = atoms
        dependency_items[0]["binder"] = "first second"
        dependency_items[0]["elaborated_outer_binder_atoms"] = atoms

        complete = self._bindings(payload, judgments)
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependency_items[0], complete
            )
        )
        swapped = deepcopy(dependency_items[0])
        swapped_atoms = deepcopy(atoms)
        swapped_atoms[0]["signature_atom_sha256"], swapped_atoms[1][
            "signature_atom_sha256"
        ] = (
            swapped_atoms[1]["signature_atom_sha256"],
            swapped_atoms[0]["signature_atom_sha256"],
        )
        swapped["elaborated_outer_binder_atoms"] = swapped_atoms
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                swapped, complete
            )
        )

    def test_exact_transparent_spec_route_reuses_evidence_record_binding(self) -> None:
        payload, judgments = self._payload_and_judgments()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list)
        assert isinstance(semantic_items[0], dict)
        raw_bindings = semantic_items[0]["record_input_bindings"]
        assert isinstance(raw_bindings, list) and isinstance(raw_bindings[0], dict)
        spec_atoms = [
            {
                "ref": "b/0",
                "role": "parameter",
                "signature_atom_sha256": sha("current spec record binder atom"),
            }
        ]
        spec_type = self.record + " Fixture.SpecParameter"
        raw_bindings[0]["elaborated_outer_binder_atoms"] = spec_atoms
        raw_bindings[0]["fully_qualified_expanded_type_canonical"] = spec_type
        bindings = self._bindings(payload, judgments)
        dependency = payload["conclusion_dependency_items"][0]
        assert isinstance(dependency, dict)

        projected = self._transparent_spec_dependency(dependency)
        projected["elaborated_outer_binder_atoms"] = spec_atoms
        projected["fully_qualified_expanded_binder_type_canonical"] = spec_type
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                projected, bindings
            )
        )

        stale_atom = deepcopy(projected)
        stale_atom["elaborated_outer_binder_atoms"] = dependency[
            "elaborated_outer_binder_atoms"
        ]
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                stale_atom, bindings
            )
        )

        stale_type = deepcopy(projected)
        stale_type["fully_qualified_expanded_binder_type_canonical"] = self.record
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                stale_type, bindings
            )
        )

    def test_transparent_spec_record_route_fails_closed_when_stale_or_wrong(
        self,
    ) -> None:
        payload, judgments = self._payload_and_judgments()
        bindings = self._bindings(payload, judgments)
        dependency = payload["conclusion_dependency_items"][0]
        assert isinstance(dependency, dict)

        def projected() -> dict[str, object]:
            return self._transparent_spec_dependency(dependency)

        stale_digest = projected()
        stale_association = stale_digest["source_contract_association"]
        assert isinstance(stale_association, dict)
        stale_association["semantic_model_judgment_key"] = "semantic-model::other"
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                stale_digest, bindings
            )
        )

        wrong_parent = projected()
        wrong_parent_association = wrong_parent["source_contract_association"]
        assert isinstance(wrong_parent_association, dict)
        wrong_parent_association["semantic_model_judgment_key"] = (
            "semantic-model::other"
        )
        wrong_parent_association["association_sha256"] = (
            source_contract_association_record_digest(
                wrong_parent_association
            )
        )
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                wrong_parent, bindings
            )
        )

        wrong_evidence = projected()
        wrong_evidence_association = wrong_evidence[
            "source_contract_association"
        ]
        assert isinstance(wrong_evidence_association, dict)
        identities = wrong_evidence_association["source_item_identities"]
        assert isinstance(identities, list) and isinstance(identities[0], dict)
        semantic_contract = identities[0]["semantic_contract"]
        assert isinstance(semantic_contract, dict)
        semantic_contract["evidence_declaration"] = (
            "Fixture.PaperInterface.other"
        )
        wrong_evidence_association["association_sha256"] = (
            source_contract_association_record_digest(
                wrong_evidence_association
            )
        )
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                wrong_evidence, bindings
            )
        )

        stale_signature = projected()
        stale_signature_identities = stale_signature[
            "reviewed_elaborated_signature_identities"
        ]
        assert isinstance(stale_signature_identities, list)
        assert isinstance(stale_signature_identities[0], dict)
        stale_signature_identities[0]["elaborated_signature_sha256"] = sha(
            "changed spec signature"
        )
        self.assertFalse(
            GATE.dependency_has_complete_semantic_model_record_binding(
                stale_signature, bindings
            )
        )

    def test_schema_one_binding_is_independent_of_reviewer_classification(self) -> None:
        payload, judgments = self._payload_and_judgments()
        baseline = self._bindings(payload, judgments)
        self.assertEqual(len(baseline), 1)

        # The source-domain receipts and generated component occurrences are
        # unchanged.  Classifications are navigation/legacy review metadata,
        # so changing them cannot create or erase schema-1 closure credit.
        for judgment in judgments.values():
            judgment["classification"] = "unrelated_reviewer_label"
        renamed = self._bindings(payload, judgments)
        self.assertEqual(renamed, baseline)

    def test_wrong_component_receipt_cannot_close_record(self) -> None:
        payload, judgments = self._payload_and_judgments()
        field_key = "Fixture.SourceModel.kernel_isMarkov"
        contract = judgments[field_key]["source_claim_semantic_contract"]
        assert isinstance(contract, dict)
        correspondence = contract["source_domain_correspondence"]
        assert isinstance(correspondence, dict)
        correspondence["source_model_judgment_key"] = "semantic-model::other"
        self.assertEqual(self._bindings(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        contract = judgments[field_key]["source_claim_semantic_contract"]
        assert isinstance(contract, dict)
        contract["component_sha256"] = sha("wrong component occurrence")
        self.assertEqual(self._bindings(payload, judgments), ())

    def test_v10_parent_closure_attestation_is_exact_and_not_a_v11_contract(self) -> None:
        payload, judgments = self._payload_and_judgments()
        candidates = CLOSURE.current_record_field_closure_completion_candidates(payload)
        self.assertEqual(len(candidates), 1)
        candidate = candidates[0]
        semantic_key = candidate.semantic_model_judgment_key
        parent = judgments[semantic_key]
        attestation = {
            "schema": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_SCHEMA,
            "closure_sha256": candidate.closure_sha256,
            "verdict": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_VERDICT,
            "source_location": "source.txt:10-20",
            "closure_semantics": (
                "The source model specifies the complete kernel and Markov-law "
                "record, including both generated field occurrences."
            ),
            "lean_evidence": (
                "The generated record closure and component identities cover each "
                "field under the reviewed declaration."
            ),
        }
        parent[CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD] = [
            attestation
        ]
        attestation_sha = CLOSURE.closure_attestation_sha256(attestation)
        for (
            field_key,
            component_key,
            component_sha,
            structural_type_sha,
        ) in candidate.field_components:
            judgments[field_key] = {
                "classification": "semantic_model_review",
                CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD: {
                    "schema": CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA,
                    "closure_sha256": candidate.closure_sha256,
                    "attestation_sha256": attestation_sha,
                    "semantic_model_judgment_key": semantic_key,
                    "component_sha256": component_sha,
                    "structural_type_sha256": structural_type_sha,
                },
            }

        # This is a v10 source-model closure projection. It can close only
        # this exact parent/binding/field closure.
        self.assertEqual(len(self._bindings(payload, judgments, strict=False)), 1)

        # It intentionally does not manufacture v11 occurrence contracts.
        self.assertEqual(self._bindings(payload, judgments, strict=True), ())

        # Any parent-attestation change invalidates all child receipts.
        parent[CLOSURE.RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD][0][
            "closure_semantics"
        ] = "Different reviewed semantics."
        self.assertEqual(self._bindings(payload, judgments, strict=False), ())

    def test_source_to_spec_direct_evidence_parent_closes_record_fields(self) -> None:
        """The current direct-evidence parent is an exact closure root too."""

        payload, _judgments = self._payload_and_judgments()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list) and isinstance(semantic_items[0], dict)
        semantic_items[0].pop("source_statement_association")

        candidates = CLOSURE.current_record_field_closure_completion_candidates(payload)

        self.assertEqual(len(candidates), 1)
        self.assertEqual(candidates[0].semantic_model_judgment_key, "semantic-model::reviewed")

    def test_result_relation_is_diagnostic_but_semantic_review_failure_blocks(self) -> None:
        payload, judgments = self._payload_and_judgments()
        dependency = payload["conclusion_dependency_items"][0]
        assert isinstance(dependency, dict)
        fields = dependency["conclusion_fields"]
        assert isinstance(fields, list) and isinstance(fields[0], dict)
        fields[0]["relation_to_row_result"] = "component_of_target"
        bindings = self._bindings(payload, judgments)
        self.assertEqual(len(bindings), 1)
        self.assertTrue(
            GATE.dependency_has_complete_semantic_model_record_binding(
                dependency, bindings
            )
        )

        payload, judgments = self._payload_and_judgments()
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit = root / self.paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (root / self.paper / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            try:
                GATE.PAPERS = root
                with (
                    patch.object(
                        GATE, "semantic_model_review_findings", return_value=[object()]
                    ),
                    patch.object(GATE, "source_record_expected_item_digests", return_value={}),
                    patch.object(
                        GATE, "source_record_expected_item_digest_pins", return_value={}
                    ),
                ):
                    self.assertEqual(
                        GATE.current_complete_semantic_model_record_bindings(
                            self.paper, payload, judgments
                        ),
                        (),
                    )
            finally:
                GATE.PAPERS = old_papers

    def test_ambiguous_parent_or_missing_nested_closure_cannot_close_record(self) -> None:
        payload, judgments = self._payload_and_judgments()
        semantic_items = payload["semantic_model_items"]
        assert isinstance(semantic_items, list)
        semantic_items.append(deepcopy(semantic_items[0]))
        self.assertEqual(self._bindings(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        fields = payload["recursive_field_items"]
        assert isinstance(fields, list) and isinstance(fields[0], dict)
        fields[0]["nested_structures"] = ["Fixture.UnemittedNestedModel"]
        judgments["Fixture.SourceModel.kernel"] = {
            "classification": "container_recursively_audited"
        }
        self.assertEqual(self._bindings(payload, judgments), ())

    def test_cached_audit_reuse_skips_helper(self) -> None:
        payload = {"prompt_version": GATE.SOURCE_RECORD_PROMPT_VERSION}
        cached = GATE.SourceRecordAuditSnapshot(
            paper=self.paper,
            payload=payload,
            source_file_sha256="a" * 64,
            source_path=None,
        )
        with (
            patch.object(
                GATE,
                "current_saved_source_record_audit_snapshot",
                return_value=cached,
            ),
            patch.object(GATE.subprocess, "run") as run,
            patch.object(GATE.tempfile, "NamedTemporaryFile") as temporary,
        ):
            snapshot, result = GATE.acquire_source_record_audit_snapshot(self.paper)
        self.assertEqual(result.returncode, 0)
        self.assertIs(snapshot, cached)
        run.assert_not_called()
        temporary.assert_not_called()


if __name__ == "__main__":
    unittest.main()
