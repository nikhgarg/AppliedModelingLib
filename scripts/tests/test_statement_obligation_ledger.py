#!/usr/bin/env python3
"""Regression tests for semantic source/Lean obligation ledgers."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

import audit_repository  # noqa: E402
import review_dashboard  # noqa: E402
from scripts import lean_signature_manifest  # noqa: E402
from scripts import semantic_obligation_review  # noqa: E402


def valid_manifest() -> dict[str, object]:
    manifest = {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "b/0",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {
                    "tag": "app",
                    "fn": {"tag": "const", "name": "LT.lt", "levels": []},
                    "arg": {"tag": "lit", "value": "0"},
                },
                "display": "0 < x",
            },
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "result"},
                "display": "P x",
            },
        ],
    }
    manifest["sha256"] = lean_signature_manifest.signature_manifest_digest(manifest)
    return manifest


def valid_numeric_semantics_review() -> dict[str, object]:
    return {
        "formulas_present": True,
        "items": [
            {
                "id": "strict_positivity",
                "source_obligation_ids": ["s_assumption"],
                "lean_obligation_ids": ["l_assumption"],
                "source_expression": "The source assumption is the strict inequality 0 < x.",
                "lean_expression": "The Lean assumption is the strict inequality 0 < x.",
                "source_domain": "The source variable ranges over the same ordered scalar domain.",
                "lean_domain": "The Lean variable ranges over the same ordered scalar domain.",
                "source_operations": "The source applies strict less-than to zero and x.",
                "lean_operations": "Lean applies strict less-than to zero and x.",
                "source_coercions": "The source expression performs no implicit domain coercion.",
                "lean_coercions": "The Lean expression performs no implicit domain coercion.",
                "source_division": "No division operation occurs in the source expression.",
                "lean_division": "No division operation occurs in the Lean expression.",
                "source_rounding": "No rounding or truncation occurs in the source expression.",
                "lean_rounding": "No rounding or truncation occurs in the Lean expression.",
                "source_normalization": "The source expression uses the literal zero comparison directly.",
                "lean_normalization": "The Lean expression uses the literal zero comparison directly.",
                "source_strictness": "The source inequality is strict rather than weak.",
                "lean_strictness": "The Lean inequality is strict rather than weak.",
                "source_zero_denominator": "No denominator occurs in the source strict inequality.",
                "lean_zero_denominator": "No denominator occurs in the Lean strict inequality.",
                "relation": "definitionally_equal",
                "relation_basis": "Both sides state the identical strict comparison of zero with x.",
            }
        ],
        "non_numeric_source_obligation_ids": ["s_conclusion"],
        "non_numeric_lean_obligation_ids": ["l_conclusion"],
    }


def valid_discrete_semantics_review() -> dict[str, object]:
    return {
        "operations_present": False,
        "items": [],
        "non_discrete_source_obligation_ids": ["s_assumption", "s_conclusion"],
        "non_discrete_lean_obligation_ids": ["l_assumption", "l_conclusion"],
        "absence_basis": (
            "Neither reviewed proposition applies a list, ranking, support, or other discrete selector."
        ),
    }


def absent_fidelity_dimension(reason: str) -> dict[str, object]:
    return {"applicable": False, "absence_basis": reason}


def applicable_fidelity_dimension(
    source_semantics: str,
    lean_semantics: str,
    *,
    relation: str = "equivalent",
) -> dict[str, object]:
    return {
        "applicable": True,
        "source_obligation_ids": ["s_conclusion"],
        "lean_obligation_ids": ["l_conclusion"],
        "source_semantics": source_semantics,
        "lean_semantics": lean_semantics,
        "relation": relation,
        "relation_basis": (
            "The comparison expands both source and Lean semantics on the complete legal domain."
        ),
        "lean_evidence_statement": (
            "The Lean conclusion exposes the reviewed semantic relation on every legal input."
        ),
        "lean_evidence_conclusion_id": "l_conclusion",
    }


def valid_fidelity_risk_review(*, algorithmic: bool) -> dict[str, object]:
    dimensions: dict[str, object] = {
        "output_shape": absent_fidelity_dimension(
            "The scalar proposition exposes no structured sequence or trace output."
        ),
        "adversarial_action_space": absent_fidelity_dimension(
            "The proposition has no universally transformed or adversarial action family."
        ),
        "coherent_extrema_witness": absent_fidelity_dimension(
            "The proposition does not combine candidatewise or coordinatewise extrema."
        ),
        "cardinality_fibers": absent_fidelity_dimension(
            "The proposition states no exact family cardinality or realized-fiber count."
        ),
        "execution_claim_scope": absent_fidelity_dimension(
            "The proposition states no algorithm, runner, execution trace, or complexity claim."
        ),
    }
    if algorithmic:
        dimensions["execution_claim_scope"] = {
            "applicable": True,
            "source_obligation_ids": ["s_conclusion"],
            "lean_obligation_ids": ["l_conclusion"],
            "source_semantics": (
                "The source claim evaluates every legal profile with its complete executable runner."
            ),
            "lean_semantics": (
                "The Lean claim evaluates every legal profile with the same complete executable runner."
            ),
            "relation": "equivalent",
            "relation_basis": (
                "Both claims cover the identical runner, input domain, arithmetic, and returned result."
            ),
            "lean_evidence_statement": (
                "The Lean conclusion exposes the complete runner result for every legal input profile."
            ),
            "lean_evidence_conclusion_id": "l_conclusion",
            "source_input_scope": (
                "The source runner accepts every legal input object in the stated source domain."
            ),
            "lean_input_scope": (
                "The Lean runner accepts the same legal input objects in the corresponding domain."
            ),
            "source_state_transition_scope": (
                "The source claim covers every state transition and output branch of complete execution."
            ),
            "lean_state_transition_scope": (
                "The Lean claim covers the same state transition relation and output branches."
            ),
            "source_termination_scope": (
                "The source runner terminates under the stated measure on every legal input."
            ),
            "lean_termination_scope": (
                "The Lean runner uses the same termination condition on every legal input."
            ),
            "source_numeric_representation": (
                "The source uses the stated exact numeric representation throughout execution."
            ),
            "lean_numeric_representation": (
                "Lean uses the same exact numeric representation throughout the audited runner."
            ),
            "source_cost_scope": (
                "The source row claims executable correctness without a separate runtime bound."
            ),
            "lean_cost_scope": (
                "The Lean row claims executable correctness without a separate runtime bound."
            ),
            "global_claim_bridge_basis": (
                "No local-to-global promotion is needed because both sides expose the same full execution."
            ),
        }
    return {
        "schema_version": semantic_obligation_review.FIDELITY_RISK_REVIEW_VERSION,
        "dimensions": dimensions,
    }


def division_numeric_item(relation: str) -> dict[str, object]:
    return {
        "id": "division_formula",
        "source_obligation_ids": ["s_assumption"],
        "lean_obligation_ids": ["l_assumption"],
        "source_expression": "x / y in the paper formula",
        "lean_expression": "encoded division of x by y in the formal checker",
        "source_domain": "The source expression ranges over rational weighted tallies.",
        "lean_domain": "The Lean expression ranges over encoded weighted tallies.",
        "source_operations": "Division is exact field division on the source values.",
        "lean_operations": "The Lean operation computes division on its encoded values.",
        "source_coercions": "Natural support counts are coerced into the source rational field.",
        "lean_coercions": "Lean coercions into the encoded tally domain are made explicit.",
        "source_division": "The source uses exact field division without truncation.",
        "lean_division": "The Lean division convention is recorded for exact comparison.",
        "source_rounding": "The source formula performs no rounding or integer truncation.",
        "lean_rounding": "The Lean rounding or truncation behavior is stated explicitly.",
        "source_normalization": "The source evaluates the quotient before its outer normalization.",
        "lean_normalization": "Lean evaluates the quotient before the corresponding normalization.",
        "source_strictness": "The source boundary comparisons retain their printed strictness.",
        "lean_strictness": "The Lean boundary comparisons expose the same strictness question.",
        "source_zero_denominator": "The source formula is defined only on its stated nonzero denominator domain.",
        "lean_zero_denominator": "The Lean formula records whether zero denominators are rejected or totalized.",
        "relation": relation,
        "relation_basis": "The exact quotient operations are compared on every input in the reviewed domain.",
    }


def classify_operator_free(
    review: dict[str, object],
    *,
    source_ids: tuple[str, ...] = (),
    lean_ids: tuple[str, ...] = (),
) -> None:
    review["numeric_semantics_review"][
        "non_numeric_source_obligation_ids"
    ].extend(source_ids)
    review["numeric_semantics_review"][
        "non_numeric_lean_obligation_ids"
    ].extend(lean_ids)
    review["discrete_semantics_review"][
        "non_discrete_source_obligation_ids"
    ].extend(source_ids)
    review["discrete_semantics_review"][
        "non_discrete_lean_obligation_ids"
    ].extend(lean_ids)
    review["named_definition_review"][
        "non_definition_lean_obligation_ids"
    ].extend(lean_ids)


def valid_ledger() -> dict[str, object]:
    manifest = valid_manifest()
    atom_digests = {
        atom["ref"]: semantic_obligation_review.signature_manifest_atom_digest(atom)
        for atom in manifest["atoms"]
    }
    return {
        "judgment": "matches",
        "lean_signature_sha256": manifest["sha256"],
        "source_obligations": [
            {
                "id": "s_assumption",
                "kind": "assumption",
                "statement": "0 < x",
                "source_location": "Theorem 2, p. 4",
            },
            {
                "id": "s_conclusion",
                "kind": "conclusion",
                "statement": "P x",
                "source_location": "Theorem 2, p. 4",
            },
        ],
        "lean_obligations": [
            {
                "id": "l_assumption",
                "kind": "assumption",
                "signature_ref": "b/0",
                "signature_atom_sha256": atom_digests["b/0"],
            },
            {
                "id": "l_conclusion",
                "kind": "conclusion",
                "signature_ref": "result",
                "signature_atom_sha256": atom_digests["result"],
            },
        ],
        "obligation_alignment": [
            {
                "source_id": "s_assumption",
                "lean_id": "l_assumption",
                "relation": "equivalent",
                "semantic_basis": "Both formulas are strict positivity of x.",
                "bridge_statement": "For every x, 0 < x if and only if x > 0.",
            },
            {
                "source_id": "s_conclusion",
                "lean_id": "l_conclusion",
                "relation": "equivalent",
                "semantic_basis": "The propositions are identical after notation expansion.",
                "bridge_statement": "For every x, P x if and only if P x.",
            },
        ],
        "unmatched_source_conclusions": [],
        "unmatched_source_inputs": [],
        "unjustified_lean_inputs": [],
        "unmatched_lean_conclusions": [],
        "semantic_scope_review": {
            "source_quantification": "not_profile_based",
            "lean_quantification": "not_profile_based",
            "quantification_relation": "equivalent",
            "source_quantification_basis": (
                "The source theorem quantifies over an arbitrary scalar input, not profiles."
            ),
            "lean_quantification_basis": (
                "The Lean theorem quantifies over the same arbitrary scalar input, not profiles."
            ),
            "named_definition_review": {
                "definitions_present": False,
                "items": [],
                "non_definition_lean_obligation_ids": [
                    "l_assumption",
                    "l_conclusion",
                ],
                "absence_basis": (
                    "No named result-bearing predicate or wrapper occurs in the reviewed statement."
                ),
            },
            "numeric_semantics_review": valid_numeric_semantics_review(),
            "discrete_semantics_review": valid_discrete_semantics_review(),
            "algorithm_review": {
                "source_claim_level": "not_algorithmic",
                "lean_claim_level": "not_algorithmic",
                "runner_provenance": "not_applicable",
                "result_provenance": "not_applicable",
                "source_claim_basis": (
                    "The source conclusion is a mathematical proposition without an algorithm claim."
                ),
                "lean_claim_basis": (
                    "The Lean conclusion is the same proposition and exposes no computational claim."
                ),
            },
            "fidelity_risk_review": valid_fidelity_risk_review(
                algorithmic=False
            ),
            "semantic_worlds": [
                {
                    "id": "arbitrary_shared_world",
                    "role": "shared",
                    "semantics": (
                        "The source and Lean propositions range over the same "
                        "mathematical input and result."
                    ),
                }
            ],
            "world_bridges": [],
        },
    }


def valid_source_definition_semantics_review() -> dict[str, object]:
    """A complete direct-source-definition review for structural gate tests."""

    return {
        "source_obligation_ids": ["s_assumption", "s_conclusion"],
        "lean_obligation_ids": ["l_assumption", "l_conclusion"],
        "source_legal_domain": (
            "The source definition is evaluated on every scalar input satisfying its "
            "visible strict-positivity premise."
        ),
        "lean_legal_domain": (
            "The Lean definition receives the same scalar input together with the "
            "visible strict-positivity premise."
        ),
        "domain_relation": "equivalent",
        "source_outside_domain_behavior": (
            "The source leaves inputs without the stated strict-positivity premise "
            "outside the definition's legal domain."
        ),
        "lean_outside_domain_behavior": (
            "The Lean row does not claim a source interpretation for inputs that lack "
            "the visible strict-positivity premise."
        ),
        "outside_domain_relation": "equivalent",
        "source_operational_semantics": (
            "The source object evaluates the displayed scalar proposition under the "
            "legal input condition, without any hidden selector or probability law."
        ),
        "lean_operational_semantics": (
            "The Lean object evaluates the displayed scalar proposition under the same "
            "legal input condition, without a hidden operational extension."
        ),
        "operational_relation": "equivalent",
        "advertised_property_status": "no_advertised_properties",
        "advertised_properties": [],
        "no_advertised_properties_basis": (
            "The source excerpt only introduces the scalar object itself and does not "
            "state a separate optimizer, probability-law, or outcome guarantee."
        ),
    }


def ledger_error(
    ledger: dict[str, object], manifest: dict[str, object] | None = None
) -> str:
    return semantic_obligation_review.semantic_obligation_ledger_error(
        ledger, manifest or valid_manifest()
    )


def refresh_manifest_digest(
    ledger: dict[str, object], manifest: dict[str, object]
) -> None:
    manifest["sha256"] = lean_signature_manifest.signature_manifest_digest(manifest)
    ledger["lean_signature_sha256"] = manifest["sha256"]
    atoms = {atom["ref"]: atom for atom in manifest["atoms"]}
    for obligation in ledger["lean_obligations"]:
        ref = obligation.get("signature_ref")
        if ref in atoms:
            obligation["signature_atom_sha256"] = (
                semantic_obligation_review.signature_manifest_atom_digest(atoms[ref])
            )


def executable_semantic_scope_review() -> dict[str, object]:
    return {
        "source_quantification": "all_profiles",
        "lean_quantification": "all_profiles",
        "quantification_relation": "equivalent",
        "source_quantification_basis": (
            "The source statement ranges over every legal input profile in its domain."
        ),
        "lean_quantification_basis": (
            "The Lean statement ranges over every legal input profile in the same domain."
        ),
        "named_definition_review": {
            "definitions_present": False,
            "items": [],
            "non_definition_lean_obligation_ids": [
                "l_assumption",
                "l_conclusion",
            ],
            "absence_basis": (
                "The reviewed conclusion exposes runner success directly without named result wrappers."
            ),
        },
        "numeric_semantics_review": valid_numeric_semantics_review(),
        "discrete_semantics_review": valid_discrete_semantics_review(),
        "algorithm_review": {
            "source_claim_level": "executable",
            "lean_claim_level": "executable",
            "runner_provenance": "same_formalized_runner",
            "result_provenance": "runner_derived",
            "source_claim_basis": (
                "The source statement advertises the output of a specified executable procedure."
            ),
            "lean_claim_basis": (
                "The Lean statement exposes the result of executing the same formalized procedure."
            ),
            "runner_result_statement": (
                "For every legal input profile, the formalized runner's returned "
                "profile has the advertised winner."
            ),
            "runner_result_lean_conclusion_id": "l_conclusion",
        },
        "fidelity_risk_review": valid_fidelity_risk_review(algorithmic=True),
        "semantic_worlds": [
            {
                "id": "world_1",
                "role": "shared",
                "semantics": (
                    "The source executor and Lean runner operate on the same legal "
                    "profiles and return the same result object."
                ),
            }
        ],
        "world_bridges": [],
    }


def valid_operational_complexity_review() -> dict[str, object]:
    work_descriptions = {
        "traversal_enumeration_length": (
            "Every recursive scan is charged by the length of the traversed input sequence."
        ),
        "duplicate_multiplicity": (
            "Repeated entries remain in the scan and each repeated visit contributes one charge."
        ),
        "materialization_rebuilding": (
            "Each constructed intermediate container is charged by the number of elements written."
        ),
        "representation_container_primitives": (
            "Lookup, insertion, comparison, and container reads use the stated representation costs."
        ),
        "exact_rational_bit_growth": (
            "Numerator and denominator growth is charged under the stated binary rational model."
        ),
    }
    return {
        "schema_version": semantic_obligation_review.OPERATIONAL_COMPLEXITY_REVIEW_VERSION,
        "executor_semantics": (
            "The audited executor recursively consumes one state and its materialized successor data."
        ),
        "input_domain": (
            "The bound ranges over every legal encoded profile and candidate set admitted by the theorem."
        ),
        "input_size_measure": (
            "Input size is the total binary encoding length of candidates, rankings, and rational weights."
        ),
        "dependency_graph": {
            "nodes": [
                {
                    "id": "entry_route",
                    "operation_semantics": (
                        "The root evaluates the current state, scans its entries, and dispatches recursion."
                    ),
                    "reachable_branch_domain": (
                        "This operation is reached for every legal nonterminal input state."
                    ),
                    "work_accounting_categories": [
                        "traversal_enumeration_length",
                        "duplicate_multiplicity",
                        "materialization_rebuilding",
                    ],
                },
                {
                    "id": "successor_route",
                    "operation_semantics": (
                        "The dependency constructs and evaluates the successor using encoded container operations."
                    ),
                    "reachable_branch_domain": (
                        "It is reached on every successful nonterminal branch before the recursive call."
                    ),
                    "work_accounting_categories": [
                        "representation_container_primitives",
                        "exact_rational_bit_growth",
                    ],
                },
            ],
            "edges": [
                {
                    "from_node_id": "entry_route",
                    "to_node_id": "successor_route",
                    "invocation_semantics": (
                        "A nonterminal state invokes successor construction before continuing recursion."
                    ),
                    "branch_condition": (
                        "The edge is taken for every legal branch whose current state is nonterminal."
                    ),
                }
            ],
            "root_node_ids": ["entry_route"],
            "transitive_closure_complete": True,
            "all_reachable_branches_complete": True,
            "coverage_basis": (
                "The graph follows every operation evaluated by every success, failure, and recursive branch."
            ),
        },
        "worst_case_recurrence": (
            "T(s) is bounded by T(s-1) plus the charged traversal, construction, and arithmetic work."
        ),
        "worst_case_bound": (
            "Solving the recurrence gives a polynomial in the stated binary input-size measure."
        ),
        "complexity_lean_conclusion_id": "l_conclusion",
        "complexity_statement_binding": (
            "The recurrence and work ledger establish the operation bound asserted by the Lean conclusion."
        ),
        "work_accounting": [
            {
                "category": category,
                "status": "charged",
                "operation_semantics": description,
                "worst_case_charge_or_absence_basis": (
                    "The worst-case recurrence includes this work at every branch where it is evaluated."
                ),
                "evidence_basis": (
                    "The dependency graph and cost-threaded equations expose these operations directly."
                ),
            }
            for category, description in work_descriptions.items()
        ],
        "closure_elimination": {
            "material": False,
            "non_material_basis": (
                "The claimed polynomial bound does not rely on eliminating a prior closure computation."
            ),
        },
    }


def valid_polynomial_ledger() -> dict[str, object]:
    ledger = valid_ledger()
    review = executable_semantic_scope_review()
    algorithm = review["algorithm_review"]
    algorithm["source_claim_level"] = "polynomial_time"
    algorithm["lean_claim_level"] = "polynomial_time"
    algorithm["complexity_statement"] = (
        "The audited runner uses a polynomial number of bit operations on every legal input."
    )
    algorithm["arithmetic_model"] = (
        "Exact rationals use binary numerators and denominators with bit-operation costs."
    )
    algorithm["complexity_lean_conclusion_id"] = "l_conclusion"
    ledger["semantic_scope_review"] = review
    ledger["operational_complexity_review"] = valid_operational_complexity_review()
    return ledger


class StatementObligationLedgerTests(unittest.TestCase):
    def test_visible_premise_boundary_alias_preserves_legacy_sidecars(self) -> None:
        self.assertEqual(
            review_dashboard._normalize_llm_match_resolution(
                "visible-premise boundary"
            ),
            semantic_obligation_review.CONDITIONAL_BOUNDARY_RESOLUTION,
        )
        self.assertEqual(
            review_dashboard._normalize_paper_coverage_judgment(
                "visible_premise_boundary"
            ),
            semantic_obligation_review.CONDITIONAL_BOUNDARY_RESOLUTION,
        )

    def test_complete_semantic_ledger_is_accepted(self) -> None:
        self.assertEqual(ledger_error(valid_ledger()), "")

    def test_direct_source_definition_review_fails_closed_and_accepts_complete_review(
        self,
    ) -> None:
        ledger = valid_ledger()
        self.assertIn(
            "source-expression route lacks",
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
        )
        ledger["semantic_scope_review"][  # type: ignore[index]
            "source_definition_semantics_review"
        ] = valid_source_definition_semantics_review()
        self.assertEqual(
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
            "",
        )

    def test_direct_source_definition_review_rejects_totalization_mismatch(self) -> None:
        ledger = valid_ledger()
        review = valid_source_definition_semantics_review()
        review["outside_domain_relation"] = "lean_stronger"
        ledger["semantic_scope_review"][  # type: ignore[index]
            "source_definition_semantics_review"
        ] = review
        self.assertIn(
            "non-equivalent source-definition outside-domain/totalization behavior",
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
        )

    def test_direct_source_definition_review_requires_advertised_property_evidence(
        self,
    ) -> None:
        ledger = valid_ledger()
        review = valid_source_definition_semantics_review()
        review["advertised_property_status"] = "properties_reviewed"
        review["advertised_properties"] = []
        ledger["semantic_scope_review"][  # type: ignore[index]
            "source_definition_semantics_review"
        ] = review
        self.assertIn(
            "requires at least one advertised property",
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
        )

        review["advertised_properties"] = [
            {
                "id": "attainment",
                "source_property": (
                    "The source definition advertises that its selected output attains "
                    "the displayed objective on every legal input."
                ),
                "lean_realization": (
                    "The Lean row exposes the corresponding attainment proposition as "
                    "its exact paper-facing conclusion."
                ),
                "source_obligation_ids": ["s_conclusion"],
                "lean_obligation_ids": ["l_conclusion"],
                "relation": "equivalent",
                "lean_evidence_kind": "missing",
                "evidence_basis": (
                    "The reviewed source and Lean conclusion obligations are the exact "
                    "attainment statements for the selected output."
                ),
            }
        ]
        self.assertIn(
            "without Lean evidence",
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
        )

        property_item = review["advertised_properties"][0]
        assert isinstance(property_item, dict)
        property_item.update(
            {
                "lean_evidence_kind": "paper_interface_conclusion",
                "lean_evidence_conclusion_id": "l_conclusion",
            }
        )
        self.assertEqual(
            semantic_obligation_review.semantic_obligation_ledger_error(
                ledger,
                valid_manifest(),
                require_source_definition_semantics_review=True,
            ),
            "",
        )

    def test_source_definition_endpoint_cannot_be_routed_as_component(self) -> None:
        source_statement = "P x"
        source_location = "source.txt:1-1"
        source_digest = review_dashboard.statement_digest(source_statement)
        ledger = valid_ledger()
        conclusion = ledger["source_obligations"][1]
        assert isinstance(conclusion, dict)
        conclusion.update(
            {
                "source_item": "source_definition",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "statement": source_statement,
            }
        )
        ledger["source_routes"] = [
            {
                "source_item": "source_definition",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "route_kind": "source_component",
                "semantic_relation": "equivalent_source_component",
                "source_support_scope": (
                    "The source component is the complete displayed definition used by "
                    "the reviewed endpoint on every legal scalar input."
                ),
                "lean_evidence_ids": ["l_conclusion"],
            }
        ]
        inventory = {
            "source_definition": {
                "statement": source_statement,
                "statement_sha256": source_digest,
                "source_location": source_location,
                "source_kind": "definition",
            }
        }
        self.assertIn(
            "source-result/definition endpoint obligations",
            review_dashboard.source_route_pin_error(ledger, inventory=inventory),
        )

    def test_source_definition_coverage_requires_a_direct_route(self) -> None:
        source_statement = "P x"
        source_location = "source.txt:1-1"
        source_digest = review_dashboard.statement_digest(source_statement)
        source_item = {
            "statement": source_statement,
            "statement_sha256": source_digest,
            "source_location": source_location,
            "source_kind": "definition",
        }
        row = review_dashboard.ReviewItem(
            name="arbitrary_navigation_label",
            kind="def",
            lean_statement="def arbitrary_navigation_label : Prop := P x",
            paper_statement=source_statement,
            agent_statement=source_statement,
            llm_match_source_routes=[
                {
                    "source_item": "unrelated_map_key",
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "route_kind": "source_component",
                    "semantic_relation": "equivalent_source_component",
                }
            ],
        )
        self.assertIn(
            "row route is not one of `direct`",
            review_dashboard._coverage_route_error(
                "another_navigation_key",
                source_item,
                row,
            ),
        )

    def test_loader_versions_direct_expression_semantics_review(
        self,
    ) -> None:
        source_statement = "P x"
        source_location = "source.txt:1-1"
        source_digest = review_dashboard.statement_digest(source_statement)

        def direct_ledger(source_item: str) -> dict[str, object]:
            ledger = valid_ledger()
            ledger["paper_statement_sha256"] = source_digest
            ledger["tex_statement_sha256"] = review_dashboard.statement_digest(
                "P x"
            )
            conclusion = ledger["source_obligations"][1]
            assert isinstance(conclusion, dict)
            conclusion.update(
                {
                    "source_item": source_item,
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "statement": source_statement,
                }
            )
            ledger["source_routes"] = [
                {
                    "source_item": source_item,
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "route_kind": "direct",
                }
            ]
            return ledger

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            status = {
                "review_surface": {
                    "llm_statement_review": {
                        "require_explicit_source_routes": True
                    }
                }
            }
            (folder / "status.json").write_text(
                json.dumps(status),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_definition": {
                                "statement": source_statement,
                                "statement_sha256": source_digest,
                                "source_location": source_location,
                                "source_kind": "definition",
                            },
                            "source_theorem": {
                                "statement": source_statement,
                                "statement_sha256": source_digest,
                                "source_location": source_location,
                                "source_kind": "theorem",
                            },
                            "source_formula": {
                                "statement": source_statement,
                                "statement_sha256": source_digest,
                                "source_location": source_location,
                                "source_kind": "formula",
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )

            def load(ledger: dict[str, object]) -> dict[str, object]:
                (audit / "statement_match_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            # This fixture isolates legacy route-policy behavior.  It
                            # predates the v11 verbatim-source-input credential.
                            "prompt_version": "statement-match-v10-semantic-fidelity-seat-stopping",
                            "validator": "test-model",
                            "validator_type": "agent",
                            "validated_at": "2026-07-26T00:00:00Z",
                            "items": {"row": ledger},
                        }
                    ),
                    encoding="utf-8",
                )
                return review_dashboard.load_llm_statement_judgments(
                    folder, {"row": valid_manifest()}
                )["row"]

            definition_row = load(direct_ledger("source_definition"))
            self.assertIn(
                "source-expression route lacks",
                str(definition_row["obligation_ledger_error"]),
            )

            formula_row = load(direct_ledger("source_formula"))
            self.assertEqual(
                formula_row["obligation_ledger_error"],
                "",
            )

            reviewed_definition_ledger = direct_ledger("source_definition")
            reviewed_definition_ledger["semantic_scope_review"][  # type: ignore[index]
                "source_definition_semantics_review"
            ] = valid_source_definition_semantics_review()
            self.assertEqual(
                load(reviewed_definition_ledger)["obligation_ledger_error"], ""
            )
            # Formula-like endpoints stay on the legacy route policy unless a
            # paper opts into the exact direct-expression protocol version.
            status["review_surface"]["llm_statement_review"][  # type: ignore[index]
                "require_direct_expression_semantics_review"
            ] = True
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            self.assertEqual(
                load(direct_ledger("source_formula"))["obligation_ledger_error"],
                "",
            )

            status["review_surface"]["llm_statement_review"][  # type: ignore[index]
                "require_direct_expression_semantics_review"
            ] = "v1"
            (folder / "status.json").write_text(
                json.dumps(status), encoding="utf-8"
            )
            self.assertIn(
                "source-expression route lacks",
                str(load(direct_ledger("source_formula"))["obligation_ledger_error"]),
            )

            reviewed_formula_ledger = direct_ledger("source_formula")
            reviewed_formula_ledger["semantic_scope_review"][  # type: ignore[index]
                "source_definition_semantics_review"
            ] = valid_source_definition_semantics_review()
            self.assertEqual(
                load(reviewed_formula_ledger)["obligation_ledger_error"], ""
            )
            self.assertEqual(
                load(direct_ledger("source_theorem"))["obligation_ledger_error"],
                "",
            )

    def test_explicit_source_routes_pin_semantic_source_obligations(self) -> None:
        """An enabled v10 paper cannot route a theorem through a model condition."""

        manifest = valid_manifest()
        ledger = valid_ledger()
        source_statement = "P x"
        source_location = "source.txt:1-1"
        source_digest = review_dashboard.statement_digest(source_statement)
        ledger["paper_statement_sha256"] = source_digest
        ledger["tex_statement_sha256"] = review_dashboard.statement_digest(
            "P x"
        )
        conclusion = ledger["source_obligations"][1]
        conclusion.update(
            {
                "source_item": "source_theorem",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "statement": source_statement,
            }
        )
        ledger["source_routes"] = [
            {
                "source_item": "source_theorem",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "route_kind": "direct",
            }
        ]

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "llm_statement_review": {
                                "require_explicit_source_routes": True
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_theorem": {
                                "statement": source_statement,
                                "source_location": source_location,
                                "source_kind": "theorem",
                                "lean_declarations": ["row"],
                            },
                            "source_model": {
                                "statement": source_statement,
                                "source_location": source_location,
                                "source_kind": "assumption",
                                "lean_declarations": ["row"],
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        # This fixture isolates legacy route-policy behavior.  It
                        # predates the v11 verbatim-source-input credential.
                        "prompt_version": "statement-match-v10-semantic-fidelity-seat-stopping",
                        "validator": "test-model",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T00:00:00Z",
                        "items": {"row": ledger},
                    }
                ),
                encoding="utf-8",
            )
            loaded = review_dashboard.load_llm_statement_judgments(
                folder, {"row": manifest}
            )
            self.assertEqual(loaded["row"]["source_route_error"], "")

            # The same statement text does not make an assumption a valid
            # direct theorem route.  The route kind and source-map semantics
            # are checked independently of the declaration spelling.
            ledger["source_routes"][0]["source_item"] = "source_model"
            conclusion["source_item"] = "source_model"
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v10-semantic-fidelity-seat-stopping",
                        "validator": "test-model",
                        "validator_type": "agent",
                        "validated_at": "2026-07-24T00:00:00Z",
                        "items": {"row": ledger},
                    }
                ),
                encoding="utf-8",
            )
            loaded = review_dashboard.load_llm_statement_judgments(
                folder, {"row": manifest}
            )
            self.assertIn(
                "model/assumption convention", loaded["row"]["source_route_error"]
            )

    def test_v11_route_requires_the_verbatim_source_anchor_bundle(self) -> None:
        """A v11 semantic match cannot substitute a map paraphrase for raw text."""

        source_statement = "The curator's navigation summary."
        source_quote = "\\begin{proposition}\\n  Raw source claim.\\n\\end{proposition}"
        source_location = "source.tex:10-12"
        source_digest = review_dashboard.statement_digest(source_statement)
        source_item = {
            "statement": source_statement,
            "statement_sha256": source_digest,
            "source_location": source_location,
            "source_kind": "theorem",
            "spec_lean_declarations": ["Test.rowSpec"],
            "source_anchor_evidence": [
                {
                    "path": "source.tex",
                    "line_start": 10,
                    "line_end": 12,
                    "quoted_text": source_quote,
                    "quoted_text_sha256": hashlib.sha256(
                        source_quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
        }
        anchor_identity, error = review_dashboard.source_anchor_quote_identity(
            source_item
        )
        self.assertEqual(error, "")
        _source_input, source_input_identity, source_input_error = (
            review_dashboard.source_semantic_input_bundle(source_item)
        )
        self.assertEqual(source_input_error, "")
        ledger = valid_ledger()
        # The paper target is the literal raw source text, whereas the v11
        # source-input identity also commits to its anchor/provenance bundle.
        # Those are intentionally different digests.
        ledger["paper_statement_sha256"] = review_dashboard.statement_digest(
            source_quote
        )
        ledger["tex_statement_sha256"] = review_dashboard.statement_digest("P x")
        ledger["source_input_protocol"] = "verbatim_source_anchor_bundle_v1"
        ledger["source_input_bundle_sha256"] = source_input_identity
        ledger["lean_target_protocol"] = "expanded_paperinterface_spec_v1"
        ledger["semantic_target_declaration"] = "Test.rowSpec"
        conclusion = ledger["source_obligations"][1]
        assert isinstance(conclusion, dict)
        conclusion.update(
            {
                "source_item": "theorem",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "source_anchor_quote_identity_sha256": anchor_identity,
                "source_input_bundle_sha256": source_input_identity,
                "statement": source_statement,
            }
        )
        ledger["source_routes"] = [
            {
                "source_item": "theorem",
                "source_statement_sha256": source_digest,
                "source_location": source_location,
                "source_anchor_quote_identity_sha256": anchor_identity,
                "route_kind": "direct",
            }
        ]
        self.assertEqual(
            review_dashboard.source_route_pin_error(
                ledger,
                inventory={"theorem": source_item},
                require_statement_target=True,
                require_verbatim_source_inputs=True,
            ),
            "",
        )
        conclusion.pop("source_anchor_quote_identity_sha256")
        self.assertIn(
            "no exact equivalent source-conclusion binding",
            review_dashboard.source_route_pin_error(
                ledger,
                inventory={"theorem": source_item},
                require_statement_target=True,
                require_verbatim_source_inputs=True,
            ),
        )

    def test_v11_context_requires_a_bounded_source_semantic_role(self) -> None:
        """Raw context may interpret a claim but cannot be unnamed proof material."""

        claim = "Raw displayed claim."
        context = "Raw source construction."
        source_item: dict[str, object] = {
            "source_anchor_evidence": [
                {
                    "quoted_text": claim,
                    "quoted_text_sha256": hashlib.sha256(claim.encode("utf-8")).hexdigest(),
                }
            ],
            "semantic_context_requirements": [
                {
                    "source_anchor_evidence": [
                        {
                            "quoted_text": context,
                            "quoted_text_sha256": hashlib.sha256(
                                context.encode("utf-8")
                            ).hexdigest(),
                        }
                    ]
                }
            ],
        }
        _text, _identity, error = review_dashboard.source_semantic_input_bundle(
            source_item,
            require_context_roles=True,
        )
        self.assertIn("no permitted semantic_role", error)

        requirement = source_item["semantic_context_requirements"][0]  # type: ignore[index]
        assert isinstance(requirement, dict)
        requirement["semantic_role"] = "model_construction"
        _text, identity, error = review_dashboard.source_semantic_input_bundle(
            source_item,
            require_context_roles=True,
        )
        self.assertEqual(error, "")
        self.assertRegex(identity, r"^[0-9a-f]{64}$")

    def test_direct_route_rejects_partial_model_and_defect_laundering(self) -> None:
        """Only an exact ordinary source endpoint can use the direct route."""

        def item(
            statement: str,
            location: str,
            source_kind: str,
            source_status: str = "",
        ) -> dict[str, object]:
            return {
                "statement": statement,
                "statement_sha256": review_dashboard.statement_digest(statement),
                "source_location": location,
                "source_kind": source_kind,
                "source_status": source_status,
            }

        def direct_ledger(
            source_item: str,
            source_statement: str,
            source_location: str,
            obligation_statement: str,
        ) -> dict[str, object]:
            ledger = valid_ledger()
            ledger["paper_statement_sha256"] = review_dashboard.statement_digest(
                source_statement
            )
            ledger["tex_statement_sha256"] = review_dashboard.statement_digest(
                "P x"
            )
            conclusion = ledger["source_obligations"][1]
            assert isinstance(conclusion, dict)
            conclusion.update(
                {
                    "source_item": source_item,
                    "source_statement_sha256": review_dashboard.statement_digest(
                        source_statement
                    ),
                    "source_location": source_location,
                    "statement": obligation_statement,
                }
            )
            ledger["source_routes"] = [
                {
                    "source_item": source_item,
                    "source_statement_sha256": review_dashboard.statement_digest(
                        source_statement
                    ),
                    "source_location": source_location,
                    "route_kind": "direct",
                }
            ]
            return ledger

        full_result = "Every legal setting satisfies both the transport and mixture equations."
        partial_component = "The transport equation holds for the selected component."
        model_statement = "The source model uses an event-level calibration convention."
        defect_statement = "The printed formula has the stated invalid denominator."
        inventory = {
            "source_result": item(full_result, "source.txt:10-11", "theorem"),
            "source_model": item(model_statement, "source.txt:12-12", "model"),
            "source_defect": item(
                defect_statement,
                "source.txt:13-13",
                "formula",
                "quarantined_source_defect",
            ),
        }

        with self.subTest("partial component cannot claim the full theorem endpoint"):
            error = review_dashboard.source_route_pin_error(
                direct_ledger(
                    "source_result",
                    full_result,
                    "source.txt:10-11",
                    partial_component,
                ),
                inventory=inventory,
            )
            self.assertIn("no exact equivalent source-conclusion binding", error)

        with self.subTest("model convention cannot be labeled direct"):
            error = review_dashboard.source_route_pin_error(
                direct_ledger(
                    "source_model",
                    model_statement,
                    "source.txt:12-12",
                    model_statement,
                ),
                inventory=inventory,
            )
            self.assertIn("model/assumption convention", error)

        with self.subTest("quarantined defect cannot be labeled direct"):
            error = review_dashboard.source_route_pin_error(
                direct_ledger(
                    "source_defect",
                    defect_statement,
                    "source.txt:13-13",
                    defect_statement,
                ),
                inventory=inventory,
            )
            self.assertIn("quarantined or support-only", error)

    def test_approved_corrected_target_route_is_pinned_to_the_repaired_statement(self) -> None:
        """Corrected-source credit is bound to math and source pins, not names."""

        archival = "The archival theorem has the false unrestricted conclusion."
        corrected = "Under the visible three-point convention, the repaired conclusion holds."
        archival_locator = "source.txt:40-42"
        target = {
            "schema": 1,
            "statement": corrected,
            "governing_defect_ids": ["FIXTURE-FALSE-STATEMENT"],
            "archival_equivalence_claimed": False,
            "archival_source_locator": archival_locator,
            "archival_source_quote_sha256": "a" * 64,
            "approval": {
                "kind": "explicit_user_instruction",
                "recorded_at": "2026-07-25",
                "reference": "The visible convention is approved only for the repaired target.",
                "target_statement_sha256": review_dashboard.statement_digest(corrected),
                "artifact_path": "docs/approval.md",
                "artifact_sha256": "b" * 64,
            },
        }
        target["corrected_target_sha256"] = review_dashboard.corrected_target_digest(
            target
        )
        inventory = {
            "opaque_source_key": {
                "statement": archival,
                "statement_sha256": review_dashboard.statement_digest(archival),
                "source_location": "source.txt:1-99",
                "source_kind": "theorem",
                "source_defect_ids": ["FIXTURE-FALSE-STATEMENT"],
                "coverage_status": "corrected_source_statement",
                "lean_declarations": ["repaired_complete_endpoint"],
                "corrected_target": target,
            }
        }

        def ledger() -> dict[str, object]:
            result = valid_ledger()
            conclusion = result["source_obligations"][1]
            assert isinstance(conclusion, dict)
            conclusion.update(
                {
                    "source_item": "opaque_source_key",
                    "source_statement_sha256": review_dashboard.statement_digest(corrected),
                    "source_location": archival_locator,
                    "statement": corrected,
                }
            )
            result["resolution"] = "approved_corrected_target"
            result["source_routes"] = [
                {
                    "source_item": "opaque_source_key",
                    "source_statement_sha256": review_dashboard.statement_digest(corrected),
                    "source_location": archival_locator,
                    "route_kind": "approved_corrected_target",
                    "semantic_relation": "proves_approved_corrected_target",
                    "archival_statement_sha256": review_dashboard.statement_digest(archival),
                    "archival_source_location": archival_locator,
                    "corrected_target_sha256": target["corrected_target_sha256"],
                    "governing_defect_ids": ["FIXTURE-FALSE-STATEMENT"],
                    "archival_equivalence_claimed": False,
                    "approval_artifact_sha256": "b" * 64,
                }
            ]
            return result

        self.assertEqual(
            review_dashboard.source_route_pin_error(ledger(), inventory=inventory), ""
        )

        direct = ledger()
        direct["source_routes"][0]["route_kind"] = "direct"  # type: ignore[index]
        self.assertIn(
            "approved correction", review_dashboard.source_route_pin_error(direct, inventory=inventory)
        )

        archival_conclusion = ledger()
        conclusion = archival_conclusion["source_obligations"][1]  # type: ignore[index]
        assert isinstance(conclusion, dict)
        conclusion["statement"] = archival
        conclusion["source_statement_sha256"] = review_dashboard.statement_digest(archival)
        self.assertIn(
            "no exact equivalent corrected-target conclusion binding",
            review_dashboard.source_route_pin_error(archival_conclusion, inventory=inventory),
        )

        wrong_defect = ledger()
        wrong_defect["source_routes"][0]["governing_defect_ids"] = ["OTHER"]  # type: ignore[index]
        self.assertIn(
            "exact governing", review_dashboard.source_route_pin_error(wrong_defect, inventory=inventory)
        )

        missing_approval = ledger()
        missing_approval["source_routes"][0].pop("approval_artifact_sha256")  # type: ignore[index]
        self.assertIn(
            "approval artifact", review_dashboard.source_route_pin_error(missing_approval, inventory=inventory)
        )

        false_equivalence_inventory = copy.deepcopy(inventory)
        false_equivalence_inventory["opaque_source_key"]["corrected_target"][
            "archival_equivalence_claimed"
        ] = True
        self.assertIn(
            "archival_equivalence_claimed",
            review_dashboard.source_route_pin_error(
                ledger(), inventory=false_equivalence_inventory
            ),
        )

    def test_scoped_component_and_model_routes_need_no_fabricated_endpoint(self) -> None:
        """A component or convention can be honest without claiming full equivalence."""

        component_statement = "The finite witness preserves the selected transport equation."
        component_location = "source.txt:20-21"
        model_statement = "Calibration is interpreted through event probabilities on reported values."
        model_location = "source.txt:22-23"
        inventory = {
            "source_component": {
                "statement": component_statement,
                "statement_sha256": review_dashboard.statement_digest(component_statement),
                "source_location": component_location,
                "source_kind": "formula",
                "source_status": "",
            },
            "source_model": {
                "statement": model_statement,
                "statement_sha256": review_dashboard.statement_digest(model_statement),
                "source_location": model_location,
                "source_kind": "model",
                "source_status": "",
            },
        }
        ledger = valid_ledger()
        ledger["source_routes"] = [
            {
                "source_item": "source_component",
                "source_statement_sha256": review_dashboard.statement_digest(
                    component_statement
                ),
                "source_location": component_location,
                "route_kind": "source_component",
                "semantic_relation": "lean_implies_source_component",
                "source_support_scope": (
                    "The Lean conclusion proves the finite transport equation needed by "
                    "the mixture construction on every listed component."
                ),
                "lean_evidence_ids": ["l_conclusion"],
            },
            {
                "source_item": "source_model",
                "source_statement_sha256": review_dashboard.statement_digest(
                    model_statement
                ),
                "source_location": model_location,
                "route_kind": "source_model_convention",
                "semantic_relation": "shared_model_convention",
                "source_support_scope": (
                    "The model route records the shared event-calibration convention before "
                    "any theorem conclusion is compared."
                ),
                "lean_evidence_ids": ["l_assumption"],
            },
        ]

        source_items_in_conclusions = {
            str(obligation.get("source_item") or "")
            for obligation in ledger["source_obligations"]
            if isinstance(obligation, dict)
            and str(obligation.get("kind") or "").lower() == "conclusion"
        }
        self.assertNotIn("source_component", source_items_in_conclusions)
        self.assertNotIn("source_model", source_items_in_conclusions)
        self.assertEqual(
            review_dashboard.source_route_pin_error(
                ledger,
                inventory=inventory,
            ),
            "",
        )

    def test_statement_target_receipt_requires_exact_equivalence_route(self) -> None:
        """A content-pinned v10 match cannot be certified by context alone."""

        source_statement = "The source model defines the positive calibration index."
        source_location = "source.txt:22-23"
        source_digest = review_dashboard.statement_digest(source_statement)
        inventory = {
            "source_model": {
                "statement": source_statement,
                "statement_sha256": source_digest,
                "source_location": source_location,
                "source_kind": "model",
                "source_status": "",
            }
        }

        def model_ledger(relation: str) -> dict[str, object]:
            ledger = valid_ledger()
            ledger["paper_statement_sha256"] = source_digest
            ledger["tex_statement_sha256"] = review_dashboard.statement_digest(
                "The calibration index is represented in Lean."
            )
            conclusion = ledger["source_obligations"][1]
            assert isinstance(conclusion, dict)
            conclusion.update(
                {
                    "source_item": "source_model",
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "statement": source_statement,
                }
            )
            ledger["source_routes"] = [
                {
                    "source_item": "source_model",
                    "source_statement_sha256": source_digest,
                    "source_location": source_location,
                    "route_kind": "source_model_convention",
                    "semantic_relation": relation,
                    "source_support_scope": (
                        "The source-model route records the complete displayed calibration "
                        "definition and the Lean conclusion expands that same real-valued index."
                    ),
                    "lean_evidence_ids": ["l_conclusion"],
                }
            ]
            return ledger

        contextual = model_ledger("shared_model_convention")
        self.assertIn(
            "no exact equivalence-bearing source route",
            review_dashboard.source_route_pin_error(
                contextual,
                inventory=inventory,
                require_statement_target=True,
            ),
        )
        self.assertEqual(
            review_dashboard.source_route_pin_error(
                model_ledger("equivalent_model_convention"),
                inventory=inventory,
                require_statement_target=True,
            ),
            "",
        )

        blank = model_ledger("equivalent_model_convention")
        blank["paper_statement_sha256"] = review_dashboard.statement_digest("")
        self.assertIn(
            "empty paper-statement target receipt",
            review_dashboard.source_route_pin_error(
                blank,
                inventory=inventory,
                require_statement_target=True,
            ),
        )

        stale_comment = model_ledger("equivalent_model_convention")
        stale_comment["paper_statement_sha256"] = review_dashboard.statement_digest(
            "A generated Lean doc comment."
        )
        self.assertIn(
            "not bound by any current explicit source route",
            review_dashboard.source_route_pin_error(
                stale_comment,
                inventory=inventory,
                require_statement_target=True,
            ),
        )

    def test_stale_check_rejects_blank_current_paper_statement(self) -> None:
        judgment = {
            "lean_signature_sha256": "a" * 64,
            "lean_statement_sha256": review_dashboard.statement_digest("theorem row : P"),
            "paper_statement_sha256": review_dashboard.statement_digest(""),
            "tex_statement_sha256": review_dashboard.statement_digest("T"),
        }

        self.assertTrue(
            review_dashboard._llm_statement_judgment_is_stale(
                judgment,
                signature_sha256="a" * 64,
                lean_statement="theorem row : P",
                paper_statement="",
                agent_statement="T",
            )
        )

    def test_stale_check_rejects_changed_lean_text_with_same_signature(self) -> None:
        judgment = {
            "lean_signature_sha256": "a" * 64,
            "lean_statement_sha256": review_dashboard.statement_digest(
                "theorem row : P"
            ),
            "paper_statement_sha256": review_dashboard.statement_digest("P"),
            "tex_statement_sha256": review_dashboard.statement_digest("P"),
        }

        self.assertTrue(
            review_dashboard._llm_statement_judgment_is_stale(
                judgment,
                signature_sha256="a" * 64,
                lean_statement="theorem row (h : Q) : P",
                paper_statement="P",
                agent_statement="P",
            )
        )

    def test_v10_fails_closed_without_semantic_scope_review(self) -> None:
        ledger = valid_ledger()
        del ledger["semantic_scope_review"]
        self.assertIn("semantic_scope_review", ledger_error(ledger))

    def test_v10_fails_closed_without_numeric_semantics_review(self) -> None:
        ledger = valid_ledger()
        del ledger["semantic_scope_review"]["numeric_semantics_review"]
        self.assertIn("numeric_semantics_review", ledger_error(ledger))

    def test_v10_fails_closed_without_discrete_semantics_review(self) -> None:
        ledger = valid_ledger()
        del ledger["semantic_scope_review"]["discrete_semantics_review"]
        self.assertIn("discrete_semantics_review", ledger_error(ledger))

    def test_v10_fails_closed_without_fidelity_risk_review(self) -> None:
        ledger = valid_ledger()
        del ledger["semantic_scope_review"]["fidelity_risk_review"]
        self.assertIn("fidelity_risk_review", ledger_error(ledger))

    def test_output_shape_rejects_hidden_terminal_component(self) -> None:
        ledger = valid_ledger()
        shape = applicable_fidelity_dimension(
            "The paper structure contains m candidates followed by exactly m minus one round labels.",
            "The Lean target compares m candidates followed by all m executor labels including the terminal label.",
            relation="lean_stronger",
        )
        shape.update(
            {
                "source_output_shape": (
                    "The source output is a candidate permutation plus exactly m minus one labels."
                ),
                "lean_output_shape": (
                    "The Lean output is a candidate permutation plus all m executor labels."
                ),
                "projection_terminal_policy": (
                    "The source omits the terminal component while the unprojected Lean target retains it."
                ),
                "arity_basis": (
                    "The source definition and expanded executor trace give different label lengths."
                ),
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "output_shape"
        ] = shape
        self.assertIn("non-equivalent `output_shape`", ledger_error(ledger))

    def test_fidelity_evidence_conclusion_must_be_in_dimension_obligations(self) -> None:
        ledger = valid_ledger()
        shape = applicable_fidelity_dimension(
            "The source returns one projected structured output on every legal input.",
            "Lean returns the same projected structured output on every legal input.",
        )
        shape["lean_obligation_ids"] = ["l_assumption"]
        shape.update(
            {
                "source_output_shape": (
                    "The source output has one explicitly projected terminal component."
                ),
                "lean_output_shape": (
                    "The Lean output has the same explicitly projected terminal component."
                ),
                "projection_terminal_policy": (
                    "Both sides remove the same terminal field before comparing results."
                ),
                "arity_basis": (
                    "The expanded source and Lean structures have equal component lengths."
                ),
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "output_shape"
        ] = shape
        self.assertIn("not among its reviewed Lean obligations", ledger_error(ledger))

    def test_adversarial_action_space_rejects_vacuity(self) -> None:
        ledger = valid_ledger()
        action = applicable_fidelity_dimension(
            "The source universally quantifies over every legal duplicate-free candidate prefix.",
            "The Lean predicate quantifies only over transformed ballots that remain valid after prefixing.",
        )
        action.update(
            {
                "source_action_space": (
                    "Every prefix drawn from the allowed carrier is a source adversarial action."
                ),
                "lean_action_space": (
                    "A transformed ballot is retained only when prefixing creates no duplicate candidate."
                ),
                "carrier_capacity_basis": (
                    "The retained carrier and seat capacity are compared before universal quantification."
                ),
                "duplicate_interaction_basis": (
                    "A selected strategy ballot may already contain a prefixed candidate and become invalid."
                ),
                "nonvacuity_basis": (
                    "The source family is inhabited, but the Lean validity filter may erase every action."
                ),
                "source_nonvacuous": True,
                "lean_nonvacuous": False,
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "adversarial_action_space"
        ] = action
        self.assertIn("vacuous or ill-formed", ledger_error(ledger))

    def test_candidatewise_extrema_need_one_coherent_witness(self) -> None:
        ledger = valid_ledger()
        extrema = applicable_fidelity_dimension(
            "The source allocation combines each candidate's separately maximized transfer bound.",
            "The Lean arithmetic combines the same separately witnessed candidatewise transfer bounds.",
        )
        extrema.update(
            {
                "source_extrema_semantics": (
                    "Each rival coordinate is maximized over the admissible completion family."
                ),
                "lean_extrema_semantics": (
                    "Lean inserts every rival's independent maximum into one allocation vector."
                ),
                "coherent_witness_basis": (
                    "The available witnesses realize different rival maxima and cannot be merged."
                ),
                "runner_refinement_basis": (
                    "No actual runner execution or refinement theorem realizes the combined vector."
                ),
                "source_combines_candidatewise_extrema": True,
                "lean_combines_candidatewise_extrema": True,
                "coherent_witness_status": "separate_witnesses_only",
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "coherent_extrema_witness"
        ] = extrema
        self.assertIn("not realized by one coherent witness", ledger_error(ledger))

    def test_exact_family_fiber_count_requires_surjectivity(self) -> None:
        ledger = valid_ledger()
        counting = applicable_fidelity_dimension(
            "The source claims the exact cardinality of a syntactically generated family.",
            "The Lean result claims the exact number of nonempty semantic realization fibers.",
        )
        counting.update(
            {
                "source_counted_object": (
                    "The source counts every syntax-level member generated by the indexed family."
                ),
                "lean_counted_object": (
                    "Lean counts only nonempty fibers represented by an actually realized outcome."
                ),
                "realized_fiber_semantics": (
                    "A syntax member contributes only when some legal witness realizes its fiber."
                ),
                "surjectivity_basis": (
                    "No proof currently shows that every syntactic member has a realizing witness."
                ),
                "source_counting_semantics": "syntactic_family_cardinality",
                "lean_counting_semantics": "nonempty_realized_fibers",
                "source_claims_exact_cardinality": True,
                "lean_claims_exact_cardinality": True,
                "claims_syntactic_family_equals_realized_fibers": False,
                "surjectivity_status": "missing",
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "cardinality_fibers"
        ] = counting
        self.assertIn("lacks surjectivity evidence", ledger_error(ledger))

        counting["surjectivity_status"] = "proved_surjective"
        counting["surjectivity_statement"] = (
            "Every syntactic family member has a legal witness in its corresponding nonempty fiber."
        )
        counting["surjectivity_lean_conclusion_id"] = "l_conclusion"
        self.assertEqual(ledger_error(ledger), "")

    def test_surjectivity_conclusion_must_be_in_dimension_obligations(self) -> None:
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        counting = applicable_fidelity_dimension(
            "The source claims equality between a syntax family and all realized semantic fibers.",
            "Lean proves the same equality using a surjection from witnesses onto the syntax family.",
        )
        counting["lean_obligation_ids"] = ["l_assumption"]
        counting.update(
            {
                "source_counted_object": (
                    "The source counts every member of the finite syntax-level family."
                ),
                "lean_counted_object": (
                    "Lean counts the corresponding nonempty semantic realization fibers."
                ),
                "realized_fiber_semantics": (
                    "A fiber is counted exactly when at least one legal witness realizes it."
                ),
                "surjectivity_basis": (
                    "A separate Lean conclusion is claimed to prove every syntax member realizable."
                ),
                "source_counting_semantics": "syntactic_family_cardinality",
                "lean_counting_semantics": "nonempty_realized_fibers",
                "source_claims_exact_cardinality": True,
                "lean_claims_exact_cardinality": True,
                "claims_syntactic_family_equals_realized_fibers": True,
                "surjectivity_status": "proved_surjective",
                "surjectivity_statement": (
                    "Every syntax member has a legal witness in its semantic realization fiber."
                ),
                "surjectivity_lean_conclusion_id": "l_conclusion",
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "cardinality_fibers"
        ] = counting
        self.assertIn("not among the cardinality", ledger_error(ledger))

    def test_algorithmic_row_cannot_omit_execution_scope_review(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        review["fidelity_risk_review"]["dimensions"]["execution_claim_scope"] = (
            absent_fidelity_dimension(
                "The reviewer incorrectly treats the executable row as having no execution scope."
            )
        )
        ledger["semantic_scope_review"] = review
        self.assertIn("lacks an applicable execution-claim", ledger_error(ledger))

    def test_partial_transition_does_not_match_complete_execution(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        scope = review["fidelity_risk_review"]["dimensions"][
            "execution_claim_scope"
        ]
        scope["source_semantics"] = (
            "The source claim covers every legal input, transition, and terminal branch of the complete executor."
        )
        scope["lean_semantics"] = (
            "The Lean claim covers one local transition from a supplied intermediate state."
        )
        scope["relation"] = "source_stronger"
        scope["source_input_scope"] = (
            "The source executor accepts every legal initial input in the advertised input domain."
        )
        scope["lean_input_scope"] = (
            "The Lean theorem accepts one supplied intermediate state rather than every initial input."
        )
        scope["source_state_transition_scope"] = (
            "The source algorithm claim covers every transition from initial state through terminal output."
        )
        scope["lean_state_transition_scope"] = (
            "The Lean result covers exactly one local transition without the remaining execution."
        )
        scope["source_termination_scope"] = (
            "The source claim includes the complete terminating execution on every legal initial input."
        )
        scope["lean_termination_scope"] = (
            "The Lean theorem makes no claim that repeated local transitions terminate globally."
        )
        scope["source_numeric_representation"] = (
            "The source uses an exact numeric representation for every transition in the complete execution."
        )
        scope["lean_numeric_representation"] = (
            "Lean uses natural-number arithmetic only for the single local transition under review."
        )
        scope["source_cost_scope"] = (
            "The source advertises a polynomial bound for the complete terminating executor."
        )
        scope["lean_cost_scope"] = (
            "Lean bounds only the comparisons performed by one local transition."
        )
        scope["global_claim_bridge_basis"] = (
            "No refinement theorem promotes the local scan to the complete global execution."
        )
        ledger["semantic_scope_review"] = review
        self.assertIn(
            "non-equivalent `execution_claim_scope`", ledger_error(ledger)
        )

    def test_incompatible_termination_conditions_do_not_match(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        scope = review["fidelity_risk_review"]["dimensions"][
            "execution_claim_scope"
        ]
        scope["lean_semantics"] = (
            "The Lean statement stops after one transition while the source stops at a fixed point."
        )
        scope["relation"] = "incomparable"
        scope["source_termination_scope"] = (
            "The source executor repeats its transition relation until it reaches a fixed point."
        )
        scope["lean_termination_scope"] = (
            "The Lean executor always stops after one transition regardless of the resulting state."
        )
        scope["global_claim_bridge_basis"] = (
            "No premise or refinement identifies one transition with convergence to a fixed point."
        )
        ledger["semantic_scope_review"] = review
        self.assertIn(
            "non-equivalent `execution_claim_scope`", ledger_error(ledger)
        )

    def test_algorithmic_row_requires_termination_scope(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        scope = review["fidelity_risk_review"]["dimensions"][
            "execution_claim_scope"
        ]
        del scope["lean_termination_scope"]
        ledger["semantic_scope_review"] = review
        self.assertIn(
            "Lean termination scope", ledger_error(ledger)
        )

    def test_v3_execution_scope_does_not_accept_legacy_field_substitution(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        scope = review["fidelity_risk_review"]["dimensions"][
            "execution_claim_scope"
        ]
        del scope["source_input_scope"]
        scope["source_quota_turnout_scope"] = (
            "A legacy field records an input-domain statement but is not a v3 field."
        )
        ledger["semantic_scope_review"] = review
        self.assertIn("source input scope", ledger_error(ledger))

    def test_v3_execution_scope_rejects_function_name_evidence(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        scope = review["fidelity_risk_review"]["dimensions"][
            "execution_claim_scope"
        ]
        scope["relation_basis"] = (
            "The source and Lean executors have the same function name in their declarations."
        )
        ledger["semantic_scope_review"] = review
        self.assertIn("relation basis", ledger_error(ledger))

    def test_legacy_v2_execution_scope_record_remains_accepted(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        fidelity_review = review["fidelity_risk_review"]
        fidelity_review["schema_version"] = (
            semantic_obligation_review.LEGACY_FIDELITY_RISK_REVIEW_VERSION
        )
        scope = fidelity_review["dimensions"]["execution_claim_scope"]
        for field, _ in semantic_obligation_review.FIDELITY_EXECUTION_SCOPE_FIELDS:
            if field != "global_claim_bridge_basis":
                del scope[field]
        scope.update(
            {
                "source_quota_turnout_scope": (
                    "The archived source record describes the complete source input domain."
                ),
                "lean_quota_turnout_scope": (
                    "The archived Lean record describes the corresponding complete input domain."
                ),
                "source_seat_termination_scope": (
                    "The archived source record describes its complete termination condition."
                ),
                "lean_seat_termination_scope": (
                    "The archived Lean record describes the corresponding termination condition."
                ),
                "source_round_scope": (
                    "The archived source record covers every state transition in execution."
                ),
                "lean_round_scope": (
                    "The archived Lean record covers every corresponding state transition."
                ),
                "source_arithmetic_domain": (
                    "The archived source record specifies its numeric representation."
                ),
                "lean_arithmetic_domain": (
                    "The archived Lean record specifies the corresponding numeric representation."
                ),
                "source_cost_claim_scope": (
                    "The archived source record states the claimed cost scope for execution."
                ),
                "lean_cost_claim_scope": (
                    "The archived Lean record states the corresponding cost scope."
                ),
            }
        )
        ledger["semantic_scope_review"] = review
        self.assertEqual(ledger_error(ledger), "")

    def test_fidelity_evidence_cannot_be_function_name_matching(self) -> None:
        ledger = valid_ledger()
        shape = applicable_fidelity_dimension(
            "The source returns a structured result with one projected terminal component.",
            "Lean returns a structured result with the same projected terminal component.",
        )
        shape.update(
            {
                "source_output_shape": (
                    "The source structure contains the projected candidate and round components."
                ),
                "lean_output_shape": (
                    "The Lean structure contains the projected candidate and round components."
                ),
                "projection_terminal_policy": (
                    "Both structures remove the same final terminal component before comparison."
                ),
                "arity_basis": (
                    "The expanded constructors yield equal component lengths on every legal input."
                ),
                "relation_basis": (
                    "The two functions have the same function name in their declarations."
                ),
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "output_shape"
        ] = shape
        self.assertIn("relation basis", ledger_error(ledger))

    def test_numeric_absence_cannot_hide_manifest_visible_comparison(self) -> None:
        ledger = valid_ledger()
        ledger["semantic_scope_review"]["numeric_semantics_review"] = {
            "formulas_present": False,
            "items": [],
            "non_numeric_source_obligation_ids": [
                "s_assumption",
                "s_conclusion",
            ],
            "non_numeric_lean_obligation_ids": [
                "l_assumption",
                "l_conclusion",
            ],
            "absence_basis": (
                "The reviewer incorrectly claims that neither side contains numeric semantics."
            ),
        }
        self.assertIn("manifest-visible operator semantics", ledger_error(ledger))

    def test_operator_review_must_cover_every_obligation(self) -> None:
        ledger = valid_ledger()
        ledger["semantic_scope_review"]["numeric_semantics_review"][
            "non_numeric_source_obligation_ids"
        ] = []
        self.assertIn("every source obligation", ledger_error(ledger))

    def test_matches_rejects_real_division_vs_natural_floor_division(self) -> None:
        ledger = valid_ledger()
        numeric_item = division_numeric_item("different")
        numeric_item["lean_expression"] = "Nat.div x y in the executable checker"
        numeric_item["lean_domain"] = (
            "The Lean expression ranges over natural-number support counts."
        )
        numeric_item["lean_operations"] = (
            "Natural division truncates to the Euclidean floor of the quotient."
        )
        numeric_item["lean_division"] = (
            "Lean uses natural Euclidean division rather than exact field division."
        )
        numeric_item["lean_rounding"] = (
            "Lean truncates every nonintegral quotient toward the natural floor."
        )
        ledger["semantic_scope_review"]["numeric_semantics_review"] = {
            "formulas_present": True,
            "items": [numeric_item],
            "non_numeric_source_obligation_ids": ["s_conclusion"],
            "non_numeric_lean_obligation_ids": ["l_conclusion"],
        }
        self.assertIn("non-equivalent", ledger_error(ledger))

    def test_proved_numeric_equivalence_requires_explicit_equivalence_conclusion(self) -> None:
        ledger = valid_ledger()
        numeric_item = division_numeric_item("proved_equivalent")
        numeric_item["lean_obligation_ids"] = ["l_assumption", "l_conclusion"]
        ledger["semantic_scope_review"]["numeric_semantics_review"] = {
            "formulas_present": True,
            "items": [numeric_item],
            "non_numeric_source_obligation_ids": ["s_conclusion"],
            "non_numeric_lean_obligation_ids": [],
        }
        self.assertIn("Lean conclusion obligation", ledger_error(ledger))
        numeric_item["lean_equivalence_conclusion_id"] = "l_conclusion"
        numeric_item["lean_equivalence_statement"] = (
            "For every legal denominator, encoded division equals exact rational division."
        )
        self.assertIn("does not explicitly contain equality or iff", ledger_error(ledger))

        manifest = valid_manifest()
        manifest["atoms"][-1]["canonical"] = {
            "tag": "app",
            "fn": {"tag": "const", "name": "Eq", "levels": []},
            "arg": {"tag": "formula-equivalence"},
        }
        manifest["atoms"][-1]["display"] = "encodedDiv x y = x / y"
        refresh_manifest_digest(ledger, manifest)
        self.assertEqual(ledger_error(ledger, manifest), "")

    def test_matches_rejects_immediate_successor_vs_restricted_support(self) -> None:
        ledger = valid_ledger()
        ledger["semantic_scope_review"]["discrete_semantics_review"] = {
            "operations_present": True,
            "items": [
                {
                    "id": "next_ranked_candidate",
                    "source_obligation_ids": ["s_conclusion"],
                    "lean_obligation_ids": ["l_conclusion"],
                    "source_expression": "The candidate immediately following the winner.",
                    "lean_expression": "Support after restricting the ballot carrier.",
                    "source_domain": "Duplicate-free ranked ballots in their reduced source order.",
                    "lean_domain": "The same ballots after hiding candidates outside a carrier.",
                    "source_operation": (
                        "Drop the prefix through the winner and inspect the literal next entry."
                    ),
                    "lean_operation": (
                        "Filter to a restricted carrier and test eventual candidate support."
                    ),
                    "source_order_sensitivity": (
                        "A retained candidate between the winner and target changes the result."
                    ),
                    "lean_order_sensitivity": (
                        "Candidates hidden by the carrier do not block later target support."
                    ),
                    "relation": "different",
                    "relation_basis": (
                        "A ballot winner, retained, target separates immediate adjacency from support."
                    ),
                }
            ],
            "non_discrete_source_obligation_ids": ["s_assumption"],
            "non_discrete_lean_obligation_ids": ["l_assumption"],
        }
        self.assertIn("non-equivalent", ledger_error(ledger))

    def test_discrete_absence_cannot_hide_manifest_visible_list_operation(self) -> None:
        ledger = valid_ledger()
        manifest = valid_manifest()
        manifest["atoms"][-1]["canonical"] = {
            "tag": "app",
            "fn": {"tag": "const", "name": "List.dropWhile", "levels": []},
            "arg": {"tag": "ballot"},
        }
        manifest["atoms"][-1]["display"] = "List.dropWhile predicate ballot"
        refresh_manifest_digest(ledger, manifest)
        self.assertIn(
            "manifest-visible operator semantics",
            ledger_error(ledger, manifest),
        )

    def test_nonalgorithmic_separate_worlds_require_semantic_bridge(self) -> None:
        ledger = valid_ledger()
        review = ledger["semantic_scope_review"]
        review["semantic_worlds"] = [
            {
                "id": "paper_model",
                "role": "source",
                "semantics": "The source proposition is interpreted in the paper's outcome model.",
            },
            {
                "id": "formal_model",
                "role": "lean",
                "semantics": "The Lean proposition is interpreted in a distinct formal outcome model.",
            },
        ]
        review["world_bridges"] = []
        self.assertIn("no exposed equality", ledger_error(ledger))

    def test_nonalgorithmic_separate_worlds_accept_exposed_equivalence(self) -> None:
        ledger = valid_ledger()
        review = ledger["semantic_scope_review"]
        review["semantic_worlds"] = [
            {
                "id": "paper_model",
                "role": "source",
                "semantics": "The source proposition is interpreted in the paper's outcome model.",
            },
            {
                "id": "formal_model",
                "role": "lean",
                "semantics": "The Lean proposition is interpreted in a distinct formal outcome model.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "paper_model",
                "to_world": "formal_model",
                "relation": "equivalent",
                "statement": (
                    "Every source outcome corresponds to exactly one formal outcome "
                    "with the same advertised proposition."
                ),
                "lean_conclusion_id": "l_conclusion",
            }
        ]
        self.assertEqual(ledger_error(ledger), "")

    def test_definitionally_equal_world_bridge_transfers_result(self) -> None:
        ledger = valid_ledger()
        review = ledger["semantic_scope_review"]
        review["semantic_worlds"] = [
            {
                "id": "paper_model",
                "role": "source",
                "semantics": "The source proposition uses the paper's expanded mathematical outcome.",
            },
            {
                "id": "formal_model",
                "role": "lean",
                "semantics": "The Lean proposition uses a definitionally identical expanded outcome.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "paper_model",
                "to_world": "formal_model",
                "relation": "definitionally_equal",
                "statement": (
                    "Unfolding both outcomes yields the same carrier, transition, and "
                    "advertised result proposition."
                ),
                "lean_conclusion_id": "l_conclusion",
            }
        ]
        self.assertEqual(ledger_error(ledger), "")

    def test_omitted_source_conclusion_is_rejected(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"] = ledger["obligation_alignment"][:1]
        self.assertIn(
            "unmatched source conclusion",
            ledger_error(ledger),
        )

    def test_unjustified_lean_input_is_rejected(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"] = ledger["obligation_alignment"][1:]
        ledger["unmatched_source_inputs"] = ["s_assumption"]
        self.assertIn(
            "unjustified Lean input",
            ledger_error(ledger),
        )

    def test_obligation_ids_are_not_semantic_evidence(self) -> None:
        ledger = valid_ledger()
        action = applicable_fidelity_dimension(
            "The source assumption ranges over an inhabited legal transformation family.",
            "The Lean assumption ranges over the same inhabited legal transformation family.",
        )
        action["source_obligation_ids"] = ["s_assumption"]
        action["lean_obligation_ids"] = ["l_assumption", "l_conclusion"]
        action.update(
            {
                "source_action_space": (
                    "The source carrier contains every legal transformation under review."
                ),
                "lean_action_space": (
                    "The Lean carrier contains every corresponding legal transformation."
                ),
                "carrier_capacity_basis": (
                    "Both sides impose the same carrier membership and capacity condition."
                ),
                "duplicate_interaction_basis": (
                    "Both sides reject exactly the same duplicate-producing transformations."
                ),
                "nonvacuity_basis": (
                    "A shared identity transformation witnesses inhabitation on both sides."
                ),
                "source_nonvacuous": True,
                "lean_nonvacuous": True,
            }
        )
        ledger["semantic_scope_review"]["fidelity_risk_review"]["dimensions"][
            "adversarial_action_space"
        ] = action
        ledger["source_obligations"][0]["id"] = "arbitrary_source_name"
        ledger["lean_obligations"][0]["id"] = "arbitrary_lean_name"
        ledger["obligation_alignment"][0]["source_id"] = "arbitrary_source_name"
        ledger["obligation_alignment"][0]["lean_id"] = "arbitrary_lean_name"
        numeric_item = ledger["semantic_scope_review"]["numeric_semantics_review"][
            "items"
        ][0]
        numeric_item["source_obligation_ids"] = ["arbitrary_source_name"]
        numeric_item["lean_obligation_ids"] = ["arbitrary_lean_name"]
        discrete_review = ledger["semantic_scope_review"]["discrete_semantics_review"]
        discrete_review["non_discrete_source_obligation_ids"][0] = (
            "arbitrary_source_name"
        )
        discrete_review["non_discrete_lean_obligation_ids"][0] = (
            "arbitrary_lean_name"
        )
        ledger["semantic_scope_review"]["named_definition_review"][
            "non_definition_lean_obligation_ids"
        ][0] = "arbitrary_lean_name"
        action["source_obligation_ids"] = ["arbitrary_source_name"]
        action["lean_obligation_ids"] = [
            "arbitrary_lean_name",
            "l_conclusion",
        ]
        self.assertEqual(
            ledger_error(ledger), ""
        )

    def test_name_matching_is_not_a_semantic_basis(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"][1]["semantic_basis"] = "The theorem names match."
        self.assertIn(
            "relies on names",
            ledger_error(ledger),
        )

    def test_name_matching_is_not_a_semantic_bridge(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"][1]["bridge_statement"] = (
            "The theorem names match."
        )
        self.assertIn(
            "bridge_statement relies on names",
            ledger_error(ledger),
        )

    def test_equivalence_requires_explicit_semantic_bridge(self) -> None:
        ledger = valid_ledger()
        del ledger["obligation_alignment"][1]["bridge_statement"]
        self.assertIn(
            "semantic bridge statement",
            ledger_error(ledger),
        )

    def test_algorithm_result_must_be_runner_derived(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        review["algorithm_review"]["result_provenance"] = (
            "independent_characterization"
        )
        review["named_definition_review"] = {
            "definitions_present": True,
            "non_definition_lean_obligation_ids": ["l_assumption"],
            "items": [
                {
                    "lean_obligation_ids": ["l_conclusion"],
                    "surface_expression": "winnerCharacterization output candidate",
                    "unfolded_semantics": (
                        "The predicate unfolds to candidate membership in the winner "
                        "set of the independently supplied output."
                    ),
                    "expansion_basis": (
                        "The reviewed Lean definition body is unfolded in the elaborated row."
                    ),
                    "recursive_result_dependencies": [],
                    "recursive_expansion_complete": True,
                    "classification": "self_characterizing",
                    "used_as_source_conclusion_evidence": False,
                }
            ],
        }
        ledger["semantic_scope_review"] = review
        self.assertIn("runner-derived result provenance", ledger_error(ledger))

    def test_self_characterizing_iff_cannot_supply_paper_credit(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        review["named_definition_review"] = {
            "definitions_present": True,
            "non_definition_lean_obligation_ids": ["l_assumption"],
            "items": [
                {
                    "lean_obligation_ids": ["l_conclusion"],
                    "surface_expression": "winnerCharacterization output candidate",
                    "unfolded_semantics": (
                        "The advertised characterization unfolds back to the same "
                        "winner-set membership proposition on an independent output."
                    ),
                    "expansion_basis": (
                        "The reviewed Lean definition body is unfolded in the elaborated row."
                    ),
                    "recursive_result_dependencies": [],
                    "recursive_expansion_complete": True,
                    "classification": "self_characterizing",
                    "used_as_source_conclusion_evidence": True,
                }
            ],
        }
        ledger["semantic_scope_review"] = review
        self.assertIn("self-characterizing definition", ledger_error(ledger))

    def test_matches_requires_recursive_named_definition_expansion(self) -> None:
        ledger = valid_ledger()
        review = ledger["semantic_scope_review"]
        review["named_definition_review"] = {
            "definitions_present": True,
            "non_definition_lean_obligation_ids": ["l_assumption"],
            "items": [
                {
                    "lean_obligation_ids": ["l_conclusion"],
                    "surface_expression": "MultiwinnerRouteCertificate profile",
                    "unfolded_semantics": (
                        "The inductive certificate permits loss nodes and synchronized "
                        "winner nodes carrying a retained continuation-mass relation."
                    ),
                    "expansion_basis": (
                        "The audit reads every constructor in the certificate declaration."
                    ),
                    "recursive_result_dependencies": [
                        {
                            "surface_expression": "RetainedContinuationMassEq left right",
                            "unfolded_semantics": (
                                "Every visible continuation class has equal aggregate "
                                "post-step weight in the two generated states."
                            ),
                            "expansion_basis": (
                                "The predicate body is unfolded to finite class mass sums."
                            ),
                        }
                    ],
                    "recursive_expansion_complete": False,
                    "classification": "substantive",
                    "used_as_source_conclusion_evidence": False,
                }
            ],
        }
        self.assertIn("incomplete recursive", ledger_error(ledger))
        review["named_definition_review"]["items"][0][
            "recursive_expansion_complete"
        ] = True
        self.assertEqual(ledger_error(ledger), "")

    def test_definition_absence_cannot_hide_manifest_expansion(self) -> None:
        ledger = valid_ledger()
        manifest = valid_manifest()
        manifest["atoms"][-1]["canonical"] = {
            "tag": "inlined_definition",
            "type": {"tag": "sort"},
            "value": {"tag": "expanded-result-body"},
        }
        manifest["atoms"][-1]["display"] = "expandedResult x"
        refresh_manifest_digest(ledger, manifest)
        self.assertIn(
            "manifest-expanded definitions as absent",
            ledger_error(ledger, manifest),
        )

    def test_fixed_profile_does_not_match_all_profile_source_claim(self) -> None:
        ledger = valid_ledger()
        review = ledger["semantic_scope_review"]
        review["source_quantification"] = "all_profiles"
        review["lean_quantification"] = "fixed_profile"
        ledger["semantic_scope_review"] = review
        self.assertIn("all-profile scope", ledger_error(ledger))

    def test_polynomial_claim_is_not_noncomputable_existence(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        algorithm = review["algorithm_review"]
        algorithm["source_claim_level"] = "polynomial_time"
        algorithm["lean_claim_level"] = "noncomputable_existence"
        algorithm["complexity_statement"] = (
            "The runner terminates in a polynomial number of arithmetic operations."
        )
        algorithm["arithmetic_model"] = (
            "Input rationals use binary encoding and exact rational arithmetic."
        )
        algorithm["complexity_lean_conclusion_id"] = "l_conclusion"
        ledger["semantic_scope_review"] = review
        self.assertIn("noncomputable existence", ledger_error(ledger))

    def test_polynomial_match_requires_operational_complexity_review(self) -> None:
        ledger = valid_polynomial_ledger()
        del ledger["operational_complexity_review"]
        self.assertIn("missing operational_complexity_review", ledger_error(ledger))

    def test_complete_operational_complexity_review_is_accepted(self) -> None:
        self.assertEqual(ledger_error(valid_polynomial_ledger()), "")

    def test_operational_complexity_review_version_is_independent(self) -> None:
        ledger = valid_polynomial_ledger()
        ledger["operational_complexity_review"]["schema_version"] = "stale-version"
        self.assertIn("invalid schema_version", ledger_error(ledger))

    def test_operational_graph_requires_transitive_all_branch_coverage(self) -> None:
        for field, message in (
            ("transitive_closure_complete", "complete transitive closure"),
            ("all_reachable_branches_complete", "every reachable branch"),
        ):
            with self.subTest(field=field):
                ledger = valid_polynomial_ledger()
                ledger["operational_complexity_review"]["dependency_graph"][field] = False
                self.assertIn(message, ledger_error(ledger))

        ledger = valid_polynomial_ledger()
        graph = ledger["operational_complexity_review"]["dependency_graph"]
        graph["nodes"].append(
            {
                "id": "unreachable_route",
                "operation_semantics": (
                    "This operation performs additional materialization work on a reachable state."
                ),
                "reachable_branch_domain": (
                    "The reviewer claims this operation belongs to a legal recursive branch."
                ),
                "work_accounting_categories": ["materialization_rebuilding"],
            }
        )
        self.assertIn("unreachable from its roots", ledger_error(ledger))

    def test_operational_review_requires_worst_case_recurrence_and_binding(self) -> None:
        ledger = valid_polynomial_ledger()
        ledger["operational_complexity_review"]["worst_case_recurrence"] = ""
        self.assertIn("worst-case recurrence", ledger_error(ledger))

        ledger = valid_polynomial_ledger()
        ledger["operational_complexity_review"][
            "complexity_lean_conclusion_id"
        ] = "some_other_conclusion"
        self.assertIn("bound to the complexity conclusion", ledger_error(ledger))

    def test_operational_work_accounting_must_cover_every_category(self) -> None:
        for category in semantic_obligation_review.OPERATIONAL_WORK_CATEGORIES:
            with self.subTest(category=category):
                ledger = valid_polynomial_ledger()
                work = ledger["operational_complexity_review"]["work_accounting"]
                ledger["operational_complexity_review"]["work_accounting"] = [
                    item for item in work if item["category"] != category
                ]
                self.assertIn("every required category", ledger_error(ledger))

    def test_charged_work_must_be_linked_to_a_dependency_node(self) -> None:
        ledger = valid_polynomial_ledger()
        graph = ledger["operational_complexity_review"]["dependency_graph"]
        graph["nodes"][0]["work_accounting_categories"].remove(
            "duplicate_multiplicity"
        )
        self.assertIn("linked to a dependency graph node", ledger_error(ledger))

        duplicate_item = next(
            item
            for item in ledger["operational_complexity_review"]["work_accounting"]
            if item["category"] == "duplicate_multiplicity"
        )
        duplicate_item["status"] = "proved_absent"
        duplicate_item["operation_semantics"] = (
            "The legal input representation contains no duplicate entries to revisit."
        )
        duplicate_item["worst_case_charge_or_absence_basis"] = (
            "The profile well-formedness invariant proves each encoded entry occurs once."
        )
        self.assertEqual(ledger_error(ledger), "")

    def test_missing_or_excluded_work_rejects_polynomial_match(self) -> None:
        for status in ("missing", "excluded_by_claim"):
            with self.subTest(status=status):
                ledger = valid_polynomial_ledger()
                ledger["operational_complexity_review"]["work_accounting"][0][
                    "status"
                ] = status
                self.assertIn("missing or excluded_by_claim", ledger_error(ledger))

    def test_material_closure_elimination_requires_pinned_semantic_evidence(self) -> None:
        ledger = valid_polynomial_ledger()
        closure = {
            "material": True,
            "evidence_kind": "generated_ir_call_graph",
            "evidence_artifact_sha256": "a" * 64,
            "audited_source_sha256": "b" * 64,
            "evidence_locator": "audit/generated/runner.callgraph.json",
            "old_dependency_semantics": (
                "The eliminated dependency recomputes the complete semantic closure at each step."
            ),
            "semantic_binding": (
                "Source spans bind each generated operation to the corresponding unfolded computation."
            ),
            "elimination_basis": (
                "Every reachable generated branch uses the materialized successor and omits recomputation."
            ),
            "symbol_names_used_as_evidence": False,
        }
        ledger["operational_complexity_review"]["closure_elimination"] = closure
        self.assertEqual(ledger_error(ledger), "")

        closure["evidence_artifact_sha256"] = "not-a-hash"
        self.assertIn("evidence artifact SHA-256 pin", ledger_error(ledger))
        closure["evidence_artifact_sha256"] = "a" * 64
        closure["symbol_names_used_as_evidence"] = True
        self.assertIn("symbol names as evidence", ledger_error(ledger))

    def test_operational_graph_identifier_renaming_preserves_validity(self) -> None:
        ledger = valid_polynomial_ledger()
        graph = ledger["operational_complexity_review"]["dependency_graph"]
        graph["nodes"][0]["id"] = "unrelated_root_identifier"
        graph["nodes"][1]["id"] = "unrelated_dependency_identifier"
        graph["root_node_ids"] = ["unrelated_root_identifier"]
        graph["edges"][0]["from_node_id"] = "unrelated_root_identifier"
        graph["edges"][0]["to_node_id"] = "unrelated_dependency_identifier"
        self.assertEqual(ledger_error(ledger), "")

    def test_non_polynomial_match_needs_no_operational_complexity_review(self) -> None:
        ledger = valid_ledger()
        self.assertNotIn("operational_complexity_review", ledger)
        self.assertEqual(ledger_error(ledger), "")

    def test_cross_world_result_requires_exposed_preservation_bridge(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        review["algorithm_review"] = {
            "source_claim_level": "executable",
            "lean_claim_level": "executable",
            "runner_provenance": "proved_refinement",
            "result_provenance": "preservation_bridge",
            "source_claim_basis": (
                "The source statement advertises the output of its specified executable procedure."
            ),
            "lean_claim_basis": (
                "The Lean statement advertises the output of a distinct executable runner."
            ),
            "refinement_statement": (
                "Every step of the Lean runner simulates the corresponding source "
                "algorithm step on related profiles."
            ),
            "result_preservation_statement": (
                "Related terminal profiles have exactly the same advertised winner set."
            ),
        }
        review["semantic_worlds"] = [
            {
                "id": "source_side",
                "role": "source",
                "semantics": "Profiles and outcomes produced by the paper's source algorithm.",
            },
            {
                "id": "lean_side",
                "role": "lean",
                "semantics": "Profiles and outcomes produced by the executable Lean runner.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "source_side",
                "to_world": "lean_side",
                "relation": "refines",
                "statement": review["algorithm_review"]["refinement_statement"],
                "lean_conclusion_id": "l_conclusion",
            }
        ]
        ledger["semantic_scope_review"] = review
        self.assertIn("result preservation is not exposed", ledger_error(ledger))

    def test_refined_runner_success_alone_does_not_transfer_source_result(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        review["algorithm_review"]["runner_provenance"] = "proved_refinement"
        review["algorithm_review"]["refinement_statement"] = (
            "Every step of the Lean runner simulates the corresponding source "
            "algorithm step on related profiles."
        )
        review["semantic_worlds"] = [
            {
                "id": "first",
                "role": "source",
                "semantics": "Profiles and outcomes produced by the paper's source algorithm.",
            },
            {
                "id": "second",
                "role": "lean",
                "semantics": "Profiles and outcomes produced by the executable Lean runner.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "first",
                "to_world": "second",
                "relation": "refines",
                "statement": review["algorithm_review"]["refinement_statement"],
                "lean_conclusion_id": "l_conclusion",
            }
        ]
        ledger["semantic_scope_review"] = review
        self.assertIn("result-preservation bridge", ledger_error(ledger))

    def test_exposed_refinement_and_preservation_bridges_are_accepted(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        refinement = (
            "Every step of the Lean runner simulates the corresponding source "
            "algorithm step on related profiles."
        )
        preservation = (
            "Related terminal profiles have exactly the same advertised winner set."
        )
        review["algorithm_review"] = {
            "source_claim_level": "executable",
            "lean_claim_level": "executable",
            "runner_provenance": "proved_refinement",
            "result_provenance": "preservation_bridge",
            "source_claim_basis": (
                "The source statement advertises the output of its specified executable procedure."
            ),
            "lean_claim_basis": (
                "The Lean statement advertises the output of a distinct executable runner."
            ),
            "refinement_statement": refinement,
            "result_preservation_statement": preservation,
        }
        review["semantic_worlds"] = [
            {
                "id": "alpha",
                "role": "source",
                "semantics": "Profiles and outcomes produced by the paper's source algorithm.",
            },
            {
                "id": "beta",
                "role": "lean",
                "semantics": "Profiles and outcomes produced by the executable Lean runner.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "alpha",
                "to_world": "beta",
                "relation": "refines",
                "statement": refinement,
                "lean_conclusion_id": "l_conclusion",
            },
            {
                "from_world": "alpha",
                "to_world": "beta",
                "relation": "preserves_result",
                "statement": preservation,
                "lean_conclusion_id": "l_conclusion",
            },
        ]
        ledger["semantic_scope_review"] = review
        self.assertEqual(ledger_error(ledger), "")

        # World ids are routing keys only; arbitrary renaming preserves validity.
        review["semantic_worlds"][0]["id"] = "unrelated_first_id"
        review["semantic_worlds"][1]["id"] = "unrelated_second_id"
        for bridge in review["world_bridges"]:
            bridge["from_world"] = "unrelated_first_id"
            bridge["to_world"] = "unrelated_second_id"
        self.assertEqual(ledger_error(ledger), "")

    def test_cross_world_existence_accepts_refinement_and_preservation(self) -> None:
        ledger = valid_ledger()
        review = executable_semantic_scope_review()
        refinement = (
            "Every formal witness decodes to a source witness satisfying the same "
            "primitive feasibility constraints."
        )
        preservation = (
            "Decoding preserves the advertised existence property of the witness."
        )
        review["algorithm_review"] = {
            "source_claim_level": "existence",
            "lean_claim_level": "noncomputable_existence",
            "runner_provenance": "proved_refinement",
            "result_provenance": "preservation_bridge",
            "source_claim_basis": (
                "The source theorem asserts existence of a witness in its native model."
            ),
            "lean_claim_basis": (
                "Lean noncomputably constructs a witness in a separate finite representation."
            ),
            "refinement_statement": refinement,
            "result_preservation_statement": preservation,
        }
        review["semantic_worlds"] = [
            {
                "id": "source_witnesses",
                "role": "source",
                "semantics": "Witnesses satisfying the paper's primitive feasibility relation.",
            },
            {
                "id": "encoded_witnesses",
                "role": "lean",
                "semantics": "Finite encoded witnesses constructed by the Lean existence proof.",
            },
        ]
        review["world_bridges"] = [
            {
                "from_world": "source_witnesses",
                "to_world": "encoded_witnesses",
                "relation": "refines",
                "statement": refinement,
                "lean_conclusion_id": "l_conclusion",
            },
            {
                "from_world": "source_witnesses",
                "to_world": "encoded_witnesses",
                "relation": "preserves_result",
                "statement": preservation,
                "lean_conclusion_id": "l_conclusion",
            },
        ]
        ledger["semantic_scope_review"] = review
        self.assertEqual(ledger_error(ledger), "")

    def test_vague_source_location_is_rejected(self) -> None:
        ledger = valid_ledger()
        ledger["source_obligations"][1]["source_location"] = "the paper"
        self.assertIn(
            "exact source locator",
            ledger_error(ledger),
        )

    def test_non_string_semantic_statement_is_rejected(self) -> None:
        ledger = valid_ledger()
        ledger["source_obligations"][1]["statement"] = {"claim": "P x"}
        self.assertIn(
            "no semantic statement",
            ledger_error(ledger),
        )

    def test_unmatched_conclusion_is_a_valid_mismatch_but_not_a_boundary(self) -> None:
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        ledger["resolution"] = "conditional_boundary"
        ledger["obligation_alignment"] = ledger["obligation_alignment"][:1]
        ledger["unmatched_source_conclusions"] = ["s_conclusion"]
        ledger["unmatched_lean_conclusions"] = ["l_conclusion"]
        self.assertEqual(ledger_error(ledger), "")
        ledger["obligation_ledger_error"] = ""
        self.assertFalse(review_dashboard._is_conditional_boundary_judgment(ledger))

    def test_extra_lean_assumption_can_be_an_explicit_boundary(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            1,
            {
                "ref": "b/extra",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {"tag": "extra-premise"},
                "display": "R x",
            },
        )
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        ledger["resolution"] = "conditional_boundary"
        ledger["lean_obligations"].insert(
            1,
            {
                "id": "l_extra_assumption",
                "kind": "assumption",
                "signature_ref": "b/extra",
            },
        )
        ledger["unjustified_lean_inputs"] = ["l_extra_assumption"]
        classify_operator_free(
            ledger["semantic_scope_review"], lean_ids=("l_extra_assumption",)
        )
        refresh_manifest_digest(ledger, manifest)
        self.assertEqual(ledger_error(ledger, manifest), "")
        ledger["obligation_ledger_error"] = ""
        self.assertTrue(review_dashboard._is_conditional_boundary_judgment(ledger))

    def test_polynomial_conditional_boundary_does_not_require_full_match_gate(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            1,
            {
                "ref": "b/extra",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {"tag": "extra-premise"},
                "display": "R x",
            },
        )
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        ledger["resolution"] = "conditional_boundary"
        ledger["lean_obligations"].insert(
            1,
            {
                "id": "l_extra_assumption",
                "kind": "assumption",
                "signature_ref": "b/extra",
            },
        )
        ledger["unjustified_lean_inputs"] = ["l_extra_assumption"]
        review = executable_semantic_scope_review()
        algorithm = review["algorithm_review"]
        algorithm["source_claim_level"] = "polynomial_time"
        algorithm["lean_claim_level"] = "polynomial_time"
        algorithm["complexity_statement"] = (
            "The audited runner uses polynomially many bit operations on every legal input."
        )
        algorithm["arithmetic_model"] = (
            "Exact rationals use binary numerators and denominators with bit-operation costs."
        )
        algorithm["complexity_lean_conclusion_id"] = "l_conclusion"
        classify_operator_free(review, lean_ids=("l_extra_assumption",))
        ledger["semantic_scope_review"] = review
        refresh_manifest_digest(ledger, manifest)

        self.assertNotIn("operational_complexity_review", ledger)
        self.assertEqual(ledger_error(ledger, manifest), "")

    def test_claim_weakening_cannot_be_a_conditional_boundary(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            1,
            {
                "ref": "b/extra",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {"tag": "extra-premise"},
                "display": "R x",
            },
        )
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        ledger["resolution"] = "conditional_boundary"
        ledger["lean_obligations"].insert(
            1,
            {
                "id": "l_extra_assumption",
                "kind": "assumption",
                "signature_ref": "b/extra",
            },
        )
        ledger["unjustified_lean_inputs"] = ["l_extra_assumption"]
        review = ledger["semantic_scope_review"]
        review["source_quantification"] = "all_profiles"
        review["lean_quantification"] = "fixed_profile"
        classify_operator_free(review, lean_ids=("l_extra_assumption",))
        refresh_manifest_digest(ledger, manifest)

        self.assertIn(
            "confuses fixed-, existential-, and all-profile scope",
            ledger_error(ledger, manifest),
        )

        executable_review = executable_semantic_scope_review()
        executable_review["algorithm_review"]["source_claim_level"] = (
            "polynomial_time"
        )
        executable_review["algorithm_review"]["lean_claim_level"] = "executable"
        classify_operator_free(
            executable_review, lean_ids=("l_extra_assumption",)
        )
        ledger["semantic_scope_review"] = executable_review
        self.assertIn(
            "conflates noncomputable existence, executable output, and polynomial-time claims",
            ledger_error(ledger, manifest),
        )

    def test_recorded_gap_ids_must_match_computed_gaps(self) -> None:
        ledger = valid_ledger()
        ledger["judgment"] = "mismatch"
        ledger["obligation_alignment"] = ledger["obligation_alignment"][:1]
        ledger["unmatched_source_conclusions"] = ["some_other_id"]
        self.assertIn(
            "does not equal",
            ledger_error(ledger),
        )

    def test_signature_manifest_is_required(self) -> None:
        self.assertIn(
            "manifest is unavailable",
            semantic_obligation_review.semantic_obligation_ledger_error(
                valid_ledger(), None
            ),
        )

    def test_signature_manifest_digest_is_authoritative(self) -> None:
        ledger = valid_ledger()
        ledger["lean_signature_sha256"] = "stale-signature"
        self.assertIn("digest is stale", ledger_error(ledger))

    def test_every_manifest_atom_must_be_referenced(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            1,
            {
                "ref": "b/1",
                "role": "parameter",
                "binder_info": "implicit",
                "canonical": {"tag": "parameter"},
                "display": "Type",
            },
        )
        ledger = valid_ledger()
        refresh_manifest_digest(ledger, manifest)
        self.assertIn("omit signature atom", ledger_error(ledger, manifest))

    def test_signature_ref_must_be_unique(self) -> None:
        ledger = valid_ledger()
        ledger["lean_obligations"][1]["signature_ref"] = "b/0"
        self.assertIn("multiple obligations", ledger_error(ledger))

    def test_obligation_kind_must_match_manifest_role(self) -> None:
        ledger = valid_ledger()
        ledger["lean_obligations"][0]["kind"] = "parameter"
        self.assertIn("does not match", ledger_error(ledger))

    def test_parameter_binder_is_aligned_as_a_lean_input(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            0,
            {
                "ref": "b/parameter",
                "role": "parameter",
                "binder_info": "implicit",
                "canonical": {"tag": "sort"},
                "display": "Type",
            },
        )
        ledger = valid_ledger()
        ledger["source_obligations"].insert(
            0,
            {
                "id": "s_parameter",
                "kind": "parameter",
                "statement": "An arbitrary carrier type.",
                "source_location": "Theorem 2, p. 4",
            },
        )
        ledger["lean_obligations"].insert(
            0,
            {
                "id": "l_parameter",
                "kind": "parameter",
                "signature_ref": "b/parameter",
            },
        )
        ledger["obligation_alignment"].insert(
            0,
            {
                "source_id": "s_parameter",
                "lean_id": "l_parameter",
                "relation": "equivalent",
                "semantic_basis": "Both quantify over the same carrier domain.",
                "bridge_statement": "The source carrier and Lean carrier range over the same type domain.",
            },
        )
        classify_operator_free(
            ledger["semantic_scope_review"],
            source_ids=("s_parameter",),
            lean_ids=("l_parameter",),
        )
        refresh_manifest_digest(ledger, manifest)
        self.assertEqual(ledger_error(ledger, manifest), "")

    def test_omitted_source_input_is_rejected(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"] = ledger["obligation_alignment"][1:]
        ledger["unmatched_source_inputs"] = ["s_assumption"]
        ledger["unjustified_lean_inputs"] = ["l_assumption"]
        ledger["judgment"] = "mismatch"
        self.assertEqual(ledger_error(ledger), "")
        ledger["judgment"] = "matches"
        self.assertIn("semantic obligation gap", ledger_error(ledger))

    def test_directional_conclusion_is_not_an_exact_match_or_boundary(self) -> None:
        ledger = valid_ledger()
        ledger["obligation_alignment"][1]["relation"] = "lean_implies_source"
        ledger["judgment"] = "matches"
        self.assertIn("semantic obligation gap", ledger_error(ledger))
        ledger["judgment"] = "mismatch"
        ledger["resolution"] = "conditional_boundary"
        self.assertEqual(ledger_error(ledger), "")
        self.assertFalse(review_dashboard._is_conditional_boundary_judgment(ledger))

    def test_lean_obligation_cannot_supply_free_form_prose(self) -> None:
        ledger = valid_ledger()
        ledger["lean_obligations"][0]["statement"] = "This says something unrelated."
        self.assertIn("unaudited prose", ledger_error(ledger))

    def test_lean_obligation_atom_digest_is_authoritative(self) -> None:
        ledger = valid_ledger()
        ledger["lean_obligations"][0]["signature_atom_sha256"] = "stale"
        self.assertIn("atom digest is stale", ledger_error(ledger))

    def test_statement_loader_fails_closed_without_current_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            item = valid_ledger()
            item["judgment"] = "matches"
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                        "validator": "test-model",
                        "validated_at": "2026-07-10T00:00:00Z",
                        "items": {"row": item},
                    }
                ),
                encoding="utf-8",
            )
            missing = review_dashboard.load_llm_statement_judgments(folder)
            current = review_dashboard.load_llm_statement_judgments(
                folder, {"row": valid_manifest()}
            )
        self.assertIn("manifest is unavailable", missing["row"]["obligation_ledger_error"])
        self.assertEqual(current["row"]["obligation_ledger_error"], "")

    def test_statement_loader_propagates_missing_runtime_gate(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            item = valid_polynomial_ledger()
            del item["operational_complexity_review"]
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                        "validator": "test-model",
                        "validated_at": "2026-07-16T00:00:00Z",
                        "items": {"runtime_row": item},
                    }
                ),
                encoding="utf-8",
            )
            loaded = review_dashboard.load_llm_statement_judgments(
                folder, {"runtime_row": valid_manifest()}
            )
        self.assertIn(
            "missing operational_complexity_review",
            loaded["runtime_row"]["obligation_ledger_error"],
        )

    def test_statement_loader_accepts_row_level_prompt_version(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            item = valid_ledger()
            item.update(
                {
                    "judgment": "matches",
                    "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                }
            )
            legacy_item = dict(item)
            legacy_item.pop("prompt_version")
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v3-semantic-full-statement",
                        "validator": "test-model",
                        "validated_at": "2026-07-10T00:00:00Z",
                        "items": {"current_row": item, "legacy_row": legacy_item},
                    }
                ),
                encoding="utf-8",
            )
            loaded = review_dashboard.load_llm_statement_judgments(
                folder,
                {
                    "current_row": valid_manifest(),
                    "legacy_row": valid_manifest(),
                },
            )
        self.assertFalse(loaded["current_row"]["prompt_version_stale"])
        self.assertTrue(loaded["legacy_row"]["prompt_version_stale"])

    def test_statement_prompt_compatibility_is_code_owned_and_item_local(self) -> None:
        compatible_prompt = "statement-match-v10-copyedit-fixture"
        compatible_item = valid_ledger()
        compatible_item["prompt_version"] = compatible_prompt
        unknown_item = valid_ledger()
        unknown_item.update(
            {
                "prompt_version": "statement-match-v10-unreviewed-fixture",
                # This must not let a sidecar self-declare compatibility.
                "semantic_contract_version": (
                    review_dashboard.REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION
                ),
            }
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v7-semantic-world-refinement",
                        "validator": "test-model",
                        "validated_at": "2026-07-28T00:00:00Z",
                        "items": {
                            "compatible_row": compatible_item,
                            "unknown_row": unknown_item,
                        },
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.dict(
                review_dashboard.LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
                {
                    compatible_prompt: (
                        review_dashboard.REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION
                    )
                },
            ):
                loaded = review_dashboard.load_llm_statement_judgments(
                    folder,
                    {
                        "compatible_row": valid_manifest(),
                        "unknown_row": valid_manifest(),
                    },
                )

        self.assertFalse(loaded["compatible_row"]["prompt_version_stale"])
        self.assertTrue(loaded["unknown_row"]["prompt_version_stale"])

    def test_compatible_statement_prompt_keeps_signature_and_ledger_gates(self) -> None:
        compatible_prompt = "statement-match-v10-copyedit-fixture"
        manifest = valid_manifest()
        lean_statement = "theorem fixture : P x"
        paper_statement = "Paper statement"
        agent_statement = "Context-free Lean translation"
        compatible_item = valid_ledger()
        compatible_item.update(
            {
                "prompt_version": compatible_prompt,
                "paper_statement_sha256": review_dashboard.statement_digest(
                    paper_statement
                ),
                "tex_statement_sha256": review_dashboard.statement_digest(
                    agent_statement
                ),
                "lean_statement_sha256": review_dashboard.statement_digest(
                    lean_statement
                ),
            }
        )
        invalid_item = copy.deepcopy(compatible_item)
        invalid_item["lean_obligations"] = []
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v7-semantic-world-refinement",
                        "validator": "test-model",
                        "validated_at": "2026-07-28T00:00:00Z",
                        "items": {
                            "compatible_row": compatible_item,
                            "invalid_row": invalid_item,
                        },
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.dict(
                review_dashboard.LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
                {
                    compatible_prompt: (
                        review_dashboard.REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION
                    )
                },
            ):
                loaded = review_dashboard.load_llm_statement_judgments(
                    folder,
                    {
                        "compatible_row": manifest,
                        "invalid_row": manifest,
                    },
                )

        self.assertFalse(
            review_dashboard._llm_statement_judgment_is_stale(
                loaded["compatible_row"],
                signature_sha256=str(manifest["sha256"]),
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
            )
        )
        self.assertTrue(
            review_dashboard._llm_statement_judgment_is_stale(
                loaded["compatible_row"],
                signature_sha256="changed-signature",
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
            )
        )
        self.assertTrue(
            review_dashboard._llm_statement_judgment_is_stale(
                loaded["invalid_row"],
                signature_sha256=str(manifest["sha256"]),
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
            )
        )

    def test_lean_to_tex_prompt_compatibility_is_code_owned_and_item_local(self) -> None:
        compatible_prompt = "lean-to-tex-v3-copyedit-fixture"
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "lean_to_tex_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "lean-to-tex-v2-legacy-fixture",
                        "translator": "test-translator",
                        "translated_at": "2026-07-28T00:00:00Z",
                        "items": {
                            "compatible_row": {
                                "tex_statement": "P x",
                                "lean_statement_sha256": "a" * 64,
                                "prompt_version": compatible_prompt,
                            },
                            "unknown_row": {
                                "tex_statement": "Q x",
                                "lean_statement_sha256": "b" * 64,
                                "prompt_version": "lean-to-tex-v3-unreviewed-fixture",
                                "semantic_contract_version": (
                                    review_dashboard.REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION
                                ),
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.dict(
                review_dashboard.LLM_LEAN_TO_TEX_PROMPT_SEMANTIC_CONTRACTS,
                {
                    compatible_prompt: (
                        review_dashboard.REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION
                    )
                },
            ):
                loaded = review_dashboard.load_llm_lean_to_tex_draft_entries(folder)

        self.assertEqual(loaded["compatible_row"]["prompt_version"], compatible_prompt)
        self.assertFalse(loaded["compatible_row"]["prompt_version_stale"])
        self.assertTrue(loaded["unknown_row"]["prompt_version_stale"])

    def test_statement_summary_rechecks_prompt_version_for_cached_rows(self) -> None:
        manifest = valid_manifest()
        paper_statement = "Paper statement"
        agent_statement = "Context-free Lean translation"
        ledger = valid_ledger()
        ledger.update(
            {
                "paper_statement_sha256": review_dashboard.statement_digest(
                    paper_statement
                ),
                "tex_statement_sha256": review_dashboard.statement_digest(
                    agent_statement
                ),
            }
        )
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement=paper_statement,
            agent_statement=agent_statement,
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
            llm_match_judgment="matches",
            llm_match_stale=False,
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v7-semantic-world-refinement",
                        "validator": "test-model",
                        "validated_at": "2026-07-10T00:00:00Z",
                        "items": {"row": ledger},
                    }
                ),
                encoding="utf-8",
            )
            summary = review_dashboard.statement_translation_audit_summary(
                folder, [cached_item]
            )

        self.assertEqual(summary["stale_judgment_count"], 1)
        self.assertEqual(summary["stale_judgment"], ["row"])

    def test_statement_summary_accepts_current_bound_v11_spec_judgment(self) -> None:
        paper_statement = "Verbatim source theorem"
        item = review_dashboard.ReviewItem(
            name="sourceTheoremSpec",
            full_name="Fixture.PaperInterface.sourceTheoremSpec",
            kind="def",
            lean_statement="def sourceTheoremSpec : Prop := True",
            paper_statement=paper_statement,
            agent_statement="True",
            lean_signature_sha256="1" * 64,
            source_input_bundle_sha256="2" * 64,
            llm_match_judgment="matches",
            llm_match_stale=False,
            llm_match_source="v11_raw_source_spec_screening.json",
            llm_match_validator="fixture-reviewer",
            llm_match_validator_type="llm_as_judge",
            llm_match_validated_at="2026-08-23T00:00:00Z",
            llm_match_lean_statement_sha256="3" * 64,
            llm_match_paper_statement_sha256=(
                review_dashboard.statement_digest(paper_statement)
            ),
        )
        with tempfile.TemporaryDirectory() as temp_dir, mock.patch.object(
            review_dashboard,
            "library_semantic_review_summary",
            return_value={"needs_attention": False},
        ):
            summary = review_dashboard.statement_translation_audit_summary(
                Path(temp_dir), [item]
            )

        self.assertEqual(summary["row_count"], 1)
        self.assertEqual(summary["judgment_count"], 1)
        self.assertEqual(summary["semantic_current_judgment_count"], 1)
        self.assertEqual(summary["matches"], 1)
        self.assertEqual(summary["missing_judgment"], [])
        self.assertFalse(summary["needs_attention"])

        item.llm_match_paper_statement_sha256 = "4" * 64
        with tempfile.TemporaryDirectory() as temp_dir, mock.patch.object(
            review_dashboard,
            "library_semantic_review_summary",
            return_value={"needs_attention": False},
        ):
            stale = review_dashboard.statement_translation_audit_summary(
                Path(temp_dir), [item]
            )
        self.assertEqual(stale["missing_judgment"], ["sourceTheoremSpec"])
        self.assertTrue(stale["needs_attention"])

    def test_stale_translation_reuse_requires_unique_current_semantic_pins(self) -> None:
        manifest = valid_manifest()
        paper_statement = "Paper statement"
        agent_statement = "Current context-free translation"
        item = review_dashboard.ReviewItem(
            name="current_row",
            kind="theorem",
            lean_statement="theorem current_row (x : Real) : True",
            paper_statement=paper_statement,
            agent_statement=agent_statement,
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
            source_input_bundle_sha256="b" * 64,
        )
        ledger = valid_ledger()
        ledger.update(
            {
                "lean_statement_sha256": review_dashboard.statement_digest(
                    item.lean_statement
                ),
                "paper_statement_sha256": review_dashboard.statement_digest(
                    paper_statement
                ),
                "tex_statement_sha256": review_dashboard.statement_digest(
                    agent_statement
                ),
                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                "source_input_bundle_sha256": "b" * 64,
                "lean_target_protocol": "expanded_paperinterface_spec_v1",
                "semantic_target_declaration": "Test.current_rowSpec",
            }
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "lean_to_tex_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": (
                            review_dashboard.REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION
                        ),
                        "translator": "fixture translator",
                        "translated_at": "2026-07-28T00:00:00Z",
                        "items": {
                            "current_row": {
                                "tex_statement": "legacy rendering",
                                "lean_statement_sha256": "0" * 64,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )

            def write_judgments(entries: dict[str, dict[str, object]]) -> None:
                (audit / "statement_match_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": (
                                review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION
                            ),
                            "validator": "fixture reviewer",
                            "validated_at": "2026-07-28T00:00:00Z",
                            "items": entries,
                        }
                    ),
                    encoding="utf-8",
                )

            write_judgments({"renamed_storage_key": ledger})
            reused = review_dashboard.statement_translation_audit_summary(
                folder, [item]
            )
            self.assertEqual(reused["stale_draft_count"], 0)
            self.assertEqual(
                reused["semantic_reused_stale_draft"], ["current_row"]
            )
            self.assertEqual(reused["semantic_rebound_judgment"], ["current_row"])
            self.assertFalse(reused["needs_attention"])

            duplicate = copy.deepcopy(ledger)
            write_judgments(
                {
                    "renamed_storage_key": ledger,
                    "ambiguous_storage_key": duplicate,
                }
            )
            ambiguous = review_dashboard.statement_translation_audit_summary(
                folder, [item]
            )
            self.assertEqual(
                ambiguous["ambiguous_semantic_judgment"], ["current_row"]
            )
            self.assertEqual(ambiguous["stale_draft_count"], 0)
            self.assertTrue(ambiguous["needs_attention"])

            wrong_pin = copy.deepcopy(ledger)
            wrong_pin["lean_statement_sha256"] = "1" * 64
            write_judgments({"renamed_storage_key": wrong_pin})
            pin_mismatch = review_dashboard.statement_translation_audit_summary(
                folder, [item]
            )
            self.assertEqual(pin_mismatch["stale_draft_count"], 0)
            self.assertEqual(pin_mismatch["missing_judgment_count"], 1)
            self.assertTrue(pin_mismatch["needs_attention"])

            prompt_drift = copy.deepcopy(ledger)
            prompt_drift["prompt_version"] = "statement-match-v1-stale-fixture"
            write_judgments({"renamed_storage_key": prompt_drift})
            stale_prompt = review_dashboard.statement_translation_audit_summary(
                folder, [item]
            )
            self.assertEqual(stale_prompt["stale_draft_count"], 0)
            self.assertEqual(stale_prompt["missing_judgment_count"], 1)
            self.assertTrue(stale_prompt["needs_attention"])

    def test_cache_loader_rechecks_prompt_version_for_cached_rows(self) -> None:
        manifest = valid_manifest()
        paper_statement = "Paper statement"
        agent_statement = "Context-free Lean translation"
        ledger = valid_ledger()
        ledger.update(
            {
                "paper_statement_sha256": review_dashboard.statement_digest(
                    paper_statement
                ),
                "tex_statement_sha256": review_dashboard.statement_digest(
                    agent_statement
                ),
            }
        )
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement=paper_statement,
            agent_statement=agent_statement,
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
            llm_match_judgment="matches",
            llm_match_stale=False,
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / "audit"
            traces = folder / ".review_traces"
            audit.mkdir(parents=True)
            traces.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem row (x : Real) : True := by trivial\n",
                encoding="utf-8",
            )
            (audit / "statement_match_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": "statement-match-v7-semantic-world-refinement",
                        "validator": "test-model",
                        "validated_at": "2026-07-10T00:00:00Z",
                        "items": {"row": ledger},
                    }
                ),
                encoding="utf-8",
            )
            cache_path = review_dashboard.paper_interface_cache_file(folder)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": review_dashboard._cache_source_hashes(folder),
                        "rows": [cached_item.__dict__],
                    }
                ),
                encoding="utf-8",
            )
            loaded = review_dashboard.load_cached_review_rows(folder)

        self.assertIsNotNone(loaded)
        assert loaded is not None
        self.assertTrue(loaded[0].llm_match_stale)

    def test_cache_loader_rebinds_tex_sidecar_without_reparsing_lean(self) -> None:
        manifest = valid_manifest()
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement="Paper statement",
            agent_statement="stale cached translation",
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / "audit"
            traces = folder / ".review_traces"
            audit.mkdir(parents=True)
            traces.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem row (x : Real) : True := by trivial\n",
                encoding="utf-8",
            )
            cache_path = review_dashboard.paper_interface_cache_file(folder)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": review_dashboard._cache_source_hashes(folder),
                        "rows": [cached_item.__dict__],
                    }
                ),
                encoding="utf-8",
            )
            # This sidecar is written after the cache.  It must be rebound
            # without rerunning the declaration parser or Lean Meta extraction.
            (audit / "lean_to_tex_llm.json").write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "prompt_version": review_dashboard.REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION,
                        "translator": "test-translator",
                        "translated_at": "2026-07-24T12:00:00Z",
                        "items": {
                            "row": {
                                "tex_statement": "\\forall x : \\mathbb{R}, \\mathrm{True}",
                                "lean_statement_sha256": review_dashboard.statement_digest(
                                    cached_item.lean_statement
                                ),
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                review_dashboard,
                "parse_interface_items",
                side_effect=AssertionError("sidecar update must not reparse Lean"),
            ):
                loaded = review_dashboard.load_cached_review_rows(folder)

        self.assertIsNotNone(loaded)
        assert loaded is not None
        self.assertEqual(
            loaded[0].agent_statement,
            "\\forall x : \\mathbb{R}, \\mathrm{True}",
        )

    def test_cache_loader_rebinds_report_text_without_lean_manifest_refresh(self) -> None:
        """A closeout-report edit must not repeat unchanged Lean Meta work."""

        manifest = valid_manifest()
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement="First report statement.",
            agent_statement="Lean translation",
            interface_source="theorem row (x : Real) : True",
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
        )

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            traces = folder / ".review_traces"
            traces.mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text(
                "theorem row (x : Real) : True := by trivial\n",
                encoding="utf-8",
            )
            report = folder / "FINAL_VALIDATION_REPORT.md"
            report.write_text(
                "## Current Statement\n\n- `row`: First report statement.\n",
                encoding="utf-8",
            )
            cache_path = review_dashboard.paper_interface_cache_file(folder)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": review_dashboard._cache_source_hashes(folder),
                        "rows": [cached_item.__dict__],
                    }
                ),
                encoding="utf-8",
            )
            report.write_text(
                "## Current Statement\n\n- `row`: Updated report statement.\n",
                encoding="utf-8",
            )
            with mock.patch.object(
                review_dashboard,
                "parse_interface_items",
                side_effect=AssertionError("report rebind must not run Lean extraction"),
            ):
                loaded = review_dashboard.load_cached_review_rows(folder)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))

        self.assertIsNotNone(loaded)
        assert loaded is not None
        self.assertEqual(loaded[0].paper_statement, "Updated report statement.")
        self.assertEqual(
            persisted["hashes"]["report_sha256"],
            review_dashboard.statement_digest(
                "## Current Statement\n\n- `row`: Updated report statement.\n"
            ),
        )

    def test_cache_reuses_static_rows_after_dynamic_status_change(self) -> None:
        """Status receipts and sidecar policy changes need no Lean manifest rerun."""

        manifest = valid_manifest()
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement="Paper statement",
            agent_statement="Lean translation",
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            traces = folder / ".review_traces"
            traces.mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text(
                "theorem row (x : Real) : True := by trivial\n", encoding="utf-8"
            )
            status = {
                "status": "partially formalized",
                "review_surface": {
                    "include_names": ["row"],
                    "llm_statement_review": {
                        "require_explicit_source_routes": False
                    },
                },
            }
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            cache_path = review_dashboard.paper_interface_cache_file(folder)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": review_dashboard._cache_source_hashes(folder),
                        "rows": [cached_item.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            # Overall status and dynamic audit policy do not change the review
            # rows or their elaborated Lean declarations.
            status["status"] = "formalized"
            status["review_surface"]["llm_statement_review"][
                "require_explicit_source_routes"
            ] = True
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            self.assertIsNotNone(review_dashboard.load_cached_review_rows(folder))

            # Selection fields still invalidate the cache because they change
            # the static review surface.
            status["review_surface"]["include_names"] = ["other_row"]
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            self.assertIsNone(review_dashboard.load_cached_review_rows(folder))

    def test_cache_rebinds_source_map_scope_without_lean_manifest_refresh(self) -> None:
        """Coverage-scope metadata must not discard current elaborated rows."""

        manifest = valid_manifest()
        cached_item = review_dashboard.ReviewItem(
            name="row",
            kind="theorem",
            lean_statement="theorem row (x : Real) : True",
            paper_statement="Mapped statement.",
            agent_statement="Lean translation",
            interface_source="theorem row (x : Real) : True",
            lean_signature_manifest=manifest,
            lean_signature_sha256=str(manifest["sha256"]),
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            audit = folder / "audit"
            traces = folder / ".review_traces"
            audit.mkdir(parents=True)
            traces.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem row (x : Real) : True := by trivial\n",
                encoding="utf-8",
            )
            source_map = {
                "items": {
                    "source_row": {
                        "statement": "Mapped statement.",
                        "lean_declarations": ["row"],
                    }
                }
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            cache_path = review_dashboard.paper_interface_cache_file(folder)
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": review_dashboard._cache_source_hashes(folder),
                        "rows": [cached_item.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            # An explicit closeout-scope decision changes paper-coverage
            # bookkeeping, not the selected Lean declarations or their
            # elaborated signatures.
            source_map["source_coverage_mode"] = "named_theoretical_statements"
            map_path.write_text(json.dumps(source_map), encoding="utf-8")
            with mock.patch.object(
                review_dashboard,
                "parse_interface_items",
                side_effect=AssertionError("map rebind must not run Lean extraction"),
            ):
                loaded = review_dashboard.load_cached_review_rows(folder)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))

        self.assertIsNotNone(loaded)
        assert loaded is not None
        self.assertEqual(loaded[0].paper_statement, "Mapped statement.")
        self.assertEqual(
            persisted["hashes"]["paper_statement_map_sha256"],
            review_dashboard.statement_digest(json.dumps(source_map)),
        )

    def test_loaded_conditional_boundary_preserves_v6_alignment(self) -> None:
        manifest = valid_manifest()
        manifest["atoms"].insert(
            1,
            {
                "ref": "b/extra",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {"tag": "extra-premise"},
                "display": "R x",
            },
        )
        ledger = valid_ledger()
        ledger.update(
            {
                "judgment": "mismatch",
                "resolution": "conditional_boundary",
                "unjustified_lean_inputs": ["l_extra_assumption"],
            }
        )
        ledger["lean_obligations"].insert(
            1,
            {
                "id": "l_extra_assumption",
                "kind": "assumption",
                "signature_ref": "b/extra",
            },
        )
        classify_operator_free(
            ledger["semantic_scope_review"], lean_ids=("l_extra_assumption",)
        )
        refresh_manifest_digest(ledger, manifest)
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()

            def load() -> dict[str, object]:
                (audit / "statement_match_llm.json").write_text(
                    json.dumps(
                        {
                            "schema": 1,
                            "paper": folder.name,
                            "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                            "validator": "independent-test",
                            "validated_at": "2026-07-10T00:00:00Z",
                            "items": {"row": ledger},
                        }
                    ),
                    encoding="utf-8",
                )
                return review_dashboard.load_llm_statement_judgments(
                    folder, {"row": manifest}
                )["row"]

            loaded = load()
            self.assertTrue(review_dashboard._is_conditional_boundary_judgment(loaded))
            ledger["obligation_alignment"][1]["relation"] = "lean_implies_source"
            directional = load()
            self.assertEqual(directional["obligation_ledger_error"], "")
            self.assertFalse(
                review_dashboard._is_conditional_boundary_judgment(directional)
            )

    def test_semantic_bridge_declaration_routes_exact_source_statement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            statement = "For every feasible x, the value is at most one."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_claim": {
                                "statement": statement,
                                "semantic_bridge_declarations": ["arbitrarily_named_bridge"],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_paper_statement_map(folder)
            self.assertEqual(parsed["arbitrarily_named_bridge"], statement)

        item = {
            "statement": statement,
            "lean_declarations": ["paper_endpoint"],
            "semantic_bridge_declarations": ["arbitrarily_named_bridge"],
        }
        self.assertEqual(
            review_dashboard.source_item_direct_coverage_declarations(item),
            ["paper_endpoint"],
        )
        self.assertEqual(
            review_dashboard.source_item_statement_routing_declarations(item),
            ["paper_endpoint", "arbitrarily_named_bridge"],
        )

    def test_semantic_contract_spec_routes_comparison_text_without_coverage_credit(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            statement = "For every feasible input, the complete source conclusion holds."
            item = {
                "statement": statement,
                "lean_declarations": ["paper_endpoint"],
                "spec_lean_declarations": ["declared_spec"],
                "semantic_contract": {
                    "spec_declaration": "contract_spec",
                    "evidence_declaration": "paper_endpoint",
                    "evidence_mode": "proves",
                    "semantic_shape": "plain",
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {"source_claim": item}}),
                encoding="utf-8",
            )

            parsed = review_dashboard.parse_paper_statement_map(folder)

        self.assertEqual(parsed["paper_endpoint"], statement)
        self.assertEqual(parsed["declared_spec"], statement)
        self.assertEqual(parsed["contract_spec"], statement)
        self.assertEqual(
            review_dashboard.source_item_direct_coverage_declarations(item),
            ["paper_endpoint"],
        )
        self.assertEqual(
            review_dashboard.source_item_statement_routing_declarations(item),
            ["paper_endpoint", "declared_spec", "contract_spec"],
        )

    def test_navigation_alias_does_not_route_source_statement(self) -> None:
        """An alias cannot turn a named wrapper into a semantic audit row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_claim": {
                                "statement": "The source conclusion.",
                                "lean_declarations": ["semantic_endpoint"],
                                "aliases": ["renamed_partial_wrapper"],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            parsed = review_dashboard.parse_paper_statement_map(folder)

        self.assertNotIn("renamed_partial_wrapper", parsed)
        self.assertEqual(parsed["semantic_endpoint"], "The source conclusion.")

    def test_component_route_uses_pinned_quote_not_parent_theorem_text(self) -> None:
        """A formula row may display one pinned source component honestly."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            parent_statement = "The parent theorem has several independent conclusions."
            component_quote = "The second component is the displayed scalar formula."
            component_hash = hashlib.sha256(
                component_quote.encode("utf-8")
            ).hexdigest()
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "opaque_source_item": {
                                "statement": parent_statement,
                                "source_kind": "lemma",
                                "source_location": "source.txt:10-20",
                                "source_components": [
                                    {
                                        "component": "scalar formula",
                                        "source_location": "source.txt:16-17",
                                        "source_anchor_evidence": [
                                            {
                                                "quoted_text": component_quote,
                                                "quoted_text_sha256": component_hash,
                                            }
                                        ],
                                    }
                                ],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_component_statement_routes": [
                                {
                                    "row": "unrelated_formula_row",
                                    "source_item": "opaque_source_item",
                                    "source_component_anchor_sha256": component_hash,
                                    "source_location": "source.txt:16-17",
                                }
                            ]
                        }
                    }
                ),
                encoding="utf-8",
            )

            key = review_dashboard.source_component_route_key(
                "opaque_source_item", component_hash
            )
            components = review_dashboard.paper_source_component_route_inventory(folder)
            self.assertEqual(
                components[key]["statement"],
                review_dashboard.normalize_statement(component_quote),
            )
            displayed = review_dashboard.collected_paper_statements(folder)
            self.assertEqual(
                displayed["unrelated_formula_row"],
                review_dashboard.normalize_statement(component_quote),
            )
            self.assertNotEqual(
                displayed["unrelated_formula_row"], parent_statement
            )

            # A location mismatch must not fall back to an unpinned component.
            status = json.loads((folder / "status.json").read_text(encoding="utf-8"))
            status["review_surface"]["source_component_statement_routes"][0][
                "source_location"
            ] = "source.txt:17-18"
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            self.assertNotIn(
                "unrelated_formula_row",
                review_dashboard.review_source_component_statement_routes(folder),
            )

    def test_corrected_target_excludes_alias_and_support_components(self) -> None:
        """Only a designated complete endpoint may receive a repaired target."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            audit = folder / "audit"
            audit.mkdir()
            archival = "The archival assertion permits every input."
            corrected = "Under the explicit finite convention, the repaired result holds."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "opaque_source_key": {
                                "statement": archival,
                                "coverage_status": "corrected_source_statement",
                                "corrected_target": {
                                    "schema": 1,
                                    "statement": corrected,
                                },
                                "lean_declarations": ["complete_endpoint"],
                                "aliases": ["named_but_partial_alias"],
                                "proof_lean_declarations": ["partial_proof_step"],
                                "support_lean_declarations": ["partial_support_step"],
                                "spec_lean_declarations": ["comparison_spec"],
                                "semantic_contract": {
                                    "spec_declaration": "comparison_spec",
                                    "evidence_declaration": "complete_endpoint",
                                    "evidence_mode": "proves",
                                    "semantic_shape": "plain",
                                },
                                "semantic_bridge_declarations": ["partial_bridge"],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            parsed = review_dashboard.parse_paper_statement_map(folder)

        self.assertEqual(parsed["opaque_source_key"], archival)
        self.assertEqual(parsed["complete_endpoint"], corrected)
        self.assertEqual(parsed["comparison_spec"], corrected)
        for partial_name in (
            "named_but_partial_alias",
            "partial_proof_step",
            "partial_support_step",
            "partial_bridge",
        ):
            self.assertNotIn(partial_name, parsed)

    def test_semantic_bridge_fields_are_strict_string_lists(self) -> None:
        self.assertIsNone(
            audit_repository.source_inventory_semantic_bridge_names(
                {"semantic_bridge_declarations": ["valid_bridge", 7]}
            )
        )
        self.assertIsNone(
            audit_repository.source_inventory_semantic_bridge_names(
                {"semantic_bridge_declarations": [""]}
            )
        )

    def test_assumption_surface_bridge_comment_is_audited(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            source_path = folder / "PaperInterface.lean"
            assumption_path = folder / "Assumptions.lean"
            source_path.write_text("", encoding="utf-8")
            assumption_path.write_text(
                "/-- Source status: Theorem 3, p. 9. -/\n"
                "theorem arbitrary_bridge_name : True := by trivial\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": [],
                            "assumption_names": ["arbitrary_bridge_name"],
                        }
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(
                    audit_repository,
                    "review_surface_source_file_path",
                    return_value=source_path,
                ),
                mock.patch.object(
                    audit_repository,
                    "assumption_source_file_path",
                    return_value=assumption_path,
                ),
            ):
                names, comments = audit_repository.paper_reviewed_semantic_bridge_names(
                    folder, include_legacy_comment_hygiene=True
                )
            self.assertIn("arbitrary_bridge_name", names)
            self.assertIn("Source status:", comments["arbitrary_bridge_name"])


if __name__ == "__main__":
    unittest.main()
