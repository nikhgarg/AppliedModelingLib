#!/usr/bin/env python3
"""Generic closeout regressions for recursive operational proposition fields."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for path in (ROOT, ROOT / "scripts"):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

import source_record_operational_prop_obligations as OBLIGATIONS


SOURCE_KEY = "source-assumption-fixture"
SOURCE_SHA = "a" * 64


def operational_field(
    kind: str,
    *,
    alias: str = "CarrierAlias",
    predicate: str = "predicate",
) -> dict[str, object]:
    """Return unrelated formula families with the same type-level role."""

    formulas = {
        "calculus": (
            f"forall (background : {alias}) (left right : Real), "
            f"left < right -> exists slope : Real, {predicate} background left right slope"
        ),
        "probability": (
            f"forall (sample : {alias}) (event : Nat), "
            f"0 <= event -> {predicate} sample event"
        ),
        "optimization": (
            f"forall (candidate : {alias}) (budget : Nat), "
            f"0 <= budget -> {predicate} candidate budget"
        ),
    }
    return {
        "judgment_key": f"Fixture.{kind}.derived_property",
        "type": formulas[kind],
        "nested_structures": [],
    }


def approved_convention_judgment() -> dict[str, object]:
    return {
        "classification": "approved_source_convention",
        "source_location": "source.txt:100-130",
        "source_target_disposition": "approved_source_convention",
    }


def explicit_source_judgment(field: dict[str, object]) -> dict[str, object]:
    return {
        "classification": "validated_source_assumption",
        "source_target_disposition": "literal_source_match",
        "operational_prop_obligation": {
            "schema": 1,
            "route": "explicit_semantically_matched_source_assumption",
            "field_type_sha256": OBLIGATIONS.field_type_sha256(field),
            "source_assumption": {
                "source_item_key": SOURCE_KEY,
                "source_item_semantic_sha256": SOURCE_SHA,
                "source_locator": "source.txt:100-130",
                "source_formula": "For every admissible state, the stated property holds.",
                "semantic_match": "The quantified source condition has the same carrier, parameters, and property as the expanded Lean field.",
            },
        },
    }


def bridge_judgment(field: dict[str, object]) -> dict[str, object]:
    component_sha = OBLIGATIONS.source_claim_component_sha256(field)
    return {
        "classification": "proved_from_primitives",
        "operational_prop_obligation": {
            "schema": 1,
            "route": "checked_lean_bridge",
            "field_type_sha256": OBLIGATIONS.field_type_sha256(field),
            "bridge": {
                "declaration": "Fixture.Bridge.derivedProperty",
                "field_type_sha256": OBLIGATIONS.field_type_sha256(field),
                "component_sha256": component_sha,
                "source_antecedent_keys": ["Fixture.Source.assumption"],
            },
        },
    }


class OperationalPropFieldObligationTests(unittest.TestCase):
    def test_convention_does_not_close_any_operational_formula_family(self) -> None:
        for kind in ("calculus", "probability", "optimization"):
            with self.subTest(kind=kind):
                field = operational_field(kind)
                errors = OBLIGATIONS.operational_prop_field_obligation_errors(
                    field,
                    approved_convention_judgment(),
                    current_component_sha256s_by_source_judgment_key={
                        str(field["judgment_key"]): {
                            OBLIGATIONS.source_claim_component_sha256(field)
                        }
                    },
                )
                self.assertTrue(errors)
                self.assertIn("no source-claim semantic contract", errors[0])

    def test_alias_and_predicate_renaming_do_not_change_the_policy(self) -> None:
        original = operational_field("calculus")
        renamed = operational_field(
            "calculus",
            alias="OtherNamespace.ArbitraryState",
            predicate="differentRelation",
        )
        self.assertEqual(
            OBLIGATIONS.recursive_field_proposition_status(original),
            OBLIGATIONS.recursive_field_proposition_status(renamed),
        )
        self.assertEqual(
            bool(
                OBLIGATIONS.operational_prop_field_obligation_errors(
                    original, approved_convention_judgment()
                )
            ),
            bool(
                OBLIGATIONS.operational_prop_field_obligation_errors(
                    renamed, approved_convention_judgment()
                )
            ),
        )

    def test_known_data_and_containers_need_component_contracts(self) -> None:
        data = {
            "judgment_key": "Fixture.Data.measure",
            "type": "MeasureTheory.Measure Outcome",
            "nested_structures": [],
        }
        container = {
            "judgment_key": "Fixture.Container.child",
            "type": "OpaqueCarrier",
            "nested_structures": ["Fixture.Child"],
        }
        self.assertTrue(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                data,
                approved_convention_judgment(),
                current_component_sha256s_by_source_judgment_key={
                    str(data["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(data)
                    }
                },
            )
        )
        self.assertTrue(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                container,
                approved_convention_judgment(),
                current_component_sha256s_by_source_judgment_key={
                    str(container["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(container)
                    }
                },
            )
        )

    def test_exact_recursive_container_route_is_structural_only(self) -> None:
        field = {
            "judgment_key": "Fixture.Model.child",
            "source_component_section": "recursive_field_items",
            "source_claim_component_kind": "recursive_record_field",
            "type": "Fixture.Child",
            "nested_structures": ["Fixture.Child"],
            "recursive_field_explicit_parent_route": {
                "permitted_classifications": ["container_recursively_audited"]
            },
        }
        judgment = {"classification": "container_recursively_audited"}
        self.assertEqual(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                field,
                judgment,
                current_component_sha256s_by_source_judgment_key={
                    str(field["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(field)
                    }
                },
            ),
            [],
        )

    def test_opaque_leaf_requires_a_sort_refresh_instead_of_data_credit(self) -> None:
        field = {
            "judgment_key": "Fixture.Opaque.leaf",
            "type": "OtherNamespace.HiddenAlias parameter",
            "nested_structures": [],
        }
        errors = OBLIGATIONS.operational_prop_field_obligation_errors(
            field,
            approved_convention_judgment(),
            current_component_sha256s_by_source_judgment_key={
                str(field["judgment_key"]): {
                    OBLIGATIONS.source_claim_component_sha256(field)
                }
            },
        )
        self.assertTrue(errors)
        self.assertIn("no source-claim semantic contract", errors[0])

    def test_explicit_field_level_source_assumption_requires_current_identity(self) -> None:
        field = operational_field("probability", alias="ProbabilityState")
        judgment = explicit_source_judgment(field)
        self.assertEqual(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                field,
                judgment,
                source_item_semantic_sha256_by_key={SOURCE_KEY: SOURCE_SHA},
                current_component_sha256s_by_source_judgment_key={
                    str(field["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(field)
                    }
                },
                current_explicit_source_assumption_keys={str(field["judgment_key"])},
                allow_legacy_implicit_route=True,
            ),
            [],
        )
        self.assertTrue(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                field,
                judgment,
                source_item_semantic_sha256_by_key={SOURCE_KEY: "b" * 64},
                current_component_sha256s_by_source_judgment_key={
                    str(field["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(field)
                    }
                },
                current_explicit_source_assumption_keys={str(field["judgment_key"])},
                allow_legacy_implicit_route=True,
            )
        )

    def test_legacy_implicit_source_route_does_not_raise(self) -> None:
        """The compatibility fallback must fail/close by result, never NameError."""

        field = operational_field("calculus")
        key = str(field["judgment_key"])
        self.assertEqual(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                field,
                {"classification": "validated_source_assumption"},
                current_component_sha256s_by_source_judgment_key={
                    key: {OBLIGATIONS.source_claim_component_sha256(field)}
                },
                current_explicit_source_assumption_keys={key},
                allow_legacy_implicit_route=True,
            ),
            [],
        )

    def test_checked_bridge_requires_a_lean_owned_receipt_not_a_label(self) -> None:
        field = operational_field("optimization", alias="DecisionCarrier")
        judgment = bridge_judgment(field)
        judgment["operational_prop_obligation"]["bridge"]["lean_checked"] = True  # type: ignore[index]
        errors = OBLIGATIONS.operational_prop_field_obligation_errors(
            field,
            judgment,
            current_exact_source_antecedent_keys={"Fixture.Source.assumption"},
            current_component_sha256s_by_source_judgment_key={
                str(field["judgment_key"]): {
                    OBLIGATIONS.source_claim_component_sha256(field)
                }
            },
            allow_legacy_implicit_route=True,
        )
        self.assertTrue(errors)
        self.assertIn("Lean-generated", errors[-1])

        receipt = OBLIGATIONS.CheckedLeanBridgeReceipt(
            component_key=str(field["judgment_key"]),
            declaration="Fixture.Bridge.derivedProperty",
            component_sha256=OBLIGATIONS.source_claim_component_sha256(field),
            field_type_sha256=OBLIGATIONS.field_type_sha256(field),
            source_antecedent_keys=frozenset({"Fixture.Source.assumption"}),
        )
        self.assertEqual(
            OBLIGATIONS.operational_prop_field_obligation_errors(
                field,
                judgment,
                current_exact_source_antecedent_keys={"Fixture.Source.assumption"},
                checked_lean_bridge_receipts={receipt},
                current_component_sha256s_by_source_judgment_key={
                    str(field["judgment_key"]): {
                        OBLIGATIONS.source_claim_component_sha256(field)
                    }
                },
                allow_legacy_implicit_route=True,
            ),
            [],
        )

    def test_bridge_cannot_reuse_its_own_field_as_a_source_antecedent(self) -> None:
        field = operational_field("calculus")
        judgment = bridge_judgment(field)
        bridge = judgment["operational_prop_obligation"]["bridge"]  # type: ignore[index]
        bridge["source_antecedent_keys"] = [field["judgment_key"]]  # type: ignore[index]
        errors = OBLIGATIONS.operational_prop_field_obligation_errors(
            field,
            judgment,
            current_exact_source_antecedent_keys={str(field["judgment_key"])},
            current_component_sha256s_by_source_judgment_key={
                str(field["judgment_key"]): {
                    OBLIGATIONS.source_claim_component_sha256(field)
                }
            },
            allow_legacy_implicit_route=True,
        )
        self.assertTrue(errors)
        self.assertTrue(any("may not include" in error for error in errors))


if __name__ == "__main__":
    unittest.main()
