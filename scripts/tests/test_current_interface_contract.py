"""Regression tests for typed current paper-interface routes."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.current_closeout.declarations import LeanDeclaration
from scripts.current_closeout.primary_gate import (
    partition_review_routes,
)
from scripts.obligation_routes import EvidenceRouteSet


def _result_routes() -> EvidenceRouteSet:
    return EvidenceRouteSet.from_source_map(
        {
            "items": {
                "first": {
                    "claim_bearing": True,
                    "source_kind": "theorem",
                    "inventory_role": "named_result",
                    "semantic_contract": {
                        "spec_declaration": "Fixture.firstSpec",
                        "evidence_declaration": "Fixture.first_proof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
                "second": {
                    "claim_bearing": True,
                    "source_kind": "theorem",
                    "inventory_role": "named_result",
                    "semantic_contract": {
                        "spec_declaration": "Fixture.secondSpec",
                        "evidence_declaration": "Fixture.second_proof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    },
                },
            }
        }
    )


def _declaration(path: Path, name: str, kind: str) -> LeanDeclaration:
    return LeanDeclaration(
        path=path,
        line=1,
        kind=kind,
        name=name.rsplit(".", 1)[-1],
        source="",
        qualified_name=name,
        identity_authority="lean_environment",
    )


class CurrentInterfaceContractTests(unittest.TestCase):
    def test_review_surface_must_select_every_typed_result_spec(self) -> None:
        interface = Path("/tmp/Fixture/PaperInterface.lean")
        first = _declaration(interface, "Fixture.firstSpec", "def")
        second = _declaration(interface, "Fixture.secondSpec", "def")
        declarations = {
            "Fixture.firstSpec": [first],
            "firstSpec": [first],
            "Fixture.secondSpec": [second],
            "secondSpec": [second],
        }

        partition = partition_review_routes(
            paper_id="Fixture",
            review_names=["firstSpec"],
            route_set=_result_routes(),
            declarations=declarations,
        )

        self.assertTrue(
            any("omits typed source-result Spec(s)" in error for error in partition.errors),
            partition.errors,
        )

if __name__ == "__main__":
    unittest.main()
