#!/usr/bin/env python3
"""Regression tests for the non-accepting native strict transaction."""

from __future__ import annotations

import unittest
from types import MappingProxyType, SimpleNamespace
from unittest import mock

from scripts.closeout_pipeline import (
    STAGE_DEPENDENCIES,
    CloseoutContext,
    CloseoutStage,
    StageReceipt,
)
from scripts.strict_closeout_authority import (
    CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA,
    CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
    CurrentStrictCloseoutAuthority,
    StrictCloseoutAuthority,
    StrictCloseoutAuthorityError,
    authenticate_strict_closeout_authority,
    issue_current_strict_closeout_authority,
    recorded_strict_closeout_authority,
    validate_strict_closeout_authority,
)


class StrictCloseoutAuthorityTests(unittest.TestCase):
    def test_current_authority_records_contract_not_operational_stage_hashes(self) -> None:
        accepted = SimpleNamespace(
            paper="Fixture",
            engine_registration=lambda: self.engine(),
        )
        with mock.patch(
            "scripts.current_closeout.pass_capability.validate_current_closeout_pass",
            return_value=accepted,
        ):
            authority = issue_current_strict_closeout_authority(
                mock.sentinel.current_pass
            )
        self.assertIsInstance(authority, CurrentStrictCloseoutAuthority)
        projection = authority.projection()
        self.assertEqual(projection["schema"], CURRENT_STRICT_CLOSEOUT_AUTHORITY_SCHEMA)
        self.assertEqual(
            projection["closeout_contract_sha256"],
            CURRENT_STRICT_CLOSEOUT_CONTRACT_SHA256,
        )
        self.assertNotIn("context_sha256", projection)
        self.assertNotIn("stage_receipt_sha256s", projection)
        self.assertEqual(recorded_strict_closeout_authority(projection), authority)

    def test_current_authority_identity_ignores_operational_context_and_stages(
        self,
    ) -> None:
        first_pass = SimpleNamespace(
            paper="Fixture",
            engine_registration=lambda: self.engine(),
            closeout_context=SimpleNamespace(context_sha256="1" * 64),
            operational_stage_receipt_sha256s={"source_inventory": "2" * 64},
        )
        second_pass = SimpleNamespace(
            paper="Fixture",
            engine_registration=lambda: self.engine(),
            closeout_context=SimpleNamespace(context_sha256="3" * 64),
            operational_stage_receipt_sha256s={"source_inventory": "4" * 64},
        )
        with mock.patch(
            "scripts.current_closeout.pass_capability.validate_current_closeout_pass",
            side_effect=(first_pass, second_pass),
        ):
            first = issue_current_strict_closeout_authority(mock.sentinel.first_pass)
            second = issue_current_strict_closeout_authority(mock.sentinel.second_pass)
        self.assertEqual(first, second)

    def context(self) -> CloseoutContext:
        return CloseoutContext(
            paper="Fixture",
            plan_identity_sha256="1" * 64,
            source_map_sha256="2" * 64,
            status_sha256="3" * 64,
            route_set_sha256="4" * 64,
            route_object=MappingProxyType({"schema": 1}),
            content_inputs_sha256="5" * 64,
            compiled_inputs_sha256="6" * 64,
            lean_closure_sha256="7" * 64,
            protocol_sha256="8" * 64,
            context_sha256="9" * 64,
        )

    def stages(self, context: CloseoutContext) -> dict[CloseoutStage, StageReceipt]:
        result: dict[CloseoutStage, StageReceipt] = {}
        for index, stage in enumerate(CloseoutStage, start=1):
            if stage is CloseoutStage.CANONICAL_RECEIPT:
                break
            dependencies = tuple(
                (dependency.value, result[dependency].receipt_sha256)
                for dependency in STAGE_DEPENDENCIES[stage]
            )
            result[stage] = StageReceipt(
                stage=stage,
                paper=context.paper,
                context_sha256=context.context_sha256,
                input_sha256=f"{index:x}" * 64,
                dependency_receipt_sha256s=dependencies,
                output_object=MappingProxyType(
                    {"schema": 1, "sha256": f"{index + 8:x}" * 64}
                ),
                metrics=MappingProxyType({}),
                receipt_sha256=f"{index + 1:x}" * 64,
            )
        return result

    def engine(self) -> dict[str, object]:
        return {
            "engine_tree_sha256": "a" * 64,
            "review_semantic_class_sha256": "b" * 64,
            "revision_sequence": 1,
            "registration_kind": "independent",
            "engine_file_count": 1,
        }

    def test_complete_stage_chain_yields_one_nonaccepting_portable_authority(self) -> None:
        context = self.context()
        authority = authenticate_strict_closeout_authority(
            context, self.stages(context), self.engine()
        )
        self.assertFalse(authority.projection()["acceptance_credential"])
        self.assertEqual(authority.paper, "Fixture")
        self.assertEqual(len(authority.stage_receipt_sha256s), 8)
        self.assertEqual(len(authority.authority_sha256), 64)

    def test_missing_stage_and_broken_dependency_fail_closed(self) -> None:
        context = self.context()
        stages = self.stages(context)
        stages.pop(CloseoutStage.LEAN_ATTESTATION)
        with self.assertRaisesRegex(StrictCloseoutAuthorityError, "missing stages"):
            authenticate_strict_closeout_authority(context, stages, self.engine())

        stages = self.stages(context)
        focused = stages[CloseoutStage.FOCUSED_BUILD]
        stages[CloseoutStage.FOCUSED_BUILD] = StageReceipt(
            stage=focused.stage,
            paper=focused.paper,
            context_sha256=focused.context_sha256,
            input_sha256=focused.input_sha256,
            dependency_receipt_sha256s=((CloseoutStage.STRICT_INTEGRATION.value, "f" * 64),),
            output_object=focused.output_object,
            metrics=focused.metrics,
            receipt_sha256=focused.receipt_sha256,
        )
        with self.assertRaisesRegex(StrictCloseoutAuthorityError, "broken dependency"):
            authenticate_strict_closeout_authority(context, stages, self.engine())

    def test_mutated_authority_identity_fails_closed(self) -> None:
        context = self.context()
        authority = authenticate_strict_closeout_authority(
            context, self.stages(context), self.engine()
        )
        corrupt = StrictCloseoutAuthority(
            paper=authority.paper,
            context_sha256=authority.context_sha256,
            engine_tree_sha256=authority.engine_tree_sha256,
            stage_receipt_sha256s=authority.stage_receipt_sha256s,
            authority_sha256="f" * 64,
        )
        with self.assertRaisesRegex(StrictCloseoutAuthorityError, "identity is corrupt"):
            validate_strict_closeout_authority(corrupt)


if __name__ == "__main__":
    unittest.main()
