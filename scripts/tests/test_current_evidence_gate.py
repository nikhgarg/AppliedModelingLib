#!/usr/bin/env python3
"""Current evidence acceptance is exact, complete, and fail-closed."""

from __future__ import annotations

import tempfile
import unittest
from collections.abc import Iterator
from contextlib import ExitStack, contextmanager
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as validators
from scripts import source_manifest_validation as source_validation
from scripts.current_closeout import evidence_gate
from scripts.evidence_run_context import (
    CommonEvidenceRunContextInputs,
    EvidenceJSONSnapshot,
    V11EvidenceRunContext,
)


class CurrentEvidenceGateTests(unittest.TestCase):
    @contextmanager
    def _validator_results(
        self,
        **overrides: list[validators.Finding],
    ) -> Iterator[dict[str, mock.Mock]]:
        functions = {
            "report_generator": "check_report_generator",
            "duplicate_sidecars": "check_duplicate_sidecars",
            "placeholder_evidence": "check_placeholder_evidence",
            "assumption_alignment": "check_full_closeout_assumption_alignment",
            "source_manifest": "check_source_manifest",
            "semantic_contract_inventory": "semantic_contract_inventory_findings",
            "source_route": "current_v11_source_route_findings",
            "source_proof_fidelity": "source_proof_fidelity_findings",
            "validator_independence": "check_validator_independence",
            "human_review_metadata": "check_human_review",
            "vacuous_assumptions": "check_vacuous_assumptions",
            "active_status": "check_active_status",
            "focused_build_route": "check_build_coverage",
        }
        with ExitStack() as stack:
            patched = {
                family: stack.enter_context(
                    mock.patch.object(
                        source_validation if family == "source_proof_fidelity" else validators,
                        function,
                        return_value=overrides.get(family, []),
                    )
                )
                for family, function in functions.items()
            }
            stack.enter_context(
                mock.patch.object(
                    validators,
                    "lake_targets",
                    return_value=(set(), set()),
                )
            )
            yield patched

    def _context(self, root: Path) -> V11EvidenceRunContext:
        folder = (root / "papers" / "Fixture").resolve()
        report = root / "scripts" / "refresh_validation_report_audit_summaries.py"
        lakefile = root / "lakefile.toml"
        status = EvidenceJSONSnapshot(
            path=folder / "status.json",
            sha256="a" * 64,
            payload={
                "status": "formalized",
                "human_review": {
                    "reviewed_rows": 0,
                    "total_rows": 0,
                    "stale_rows": 0,
                    "mismatch_rows": 0,
                },
            },
            raw_bytes=b"{}",
        )
        config = EvidenceJSONSnapshot(
            path=root / "papers" / "audit_config.json",
            sha256="b" * 64,
            payload={"schema": 1, "active_papers": []},
            raw_bytes=b"{}",
        )
        statement_map = EvidenceJSONSnapshot(
            path=folder / "audit" / "paper_statement_map.json",
            sha256="c" * 64,
            payload={"items": {}},
            raw_bytes=b"{}",
        )
        sidecars = (
            EvidenceJSONSnapshot(report, "d" * 64, None, b"report"),
            EvidenceJSONSnapshot(lakefile, "e" * 64, None, b"lake"),
            EvidenceJSONSnapshot(
                folder / ".review_traces" / "paper_theorem_validations.jsonl",
                None,
                None,
                None,
            ),
            EvidenceJSONSnapshot(
                folder / "Assumptions.lean",
                "f" * 64,
                None,
                b"",
            ),
        )
        return CommonEvidenceRunContextInputs(
            folder=folder,
            status="formalized",
            audit_config_snapshot=config,
            status_snapshot=status,
            statement_map_snapshot=statement_map,
            source_proof_fidelity_snapshot=None,
            sidecar_snapshots=sidecars,
            source_proof_fidelity_path_error="",
        ).issue_v11(None)

    def test_missing_primary_acceptance_stops_before_validators(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            context = self._context(root)
            with (
                mock.patch.object(
                    evidence_gate,
                    "accepted_current_v11_primary_gate",
                    return_value=None,
                ),
                self._validator_results() as families,
            ):
                findings = evidence_gate.run_current_evidence_gate(
                    repository_root=root,
                    paper_id="Fixture",
                    release=False,
                    require_source_bytes=True,
                    context=context,
                )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("primary acceptance", findings[0].message)
        for validator in families.values():
            validator.assert_not_called()

    def test_each_error_family_cannot_issue_acceptance(self) -> None:
        for failing_family in evidence_gate.CURRENT_EVIDENCE_FAMILIES:
            with self.subTest(family=failing_family), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                context = self._context(root)
                error = validators.Finding(
                    "ERROR",
                    "Fixture",
                    "papers/Fixture/audit/paper_statement_map.json",
                    f"injected {failing_family} failure",
                )
                with (
                    mock.patch.object(
                        evidence_gate,
                        "accepted_current_v11_primary_gate",
                        return_value=object(),
                    ),
                    self._validator_results(**{failing_family: [error]}),
                    mock.patch.object(
                        evidence_gate,
                        "_issue_current_v11_evidence_integrity",
                    ) as issue,
                ):
                    findings = evidence_gate.run_current_evidence_gate(
                        repository_root=root,
                        paper_id="Fixture",
                        release=False,
                        require_source_bytes=True,
                        context=context,
                    )

                self.assertEqual(findings, [error])
                issue.assert_not_called()

    def test_complete_conjunction_issues_exact_acceptance(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            context = self._context(root)
            warning = validators.Finding(
                "WARN",
                "Fixture",
                "papers/Fixture/status.json",
                "human review remains optional",
            )
            with (
                mock.patch.object(
                    evidence_gate,
                    "accepted_current_v11_primary_gate",
                    return_value=object(),
                ),
                self._validator_results(
                    validator_independence=[warning]
                ) as families,
                mock.patch.object(
                    evidence_gate,
                    "_issue_current_v11_evidence_integrity",
                    return_value=object(),
                ) as issue,
            ):
                findings = evidence_gate.run_current_evidence_gate(
                    repository_root=root,
                    paper_id="Fixture",
                    release=True,
                    require_source_bytes=True,
                    diagnostics={},
                    context=context,
                )

        self.assertEqual(findings, [warning])
        self.assertEqual(
            tuple(families),
            evidence_gate.CURRENT_EVIDENCE_FAMILIES,
        )
        for validator in families.values():
            validator.assert_called_once()
        issue.assert_called_once_with(
            context,
            (warning,),
            release=True,
            require_source_bytes=True,
        )


if __name__ == "__main__":
    unittest.main()
