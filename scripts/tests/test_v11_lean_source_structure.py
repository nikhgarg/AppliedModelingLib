#!/usr/bin/env python3
"""Regressions for the Lean-owned v11 source-structure closeout gate."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import audit_repository as audit
from scripts.current_closeout.primary_gate import source_structure_errors


def canonical_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


class V11LeanSourceStructureTests(unittest.TestCase):
    def _surface(
        self,
        *,
        assumption_path: Path | None = None,
        malformed_role: bool = False,
    ) -> object:
        atoms = [
            {
                "ref": "b/0",
                "role": "parameter",
                "binder_info": "explicit",
                "canonical": {"tag": "const", "name": "Nat"},
                "display": "Nat",
            },
            {
                "ref": "result",
                "role": "assumption" if malformed_role else "conclusion",
                "canonical": {"tag": "const", "name": "True"},
                "display": "True",
            },
        ]
        semantic_atoms = [
            {key: value for key, value in atom.items() if key != "display"}
            for atom in atoms
        ]
        atom_digest = canonical_sha256({"schema": 1, "atoms": semantic_atoms})
        manifest_digest = hashlib.sha256(b"manifest").hexdigest()
        declarations: dict[str, object] = {}
        if assumption_path is not None:
            declarations["Fixture.unlistedSupport"] = {
                "source_path": assumption_path,
            }
        return SimpleNamespace(
            semantic_targets={
                "Fixture.SourceSpec": {
                    "review_claim_atoms": atoms,
                    "review_claim_atoms_sha256": atom_digest,
                    "review_claim_manifest_sha256": manifest_digest,
                }
            },
            review_claim_manifests={
                "Fixture.SourceSpec": {
                    "semantic_review_declaration": "Fixture.SourceSpec",
                    "schema": 1,
                    "manifest_sha256": manifest_digest,
                    "claim_atoms_sha256": atom_digest,
                    "claim_atoms": atoms,
                }
            },
            source_declarations=declarations,
        )

    def test_current_v11_closeout_never_resolves_legacy_raw_payload(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            stage = mock.Mock()
            context = SimpleNamespace(
                issued_by_builder=True,
                selected_v11_closeout=True,
                current_v11_closeout=True,
                v11_direct_semantic_review_current=True,
                v11_lean_review_surface=self._surface(),
                stage_strict_v11_source_record_judgment_handoff=stage,
            )
            context.current_v11_primary_gate_result = lambda: SimpleNamespace(
                configuration_errors=(),
                semantic_errors=(),
                structure_errors=source_structure_errors(
                    paper_id="Fixture",
                    folder=folder,
                    review_surface={"assumption_policy": "strict"},
                    surface=context.v11_lean_review_surface,
                    declaration_index={},
                ),
            )
            prevalidated: set[str] = set()
            with mock.patch.object(
                audit,
                "source_record_structural_payload_for_closeout",
                side_effect=AssertionError("legacy raw source-record path was resolved"),
            ):
                findings = audit.check_source_record_audit(
                    "Fixture",
                    folder,
                    {"assumption_policy": "strict"},
                    "formalized",
                    True,
                    paper_closeout=True,
                    prevalidated_strict_v11_occurrence_papers=prevalidated,
                    run_context=context,  # type: ignore[arg-type]
                )

        self.assertEqual(findings, [])
        self.assertEqual(prevalidated, {"Fixture"})
        stage.assert_called_once_with()

    def test_lean_claim_roles_and_assumption_inventory_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            assumption_path = folder / "Assumptions.lean"
            assumption_path.write_text("def unlistedSupport : Prop := True\n")
            context = SimpleNamespace(
                issued_by_builder=True,
                selected_v11_closeout=True,
                current_v11_closeout=True,
                v11_direct_semantic_review_current=True,
                v11_lean_review_surface=self._surface(
                    assumption_path=assumption_path,
                    malformed_role=True,
                ),
                stage_strict_v11_source_record_judgment_handoff=mock.Mock(),
            )
            review_surface = {
                "assumption_policy": "strict",
                "assumption_names": [],
                "auxiliary_names": [],
            }
            context.current_v11_primary_gate_result = lambda: SimpleNamespace(
                configuration_errors=(),
                semantic_errors=(),
                structure_errors=source_structure_errors(
                    paper_id="Fixture",
                    folder=folder,
                    review_surface=review_surface,
                    surface=context.v11_lean_review_surface,
                    declaration_index={},
                ),
            )
            findings = audit.check_source_record_audit(
                "Fixture",
                folder,
                review_surface,
                "formalized",
                True,
                paper_closeout=True,
                run_context=context,  # type: ignore[arg-type]
            )

        messages = [finding.message for finding in findings]
        self.assertTrue(any("claim-atom manifest" in message for message in messages))
        self.assertTrue(any("unconfigured Assumptions.lean" in message for message in messages))


if __name__ == "__main__":
    unittest.main()
