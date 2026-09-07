#!/usr/bin/env python3
"""Dependency-isolation regressions for current closeout authorities."""

from __future__ import annotations

import json
import subprocess
import sys
import unittest
from pathlib import Path

from scripts.python_import_closure import repository_python_import_closure

ROOT = Path(__file__).resolve().parents[2]
PLANNER_ENTRYPOINT = ROOT / "scripts" / "closeout_reuse_plan.py"
PRIMARY_GATE_ENTRYPOINT = ROOT / "scripts" / "current_closeout" / "primary_gate.py"
PRIMARY_GATE_TRANSACTION_ENTRYPOINT = (
    ROOT / "scripts" / "current_closeout" / "primary_gate_transaction.py"
)
SOURCE_ROUTE_GATE_ENTRYPOINT = (
    ROOT / "scripts" / "current_closeout" / "source_route_gate.py"
)
EVIDENCE_ACCEPTANCE_ENTRYPOINT = (
    ROOT / "scripts" / "current_closeout" / "evidence_acceptance.py"
)
EVIDENCE_GATE_ENTRYPOINT = ROOT / "scripts" / "current_closeout" / "evidence_gate.py"
SOURCE_MANIFEST_ENTRYPOINT = ROOT / "scripts" / "source_manifest_validation.py"
FORBIDDEN_CURRENT_PLANNER_MODULES = frozenset(
    {
        "scripts/audit_conclusion_provenance.py",
        "scripts/audit_evidence_integrity.py",
        "scripts/audit_repository.py",
        "scripts/review_dashboard.py",
        "scripts/review_dashboard_packet.py",
        "scripts/theorem_realization_transition.py",
    }
)
FORBIDDEN_CURRENT_PRIMARY_GATE_MODULES = FORBIDDEN_CURRENT_PLANNER_MODULES | {
    "scripts/lean_signature_manifest.py",
    "scripts/review_surface_structure.py",
}


class CurrentCloseoutDependencyBoundaryTests(unittest.TestCase):
    def test_packet_renderer_uses_only_pure_presentation_and_identity_owners(self) -> None:
        entrypoints = [ROOT / "scripts" / name for name in (
            "human_review_packet_renderer.py", "public_release_projection.py",
            "report_context_presentation.py",
        )]
        closure = repository_python_import_closure(ROOT, entrypoints)
        # The public projection verifies correction digests before withholding
        # private approval text. This pure identity helper imports no issuer,
        # evidence gate, source reader, or Lean producer.
        self.assertEqual(
            set(closure),
            set(entrypoints) | {ROOT / "scripts" / "corrected_target_identity.py"},
        )

    def test_source_manifest_owner_excludes_legacy_and_presentation(
        self,
    ) -> None:
        closure = repository_python_import_closure(ROOT, [SOURCE_MANIFEST_ENTRYPOINT])
        relative = {path.relative_to(ROOT).as_posix() for path in closure}
        self.assertEqual(
            relative.intersection(FORBIDDEN_CURRENT_PLANNER_MODULES),
            set(),
        )

    def test_evidence_facade_reexports_the_shared_source_manifest_validator(self) -> None:
        from scripts import audit_evidence_integrity, source_manifest_validation

        self.assertIs(
            audit_evidence_integrity.check_source_manifest,
            source_manifest_validation.check_source_manifest,
        )

    def test_static_current_planner_closure_excludes_legacy_and_presentation(
        self,
    ) -> None:
        closure = repository_python_import_closure(ROOT, [PLANNER_ENTRYPOINT])
        relative = {path.relative_to(ROOT).as_posix() for path in closure}
        self.assertEqual(
            relative.intersection(FORBIDDEN_CURRENT_PLANNER_MODULES),
            set(),
        )

    def test_fresh_current_planner_import_loads_no_forbidden_module(self) -> None:
        module_names = sorted(
            path.removesuffix(".py").replace("/", ".")
            for path in FORBIDDEN_CURRENT_PLANNER_MODULES
        )
        script = (
            "import json, sys; "
            "import scripts.current_closeout.planner; "
            f"names={module_names!r}; "
            "print(json.dumps({name: name in sys.modules for name in names}, "
            "sort_keys=True))"
        )
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        loaded = json.loads(result.stdout)
        self.assertEqual(loaded, {name: False for name in module_names})

    def test_static_current_primary_gate_excludes_legacy_and_lean_producer(
        self,
    ) -> None:
        closure = repository_python_import_closure(ROOT, [PRIMARY_GATE_ENTRYPOINT])
        relative = {path.relative_to(ROOT).as_posix() for path in closure}
        self.assertEqual(
            relative.intersection(FORBIDDEN_CURRENT_PRIMARY_GATE_MODULES),
            set(),
        )

    def test_static_primary_transaction_excludes_legacy_and_presentation(
        self,
    ) -> None:
        closure = repository_python_import_closure(
            ROOT, [PRIMARY_GATE_TRANSACTION_ENTRYPOINT]
        )
        relative = {path.relative_to(ROOT).as_posix() for path in closure}
        self.assertEqual(
            relative.intersection(FORBIDDEN_CURRENT_PLANNER_MODULES),
            set(),
        )

    def test_static_source_route_gate_excludes_legacy_and_presentation(self) -> None:
        closure = repository_python_import_closure(
            ROOT, [SOURCE_ROUTE_GATE_ENTRYPOINT]
        )
        relative = {path.relative_to(ROOT).as_posix() for path in closure}
        self.assertEqual(
            relative.intersection(FORBIDDEN_CURRENT_PRIMARY_GATE_MODULES),
            set(),
        )

    def test_fresh_current_runner_imports_no_legacy_auditor(self) -> None:
        script = (
            "import json, sys; import scripts.current_closeout.strict_runner; "
            "names=['scripts.audit_repository','scripts.audit_conclusion_provenance',"
            "'scripts.audit_evidence_integrity','scripts.closeout_pipeline']; "
            "print(json.dumps({name: name in sys.modules for name in names}, "
            "sort_keys=True))"
        )
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            json.loads(result.stdout),
            {
                "scripts.audit_repository": False,
                "scripts.audit_conclusion_provenance": False,
                "scripts.audit_evidence_integrity": False,
                "scripts.closeout_pipeline": False,
            },
        )

    def test_current_authority_import_does_not_load_historical_stage_schema(
        self,
    ) -> None:
        script = (
            "import json, sys; import scripts.strict_closeout_authority; "
            "print(json.dumps({'scripts.closeout_pipeline': "
            "'scripts.closeout_pipeline' in sys.modules}))"
        )
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        self.assertEqual(
            json.loads(result.stdout), {"scripts.closeout_pipeline": False}
        )

    def test_only_current_gate_references_evidence_capability_issuer(self) -> None:
        issuer_name = "_issue_current_v11_evidence_integrity"
        owners = {
            path.resolve()
            for path in (EVIDENCE_ACCEPTANCE_ENTRYPOINT, EVIDENCE_GATE_ENTRYPOINT)
        }
        references = {
            path.resolve()
            for path in (ROOT / "scripts").rglob("*.py")
            if "tests" not in path.parts
            and issuer_name in path.read_text(encoding="utf-8")
        }
        self.assertEqual(references, owners)


if __name__ == "__main__":
    unittest.main()
