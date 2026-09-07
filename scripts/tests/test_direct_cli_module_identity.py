#!/usr/bin/env python3
"""Fresh-interpreter checks for direct CLI capability issuers.

The audit entrypoints can be executed as files, while their source-record
transport consumers import them lazily as package or top-level modules.  Those
paths must resolve to the same module object: opaque evidence and strict
closeout capabilities intentionally depend on exact class identity.
"""

from __future__ import annotations

import os
import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


class DirectCLIModuleIdentityTests(unittest.TestCase):
    def assert_fresh_direct_entrypoint(self, entrypoint: str, assertions: str) -> None:
        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        script = f"""
import importlib.util
import sys
from pathlib import Path

root = Path({str(ROOT)!r})
path = root / "scripts" / {entrypoint!r}
sys.path.insert(0, str(root))
spec = importlib.util.spec_from_file_location("__main__", path)
assert spec is not None and spec.loader is not None
entrypoint_module = importlib.util.module_from_spec(spec)
sys.modules["__main__"] = entrypoint_module
sys.argv = [str(path), "--help"]
try:
    spec.loader.exec_module(entrypoint_module)
except SystemExit as exc:
    assert exc.code in (0, None), exc.code

{assertions}
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            0,
            msg=(
                f"direct `{entrypoint}` module identity probe failed\n"
                + result.stdout
                + result.stderr
            ),
        )

    def assert_fresh_hybrid_imports(
        self, module_name: str, consumer_assertions: str
    ) -> None:
        """Exercise both supported library-import orders in fresh interpreters."""

        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        for top_level_first in (True, False):
            script = f"""
import sys
from pathlib import Path

root = Path({str(ROOT)!r})
sys.path.insert(0, str(root))
module_name = {module_name!r}
package_name = "scripts." + module_name
if {top_level_first!r}:
    sys.path.insert(0, str(root / "scripts"))
    issuer = __import__(module_name)
    package = __import__(package_name, fromlist=[module_name])
else:
    package = __import__(package_name, fromlist=[module_name])
    sys.path.insert(0, str(root / "scripts"))
    issuer = __import__(module_name)

assert issuer is package
assert sys.modules[module_name] is issuer
assert sys.modules[package_name] is issuer
{consumer_assertions}
"""
            result = subprocess.run(
                [sys.executable, "-c", script],
                cwd=ROOT,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            order = "top-level first" if top_level_first else "package first"
            self.assertEqual(
                result.returncode,
                0,
                msg=(
                    f"{module_name} hybrid import probe ({order}) failed\n"
                    + result.stdout
                    + result.stderr
                ),
            )

    def test_direct_evidence_cli_remains_lazy_overlay_issuer(self) -> None:
        self.assert_fresh_direct_entrypoint(
            "audit_evidence_integrity.py",
            """
assert sys.modules["scripts.audit_evidence_integrity"] is entrypoint_module
assert sys.modules["audit_evidence_integrity"] is entrypoint_module
from scripts import audit_evidence_integrity as package_evidence
import audit_evidence_integrity as top_level_evidence
from scripts import source_record_authenticated_overlay_union as union
from scripts import audit_conclusion_provenance as conclusion

assert package_evidence is entrypoint_module
assert top_level_evidence is entrypoint_module
assert union._evidence_module() is entrypoint_module
assert set(union._overlay_modules()) == {
    "differential",
    "semantic_rebind",
}

folder = (conclusion.PAPERS / "Fixture").resolve()
snapshot = entrypoint_module.EvidenceJSONSnapshot(
    path=folder / "audit" / "source_record_audit.json",
    sha256="a" * 64,
    payload={"paper": "Fixture"},
    raw_bytes=b'{"paper":"Fixture"}',
)
binding = entrypoint_module._EvidenceRunContextIssuerBinding()
context = entrypoint_module.LegacyEvidenceRunContext(
    folder=folder,
    status="formalized",
    audit_config_snapshot=snapshot,
    status_snapshot=entrypoint_module.EvidenceJSONSnapshot(
        folder / "status.json", None, {}, b"{}"
    ),
    statement_map_snapshot=entrypoint_module.EvidenceJSONSnapshot(
        folder / "audit" / "paper_statement_map.json", None, {}, b"{}"
    ),
    source_proof_fidelity_snapshot=None,
    sidecar_snapshots=(),
    source_proof_fidelity_path_error="",
    legacy_state=entrypoint_module.LegacySourceRecordState(
        inputs=entrypoint_module.LegacySourceRecordInputs(
            audit_snapshot=snapshot,
            match_snapshot=entrypoint_module.EvidenceJSONSnapshot(
                folder / "audit" / "source_record_match_llm.json", None, {}, b"{}"
            ),
            audit_path_error="",
            match_path_error="",
        ),
        source_record_identity_error="",
        semantic_contract_revalidation=None,
        semantic_contract_revalidation_error="",
        corrected_scope_findings=(),
        corrected_scope_current=True,
        corrected_model_field_items={},
        administrative_projection_rebind=None,
        administrative_projection_rebind_path=None,
        administrative_projection_rebind_error="",
        configured_assumption_regularity_context=None,
        configured_assumption_regularity_context_error="",
        current_source_record_judgments={},
        auxiliary_routing_context=None,
        auxiliary_routing_context_error="",
        watched_input_digest="stable",
    ),
    _issuer_token=binding,
)
binding.context = context
transferred, transfer_error = conclusion.source_record_audit_snapshot_from_evidence_context(
    "Fixture", context
)
assert transfer_error == ""
assert transferred is not None
""",
        )

    def test_source_intake_entrypoints_use_only_canonical_package_imports(self) -> None:
        for entrypoint in (
            "closeout_intake_freeze.py",
            "prepare_v11_source_map.py",
            "source_inventory_review.py",
        ):
            self.assert_fresh_direct_entrypoint(
                entrypoint,
                """
for name in (
    "closeout_plan_receipt",
    "lean_import_closure",
    "obligation_routes",
    "source_coverage_scope",
    "source_inventory_review",
    "source_map_inventory",
    "source_named_result_index",
    "source_review_input",
):
    assert name not in sys.modules, name
assert "scripts.source_review_input" in sys.modules
""",
            )

    def test_direct_repository_cli_remains_strict_runtime_issuer(self) -> None:
        self.assert_fresh_direct_entrypoint(
            "audit_repository.py",
            """
assert sys.modules["scripts.audit_repository"] is entrypoint_module
assert sys.modules["audit_repository"] is entrypoint_module
from scripts import audit_repository as package_repository
import audit_repository as top_level_repository
from scripts import source_record_current_revalidation as revalidation
from scripts import source_record_manual_complement as manual_complement

assert package_repository is entrypoint_module
assert top_level_repository is entrypoint_module
assert revalidation.REPOSITORY is entrypoint_module
assert manual_complement._audit_repository_module() is entrypoint_module
""",
        )

    def test_evidence_library_import_orders_preserve_overlay_issuer(self) -> None:
        self.assert_fresh_hybrid_imports(
            "audit_evidence_integrity",
            """
from scripts import source_record_authenticated_overlay_union as union

assert union._evidence_module() is issuer
""",
        )

    def test_repository_library_import_orders_preserve_runtime_issuer(self) -> None:
        self.assert_fresh_hybrid_imports(
            "audit_repository",
            """
from scripts import source_record_current_revalidation as revalidation
from scripts import source_record_manual_complement as manual_complement

assert revalidation.REPOSITORY is issuer
assert manual_complement._audit_repository_module() is issuer
""",
        )

    def test_direct_planner_does_not_load_presentation_authorities(self) -> None:
        self.assert_fresh_direct_entrypoint(
            "closeout_reuse_plan.py",
            """
from scripts import reissue_library_semantic_review
from scripts import reissue_paper_semantic_prerequisites
from scripts import reissue_v11_raw_source_spec_screening

assert "scripts.review_dashboard" not in sys.modules
assert "scripts.review_dashboard_packet" not in sys.modules
assert "review_dashboard" not in sys.modules
assert "review_dashboard_packet" not in sys.modules
""",
        )

    def test_current_review_clis_use_only_canonical_support_modules(self) -> None:
        for entrypoint in (
            "generate_v11_source_contracts_patch.py",
            "generate_v11_specs_patch.py",
            "issue_defect_support_review.py",
            "issue_paper_coverage_review.py",
            "public_source_display_projection.py",
            "refresh_source_spec_correspondence.py",
            "reissue_library_semantic_review.py",
            "reissue_paper_semantic_prerequisites.py",
            "reissue_v11_raw_source_spec_screening.py",
            "review_dashboard_packet.py",
            "seed_paper_coverage.py",
            "seed_paper_statement_map_from_dashboard.py",
        ):
            with self.subTest(entrypoint=entrypoint):
                self.assert_fresh_direct_entrypoint(
                    entrypoint,
                    """
assert "review_dashboard" not in sys.modules
assert "review_dashboard_packet" not in sys.modules
assert "lean_signature_manifest" not in sys.modules
""",
                )

    def test_terminal_graph_modules_use_only_canonical_support_modules(self) -> None:
        for entrypoint in (
            "accepted_obligation_graph.py",
            "obligation_closure_credential.py",
            "final_closure_receipt.py",
        ):
            with self.subTest(entrypoint=entrypoint):
                self.assert_fresh_direct_entrypoint(
                    entrypoint,
                    """
for name in (
    "accepted_obligation_graph",
    "obligation_closure_credential",
    "obligation_evidence_graph",
    "obligation_evidence_store",
    "paper_build_command",
    "terminal_lean_semantic_revalidation",
):
    assert name not in sys.modules, name
""",
                )

    def test_current_obligation_projection_uses_canonical_support_modules(self) -> None:
        for entrypoint in (
            "obligation_evidence_projection.py",
            "terminal_lean_semantic_revalidation.py",
            "obligation_current_material.py",
            "obligation_closeout_materialization.py",
        ):
            with self.subTest(entrypoint=entrypoint):
                self.assert_fresh_direct_entrypoint(
                    entrypoint,
                    """
for name in (
    "obligation_evidence_graph",
    "obligation_evidence_projection",
    "obligation_resolution",
    "obligation_closeout_materialization",
    "obligation_closeout_migration",
    "review_dashboard",
    "review_dashboard_packet",
):
    assert name not in sys.modules, name
""",
                )

    def test_historical_migration_uses_the_canonical_shared_materializer(self) -> None:
        self.assert_fresh_direct_entrypoint(
            "obligation_closeout_migration.py",
            """
for name in (
    "obligation_closeout_materialization",
    "obligation_closeout_migration",
    "obligation_evidence_projection",
):
    assert name not in sys.modules, name
assert "scripts.obligation_closeout_materialization" in sys.modules
            """,
        )

    def test_review_queue_shares_nonrendering_source_helpers(self) -> None:
        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        script = f"""
import sys
from pathlib import Path

root = Path({str(ROOT)!r})
sys.path.insert(0, str(root / "scripts"))
sys.path.insert(0, str(root))
import audit_evidence_integrity
from scripts import reissue_v11_raw_source_spec_screening as reissue
from scripts import semantic_review_decision_queue as queue

assert queue.source_anchor_file_error is reissue.source_anchor_file_error
assert queue.source_semantic_input_bundle is reissue.source_semantic_input_bundle
assert "scripts.review_dashboard" not in sys.modules
assert "scripts.review_dashboard_packet" not in sys.modules
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            env=environment,
            capture_output=True,
            text=True,
            check=False,
        )
        self.assertEqual(
            result.returncode,
            0,
            msg=(
                "semantic review queue dashboard identity probe failed\n"
                + result.stdout
                + result.stderr
            ),
        )

    def test_distinct_supported_issuer_fails_closed(self) -> None:
        """Neither issuer may silently coexist with an earlier alias import."""

        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        for module_name in ("audit_evidence_integrity", "audit_repository"):
            script = f"""
import sys
import types
from pathlib import Path

root = Path({str(ROOT)!r})
sys.path.insert(0, str(root / "scripts"))
sys.modules["scripts.{module_name}"] = types.ModuleType(
    "scripts.{module_name}"
)
try:
    __import__({module_name!r})
except RuntimeError as exc:
    assert "cannot share an interpreter" in str(exc)
else:
    raise AssertionError("distinct supported issuer was accepted")
"""
            result = subprocess.run(
                [sys.executable, "-c", script],
                cwd=ROOT,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(
                result.returncode,
                0,
                msg=(
                    f"{module_name} distinct-issuer rejection probe failed\n"
                    + result.stdout
                    + result.stderr
                ),
            )

    def test_stale_parent_package_attribute_fails_closed(self) -> None:
        """A pre-bound ``scripts.audit_*`` attribute cannot bypass ``sys.modules``."""

        environment = dict(os.environ)
        existing = environment.get("PYTHONPATH")
        environment["PYTHONPATH"] = (
            str(ROOT) if not existing else str(ROOT) + os.pathsep + existing
        )
        for entrypoint, child_name in (
            ("audit_evidence_integrity.py", "audit_evidence_integrity"),
            ("audit_repository.py", "audit_repository"),
        ):
            script = f"""
import importlib.util
import sys
import types
from pathlib import Path

root = Path({str(ROOT)!r})
sys.path.insert(0, str(root))
import scripts
setattr(scripts, {child_name!r}, types.ModuleType("stale_{child_name}"))
path = root / "scripts" / {entrypoint!r}
spec = importlib.util.spec_from_file_location("__main__", path)
assert spec is not None and spec.loader is not None
entrypoint_module = importlib.util.module_from_spec(spec)
sys.modules["__main__"] = entrypoint_module
try:
    spec.loader.exec_module(entrypoint_module)
except RuntimeError as exc:
    assert "package attribute" in str(exc)
else:
    raise AssertionError("stale scripts package attribute was accepted")
"""
            result = subprocess.run(
                [sys.executable, "-c", script],
                cwd=ROOT,
                env=environment,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(
                result.returncode,
                0,
                msg=(
                    f"{entrypoint} stale-parent-attribute rejection probe failed\n"
                    + result.stdout
                    + result.stderr
                ),
            )


if __name__ == "__main__":
    unittest.main()
