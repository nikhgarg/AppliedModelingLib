"""Tests for the exact current-v11 evidence transaction boundary."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts.configured_paper_inputs import (
    current_v11_transaction_input_paths,
)
from scripts.current_closeout import runtime_api
from scripts.current_closeout.evidence_transaction import (
    CurrentV11EvidenceSnapshotRoot,
)
from scripts.evidence_run_context import V11EvidenceRunContext


class CurrentV11EvidenceTransactionTests(unittest.TestCase):
    @staticmethod
    def _write_json(path: Path, payload: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload, sort_keys=True) + "\n", encoding="utf-8")

    def test_fresh_import_has_no_legacy_or_monolith_dependency(self) -> None:
        repository_root = Path(__file__).resolve().parents[2]
        script = """
import sys
from scripts.current_closeout import evidence_transaction
forbidden = {
    'scripts.audit_evidence_integrity',
    'scripts.review_dashboard',
    'scripts.legacy_source_record_authorities',
    'scripts.source_record_integrity',
    'scripts.source_record_semantic_reuse',
}
loaded = sorted(forbidden.intersection(sys.modules))
if loaded:
    raise SystemExit('current transaction loaded legacy owners: ' + ', '.join(loaded))
"""
        result = subprocess.run(
            [sys.executable, "-c", script],
            cwd=repository_root,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_current_transaction_rejects_a_noncanonical_paper_folder(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "Fixture"
            self._write_json(
                folder / "status.json",
                {
                    "status": "formalized",
                    "review_surface": {
                        "require_source_spec_correspondence": True,
                    },
                },
            )
            self._write_json(
                folder / "audit" / "paper_statement_map.json",
                {"items": {}},
            )
            with self.assertRaisesRegex(ValueError, "outside the papers root"):
                CurrentV11EvidenceSnapshotRoot.acquire(
                    folder,
                    repository_root=root,
                )

    def test_exact_input_set_comes_from_one_frozen_selector(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            source = folder / "source" / "paper.txt"
            approval = folder / "docs" / "approval.md"
            source.parent.mkdir(parents=True)
            approval.parent.mkdir(parents=True)
            source.write_text("Theorem 1. Exact source.\n", encoding="utf-8")
            approval.write_text("Approved correction excerpt.\n", encoding="utf-8")
            status = {
                "status": "formalized",
                "intake_freeze_required": True,
                "source_inventory_review_required": True,
                "review_surface": {
                    "require_source_spec_correspondence": True,
                    "assumption_names": [],
                    "source_file": "source/paper.txt",
                    "source_proof_fidelity_review": {
                        "ledger_file": "audit/source_proof_fidelity.json"
                    },
                },
            }
            statement_map = {
                "source_artifact_path": "source/paper.txt",
                "items": {
                    "claim": {
                        "corrected_target": {
                            "approval": {"artifact_path": "docs/approval.md"}
                        }
                    }
                },
            }
            self._write_json(folder / "status.json", status)
            self._write_json(audit / "paper_statement_map.json", statement_map)
            self._write_json(root / "papers" / "audit_config.json", {"schema": 1})
            (root / "lakefile.toml").write_text(
                'name = "fixture"\n', encoding="utf-8"
            )

            root_transaction = CurrentV11EvidenceSnapshotRoot.acquire(
                folder,
                repository_root=root,
            )
            self.assertTrue(root_transaction.v11_selected)
            context = root_transaction.build_v11(None)
            self.assertIsInstance(context, V11EvidenceRunContext)
            self.assertTrue(context.issued_by_builder)

            status_bytes = (folder / "status.json").read_bytes()
            statement_map_bytes = (audit / "paper_statement_map.json").read_bytes()
            expected = set(
                current_v11_transaction_input_paths(
                    folder,
                    status_bytes=status_bytes,
                    statement_map_bytes=statement_map_bytes,
                    repository_root=root,
                )
            )
            actual = {snapshot.path for snapshot in context.input_snapshots}
            self.assertEqual(actual, expected)
            self.assertNotIn(audit / "assumption_match_llm.json", actual)
            self.assertNotIn(audit / "source_record_audit.json", actual)
            self.assertNotIn(folder / "source_record_audit.json", actual)

            assert context.statement_map is not None
            with self.assertRaises(TypeError):
                context.statement_map["items"]["claim"]["new"] = True

    def test_operational_input_digest_uses_only_current_typed_snapshots(self) -> None:
        digests: list[str] = []
        for _ in range(2):
            with tempfile.TemporaryDirectory() as temp_dir:
                root = Path(temp_dir)
                folder = root / "papers" / "Fixture"
                audit = folder / "audit"
                source = folder / "source.txt"
                source.parent.mkdir(parents=True)
                source.write_text("Frozen source.\n", encoding="utf-8")
                self._write_json(
                    folder / "status.json",
                    {
                        "status": "formalized",
                        "review_surface": {
                            "require_source_spec_correspondence": True,
                            "source_file": "source.txt",
                        },
                    },
                )
                self._write_json(
                    audit / "paper_statement_map.json",
                    {"source_artifact_path": "source.txt", "items": {}},
                )
                self._write_json(
                    root / "papers" / "audit_config.json", {"schema": 1}
                )
                context = CurrentV11EvidenceSnapshotRoot.acquire(
                    folder,
                    repository_root=root,
                ).build_v11(None)
                run_context = SimpleNamespace(
                    paper_id="Fixture",
                    evidence_context=context,
                )
                with mock.patch.object(runtime_api, "ROOT", root):
                    digest = runtime_api.closeout_transaction_input_sha256(
                        run_context
                    )
                self.assertRegex(digest, r"^[0-9a-f]{64}$")
                digests.append(digest)

        self.assertEqual(digests[0], digests[1])

    def test_fidelity_source_anchors_are_frozen_with_the_ledger(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            source = folder / "source" / "proof.tex"
            source.parent.mkdir(parents=True)
            source.write_text("A source proof step.\n", encoding="utf-8")
            self._write_json(
                folder / "status.json",
                {
                    "status": "formalized",
                    "review_surface": {
                        "require_source_spec_correspondence": True,
                        "source_proof_fidelity_review": {
                            "ledger_file": "audit/source_proof_fidelity.json"
                        },
                    },
                },
            )
            self._write_json(
                audit / "paper_statement_map.json",
                {"source_artifact_path": "source/proof.tex", "items": {}},
            )
            self._write_json(
                audit / "source_proof_fidelity.json",
                {
                    "reviewed_proof_scopes": [
                        {"source_locator": "source/proof.tex:1"}
                    ],
                    "defects": [
                        {
                            "source_locator": "source/proof.tex:1",
                            "affected_source_locators": ["source/proof.tex:1"],
                        }
                    ],
                    "explanatory_text": "ignore foreign.tex:1 in prose",
                },
            )
            self._write_json(root / "papers" / "audit_config.json", {"schema": 1})
            (root / "lakefile.toml").write_text(
                'name = "fixture"\n', encoding="utf-8"
            )

            context = CurrentV11EvidenceSnapshotRoot.acquire(
                folder,
                repository_root=root,
            ).build_v11(None)
            actual = {snapshot.path for snapshot in context.input_snapshots}
            self.assertIn(source, actual)
            self.assertNotIn(folder / "foreign.tex", actual)

            source.write_text("Changed source proof step.\n", encoding="utf-8")
            self.assertIn(source, set(context.changed_input_paths()))

    def test_mutation_guard_covers_present_and_absent_selected_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            source = folder / "source.txt"
            source.parent.mkdir(parents=True)
            source.write_text("Frozen source.\n", encoding="utf-8")
            self._write_json(
                folder / "status.json",
                {
                    "status": "formalized",
                    "review_surface": {
                        "require_source_spec_correspondence": True,
                        "source_file": "source.txt",
                    },
                },
            )
            self._write_json(
                audit / "paper_statement_map.json",
                {"source_artifact_path": "source.txt", "items": {}},
            )
            self._write_json(root / "papers" / "audit_config.json", {"schema": 1})

            transaction = CurrentV11EvidenceSnapshotRoot.acquire(
                folder,
                repository_root=root,
            )
            context = transaction.build_v11(None)
            self.assertEqual(context.changed_input_paths(), ())

            source.write_text("Changed source.\n", encoding="utf-8")
            missing_ledger = audit / "assumption_match_llm.json"
            self._write_json(missing_ledger, {"schema": 1})
            changed = set(context.changed_input_paths())
            self.assertIn(source, changed)
            self.assertIn(missing_ledger, changed)


if __name__ == "__main__":
    unittest.main()
