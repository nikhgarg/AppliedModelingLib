#!/usr/bin/env python3
"""Regression tests for prospective source-intake freeze validation."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import closeout_intake_freeze as intake
from scripts import review_dashboard
from scripts.current_closeout import planner


class CloseoutIntakeFreezeTests(unittest.TestCase):
    @mock.patch(
        "scripts.source_manifest_validation.check_source_manifest", return_value=[]
    )
    def test_reviewed_source_inventory_is_one_exact_intake_authority(
        self, _source_manifest: mock.Mock
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            status = {
                intake.SOURCE_INVENTORY_REVIEW_REQUIRED_FIELD: True,
                "status": "formalized",
            }
            source_map = {
                "source_named_result_inventory_review": {
                    "complete": True,
                    "candidate_presentations": [],
                    "discovered_candidate_presentation_sha256": "a" * 64,
                },
                "items": {},
            }
            config = {
                "paper": "Fixture",
                "source_named_result_inventory_review": {
                    "candidate_presentations": []
                },
            }
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            (audit / "paper_statement_map.json").write_text(
                json.dumps(source_map), encoding="utf-8"
            )
            (audit / intake.SOURCE_INVENTORY_REVIEW_CONFIG).write_text(
                json.dumps(config), encoding="utf-8"
            )

            with mock.patch(
                "scripts.prepare_v11_source_map.prepare",
                return_value=dict(source_map),
            ):
                current = intake.source_intake_readiness(
                    folder, repository_root=root
                )
            self.assertTrue(current["ready"], current["errors"])
            self.assertEqual(current["state"], "current")
            self.assertEqual(current["authority"], "reviewed_source_inventory_v1")

            (audit / intake.SOURCE_INVENTORY_REVIEW_CONFIG).write_text(
                json.dumps(
                    {
                        "paper": "Fixture",
                        "source_named_result_inventory_review": {},
                    }
                ),
                encoding="utf-8",
            )
            missing_candidate_review = intake.source_intake_readiness(
                folder, repository_root=root
            )
            self.assertFalse(missing_candidate_review["ready"])
            self.assertTrue(
                any(
                    "candidate_presentations" in error
                    for error in missing_candidate_review["errors"]
                )
            )
            (audit / intake.SOURCE_INVENTORY_REVIEW_CONFIG).write_text(
                json.dumps(config), encoding="utf-8"
            )

            with mock.patch(
                "scripts.prepare_v11_source_map.prepare",
                return_value={**source_map, "materialized_change": True},
            ):
                stale = intake.source_intake_readiness(
                    folder, repository_root=root
                )
            self.assertFalse(stale["ready"])
            self.assertTrue(
                any("exact current materialization" in error for error in stale["errors"])
            )

            status["intake_freeze_required"] = True
            (folder / "status.json").write_text(json.dumps(status), encoding="utf-8")
            ambiguous = intake.source_intake_readiness(folder, repository_root=root)
            self.assertFalse(ambiguous["ready"])
            self.assertEqual(ambiguous["state"], "ambiguous")

    def test_current_canonical_source_surface_fails_before_later_closeout_work(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            source_finding = mock.Mock(
                severity="ERROR", message="canonical named result is unanchored"
            )
            with mock.patch(
                "scripts.source_manifest_validation.check_source_manifest",
                return_value=[source_finding],
            ):
                readiness = intake.source_intake_readiness(
                    folder, repository_root=root
                )
            self.assertFalse(readiness["ready"])
            self.assertEqual(readiness["state"], "incomplete")
            self.assertTrue(
                any(
                    "canonical source-surface preflight: canonical named result is unanchored"
                    == error
                    for error in readiness["errors"]
                )
            )

    def test_declared_paper_status_requires_a_source_map_at_preflight(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps({"status": "formalized"}), encoding="utf-8"
            )
            readiness = intake.source_intake_readiness(
                folder, repository_root=root
            )
            self.assertFalse(readiness["ready"])
            self.assertTrue(
                any("paper_statement_map.json" in error for error in readiness["errors"])
            )

    def test_intake_marker_grandfathers_only_status_files_without_the_field(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            status = folder / "status.json"
            status.write_text("{}", encoding="utf-8")
            with (
                mock.patch.object(intake, "ROOT", root),
                mock.patch.object(
                    intake,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                legacy = intake.intake_freeze_readiness(folder)
            self.assertTrue(legacy["ready"])
            self.assertEqual(legacy["state"], "legacy_not_configured")

            status.write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            with mock.patch.object(intake, "ROOT", root):
                missing = intake.intake_freeze_readiness(folder)
            self.assertFalse(missing["ready"])
            self.assertEqual(missing["state"], "missing")

            status.write_text(
                json.dumps({"intake_freeze_required": False}), encoding="utf-8"
            )
            with mock.patch.object(intake, "ROOT", root):
                disabled = intake.intake_freeze_readiness(folder)
            self.assertFalse(disabled["ready"])
            self.assertTrue(
                any("exactly true" in error for error in disabled["errors"])
            )

    def test_new_scaffold_cannot_downgrade_by_deleting_its_intake_seal(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            with (
                mock.patch.object(intake, "ROOT", root),
                mock.patch.object(
                    intake,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=False,
                ),
            ):
                readiness = intake.intake_freeze_readiness(folder)
            self.assertFalse(readiness["ready"])
            self.assertEqual(readiness["state"], "prospective_marker_missing")

    def test_prospective_intake_atoms_are_bound_to_current_source_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            artifact = folder / "source.txt"
            artifact_bytes = b"prefix Theorem X. suffix"
            artifact.write_bytes(artifact_bytes)
            statement = "Theorem X."
            mapped_statement = "Theorem   X.\n"
            artifact_digest = hashlib.sha256(artifact_bytes).hexdigest()
            (folder / "status.json").write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "papers/Fixture/source.txt",
                        "source_artifact_sha256": artifact_digest,
                        "items": {
                            "opaque_map_key": {
                                "source_item": "A label that need not match",
                                "source_location": "line 1",
                                "statement": mapped_statement,
                            }
                        },
                    }
                )
            )
            start = artifact_bytes.index(statement.encode())
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "state": "sealed",
                "inventory_complete": True,
                "source_item_identity": intake.INTAKE_SOURCE_IDENTITY,
                "source_artifact_path": "papers/Fixture/source.txt",
                "source_artifact_sha256": artifact_digest,
                "items": [
                    {
                        "source_item": "Unrelated navigation label",
                        "source_location": "line 1",
                        "source_statement_sha256": hashlib.sha256(
                            statement.encode()
                        ).hexdigest(),
                        "dependency_order": 1,
                        "owner": "proof-agent",
                        "acceptance_conditions": ["prove the exact target"],
                        "source_atoms": [
                            {
                                "source_location": "line 1",
                                "quoted_text": "invented",
                                "quoted_text_sha256": hashlib.sha256(
                                    b"invented"
                                ).hexdigest(),
                                "byte_start": start,
                                "byte_end": start + len(statement),
                            }
                        ],
                    }
                ],
            }
            freeze = audit / "intake_freeze.json"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(intake, "ROOT", root):
                rejected = intake.intake_freeze_readiness(folder)
            self.assertFalse(rejected["ready"])

            payload["items"][0]["source_atoms"][0].update(
                {
                    "quoted_text": statement,
                    "quoted_text_sha256": hashlib.sha256(
                        statement.encode()
                    ).hexdigest(),
                }
            )
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(intake, "ROOT", root):
                accepted = intake.intake_freeze_readiness(folder)
            self.assertTrue(accepted["ready"], accepted["errors"])

            payload["items"][0]["acceptance_conditions"] = []
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(intake, "ROOT", root):
                empty_acceptance = intake.intake_freeze_readiness(folder)
            self.assertFalse(empty_acceptance["ready"])
            self.assertTrue(
                any(
                    "incomplete acceptance conditions" in error
                    for error in empty_acceptance["errors"]
                )
            )
            payload["items"][0]["acceptance_conditions"] = ["prove the exact target"]
            freeze.write_text(json.dumps(payload))

            source_map_path = audit / "paper_statement_map.json"
            current_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            current_map["items"]["second"] = {
                "source_item": "Theorem Y",
                "source_location": "line 2",
                "statement": "Theorem Y.",
            }
            source_map_path.write_text(json.dumps(current_map), encoding="utf-8")
            with mock.patch.object(intake, "ROOT", root):
                incomplete_inventory = intake.intake_freeze_readiness(folder)
            self.assertFalse(incomplete_inventory["ready"])
            self.assertTrue(
                any(
                    "exactly equal the current source-map inventory" in error
                    for error in incomplete_inventory["errors"]
                )
            )
            del current_map["items"]["second"]
            source_map_path.write_text(json.dumps(current_map), encoding="utf-8")

            payload["source_artifact_path"] = "papers/Fixture/not-canonical.txt"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(intake, "ROOT", root):
                wrong_artifact = intake.intake_freeze_readiness(folder)
            self.assertFalse(wrong_artifact["ready"])
            self.assertTrue(
                any(
                    "canonical source-map identity" in error
                    for error in wrong_artifact["errors"]
                )
            )

            payload["source_artifact_path"] = "papers/Fixture/source.txt"
            payload["items"][0]["source_location"] = "line 2"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(intake, "ROOT", root):
                wrong_location = intake.intake_freeze_readiness(folder)
            self.assertFalse(wrong_location["ready"])
            self.assertTrue(
                any(
                    "location and normalized statement" in error
                    for error in wrong_location["errors"]
                )
            )

    def test_pdf_intake_atoms_use_bound_normalized_text_not_pdf_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            pdf_bytes = b"%PDF-1.7 compressed bytes without the theorem"
            text_bytes = b"prefix Theorem X. suffix\n"
            pdf = folder / "source.pdf"
            text_artifact = folder / "source.txt"
            pdf.write_bytes(pdf_bytes)
            text_artifact.write_bytes(text_bytes)
            pdf_digest = hashlib.sha256(pdf_bytes).hexdigest()
            text_digest = hashlib.sha256(text_bytes).hexdigest()
            statement = "Theorem X."
            statement_digest = review_dashboard.statement_digest(statement)
            (folder / "status.json").write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "papers/Fixture/source.pdf",
                        "source_artifact_sha256": pdf_digest,
                        "items": {
                            "x": {
                                "source_location": "Theorem 1, p. 2",
                                "statement": statement,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            start = text_bytes.index(statement.encode("utf-8"))
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "state": "sealed",
                "inventory_complete": True,
                "source_item_identity": intake.INTAKE_SOURCE_IDENTITY,
                "source_artifact_path": "papers/Fixture/source.pdf",
                "source_artifact_sha256": pdf_digest,
                "source_text_artifact": {
                    "schema": 1,
                    "path": "papers/Fixture/source.txt",
                    "sha256": text_digest,
                    "normalization": "utf8-lf-v1",
                    "extraction": {
                        "schema": 1,
                        "source_artifact_path": "papers/Fixture/source.pdf",
                        "source_artifact_sha256": pdf_digest,
                        "tool": "pdftotext",
                        "options": [],
                    },
                },
                "items": [
                    {
                        "source_item": "navigation-only label",
                        "source_location": "Theorem 1, p. 2",
                        "source_statement_sha256": statement_digest,
                        "dependency_order": 1,
                        "owner": "proof-agent",
                        "acceptance_conditions": ["prove the exact target"],
                        "source_atoms": [
                            {
                                "source_location": "Theorem 1, p. 2",
                                "quoted_text": statement,
                                "quoted_text_sha256": hashlib.sha256(
                                    statement.encode("utf-8")
                                ).hexdigest(),
                                "byte_start": start,
                                "byte_end": start + len(statement.encode("utf-8")),
                            }
                        ],
                    }
                ],
            }
            freeze = audit / "intake_freeze.json"
            freeze.write_text(json.dumps(payload), encoding="utf-8")
            with mock.patch.object(intake, "ROOT", root):
                accepted = intake.intake_freeze_readiness(folder)
            self.assertTrue(accepted["ready"], accepted["errors"])

            del payload["source_text_artifact"]
            freeze.write_text(json.dumps(payload), encoding="utf-8")
            with mock.patch.object(intake, "ROOT", root):
                missing_receipt = intake.intake_freeze_readiness(folder)
            self.assertFalse(missing_receipt["ready"])
            self.assertTrue(
                any(
                    "normalized source-text" in error
                    for error in missing_receipt["errors"]
                )
            )


    def test_planner_consumes_single_source_intake_authority(self) -> None:
        self.assertIs(planner.source_intake_readiness, intake.source_intake_readiness)


if __name__ == "__main__":
    unittest.main()
