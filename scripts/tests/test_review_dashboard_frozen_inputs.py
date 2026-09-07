from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import configured_paper_inputs, dashboard_audit_inputs, review_dashboard


class ReviewDashboardFrozenInputTests(unittest.TestCase):
    def test_dashboard_reexports_the_authoritative_input_transaction(self) -> None:
        self.assertIs(
            review_dashboard.DashboardAuditInputs,
            dashboard_audit_inputs.DashboardAuditInputs,
        )
        self.assertIs(
            review_dashboard.DashboardFrozenInputError,
            dashboard_audit_inputs.DashboardFrozenInputError,
        )
        self.assertIs(
            review_dashboard.dashboard_audit_input_scope,
            dashboard_audit_inputs.dashboard_audit_input_scope,
        )

    def _json_bytes(self, payload: object) -> bytes:
        return json.dumps(payload, sort_keys=True).encode("utf-8")

    def _empty_sidecar(self, paper: str) -> bytes:
        return self._json_bytes({"schema": 1, "paper": paper, "items": {}})

    def test_strict_review_uses_frozen_interface_after_live_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "FrozenPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            interface.write_text("theorem initial_live : True := by trivial\n")

            status = {
                "status": "formalized",
                "review_surface": {"include_names": ["snapshot_row"]},
            }
            snapshots = {
                folder / "status.json": self._json_bytes(status),
                interface: b"theorem snapshot_row : True := by trivial\n",
                folder / "FINAL_VALIDATION_REPORT.md": None,
                audit / "paper_statement_map.json": self._json_bytes(
                    {
                        "items": {
                            "snapshot_row": {
                                "statement": "Frozen paper statement.",
                            }
                        }
                    }
                ),
                audit / "lean_to_tex_llm.json": self._empty_sidecar(folder.name),
                audit / "statement_match_llm.json": self._empty_sidecar(folder.name),
                audit / "assumption_match_llm.json": self._empty_sidecar(folder.name),
            }
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root, snapshots
            )

            interface.write_text("theorem replacement_live : False := by simp\n")
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {"include_names": ["replacement_live"]},
                    }
                )
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "replacement_live": {
                                "statement": "Live replacement statement."
                            }
                        }
                    }
                )
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## Results\n- `snapshot_row`: Live report statement.\n"
            )

            provider = mock.Mock()
            with (
                mock.patch.object(
                    review_dashboard,
                    "repository_build_input_snapshot",
                    return_value="frozen-build-input",
                ),
                mock.patch.object(
                    review_dashboard,
                    "current_review_signature_contexts",
                    return_value={"PaperInterface.lean": {"sha256": "c" * 64}},
                ),
                mock.patch.object(
                    review_dashboard, "prime_review_signature_manifest_store"
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    return_value=("FrozenPaper.PaperInterface",),
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    return_value={
                        "snapshot_row": {
                            "schema": 1,
                            "declaration": "snapshot_row",
                            "sha256": "a" * 64,
                        }
                    },
                ),
                mock.patch.object(
                    review_dashboard,
                    "_cache_source_hashes",
                ) as cache_source_hashes,
            ):
                rows = review_dashboard.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    require_current_signatures=True,
                    persist_cache_rebind=False,
                    build_input_provider=provider,
                    audit_inputs=inputs,
                )

            cache_source_hashes.assert_not_called()
            self.assertEqual([row.name for row in rows], ["snapshot_row"])
            self.assertIn("snapshot_row", rows[0].interface_source)
            self.assertNotIn("replacement_live", rows[0].interface_source)
            self.assertEqual(rows[0].paper_statement, "Frozen paper statement.")

    def test_manifest_binding_uses_frozen_source_after_aba_replacement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "FrozenBinding"
            folder.mkdir(parents=True)
            interface = folder / "PaperInterface.lean"
            frozen_source = (
                "namespace FrozenBinding\n"
                "theorem reviewed : True := by trivial\n"
                "end FrozenBinding\n"
            ).encode()
            interface.write_text(
                "namespace FrozenBinding\n"
                "theorem reviewed : False := by simp\n"
                "end FrozenBinding\n",
                encoding="utf-8",
            )
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root,
                {
                    interface: frozen_source,
                    folder / "Assumptions.lean": None,
                    folder / "status.json": self._json_bytes(
                        {"status": "formalized", "review_surface": {}}
                    ),
                },
            )
            graph_sha256 = (
                review_dashboard.configured_review_row_proposition_graph_sha256(
                    {
                        "elaborated_proposition_graph": {
                            "schema": 1,
                            "nodes": [],
                        }
                    }
                )
            )
            row = {
                "qualified_declaration": "FrozenBinding.reviewed",
                "source_file": "papers/FrozenBinding/PaperInterface.lean",
                "source_sha256": hashlib.sha256(frozen_source).hexdigest(),
                "elaborated_signature_sha256": "a" * 64,
                "semantic_dependency_sha256": "b" * 64,
                "elaborated_proposition_graph_sha256": graph_sha256,
            }
            with (
                mock.patch.object(review_dashboard, "ROOT", root),
                review_dashboard.dashboard_audit_input_scope(inputs),
            ):
                bindings = (
                    review_dashboard.current_review_signature_manifest_bindings(
                        folder, [row]
                    )
                )

        authority = bindings["FrozenBinding.reviewed"]["authority_binding"]
        self.assertIn("True", authority["lean_source_declaration"])
        self.assertNotIn("False", authority["lean_source_declaration"])

    def test_missing_required_frozen_status_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "MissingPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text("theorem live_only : True := by trivial\n")
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root,
                {interface: b"theorem frozen_only : True := by trivial\n"},
            )

            with self.assertRaisesRegex(
                review_dashboard.DashboardFrozenInputError,
                r"missing frozen dashboard input: MissingPaper/status\.json",
            ):
                review_dashboard.review_items_for_paper(
                    folder,
                    use_cache=False,
                    render_images=False,
                    audit_inputs=inputs,
                )

    def test_statement_loader_uses_exact_frozen_sidecar_payload(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "JudgmentPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            sidecar = audit / "statement_match_llm.json"
            frozen_payload = {
                "schema": 1,
                "paper": folder.name,
                "items": {"frozen": {"judgment": "uncertain"}},
            }
            sidecar.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "items": {"live": {"judgment": "matches"}},
                    }
                )
            )
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root,
                {
                    sidecar: self._json_bytes(frozen_payload),
                    folder / "status.json": self._json_bytes(
                        {"status": "formalized", "review_surface": {}}
                    ),
                },
            )

            judgments = review_dashboard.load_llm_statement_judgments(
                folder, audit_inputs=inputs
            )

            self.assertEqual(set(judgments), {"frozen"})

    def test_file_snapshot_mapping_is_read_only(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            path = root / "status.json"
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root, {path: b"{}"}
            )

            with self.assertRaises(TypeError):
                inputs.file_snapshots["status.json"] = b"changed"  # type: ignore[index]

    def test_json_payload_is_parsed_once_shared_and_recursively_immutable(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            path = root / "large.json"
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root,
                {
                    path: self._json_bytes(
                        {"nested": {"value": 1}, "items": [{"name": "row"}]}
                    )
                },
            )
            original_read_bytes = inputs.read_bytes
            read_bytes = mock.Mock(wraps=original_read_bytes)
            object.__setattr__(inputs, "read_bytes", read_bytes)

            with mock.patch.object(
                review_dashboard.json,
                "loads",
                wraps=json.loads,
            ) as loads:
                first = inputs.json_payload(path)
                second = inputs.json_payload(path)

            self.assertIs(first, second)
            self.assertIsInstance(first, dict)
            self.assertIsInstance(first["items"], list)
            self.assertEqual(loads.call_count, 1)
            self.assertEqual(read_bytes.call_count, 1)
            with self.assertRaisesRegex(TypeError, "cannot be mutated"):
                first["added"] = True
            with self.assertRaisesRegex(TypeError, "cannot be mutated"):
                first["nested"]["value"] = 2
            with self.assertRaisesRegex(TypeError, "cannot be mutated"):
                first["items"].append({"name": "later"})

    def test_explicit_sidecar_absence_does_not_fall_back_to_live_trace(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "AbsentSidecarPaper"
            trace = folder / ".review_traces" / "statement_match_llm.json"
            trace.parent.mkdir(parents=True)
            trace.write_text(
                json.dumps(
                    {
                        "schema": 1,
                        "paper": folder.name,
                        "items": {"live_trace": {"judgment": "matches"}},
                    }
                )
            )
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root,
                {
                    folder / "audit" / "statement_match_llm.json": None,
                    folder / "statement_match_llm.json": None,
                },
            )

            judgments = review_dashboard.load_llm_statement_judgments(
                folder, audit_inputs=inputs
            )

            self.assertEqual(judgments, {})

    def test_required_input_collector_is_bounded_and_payload_driven(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "review_entrypoint": "papers/CollectorPaper/reports/final.md",
            "review_surface": {
                "source_file": "papers/CollectorPaper/PaperInterface.lean",
                "assumption_source_file": "AssumptionsExtra.lean",
                "llm_statement_review": {
                    "match_judgment_file": (
                        "papers/CollectorPaper/review/current_statement.json"
                    )
                },
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/proof_ledger.json"
                },
            },
        }
        statement_map = {
            "source_artifact_path": "sources/canonical.txt",
            "source_text_companion": {
                "canonical_text": {"path": "sources/canonical.txt"},
                "visual_primary_scan": {"path": "sources/visual.pdf"},
                "transcript_input_scan": {"path": "sources/input.pdf"},
            },
            "items": {
                "theorem": {
                    "source_text_file": "sources/excerpt.txt",
                    "source_anchor_evidence": [
                        {"path": "sources/canonical.txt"}
                    ],
                }
            },
        }

        with (
            mock.patch.object(Path, "read_bytes", side_effect=AssertionError("read")),
            mock.patch.object(Path, "read_text", side_effect=AssertionError("read")),
            mock.patch.object(Path, "exists", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "is_file", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "glob", side_effect=AssertionError("walk")),
            mock.patch.object(Path, "rglob", side_effect=AssertionError("walk")),
        ):
            paths = set(
                review_dashboard.required_dashboard_audit_input_paths(
                    folder,
                    status_bytes=self._json_bytes(status),
                    statement_map_bytes=self._json_bytes(statement_map),
                    repository_root=root,
                )
            )

        expected = {
            folder / "status.json",
            folder / "PaperInterface.lean",
            folder / "Assumptions.lean",
            folder / "AssumptionsExtra.lean",
            folder / "FINAL_VALIDATION_REPORT.md",
            folder / "audit/intake_freeze.json",
            folder / "reports/final.md",
            folder / "audit/statement_match_llm.json",
            folder / "statement_match_llm.json",
            folder / "review/current_statement.json",
            folder / "audit/proof_ledger.json",
            folder / "sources/canonical.txt",
            folder / "sources/visual.pdf",
            folder / "sources/input.pdf",
            folder / "sources/excerpt.txt",
            folder / "CollectorPaper.tex",
            folder / "source.txt",
            folder / "CollectorPaper.pdf",
        }
        self.assertTrue(expected <= paths)
        self.assertLess(len(paths), 50)

    def test_configured_input_collector_has_no_conventional_fallbacks(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "review_surface": {
                "source_file": "papers/CollectorPaper/PaperInterface.lean",
                "assumption_source_file": "AssumptionsExtra.lean",
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/proof_ledger.json"
                },
            }
        }
        statement_map = {
            "source_artifact_path": "sources/canonical.txt",
            "items": {
                "theorem": {
                    "source_anchor_evidence": [
                        {"path": "sources/canonical.txt"}
                    ]
                }
            },
        }

        with (
            mock.patch.object(Path, "read_bytes", side_effect=AssertionError("read")),
            mock.patch.object(Path, "read_text", side_effect=AssertionError("read")),
            mock.patch.object(Path, "exists", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "is_file", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "glob", side_effect=AssertionError("walk")),
            mock.patch.object(Path, "rglob", side_effect=AssertionError("walk")),
        ):
            paths = set(
                review_dashboard.configured_dashboard_audit_input_paths(
                    folder,
                    status_bytes=self._json_bytes(status),
                    statement_map_bytes=self._json_bytes(statement_map),
                    repository_root=root,
                )
            )

        self.assertEqual(
            paths,
            {
                folder / "PaperInterface.lean",
                folder / "AssumptionsExtra.lean",
                folder / "audit/proof_ledger.json",
                folder / "sources/canonical.txt",
            },
        )
        self.assertNotIn(folder / "paper.tex", paths)
        self.assertNotIn(folder / "source.txt", paths)
        self.assertNotIn(folder / "audit/intake_freeze.json", paths)

    def test_v11_evidence_collector_excludes_presentation_paths(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "review_entrypoint": (
                "papers/CollectorPaper/FINAL_VALIDATION_REPORT.md"
            ),
            "intake_freeze_required": True,
            "review_surface": {
                "source_file": "papers/CollectorPaper/PaperInterface.lean",
                "assumption_source_file": "Assumptions.lean",
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/source_proof_fidelity.json"
                },
            },
        }
        statement_map = {
            "source_artifact_path": "sources/canonical.txt",
            "items": {},
        }

        paths = set(
            configured_paper_inputs.configured_v11_evidence_input_paths(
                folder,
                status_bytes=self._json_bytes(status),
                statement_map_bytes=self._json_bytes(statement_map),
                repository_root=root,
            )
        )

        self.assertEqual(
            paths,
            {
                folder / "PaperInterface.lean",
                folder / "Assumptions.lean",
                folder / "audit/source_proof_fidelity.json",
                folder / "audit/intake_freeze.json",
                folder / "sources/canonical.txt",
            },
        )
        self.assertNotIn(folder / "FINAL_VALIDATION_REPORT.md", paths)

    def test_v11_evidence_collector_binds_reviewed_source_inventory_plan(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "source_inventory_review_required": True,
            "review_surface": {
                "source_file": "papers/CollectorPaper/PaperInterface.lean",
            },
        }
        statement_map = {
            "source_artifact_path": "sources/canonical.txt",
            "items": {},
        }

        paths = set(
            configured_paper_inputs.configured_v11_evidence_input_paths(
                folder,
                status_bytes=self._json_bytes(status),
                statement_map_bytes=self._json_bytes(statement_map),
                repository_root=root,
            )
        )

        self.assertIn(
            folder / "audit/v11_source_map_preparation_config.json", paths
        )
        self.assertNotIn(folder / "audit/intake_freeze.json", paths)

    def test_current_v11_transaction_paths_are_complete_and_payload_only(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "intake_freeze_required": True,
            "source_inventory_review_required": True,
            "review_surface": {
                "assumption_names": [],
                "source_file": "source/paper.tex",
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/source_proof_fidelity.json"
                },
            },
        }
        statement_map = {
            "source_artifact_path": "source/paper.tex",
            "items": {
                "corrected": {
                    "corrected_target": {
                        "approval": {"artifact_path": "docs/approval.md"}
                    }
                }
            },
        }

        with (
            mock.patch.object(Path, "read_bytes", side_effect=AssertionError("read")),
            mock.patch.object(Path, "read_text", side_effect=AssertionError("read")),
            mock.patch.object(Path, "exists", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "is_file", side_effect=AssertionError("probe")),
            mock.patch.object(Path, "glob", side_effect=AssertionError("walk")),
            mock.patch.object(Path, "rglob", side_effect=AssertionError("walk")),
        ):
            paths = set(
                configured_paper_inputs.current_v11_transaction_input_paths(
                    folder,
                    status_bytes=self._json_bytes(status),
                    statement_map_bytes=self._json_bytes(statement_map),
                    repository_root=root,
                )
            )

        self.assertEqual(
            paths,
            {
                root / "papers/audit_config.json",
                root / "lakefile.toml",
                root / "scripts/refresh_validation_report_audit_summaries.py",
                folder / "status.json",
                folder / "Assumptions.lean",
                folder / "source/paper.tex",
                folder / "docs/approval.md",
                folder / "audit/intake_freeze.json",
                folder / "audit/v11_source_map_preparation_config.json",
                folder / "audit/paper_statement_map.json",
                folder / "audit/LEAN_IMPORT_CLOSURE_RECEIPT.json",
                folder / "audit/v11_raw_source_spec_screening.json",
                folder / "audit/paper_semantic_prerequisites.json",
                folder / "audit/library_semantic_review.json",
                folder / "audit/source_proof_fidelity.json",
            },
        )
        self.assertNotIn(folder / "audit/assumption_match_llm.json", paths)

        status["review_surface"]["assumption_names"] = ["Fixture.Assumption"]
        with_assumption = set(
            configured_paper_inputs.current_v11_transaction_input_paths(
                folder,
                status_bytes=self._json_bytes(status),
                statement_map_bytes=self._json_bytes(statement_map),
                repository_root=root,
            )
        )
        self.assertIn(folder / "audit/assumption_match_llm.json", with_assumption)

    def test_current_v11_transaction_freezes_proof_fidelity_canonical_artifact(self) -> None:
        """The frozen ledger's own source pin must be available to its validator."""

        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "review_surface": {
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/source_proof_fidelity.json"
                }
            },
        }
        statement_map = {"items": {}}
        proof_fidelity = {
            "source_artifact_path": "source.tar.gz",
            "source_artifact_sha256": "a" * 64,
            "reviewed_proof_scopes": [
                {
                    "source_locator": "source/chapter.tex:1-2",
                }
            ],
        }

        paths = set(
            configured_paper_inputs.current_v11_transaction_input_paths(
                folder,
                status_bytes=self._json_bytes(status),
                statement_map_bytes=self._json_bytes(statement_map),
                source_proof_fidelity_bytes=self._json_bytes(proof_fidelity),
                repository_root=root,
            )
        )

        self.assertIn(folder / "source.tar.gz", paths)
        self.assertIn(folder / "source/chapter.tex", paths)

    def test_proof_fidelity_path_uses_the_same_frozen_status_rule(self) -> None:
        root = Path("/bounded/repository")
        folder = root / "papers" / "CollectorPaper"
        status = {
            "review_surface": {
                "source_proof_fidelity_review": {
                    "ledger_file": "audit/source_proof_fidelity.json"
                }
            }
        }
        path, error = (
            configured_paper_inputs.configured_source_proof_fidelity_ledger_path(
                folder,
                status,
                repository_root=root,
            )
        )
        self.assertEqual(path, folder / "audit/source_proof_fidelity.json")
        self.assertEqual(error, "")

        escaped, escaped_error = (
            configured_paper_inputs.configured_source_proof_fidelity_ledger_path(
                folder,
                {
                    "review_surface": {
                        "source_proof_fidelity_review": {
                            "ledger_file": "../foreign.json"
                        }
                    }
                },
                repository_root=root,
            )
        )
        self.assertIsNone(escaped)
        self.assertIn("escapes the paper folder", escaped_error)

    def test_shared_source_validators_receive_the_frozen_byte_mapping(self) -> None:
        from scripts import audit_evidence_integrity

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "ValidatorPaper"
            audit = folder / "audit"
            source = folder / "source.txt"
            ledger = audit / "source_proof_fidelity.json"
            map_path = audit / "paper_statement_map.json"
            status_path = folder / "status.json"
            source_bytes = b"Theorem 1. Frozen source.\n"
            status = {
                "status": "formalized",
                "review_surface": {
                    "source_proof_fidelity_review": {
                        "ledger_file": "audit/source_proof_fidelity.json"
                    }
                },
            }
            statement_map = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": "a" * 64,
                "items": {},
            }
            snapshots = {
                status_path: self._json_bytes(status),
                map_path: self._json_bytes(statement_map),
                source: source_bytes,
                ledger: self._json_bytes(
                    {"review_status": "defects_recorded", "defects": []}
                ),
            }
            inputs = review_dashboard.DashboardAuditInputs.from_file_snapshots(
                root, snapshots
            )

            with (
                review_dashboard.dashboard_audit_input_scope(inputs),
                mock.patch.dict(
                    sys.modules,
                    {"audit_evidence_integrity": audit_evidence_integrity},
                ),
                mock.patch.object(
                    review_dashboard,
                    "source_text_companion_validation_issues",
                    return_value=[],
                ) as companion,
                mock.patch.object(
                    review_dashboard,
                    "source_index_byte_pinned_anchor_item_ids",
                    return_value=set(),
                ) as source_index,
                mock.patch.object(
                    audit_evidence_integrity,
                    "source_anchor_evidence_findings",
                    return_value=[],
                ) as anchors,
                mock.patch.object(
                    audit_evidence_integrity,
                    "source_named_result_inventory_findings",
                    return_value=[],
                ) as named_results,
                mock.patch.object(
                    audit_evidence_integrity,
                    "source_proof_fidelity_config",
                    return_value={"ledger_file": "audit/source_proof_fidelity.json"},
                ),
                mock.patch.object(
                    audit_evidence_integrity,
                    "source_proof_fidelity_ledger_path",
                    return_value=(ledger, ""),
                ),
                mock.patch.object(
                    audit_evidence_integrity,
                    "source_proof_fidelity_findings",
                    return_value=[],
                ) as proof_fidelity,
            ):
                review_dashboard.paper_source_map_structural_errors(folder)
                review_dashboard.paper_coverage_inventory(folder)
                review_dashboard._scoped_source_anchor_evidence_errors(folder)
                review_dashboard._source_named_result_inventory_errors(folder)
                review_dashboard._validated_source_proof_defects(folder)

            for validator in (
                companion,
                source_index,
                anchors,
                named_results,
                proof_fidelity,
            ):
                override = validator.call_args.kwargs["file_bytes_override"]
                self.assertEqual(override[source], source_bytes)
                with self.assertRaises(TypeError):
                    override[source] = b"replacement"


if __name__ == "__main__":
    unittest.main()
