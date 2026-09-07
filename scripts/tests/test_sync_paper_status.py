#!/usr/bin/env python3
"""Regression tests for scoped aggregate dashboard auditing."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

import sync_paper_status  # noqa: E402
from source_coverage_scope import SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA  # noqa: E402


def write_json(path: Path, payload: dict[str, object]) -> None:
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def paper_status(paper_id: str) -> dict[str, object]:
    return {
        "id": paper_id,
        "title": paper_id,
        "authors": "Example Author",
        "status": "paper draft",
        "repository_visibility": "public",
        "review_entrypoint": f"papers/{paper_id}/PaperInterface.lean",
    }


def alternate_review_route_status(status: str) -> dict[str, object]:
    return {
        "id": "Fixture",
        "status": status,
        "paper_interface": {
            "path": "papers/Fixture/PaperInterface.lean",
            "audit_surface_path": "papers/Fixture/AuditInterface.lean",
        },
        "review_surface": {
            "source_file": "papers/Fixture/AuditInterface.lean",
            "human_source_file": "papers/Fixture/AuditInterface.lean",
        },
    }


def immutable_v10_protocol_stub() -> dict[str, object]:
    return {
        "audit_versions": {
            "theorem_realization": {
                "legacy_v10_transition_baseline": {
                    "authority": "immutable_material_identity_manifest"
                }
            }
        }
    }


def named_theorem_source_map(
    folder: Path,
    statement: str,
    *,
    preface: str = "",
) -> dict[str, object]:
    """Write one canonical named theorem and return its source-pinned map."""

    import source_named_result_index

    normalized_preface = preface
    if normalized_preface and not normalized_preface.endswith("\n"):
        normalized_preface += "\n"
    theorem_line = f"Theorem 1. {statement}"
    source_text = normalized_preface + theorem_line + "\n"
    source_path = folder / "source.txt"
    source_path.write_text(source_text, encoding="utf-8")
    source_sha256 = hashlib.sha256(source_path.read_bytes()).hexdigest()
    theorem_line_number = len(normalized_preface.splitlines()) + 1
    presentations = source_named_result_index.extract_named_result_presentations(
        source_text,
        source_format="text",
    )
    presentation_sha256 = source_named_result_index.named_result_presentations_sha256(
        presentations
    )

    return {
        "schema": 1,
        "paper": folder.name,
        "source_curated": True,
        "source_inventory_kind": "curated_test",
        "source_coverage_mode": "named_theoretical_statements",
        "source_artifact_path": "source.txt",
        "source_artifact_sha256": source_sha256,
        "source_anchor_evidence_required": True,
        "source_named_result_inventory_review": {
            "schema": 1,
            "complete": True,
            "validator": "fixture-reviewer",
            "validated_at": "2026-07-26",
            "method": "fixture named-result source scan",
            "source_artifact_sha256": source_sha256,
            "discovered_named_result_sha256": presentation_sha256,
            "prose_definition_presentations": [],
            "discovered_prose_definition_sha256": hashlib.sha256(b"[]").hexdigest(),
        },
        "items": {
            "source_claim": {
                "title": "Theorem 1",
                "statement": statement,
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_url": "https://example.invalid/paper",
                "source_location": (
                    f"source.txt:{theorem_line_number}-{theorem_line_number}"
                ),
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": theorem_line_number,
                        "line_end": theorem_line_number,
                        "quoted_text": theorem_line,
                        "quoted_text_sha256": sha256_text(theorem_line),
                    }
                ],
            }
        },
    }


class ScopedDashboardAuditTests(unittest.TestCase):
    def test_partial_paper_may_retain_alternate_review_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text(
                "theorem fixture : True := by trivial\n",
                encoding="utf-8",
            )
            (folder / "AuditInterface.lean").write_text(
                "theorem audited_fixture : True := by trivial\n",
                encoding="utf-8",
            )
            payload = alternate_review_route_status("partially formalized")

            with mock.patch.object(sync_paper_status, "ROOT", root):
                errors = sync_paper_status.validate_review_surface_routes(
                    [(folder, payload)]
                )
                readme_block = sync_paper_status.generated_paper_readme_block(
                    folder,
                    payload,
                    lean_line_count=2,
                )

        self.assertEqual(errors, [])
        self.assertIn(
            "- Audited review surface: [AuditInterface.lean](AuditInterface.lean)",
            readme_block,
        )

    def test_formalized_paper_rejects_same_alternate_review_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "PaperInterface.lean").write_text(
                "theorem fixture : True := by trivial\n",
                encoding="utf-8",
            )
            payload = alternate_review_route_status("formalized")

            with mock.patch.object(sync_paper_status, "ROOT", root):
                errors = sync_paper_status.validate_review_surface_routes(
                    [(folder, payload)]
                )

        self.assertEqual(len(errors), 3)
        self.assertTrue(
            any("audit_surface_path is obsolete" in error for error in errors)
        )
        self.assertTrue(
            any("review_surface.source_file must be" in error for error in errors)
        )
        self.assertTrue(
            any("review_surface.human_source_file must be" in error for error in errors)
        )

    def test_aggregate_renderer_never_renders_paper_owned_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            aggregate = root / "papers" / "status.json"
            human = root / "papers" / "human_status.json"
            docs = root / "docs" / "PAPER_STATUS.md"
            site = root / "site" / "index.html"
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(sync_paper_status, "AGGREGATE_STATUS", aggregate),
                mock.patch.object(sync_paper_status, "HUMAN_STATUS", human),
                mock.patch.object(sync_paper_status, "DOCS_PAPER_STATUS", docs),
                mock.patch.object(sync_paper_status, "SITE_INDEX", site),
                mock.patch.object(sync_paper_status, "paper_records", return_value=[]),
                mock.patch.object(
                    sync_paper_status, "validate_review_surface_routes", return_value=[]
                ),
                mock.patch.object(
                    sync_paper_status,
                    "aggregate_payload",
                    return_value={"schema": 1, "papers": []},
                ),
                mock.patch.object(
                    sync_paper_status,
                    "human_payload",
                    return_value={"schema": 1, "papers": []},
                ),
                mock.patch.object(
                    sync_paper_status, "render_paper_status_md", return_value="docs\n"
                ),
                mock.patch.object(
                    sync_paper_status, "render_site_index", return_value="site\n"
                ),
                mock.patch.object(sync_paper_status, "assert_no_root_readme_outputs"),
                mock.patch.object(sync_paper_status, "assert_required_static_site_copy"),
                mock.patch.object(
                    sync_paper_status,
                    "render_paper_readme",
                    side_effect=AssertionError("aggregate-only rendered a paper README"),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "render_legacy_readme_notes",
                    side_effect=AssertionError("aggregate-only rendered legacy notes"),
                ),
            ):
                outputs = sync_paper_status.aggregate_only_status_outputs()

        self.assertEqual(set(outputs), {aggregate, human, docs, site})

    def test_aggregate_only_check_owns_exactly_four_outputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            docs = root / "docs"
            site = root / "site"
            papers.mkdir()
            docs.mkdir()
            site.mkdir()
            paths = {
                papers / "status.json": "machine\n",
                papers / "human_status.json": "human\n",
                docs / "PAPER_STATUS.md": "docs\n",
                site / "index.html": "site\n",
            }
            for path, rendered in paths.items():
                path.write_text(rendered, encoding="utf-8")

            with (
                mock.patch.object(sys, "argv", ["sync_paper_status.py", "--aggregate-only", "--check"]),
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "aggregate_only_status_outputs",
                    return_value=paths,
                ) as renderer,
                mock.patch.object(
                    sync_paper_status,
                    "render_paper_readme",
                    side_effect=AssertionError("aggregate-only rendered a paper README"),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "render_legacy_readme_notes",
                    side_effect=AssertionError("aggregate-only rendered legacy notes"),
                ),
            ):
                self.assertEqual(sync_paper_status.main(), 0)

        renderer.assert_called_once_with()

    def test_aggregate_only_distinguishes_stale_from_invalid_inputs(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            output = root / "papers" / "status.json"
            output.parent.mkdir()
            output.write_text("old\n", encoding="utf-8")
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "aggregate_only_status_outputs",
                    return_value={output: "new\n"},
                ),
            ):
                self.assertEqual(sync_paper_status.run_aggregate_only(check=True), 1)

            with mock.patch.object(
                sync_paper_status,
                "aggregate_only_status_outputs",
                side_effect=ValueError("malformed fixture"),
            ):
                self.assertEqual(sync_paper_status.run_aggregate_only(check=True), 2)

    def test_paper_scoped_main_never_enumerates_other_papers(self) -> None:
        with (
            mock.patch.object(
                sys,
                "argv",
                [
                    "sync_paper_status.py",
                    "--paper",
                    "Fixture",
                    "--check",
                ],
            ),
            mock.patch.object(
                sync_paper_status,
                "check_one_paper_generated_status",
                return_value=[],
            ) as scoped_check,
            mock.patch.object(
                sync_paper_status,
                "paper_records",
                side_effect=AssertionError(
                    "paper-scoped status must not enumerate the inventory"
                ),
            ),
        ):
            self.assertEqual(sync_paper_status.main(), 0)

        scoped_check.assert_called_once_with("Fixture")

    def test_paper_local_outputs_validate_only_selected_public_row(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            folder = papers / "Fixture"
            folder.mkdir(parents=True)
            payload = paper_status("Fixture")
            payload["schema"] = 1
            write_json(folder / "status.json", payload)
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(sync_paper_status, "PAPERS", papers),
                mock.patch.object(
                    sync_paper_status,
                    "validate_review_surface_routes",
                    return_value=[],
                ),
                mock.patch.object(
                    sync_paper_status,
                    "validated_human_review_counts",
                    return_value={"total_rows": 0},
                ) as validate_counts,
                mock.patch.object(sync_paper_status, "lean_loc", return_value=7),
                mock.patch.object(
                    sync_paper_status,
                    "render_paper_readme",
                    return_value="selected readme\n",
                ),
                mock.patch.object(
                    sync_paper_status,
                    "render_legacy_readme_notes",
                    return_value=None,
                ),
            ):
                outputs, problems = sync_paper_status.one_paper_local_status_outputs(
                    "Fixture"
                )

        self.assertEqual(problems, [])
        self.assertEqual(outputs, {folder / "README.md": "selected readme\n"})
        validate_counts.assert_called_once_with(payload)

    def test_paper_local_mode_rejects_path_expressions(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers").mkdir()
            with mock.patch.object(sync_paper_status, "ROOT", root):
                outputs, problems = sync_paper_status.one_paper_local_status_outputs(
                    "../Outside"
                )
        self.assertEqual(outputs, {})
        self.assertEqual(problems, ["unknown paper folder: ../Outside"])

    def test_default_reuses_trusted_saved_counts_without_dashboard_cache(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "TrustedLegacyPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            payload["review_surface"] = {
                "include_names": ["navigation-only-row-name"],
                "assumption_names": [],
            }
            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 1,
                "stale_rows": 0,
                "mismatch_rows": 0,
                "uncertain_rows": 0,
            }
            write_json(folder / "status.json", payload)
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "prompt_version": "statement-match-v10-fixture",
                    "validator": "independent semantic reviewer",
                    "validator_type": "agent",
                    "validated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "navigation-only-row-name": {
                            "judgment": "matches",
                            "reason": "The complete source and Lean propositions are equivalent.",
                            "lean_signature_sha256": "1" * 64,
                            "paper_statement_sha256": "2" * 64,
                            "tex_statement_sha256": "3" * 64,
                        }
                    },
                },
            )
            write_json(
                audit / "paper_statement_map.json",
                named_theorem_source_map(
                    folder,
                    "Every trusted fixture satisfies the advertised property.",
                ),
            )
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "audit_kind": "source_to_dashboard_agent",
                    "source_grounded": True,
                    "seed_scaffold": False,
                    "prompt_version": "paper-coverage-v10-fixture",
                    "validator": "independent semantic reviewer",
                    "validator_type": "agent",
                    "validated_at": "2026-07-31T12:00:00Z",
                    "items": {
                        "source_claim": {
                            "coverage": "covered",
                            "review_rows": ["navigation-only-row-name"],
                            "support_declarations": [],
                            "reason": "The selected source proposition has a reviewed proof row.",
                            "source_evidence": "Pinned source bytes contain the proposition.",
                        }
                    },
                },
            )
            identity = "a" * 64
            reuse = mock.Mock(
                required=False,
                reason="unchanged immutable saved-status receipt",
                current_material_identity_sha256=identity,
                baseline_material_identity_sha256=identity,
                current_receipt_sha256="b" * 64,
                baseline_receipt_sha256="b" * 64,
                statement_counts={
                    "total": 1,
                    "matches": 1,
                    "mismatch": 0,
                    "formalization_boundary": 0,
                    "uncertain": 0,
                    "unknown": 0,
                    "source_condition_rows": 0,
                },
                coverage_counts={
                    "total": 1,
                    "covered": 1,
                    "corrected_target_covered": 0,
                    "conditional_boundary": 0,
                    "support_only": 0,
                    "out_of_scope": 0,
                    "scope_exclusion": 0,
                },
                coverage_source_bindings=(
                    {
                        "source_map_item_semantic_sha256": "c" * 64,
                        "source_item_semantic_sha256": "d" * 64,
                    },
                ),
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=reuse,
                ) as reuse_requirement,
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    side_effect=AssertionError(
                        "trusted reuse must not load a row cache"
                    ),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "explicit_dashboard_review_surface_items",
                    side_effect=AssertionError(
                        "trusted reuse must not build a dashboard"
                    ),
                ),
            ):
                row = sync_paper_status.human_status_rows([(folder, payload)])[0]

        self.assertEqual(row["llm_as_judge_translation"], "1/1 match")
        self.assertEqual(row["llm_as_judge_paper_coverage"], "1/1 covered")
        reuse_requirement.assert_called_once()

    def test_saved_receipt_rejects_contradictory_human_review_total(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "ContradictoryCounts"
            folder.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 1,
                "stale_rows": 0,
                "mismatch_rows": 0,
            }
            authorization = sync_paper_status.SavedSidecarReuseAuthorization(
                True,
                statement_counts={
                    "total": 2,
                    "matches": 2,
                    "mismatch": 0,
                    "formalization_boundary": 0,
                    "uncertain": 0,
                    "unknown": 0,
                    "source_condition_rows": 1,
                },
                coverage_counts={},
            )
            with (
                mock.patch.object(
                    sync_paper_status.ReviewSurfaceProvider,
                    "authorize_saved_sidecar_reuse",
                    return_value=authorization,
                ),
                mock.patch.object(
                    sync_paper_status,
                    "llm_translation_label",
                    return_value="translation",
                ),
                mock.patch.object(
                    sync_paper_status,
                    "llm_paper_coverage_label",
                    return_value="coverage",
                ),
            ):
                with self.assertRaisesRegex(
                    ValueError, "disagrees with saved semantic review total 3"
                ):
                    sync_paper_status.human_status_rows([(folder, payload)])

    def test_paper_facing_human_total_excludes_only_deep_only_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "PaperFacingSurface"
            (folder / "audit").mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["review_surface"] = {
                "include_names": ["normal_row", "deep_row", "shared_row"],
                "assumption_names": ["paper_condition"],
                "source_component_statement_routes": [
                    {"row": "normal_row", "source_item": "normal"},
                    {"row": "deep_row", "source_item": "deep"},
                    {"row": "shared_row", "source_item": "deep"},
                ],
            }
            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 3,
                "surface": "paper_facing_excluding_deep_audit_v1",
            }
            write_json(
                folder / "audit" / "paper_statement_map.json",
                {
                    "items": {
                        "normal": {
                            "lean_declarations": [
                                "PaperFacingSurface.PaperInterface.normal_row",
                                "PaperFacingSurface.PaperInterface.shared_row",
                            ]
                        },
                        "deep": {
                            "inventory_role": "deep_audit_material",
                            "lean_declarations": [
                                "PaperFacingSurface.PaperInterface.deep_row",
                                "PaperFacingSurface.PaperInterface.shared_row",
                            ],
                        },
                    }
                },
            )

            self.assertEqual(
                sync_paper_status.source_map_deep_only_review_rows(folder, payload),
                {"deep_row"},
            )
            self.assertEqual(
                sync_paper_status.paper_facing_human_review_total(folder, payload),
                3,
            )

            payload["human_review"]["include_deep_audit_rows"] = ["deep_row"]
            self.assertEqual(
                sync_paper_status.paper_facing_human_review_total(folder, payload),
                4,
            )

            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 3,
                "surface": "normal_source_presentations_v1",
            }
            source_map_path = folder / "audit" / "paper_statement_map.json"
            payload["source_inventory"] = {
                "path": source_map_path.relative_to(folder.parents[1]).as_posix(),
                "map_sha256": sha256_text(source_map_path.read_text(encoding="utf-8")),
                "normal_named_theory_items": 2,
                "normal_definition_items": 1,
                "normal_named_result_items": 1,
            }
            with mock.patch.object(sync_paper_status, "ROOT", folder.parents[1]):
                self.assertEqual(
                    sync_paper_status.paper_facing_human_review_total(folder, payload),
                    3,
                )

    def test_normal_source_inventory_accepts_only_bound_public_display_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ProjectedPublicPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source_sha256 = "a" * 64
            private_map_sha256 = "b" * 64
            source_map_path = audit / "paper_statement_map.json"
            write_json(
                source_map_path,
                {
                    "source_artifact_sha256": source_sha256,
                    "publication_source_display_projection": {
                        "schema": 1,
                        "manifest": "audit/public_source_display_projection.json",
                        "raw_source_bytes_included": False,
                    },
                },
            )
            public_map_sha256 = sha256_text(source_map_path.read_text(encoding="utf-8"))
            manifest_path = audit / "public_source_display_projection.json"
            write_json(
                manifest_path,
                {
                    "schema": 1,
                    "private_source_map_sha256": private_map_sha256,
                    "public_source_map_sha256": public_map_sha256,
                    "public_manifest_path": manifest_path.relative_to(root).as_posix(),
                    "raw_source_artifact_included": False,
                    "source_artifact_sha256": source_sha256,
                },
            )
            payload = paper_status(folder.name)
            payload["review_surface"] = {"include_names": ["claim"]}
            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 1,
                "surface": "normal_source_presentations_v1",
            }
            payload["source_inventory"] = {
                "path": source_map_path.relative_to(root).as_posix(),
                "map_sha256": private_map_sha256,
                "normal_named_theory_items": 1,
                "normal_definition_items": 0,
                "normal_named_result_items": 1,
            }
            with mock.patch.object(sync_paper_status, "ROOT", root):
                self.assertEqual(
                    sync_paper_status.paper_facing_human_review_total(folder, payload),
                    1,
                )

                projected_manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                projected_manifest["public_source_map_sha256"] = "c" * 64
                write_json(manifest_path, projected_manifest)
                with self.assertRaisesRegex(ValueError, "inventory is stale"):
                    sync_paper_status.paper_facing_human_review_total(folder, payload)

    def test_source_claim_total_excludes_nonclaims_aliases_and_deep_rows(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "SourceClaimSurface"
            (folder / "audit").mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["review_surface"] = {
                "include_names": ["claimSpec"],
                "assumption_names": ["sourceCondition"],
            }
            payload["human_review"] = {
                "reviewed_rows": 0,
                "total_rows": 2,
                "surface": "source_claims_v1",
            }
            write_json(
                folder / "audit" / "paper_statement_map.json",
                {
                    "items": {
                        "claim": {"claim_bearing": True},
                        "source_model_prerequisite": {
                            "claim_bearing": False,
                            "inventory_role": "source_premise_declaration",
                        },
                        "repeated_presentation": {
                            "claim_bearing": True,
                            "inventory_role": "source_presentation_alias",
                        },
                        "deep_claim": {
                            "claim_bearing": True,
                            "inventory_role": "deep_audit_material",
                        },
                    }
                },
            )

            self.assertEqual(
                sync_paper_status.paper_facing_human_review_total(folder, payload),
                2,
            )

    def test_default_does_not_reuse_counts_when_trusted_material_changed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ChangedLegacyPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"old-row": {"judgment": "matches"}},
                },
            )
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"old-source": {"coverage": "covered"}},
                },
            )
            reuse = mock.Mock(
                required=True,
                reason="semantic material changed",
                current_material_identity_sha256="a" * 64,
                baseline_material_identity_sha256="b" * 64,
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=reuse,
                ) as reuse_requirement,
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    side_effect=RuntimeError("no current row cache"),
                ),
            ):
                row = sync_paper_status.human_status_rows([(folder, payload)])[0]

        self.assertTrue(
            row["llm_as_judge_translation"].startswith("stale/unavailable:")
        )
        self.assertTrue(
            row["llm_as_judge_paper_coverage"].startswith("stale/unavailable:")
        )
        reuse_requirement.assert_called_once()

    def test_default_does_not_reuse_counts_when_trust_ledger_is_unavailable(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "UncreditedLegacyPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"old-row": {"judgment": "matches"}},
                },
            )
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"old-source": {"coverage": "covered"}},
                },
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    side_effect=FileNotFoundError("configured ledger is missing"),
                ) as reuse_requirement,
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    side_effect=RuntimeError("no current row cache"),
                ),
            ):
                row = sync_paper_status.human_status_rows([(folder, payload)])[0]

        self.assertTrue(
            row["llm_as_judge_translation"].startswith("stale/unavailable:")
        )
        self.assertTrue(
            row["llm_as_judge_paper_coverage"].startswith("stale/unavailable:")
        )
        reuse_requirement.assert_called_once()

    def test_reuse_authorization_rejects_malformed_identity_receipts(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "MalformedIdentityPaper"
            folder.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            malformed = mock.Mock(
                required=False,
                reason="unchanged",
                current_material_identity_sha256="not-a-digest",
                baseline_material_identity_sha256="not-a-digest",
                current_receipt_sha256="b" * 64,
                baseline_receipt_sha256="b" * 64,
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=malformed,
                ),
            ):
                authorization = sync_paper_status.saved_sidecar_reuse_authorization(
                    folder,
                    payload,
                )

        self.assertFalse(authorization.available)
        self.assertIn("equal identity receipts", authorization.problem)

    def test_reuse_authorization_rejects_malformed_saved_status_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "MalformedReuseReceiptPaper"
            folder.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            malformed = mock.Mock(
                required=False,
                reason="unchanged",
                current_material_identity_sha256="a" * 64,
                baseline_material_identity_sha256="a" * 64,
                current_receipt_sha256="not-a-digest",
                baseline_receipt_sha256="not-a-digest",
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=malformed,
                ),
            ):
                authorization = sync_paper_status.saved_sidecar_reuse_authorization(
                    folder,
                    payload,
                )

        self.assertFalse(authorization.available)
        self.assertIn("saved-status trust evaluation", authorization.problem)

    def test_reuse_authorization_exposes_copied_semantic_source_bindings(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "SemanticBindingsPaper"
            folder.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            binding = {
                "source_map_item_semantic_sha256": "c" * 64,
                "source_item_semantic_sha256": "d" * 64,
            }
            identity = "a" * 64
            reuse = mock.Mock(
                required=False,
                reason="unchanged",
                current_material_identity_sha256=identity,
                baseline_material_identity_sha256=identity,
                current_receipt_sha256="b" * 64,
                baseline_receipt_sha256="b" * 64,
                statement_counts={
                    "total": 1,
                    "matches": 1,
                    "mismatch": 0,
                    "formalization_boundary": 0,
                    "uncertain": 0,
                    "unknown": 0,
                    "source_condition_rows": 0,
                },
                coverage_counts={
                    "total": 1,
                    "covered": 1,
                    "corrected_target_covered": 0,
                    "conditional_boundary": 0,
                    "support_only": 0,
                    "out_of_scope": 0,
                    "scope_exclusion": 0,
                },
                coverage_source_bindings=(binding,),
                canonical_source_state="verified_current_bytes",
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=reuse,
                ),
            ):
                authorization = sync_paper_status.saved_sidecar_reuse_authorization(
                    folder,
                    payload,
                )
            binding["source_map_item_semantic_sha256"] = "f" * 64

        self.assertTrue(authorization.available, authorization.problem)
        self.assertIsInstance(authorization.coverage_source_bindings, tuple)
        self.assertEqual(
            authorization.coverage_source_bindings[0][
                "source_map_item_semantic_sha256"
            ],
            "c" * 64,
        )

    def test_reuse_authorization_rejects_binding_count_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "BindingCountPaper"
            folder.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            write_json(folder / "status.json", payload)
            identity = "a" * 64
            reuse = mock.Mock(
                required=False,
                reason="unchanged",
                current_material_identity_sha256=identity,
                baseline_material_identity_sha256=identity,
                current_receipt_sha256="b" * 64,
                baseline_receipt_sha256="b" * 64,
                statement_counts={},
                coverage_counts={"total": 2},
                coverage_source_bindings=(
                    {
                        "source_map_item_semantic_sha256": "c" * 64,
                        "source_item_semantic_sha256": "d" * 64,
                    },
                ),
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "load_formalization_protocol",
                    return_value=immutable_v10_protocol_stub(),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "evaluate_saved_status_reuse",
                    return_value=reuse,
                ),
            ):
                authorization = sync_paper_status.saved_sidecar_reuse_authorization(
                    folder,
                    payload,
                )

        self.assertFalse(authorization.available)
        self.assertIn("disagree with the coverage total", authorization.problem)

    def test_public_dashboard_excludes_explicit_private_only_papers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            public = root / "PublicPaper"
            private = root / "PrivatePaper"
            public.mkdir()
            private.mkdir()
            private_payload = paper_status(private.name)
            private_payload["repository_visibility"] = "private_only"

            with mock.patch.object(sync_paper_status, "ROOT", root):
                rows = sync_paper_status.human_payload(
                    [
                        (public, paper_status(public.name)),
                        (private, private_payload),
                    ]
                )["papers"]

        self.assertEqual([row["id"] for row in rows], ["PublicPaper"])

    def test_public_dashboard_rejects_unknown_repository_visibility(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UnknownVisibility"
            folder.mkdir()
            payload = paper_status(folder.name)
            payload["repository_visibility"] = "internal"

            with self.assertRaisesRegex(ValueError, "repository_visibility"):
                sync_paper_status.human_payload([(folder, payload)])

    def test_public_dashboard_fails_closed_on_missing_repository_visibility(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "MissingVisibility"
            folder.mkdir()
            payload = paper_status(folder.name)
            payload.pop("repository_visibility")

            with self.assertRaisesRegex(
                ValueError, "missing explicit repository_visibility"
            ):
                sync_paper_status.human_payload([(folder, payload)])

    def test_approved_corrected_targets_count_as_successful_coverage(self) -> None:
        self.assertEqual(
            sync_paper_status.paper_coverage_label_from_counts(
                total=21,
                covered=16,
                corrected_target_covered=5,
            ),
            "21/21 covered (16 direct; 5 approved corrected targets)",
        )

    def test_generated_readme_discloses_author_approved_corrected_scope(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "CorrectedPaper"
            docs = folder / "docs"
            audit = folder / "audit"
            docs.mkdir(parents=True)
            audit.mkdir()
            (docs / "GOVERNING.md").write_text("governing model\n", encoding="utf-8")
            (audit / "contract.json").write_text("{}\n", encoding="utf-8")
            payload = paper_status(folder.name)
            payload.update(
                {
                    "status": "formalized",
                    "formalization_scope": {
                        "kind": "author_approved_corrected_model",
                    },
                    "artifacts": {
                        "governing_corrected_model": "papers/CorrectedPaper/docs/GOVERNING.md",
                        "corrected_model_semantic_contract": "papers/CorrectedPaper/audit/contract.json",
                    },
                }
            )
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.generated_paper_readme_block(
                    folder, payload
                )

        self.assertIn("The formalized model differs from the pinned archive", rendered)
        self.assertNotIn("Author-approved", rendered)
        self.assertIn("GOVERNING.md", rendered)
        self.assertIn("contract.json", rendered)

    def test_corrected_readme_prefers_explicit_reader_clarification(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "CorrectedPaper"
            docs = folder / "docs"
            audit = folder / "audit"
            docs.mkdir(parents=True)
            audit.mkdir()
            clarification = docs / "GOVERNING_MODEL_CLARIFICATION.md"
            clarification.write_text("# Governing-model clarification\n", encoding="utf-8")
            governing = docs / "GOVERNING_CORRECTED_MODEL.md"
            governing.write_text("# Governing corrected model\n", encoding="utf-8")
            contract = audit / "contract.json"
            contract.write_text("{}\n", encoding="utf-8")
            payload = paper_status(folder.name)
            payload.update(
                {
                    "status": "formalized",
                    "formalization_scope": {
                        "kind": "author_approved_corrected_model",
                    },
                    "artifacts": {
                        "source_clarifications": (
                            "papers/CorrectedPaper/docs/"
                            "GOVERNING_MODEL_CLARIFICATION.md"
                        ),
                        "governing_corrected_model": (
                            "papers/CorrectedPaper/docs/GOVERNING_CORRECTED_MODEL.md"
                        ),
                        "corrected_model_semantic_contract": (
                            "papers/CorrectedPaper/audit/contract.json"
                        ),
                    },
                }
            )
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.generated_paper_readme_block(
                    folder, payload
                )

        self.assertIn(
            "- Source clarifications and assumptions: "
            "[GOVERNING_MODEL_CLARIFICATION.md]"
            "(docs/GOVERNING_MODEL_CLARIFICATION.md)",
            rendered,
        )
        self.assertNotIn("GOVERNING_CORRECTED_MODEL.md", rendered)
        self.assertIn("contract.json", rendered)

    def test_generated_readme_links_present_human_review_packet(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ReviewedPaper"
            docs = folder / "docs"
            docs.mkdir(parents=True)
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"%PDF-fixture\n")
            payload = paper_status(folder.name)
            payload.update(
                {
                    "status": "formalized",
                    "artifacts": {
                        "human_review_packet_pdf": (
                            "papers/ReviewedPaper/docs/HUMAN_REVIEW_PACKET.pdf"
                        )
                    },
                }
            )
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.generated_paper_readme_block(
                    folder, payload
                )

        self.assertIn(
            "Human review packet: [HUMAN_REVIEW_PACKET.pdf]"
            "(docs/HUMAN_REVIEW_PACKET.pdf)",
            rendered,
        )

    def test_readme_links_memo_and_stable_metadata_without_legacy_audit_claims(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "ReviewedPaper"
            (folder / "docs").mkdir(parents=True)
            (folder / "audit").mkdir()
            memo = folder / "docs" / "SOURCE_CLARIFICATIONS.md"
            memo.write_text("# Source clarifications\n", encoding="utf-8")
            dag = folder / "docs" / "DependencyDAG.pdf"
            dag.write_bytes(b"%PDF-fixture\n")
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "audit/paper_coverage_llm.json",
                "audit/source_record_audit.json",
                "audit/statement_match_llm.json",
            ):
                (folder / relative).write_text("{}\n", encoding="utf-8")
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.generated_paper_readme_block(
                    folder, paper_status(folder.name)
                )
                memo.unlink()
                dag.unlink()
                without_memo = sync_paper_status.generated_paper_readme_block(
                    folder, paper_status(folder.name)
                )
                (folder / "docs" / "SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md").write_text(
                    "# Source clarifications\n", encoding="utf-8"
                )
                alternate_memo = sync_paper_status.generated_paper_readme_block(
                    folder, paper_status(folder.name)
                )
                memo.write_text("# Source clarifications\n", encoding="utf-8")
                both_memos = sync_paper_status.generated_paper_readme_block(
                    folder, paper_status(folder.name)
                )
        self.assertIn("[SOURCE_CLARIFICATIONS.md](docs/SOURCE_CLARIFICATIONS.md)", rendered)
        self.assertNotIn("SOURCE_CLARIFICATIONS.md", without_memo)
        self.assertIn(
            "[SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md](docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md)",
            alternate_memo,
        )
        self.assertIn(
            "[SOURCE_CLARIFICATIONS.md](docs/SOURCE_CLARIFICATIONS.md)",
            both_memos,
        )
        self.assertIn(
            "[SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md]"
            "(docs/SOURCE_CLARIFICATIONS_AND_CORRECTIONS.md)",
            both_memos,
        )
        self.assertIn("[DependencyDAG.pdf](docs/DependencyDAG.pdf)", rendered)
        self.assertIn("Dependency DAG: not tracked in this folder.", without_memo)
        self.assertIn("[status.json](status.json)", rendered)
        self.assertIn("[paper statement map](audit/paper_statement_map.json)", rendered)
        for legacy in ("paper_coverage_llm.json", "source_record_audit.json", "statement_match_llm.json"):
            self.assertNotIn(legacy, rendered)

    def test_current_corrected_scope_uses_contract_label_not_stale_archive_sidecars(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedPaper"
            folder.mkdir()
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            payload["formalization_scope"] = {"kind": "author_approved_corrected_model"}
            with mock.patch.object(
                sync_paper_status,
                "current_author_approved_corrected_scope",
                return_value=True,
            ):
                self.assertEqual(
                    sync_paper_status.llm_translation_label(folder, payload),
                    "formalized target differs from the pinned archive; semantic contract current",
                )
                self.assertEqual(
                    sync_paper_status.llm_paper_coverage_label(folder, payload),
                    "formalized target differs from the pinned archive; semantic contract current",
                )

    def test_status_row_evaluates_corrected_scope_only_once(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "CorrectedPaper"
            folder.mkdir()
            payload = paper_status(folder.name)
            payload["status"] = "formalized"
            payload["formalization_scope"] = {"kind": "author_approved_corrected_model"}
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "current_author_approved_corrected_scope",
                    return_value=True,
                ) as current_scope,
            ):
                row = sync_paper_status.human_status_rows([(folder, payload)])[0]

        self.assertEqual(
            row["llm_as_judge_translation"],
            "formalized target differs from the pinned archive; semantic contract current",
        )
        self.assertEqual(
            row["llm_as_judge_paper_coverage"],
            "formalized target differs from the pinned archive; semantic contract current",
        )
        current_scope.assert_called_once_with(folder, payload)

    def test_dashboard_audit_is_limited_to_selected_paper(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            selected = root / "SelectedPaper"
            other = root / "OtherPaper"
            selected.mkdir()
            other.mkdir()
            records = [
                (selected, paper_status(selected.name)),
                (other, paper_status(other.name)),
            ]

            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "llm_translation_label",
                    return_value="translation",
                ) as translation,
                mock.patch.object(
                    sync_paper_status,
                    "llm_paper_coverage_label",
                    return_value="coverage",
                ) as coverage,
            ):
                sync_paper_status.human_status_rows(
                    records,
                    use_dashboard_audit=True,
                    dashboard_audit_paper=selected.name,
                )

        self.assertEqual(
            [call.kwargs["use_dashboard_audit"] for call in translation.call_args_list],
            [True, False],
        )
        self.assertEqual(
            [call.kwargs["use_dashboard_audit"] for call in coverage.call_args_list],
            [True, False],
        )

    def test_unscoped_dashboard_audit_still_audits_every_paper(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folders = [root / "FirstPaper", root / "SecondPaper"]
            for folder in folders:
                folder.mkdir()
            records = [(folder, paper_status(folder.name)) for folder in folders]

            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "llm_translation_label",
                    return_value="translation",
                ) as translation,
                mock.patch.object(
                    sync_paper_status,
                    "llm_paper_coverage_label",
                    return_value="coverage",
                ),
            ):
                sync_paper_status.human_status_rows(
                    records,
                    use_dashboard_audit=True,
                )

        self.assertEqual(
            [call.kwargs["use_dashboard_audit"] for call in translation.call_args_list],
            [True, True],
        )

    def test_precomputed_lean_loc_is_shared_by_status_and_readme_rendering(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "Paper"
            folder.mkdir()
            payload = paper_status(folder.name)
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "lean_loc",
                    side_effect=AssertionError("Lean LOC was recomputed"),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "llm_translation_label",
                    return_value="translation",
                ),
                mock.patch.object(
                    sync_paper_status,
                    "llm_paper_coverage_label",
                    return_value="coverage",
                ),
            ):
                rows = sync_paper_status.human_status_rows(
                    [(folder, payload)],
                    lean_loc_by_folder={folder: 123},
                )
                readme = sync_paper_status.render_paper_readme(
                    folder,
                    payload,
                    lean_line_count=123,
                )

        self.assertEqual(rows[0]["lean_loc"], 123)
        self.assertIn("| Lines of Code | 123 |", readme)

    def test_template_readme_links_the_public_formalization_plan(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "TEMPLATE"
            (folder / "docs").mkdir(parents=True)
            (folder / "docs" / "FORMALIZATION_PLAN.md").write_text(
                "# Plan\n", encoding="utf-8"
            )
            payload = paper_status("TEMPLATE")
            with mock.patch.object(sync_paper_status, "ROOT", root):
                readme = sync_paper_status.generated_paper_readme_block(
                    folder, payload, lean_line_count=0
                )

        self.assertIn(
            "- Formalization plan: [FORMALIZATION_PLAN.md](docs/FORMALIZATION_PLAN.md)",
            readme,
        )
        self.assertNotIn("FORMALIZATION_NOTES.md", readme)

    def test_generated_output_write_skips_identical_text(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "status.json"
            path.write_text("same\n", encoding="utf-8")

            self.assertFalse(sync_paper_status.write_output_if_changed(path, "same\n"))
            self.assertTrue(
                sync_paper_status.write_output_if_changed(path, "changed\n")
            )
            self.assertEqual(path.read_text(encoding="utf-8"), "changed\n")


class AggregateSidecarFreshnessTests(unittest.TestCase):
    def test_stale_coverage_does_not_hide_current_translation(self) -> None:
        import review_dashboard

        paper_statement = "The paper statement."
        tex_statement = "The context-free Lean translation."
        row = review_dashboard.ReviewItem(
            name="canonical_row",
            kind="theorem",
            lean_statement="theorem canonical_row : True",
            paper_statement=paper_statement,
            agent_statement=tex_statement,
            lean_signature_sha256="current-lean-signature",
        )
        current_judgment = {
            "judgment": "matches",
            "prompt_version_stale": False,
            "metadata_missing": False,
            "obligation_ledger_error": "",
            "lean_signature_sha256": row.lean_signature_sha256,
            "lean_statement_sha256": review_dashboard.statement_digest(
                row.lean_statement
            ),
            "paper_statement_sha256": review_dashboard.statement_digest(
                paper_statement
            ),
            "tex_statement_sha256": review_dashboard.statement_digest(tex_statement),
        }

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "IndependentTranslationPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["human_review"] = {"total_rows": 1}
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"canonical_row": {"judgment": "matches"}},
                },
            )
            # Deliberately stale coverage evidence must not alter the separate
            # source-to-Lean statement-translation label.
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "paper_statement_inventory_sha256": "old-inventory",
                    "review_surface_sha256": "old-surface",
                    "items": {"source_claim": {"coverage": "covered"}},
                },
            )

            with (
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    return_value=(review_dashboard, [row]),
                ),
                mock.patch.object(
                    review_dashboard,
                    "load_llm_statement_judgments",
                    return_value={"canonical_row": current_judgment},
                ),
            ):
                self.assertEqual(
                    sync_paper_status.coverage_sidecar_freshness_problem(folder),
                    "paper-coverage inventory digest is stale",
                )
                label = sync_paper_status.llm_translation_label(folder, payload)

        self.assertEqual(label, "1/1 match")

    def test_stale_source_record_does_not_hide_current_coverage(self) -> None:
        import review_dashboard

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "IndependentCoveragePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            statement_map = named_theorem_source_map(
                folder,
                "A stable source claim.",
            )
            write_json(audit / "paper_statement_map.json", statement_map)
            inventory_digest = review_dashboard.paper_statement_inventory_digest(
                review_dashboard.paper_statement_inventory(folder)
            )
            source_item = review_dashboard.paper_statement_inventory(folder)[
                "source_claim"
            ]
            source_anchor_identity, source_anchor_error = (
                review_dashboard.source_anchor_quote_identity(source_item)
            )
            self.assertEqual(source_anchor_error, "")
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "audit_kind": "source_to_dashboard_llm",
                    "source_grounded": True,
                    "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                    "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                    "validator": "fixture-agent",
                    "validator_type": "agent",
                    "validated_at": "2026-07-26T12:00:00Z",
                    "source_coverage_mode": "named_theoretical_statements",
                    "source_artifact_path": statement_map["source_artifact_path"],
                    "source_artifact_sha256": statement_map["source_artifact_sha256"],
                    "paper_statement_inventory_sha256": inventory_digest,
                    "review_surface_sha256": review_dashboard.review_surface_digest([]),
                    "items": {
                        "source_claim": {
                            "coverage": "covered",
                            "reason": "The source item is covered by the reviewed proof row.",
                            "source_evidence": "source.txt:1-1 contains the source claim.",
                            "source_anchor_quote_identity_sha256": source_anchor_identity,
                        }
                    },
                },
            )
            # This would have invalidated both aggregate labels under the old
            # cross-lane source-record gate. It is intentionally irrelevant to
            # the source-inventory-to-review-surface coverage judgment.
            write_json(
                audit / "source_record_audit.json",
                {
                    "prompt_version": "source-record-current",
                    "source_record_audit_sha256": "current-audit-digest",
                    "boundary_input_items": [
                        {
                            "judgment_key": "semantic-boundary-input",
                            "source_record_item_sha256": "current-item-digest",
                        }
                    ],
                },
            )
            write_json(
                audit / "source_record_match_llm.json",
                {
                    "prompt_version": "source-record-old",
                    "source_record_audit_sha256": "old-audit-digest",
                    "items": {},
                },
            )

            with (
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    return_value=(review_dashboard, []),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    return_value=[],
                ),
            ):
                label = sync_paper_status.llm_paper_coverage_label(folder, payload)

        self.assertEqual(label, "1/1 covered")

    def test_orphan_source_record_match_sidecar_does_not_hide_other_lane_labels(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "OrphanSourceRecordPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            write_json(
                audit / "source_record_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {
                        "semantic-boundary-input": {
                            "classification": "validated_source_assumption",
                        }
                    },
                },
            )

            self.assertEqual(
                sync_paper_status.llm_translation_label(folder, payload),
                "not run",
            )
            self.assertEqual(
                sync_paper_status.llm_paper_coverage_label(folder, payload),
                "stale/unavailable: paper-coverage inventory or review surface is unavailable",
            )

    def test_trace_only_statement_match_sidecar_uses_canonical_freshness_gate(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "TraceOnlyStatementPaper"
            traces = folder / ".review_traces"
            traces.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["human_review"] = {"total_rows": 1}
            write_json(
                traces / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"canonical_row": {"judgment": "matches"}},
                },
            )

            with mock.patch.object(
                sync_paper_status,
                "canonical_statement_translation_summary",
                return_value={"stale_judgment_count": 1},
            ) as canonical_summary:
                label = sync_paper_status.llm_translation_label(folder, payload)

        self.assertEqual(
            label,
            "stale/unavailable: statement-match row evidence is stale",
        )
        canonical_summary.assert_called_once_with(folder, use_dashboard_audit=False)

    def test_translation_rejects_each_stale_canonical_row_pin(self) -> None:
        import review_dashboard

        paper_statement = "The paper statement."
        tex_statement = "The context-free Lean translation."
        row = review_dashboard.ReviewItem(
            name="canonical_row",
            kind="theorem",
            lean_statement="theorem canonical_row : True",
            paper_statement=paper_statement,
            agent_statement=tex_statement,
            lean_signature_sha256="current-lean-signature",
        )
        current = {
            "judgment": "matches",
            "prompt_version_stale": False,
            "metadata_missing": False,
            "obligation_ledger_error": "",
            "lean_signature_sha256": row.lean_signature_sha256,
            "paper_statement_sha256": review_dashboard.statement_digest(
                paper_statement
            ),
            "tex_statement_sha256": review_dashboard.statement_digest(tex_statement),
        }
        stale_judgments = {
            "prompt": {**current, "prompt_version_stale": True},
            "signature": {**current, "lean_signature_sha256": "old-signature"},
            "paper": {**current, "paper_statement_sha256": "old-paper"},
            "tex": {**current, "tex_statement_sha256": "old-tex"},
        }

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "StatementFreshnessPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            # The configured name deliberately differs from the canonical row:
            # freshness comes from the row's semantic pins, not this metadata.
            payload["review_surface"] = {"include_names": ["old_status_name"]}
            payload["human_review"] = {"total_rows": 1}
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"canonical_row": {"judgment": "matches"}},
                },
            )

            for pin, judgment in stale_judgments.items():
                with self.subTest(pin=pin):
                    with (
                        mock.patch.object(
                            sync_paper_status,
                            "cached_current_review_surface_items",
                            return_value=(review_dashboard, [row]),
                        ) as current_surface,
                        mock.patch.object(
                            review_dashboard,
                            "load_llm_statement_judgments",
                            return_value={"canonical_row": judgment},
                        ),
                    ):
                        label = sync_paper_status.llm_translation_label(folder, payload)

                    self.assertEqual(
                        label,
                        "stale/unavailable: statement-match row evidence is stale",
                    )
                    self.assertEqual(current_surface.call_args.args, (folder,))

            # A stale statement-match sidecar is not a paper-coverage failure.
            self.assertEqual(
                sync_paper_status.llm_paper_coverage_label(folder, payload),
                "stale/unavailable: paper-coverage inventory or review surface is unavailable",
            )

    def test_default_freshness_reads_only_a_verified_dashboard_cache(self) -> None:
        import review_dashboard

        folder = Path("/tmp") / "NonWritingFreshnessPaper"
        with mock.patch.object(
            review_dashboard,
            "load_cached_review_rows",
            return_value=[],
        ) as load_cached:
            sync_paper_status.cached_current_review_surface_items(folder)

        load_cached.assert_called_once_with(folder, persist_rebind=False)

    def test_default_status_counts_share_cache_and_forbid_lean_paths(self) -> None:
        import review_dashboard

        translation_summary = {
            "row_count": 1,
            "matches": 1,
            "stale_judgment_count": 0,
        }
        coverage_summary = {
            "inventory_count": 1,
            "covered_count": 1,
            "source_coverage_mode_error": "",
            "source_coverage_mode_migration_error": "",
            "deep_source_coverage_attestation_error": "",
            "source_presentation_classification_error_count": 0,
            "source_named_result_inventory_error_count": 0,
            "ambiguous_semantic_item_bindings": [],
            "missing_coverage_count": 0,
            "extra_coverage_count": 0,
            "source_coverage_mode_mismatch": False,
            "stale_source_item_count": 0,
            "unverified_reused_source_item_count": 0,
            "legacy_unpinned_item_count": 0,
            "stale_statement_count": 0,
            "coverage_row_signature_error_count": 0,
            "invalid_row_link_count": 0,
        }

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "CachedStatusPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            payload["human_review"] = {"total_rows": 1}
            write_json(
                audit / "statement_match_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"semantic-row": {"judgment": "matches"}},
                },
            )
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "items": {"source-claim": {"coverage": "covered"}},
                },
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch.object(
                    sync_paper_status,
                    "current_author_approved_corrected_scope",
                    return_value=False,
                ),
                mock.patch.object(
                    review_dashboard,
                    "load_cached_review_rows",
                    return_value=[object()],
                ) as load_cached,
                mock.patch.object(
                    review_dashboard,
                    "statement_translation_audit_summary",
                    return_value=translation_summary,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_coverage_audit_summary",
                    return_value=coverage_summary,
                ),
                mock.patch.object(
                    sync_paper_status,
                    "explicit_dashboard_review_surface_items",
                    side_effect=AssertionError(
                        "default sync may not extract a dashboard"
                    ),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    side_effect=AssertionError(
                        "default sync may not rebuild review rows"
                    ),
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=AssertionError("default sync may not invoke Lean"),
                ),
            ):
                row = sync_paper_status.human_status_rows([(folder, payload)])[0]

        self.assertEqual(row["llm_as_judge_translation"], "1/1 match")
        self.assertEqual(row["llm_as_judge_paper_coverage"], "1/1 covered")
        load_cached.assert_called_once_with(
            folder,
            build_input_provider=mock.ANY,
            persist_rebind=False,
        )

    def test_explicit_dashboard_audit_uses_the_explicit_surface_path(self) -> None:
        dashboard = mock.Mock()
        dashboard.statement_translation_audit_summary.return_value = {"row_count": 0}
        folder = Path("/tmp") / "ExplicitDashboardAuditPaper"
        with (
            mock.patch.object(
                sync_paper_status,
                "explicit_dashboard_review_surface_items",
                return_value=(dashboard, []),
            ) as explicit_surface,
            mock.patch.object(
                sync_paper_status,
                "cached_current_review_surface_items",
                side_effect=AssertionError("default cache path should not run"),
            ),
        ):
            summary = sync_paper_status.canonical_statement_translation_summary(
                folder,
                use_dashboard_audit=True,
            )

        self.assertEqual(summary, {"row_count": 0})
        explicit_surface.assert_called_once_with(folder)

    def test_explicit_coverage_audit_uses_the_explicit_surface_path(self) -> None:
        dashboard = mock.Mock()
        dashboard.paper_coverage_audit_summary.return_value = {
            "source_coverage_mode_error": "",
            "source_coverage_mode_migration_error": "",
            "deep_source_coverage_attestation_error": "",
            "source_presentation_classification_error_count": 0,
            "ambiguous_semantic_item_bindings": [],
            "missing_coverage_count": 0,
            "extra_coverage_count": 0,
            "source_coverage_mode_mismatch": False,
            "stale_source_item_count": 0,
            "unverified_reused_source_item_count": 0,
            "legacy_unpinned_item_count": 0,
            "stale_statement_count": 0,
            "coverage_row_signature_error_count": 0,
            "invalid_row_link_count": 0,
        }

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ExplicitCoverageAuditPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "paper_statement_inventory_sha256": "inventory-digest",
                    "review_surface_sha256": "surface-digest",
                    "items": {"source_claim": {"coverage": "covered"}},
                },
            )
            with (
                mock.patch.object(
                    sync_paper_status,
                    "explicit_dashboard_review_surface_items",
                    return_value=(dashboard, []),
                ) as explicit_surface,
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    side_effect=AssertionError("default cache path should not run"),
                ),
            ):
                problem = sync_paper_status.coverage_sidecar_freshness_problem(
                    folder,
                    use_dashboard_audit=True,
                )

        self.assertIsNone(problem)
        explicit_surface.assert_called_once_with(folder)

    def test_coverage_requires_current_review_surface_without_hiding_translation(
        self,
    ) -> None:
        import review_dashboard

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CoverageSurfacePaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            statement_map = named_theorem_source_map(
                folder,
                "A stable source claim.",
            )
            write_json(audit / "paper_statement_map.json", statement_map)
            inventory_digest = review_dashboard.paper_statement_inventory_digest(
                review_dashboard.paper_statement_inventory(folder)
            )
            source_item = review_dashboard.paper_statement_inventory(folder)[
                "source_claim"
            ]
            source_anchor_identity, source_anchor_error = (
                review_dashboard.source_anchor_quote_identity(source_item)
            )
            self.assertEqual(source_anchor_error, "")
            coverage = {
                "schema": 1,
                "paper": folder.name,
                "audit_kind": "source_to_dashboard_llm",
                "source_grounded": True,
                "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                "validator": "fixture-agent",
                "validator_type": "agent",
                "validated_at": "2026-07-26T12:00:00Z",
                "source_coverage_mode": "named_theoretical_statements",
                "source_artifact_path": statement_map["source_artifact_path"],
                "source_artifact_sha256": statement_map["source_artifact_sha256"],
                "paper_statement_inventory_sha256": inventory_digest,
                "review_surface_sha256": "old-review-surface",
                "items": {
                    "source_claim": {
                        "coverage": "covered",
                        "reason": "The source item is covered by the reviewed proof row.",
                        "source_evidence": "source.txt:1-1 contains the source claim.",
                        "source_anchor_quote_identity_sha256": source_anchor_identity,
                    }
                },
            }
            write_json(audit / "paper_coverage_llm.json", coverage)

            with (
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    return_value=(review_dashboard, []),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    return_value=[],
                ),
            ):
                label = sync_paper_status.llm_paper_coverage_label(folder, payload)
                coverage.pop("review_surface_sha256")
                write_json(audit / "paper_coverage_llm.json", coverage)
                missing_digest_label = sync_paper_status.llm_paper_coverage_label(
                    folder,
                    payload,
                )

            self.assertEqual(
                label,
                "1/1 covered; 1 stale",
            )
            self.assertEqual(
                missing_digest_label,
                "1/1 covered",
            )
            self.assertEqual(
                sync_paper_status.llm_translation_label(folder, payload),
                "not run",
            )

    def test_stale_coverage_inventory_hides_saved_coverage_count(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "InventoryPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            statement_map = named_theorem_source_map(
                folder,
                "The source claim has this exact semantic content.",
            )
            write_json(audit / "paper_statement_map.json", statement_map)

            import review_dashboard

            inventory_digest = review_dashboard.paper_statement_inventory_digest(
                review_dashboard.paper_statement_inventory(folder)
            )
            surface_digest = review_dashboard.review_surface_digest([])
            source_item = review_dashboard.paper_statement_inventory(folder)[
                "source_claim"
            ]
            source_anchor_identity, source_anchor_error = (
                review_dashboard.source_anchor_quote_identity(source_item)
            )
            self.assertEqual(source_anchor_error, "")
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "audit_kind": "source_to_dashboard_llm",
                    "source_grounded": True,
                    "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                    "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                    "validator": "fixture-agent",
                    "validator_type": "agent",
                    "validated_at": "2026-07-26T12:00:00Z",
                    "source_coverage_mode": "named_theoretical_statements",
                    "source_artifact_path": statement_map["source_artifact_path"],
                    "source_artifact_sha256": statement_map["source_artifact_sha256"],
                    "paper_statement_inventory_sha256": inventory_digest,
                    "review_surface_sha256": surface_digest,
                    "items": {
                        "source_claim": {
                            "coverage": "covered",
                            "reason": "The reviewed semantic source item has a matching proof row.",
                            "source_evidence": "source.txt:1-1 records the exact source claim.",
                            "source_anchor_quote_identity_sha256": source_anchor_identity,
                        }
                    },
                },
            )

            with (
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    return_value=(review_dashboard, []),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    return_value=[],
                ),
            ):
                self.assertEqual(
                    sync_paper_status.llm_paper_coverage_label(folder, payload),
                    "1/1 covered",
                )

                statement_map = named_theorem_source_map(
                    folder,
                    "The source claim now has different semantic content.",
                )
                write_json(audit / "paper_statement_map.json", statement_map)
                label = sync_paper_status.llm_paper_coverage_label(folder, payload)

        self.assertEqual(
            label,
            "stale/unavailable: paper-coverage legacy item evidence is stale",
        )

    def test_explicit_pinned_artifact_must_still_match(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "PinnedArtifactPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            payload = paper_status(folder.name)
            statement_map = named_theorem_source_map(
                folder,
                "A stable semantic inventory entry.",
            )
            write_json(audit / "paper_statement_map.json", statement_map)

            import review_dashboard

            inventory_digest = review_dashboard.paper_statement_inventory_digest(
                review_dashboard.paper_statement_inventory(folder)
            )
            source_item = review_dashboard.paper_statement_inventory(folder)[
                "source_claim"
            ]
            source_anchor_identity, source_anchor_error = (
                review_dashboard.source_anchor_quote_identity(source_item)
            )
            self.assertEqual(source_anchor_error, "")
            surface_digest = review_dashboard.review_surface_digest([])
            write_json(
                audit / "paper_coverage_llm.json",
                {
                    "schema": 1,
                    "paper": folder.name,
                    "audit_kind": "source_to_dashboard_llm",
                    "source_grounded": True,
                    "source_input_protocol": "verbatim_source_anchor_bundle_v1",
                    "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
                    "validator": "fixture-agent",
                    "validator_type": "agent",
                    "validated_at": "2026-07-26T12:00:00Z",
                    "source_coverage_mode": "named_theoretical_statements",
                    "paper_statement_inventory_sha256": inventory_digest,
                    "review_surface_sha256": surface_digest,
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": statement_map["source_artifact_sha256"],
                    "items": {
                        "source_claim": {
                            "coverage": "covered",
                            "reason": "The reviewed semantic source item has a matching proof row.",
                            "source_evidence": "source.txt:1-1 records the exact source claim.",
                            "statement_sha256": source_item["statement_sha256"],
                            "source_item_coverage_digest_schema": (
                                SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                            ),
                            "source_item_coverage_sha256": (
                                review_dashboard.source_item_coverage_sha256(
                                    source_item,
                                    "named_theoretical_statements",
                                )
                            ),
                            "source_anchor_quote_identity_sha256": source_anchor_identity,
                        }
                    },
                },
            )

            with (
                mock.patch.object(
                    sync_paper_status,
                    "cached_current_review_surface_items",
                    return_value=(review_dashboard, []),
                ),
                mock.patch.object(
                    review_dashboard,
                    "review_items_for_paper",
                    return_value=[],
                ),
            ):
                self.assertEqual(
                    sync_paper_status.llm_paper_coverage_label(folder, payload),
                    "1/1 covered",
                )

                statement_map = named_theorem_source_map(
                    folder,
                    "A stable semantic inventory entry.",
                    preface="Preface.",
                )
                write_json(audit / "paper_statement_map.json", statement_map)
                label = sync_paper_status.llm_paper_coverage_label(folder, payload)

        self.assertEqual(
            label,
            "stale/unavailable: paper-coverage source artifact pin is stale",
        )

    def test_site_status_uses_saved_human_review_count_not_translation_freshness(self) -> None:
        html = sync_paper_status.render_site_status_block(
            {
                "papers": [
                    {
                        "id": "Example",
                        "title": "Example Paper",
                        "authors": "Example Author",
                        "publication": "Example Venue",
                        "source_url": "https://example.invalid/paper",
                        "status": "Formalized",
                        "review_entrypoint": "papers/Example/FINAL_VALIDATION_REPORT.md",
                        "artifacts": {},
                        "human_review": "4/4",
                        "human_translation": "needs refresh (4/4)",
                        "lean_loc": 12,
                        "main_note": "",
                        "main_note_citation": None,
                    }
                ]
            }
        )
        self.assertIn(">4/4</td>", html)
        self.assertNotIn("needs refresh", html)

    def test_v11_direct_source_spec_lane_supersedes_retired_sidecars(self) -> None:
        """A v11 closeout must display its raw-source judgment, not `not run`."""

        folder = Path("/tmp") / "V11DirectSourceSpecPaper"
        payload = paper_status(folder.name)
        payload["review_surface"] = {
            "require_v11_raw_source_spec_screening": True,
        }
        payload["human_review"] = {"total_rows": 2}
        counts = {
            "total": 2,
            "matches": 2,
            "mismatch": 0,
            "uncertain": 0,
            "unknown": 0,
        }
        with mock.patch.object(
            sync_paper_status,
            "current_v11_source_spec_counts",
            return_value=(counts, ""),
        ) as v11_counts:
            self.assertEqual(
                sync_paper_status.llm_translation_label(folder, payload),
                "2/2 raw-source-to-Spec match",
            )
            self.assertEqual(
                sync_paper_status.llm_paper_coverage_label(folder, payload),
                "2/2 source claims covered",
            )

        self.assertEqual(v11_counts.call_count, 2)

    def test_all_current_protocol_opt_ins_use_graph_status_without_legacy_reads(self) -> None:
        cases = (
            ({"require_source_spec_correspondence": True}, {}),
            ({"require_v11_raw_source_spec_screening": True}, {}),
            ({"llm_statement_review": {"require_theorem_realization_contract": True}}, {}),
            ({"llm_statement_review": {"required_prompt_version": "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-claim-atoms-v3"}}, {}),
            ({}, {"source_spec_correspondence_schema": 1}),
        )
        for opt_in, source_map in cases:
            with self.subTest(opt_in=opt_in, source_map=source_map):
                with tempfile.TemporaryDirectory() as temp_dir:
                    root = Path(temp_dir)
                    folder = root / "papers" / "Fixture"
                    audit = folder / "audit"
                    audit.mkdir(parents=True)
                    write_json(audit / "paper_statement_map.json", source_map)
                    payload = paper_status("Fixture")
                    payload["review_surface"] = {**opt_in, "include_names": ["claimSpec"]}
                    payload["human_review"] = {"total_rows": 1}
                    receipt = SimpleNamespace(payload={"schema": 6, "paper": "Fixture"})
                    projection = SimpleNamespace(
                        review_declarations_by_source_item={"claim": ("Fixture.claimSpec",)},
                        source_lean_verdicts_by_source_item={"claim": "matches"},
                    )
                    with (
                        mock.patch.object(sync_paper_status, "ROOT", root),
                        mock.patch("final_closure_receipt.load_final_closure_receipt", return_value=receipt),
                        mock.patch("obligation_closure_credential.validate_nonaccepting_recorded_graph_projection", return_value=projection),
                        mock.patch.object(sync_paper_status, "saved_sidecar_reuse_authorization", side_effect=AssertionError("selected v11 consulted legacy reuse")),
                        mock.patch.object(sync_paper_status, "load_llm_statement_judgments", side_effect=AssertionError("selected v11 read legacy judgments")),
                    ):
                        self.assertEqual(sync_paper_status.llm_translation_label(folder, payload), "accepted closeout: 1/1 raw-source-to-Spec match")
                        self.assertEqual(sync_paper_status.llm_paper_coverage_label(folder, payload), "accepted closeout: 1/1 source claims covered")

    def test_correspondence_only_failed_graph_stays_in_current_status_lane(self) -> None:
        payload = paper_status("Fixture")
        payload["review_surface"] = {"require_source_spec_correspondence": True}
        with (
            mock.patch.object(sync_paper_status, "current_v11_source_spec_counts", return_value=(None, "graph unavailable")),
            mock.patch.object(sync_paper_status, "saved_sidecar_reuse_authorization", side_effect=AssertionError("failed v11 graph fell back to legacy")),
        ):
            label = sync_paper_status.llm_translation_label(Path("/tmp/Fixture"), payload)
            self.assertIn("graph unavailable", label)

    def test_v11_status_counts_read_the_pinned_ledger_without_elaboration(self) -> None:
        """The static status projection must not turn a receipt check into Lean work."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            screening_path = audit / "v11_raw_source_spec_screening.json"
            write_json(
                screening_path,
                {
                    "schema": 2,
                    "paper": "Fixture",
                    "validator": "fixture reviewer",
                    "validated_at": "2026-08-18",
                    "items": {"Fixture.PaperInterface.claimSpec": {"judgment": "matches"}},
                },
            )
            payload = paper_status("Fixture")
            payload["review_surface"] = {
                "require_v11_raw_source_spec_screening": True,
            }
            payload["human_review"] = {"total_rows": 1}
            receipt = SimpleNamespace(
                payload={
                    "paper": "Fixture",
                    "closure_status": "current",
                    "evidence_lane": "direct-source-row-review",
                    "review_ledger": {
                        "path": "papers/Fixture/audit/v11_raw_source_spec_screening.json",
                        "sha256": hashlib.sha256(screening_path.read_bytes()).hexdigest(),
                    },
                }
            )

            with mock.patch.object(sync_paper_status, "ROOT", root), mock.patch(
                "final_closure_receipt.load_final_closure_receipt",
                return_value=receipt,
            ):
                counts, problem = sync_paper_status.current_v11_source_spec_counts(
                    folder,
                    payload,
                )

        self.assertEqual(problem, "")
        self.assertEqual(
            counts,
            {"total": 1, "matches": 1, "mismatch": 0, "uncertain": 0, "unknown": 0},
        )

    def test_schema6_status_uses_only_the_nonaccepting_recorded_projection(self) -> None:
        """Website rendering must not invoke the terminal Lean validator."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            write_json(
                audit / "paper_statement_map.json",
                {
                    "schema": 1,
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "semantic_contract": {
                                "spec_declaration": "Fixture.claimSpec"
                            }
                        }
                    },
                },
            )
            payload = paper_status("Fixture")
            payload["review_surface"] = {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["claimSpec"],
            }
            payload["human_review"] = {"total_rows": 1}
            receipt = SimpleNamespace(
                payload={
                    "schema": 6,
                    "paper": "Fixture",
                    "closure_status": "current",
                    "accepted_graph": {"graph_sha256": "a" * 64},
                }
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch(
                    "final_closure_receipt.load_final_closure_receipt",
                    return_value=receipt,
                ),
                mock.patch(
                    "obligation_closure_credential.validate_nonaccepting_recorded_graph_projection",
                    return_value=SimpleNamespace(
                        graph_sha256="a" * 64,
                        review_declarations_by_source_item={
                            "claim": ("Fixture.claimSpec",)
                        },
                        source_lean_verdicts_by_source_item={"claim": "matches"},
                    ),
                ) as projection,
                mock.patch(
                    "final_closure_receipt.validate_final_closure_receipt",
                    side_effect=AssertionError("status launched terminal validation"),
                ),
                mock.patch.object(
                    sync_paper_status,
                    "load_json_object",
                    side_effect=AssertionError(
                        "status reparsed a graph-authenticated source map"
                    ),
                ),
            ):
                counts, problem = sync_paper_status.current_v11_source_spec_counts(
                    folder, payload
                )

        self.assertEqual(problem, "")
        self.assertEqual(counts["matches"], 1)
        projection.assert_called_once_with(root, "Fixture", receipt.payload)

    def test_schema6_status_counts_explicit_condition_and_excludes_deep_items(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            write_json(
                audit / "paper_statement_map.json",
                {
                    "schema": 1,
                    "paper": "Fixture",
                    "items": {
                        "corrected_result": {
                            "semantic_contract": {
                                "spec_declaration": "Fixture.correctedResultSpec"
                            }
                        },
                        "paper_condition": {
                            "lean_declarations": ["Fixture.PaperCondition"]
                        },
                        "deep_support": {
                            "inventory_role": "deep_audit_material",
                            "lean_declarations": ["Fixture.DeepSupport"]
                        },
                    },
                },
            )
            # This stale legacy spelling must not influence graph-native status.
            write_json(
                audit / "v11_raw_source_spec_screening.json",
                {
                    "schema": 2,
                    "paper": "Fixture",
                    "validator": "old reviewer",
                    "validated_at": "2026-08-18",
                    "items": {
                        "Fixture.correctedResultSpec": {
                            "judgment": "matches_approved_corrected_target"
                        }
                    },
                },
            )
            payload = paper_status("Fixture")
            payload["review_surface"] = {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["correctedResultSpec"],
                "source_condition_items": ["paper_condition"],
            }
            payload["human_review"] = {"total_rows": 2}
            receipt = SimpleNamespace(payload={"schema": 6})
            projection = SimpleNamespace(
                graph_sha256="a" * 64,
                review_declarations_by_source_item={
                    "corrected_result": ("Fixture.correctedResultSpec",),
                    "paper_condition": ("Fixture.PaperCondition",),
                    "deep_support": ("Fixture.DeepSupport",),
                },
                source_lean_verdicts_by_source_item={
                    "corrected_result": "matches",
                    "paper_condition": "matches",
                    "deep_support": "does_not_match",
                },
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch(
                    "final_closure_receipt.load_final_closure_receipt",
                    return_value=receipt,
                ),
                mock.patch(
                    "obligation_closure_credential.validate_nonaccepting_recorded_graph_projection",
                    return_value=projection,
                ),
            ):
                counts, problem = sync_paper_status.current_v11_source_spec_counts(
                    folder, payload
                )

        self.assertEqual(problem, "")
        self.assertEqual(
            counts,
            {
                "total": 2,
                "matches": 2,
                "mismatch": 0,
                "uncertain": 0,
                "unknown": 0,
                "recorded_closeout": 1,
            },
        )

    def test_schema6_status_requires_explicit_condition_item_selection(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            write_json(
                audit / "paper_statement_map.json",
                {
                    "schema": 1,
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "semantic_contract": {
                                "spec_declaration": "Fixture.claimSpec"
                            }
                        },
                        "condition": {
                            "lean_declarations": ["Fixture.Condition"]
                        },
                    },
                },
            )
            payload = paper_status("Fixture")
            payload["review_surface"] = {
                "require_v11_raw_source_spec_screening": True,
                "include_names": ["claimSpec"],
            }
            payload["human_review"] = {"total_rows": 2}
            receipt = SimpleNamespace(payload={"schema": 6})
            projection = SimpleNamespace(
                graph_sha256="a" * 64,
                review_declarations_by_source_item={
                    "claim": ("Fixture.claimSpec",),
                    "condition": ("Fixture.Condition",),
                },
                source_lean_verdicts_by_source_item={
                    "claim": "matches",
                    "condition": "matches",
                },
            )
            with (
                mock.patch.object(sync_paper_status, "ROOT", root),
                mock.patch(
                    "final_closure_receipt.load_final_closure_receipt",
                    return_value=receipt,
                ),
                mock.patch(
                    "obligation_closure_credential.validate_nonaccepting_recorded_graph_projection",
                    return_value=projection,
                ),
            ):
                counts, problem = sync_paper_status.current_v11_source_spec_counts(
                    folder, payload
                )

        self.assertIsNone(counts)
        self.assertIn("selection does not equal total_rows", problem)

    def test_public_display_preserves_internal_coverage_dispositions(self) -> None:
        for status in ("formalized", "formalized with caveat", "partially formalized", "conditional"):
            with self.subTest(status=status):
                payload = paper_status("LimitedScope")
                payload["status"] = status
                payload["human_summary"] = (
                    "Limited scope: Theorem 3 proves the forward implication; "
                    "the reverse implication remains unproved."
                )
                original = dict(payload)
                self.assertEqual(sync_paper_status.human_status_label(status), "Formalized")
                self.assertEqual(sync_paper_status.human_note(payload), payload["human_summary"])
                self.assertEqual(payload, original)
        self.assertEqual(sync_paper_status.status_label("partially formalized"), "Partially formalized")
        for status in ("not started", "not formalized", "paper draft", "scaffold"):
            with self.subTest(status=status):
                self.assertEqual(
                    sync_paper_status.human_status_label(status),
                    sync_paper_status.status_label(status),
                )

    def test_designated_unfinished_papers_retain_partial_display_and_count(self) -> None:
        with mock.patch.object(sync_paper_status, "CATALOG_PAYLOAD", {
            "preserve_partial_status": ["Unfinished"],
        }):
            labels = [
                sync_paper_status.human_status_label(status, paper_id=paper)
                for paper, status in [
                    ("Unfinished", "partially formalized"),
                    ("Other", "partially formalized"),
                    ("Unfinished", "formalized"),
                ]
            ]
        self.assertEqual(labels, ["Partially formalized", "Formalized", "Formalized"])
        with mock.patch.object(sync_paper_status, "component_loc", return_value=0):
            rendered = sync_paper_status.render_site_stats_block({"papers": [
                {"id": str(i), "status": label, "lean_loc": 0}
                for i, label in enumerate(labels)
            ]})
        self.assertIn("2 formalized papers and 1 partially formalized paper", rendered)

    def test_draft_human_summary_is_not_projected_as_public_note(self) -> None:
        payload = paper_status("DraftSummary")
        payload["status"] = "formalized"
        payload["human_summary"] = "Draft wording that is not user-approved."
        payload["human_summary_review"] = {"status": "draft"}
        self.assertEqual(sync_paper_status.human_note(payload), "")

        payload["human_summary_review"] = {"status": "human_approved"}
        self.assertEqual(
            sync_paper_status.human_note(payload),
            "Draft wording that is not user-approved.",
        )
        payload["human_summary_review"] = {"status": "human_written"}
        self.assertEqual(
            sync_paper_status.human_note(payload),
            "Draft wording that is not user-approved.",
        )

    def test_public_copy_survives_incoming_paper_summary_and_status_changes(self) -> None:
        payload = paper_status("ProtectedCopy")
        payload.update({
            "human_summary": "Unrequested replacement from a paper closeout.",
            "human_summary_review": {"status": "human_approved"},
            "main_caveat": "Implementation details from an audit.",
        })
        for preserved in ("An exact maintainer note.", ""):
            with mock.patch.dict(sync_paper_status.CATALOG_PAYLOAD, {
                "public_summary_overrides": {"ProtectedCopy": preserved},
            }):
                for status in ("formalized", "partially formalized"):
                    payload["status"] = status
                    self.assertEqual(sync_paper_status.human_note(payload), preserved)

    def test_malformed_public_copy_never_falls_back_to_paper_draft(self) -> None:
        with mock.patch.dict(sync_paper_status.CATALOG_PAYLOAD, {
            "public_summary_overrides": {"ProtectedCopy": None},
        }):
            with self.assertRaisesRegex(ValueError, "exact text"):
                sync_paper_status.human_note(paper_status("ProtectedCopy"))

    def test_site_artifact_anchor_uses_neutral_local_preview_route(self) -> None:
        anchor = sync_paper_status.artifact_anchor(
            "Review packet", "papers/Fixture/docs/HUMAN_REVIEW_PACKET.pdf"
        )
        self.assertIn('data-local-artifact-href="/artifacts/papers/Fixture/', anchor)
        self.assertNotIn("private-artifacts", anchor)
        self.assertNotIn("data-private-local-href", anchor)

    def test_site_uses_a_preview_capability_before_rewriting_artifact_links(self) -> None:
        site_text = (ROOT / "site" / "index.html").read_text(encoding="utf-8")
        self.assertIn('fetch("/.local-artifact-capability"', site_text)
        self.assertIn('data-local-artifact-href', site_text)
        self.assertNotIn('data-private-local-href', site_text)
        self.assertNotIn('/private-artifacts/', site_text)

    def test_site_preserves_display_name_and_former_name_without_slack(self) -> None:
        site_text = (ROOT / "site" / "index.html").read_text(encoding="utf-8")
        sync_paper_status.assert_required_static_site_copy(site_text)
        self.assertIn("<title>Applied Modeling Lib</title>", site_text)
        self.assertIn("This project was previously called EconCSLib.", site_text)
        self.assertNotIn("join.slack.com", site_text)
        self.assertNotIn("Slack workspace link", sync_paper_status.SITE_REQUIRED_STATIC_COPY)

    def test_publication_fallback_never_renders_source_provenance(self) -> None:
        with mock.patch.object(sync_paper_status, "PUBLICATION_OVERRIDES", {}):
            label, year = sync_paper_status.publication_for({
                "id": "Fixture",
                "source_version": "Private Overleaf draft.tex at revision SHA-256 abc123",
            })
        self.assertEqual(label, "Publication details not listed")
        self.assertEqual(year, 9999)
        with mock.patch.object(sync_paper_status, "SOURCE_URL_OVERRIDES", {}):
            self.assertEqual(sync_paper_status.source_url_for({
                "id": "Fixture", "source_url": "https://www.overleaf.com/project/private",
            }), "")

    def test_site_total_includes_shared_library_and_public_paper_roots_once(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "AppliedModelingLib").mkdir()
            (root / "papers").mkdir()
            (root / "AppliedModelingLib" / "Shared.lean").write_text("a\nb\n")
            (root / "AppliedModelingLib.lean").write_text("c\n")
            (root / "papers" / "A.lean").write_text("d\n")
            (root / "papers" / "B.lean").write_text("e\n")
            (root / "papers" / "Private.lean").write_text("not counted\n")
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.render_site_stats_block({"papers": [
                    {"id": "A", "status": "Formalized", "lean_loc": 10},
                    {"id": "B", "status": "Formalized", "lean_loc": 20},
                ]})
        self.assertIn("35 total lines of Lean code", rendered)
        self.assertIn("2 formalized papers", rendered)
        self.assertNotIn("partially formalized", rendered)

    def test_site_links_the_actual_paper_interface_locally_and_publicly(self) -> None:
        rendered = sync_paper_status.site_paper_artifact_links({
            "id": "Fixture",
            "status": "Formalized",
            "review_entrypoint": "papers/Fixture/FINAL_VALIDATION_REPORT.md",
            "artifacts": {"paper_interface": "papers/Fixture/PaperInterface.lean"},
        })
        self.assertIn(
            'href="https://github.com/nikhgarg/EconCSLib/blob/main/papers/Fixture/PaperInterface.lean"',
            rendered,
        )
        self.assertIn('data-local-artifact-href="/artifacts/papers/Fixture/PaperInterface.lean"', rendered)
        self.assertIn(">Lean statements</a>", rendered)
        self.assertIn(">Report</a>", rendered)
        self.assertIn(
            '<a href="https://github.com/nikhgarg/EconCSLib/tree/main/papers/Fixture">Repo</a>',
            rendered,
        )
        self.assertNotIn(">Formalized</a>", rendered)

    def test_site_links_generated_packet_and_pdf_dag_without_status_metadata(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            docs = root / "papers" / "Fixture" / "docs"
            docs.mkdir(parents=True)
            (docs / "HUMAN_REVIEW_PACKET.pdf").write_bytes(b"%PDF-1.5\n")
            (docs / "DependencyDAG.pdf").write_bytes(b"%PDF-1.5\n")
            with mock.patch.object(sync_paper_status, "ROOT", root):
                rendered = sync_paper_status.site_paper_artifact_links({
                    "id": "Fixture",
                    "review_entrypoint": "papers/Fixture/FINAL_VALIDATION_REPORT.md",
                    "artifacts": {"dependency_dag_tex": "papers/Fixture/docs/DependencyDAG.tex"},
                })
        self.assertIn("docs/HUMAN_REVIEW_PACKET.pdf", rendered)
        self.assertIn("docs/DependencyDAG.pdf", rendered)
        self.assertNotIn("docs/DependencyDAG.tex", rendered)

    def test_library_catalog_uses_existing_nonoverlapping_architecture_paths(self) -> None:
        covered_files: set[Path] = set()
        represented_areas: set[str] = set()
        for component in sync_paper_status.LIBRARY_COMPONENTS:
            component_files: set[Path] = set()
            self.assertTrue(component["examples"])
            for relative in component["paths"]:
                path = ROOT / relative
                self.assertTrue(path.exists(), relative)
                represented_areas.add(Path(relative).parts[1].removesuffix(".lean"))
                if path.is_dir():
                    component_files.update(path.rglob("*.lean"))
                else:
                    component_files.add(path)
            self.assertFalse(covered_files & component_files, component["title"])
            covered_files.update(component_files)
        research_areas = {
            path.name for path in (ROOT / "AppliedModelingLib").iterdir()
            if path.is_dir() and path.name != "Audit"
        }
        self.assertEqual(represented_areas, research_areas)


if __name__ == "__main__":
    unittest.main()
