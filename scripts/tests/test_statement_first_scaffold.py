#!/usr/bin/env python3
"""Regression tests for the statement-first new-paper scaffold."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.current_closeout.protocol_selection import current_v11_protocol_selected

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "new_paper", ROOT / "scripts" / "new_paper.py"
)
assert SPEC is not None and SPEC.loader is not None
NEW_PAPER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = NEW_PAPER
SPEC.loader.exec_module(NEW_PAPER)


class StatementFirstScaffoldTests(unittest.TestCase):
    def install_status_sync_fixture(self, root: Path) -> None:
        config = root / "config"
        config.mkdir()
        (config / "formalization_audit_protocol.json").write_bytes(
            (ROOT / "config" / "formalization_audit_protocol.json").read_bytes()
        )

    def write_spec(
        self,
        directory: Path,
        *,
        source_location: str = "Theorem 2, p. 4",
        source_kind: str = "theorem",
        recorded_sha256: str | None = None,
        artifact_name: str = "source-transcript.txt",
        artifact_bytes: bytes = b"Theorem 2. For every n, n equals itself.\n",
    ) -> tuple[Path, bytes]:
        artifact = directory / artifact_name
        artifact.write_bytes(artifact_bytes)
        digest = hashlib.sha256(artifact_bytes).hexdigest()
        spec_path = directory / "statement-spec.json"
        spec_path.write_text(
            json.dumps(
                {
                    "schema": 1,
                    "source_artifact_path": artifact.name,
                    "source_artifact_sha256": recorded_sha256 or digest,
                    "source_version": "arXiv v2 (2025-01-01)",
                    "targets": [
                        {
                            "source_item": "Theorem 2",
                            "source_kind": source_kind,
                            "source_location": source_location,
                            "source_statement": "For every natural n, n equals itself.",
                            "lean_name": "theorem2_reflexive",
                            "lean_type": "(n : Nat) -> n = n",
                            "kind": "theorem",
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return spec_path, artifact_bytes

    def test_interface_without_spec_has_no_fake_target_or_proof(self) -> None:
        interface = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example"
        )
        assumptions = NEW_PAPER.assumption_source_text(
            "Example", "EX00Example", "EX00Example"
        )
        implementation = NEW_PAPER.main_theorems_text("Example", "EX00Example")
        self.assertIn("Intentionally no theorem placeholder", interface)
        self.assertNotIn("theorem paper_", interface)
        self.assertNotIn(":= by\n  sorry", interface)
        self.assertNotIn("abbrev paperDefinition", interface)
        self.assertNotIn("assumption_source_model_conditions", assumptions)
        self.assertNotIn("theorem paper_theorem_1", implementation)
        self.assertNotIn("trivial", implementation)
        NEW_PAPER.validate_rendered_statement_interface("EX00Example", [], interface)

    def test_verified_spec_emits_exact_type_but_not_source_certification(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        interface = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        proof_interface = NEW_PAPER.proof_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        self.assertIn(
            "def theorem2_reflexiveSpec : Prop :=\n  (n : Nat) -> n = n",
            interface,
        )
        self.assertIn(
            "theorem theorem2_reflexive :\n  theorem2_reflexiveSpec := by",
            proof_interface,
        )
        self.assertNotIn("theorem theorem2_reflexive", interface)
        self.assertIn("\n  sorry", proof_interface)
        self.assertIn(
            "Source status: pinned statement-spec transcription; independent source audit pending",
            interface,
        )
        self.assertNotIn("Source status: direct source text", interface)

        args = argparse.Namespace(
            official_url="https://example.test/paper",
            url="https://example.test/paper.pdf",
        )
        source_map = json.loads(
            NEW_PAPER.paper_statement_map_text(
                args,
                "EX00Example",
                spec,
                "papers/EX00Example/source-audited.txt",
            )
        )
        self.assertFalse(source_map["source_curated"])
        self.assertTrue(source_map["seed_scaffold"])
        self.assertEqual(
            source_map["source_artifact_path"],
            "papers/EX00Example/source-audited.txt",
        )
        self.assertIn(
            "independent source audit pending",
            source_map["items"]["theorem2_reflexive"]["source_status"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["proof_lean_declarations"],
            ["theorem2_reflexive"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["spec_lean_declarations"],
            ["theorem2_reflexiveSpec"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["semantic_contract_template"],
            {
                "spec_declaration": "theorem2_reflexiveSpec",
                "evidence_declaration": "theorem2_reflexive",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        )
        self.assertNotIn("semantic_contract", source_map["items"]["theorem2_reflexive"])
        self.assertNotIn("lean_declarations", source_map["items"]["theorem2_reflexive"])
        self.assertNotIn("semantic_contract_schema", source_map)
        self.assertNotIn("source_spec_correspondence_schema", source_map)
        self.assertIn(
            "Do not manufacture a contract",
            source_map["semantic_contract_policy"]["activation"],
        )
        activation = source_map["semantic_contract_policy"]["activation"]
        self.assertNotIn("source_spec_correspondence_schema: 1", activation)
        self.assertIn("builder-issued Lean graph owns", activation)
        self.assertIn("proof and instance arguments", activation)
        self.assertIn("current accepted obligation graph", activation)

    def test_v11_requirement_selects_graph_lane_without_legacy_correspondence(
        self,
    ) -> None:
        args = argparse.Namespace(
            title="Example",
            authors="A. Author",
            version="arXiv v2 (2025-01-01)",
        )
        status = json.loads(NEW_PAPER.status_text(args, "EX00Example"))
        self.assertEqual(status["status"], "not started")
        self.assertEqual(status["repository_visibility"], "private_only")
        self.assertIs(status["source_inventory_review_required"], True)
        self.assertNotIn("intake_freeze_required", status)
        self.assertTrue(
            status["review_surface"]["require_v11_raw_source_spec_screening"]
        )
        self.assertNotIn(
            "require_source_spec_correspondence", status["review_surface"]
        )
        source_map = {"schema": 1, "items": {}}
        self.assertTrue(current_v11_protocol_selected(status, source_map))
        self.assertNotIn("source_spec_correspondence_schema", source_map)

    def test_main_copies_verified_artifact_to_stable_paper_local_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.install_status_sync_fixture(root)
            papers = root / "papers"
            papers.mkdir()
            template_dir = papers / "TEMPLATE"
            template_dir.mkdir()
            spec_path, artifact_bytes = self.write_spec(root)
            args = argparse.Namespace(
                url="https://example.test/paper.pdf",
                folder="EX00Example",
                title="Example",
                authors="A. Author",
                version="arXiv v2 (2025-01-01)",
                official_url="https://example.test/paper",
                pdf_url=None,
                namespace="EX00Example",
                statement_spec=spec_path,
                no_download=True,
                force=True,
                with_notes=False,
            )
            with (
                mock.patch.object(NEW_PAPER, "ROOT", root),
                mock.patch.object(NEW_PAPER, "PAPERS", papers),
                mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                mock.patch.object(NEW_PAPER, "refresh_review_cache") as refresh_cache,
            ):
                self.assertEqual(NEW_PAPER.main(), 0)
            refresh_cache.assert_not_called()

            paper = papers / "EX00Example"
            audited = paper / "source-audited.txt"
            self.assertEqual(audited.read_bytes(), artifact_bytes)
            self.assertIn(
                "source-audited*", (paper / ".gitignore").read_text(encoding="utf-8")
            )
            source_map = json.loads(
                (paper / "audit" / "paper_statement_map.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                source_map["source_artifact_path"],
                "papers/EX00Example/source-audited.txt",
            )
            review_config = json.loads(
                (
                    paper / "audit" / "v11_source_map_preparation_config.json"
                ).read_text(encoding="utf-8")
            )
            self.assertFalse(
                review_config["source_named_result_inventory_review"]["complete"]
            )
            self.assertEqual(
                review_config["include_specs"], ["theorem2_reflexiveSpec"]
            )
            self.assertEqual(
                review_config["source_item_for_spec"],
                {"theorem2_reflexiveSpec": "theorem2_reflexive"},
            )
            self.assertEqual(
                review_config["source_named_result_inventory_review"][
                    "candidate_presentations"
                ],
                [],
            )
            self.assertFalse((paper / "audit" / "intake_freeze.json").exists())
            proof_fidelity = json.loads(
                (paper / "audit" / "source_proof_fidelity.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(proof_fidelity["review_status"], "not_started")
            self.assertEqual(proof_fidelity["model_conventions"], [])
            self.assertEqual(proof_fidelity["checked_proof_steps"], [])
            self.assertIn(
                "checked_scope",
                proof_fidelity["model_convention_entry_schema"]["required"],
            )
            self.assertEqual(
                proof_fidelity["source_artifact_path"],
                "papers/EX00Example/source-audited.txt",
            )
            self.assertEqual(
                proof_fidelity["source_artifact_sha256"],
                hashlib.sha256(artifact_bytes).hexdigest(),
            )
            self.assertNotIn(
                "validated_source_assumption",
                proof_fidelity["defect_entry_schema"]["resolution_values"],
            )
            self.assertIn("id", proof_fidelity["defect_entry_schema"]["required"])
            defect_support = json.loads(
                (paper / "audit" / "defect_support_match_llm.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                defect_support["prompt_version"],
                "defect-support-v1-exact-source-defect-to-lean-semantic",
            )
            status = json.loads((paper / "status.json").read_text(encoding="utf-8"))
            self.assertEqual(status["paper_interface"]["declaration_rows"], 1)
            self.assertEqual(status["paper_interface"]["review_rows"], 1)
            self.assertEqual(
                status["review_surface"]["include_names"],
                ["theorem2_reflexiveSpec"],
            )
            self.assertEqual(
                status["review_surface"]["proposition_spec_proofs"],
                {"theorem2_reflexiveSpec": "theorem2_reflexive"},
            )
            self.assertEqual(
                status["review_surface"]["proof_module"],
                "EX00Example.ProofInterface",
            )
            self.assertEqual(
                status["review_surface"]["proof_file"],
                "papers/EX00Example/ProofInterface.lean",
            )
            review = status["review_surface"]["source_proof_fidelity_review"]
            self.assertEqual(
                review["ledger_file"],
                "papers/EX00Example/audit/source_proof_fidelity.json",
            )
            self.assertEqual(
                status["artifacts"]["defect_support_match"],
                "papers/EX00Example/audit/defect_support_match_llm.json",
            )
            self.assertNotIn(
                "llm_paper_coverage_review", status["review_surface"]
            )
            self.assertTrue(
                status["review_surface"]["llm_statement_review"][
                    "require_explicit_source_routes"
                ]
            )
            self.assertEqual(
                status["review_surface"]["llm_statement_review"][
                    "require_direct_expression_semantics_review"
                ],
                "v1",
            )
            self.assertTrue(
                status["review_surface"]["require_v11_raw_source_spec_screening"]
            )
            route_policy = status["review_surface"]["llm_statement_review"]["policy"]
            self.assertIn("exact equivalent paper-facing endpoint", route_policy)
            self.assertIn("source_model_convention", route_policy)
            self.assertIn("defect_or_remark_support", route_policy)
            self.assertIn("proof_support", route_policy)
            model_review = status["review_surface"]["semantic_model_review"]
            self.assertEqual(
                model_review["schema"], NEW_PAPER.SEMANTIC_MODEL_REVIEW_SCHEMA
            )
            self.assertEqual(
                set(model_review["required_dimensions"]),
                set(NEW_PAPER.SEMANTIC_MODEL_DIMENSION_ORDER),
            )
            self.assertNotIn("llm_source_record_review", status["review_surface"])
            self.assertNotIn(
                "lean_to_tex_file",
                status["review_surface"]["llm_statement_review"],
            )
            self.assertNotIn(
                "match_judgment_file",
                status["review_surface"]["llm_statement_review"],
            )
            self.assertFalse((paper / "audit" / "lean_to_tex_llm.json").exists())
            self.assertFalse((paper / "audit" / "statement_match_llm.json").exists())
            self.assertFalse((paper / "audit" / "review_surface_llm.json").exists())
            self.assertFalse((paper / "audit" / "paper_coverage_llm.json").exists())
            self.assertFalse(
                (paper / "audit" / "source_record_match_llm.json").exists()
            )
            self.assertFalse((paper / "source.pdf").exists())
            readme = (paper / "README.md").read_text(encoding="utf-8")
            self.assertTrue(
                readme.startswith("<!-- BEGIN GENERATED PAPER FOLDER README -->\n")
            )
            notes = paper / "docs" / "FORMALIZATION_NOTES.md"
            self.assertTrue(notes.is_file())
            self.assertIn("## Paper-Facing Ledger", notes.read_text(encoding="utf-8"))
            working_memo = paper / "docs" / "FORMALIZATION_WORKING_MEMO.md"
            self.assertTrue(working_memo.is_file())
            self.assertIn(
                "working lead log, not audit evidence",
                working_memo.read_text(encoding="utf-8"),
            )
            self.assertFalse((paper / "FINAL_VALIDATION_REPORT.md").exists())
            self.assertFalse((paper / "docs" / "DependencyDAG.tex").exists())
            self.assertFalse((paper / "docs" / "DependencyDAG.pdf").exists())
            status_check = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "scripts" / "sync_paper_status.py"),
                    "--repo",
                    str(root),
                    "--paper",
                    "EX00Example",
                    "--check",
                ],
                cwd=root,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                status_check.returncode,
                0,
                status_check.stderr or status_check.stdout,
            )

    def test_main_keeps_pdf_extraction_outside_the_intake_authority(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.install_status_sync_fixture(root)
            papers = root / "papers"
            papers.mkdir()
            template_dir = papers / "TEMPLATE"
            template_dir.mkdir()
            pdf_bytes = b"%PDF-1.7 fixture"
            spec_path, _ = self.write_spec(
                root,
                artifact_name="source-transcript.pdf",
                artifact_bytes=pdf_bytes,
            )
            args = argparse.Namespace(
                url="https://example.test/paper.pdf",
                folder="EX00Example",
                title="Example",
                authors="A. Author",
                version="arXiv v2 (2025-01-01)",
                official_url="https://example.test/paper",
                pdf_url=None,
                namespace="EX00Example",
                statement_spec=spec_path,
                no_download=True,
                force=True,
                with_notes=False,
            )

            def extract_fixture(_pdf: Path, txt: Path, _force: bool) -> bool:
                txt.write_bytes(b"Theorem 2.\r\nFor every n, n equals itself.\r")
                return True

            with (
                mock.patch.object(NEW_PAPER, "ROOT", root),
                mock.patch.object(NEW_PAPER, "PAPERS", papers),
                mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                mock.patch.object(
                    NEW_PAPER, "extract_text", side_effect=extract_fixture
                ),
            ):
                self.assertEqual(NEW_PAPER.main(), 0)

            paper = papers / "EX00Example"
            review_config = json.loads(
                (
                    paper / "audit" / "v11_source_map_preparation_config.json"
                ).read_text(encoding="utf-8")
            )
            self.assertEqual(
                (paper / "source.txt").read_bytes(),
                b"Theorem 2.\r\nFor every n, n equals itself.\r",
            )
            self.assertFalse((paper / "audit" / "intake_freeze.json").exists())
            self.assertFalse(
                review_config["source_named_result_inventory_review"]["complete"]
            )

    def test_spec_rejects_hash_mismatch_vague_locator_and_definition_kind(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            mismatch, _ = self.write_spec(directory, recorded_sha256="0" * 64)
            with self.assertRaisesRegex(
                ValueError, "does not match source artifact bytes"
            ):
                NEW_PAPER.load_statement_spec(mismatch)

            vague, _ = self.write_spec(
                directory, source_location="near the main result"
            )
            with self.assertRaisesRegex(ValueError, "no exact source locator"):
                NEW_PAPER.load_statement_spec(vague)

            definition, _ = self.write_spec(directory, source_kind="definition")
            with self.assertRaisesRegex(ValueError, "unsupported source_kind"):
                NEW_PAPER.load_statement_spec(definition)

            runtime_claim, _ = self.write_spec(directory, source_kind="runtime_claim")
            runtime_spec = NEW_PAPER.load_statement_spec(runtime_claim)
            self.assertEqual(runtime_spec.targets[0].source_kind, "runtime_claim")

    def test_spec_rejects_declaration_breakout_but_allows_type_local_assignments(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            spec_path, _ = self.write_spec(directory)
            payload = json.loads(spec_path.read_text(encoding="utf-8"))
            payload["targets"][0]["lean_type"] = (
                "True := by trivial\naxiom hidden : False\ntheorem dummy : True"
            )
            spec_path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "top-level"):
                NEW_PAPER.load_statement_spec(spec_path)

        NEW_PAPER._validate_lean_type_fragment(
            "let n : Nat := 1\nList.replicate (n := n) True = [True]", 1
        )

    def test_post_render_validation_rejects_an_extra_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        injected = rendered.replace(
            "\n\nend EX00Example", "\n\naxiom hidden : False\n\nend EX00Example"
        )
        with self.assertRaisesRegex(ValueError, "outside the requested targets"):
            NEW_PAPER.validate_rendered_statement_interface(
                "EX00Example", spec.targets, injected
            )

    def test_post_render_validation_rejects_changed_spec_or_proof_route(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        changed_spec = rendered.replace(
            "(n : Nat) -> n = n", "(n : Nat) -> n + 1 = n", 1
        )
        with self.assertRaisesRegex(ValueError, "transparent `...Spec : Prop`"):
            NEW_PAPER.validate_rendered_statement_interface(
                "EX00Example", spec.targets, changed_spec
            )
        proof_rendered = NEW_PAPER.proof_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        changed_proof = proof_rendered.replace(
            "theorem2_reflexiveSpec := by", "True := by", 1
        )
        with self.assertRaisesRegex(ValueError, "`...Spec := by sorry`"):
            NEW_PAPER.validate_rendered_proof_interface(
                "EX00Example", spec.targets, changed_proof
            )

    def test_spec_rejects_generated_spec_name_collision(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            spec_path, _ = self.write_spec(directory)
            payload = json.loads(spec_path.read_text(encoding="utf-8"))
            second = dict(payload["targets"][0])
            second["lean_name"] = "theorem2_reflexiveSpec"
            second["source_item"] = "Theorem 3"
            second["source_location"] = "Theorem 3, p. 5"
            second["source_statement"] = "For every natural n, n equals itself again."
            payload["targets"].append(second)
            spec_path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaisesRegex(
                ValueError, "collide after generating `...Spec`"
            ):
                NEW_PAPER.load_statement_spec(spec_path)

    def test_post_render_validation_imports_econcs_library_surface(self) -> None:
        target = NEW_PAPER.StatementTarget(
            source_item="Theorem 3",
            source_kind="theorem",
            source_location="Theorem 3, p. 5",
            source_statement="Every position environment equals itself.",
            lean_name="theorem3_environment_reflexive",
            lean_type=(
                "(environment : AppliedModelingLib.Auction.PositionEnvironment Unit) -> "
                "environment = environment"
            ),
        )
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        proof_rendered = NEW_PAPER.proof_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        NEW_PAPER.validate_rendered_statement_interface(
            "EX00Example", [target], rendered
        )
        NEW_PAPER.validate_rendered_proof_interface(
            "EX00Example", [target], proof_rendered
        )

    def test_statement_first_pair_preserves_lemma_kind(self) -> None:
        target = NEW_PAPER.StatementTarget(
            source_item="Lemma 1",
            source_kind="lemma",
            source_location="Lemma 1, p. 2",
            source_statement="Every natural number equals itself.",
            lean_name="lemma1_reflexive",
            lean_type="(n : Nat) -> n = n",
            kind="lemma",
        )
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        proof_rendered = NEW_PAPER.proof_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        self.assertIn(
            "def lemma1_reflexiveSpec : Prop :=\n  (n : Nat) -> n = n",
            rendered,
        )
        self.assertIn(
            "lemma lemma1_reflexive :\n  lemma1_reflexiveSpec := by",
            proof_rendered,
        )
        NEW_PAPER.validate_rendered_statement_interface(
            "EX00Example", [target], rendered
        )
        NEW_PAPER.validate_rendered_proof_interface(
            "EX00Example", [target], proof_rendered
        )

    def test_plan_records_current_semantic_identity_and_planner_owned_closeout(
        self,
    ) -> None:
        plan = NEW_PAPER.formalization_plan_text("Example", "EX00Example")
        self.assertIn("## Audited Statement Skeleton", plan)
        self.assertIn("Lean semantic identity", plan)
        self.assertIn("numeric and discrete obligation partitions", plan)
        self.assertNotIn("v7 statement", plan)
        self.assertIn("`by sorry`", plan)
        self.assertIn("`<name>Spec : Prop`", plan)
        self.assertIn("`semantic_contract_template`", plan)
        self.assertIn("current source-to-Spec correspondence", plan)
        self.assertIn("proof and instance arguments", plan)
        self.assertIn("current accepted obligation graph", plan)
        self.assertNotIn("Legacy v10 evidence", plan)
        self.assertIn(
            "Signature changes after a `matches` verdict invalidate the row", plan
        )
        self.assertIn("source_model_convention", plan)
        self.assertIn("defect_or_remark_support", plan)
        self.assertIn("proof_support", plan)
        self.assertIn("## Reviewed Source Inventory Boundary", plan)
        self.assertNotIn("--bootstrap-current", plan)
        self.assertIn("single `closeout_review_policy`", plan)
        self.assertIn("source_region_partition", plan)
        self.assertIn("run_paper_closeout.py", plan)
        self.assertIn("Do not invoke", plan)
        self.assertLess(
            plan.index("Closeout readiness:"),
            plan.index("terminal closeout documents"),
        )
        self.assertIn("exact current compiled cache skips a redundant", plan)
        self.assertIn("--source-inventory-check", plan)
        self.assertIn("bounded manifest retry", plan)
        self.assertIn("let the planner schedule the required delta", plan)
        self.assertIn(
            "do not pre-run those\n      gates just to recreate an intermediate receipt",
            plan,
        )
        future_intake = json.loads(
            NEW_PAPER.source_inventory_review_config_text(
                "EX00Example", None, "EX00Example"
            )
        )
        self.assertFalse(
            future_intake["source_named_result_inventory_review"]["complete"]
        )
        self.assertEqual(future_intake["include_specs"], [])
        self.assertEqual(
            future_intake["closeout_review_policy"]["source_scope"],
            "all_named_theory",
        )
        self.assertEqual(
            future_intake["closeout_review_policy"]["repeat_final_scope"],
            "main_primary",
        )
        self.assertFalse(
            future_intake["source_named_result_inventory_review"][
                "source_region_partition"
            ]["complete"]
        )

    def test_rendered_scaffold_includes_resumable_workflow_guidance(
        self,
    ) -> None:
        args = argparse.Namespace(
            title="Example",
            authors="A. Author",
            version="arXiv v2 (2025-01-01)",
            official_url="https://example.test/paper",
            url="https://example.test/paper.pdf",
            pdf_url=None,
        )
        rendered = {
            "README": NEW_PAPER.readme_text(args, "EX00Example"),
            "planning document": NEW_PAPER.formalization_plan_text(
                "Example", "EX00Example"
            ),
            "paper interface": NEW_PAPER.paper_interface_text(
                "Example", "EX00Example", "EX00Example"
            ),
            "working notes": NEW_PAPER.notes_text(
                "Example", "EX00Example", args
            ),
        }
        disallowed = ("EconCSLib-private", "~/.codex", "/tmp/")
        for label, text in rendered.items():
            for phrase in disallowed:
                with self.subTest(rendered=label, phrase=phrase):
                    self.assertNotIn(phrase, text)
        self.assertIn("`source.pdf`", rendered["README"])
        self.assertIn("`source.txt`", rendered["README"])
        self.assertIn("Private outside-Lean proof plan", rendered["README"])
        self.assertIn("temporary private", rendered["README"])
        self.assertIn("private draft", rendered["paper interface"])
        self.assertIn("handoff", rendered["working notes"])
        self.assertIn(".review_traces", rendered["planning document"])
        self.assertIn(
            "current accepted obligation graph", rendered["planning document"]
        )
        self.assertIn(
            "FINAL_ADVERSARIAL_REVIEW_PANEL.json", rendered["README"]
        )
        self.assertNotIn("Legacy v10 evidence", rendered["planning document"])

    def test_no_spec_cli_rejects_path_namespace_and_comment_injection(self) -> None:
        base = {
            "url": "https://example.test/paper.pdf",
            "folder": "EX00Example",
            "title": "Example",
            "authors": "A. Author",
            "version": "arXiv v2",
            "official_url": None,
            "pdf_url": None,
            "namespace": "EX00Example",
            "statement_spec": None,
            "no_download": True,
            "force": True,
            "with_notes": False,
        }
        cases = [
            {"folder": "../Escape"},
            {"namespace": "EX00Example\nend EX00Example\naxiom hidden : False"},
            {"title": "Example -/\naxiom hidden : False\n/-"},
        ]
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            papers.mkdir()
            for overrides in cases:
                with self.subTest(overrides=overrides):
                    args = argparse.Namespace(**(base | overrides))
                    with (
                        mock.patch.object(NEW_PAPER, "ROOT", root),
                        mock.patch.object(NEW_PAPER, "PAPERS", papers),
                        mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                        mock.patch.object(NEW_PAPER, "refresh_review_cache"),
                    ):
                        self.assertEqual(NEW_PAPER.main(), 2)
            self.assertEqual(list(papers.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
