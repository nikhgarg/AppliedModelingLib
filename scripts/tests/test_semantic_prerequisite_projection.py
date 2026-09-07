#!/usr/bin/env python3
"""Strict prerequisite projection regressions."""

from __future__ import annotations

import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import review_dashboard  # noqa: E402
from scripts.semantic_prerequisite_projection import (  # noqa: E402
    LIBRARY_SEMANTIC_REVIEW_SCHEMA,
    LIBRARY_SEMANTIC_TARGET_PROTOCOL,
    PAPER_PREREQUISITE_PROMPT_VERSION,
    PAPER_PREREQUISITE_SCHEMA,
    PAPER_PREREQUISITE_TARGET_PROTOCOL,
    REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
    lean_graph_library_declaration_sources,
    project_library_semantic_prerequisites,
    project_paper_semantic_prerequisites,
    selected_library_semantic_prerequisite_targets,
)
from scripts.corrected_target_identity import (  # noqa: E402
    CORRECTED_TARGET_REVIEW_PROTOCOL,
    corrected_target_review_digest,
)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


class SemanticPrerequisiteProjectionTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.paper = self.root / "FixturePaper"
        self.paper.mkdir()
        self.source_path = self.paper / "source.txt"
        self.source_text = "The source mathematical definition."
        self.source_path.write_text(self.source_text + "\n", encoding="utf-8")
        self.anchor = {
            "path": "source.txt",
            "line_start": 1,
            "line_end": 1,
            "quoted_text": self.source_text,
            "quoted_text_sha256": digest(self.source_text),
        }
        self.source_map = {
            "items": {
                "definition": {
                    "source_location": "Definition 1",
                    "source_anchor_evidence": [self.anchor],
                }
            }
        }
        self.frozen = {self.source_path: self.source_path.read_bytes()}

    def paper_inputs(self) -> dict[str, object]:
        name = "FixturePaper.Model"
        declaration = "def Model : Prop := True"
        target = "def Model : Prop := True"
        identity = digest("elaborated Model")
        source_bundle = review_dashboard.source_semantic_input_bundle(
            self.source_map["items"]["definition"],  # type: ignore[index]
            require_context_roles=True,
        )[1]
        return {
            "name": name,
            "claim_targets": {
                "FixturePaper.ResultSpec": {
                    "prerequisite_declarations": [name]
                }
            },
            "targets": {
                name: {
                    "display": target,
                    "display_sha256": digest(target),
                    "elaborated_signature_sha256": identity,
                    "declaration_kind": "definition",
                    "root_expanded": True,
                    "direct_paper_declarations": [],
                    "direct_library_declarations": ["AppliedModelingLib.Fixture.Primitive"],
                }
            },
            "declarations": {
                name: {
                    "paper_declaration": name,
                    "paper_declaration_source": declaration,
                    "paper_declaration_sha256": digest(declaration),
                    "paper_source_path": "papers/FixturePaper/PaperInterface.lean",
                    "paper_line_start": 1,
                }
            },
            "ledger": {
                "schema": PAPER_PREREQUISITE_SCHEMA,
                "paper": self.paper.name,
                "prompt_version": PAPER_PREREQUISITE_PROMPT_VERSION,
                "target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                "items": {
                    name: {
                        "paper_declaration": name,
                        "paper_declaration_sha256": digest(declaration),
                        "elaborated_signature_sha256": identity,
                        "paper_semantic_target_protocol": PAPER_PREREQUISITE_TARGET_PROTOCOL,
                        "paper_semantic_target_sha256": digest(target),
                        "source_item": "definition",
                        "source_input_bundle_sha256": source_bundle,
                        "judgment": "matches",
                        "reason": "The exact source and expanded declaration agree.",
                        "validator": "independent reviewer",
                        "validator_type": "llm_as_judge",
                        "validated_at": "2026-08-27T00:00:00Z",
                    }
                },
            },
        }

    def library_inputs(self) -> dict[str, object]:
        name = "AppliedModelingLib.Fixture.Primitive"
        definition = "def Primitive : Prop := True"
        target = "def Primitive : Prop := True"
        identity = digest("elaborated Primitive")
        source_bundle = review_dashboard.source_semantic_input_bundle(
            self.source_map["items"]["definition"],  # type: ignore[index]
            require_context_roles=True,
        )[1]
        return {
            "name": name,
            "targets": {
                name: {
                    "display": target,
                    "display_sha256": digest(target),
                    "elaborated_signature_sha256": identity,
                    "declaration_kind": "definition",
                    "direct_library_declarations": [],
                }
            },
            "declarations": {
                name: {
                    "library_definition": definition,
                    "library_definition_sha256": digest(definition),
                    "library_definition_error": "",
                    "library_source_path": "AppliedModelingLib/Fixture.lean",
                    "library_line_start": 1,
                    "library_line_end": 1,
                }
            },
            "ledger": {
                "schema": LIBRARY_SEMANTIC_REVIEW_SCHEMA,
                "paper": self.paper.name,
                "prompt_version": REQUIRED_LLM_LIBRARY_SEMANTIC_REVIEW_PROMPT_VERSION,
                "target_protocol": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
                "items": {
                    name: {
                        "library_declaration": name,
                        "library_definition_sha256": digest(definition),
                        "elaborated_signature_sha256": identity,
                        "library_semantic_target_protocol": LIBRARY_SEMANTIC_TARGET_PROTOCOL,
                        "library_semantic_target_sha256": digest(target),
                        "library_source_path": "AppliedModelingLib/Fixture.lean",
                        "source_item": "definition",
                        "source_input_bundle_sha256": source_bundle,
                        "judgment": "matches",
                        "reason": "The exact source and expanded declaration agree.",
                        "validator": "independent reviewer",
                        "validator_type": "llm_as_judge",
                        "validated_at": "2026-08-27T00:00:00Z",
                    }
                },
            },
        }

    def test_paper_projection_exposes_acceptance_fields(self) -> None:
        inputs = self.paper_inputs()
        current = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertEqual(len(current), 1)
        self.assertTrue(current[0]["semantic_current"])
        for field in (
            "lean_name",
            "paper_declaration_sha256",
            "paper_semantic_target_sha256",
            "elaborated_signature_sha256",
            "source_input_bundle_sha256",
            "semantic_judgment",
            "semantic_current",
            "semantic_status",
            "direct_library_declarations",
        ):
            self.assertIn(field, current[0])

    def test_current_library_frontier_keeps_only_explicit_source_roots(self) -> None:
        """Lean keeps helpers in the graph; source review does not invent rows."""

        root = "AppliedModelingLib.Fixture.SourceModel"
        helper = "AppliedModelingLib.Fixture.ProofHelper"
        source_map = {
            "semantic_route_schema": 2,
            "items": {
                "model": {
                    "source_kind": "definition",
                    "claim_bearing": True,
                    "inventory_role": "source_semantic_declaration",
                    "lean_declarations": [root],
                }
            },
            "library_semantic_prerequisite_sources": {root: "model"},
        }
        targets = {
            root: {"direct_library_declarations": [helper]},
            helper: {"direct_library_declarations": []},
        }

        self.assertEqual(
            selected_library_semantic_prerequisite_targets(source_map, targets),
            {root: targets[root]},
        )

    def test_paper_projection_does_not_reopen_on_reviewer_context_change(self) -> None:
        inputs = self.paper_inputs()
        name = str(inputs["name"])
        support_digest = digest("Lean-produced transitive reviewer support")

        current = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
            supporting_declarations_sha256_by_name={name: support_digest},
        )
        self.assertTrue(current[0]["semantic_current"])
        self.assertEqual(
            current[0]["semantic_supporting_declarations_sha256"], support_digest
        )

    def test_paper_projection_accepts_only_a_current_approved_correction(self) -> None:
        """A correction is distinct from raw source matching and stays pinned."""

        inputs = self.paper_inputs()
        name = str(inputs["name"])
        corrected = {
            "statement": "The approved corrected mathematical definition.",
            "archival_equivalence_claimed": False,
        }
        corrected["corrected_target_review_sha256"] = (
            corrected_target_review_digest(corrected)
        )
        self.source_map["items"]["definition"].update(  # type: ignore[index]
            {
                "coverage_status": "corrected_source_statement",
                "corrected_target": corrected,
            }
        )
        row = inputs["ledger"]["items"][name]  # type: ignore[index]
        row.update(
            {
                "judgment": "matches_approved_corrected_target",
                "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
                "corrected_target_review_sha256": corrected[
                    "corrected_target_review_sha256"
                ],
            }
        )
        kwargs = {
            "claim_semantic_targets": inputs["claim_targets"],
            "prerequisite_semantic_targets": inputs["targets"],
            "declaration_sources": inputs["declarations"],
            "source_map": self.source_map,
            "ledger": inputs["ledger"],
            "repository_root": self.root,
            "file_bytes_override": self.frozen,
        }
        current = project_paper_semantic_prerequisites(
            self.paper, **kwargs  # type: ignore[arg-type]
        )
        self.assertTrue(current[0]["semantic_current"])

        corrected["statement"] = "A different corrected mathematical definition."
        corrected["corrected_target_review_sha256"] = (
            corrected_target_review_digest(corrected)
        )
        stale = project_paper_semantic_prerequisites(
            self.paper, **kwargs  # type: ignore[arg-type]
        )
        self.assertFalse(stale[0]["semantic_current"])

    def test_library_projection_needs_no_dashboard_registry_entry(self) -> None:
        inputs = self.library_inputs()
        current = project_library_semantic_prerequisites(
            self.paper,
            semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            semantic_target_errors={},
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertEqual([row["lean_name"] for row in current], [inputs["name"]])
        self.assertTrue(current[0]["semantic_current"])
        self.assertEqual(current[0]["semantic_judgment"], "matches")

    def test_library_projection_rejects_archival_match_for_corrected_source(self) -> None:
        """Library and paper-local rows share correction-target semantics."""

        inputs = self.library_inputs()
        name = str(inputs["name"])
        corrected = {
            "statement": "The approved corrected mathematical definition.",
            "archival_equivalence_claimed": False,
        }
        corrected["corrected_target_review_sha256"] = (
            corrected_target_review_digest(corrected)
        )
        self.source_map["items"]["definition"].update(  # type: ignore[index]
            {
                "coverage_status": "corrected_source_statement",
                "corrected_target": corrected,
            }
        )
        row = inputs["ledger"]["items"][name]  # type: ignore[index]
        stale = project_library_semantic_prerequisites(
            self.paper,
            semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            semantic_target_errors={},
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertFalse(stale[0]["semantic_current"])

        row.update(
            {
                "judgment": "matches_approved_corrected_target",
                "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
                "corrected_target_review_sha256": corrected[
                    "corrected_target_review_sha256"
                ],
            }
        )
        current = project_library_semantic_prerequisites(
            self.paper,
            semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            semantic_target_errors={},
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertTrue(current[0]["semantic_current"])
        self.assertEqual(
            current[0]["semantic_judgment"], "matches_approved_corrected_target"
        )

    def test_paper_projection_reuses_a_unique_semantic_rename_without_rewrite(
        self,
    ) -> None:
        inputs = self.paper_inputs()
        old_name = str(inputs["name"])
        new_name = "AppliedModeling.Fixture.Model"
        target = inputs["targets"].pop(old_name)  # type: ignore[union-attr]
        declaration = inputs["declarations"].pop(old_name)  # type: ignore[union-attr]
        declaration["paper_declaration"] = new_name  # type: ignore[index]
        declaration["paper_source_path"] = "AppliedModeling/Fixture.lean"  # type: ignore[index]
        declaration["paper_line_start"] = 19  # type: ignore[index]
        inputs["targets"][new_name] = target  # type: ignore[index]
        inputs["declarations"][new_name] = declaration  # type: ignore[index]
        inputs["claim_targets"]["FixturePaper.ResultSpec"][  # type: ignore[index]
            "prerequisite_declarations"
        ] = [new_name]

        rows = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )

        self.assertEqual([row["lean_name"] for row in rows], [new_name])
        self.assertTrue(rows[0]["semantic_current"])
        self.assertEqual(rows[0]["paper_source_path"], "AppliedModeling/Fixture.lean")

    def test_library_projection_reuses_a_unique_semantic_rename_without_rewrite(
        self,
    ) -> None:
        inputs = self.library_inputs()
        old_name = str(inputs["name"])
        new_name = "AppliedModeling.Fixture.Primitive"
        target = inputs["targets"].pop(old_name)  # type: ignore[union-attr]
        declaration = inputs["declarations"].pop(old_name)  # type: ignore[union-attr]
        declaration["library_source_path"] = "AppliedModeling/Fixture.lean"  # type: ignore[index]
        declaration["library_line_start"] = 23  # type: ignore[index]
        declaration["library_line_end"] = 23  # type: ignore[index]
        inputs["targets"][new_name] = target  # type: ignore[index]
        inputs["declarations"][new_name] = declaration  # type: ignore[index]

        rows = project_library_semantic_prerequisites(
            self.paper,
            semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            semantic_target_errors={},
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )

        self.assertEqual([row["lean_name"] for row in rows], [new_name])
        self.assertTrue(rows[0]["semantic_current"])
        self.assertEqual(rows[0]["library_source_path"], "AppliedModeling/Fixture.lean")

    def test_projection_refuses_an_ambiguous_semantic_rename(self) -> None:
        inputs = self.paper_inputs()
        old_name = str(inputs["name"])
        target = inputs["targets"].pop(old_name)  # type: ignore[union-attr]
        declaration = inputs["declarations"].pop(old_name)  # type: ignore[union-attr]
        new_names = ("AppliedModeling.Fixture.First", "AppliedModeling.Fixture.Second")
        inputs["claim_targets"]["FixturePaper.ResultSpec"][  # type: ignore[index]
            "prerequisite_declarations"
        ] = list(new_names)
        for new_name in new_names:
            inputs["targets"][new_name] = dict(target)  # type: ignore[index,arg-type]
            inputs["declarations"][new_name] = {  # type: ignore[index]
                **declaration,  # type: ignore[arg-type]
                "paper_declaration": new_name,
            }

        rows = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )

        self.assertEqual(len(rows), 2)
        self.assertTrue(all(row["semantic_current"] is False for row in rows))

    def test_lean_graph_coordinates_own_current_library_source_projection(self) -> None:
        library_path = self.root / "AppliedModelingLib" / "Fixture.lean"
        library_path.parent.mkdir()
        definition = "def Primitive : Prop := True"
        library_path.write_text(
            "namespace AppliedModelingLib.Fixture\n" + definition + "\nend AppliedModelingLib.Fixture\n",
            encoding="utf-8",
        )
        name = "AppliedModelingLib.Fixture.Primitive"
        targets = {
            name: {
                "review_owner_declaration": name,
                "source_module": "AppliedModelingLib.Fixture",
                "source_line_start": 2,
                "source_column_start": 0,
                "source_line_end": 2,
                "source_column_end": len(definition),
            }
        }
        frozen = {library_path.resolve(): library_path.read_bytes()}

        sources = lean_graph_library_declaration_sources(
            self.root,
            semantic_targets=targets,
            semantic_target_errors={},
            file_bytes_override=frozen,
        )

        self.assertEqual(sources[name]["library_definition"], definition)
        self.assertEqual(
            sources[name]["library_definition_sha256"], digest(definition)
        )
        self.assertEqual(
            sources[name]["library_source_path"], "AppliedModelingLib/Fixture.lean"
        )
        self.assertEqual(sources[name]["library_definition_error"], "")

        missing_snapshot = lean_graph_library_declaration_sources(
            self.root,
            semantic_targets=targets,
            semantic_target_errors={},
            file_bytes_override={},
        )
        self.assertIn(
            "absent from the frozen graph snapshot",
            missing_snapshot[name]["library_definition_error"],
        )

        targets[name]["review_owner_declaration"] = "AppliedModelingLib.Fixture.Other"
        rejected = lean_graph_library_declaration_sources(
            self.root,
            semantic_targets=targets,
            semantic_target_errors={},
            file_bytes_override=frozen,
        )
        self.assertIn(
            "no exact source-presented owner",
            rejected[name]["library_definition_error"],
        )

    def test_legacy_row_reuses_exact_reviewed_target_not_source_navigation(self) -> None:
        """An old row remains current when its exact judged Lean display is unchanged."""

        inputs = self.paper_inputs()
        name = str(inputs["name"])
        raw = inputs["ledger"]["items"][name]  # type: ignore[index]
        raw.pop("elaborated_signature_sha256")
        raw["paper_declaration_sha256"] = "0" * 64
        current = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertTrue(current[0]["semantic_current"])

        inputs["targets"][name]["display"] = "def Model : Prop := False"  # type: ignore[index]
        inputs["targets"][name]["display_sha256"] = digest(  # type: ignore[index]
            "def Model : Prop := False"
        )
        changed = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertFalse(changed[0]["semantic_current"])

    def test_library_legacy_row_uses_the_same_exact_target_rule(self) -> None:
        inputs = self.library_inputs()
        name = str(inputs["name"])
        raw = inputs["ledger"]["items"][name]  # type: ignore[index]
        raw.pop("elaborated_signature_sha256")
        raw["library_definition_sha256"] = "0" * 64
        current = project_library_semantic_prerequisites(
            self.paper,
            semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            semantic_target_errors={},
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertTrue(current[0]["semantic_current"])

    def test_recorded_signature_mismatch_cannot_fall_back_to_target_digest(self) -> None:
        inputs = self.paper_inputs()
        name = str(inputs["name"])
        inputs["ledger"]["items"][name]["elaborated_signature_sha256"] = (  # type: ignore[index]
            "f" * 64
        )
        rows = project_paper_semantic_prerequisites(
            self.paper,
            claim_semantic_targets=inputs["claim_targets"],  # type: ignore[arg-type]
            prerequisite_semantic_targets=inputs["targets"],  # type: ignore[arg-type]
            declaration_sources=inputs["declarations"],  # type: ignore[arg-type]
            source_map=self.source_map,
            ledger=inputs["ledger"],  # type: ignore[arg-type]
            repository_root=self.root,
            file_bytes_override=self.frozen,
        )
        self.assertFalse(rows[0]["semantic_current"])

    def test_frozen_bytes_are_atomic_and_missing_snapshot_fails_closed(self) -> None:
        inputs = self.paper_inputs()
        self.source_path.write_text("mutated after freeze\n", encoding="utf-8")
        kwargs = {
            "claim_semantic_targets": inputs["claim_targets"],
            "prerequisite_semantic_targets": inputs["targets"],
            "declaration_sources": inputs["declarations"],
            "source_map": self.source_map,
            "ledger": inputs["ledger"],
            "repository_root": self.root,
        }
        frozen = project_paper_semantic_prerequisites(
            self.paper,
            **kwargs,  # type: ignore[arg-type]
            file_bytes_override=self.frozen,
        )
        live = project_paper_semantic_prerequisites(
            self.paper,
            **kwargs,  # type: ignore[arg-type]
            file_bytes_override=None,
        )
        missing = project_paper_semantic_prerequisites(
            self.paper,
            **kwargs,  # type: ignore[arg-type]
            file_bytes_override={},
        )
        self.assertTrue(frozen[0]["semantic_current"])
        self.assertFalse(live[0]["semantic_current"])
        self.assertIn("quote does not equal", live[0]["source_connection_error"])
        self.assertFalse(missing[0]["semantic_current"])
        self.assertIn("absent from the frozen transaction", missing[0]["source_connection_error"])

    def test_accepting_module_imports_no_dashboard_or_packet(self) -> None:
        code = (
            "import sys\n"
            "import scripts.semantic_prerequisite_projection\n"
            "assert 'scripts.review_dashboard' not in sys.modules\n"
            "assert 'scripts.review_dashboard_packet' not in sys.modules\n"
        )
        result = subprocess.run(
            [sys.executable, "-c", code],
            cwd=ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
