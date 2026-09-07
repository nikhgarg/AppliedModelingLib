"""Keep planner refresh decisions consistent with both real ledger writers."""

import json
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
import unittest

from scripts import reissue_library_semantic_review as library
from scripts import reissue_paper_semantic_prerequisites as paper


class PrerequisiteStructuralRefreshTests(unittest.TestCase):
    def exercise(self, module, lane, *, changed_anchor=False):
        with TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Paper"
            ledger_path = folder / module.LEDGER_RELATIVE
            ledger_path.parent.mkdir(parents=True)
            name = "Paper.Model"
            declaration = f"{lane}_declaration"
            code_digest = "paper_declaration_sha256" if lane == "paper" else "library_definition_sha256"
            protocol = paper.PAPER_PREREQUISITE_TARGET_PROTOCOL if lane == "paper" else library.TARGET_PROTOCOL
            reviewer = {
                "judgment": "matches", "reason": "The exact source and Lean model agree.",
                "validator": "Independent reviewer", "validator_type": "llm_as_judge",
                "validated_at": "2026-09-05T00:00:00Z",
            }
            prior = {
                declaration: name, "source_item": "definition",
                f"{lane}_semantic_target_protocol": protocol,
                "elaborated_signature_sha256": "a" * 64,
                "source_input_bundle_sha256": "b" * 64,
                "source_anchor_bundle_sha256": "c" * 64,
                code_digest: "d" * 64,
                f"{lane}_semantic_target_sha256": "e" * 64,
                **reviewer,
            }
            ledger_path.write_text(json.dumps({"items": {name: prior}}))
            entry = {
                **prior, "lean_name": name, "semantic_current": True,
                "source_input_bundle_sha256": "f" * 64,
                "source_anchor_bundle_sha256": ("9" if changed_anchor else "c") * 64,
                f"{lane}_source_path": "papers/Paper/Model.lean",
                f"{lane}_line_start": 1, f"{lane}_line_end": 1,
                f"{lane}_declaration_source": "def Model : Prop := True",
                "library_definition": "def Model : Prop := True",
                f"{lane}_semantic_target": "Prop",
                "verbatim_source_input": "Definition. The model holds.",
                "source_locator": "source.txt:1",
            }
            source_map = {
                "semantic_route_schema": 2,
                "items": {"definition": {
                    "source_kind": "definition", "inventory_role": "source_semantic_declaration",
                    "claim_bearing": True, "lean_declarations": [name],
                }},
                f"{lane}_semantic_prerequisite_sources": {name: "definition"},
            }
            graph = SimpleNamespace(
                context=SimpleNamespace(statement_map=source_map), specifications=[],
                semantic_targets={}, paper_prerequisite_targets={name: {}} if lane == "paper" else {},
                library_semantic_targets={name: {}} if lane == "library" else {},
                paper_prerequisite_review_support=lambda _roots: ({}, {name: ()}, {name: ""}),
                project_paper_prerequisites=lambda *_args, **_kwargs: [entry],
                project_library_prerequisites=lambda *_args, **_kwargs: [entry],
            )
            if changed_anchor:
                error = paper.PaperPrerequisiteReissueError if lane == "paper" else library.LibraryReviewReissueError
                with self.assertRaises(error):
                    module.current_structural_refresh_required(folder, review_graph=graph)
                self.assertEqual(json.loads(ledger_path.read_text())["items"][name], prior)
                return
            self.assertIsNotNone(module._unchanged_semantic_judgment(prior, entry))
            self.assertTrue(module.current_structural_refresh_required(folder, review_graph=graph))
            refreshed = module.reissue(folder, {}, validator="", review_graph=graph)
            row = refreshed["items"][name]
            self.assertEqual(row["source_input_bundle_sha256"], "f" * 64)
            for field, value in reviewer.items():
                self.assertEqual(row[field], value)
            ledger_path.write_text(json.dumps(refreshed))
            self.assertFalse(module.current_structural_refresh_required(folder, review_graph=graph))

    def test_paper_context_rebind_refreshes_once_without_review(self):
        self.exercise(paper, "paper")

    def test_library_context_rebind_refreshes_once_without_review(self):
        self.exercise(library, "library")

    def test_paper_changed_source_cannot_be_refreshed_without_review(self):
        self.exercise(paper, "paper", changed_anchor=True)

    def test_library_changed_source_cannot_be_refreshed_without_review(self):
        self.exercise(library, "library", changed_anchor=True)


if __name__ == "__main__":
    unittest.main()
