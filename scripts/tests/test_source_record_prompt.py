#!/usr/bin/env python3
"""Focused regressions for the source-record semantic-review prompt."""

from __future__ import annotations

import ast
import json
from pathlib import Path
import unittest

from scripts import source_record_prompt as PROMPT


ROOT = Path(__file__).resolve().parents[2]
AUDIT_PATH = ROOT / "skills/econcs-formalizer/scripts/source_record_audit.py"
PROMPT_PATH = ROOT / "scripts/source_record_prompt.py"
MOVED_NAMES = {"judge_prompt", "source_record_llm_judge_prompt"}


class SourceRecordPromptArchitectureTests(unittest.TestCase):
    def test_semantic_producer_does_not_import_presentation_authority(self) -> None:
        tree = ast.parse(AUDIT_PATH.read_text(encoding="utf-8"))
        definitions = {
            node.name
            for node in tree.body
            if isinstance(node, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))
        }
        self.assertTrue(MOVED_NAMES.isdisjoint(definitions))
        imported: set[str] = set()
        for node in tree.body:
            if (
                isinstance(node, ast.ImportFrom)
                and node.module == "scripts.source_record_prompt"
            ):
                imported.update(alias.asname or alias.name for alias in node.names)
        self.assertTrue(MOVED_NAMES.isdisjoint(imported))

    def test_prompt_authority_has_no_project_or_operational_imports(self) -> None:
        tree = ast.parse(PROMPT_PATH.read_text(encoding="utf-8"))
        imported_modules: set[str] = set()
        for node in tree.body:
            if isinstance(node, ast.ImportFrom):
                imported_modules.add(str(node.module or ""))
            elif isinstance(node, ast.Import):
                imported_modules.update(alias.name for alias in node.names)
        self.assertEqual(imported_modules, {"__future__", "json", "typing"})


class SourceRecordPromptBehaviorTests(unittest.TestCase):
    def test_context_is_literal_review_input_not_automatic_evidence(self) -> None:
        semantic_context = [{"source_quote": "literal context", "kind": "model"}]
        fidelity = {"defects": [{"claim": "proof step needs repair"}]}
        item = {"judgment_key": "claim", "lean_checked_statement": "P"}

        prompt = PROMPT.judge_prompt(
            "Fixture",
            [item],
            fidelity,
            semantic_context,
        )

        self.assertIn("Paper: Fixture", prompt)
        self.assertIn(json.dumps(semantic_context, indent=2, sort_keys=True), prompt)
        self.assertIn(json.dumps(fidelity, indent=2, sort_keys=True), prompt)
        self.assertIn(json.dumps([item], indent=2, sort_keys=True), prompt)
        self.assertIn("not theorem statements", prompt)
        self.assertIn("never by itself a validated paper/source assumption", prompt)
        self.assertIn("Do not infer anything", prompt)

    def test_payload_selection_omits_already_covered_or_dependency_boundary_rows(self) -> None:
        payload = {
            "conclusion_dependency_items": [{"judgment_key": "dependency"}],
            "statement_ledger_covered_boundary_input_keys": ["covered"],
            "boundary_input_items": [
                {"judgment_key": "covered"},
                {"judgment_key": "dependency"},
                {"judgment_key": "uncovered"},
            ],
            "type_valued_certificate_result_items": [{"judgment_key": "typed"}],
            "rows_with_semantic_inputs": [{"judgment_key": "row"}],
            "recursive_field_items": [{"judgment_key": "field"}],
            "semantic_model_items": [{"judgment_key": "model"}],
        }

        prompt = PROMPT.source_record_llm_judge_prompt("Fixture", payload)

        self.assertIn('"judgment_key": "dependency"', prompt)
        self.assertIn('"judgment_key": "uncovered"', prompt)
        self.assertIn('"judgment_key": "typed"', prompt)
        self.assertIn('"judgment_key": "row"', prompt)
        self.assertIn('"judgment_key": "field"', prompt)
        self.assertIn('"judgment_key": "model"', prompt)
        self.assertNotIn('"judgment_key": "covered"', prompt)
        self.assertEqual(prompt.count('"judgment_key": "dependency"'), 1)


if __name__ == "__main__":
    unittest.main()
