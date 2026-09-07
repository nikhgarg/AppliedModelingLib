#!/usr/bin/env python3
"""Regression tests for operational complexity-audit guidance."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path

from scripts import semantic_obligation_review as obligation_review

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "new_paper_runtime_guidance", ROOT / "scripts" / "new_paper.py"
)
assert SPEC is not None and SPEC.loader is not None
NEW_PAPER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = NEW_PAPER
SPEC.loader.exec_module(NEW_PAPER)


class RuntimeComplexityAuditGuidanceTests(unittest.TestCase):
    def test_current_runtime_validator_retains_every_strict_work_category(self) -> None:
        self.assertEqual(
            obligation_review.OPERATIONAL_COMPLEXITY_REVIEW_VERSION,
            "operational-complexity-review-v1-transitive-work-accounting",
        )
        self.assertEqual(
            obligation_review.OPERATIONAL_WORK_CATEGORIES,
            {
                "traversal_enumeration_length",
                "duplicate_multiplicity",
                "materialization_rebuilding",
                "representation_container_primitives",
                "exact_rational_bit_growth",
            },
        )
        self.assertNotIn(
            "missing", obligation_review.FULL_RUNTIME_MATCH_WORK_STATUSES
        )
        self.assertNotIn(
            "excluded_by_claim",
            obligation_review.FULL_RUNTIME_MATCH_WORK_STATUSES,
        )
        self.assertEqual(
            obligation_review.CLOSURE_ELIMINATION_EVIDENCE_KINDS,
            {"generated_ir_call_graph", "cost_threaded_executor"},
        )

    def test_generated_plan_records_runtime_evidence_and_exclusions(self) -> None:
        plan = NEW_PAPER.formalization_plan_text("Example", "EX00Example")
        self.assertIn("Algorithmic complexity audit, when applicable", plan)
        self.assertIn("Transitive operational dependency graph", plan)
        self.assertIn("every reachable branch", plan)
        self.assertIn("old semantic closure/oracle dependencies", plan)
        self.assertIn("Worst-case recurrence and bound", plan)
        self.assertIn("duplicates, and materialization/rebuild charges", plan)
        self.assertIn("missing/excluded work withholds a runtime match", plan)
        self.assertIn("artifact/source hashes and semantic binding", plan)
        self.assertIn("refinement alone is not cost evidence", plan)

    def test_skill_and_workflow_reject_name_based_runtime_evidence(self) -> None:
        skill = (ROOT / "skills" / "econcs-formalizer" / "SKILL.md").read_text(encoding="utf-8")
        architecture = (
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "references"
            / "formalization-architecture.md"
        ).read_text(encoding="utf-8")
        workflow = (ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md").read_text(
            encoding="utf-8"
        )
        self.assertIn("references/formalization-architecture.md", skill)
        guidance = " ".join(architecture.split())
        self.assertIn("transitive semantic operational", guidance)
        self.assertIn("every branch reachable", guidance)
        self.assertIn("old semantic closure or oracle", guidance)
        self.assertIn("function and declaration names", guidance)
        self.assertIn("generated IR/C", guidance)
        self.assertIn("pinned by source and artifact digests", guidance)
        self.assertIn("cost-threaded executor", guidance)
        workflow_guidance = " ".join(workflow.split())
        self.assertIn("fully expanded transparent Spec", workflow_guidance)
        self.assertIn("Never interpose a Lean-to-TeX", workflow_guidance)

    def test_skills_and_workflow_cover_semantic_fidelity_hazards(self) -> None:
        path = (
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "references"
            / "formalization-architecture.md"
        )
        guidance = " ".join(path.read_text(encoding="utf-8").split()).lower()
        for phrase in (
            "terminal",
            "nonvacu",
            "coherent",
            "nonempty",
            "surject",
            "input domain",
            "state transition",
            "termination",
            "numeric representation",
            "global bridge",
            "names are routing only",
        ):
            self.assertIn(phrase, guidance, path)


if __name__ == "__main__":
    unittest.main()
