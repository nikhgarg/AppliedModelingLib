from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

from scripts.source_claim_policy import (
    USER_APPROVED_SCOPE_EXCLUSION,
    source_inventory_item_requires_proof_evidence,
)
from scripts.source_coverage_scope import USER_APPROVED_SCOPE_EXCLUSION_KEY


ROOT = Path(__file__).resolve().parents[2]


class SourceClaimPolicyTests(unittest.TestCase):
    def test_scope_exclusion_compatibility_export_uses_shared_key(self) -> None:
        self.assertEqual(
            USER_APPROVED_SCOPE_EXCLUSION,
            USER_APPROVED_SCOPE_EXCLUSION_KEY,
        )

    def test_structured_translation_and_separate_evidence_lanes_remain_nonproof(self) -> None:
        for item in (
            {"source_kind": "definition", "claim_bearing": True},
            {"source_kind": "predicate_vocabulary", "claim_bearing": True},
            {"source_kind": "assumption", "claim_bearing": True},
            {"source_kind": "model", "claim_bearing": True},
            {
                "source_kind": "lemma",
                "source_status": "support_only",
                "claim_bearing": True,
            },
            {
                "source_kind": "theorem",
                "source_status": "quarantined_source_defect",
                "claim_bearing": True,
            },
        ):
            with self.subTest(item=item):
                self.assertFalse(source_inventory_item_requires_proof_evidence(item))

    def test_results_and_ambiguous_statement_map_items_fail_closed(self) -> None:
        for item in (
            {"source_kind": "theorem"},
            {"source_kind": "claim"},
            {"source_kind": "prose_assertion", "claim_bearing": True},
            {
                "source_kind": "example",
                "claim_bearing": False,
                "statement": "An equilibrium exists for every instance.",
            },
            {"source": "audit/paper_statement_map.json"},
            None,
        ):
            with self.subTest(item=item):
                self.assertTrue(source_inventory_item_requires_proof_evidence(item))

    def test_accepting_classifier_does_not_import_dashboard(self) -> None:
        script = """
import sys
from pathlib import Path
from scripts.audit_evidence_integrity import (
    _semantic_contract_item_requires_proof_evidence,
    _semantic_contract_nonclaim_scope_error,
)
assert _semantic_contract_item_requires_proof_evidence(
    {}, 'claim', {'source_kind': 'theorem'}
) is True
assert 'claim_bearing: false is permitted' in _semantic_contract_nonclaim_scope_error(
    Path('.'),
    'formalized',
    Path('audit/paper_statement_map.json'),
    {},
    {'claim_bearing': False, 'source_scope_classification': 'invalid'},
)
assert 'scripts.review_dashboard' not in sys.modules
"""
        completed = subprocess.run(
            [sys.executable, "-c", script],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        self.assertEqual(completed.returncode, 0, completed.stderr)


if __name__ == "__main__":
    unittest.main()
