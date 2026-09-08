"""File-contract checks follow the configured proof owner without weakening it."""

import json
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from unittest.mock import patch

from scripts import audit_repository as audit


class PaperFileContractTests(unittest.TestCase):
    def setUp(self):
        self.stack = ExitStack()
        self.addCleanup(self.stack.close)
        self.root = Path(self.stack.enter_context(tempfile.TemporaryDirectory()))
        self.folder = self.root / "papers" / "AB24Example"
        self.folder.mkdir(parents=True)
        self.folder.with_suffix(".lean").write_text("", encoding="utf-8")
        (self.folder / "PaperInterface.lean").write_text("", encoding="utf-8")
        (self.folder / ".gitignore").write_text(
            "\n".join(sorted(audit.REQUIRED_GITIGNORE_PATTERNS)), encoding="utf-8"
        )
        self.status({})
        for name, value in [("ROOT", self.root), ("PAPERS", self.root / "papers")]:
            self.stack.enter_context(patch.object(audit, name, value))
        self.stack.enter_context(patch.object(audit, "paper_dirs", return_value=[self.folder]))
        self.stack.enter_context(patch.object(audit, "has_source_pdf", return_value=True))
        self.stack.enter_context(patch.object(audit, "has_text_cache", return_value=True))

    def status(self, surface):
        (self.folder / "status.json").write_text(
            json.dumps({"review_surface": surface}), encoding="utf-8"
        )

    def errors(self):
        return [f.message for f in audit.check_paper_contract(True) if f.severity == "ERROR"]

    def test_legacy_paper_requires_main_theorems(self):
        self.assertTrue(any("MainTheorems.lean" in e for e in self.errors()))
        (self.folder / "MainTheorems.lean").write_text("", encoding="utf-8")
        self.assertEqual(self.errors(), [])

    def test_configured_owner_replaces_legacy_filename(self):
        self.status({"proof_file": "papers/AB24Example/ProofInterface.lean"})
        (self.folder / "ProofInterface.lean").write_text("", encoding="utf-8")
        self.assertEqual(self.errors(), [])

    def test_legacy_file_cannot_hide_missing_configured_owner(self):
        self.status({"proof_file": "papers/AB24Example/ProofInterface.lean"})
        (self.folder / "MainTheorems.lean").write_text("", encoding="utf-8")
        self.assertTrue(any("ProofInterface.lean" in e for e in self.errors()))

    def test_configured_owner_must_be_a_file(self):
        self.status({"proof_file": "papers/AB24Example/ProofInterface.lean"})
        (self.folder / "ProofInterface.lean").mkdir()
        self.assertTrue(any("ProofInterface.lean" in e for e in self.errors()))

    def test_blank_or_invalid_owner_preserves_legacy_requirement(self):
        for value in ["", "  ", None, [], 42]:
            with self.subTest(value=value):
                self.status({"proof_file": value})
                self.assertTrue(any("MainTheorems.lean" in e for e in self.errors()))


class ReviewPresentationContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.status_file = self.root / "status.json"
        self.interface = "\n".join(f"def helper{i} : Nat := 0" for i in range(100))
        self.interface += "\ndef claimSpec : Prop := True\ndef assumption : Prop := True\n"

    def test_only_selected_claims_and_assumptions_count_toward_slice_size(self):
        surface = {"include_names": ["claimSpec"], "assumption_names": ["assumption"]}
        rows = audit.configured_review_rows(self.interface, surface)
        self.assertEqual([name for _, name in rows], ["claimSpec", "assumption"])
        surface["auxiliary_names"] = ["assumption"]
        self.assertEqual([name for _, name in audit.configured_review_rows(self.interface, surface)], ["claimSpec"])
        self.assertEqual(len(audit.configured_review_rows(self.interface, {})), 102)

    def test_slice_counts_use_the_same_selected_surface(self):
        self.status_file.write_text(json.dumps({"review_surface": {
            "include_names": ["claimSpec"],
            "slices": [{"id": "claim", "names": ["claimSpec"]}],
        }}), encoding="utf-8")
        self.assertEqual(audit.review_surface_slice_counts(self.interface, self.status_file), ([], {"claim": 1}))

    def test_invalid_slice_regex_still_blocks(self):
        self.status_file.write_text(json.dumps({"review_surface": {
            "include_names": ["claimSpec"],
            "slices": [{"id": "claim", "name_regex": "["}],
        }}), encoding="utf-8")
        errors, _ = audit.review_surface_slice_counts(self.interface, self.status_file)
        self.assertTrue(any("invalid `name_regex`" in error for error in errors))

    def test_docs_index_accepts_current_and_legacy_section_titles(self):
        (self.root / "README.md").write_text("# Project\n", encoding="utf-8")
        docs = self.root / "docs"
        docs.mkdir()
        pairs = [
            ("Human-Facing", "Agent And Maintainer-Facing"),
            ("Reading and reviewing a formalization", "Maintaining the website and releases"),
        ]
        with patch.object(audit, "ROOT", self.root):
            for reader, maintainer in pairs:
                with self.subTest(reader=reader):
                    (docs / "README.md").write_text(f"## {reader}\n\n## {maintainer}\n", encoding="utf-8")
                    self.assertEqual(audit.check_human_facing_readme(), [])
                    for heading in [reader, maintainer]:
                        (docs / "README.md").write_text(f"## {heading}\n", encoding="utf-8")
                        self.assertTrue(any(f.severity == "ERROR" for f in audit.check_human_facing_readme()))


if __name__ == "__main__":
    unittest.main()
