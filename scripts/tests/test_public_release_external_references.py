"""External links must not import private proof files or inflate local counts."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from scripts import public_release_external_references as external


def fixture_reference():
    return {
        "schema": 1, "kind": "external_reference", "id": "ExampleExternal",
        "repository_visibility": "public", "title": "External Paper",
        "authors": "Example Author", "publication": "Working paper, 2026",
        "status": "formalized",
        "code": {"revision": "a" * 40, "lean_files": 2, "lean_lines": 25,
                 "counting_method": "tracked_lean_physical_lines"},
        "links": {
            "repository": "https://github.com/example/proofs",
            "report": "https://github.com/example/proofs/blob/main/REPORT.md",
            "lean_statements": "https://github.com/example/proofs/blob/main/Interface.lean",
            "theorem_index": "https://github.com/example/proofs/blob/main/THEOREMS.md",
        },
    }


class ExternalReferenceTests(unittest.TestCase):
    def test_reference_folder_cannot_carry_proofs_status_or_private_notes(self):
        reference = external.validate_reference(fixture_reference(), "ExampleExternal")
        paths = {"papers/ExampleExternal/external.json", "papers/ExampleExternal/README.md"}
        readme = external.render_readme(reference)
        external.validate_reference_folder(reference, paths, readme)
        for extra in ("papers/ExampleExternal/Main.lean", "papers/ExampleExternal/status.json",
                      "papers/ExampleExternal/private.md", "papers/ExampleExternal.lean"):
            with self.subTest(extra=extra), self.assertRaisesRegex(ValueError, "permits only"):
                external.validate_reference_folder(reference, paths | {extra}, readme)

    def test_invalid_links_and_unpinned_counts_are_rejected(self):
        for field, value in (("repository_visibility", "private_only"),
                             ("kind", "formalization"), ("id", "Other")):
            reference = fixture_reference()
            reference[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                external.validate_reference(reference, "ExampleExternal")
        for key, value in (("report", "javascript:alert(1)"),
                           ("lean_statements", "https://example.org/private")):
            reference = fixture_reference()
            reference["links"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                external.validate_reference(reference, "ExampleExternal")
        for key, value in (("revision", "main"), ("lean_lines", True), ("lean_lines", -1)):
            reference = fixture_reference()
            reference["code"][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                external.validate_reference(reference, "ExampleExternal")

    def test_rendered_totals_count_external_code_exactly_once(self):
        original = ('<p class="project-stats">Currently, the project contains 2 formalized papers'
                    ' and 1 partially formalized paper, with 1,000 total lines of Lean code.</p>'
                    '<table><tbody>\n' + external.PAPER_ROWS_END + '\n</tbody></table>')
        refs = [fixture_reference()]
        stored = external.render_index(original, refs)
        self.assertIn("1,000 total", stored)
        self.assertIn('<td>25</td>', stored)
        self.assertIn("Reference folder", stored)
        rendered = external.render_index(stored, refs, include_totals=True)
        self.assertIn("3 formalized papers and 1 partially formalized paper", rendered)
        self.assertIn("1,025 total", rendered)
        self.assertEqual(rendered, external.render_index(rendered, refs, include_totals=True))
        updated = copy.deepcopy(refs)
        updated[0]["code"]["lean_lines"] = 40
        self.assertIn("1,040 total", external.render_index(rendered, updated, include_totals=True))
        removed = external.render_index(rendered, [], include_totals=True)
        self.assertIn("1,000 total", removed)
        self.assertNotIn('data-external-reference=', removed)

    def test_only_tracked_reference_manifests_are_loaded(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            folder = root / "papers/ExampleExternal"
            folder.mkdir(parents=True)
            reference = fixture_reference()
            (folder / "external.json").write_text(json.dumps(reference))
            (folder / "README.md").write_text(external.render_readme(reference))
            self.assertEqual(external.load_references(root, set()), [])
            paths = {"papers/ExampleExternal/external.json", "papers/ExampleExternal/README.md"}
            self.assertEqual(external.load_references(root, paths), [reference])
            with self.assertRaisesRegex(ValueError, "permits only"):
                external.load_references(root, paths | {"papers/ExampleExternal/status.json"},
                                         check_readmes=False)
            (folder / "README.md").write_text("Private notes")
            with self.assertRaisesRegex(ValueError, "out of sync"):
                external.load_references(root, paths)


if __name__ == "__main__":
    unittest.main()
