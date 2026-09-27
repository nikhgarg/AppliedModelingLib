"""Published reports must remain readable and navigable under a project URL."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from build_public_site import build


@unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required")
class PublishedReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        subprocess.run(["git", "init", "-q", str(self.repo)], check=True)
        self.write("site/styles/site.css", "body { color: black; }")
        self.write("site/index.html", '<html><body><a href="https://github.com/nikhgarg/EconCSLib/blob/main/papers/Example/FINAL_VALIDATION_REPORT.md" data-local-artifact-href="/artifacts/papers/Example/FINAL_VALIDATION_REPORT.md">Report</a></body></html>')
        self.write("papers/Example/status.json", json.dumps({"repository_visibility": "public"}))
        self.write("papers/Example/FINAL_VALIDATION_REPORT.md", """# Report

<!-- BEGIN GENERATED -->
| Result | Status |
|---|---|
| Theorem 1 | Exact |

[Memo](docs/CLARIFICATIONS.md#6-extra-assumptions)
[PDF](docs/DependencyDAG.pdf)
[Lean](PaperInterface.lean#L2)
[Remote memo](https://github.com/nikhgarg/EconCSLib/blob/main/papers/Example/docs/CLARIFICATIONS.md#6-extra-assumptions)

The result is $x^2 > 0$.
<!-- END GENERATED -->
""")
        self.write("papers/Example/docs/CLARIFICATIONS.md", "# Memo\n\n## 6. Extra Assumptions\n\n[Report](../FINAL_VALIDATION_REPORT.md)\n")
        self.write("papers/Example/docs/DependencyDAG.pdf", "%PDF-1.7\n")
        self.write("papers/Example/PaperInterface.lean", "-- Public Lean statements\n")
        self.write("papers/Private/status.json", json.dumps({"repository_visibility": "private_only"}))
        self.write("papers/Private/FINAL_VALIDATION_REPORT.md", "# Private report\n")
        subprocess.run(["git", "-C", str(self.repo), "add", "site", "papers"], check=True)
        self.write("papers/Example/local-notes.md", "# Untracked notes\n")

    def write(self, name, value):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def test_published_report_math_tables_and_nested_navigation(self):
        output = self.root / "output"
        result = build(self.repo, output)
        self.assertEqual(result, {"public_papers": 1, "documents": 2, "assets": 1})
        index = (output / "index.html").read_text()
        self.assertIn('href="/AppliedModelingLib/artifacts/papers/Example/FINAL_VALIDATION_REPORT.html"', index)
        self.assertNotIn("data-local-artifact-href", index)
        report = (output / "artifacts/papers/Example/FINAL_VALIDATION_REPORT.html").read_text()
        self.assertIn("<table>", report)
        self.assertIn("<math", report)
        self.assertNotIn("BEGIN GENERATED", report)
        self.assertIn('href="/AppliedModelingLib/styles/site.css"', report)
        self.assertEqual(report.count('href="/AppliedModelingLib/artifacts/papers/Example/docs/CLARIFICATIONS.html#6-extra-assumptions"'), 2)
        self.assertIn('href="https://github.com/nikhgarg/AppliedModelingLib/blob/main/papers/Example/PaperInterface.lean#L2"', report)
        self.assertIn('href="https://github.com/nikhgarg/AppliedModelingLib/blob/main/papers/Example/FINAL_VALIDATION_REPORT.md">Markdown source', report)
        memo = (output / "artifacts/papers/Example/docs/CLARIFICATIONS.html").read_text()
        self.assertIn('id="6-extra-assumptions"', memo)
        self.assertIn('href="/AppliedModelingLib/artifacts/papers/Example/FINAL_VALIDATION_REPORT.html"', memo)
        self.assertEqual((output / "artifacts/papers/Example/docs/DependencyDAG.pdf").read_bytes(), b"%PDF-1.7\n")
        self.assertFalse((output / "artifacts/papers/Private").exists())
        self.assertFalse((output / "artifacts/papers/Example/local-notes.html").exists())

    def test_unpublished_landing_link_stops_deployment(self):
        self.write("site/index.html", '<a href="#" data-local-artifact-href="/artifacts/papers/Private/FINAL_VALIDATION_REPORT.md">Report</a>')
        with self.assertRaisesRegex(ValueError, "unpublished artifact"):
            build(self.repo, self.root / "output")

    def test_external_reference_renders_links_and_combined_code_without_private_files(self):
        from scripts.public_release_external_references import render_readme, PAPER_ROWS_END
        from scripts.tests.test_public_release_external_references import fixture_reference
        reference = fixture_reference()
        self.write("papers/ExampleExternal/external.json", json.dumps(reference))
        self.write("papers/ExampleExternal/README.md", render_readme(reference))
        self.write("site/index.html", '<p class="project-stats">Currently, the project contains '
                   '1 formalized papers, with 100 total lines of Lean code.</p>'
                   '<table><tbody>\n' + PAPER_ROWS_END + '\n</tbody></table>')
        subprocess.run(["git", "-C", str(self.repo), "add", "site/index.html", "papers/ExampleExternal"], check=True)
        output = self.root / "output"
        result = build(self.repo, output)
        self.assertEqual(result["public_papers"], 1)
        self.assertEqual(result["external_references"], 1)
        index = (output / "index.html").read_text()
        self.assertIn("125 total lines", index)
        self.assertIn("2 formalized papers", index)
        self.assertIn('href="https://github.com/example/proofs/blob/main/REPORT.md"', index)
        self.assertIn('href="/AppliedModelingLib/artifacts/papers/ExampleExternal/README.html"', index)
        page = (output / "artifacts/papers/ExampleExternal/README.html").read_text()
        self.assertIn("External Paper", page)
        self.assertIn("https://github.com/example/proofs", page)
        self.assertFalse((output / "artifacts/papers/Private").exists())

    def test_project_root_can_be_previewed_without_a_prefix(self):
        output = self.root / "output"
        build(self.repo, output, "")
        self.assertIn('href="/artifacts/papers/Example/FINAL_VALIDATION_REPORT.html"', (output / "index.html").read_text())


if __name__ == "__main__":
    unittest.main()
