"""Reader-visible behavior of checkout-local report rendering."""

from __future__ import annotations

import importlib.util
import io
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest import mock
from urllib.parse import urljoin

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "private_preview_server", ROOT / "site" / "private_preview_server.py"
)
preview = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(preview)


@unittest.skipUnless(shutil.which("pandoc"), "Pandoc is required for report preview")
class MarkdownArtifactTests(unittest.TestCase):
    def response(self, route: str, site: Path) -> tuple[bytes, bytes]:
        """Exercise the real request dispatcher without opening a network socket."""

        handler = object.__new__(preview.PrivatePreviewHandler)
        handler.path = route
        handler.directory = str(site)
        handler.headers = {}
        handler.wfile = io.BytesIO()
        handler.request_version = "HTTP/1.1"
        handler.requestline = "GET " + route + " HTTP/1.1"
        handler.command = "GET"
        handler.log_message = lambda *_args: None
        stream = handler.send_head()
        body = stream.read() if stream is not None else b""
        if stream is not None:
            stream.close()
        return handler.wfile.getvalue(), body

    def test_hides_generator_delimiters_preserving_content_and_links(self) -> None:
        source = (
            "# Report\n\n<!-- BEGIN GENERATED SETTLED REVIEW CONTEXT -->\n"
            "The **substantive clarification** stays visible.\n\n"
            "| Result | Reading |\n|---|---|\n| Lemma 1 | Closed interval |\n\n"
            "[Memo](docs/SOURCE_CLARIFICATIONS.md)\n\n"
            "<!-- END GENERATED SETTLED REVIEW CONTEXT -->\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "report.md"
            path.write_text(source)
            rendered = preview.render_markdown_artifact(path).decode()
            self.assertEqual(path.read_text(), source)
        self.assertNotIn("BEGIN GENERATED", rendered)
        self.assertNotIn("END GENERATED", rendered)
        self.assertIn("<strong>substantive clarification</strong>", rendered)
        self.assertIn("<table>", rendered)
        self.assertIn('href="docs/SOURCE_CLARIFICATIONS.md"', rendered)
        self.assertIn('class="artifact-document"', rendered)

    def test_report_and_nested_audit_open_the_existing_dag_pdf(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Example Paper"
            (folder / "docs").mkdir(parents=True)
            (root / "site").mkdir()
            pdf = b"%PDF-1.7\nExisting compiled DAG\n"
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(pdf)
            for filename in ("FINAL_VALIDATION_REPORT.md", "docs/AGENT_SOURCE_AUDIT.md"):
                (folder / filename).write_text("# Assessment\n\nThe result is checked.\n")
            with mock.patch.object(preview, "REPOSITORY_ROOT", root):
                for filename in ("FINAL_VALIDATION_REPORT.md", "docs/AGENT_SOURCE_AUDIT.md"):
                    route = "/artifacts/papers/Example%20Paper/" + filename
                    headers, body = self.response(route, root / "site")
                    self.assertIn(b"200 OK", headers)
                    self.assertIn(b"text/html; charset=utf-8", headers)
                    dag_route = "/artifacts/papers/Example%20Paper/docs/DependencyDAG.pdf"
                    self.assertIn(
                        f'<a href="{dag_route}">Dependency DAG</a>'.encode(), body
                    )
                    destination = urljoin("http://localhost:8080" + route, dag_route)
                    self.assertEqual(destination, "http://localhost:8080" + dag_route)
                    pdf_headers, pdf_body = self.response(dag_route, root / "site")
                    self.assertIn(b"200 OK", pdf_headers)
                    self.assertIn(b"Content-type: application/pdf", pdf_headers)
                    self.assertEqual(pdf_body, pdf)

    def test_heading_fragments_match_public_github_documents(self) -> None:
        source = (
            "# Report\n\n"
            "[Assumptions](#6-additional-assumptions-beyond-paper)\n\n"
            "[Memo](#theorem-32-source-page-7)\n\n"
            "## 6. Additional Assumptions Beyond Paper\n\nNone.\n\n"
            "## Theorem 3.2: [source, page 7](https://example.org/paper#page=7)\n\n"
            "The statement is exact.\n"
        )
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "report.md"
            path.write_text(source)
            rendered = preview.render_markdown_artifact(path).decode()
        self.assertIn('id="6-additional-assumptions-beyond-paper"', rendered)
        self.assertIn('id="theorem-32-source-page-7"', rendered)
        self.assertNotIn('id="additional-assumptions-beyond-paper"', rendered)
        self.assertNotIn('id="theorem-3.2', rendered)

    def test_navigation_does_not_offer_missing_or_outside_paper_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Example"
            (folder / "docs").mkdir(parents=True)
            report = folder / "FINAL_VALIDATION_REPORT.md"
            report.write_text("# Report\n")
            outside = root / "outside.pdf"
            outside.write_bytes(b"%PDF-1.7\n")
            with mock.patch.object(preview, "REPOSITORY_ROOT", root):
                self.assertNotIn("Dependency DAG", preview.paper_artifact_navigation(report))
                (folder / "docs" / "DependencyDAG.pdf").symlink_to(outside)
                self.assertNotIn("Dependency DAG", preview.paper_artifact_navigation(report))
                self.assertEqual(preview.paper_artifact_navigation(root / "outside.md"), "")


if __name__ == "__main__":
    unittest.main()
