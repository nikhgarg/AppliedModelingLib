#!/usr/bin/env python3
"""Serve the current status site and current paper artifacts on localhost.

The generated site continues to contain only public GitHub artifact URLs.
When it is viewed through this server, a small browser-side rewrite selects the
``/artifacts/`` route below, which is deliberately available only from the
local checkout.
"""

from __future__ import annotations

import argparse
import html
import http.server
import io
from pathlib import Path
import subprocess
from urllib.parse import quote, unquote, urlsplit


REPOSITORY_ROOT = Path(__file__).resolve().parents[1]
SITE_ROOT = Path(__file__).resolve().parent
ARTIFACT_PREFIX = "/artifacts/"
ARTIFACT_CAPABILITY_PATH = "/.local-artifact-capability"


def paper_artifact_navigation(path: Path) -> str:
    """Keep the paper's existing PDF reachable from reports and nested audits."""

    papers_root = (REPOSITORY_ROOT / "papers").resolve()
    try:
        relative = path.resolve().relative_to(papers_root)
    except ValueError:
        return ""
    if len(relative.parts) < 2:
        return ""
    folder = papers_root / relative.parts[0]
    links = ['<a href="/">Papers</a>']
    for label, filename in (
        ("Report", "FINAL_VALIDATION_REPORT.md"),
        ("Lean statements", "PaperInterface.lean"),
        ("Dependency DAG", "docs/DependencyDAG.pdf"),
    ):
        target = folder / filename
        if not target.is_file():
            continue
        try:
            target.resolve().relative_to(papers_root)
        except ValueError:
            continue
        route = ARTIFACT_PREFIX + quote(
            str(target.relative_to(REPOSITORY_ROOT)), safe="/"
        )
        links.append(f'<a href="{html.escape(route, quote=True)}">{label}</a>')
    return '<nav class="artifact-links" aria-label="Paper artifacts">' + " ".join(links) + "</nav>"


def render_markdown_artifact(path: Path) -> bytes:
    """Render report prose while keeping source-only generator comments hidden."""

    result = subprocess.run(
        [
            "pandoc", "--from=markdown+gfm_auto_identifiers", "--to=html5",
            "--standalone", "--strip-comments", "--mathml",
            "--metadata", f"pagetitle={path.stem.replace('_', ' ').title()}",
            "--css=/styles/site.css",
        ],
        input=path.read_text(encoding="utf-8"),
        text=True, capture_output=True, check=True, timeout=15,
    )
    return result.stdout.replace(
        "<body>", '<body class="artifact-document">' + paper_artifact_navigation(path), 1
    ).encode("utf-8")


class PrivatePreviewHandler(http.server.SimpleHTTPRequestHandler):
    """Map only ``papers/`` artifact requests outside the static-site root."""

    extensions_map = {
        **http.server.SimpleHTTPRequestHandler.extensions_map,
        ".lean": "text/plain; charset=utf-8",
    }

    def send_head(self):
        request_path = urlsplit(self.path).path
        target = Path(self.translate_path(self.path))
        if (
            request_path.startswith(ARTIFACT_PREFIX)
            and target.suffix.lower() == ".md"
            and target.is_file()
        ):
            try:
                content = render_markdown_artifact(target)
            except (OSError, subprocess.SubprocessError):
                self.send_error(500, "Could not render Markdown; local preview requires pandoc")
                return None
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(content)))
            self.end_headers()
            return io.BytesIO(content)
        return super().send_head()

    def do_HEAD(self) -> None:
        if urlsplit(self.path).path == ARTIFACT_CAPABILITY_PATH:
            self.send_response(204)
            self.end_headers()
            return
        super().do_HEAD()

    def do_GET(self) -> None:
        if urlsplit(self.path).path == ARTIFACT_CAPABILITY_PATH:
            self.send_response(204)
            self.end_headers()
            return
        super().do_GET()

    def translate_path(self, path: str) -> str:
        request_path = urlsplit(path).path
        if request_path.startswith(ARTIFACT_PREFIX):
            relative = Path(unquote(request_path[len(ARTIFACT_PREFIX) :]))
            if relative.parts[:1] != ("papers",) or relative.is_absolute():
                return str(SITE_ROOT / "__not_found__")
            target = (REPOSITORY_ROOT / relative).resolve()
            try:
                target.relative_to(REPOSITORY_ROOT / "papers")
            except ValueError:
                return str(SITE_ROOT / "__not_found__")
            return str(target)
        return super().translate_path(path)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--host", default="127.0.0.1")
    parser.add_argument("--port", type=int, default=8080)
    args = parser.parse_args()
    handler = lambda *handler_args, **handler_kwargs: PrivatePreviewHandler(
        *handler_args, directory=str(SITE_ROOT), **handler_kwargs
    )
    with http.server.ThreadingHTTPServer((args.host, args.port), handler) as server:
        print(f"Local preview: http://{args.host}:{args.port}", flush=True)
        server.serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
