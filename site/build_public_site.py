#!/usr/bin/env python3
"""Build the published website and HTML versions of released paper documents.

Only tracked files in explicitly public paper folders are eligible. The build
never changes Markdown, status, proof, or audit inputs. Pandoc is required.
"""
from __future__ import annotations

import argparse
import html
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import posixpath
import re
import shutil
import subprocess
from urllib.parse import quote, unquote, urlsplit, urlunsplit

from private_preview_server import render_markdown_artifact

REPOSITORY = "https://github.com/nikhgarg/AppliedModelingLib"
OLD_REPOSITORY = "https://github.com/nikhgarg/EconCSLib"
ASSET_SUFFIXES = {".pdf", ".svg", ".png", ".jpg", ".jpeg", ".gif", ".webp"}


class LinkRewriter(HTMLParser):
    """Change URL attributes without reformatting document text or mathematics."""

    def __init__(self, rewrite, *, landing=False):
        super().__init__(convert_charrefs=False)
        self.rewrite = rewrite
        self.landing = landing
        self.parts = []

    def handle_starttag(self, tag, attrs):
        raw = self.get_starttag_text()
        local = dict(attrs).get("data-local-artifact-href") if self.landing else None

        def replace(match):
            name, delimiter, value = match.groups()
            target = local if name == "href" and local else html.unescape(value)
            return f'{name}={delimiter}{html.escape(self.rewrite(target), quote=True)}{delimiter}'

        raw = re.sub(r'''(?<![\w-])(href|src)=(['"])(.*?)\2''', replace, raw)
        if self.landing:
            raw = re.sub(r'''\sdata-local-artifact-href=(['"]).*?\1''', "", raw)
        self.parts.append(raw)

    handle_startendtag = handle_starttag

    def handle_endtag(self, tag):
        self.parts.append(f"</{tag}>")

    def handle_data(self, data):
        self.parts.append(data)

    def handle_entityref(self, name):
        self.parts.append(f"&{name};")

    def handle_charref(self, name):
        self.parts.append(f"&#{name};")

    def handle_comment(self, data):
        self.parts.append(f"<!--{data}-->")

    def handle_decl(self, decl):
        self.parts.append(f"<!{decl}>")


def rewrite_html(content, rewrite, *, landing=False):
    parser = LinkRewriter(rewrite, landing=landing)
    parser.feed(content)
    parser.close()
    return "".join(parser.parts)


def build(repo: Path, output: Path, base_path: str = "/AppliedModelingLib") -> dict:
    repo, output = repo.resolve(), output.resolve()
    if output.exists() and any(output.iterdir()):
        raise ValueError("Output directory must be empty; use a fresh build directory")
    if output == repo or repo.is_relative_to(output):
        raise ValueError("Output must not contain the repository")
    base_path = "/" + base_path.strip("/") if base_path.strip("/") else ""
    tracked = set(subprocess.check_output(
        ["git", "-C", str(repo), "ls-files", "-z"], text=True
    ).split("\0")) - {""}
    public = set()
    for name in sorted(tracked):
        path = PurePosixPath(name)
        if len(path.parts) == 3 and path.parts[0] == "papers" and path.name == "status.json":
            if json.loads((repo / name).read_text()).get("repository_visibility") == "public":
                public.add(path.parts[1])

    artifacts = {}
    for name in sorted(tracked):
        path = PurePosixPath(name)
        if len(path.parts) < 3 or path.parts[0] != "papers" or path.parts[1] not in public:
            continue
        if path.suffix.lower() not in ASSET_SUFFIXES | {".md"}:
            continue
        source = repo / name
        if source.is_symlink() or not source.is_file() or not source.resolve().is_relative_to(repo):
            raise ValueError(f"Artifact must be a regular repository file: {name}")
        destination = path.with_suffix(".html") if path.suffix.lower() == ".md" else path
        artifacts[name] = "artifacts/" + str(destination)

    def url_for(name):
        return base_path + "/" + quote(artifacts[name], safe="/")

    def source_url(name):
        kind = "tree" if (repo / name).is_dir() else "blob"
        return f"{REPOSITORY}/{kind}/main/{quote(name, safe='/')}"

    def rewrite(url, current=None):
        url = url.replace(OLD_REPOSITORY, REPOSITORY)
        parsed = urlsplit(url)
        path = unquote(parsed.path)
        if url.startswith(REPOSITORY + "/blob/main/"):
            name = path.split("/blob/main/", 1)[1]
        elif not parsed.netloc and not parsed.scheme and path.startswith("/artifacts/"):
            name = path[len("/artifacts/"):]
            if name not in artifacts:
                if name not in tracked or PurePosixPath(name).parts[1] not in public:
                    raise ValueError(f"Landing page links to an unpublished artifact: {name}")
        elif parsed.scheme or parsed.netloc or not path or path.startswith("/") or current is None:
            return url
        else:
            name = posixpath.normpath(str(PurePosixPath(current).parent / path))
        destination = url_for(name) if name in artifacts else source_url(name)
        result = urlsplit(destination)
        return urlunsplit((result.scheme, result.netloc, result.path, parsed.query, parsed.fragment))

    output.mkdir(parents=True, exist_ok=True)
    for name in sorted(tracked):
        path = PurePosixPath(name)
        if path.parts[:2] in {("site", "styles"), ("site", "assets")}:
            source = repo / name
            if source.is_symlink():
                raise ValueError(f"Site assets cannot be symlinks: {name}")
            target = output / path.relative_to("site")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
    landing = rewrite_html((repo / "site/index.html").read_text(), rewrite, landing=True)
    (output / "index.html").write_text(landing)
    (output / ".nojekyll").touch()

    for name, destination in artifacts.items():
        target = output / destination
        target.parent.mkdir(parents=True, exist_ok=True)
        if not name.lower().endswith(".md"):
            shutil.copyfile(repo / name, target)
            continue
        folder = "/".join(PurePosixPath(name).parts[:2])
        links = [("Papers", base_path + "/")]
        for label, filename in (
            ("Report", "FINAL_VALIDATION_REPORT.md"),
            ("Lean statements", "PaperInterface.lean"),
            ("Dependency DAG", "docs/DependencyDAG.pdf"),
            ("Review packet", "docs/HUMAN_REVIEW_PACKET.pdf"),
        ):
            relative = folder + "/" + filename
            if relative in tracked:
                links.append((label, url_for(relative) if relative in artifacts else source_url(relative)))
        links.append(("Markdown source", source_url(name)))
        navigation = '<nav class="artifact-links" aria-label="Paper artifacts">' + " ".join(
            f'<a href="{html.escape(url, quote=True)}">{label}</a>' for label, url in links
        ) + "</nav>"
        rendered = render_markdown_artifact(
            repo / name, css_url=base_path + "/styles/site.css", navigation=""
        ).decode()
        rendered = rewrite_html(rendered, lambda url: rewrite(url, name))
        rendered = rendered.replace('<body class="artifact-document">',
                                    '<body class="artifact-document">' + navigation, 1)
        target.write_text(rendered)
    result = {"public_papers": len(public), "documents": sum(n.endswith(".md") for n in artifacts),
              "assets": sum(not n.endswith(".md") for n in artifacts)}
    (output / "build-manifest.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--base-path", default="/AppliedModelingLib")
    args = parser.parse_args()
    print(json.dumps(build(args.repo, args.output, args.base_path), indent=2))


if __name__ == "__main__":
    main()
