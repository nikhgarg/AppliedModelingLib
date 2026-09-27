#!/usr/bin/env python3
"""Render link-only paper references without importing proofs or audit status."""
from __future__ import annotations

import argparse
import html
import json
from pathlib import Path, PurePosixPath
import re
import subprocess

BEGIN = "<!-- BEGIN EXTERNAL PAPER REFERENCE ROWS -->"
END = "<!-- END EXTERNAL PAPER REFERENCE ROWS -->"
PAPER_ROWS_END = "<!-- END GENERATED PAPER STATUS ROWS -->"
LINK_LABELS = {
    "report": "Report",
    "lean_statements": "Lean statements",
    "theorem_index": "Theorem index",
    "repository": "Repo",
}


def validate_reference(payload: object, paper: str) -> dict:
    required = {"schema", "kind", "id", "repository_visibility", "title",
                "authors", "publication", "status", "links", "code"}
    if not isinstance(payload, dict) or set(payload) != required:
        raise ValueError(f"{paper}: malformed external reference fields")
    if (type(payload["schema"]) is not int or payload["schema"] != 1
            or payload["kind"] != "external_reference"
            or payload["id"] != paper
            or not re.fullmatch(r"[A-Za-z0-9]+", paper)
            or payload["repository_visibility"] != "public"):
        raise ValueError(f"{paper}: expected a public schema-1 external reference")
    for key in ("title", "authors", "publication"):
        value = payload[key]
        if not isinstance(value, str) or not value.strip() or any(c in value for c in "\n\r"):
            raise ValueError(f"{paper}: invalid {key}")
    if payload["status"] not in {"formalized", "partially formalized"}:
        raise ValueError(f"{paper}: invalid external report status")
    code = payload["code"]
    if (not isinstance(code, dict)
            or set(code) != {"revision", "lean_files", "lean_lines", "counting_method"}
            or not isinstance(code["revision"], str)
            or not re.fullmatch(r"[0-9a-f]{40}", code["revision"])
            or code["counting_method"] != "tracked_lean_physical_lines"
            or any(type(code[key]) is not int or code[key] <= 0
                   for key in ("lean_files", "lean_lines"))):
        raise ValueError(f"{paper}: invalid revision-pinned Lean code count")
    links = payload["links"]
    if not isinstance(links, dict) or set(links) != set(LINK_LABELS):
        raise ValueError(f"{paper}: incomplete external links")
    repository = links["repository"]
    if not isinstance(repository, str) or not re.fullmatch(
        r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository
    ):
        raise ValueError(f"{paper}: expected a public GitHub repository URL")
    for key, url in links.items():
        if not isinstance(url, str) or any(c.isspace() for c in url):
            raise ValueError(f"{paper}: invalid {key} URL")
        if key != "repository" and not url.startswith(repository + "/blob/"):
            raise ValueError(f"{paper}: {key} must link into the external repository")
    return payload


def render_readme(reference: dict) -> str:
    lines = [f"# {reference['title']}", "",
             f"{reference['authors']}; {reference['publication']}.", "",
             "This paper's Lean formalization is maintained in a separate repository.", ""]
    lines.extend(f"- [{label}]({reference['links'][key]})"
                 for key, label in LINK_LABELS.items())
    code = reference["code"]
    lines.extend(["", f"Code size: {code['lean_lines']:,} lines in {code['lean_files']:,} tracked Lean files "
                  f"at [revision {code['revision'][:8]}]({reference['links']['repository']}/tree/{code['revision']}). "
                  "The website includes this code in its total; Mathlib and other dependency code are excluded."])
    return "\n".join(lines) + "\n"


def validate_reference_folder(reference: dict, paths: set[str], readme: str) -> None:
    paper = reference["id"]
    prefix = f"papers/{paper}/"
    members = {p for p in paths if p.startswith(prefix) or p == f"papers/{paper}.lean"}
    if members != {prefix + "external.json", prefix + "README.md"}:
        raise ValueError(f"{paper}: external reference folder permits only external.json and README.md")
    if readme != render_readme(reference):
        raise ValueError(f"{paper}: external reference README is out of sync")


def load_references(repo: Path, paths: set[str], *, check_readmes: bool = True) -> list[dict]:
    references = []
    for name in sorted(paths):
        path = PurePosixPath(name)
        if len(path.parts) != 3 or path.parts[0] != "papers" or path.name != "external.json":
            continue
        source = repo / name
        if source.is_symlink():
            raise ValueError(f"External reference cannot be a symlink: {name}")
        reference = validate_reference(json.loads(source.read_text()), path.parts[1])
        readme = source.with_name("README.md")
        if readme.is_symlink():
            raise ValueError(f"External reference README cannot be a symlink: {readme}")
        if check_readmes:
            validate_reference_folder(reference, paths, readme.read_text())
        else:
            validate_reference_folder(reference, paths | {f"papers/{reference['id']}/README.md"},
                                      render_readme(reference))
        references.append(reference)
    return references


def render_rows(references: list[dict]) -> str:
    indent = " " * 14
    lines = [indent + BEGIN]
    for reference in references:
        links = reference["links"]
        folder = f"papers/{reference['id']}/README.md"
        anchor = (
            f'<a href="https://github.com/nikhgarg/AppliedModelingLib/blob/main/{folder}" '
            f'data-local-artifact-href="/artifacts/{folder}">Reference folder</a>'
        )
        artifacts = " ".join(f'<a href="{html.escape(links[key], quote=True)}">{label}</a>'
                             for key, label in LINK_LABELS.items())
        lines.extend([
            indent + f'<tr data-external-reference="{reference["id"]}">',
            indent + "  <td>",
            indent + f'    <a class="paper-source" href="{html.escape(links["repository"], quote=True)}"><cite>{html.escape(reference["title"])}</cite></a> by',
            indent + f'    {html.escape(reference["authors"])}; {html.escape(reference["publication"])}.',
            indent + "  </td>",
            indent + f'  <td>{reference["status"].capitalize()}</td>',
            indent + '  <td aria-label="Human review recorded in the external repository">—</td>',
            indent + f'  <td>{reference["code"]["lean_lines"]:,}</td>',
            indent + f'  <td><div class="artifact-links">{artifacts} {anchor}</div><p class="paper-note">Maintained in a separate repository.</p></td>',
            indent + "</tr>",
        ])
    return "\n".join([*lines, indent + END])


def render_index(current: str, references: list[dict], *, include_totals: bool = False) -> str:
    if include_totals and (references or 'data-local-counts="' in current):
        current = render_combined_totals(current, references)
    if BEGIN in current or END in current:
        if current.count(BEGIN) != 1 or current.count(END) != 1 or current.index(BEGIN) > current.index(END):
            raise ValueError("Malformed external paper reference markers")
        start = current.rfind("\n", 0, current.index(BEGIN)) + 1
        stop = current.index(END) + len(END)
        return current[:start] + render_rows(references) + current[stop:]
    if not references:
        return current
    if current.count(PAPER_ROWS_END) != 1:
        raise ValueError("Expected the generated paper table before external references")
    end = current.index(PAPER_ROWS_END) + len(PAPER_ROWS_END)
    return current[:end] + "\n" + render_rows(references) + current[end:]


def render_combined_totals(current: str, references: list[dict]) -> str:
    """Combine local and external code at presentation time, exactly once.

    The status generator continues to own the repository-local counts. Both
    Pages and the local preview add the external snapshots when serving them.
    """
    paragraph = re.compile(r'<p class="project-stats"(?P<attrs>[^>]*)>(?P<text>.*?)</p>', re.S)
    match = paragraph.search(current)
    if match is None:
        raise ValueError("Expected project totals for external code accounting")
    saved = re.search(r'data-local-counts="(\d+),(\d+),(\d+)"', match['attrs'])
    if saved:
        formalized, partial, lines = map(int, saved.groups())
    else:
        counts = re.search(r'contains ([\d,]+) formalized papers(?: and ([\d,]+) partially formalized papers?)?,\s+with ([\d,]+) total\s+lines of Lean code', match['text'])
        if counts is None:
            raise ValueError("Could not read repository-local project totals")
        formalized, partial, lines = (int((value or '0').replace(',', '')) for value in counts.groups())
    base = f'{formalized},{partial},{lines}'
    formalized += sum(r['status'] == 'formalized' for r in references)
    partial += sum(r['status'] == 'partially formalized' for r in references)
    lines += sum(r['code']['lean_lines'] for r in references)
    partial_text = f" and {partial} partially formalized {'paper' if partial == 1 else 'papers'}" if partial else ""
    rendered = (f'<p class="project-stats" data-local-counts="{base}">\n'
                f'          Currently, the project contains {formalized} formalized papers{partial_text}, '
                f'with {lines:,} total lines of Lean code.\n        </p>')
    return current[:match.start()] + rendered + current[match.end():]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    repo = args.repo.resolve()
    paths = set(subprocess.check_output(["git", "ls-files", "-z"], cwd=repo, text=True).split("\0")) - {""}
    references = load_references(repo, paths, check_readmes=args.check)
    outputs = {repo / "papers" / r["id"] / "README.md": render_readme(r) for r in references}
    index = repo / "site/index.html"
    outputs[index] = render_index(index.read_text(), references)
    changed = [p for p, text in outputs.items() if not p.exists() or p.read_text() != text]
    if args.check and changed:
        for path in changed:
            print(f"out of sync: {path.relative_to(repo)}")
        return 1
    for path in changed:
        path.write_text(outputs[path])
    print(f"External references: {len(references)}; {'checked' if args.check else 'rendered'}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
