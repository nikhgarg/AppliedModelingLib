"""Keep raw TeX labels out of reader-facing result identifiers."""

from __future__ import annotations

from pathlib import Path
import re


_STANDARD_RESULT_ENVIRONMENTS = frozenset(
    {
        "assumption",
        "claim",
        "conjecture",
        "corollary",
        "definition",
        "example",
        "lemma",
        "proposition",
        "remark",
        "theorem",
    }
)
_RESULT_WORD = re.compile(
    r"\b(?:assumptions?|claims?|conjectures?|corollaries|definitions?|examples?|"
    r"lemmas?|propositions?|remarks?|theorems?)\b",
    re.IGNORECASE,
)
_INLINE_CODE = re.compile(r"(?<!`)`([^`\n]+)`(?!`)")
_SECTION_TWELVE = re.compile(r"^ {0,3}##\s+12\.\s+", re.MULTILINE)
_MARKDOWN_HEADING = re.compile(r"^ {0,3}#{1,6}\s+")
_MARKDOWN_TABLE_SEPARATOR = re.compile(r"^:?-{3,}:?$")
_NEWTHEOREM = re.compile(
    r"\\newtheorem\*?\s*\{(?P<environment>[A-Za-z@]+)\}"
)
_RESULT_PREFIXES = frozenset(
    {
        "assump",
        "assumption",
        "claim",
        "conj",
        "conjecture",
        "cor",
        "corollary",
        "def",
        "definition",
        "ex",
        "example",
        "lem",
        "lemma",
        "prop",
        "proposition",
        "rem",
        "remark",
        "thm",
        "theorem",
    }
)


def _source_tex_paths(paper_dir: Path) -> tuple[Path, ...]:
    paths: list[Path] = []
    for path in paper_dir.rglob("*.tex"):
        relative_parts = path.relative_to(paper_dir).parts
        if any(part in {"docs", ".review_traces", ".lake"} for part in relative_parts):
            continue
        paths.append(path)
    return tuple(sorted(paths))


def _result_environments(source_texts: tuple[str, ...]) -> frozenset[str]:
    environments = set(_STANDARD_RESULT_ENVIRONMENTS)
    for source_text in source_texts:
        environments.update(
            match.group("environment") for match in _NEWTHEOREM.finditer(source_text)
        )
    return frozenset(environments)


def _tex_result_labels(paper_dir: Path) -> dict[str, str]:
    """Map raw result labels and conventional suffixes to the full TeX label."""

    source_texts = tuple(
        path.read_text(encoding="utf-8") for path in _source_tex_paths(paper_dir)
    )
    environments = _result_environments(source_texts)
    environment_alternation = "|".join(
        sorted((re.escape(environment) for environment in environments), key=len, reverse=True)
    )
    ordinary = re.compile(
        rf"\\begin\s*\{{(?:{environment_alternation})\}}"
        r"(?:\s*\[[^\]]*\])?\s*"
        r"\\label\s*\{(?P<label>[^{}]+)\}",
        re.DOTALL,
    )
    restatable = re.compile(
        rf"\\begin\s*\{{restatable\}}(?:\s*\[[^\]]*\])?\s*"
        rf"\{{(?:{environment_alternation})\}}\s*\{{[^{{}}]+\}}\s*"
        r"\\label\s*\{(?P<label>[^{}]+)\}",
        re.DOTALL,
    )

    labels: dict[str, str] = {}
    for source_text in source_texts:
        for pattern in (ordinary, restatable):
            for match in pattern.finditer(source_text):
                label = match.group("label").strip()
                if not label:
                    continue
                labels[label] = label
                if ":" in label:
                    prefix, suffix = label.split(":", 1)
                    if prefix.strip().lower() in _RESULT_PREFIXES and suffix.strip():
                        labels[suffix.strip()] = label
    return labels


def _matching_raw_label(token: str, labels: dict[str, str]) -> str | None:
    cleaned = token.strip()
    if cleaned in labels:
        return labels[cleaned]
    subpart = re.fullmatch(r"(.+?)\((?:[ivxlcdm]+|[A-Za-z0-9]+)\)", cleaned)
    if subpart and subpart.group(1) in labels:
        return labels[subpart.group(1)]
    return None


def _table_result_cell(line: str) -> str | None:
    if "|" not in line:
        return None
    cells = line.strip().strip("|").split("|")
    if not cells:
        return None
    first = cells[0].strip()
    if not first or _MARKDOWN_TABLE_SEPARATOR.fullmatch(first):
        return None
    return first


def _result_position_fragments(line: str, *, report_front: bool) -> tuple[str, ...]:
    if report_front:
        return (line,)
    fragments: list[str] = []
    if _MARKDOWN_HEADING.match(line):
        fragments.append(line)
    first_cell = _table_result_cell(line)
    if first_cell is not None:
        fragments.append(first_cell)
    if _RESULT_WORD.search(line):
        fragments.append(line)
    return tuple(dict.fromkeys(fragments))


def reader_facing_result_label_errors(
    paper_dir: Path,
    *,
    report_text: str | None = None,
) -> tuple[str, ...]:
    """Reject raw TeX labels used as human-facing result identifiers.

    The check covers all inline-code identifiers in report Sections 1--11. In
    the source-clarifications memo it checks headings, first table cells, and
    sentences that identify a theorem-like result. Technical references in the
    report appendix and ordinary memo prose are intentionally outside this
    presentation guard.
    """

    labels = _tex_result_labels(paper_dir)
    if not labels:
        return ()

    documents: list[tuple[Path, str, bool]] = []
    report_path = paper_dir / "FINAL_VALIDATION_REPORT.md"
    if report_text is None:
        if report_path.is_file():
            report_text = report_path.read_text(encoding="utf-8")
        else:
            report_text = ""
    section_twelve = _SECTION_TWELVE.search(report_text)
    report_front = report_text[: section_twelve.start()] if section_twelve else report_text
    documents.append((report_path, report_front, True))

    memo_path = paper_dir / "docs" / "SOURCE_CLARIFICATIONS.md"
    if memo_path.is_file():
        documents.append((memo_path, memo_path.read_text(encoding="utf-8"), False))

    errors: list[str] = []
    for path, text, is_report_front in documents:
        relative = path.relative_to(paper_dir).as_posix()
        for line_number, line in enumerate(text.splitlines(), start=1):
            for fragment in _result_position_fragments(line, report_front=is_report_front):
                for match in _INLINE_CODE.finditer(fragment):
                    token = match.group(1).strip()
                    raw_label = _matching_raw_label(token, labels)
                    if raw_label is None:
                        continue
                    errors.append(
                        f"{relative}:{line_number}: raw TeX label `{token}` is used "
                        "as a reader-facing result identifier "
                        f"(source label: `{raw_label}`); use the rendered result "
                        "number or a descriptive title"
                    )
    return tuple(dict.fromkeys(errors))
