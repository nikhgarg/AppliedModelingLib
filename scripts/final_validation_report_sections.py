"""Check the complete numbered report structure at document closeout."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
import re

_HEADING = re.compile(r"^ {0,3}##\s+(\d+)\.\s+\S")
_FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
_TABLE_SEPARATOR = re.compile(r"^:?-{3,}:?$")


@dataclass(frozen=True)
class ResultTableRow:
    """One visible row in the reader-facing Section 4 result table."""

    result: str
    comparison: str
    sha256: str


def _visible_lines(report_text: str) -> list[str]:
    """Return rendered lines without crediting comments or fenced examples."""

    text = re.sub(r"<!--.*?-->", "", report_text, flags=re.DOTALL)
    lines: list[str] = []
    fence = ""
    for line in text.splitlines():
        match = _FENCE.match(line)
        if match:
            marker = match.group(1)
            if not fence:
                fence = marker
            elif marker[0] == fence[0] and len(marker) >= len(fence):
                if not line[match.end():].strip():
                    fence = ""
            continue
        if not fence:
            lines.append(line)
    return lines


def _table_cells(line: str) -> tuple[str, ...] | None:
    """Split one pipe-delimited Markdown row, respecting escapes and code spans."""

    stripped = line.strip()
    if not stripped.startswith("|") or not stripped.endswith("|"):
        return None
    content = stripped[1:-1]
    cells: list[str] = []
    cell: list[str] = []
    code_fence = 0
    index = 0
    while index < len(content):
        character = content[index]
        if character == "\\" and index + 1 < len(content):
            cell.extend((character, content[index + 1]))
            index += 2
            continue
        if character == "`":
            end = index
            while end < len(content) and content[end] == "`":
                end += 1
            run = end - index
            if code_fence == run:
                code_fence = 0
            elif not code_fence:
                code_fence = run
            cell.append(content[index:end])
            index = end
            continue
        if character == "|" and not code_fence:
            cells.append("".join(cell).strip())
            cell = []
        else:
            cell.append(character)
        index += 1
    cells.append("".join(cell).strip())
    return tuple(cells)


def _result_row_sha256(result: str, comparison: str) -> str:
    encoded = json.dumps(
        {"comparison": comparison, "result": result},
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def section_four_result_table(
    report_text: str,
) -> tuple[tuple[ResultTableRow, ...], tuple[str, ...]]:
    """Extract the unique two-column result table from visible Section 4.

    This is a document parser only. It does not interpret whether a comparison
    is exact, restricted, or source-implied; that remains a human review task.
    """

    lines = _visible_lines(report_text)
    section_starts = [
        index
        for index, line in enumerate(lines)
        if (match := _HEADING.match(line)) and int(match.group(1)) == 4
    ]
    if len(section_starts) != 1:
        return (), ("final validation report must contain exactly one visible Section 4",)
    start = section_starts[0] + 1
    end = next(
        (
            index
            for index in range(start, len(lines))
            if (match := _HEADING.match(lines[index])) and int(match.group(1)) != 4
        ),
        len(lines),
    )
    tables: list[list[tuple[str, ...]]] = []
    index = start
    while index + 1 < end:
        header = _table_cells(lines[index])
        separator = _table_cells(lines[index + 1])
        if (
            header is None
            or separator is None
            or len(header) != 2
            or len(separator) != 2
            or not all(_TABLE_SEPARATOR.fullmatch(cell.replace(" ", "")) for cell in separator)
        ):
            index += 1
            continue
        rows: list[tuple[str, ...]] = []
        cursor = index + 2
        while cursor < end:
            cells = _table_cells(lines[cursor])
            if cells is None:
                break
            rows.append(cells)
            cursor += 1
        tables.append([header, *rows])
        index = cursor
    if len(tables) != 1:
        return (), ("Section 4 must contain exactly one two-column result table",)
    table = tables[0]
    header = tuple(re.sub(r"\s+", " ", cell).strip().lower() for cell in table[0])
    if header[0] not in {"result", "paper result", "paper results"} or not header[1].startswith(
        "comparison"
    ):
        return (), ("Section 4 result table must have Result and Comparison columns",)
    errors: list[str] = []
    rows: list[ResultTableRow] = []
    seen: set[str] = set()
    for row_number, cells in enumerate(table[1:], start=1):
        if len(cells) != 2 or not all(cell.strip() for cell in cells):
            errors.append(f"Section 4 result table row {row_number} must have two nonempty cells")
            continue
        digest = _result_row_sha256(cells[0], cells[1])
        if digest in seen:
            errors.append(f"Section 4 result table repeats row {row_number}")
            continue
        seen.add(digest)
        rows.append(ResultTableRow(cells[0], cells[1], digest))
    if not rows:
        errors.append("Section 4 result table has no result rows")
    return tuple(rows), tuple(errors)


def final_report_section_errors(report_text: str) -> tuple[str, ...]:
    """Require Sections 1--21 once, in order, without crediting code examples.

    Equivalent descriptive headings are allowed. Mathematical completeness is
    still assessed by readers and the source-coverage gates, not by this parser.
    """
    text = re.sub(r"<!--.*?-->", "", report_text, flags=re.DOTALL)
    numbers: list[int] = []
    fence = ""
    for line in text.splitlines():
        match = _FENCE.match(line)
        if match:
            marker = match.group(1)
            if not fence:
                fence = marker
            elif marker[0] == fence[0] and len(marker) >= len(fence):
                if not line[match.end():].strip():
                    fence = ""
            continue
        if fence:
            continue
        heading = _HEADING.match(line)
        if heading and 1 <= int(heading.group(1)) <= 21:
            numbers.append(int(heading.group(1)))
    errors: list[str] = []
    missing = [n for n in range(1, 22) if n not in numbers]
    duplicates = sorted(n for n in set(numbers) if numbers.count(n) > 1)
    if missing:
        errors.append("final validation report is missing numbered sections: "
                      + ", ".join(map(str, missing)))
    if duplicates:
        errors.append("final validation report repeats numbered sections: "
                      + ", ".join(map(str, duplicates)))
    if numbers != sorted(numbers):
        errors.append("final validation report sections are out of order")
    return tuple(errors)
