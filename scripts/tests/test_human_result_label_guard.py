from __future__ import annotations

from pathlib import Path
import tempfile
import unittest

from scripts.human_result_label_guard import reader_facing_result_label_errors


SOURCE = r"""
\newtheorem{theorem}{Theorem}
\newtheorem{proposition}{Proposition}
\newtheorem{lemma}[proposition]{Lemma}
\begin{theorem}\label{thm1v2}
Main result.
\end{theorem}
\begin{proposition}\label{prop:beet}
Auxiliary result.
\end{proposition}
\begin{lemma}\label{lem:log-bound}
Auxiliary lemma.
\end{lemma}
"""


class HumanResultLabelGuardTests(unittest.TestCase):
    def paper(self, root: Path, report: str, memo: str = "") -> Path:
        paper = root / "Fixture"
        (paper / "source_tex").mkdir(parents=True)
        (paper / "docs").mkdir()
        (paper / "source_tex" / "main.tex").write_text(SOURCE, encoding="utf-8")
        (paper / "FINAL_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        if memo:
            (paper / "docs" / "SOURCE_CLARIFICATIONS.md").write_text(
                memo, encoding="utf-8"
            )
        return paper

    def test_report_front_rejects_full_suffix_and_subpart_labels(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = self.paper(
                Path(temp_dir),
                "## 4. Results\n`thm1v2`, `beet(ii)`, and `log-bound`.\n",
            )

            errors = reader_facing_result_label_errors(paper)

        self.assertEqual(len(errors), 3)
        self.assertTrue(any("source label: `thm1v2`" in error for error in errors))
        self.assertTrue(any("source label: `prop:beet`" in error for error in errors))
        self.assertTrue(any("source label: `lem:log-bound`" in error for error in errors))

    def test_report_technical_appendix_does_not_trigger(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = self.paper(
                Path(temp_dir),
                "## 1. Verdict\nProposition 1 is checked.\n"
                "## 12. Detailed Evidence\nInternal key: `prop:beet`.\n",
            )

            self.assertEqual(reader_facing_result_label_errors(paper), ())

    def test_memo_checks_headings_table_result_cells_and_result_constructions(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = self.paper(
                Path(temp_dir),
                "## 1. Verdict\nThe results are checked.\n",
                "## Proposition `thm1v2`\n"
                "| Result | Status |\n| --- | --- |\n| `beet` | changed |\n"
                "Lemma `log-bound` uses a corrected proof.\n",
            )

            errors = reader_facing_result_label_errors(paper)

        self.assertEqual(len(errors), 3)

    def test_memo_ordinary_technical_reference_does_not_trigger(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = self.paper(
                Path(temp_dir),
                "## 1. Verdict\nThe results are checked.\n",
                "The internal trace key `prop:beet` is preserved for diagnostics.\n",
            )

            self.assertEqual(reader_facing_result_label_errors(paper), ())

    def test_rendered_numbers_are_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper = self.paper(
                Path(temp_dir),
                "## 4. Results\nProposition 7(ii) and Lemma 6 are checked.\n",
                "## Proposition 7(ii): qualitative replacement\n",
            )

            self.assertEqual(reader_facing_result_label_errors(paper), ())


if __name__ == "__main__":
    unittest.main()
