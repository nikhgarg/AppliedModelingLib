import unittest

from scripts.final_validation_report_sections import (
    final_report_section_errors,
    section_four_result_table,
)


class FinalReportSectionsTests(unittest.TestCase):
    def setUp(self):
        self.sections = [f"## {n}. Section title\n\nAssessed content.\n" for n in range(1, 22)]

    def test_complete_report_accepts_descriptive_heading_variants(self):
        self.assertEqual(final_report_section_errors("\n".join(self.sections)), ())

    def test_reader_front_matter_does_not_replace_technical_closeout(self):
        text = "\n".join(self.sections[:11]) + "\n## DAG Audit\nVisually inspected.\n"
        errors = final_report_section_errors(text)
        self.assertEqual(len(errors), 1)
        self.assertIn("12, 13, 14, 15, 16, 17, 18, 19, 20, 21", errors[0])

    def test_examples_and_hidden_comments_cannot_supply_missing_section(self):
        text = "\n".join(self.sections[:20])
        text += "\n```markdown\n## 21. Coverage\n```\n<!--\n## 21. Coverage\n-->\n"
        self.assertIn("missing numbered sections: 21", final_report_section_errors(text)[0])

    def test_duplicate_and_reordered_sections_are_reported(self):
        text = "\n".join(self.sections) + "\n" + self.sections[15]
        errors = final_report_section_errors(text)
        self.assertTrue(any("repeats numbered sections: 16" in error for error in errors))
        self.assertTrue(any("out of order" in error for error in errors))

    def test_section_four_result_table_is_stable_and_handles_literal_pipes(self):
        text = (
            "## 4. Results\n\n"
            "| Result | Comparison with source |\n"
            "| :--- | ---: |\n"
            "| Theorem 1 | Uses `x | y` and the event `A \\| B`. |\n"
            "| Lemmas 2–3 | [Clarification](docs/NOTE.md#lemmas). |\n\n"
            "## 5. Coverage\n"
        )
        rows, errors = section_four_result_table(text)
        self.assertEqual(errors, ())
        self.assertEqual(len(rows), 2)
        self.assertEqual(rows[0].result, "Theorem 1")
        self.assertEqual(rows, section_four_result_table(text)[0])

    def test_hidden_or_duplicate_tables_cannot_supply_the_result_table(self):
        hidden = (
            "## 4. Results\n"
            "```markdown\n| Result | Comparison |\n| --- | --- |\n| Theorem 1 | Exact. |\n```\n"
            "<!-- | Result | Comparison |\n| --- | --- |\n| Theorem 1 | Exact. | -->\n"
            "## 5. Coverage\n"
        )
        self.assertTrue(section_four_result_table(hidden)[1])
        visible = (
            "| Result | Comparison |\n| --- | --- |\n| Theorem 1 | Exact. |\n"
        )
        duplicate = "## 4. Results\n" + visible + "\n" + visible + "## 5. Coverage\n"
        self.assertTrue(any("exactly one" in error for error in section_four_result_table(duplicate)[1]))

    def test_malformed_or_repeated_rows_fail(self):
        malformed = (
            "## 4. Results\n"
            "| Result | Comparison |\n| --- | --- |\n"
            "| Theorem 1 | |\n"
            "| Theorem 2 | Exact. | extra |\n"
            "## 5. Coverage\n"
        )
        self.assertTrue(any("nonempty" in error for error in section_four_result_table(malformed)[1]))
        repeated = (
            "## 4. Results\n"
            "| Result | Comparison |\n| --- | --- |\n"
            "| Theorem 1 | Exact. |\n| Theorem 1 | Exact. |\n"
            "## 5. Coverage\n"
        )
        self.assertTrue(any("repeats" in error for error in section_four_result_table(repeated)[1]))


if __name__ == "__main__":
    unittest.main()
