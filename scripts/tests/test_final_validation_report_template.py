#!/usr/bin/env python3
"""Regression tests for the single human-facing validation-report template."""

from __future__ import annotations

import json
import os
import re
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

import audit_repository  # noqa: E402
import new_paper  # noqa: E402
from scripts import refresh_validation_report_audit_summaries as report_refresh  # noqa: E402


EXPECTED_FRONT_SECTIONS = [
    "Human Verdict",
    "Closeout Status",
    "Source and Scope",
    "Researcher Summary of Checked Results",
    "Remaining Boundaries and Gaps",
    "Additional Assumptions Beyond Paper",
    "Proof-Strategy Deviations",
    "Proof Tricks Worth Reusing",
    "Generalizations, Conjectures, and Extensions",
    "Source Clarifications and Exact Readings",
    "Paper Issues or Caveats",
]


class FinalValidationReportTemplateTests(unittest.TestCase):
    def test_scaffold_reads_authoritative_template(self) -> None:
        template = (
            ROOT / "papers" / "TEMPLATE" / "FINAL_VALIDATION_REPORT.md"
        ).read_text(encoding="utf-8")
        expected = template.replace(
            "# Final Validation Report: [Paper Short Name]",
            "# Final Validation Report: Example Paper",
            1,
        ).replace("papers/TEMPLATE", "papers/EX24Example")
        self.assertEqual(
            new_paper.final_validation_report_text("Example Paper", "EX24Example"),
            expected,
        )

    def test_authoritative_template_has_human_facing_front_sections_in_order(self) -> None:
        text = new_paper.final_validation_report_text("Example Paper", "EX24Example")
        positions = []
        for index, section in enumerate(EXPECTED_FRONT_SECTIONS, start=1):
            heading = f"## {index}. {section}"
            self.assertEqual(text.count(heading), 1, heading)
            positions.append(text.index(heading))
        self.assertEqual(positions, sorted(positions))

    def test_authoritative_template_placeholder_is_not_a_report_warning(self) -> None:
        findings = audit_repository.check_final_report_human_facing_front_matter(
            include_active=True,
            paper_filter="TEMPLATE",
        )
        self.assertEqual(findings, [])

    def test_every_report_starts_with_the_shared_human_facing_surface(self) -> None:
        for report in sorted((ROOT / "papers").glob("*/FINAL_VALIDATION_REPORT.md")):
            with self.subTest(report=report.parent.name):
                text = report.read_text(encoding="utf-8")
                headings = re.findall(r"(?m)^## (\d+)\. (.+)$", text)
                self.assertEqual(
                    headings[:4],
                    [
                        (str(index), section)
                        for index, section in enumerate(EXPECTED_FRONT_SECTIONS[:4], start=1)
                    ],
                )

    def test_generated_report_blocks_do_not_expose_machine_enum_labels(self) -> None:
        machine_labels = report_refresh.FORBIDDEN_RAW_ENUMS
        for report in report_refresh.public_report_paths():
            text = report.read_text(encoding="utf-8")
            markers_present = report_refresh.BEGIN in text or report_refresh.END in text
            if not markers_present:
                continue
            self.assertEqual(text.count(report_refresh.BEGIN), 1, report)
            self.assertEqual(text.count(report_refresh.END), 1, report)
            blocks = [text.split(report_refresh.BEGIN, 1)[1].split(report_refresh.END, 1)[0]]
            for _section, (_title, begin, end) in report_refresh.SECTION_BLOCKS.items():
                if begin not in text and end not in text:
                    continue
                self.assertEqual(text.count(begin), 1, report)
                self.assertEqual(text.count(end), 1, report)
                blocks.append(text.split(begin, 1)[1].split(end, 1)[0])
            block = "\n".join(blocks)
            for label in machine_labels:
                with self.subTest(report=report.parent.name, label=label):
                    self.assertIsNone(
                        re.search(
                            rf"(?<![A-Za-z0-9_]){re.escape(label)}(?![A-Za-z0-9_])",
                            block,
                        )
                    )

    def test_audit_requires_source_clarifications_front_section(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            report = new_paper.final_validation_report_text(
                "Example Paper", "EX24Example"
            ).replace("## 10. Source Clarifications and Exact Readings", "## Notes")
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
            with (
                mock.patch.object(
                    audit_repository, "paper_dirs", return_value=[folder]
                ),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = (
                    audit_repository.check_final_report_human_facing_front_matter(
                        include_active=True,
                        paper_filter=folder.name,
                    )
                )
            self.assertTrue(
                any("Source Clarifications and Exact Readings" in item.message for item in findings)
            )

    def test_status_alignment_rejects_markdown_wrapped_opposite_status(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "## 1. Human Verdict\n"
                "The old route was checked.\n\n"
                "## 2. Closeout Status\n"
                "- Completion status: `formalized`; historical claim.\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].severity, "ERROR")

    def test_report_reader_status_uses_public_catalog_and_preserves_private_status(self) -> None:
        cases = [
            ("GJ19", "public", "partially formalized", "formalized", True),
            ("MSVV07", "public", "conditional", "formalized", True),
            ("GJ19", "public", "partially formalized", "partially formalized", False),
            ("LOS02", "public", "partially formalized", "partially formalized", True),
            ("LMMS04", "public", "conditional", "partially formalized", True),
            ("LOS02", "public", "formalized", "formalized", True),
            ("SNVD17", "private_only", "partially formalized", "partially formalized", True),
            ("SNVD17", "private_only", "partially formalized", "formalized", False),
            ("Draft", "public", "paper draft", "formalized", False),
        ]
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers").mkdir()
            (root / "papers/catalog.json").write_text(json.dumps({
                "schema": 1, "preserve_partial_status": ["LOS02", "LMMS04"],
            }), encoding="utf-8")
            for paper, visibility, technical, reader, passes in cases:
                with self.subTest(paper=paper, technical=technical, reader=reader):
                    folder = root / "papers" / paper
                    folder.mkdir(exist_ok=True)
                    status_text = json.dumps({
                        "id": paper, "repository_visibility": visibility, "status": technical,
                    })
                    status_file = folder / "status.json"
                    status_file.write_text(status_text, encoding="utf-8")
                    (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                        f"## 2. Closeout Status\n\n- Completion status: **{reader}**.\n",
                        encoding="utf-8",
                    )
                    with (
                        mock.patch.dict(os.environ, {"APPLIEDMODELINGLIB_REPO_ROOT": str(root)}),
                        mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                        mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
                    ):
                        findings = audit_repository.check_final_report_status_alignment(
                            include_active=True, paper_filter=paper
                        )
                    self.assertEqual(not findings, passes, findings)
                    self.assertEqual(status_file.read_text(encoding="utf-8"), status_text)

    def test_status_alignment_ignores_historical_status_outside_closeout_section(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "## 1. Human Verdict\nCurrent boundary remains open.\n\n"
                "## 2. Closeout Status\n"
                "- **Completion status**: `partially formalized`.\n\n"
                "## 12. Detailed Formalization Evidence\n"
                "Historical note: Completion status: formalized.\n"
                "```text\nCompletion status: formalized\n```\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertEqual(findings, [])

    def test_status_alignment_ignores_fenced_fake_closeout_section(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "```markdown\n"
                "## 2. Closeout Status\n"
                "- Completion status: formalized.\n"
                "```\n\n"
                "## 2. Closeout Status\n"
                "- Completion status: partially formalized.\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertEqual(findings, [])

    def test_status_alignment_rejects_two_current_statuses(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "## 2. Closeout Status\n"
                "- Completion status: formalized.\n"
                "- Lean formalization status: partially formalized.\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertTrue(
                any("mutually exclusive" in finding.message for finding in findings)
            )

    def test_status_alignment_rejects_formalized_claim_for_paper_draft(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "paper draft"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "## 2. Closeout Status\n"
                "- Completion status: formalized.\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].severity, "ERROR")

    def test_status_alignment_requires_parseable_controlled_status(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "EX24Example"
            folder.mkdir()
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "# Final Validation Report: Example\n\n"
                "## 2. Closeout Status\n"
                "The report has not stated a controlled completion status.\n",
                encoding="utf-8",
            )
            with (
                mock.patch.object(audit_repository, "paper_dirs", return_value=[folder]),
                mock.patch.object(audit_repository, "ACTIVE_PAPERS", set()),
            ):
                findings = audit_repository.check_final_report_status_alignment(
                    include_active=True, paper_filter=folder.name
                )
            self.assertEqual(len(findings), 1)
            self.assertEqual(findings[0].severity, "ERROR")
            self.assertIn("no parseable controlled", findings[0].message)

    def test_closeout_status_predicate_rejects_unrecognized_favorable_prefix(self) -> None:
        self.assertFalse(audit_repository.is_closeout_status("formalized-but-unverified"))
        self.assertFalse(audit_repository.is_closeout_status("formalized pending audit"))
        self.assertTrue(audit_repository.is_closeout_status("formalized"))
        self.assertTrue(audit_repository.is_closeout_status("formalized with caveat"))


if __name__ == "__main__":
    unittest.main()
