#!/usr/bin/env python3
"""Regression tests for archive-derived canonical text source surfaces."""

from __future__ import annotations

import hashlib
import io
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as integrity  # noqa: E402
from scripts import source_archive_surface as archive_surface  # noqa: E402
from scripts import source_coverage_scope as coverage  # noqa: E402
from scripts import migrate_archive_source_surface as migration  # noqa: E402


def sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


class SourceArchiveSurfaceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        self.member = (
            b"\\begin{theorem}\\label{thm:fixture}\n"
            b"Every fixture has a witness.\n"
            b"\\end{theorem}\n"
        )
        self.archive = self.paper / "source.tar"
        with tarfile.open(self.archive, "w") as handle:
            info = tarfile.TarInfo("main.tex")
            info.size = len(self.member)
            handle.addfile(info, io.BytesIO(self.member))
        self.surface = self.paper / "audit" / "source_archive_surface.tex"
        self.surface.write_text(
            archive_surface.render_archive_surface(
                [("main.tex", self.member.decode("utf-8"))]
            ),
            encoding="utf-8",
        )

    def payload(self) -> dict[str, object]:
        text = self.surface.read_text(encoding="utf-8")
        quote = "\n".join(text.splitlines()[1:4])
        return {
            "source_coverage_mode": "named_theoretical_statements",
            "source_artifact_path": "audit/source_archive_surface.tex",
            "source_artifact_sha256": sha256(self.surface.read_bytes()),
            "source_archive_surface": {
                "schema": 1,
                "generator": "archive-members-normalized-text-v1",
                "archive": {"path": "source.tar", "sha256": sha256(self.archive.read_bytes())},
                "members": [{"path": "main.tex", "sha256": sha256(self.member)}],
            },
            "source_named_result_inventory_review": {
                "environment_kinds": {"theorem": "theorem"},
                "heading_kinds": {},
            },
            "items": {
                "opaque_fixture": {
                    "source_kind": "theorem",
                    "source_location": "audit/source_archive_surface.tex:2-4",
                    "source_anchor_evidence": [
                        {
                            "path": "audit/source_archive_surface.tex",
                            "line_start": 2,
                            "line_end": 4,
                            "quoted_text": quote,
                            "quoted_text_sha256": sha256(quote.encode("utf-8")),
                        }
                    ],
                }
            },
        }

    def test_archive_surface_is_reconstructed_before_source_selection(self) -> None:
        payload = self.payload()
        self.assertEqual(
            archive_surface.source_archive_surface_validation_issues(
                self.paper, payload, repository_root=self.root
            ),
            [],
        )
        previous_root = integrity.ROOT
        integrity.ROOT = self.root
        self.addCleanup(setattr, integrity, "ROOT", previous_root)
        self.assertEqual(
            integrity.source_artifact_pin_findings(
                self.paper,
                "formalized",
                self.paper / "audit" / "paper_statement_map.json",
                payload,
            ),
            [],
        )
        self.assertEqual(
            coverage.source_index_byte_pinned_anchor_item_ids(
                self.paper,
                payload,
                "named_theoretical_statements",
                repository_root=self.root,
            ),
            {"opaque_fixture"},
        )

    def test_tampered_derived_surface_and_archive_member_fail_closed(self) -> None:
        payload = self.payload()
        self.surface.write_text("replacement\n", encoding="utf-8")
        messages = [
            issue.message
            for issue in archive_surface.source_archive_surface_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(any("do not equal" in message for message in messages), messages)

        self.surface.write_text(
            archive_surface.render_archive_surface(
                [("main.tex", self.member.decode("utf-8"))]
            ),
            encoding="utf-8",
        )
        with tarfile.open(self.archive, "w") as handle:
            replacement = b"replacement"
            info = tarfile.TarInfo("main.tex")
            info.size = len(replacement)
            handle.addfile(info, io.BytesIO(replacement))
        messages = [
            issue.message
            for issue in archive_surface.source_archive_surface_validation_issues(
                self.paper, payload, repository_root=self.root
            )
        ]
        self.assertTrue(any("archive.sha256" in message for message in messages), messages)

    def test_structural_checkout_only_relaxes_missing_bytes(self) -> None:
        payload = self.payload()
        self.surface.unlink()
        self.archive.unlink()
        issues = archive_surface.source_archive_surface_validation_issues(
            self.paper,
            payload,
            repository_root=self.root,
            require_source_bytes=False,
        )
        self.assertTrue(issues)
        self.assertTrue(all(issue.missing_bytes for issue in issues), issues)

    def test_migration_rewrites_both_tex_and_archive_member_coordinates(self) -> None:
        legacy = {
            "source_coverage_mode": "named_theoretical_statements",
            "source_artifact_path": "source.tar",
            "source_artifact_sha256": sha256(self.archive.read_bytes()),
            "items": {
                "tex_source": {
                    "source_location": "source_tex/main.tex:1-3",
                },
                "archived_transcript": {
                    "source_location": "source.tar member main.tex, extracted lines 1-3; source",
                },
            },
        }
        surface, changes = migration.migrate_payload(
            self.paper,
            legacy,
            member_mapping={"source_tex/main.tex": "main.tex", "main.tex": "main.tex"},
            surface_path="audit/source_archive_surface.tex",
        )
        # Two legacy spellings may point to one exact archive member; the
        # canonical surface still includes that member only once.
        self.assertEqual(changes, 2)
        self.assertEqual(
            legacy["items"]["tex_source"]["source_location"],
            "audit/source_archive_surface.tex:2-4",
        )
        self.assertEqual(
            legacy["items"]["archived_transcript"]["source_location"],
            "audit/source_archive_surface.tex:2-4; source",
        )
        self.surface.write_text(surface, encoding="utf-8")
        self.assertEqual(
            archive_surface.source_archive_surface_validation_issues(
                self.paper, legacy, repository_root=self.root
            ),
            [],
        )

    def test_migration_preserves_offsets_after_member_without_final_newline(self) -> None:
        second_member = b"The second source claim has no final newline."
        with tarfile.open(self.archive, "w") as handle:
            for name, raw in (("first.tex", self.member), ("second.tex", second_member)):
                info = tarfile.TarInfo(name)
                info.size = len(raw)
                handle.addfile(info, io.BytesIO(raw))
        legacy = {
            "source_artifact_path": "source.tar",
            "source_artifact_sha256": sha256(self.archive.read_bytes()),
            "items": {
                "first": {"source_location": "source_tex/first.tex:1-3"},
                "second": {"source_location": "source_tex/second.tex:1"},
            },
        }
        surface, changes = migration.migrate_payload(
            self.paper,
            legacy,
            member_mapping={
                "source_tex/first.tex": "first.tex",
                "source_tex/second.tex": "second.tex",
            },
            surface_path="audit/source_archive_surface.tex",
        )
        self.assertEqual(changes, 2)
        self.assertEqual(
            legacy["items"]["first"]["source_location"],
            "audit/source_archive_surface.tex:2-4",
        )
        self.assertEqual(
            legacy["items"]["second"]["source_location"],
            "audit/source_archive_surface.tex:7",
        )
        self.surface.write_text(surface, encoding="utf-8")
        self.assertEqual(
            archive_surface.source_archive_surface_validation_issues(
                self.paper, legacy, repository_root=self.root
            ),
            [],
        )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
