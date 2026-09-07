"""Exact local and public excerpt readers have distinct, fail-closed authority."""

import hashlib
import tempfile
from pathlib import Path
from unittest import TestCase, mock

from scripts import source_display_projection as display
from scripts.dashboard_audit_inputs import DashboardAuditInputs, dashboard_audit_input_scope


class SourceDisplayProjectionTests(TestCase):
    def test_local_bytes_take_precedence_over_any_public_manifest(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            path = folder / "source.txt"
            path.write_text("Exact source.\n", encoding="utf-8")
            record = {"source_anchor_evidence": [{
                "path": "source.txt", "line_start": 1, "line_end": 1,
                "quoted_text": "Exact source.",
                "quoted_text_sha256": hashlib.sha256(b"Exact source.").hexdigest(),
            }]}
            with mock.patch.object(display, "public_source_display_projection_state",
                                   side_effect=AssertionError("public fallback")):
                self.assertEqual(display.source_anchor_display_state(folder, record),
                                 ("locally_byte_verified", ""))
                frozen = DashboardAuditInputs(
                    repository_root=root,
                    file_snapshots={"papers/Fixture/source.txt": path.read_bytes()},
                )
                path.write_text("Changed live source.\n", encoding="utf-8")
                with dashboard_audit_input_scope(frozen):
                    self.assertEqual(display.source_anchor_display_state(folder, record),
                                     ("locally_byte_verified", ""))

    def test_public_context_reordering_does_not_match_recorded_manifest(self):
        def anchor(quote):
            return {"publication_locator": "cited publication", "line_start": 1,
                    "line_end": 1, "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(quote.encode()).hexdigest()}
        contexts = [
            {"semantic_role": role, "source_anchor_evidence": [anchor(role)]}
            for role in ("definition", "scope")
        ]
        record = {"source_anchor_evidence": [anchor("claim")],
                  "semantic_context_requirements": contexts}
        manifest = {"source_anchors": [anchor("claim")], "semantic_context": [
            {"semantic_role": item["semantic_role"],
             "source_anchors": item["source_anchor_evidence"]}
            for item in contexts
        ]}
        self.assertEqual(display._public_display_record_matches_manifest(record, manifest, label="claim"), "")
        record["semantic_context_requirements"] = list(reversed(contexts))
        self.assertIn("semantic context does not match", display._public_display_record_matches_manifest(record, manifest, label="claim"))
