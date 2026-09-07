from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import source_spec_protocol as protocol


class SourceSpecProtocolTests(unittest.TestCase):
    def test_explicit_selection_never_consults_legacy_baseline(self) -> None:
        with mock.patch.object(
            protocol,
            "theorem_realization_reissue_requirement",
        ) as transition:
            selected = protocol.source_spec_correspondence_requested(
                {"review_surface": {"require_source_spec_correspondence": True}}
            )

        self.assertTrue(selected)
        transition.assert_not_called()

    def test_repository_paper_uses_the_shared_automatic_transition(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(protocol, "ROOT", root),
                mock.patch.object(
                    protocol,
                    "theorem_realization_reissue_requirement",
                    return_value=SimpleNamespace(required=True),
                ) as transition,
            ):
                selected = protocol.source_spec_correspondence_requested(
                    {"status": "formalized"}, folder=folder
                )

        self.assertTrue(selected)
        transition.assert_called_once()

    def test_isolated_tree_retains_explicit_switch_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            with mock.patch.object(
                protocol,
                "theorem_realization_reissue_requirement",
            ) as transition:
                selected = protocol.source_spec_correspondence_requested(
                    {"status": "formalized"}, folder=folder
                )

        self.assertFalse(selected)
        transition.assert_not_called()

    def test_unavailable_automatic_transition_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(protocol, "ROOT", root),
                mock.patch.object(
                    protocol,
                    "theorem_realization_reissue_requirement",
                    side_effect=RuntimeError("unavailable"),
                ),
            ):
                selected = protocol.source_spec_correspondence_requested(
                    {"status": "formalized"}, folder=folder
                )

        self.assertTrue(selected)


if __name__ == "__main__":
    unittest.main()
