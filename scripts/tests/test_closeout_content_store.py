from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.closeout_content_store import (
    CloseoutContentStoreError,
    load_closeout_object,
    store_closeout_object,
)


class CloseoutContentStoreTests(unittest.TestCase):
    def test_exact_payload_is_deduplicated_and_round_trips(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            payload = {"large": [3, 2, 1], "nested": {"ok": True}}
            first = store_closeout_object(root, payload, kind="fixture")
            second = store_closeout_object(root, payload, kind="fixture")
            self.assertEqual(first, second)
            self.assertEqual(
                load_closeout_object(root, first, expected_kind="fixture"), payload
            )
            self.assertLess(len(json.dumps(first)), 400)

    def test_tampered_object_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            reference = store_closeout_object(root, {"value": 1}, kind="fixture")
            (root / reference["path"]).write_text('{"value":2}\n', encoding="utf-8")
            with self.assertRaises(CloseoutContentStoreError):
                load_closeout_object(root, reference, expected_kind="fixture")

    def test_reference_cannot_escape_store_contract(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            reference = store_closeout_object(root, {"value": 1}, kind="fixture")
            escaped = dict(reference)
            escaped["path"] = "../outside.json"
            with self.assertRaises(CloseoutContentStoreError):
                load_closeout_object(root, escaped, expected_kind="fixture")


if __name__ == "__main__":
    unittest.main()
