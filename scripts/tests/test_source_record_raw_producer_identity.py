#!/usr/bin/env python3
"""Tests for path-normalized raw-producer provenance discovery."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.source_record_raw_producer_identity import (
    SOURCE_RECORD_RAW_PRODUCER_BEGIN_MARKER,
    SOURCE_RECORD_RAW_PRODUCER_END_MARKER,
    raw_generation_code_identity,
)


class RawProducerIdentityImportTests(unittest.TestCase):
    def _identity(self, entry_text: str, modules: dict[str, str]) -> dict[str, str]:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            entry = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
            entry.parent.mkdir(parents=True)
            entry.write_text(entry_text, encoding="utf-8")
            for relative, text in modules.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(text, encoding="utf-8")

            def read_bytes(relative: str) -> bytes | None:
                path = root / relative
                return path.read_bytes() if path.is_file() else None

            return raw_generation_code_identity(read_bytes)

    @staticmethod
    def _entry(import_block: str) -> str:
        return (
            import_block
            + "\n\n"
            + "def _run_audit():\n"
            + f"    {SOURCE_RECORD_RAW_PRODUCER_BEGIN_MARKER}\n"
            + "    result = produce()\n"
            + f"    {SOURCE_RECORD_RAW_PRODUCER_END_MARKER}\n"
            + "    return result\n"
        )

    def test_guarded_direct_and_package_imports_resolve_to_one_module(self) -> None:
        identity = self._identity(
            self._entry(
                "try:\n"
                "    from helper import produce\n"
                "except ModuleNotFoundError:\n"
                "    from scripts.helper import produce"
            ),
            {"scripts/helper.py": "def produce():\n    return 1\n"},
        )

        self.assertEqual(identity["status"], "present")
        self.assertEqual(len(identity["sha256"]), 64)

    def test_guarded_imports_to_different_modules_fail_closed(self) -> None:
        identity = self._identity(
            self._entry(
                "try:\n"
                "    from scripts.first import produce\n"
                "except ModuleNotFoundError:\n"
                "    from scripts.second import produce"
            ),
            {
                "scripts/first.py": "def produce():\n    return 1\n",
                "scripts/second.py": "def produce():\n    return 2\n",
            },
        )

        self.assertEqual(identity["status"], "unavailable")
        self.assertEqual(identity["sha256"], "")


if __name__ == "__main__":
    unittest.main()
