#!/usr/bin/env python3
"""Regressions for the narrow Lean graph-producer identity."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as evidence
from scripts.current_closeout import lean_review_graph as graph_contract
from scripts import lean_signature_manifest as manifest
from scripts.lean_declaration_graph_producer import (
    LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES,
    lean_declaration_graph_producer_identity,
)


class LeanDeclarationGraphProducerIdentityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        for index, relative in enumerate(LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES):
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"producer source {index}\n", encoding="utf-8")
        consumer = self.root / "scripts" / "lean_signature_manifest.py"
        consumer.write_text("consumer version one\n", encoding="utf-8")
        self.hash_tool = {
            "schema": 1,
            "sha256": "a" * 64,
            "byte_length": 1,
        }

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def identity(self) -> dict[str, object]:
        return lean_declaration_graph_producer_identity(
            self.root,
            semantic_hash_tool_identity=self.hash_tool,
        )

    def test_consumer_only_python_edit_does_not_change_producer_identity(self) -> None:
        before = self.identity()
        (self.root / "scripts" / "lean_signature_manifest.py").write_text(
            "consumer version two\n",
            encoding="utf-8",
        )
        self.assertEqual(self.identity(), before)
        self.assertNotIn(
            "scripts/lean_signature_manifest.py",
            {row["path"] for row in before["sources"]},
        )

    def test_native_graph_change_changes_producer_identity(self) -> None:
        before = self.identity()
        producer = self.root / LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES[0]
        producer.write_text("changed native graph\n", encoding="utf-8")
        self.assertNotEqual(self.identity(), before)

    def test_hash_tool_change_changes_producer_identity(self) -> None:
        before = self.identity()
        changed = lean_declaration_graph_producer_identity(
            self.root,
            semantic_hash_tool_identity={**self.hash_tool, "sha256": "b" * 64},
        )
        self.assertNotEqual(changed, before)

    def test_v11_checkpoint_uses_only_native_producer_sources(self) -> None:
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                manifest,
                "_semantic_contract_closure_hash_tool_identity",
                return_value=self.hash_tool,
            ),
            mock.patch.object(
                manifest,
                "portable_semantic_hash_tool_identity",
                return_value=self.hash_tool,
            ),
        ):
            projection = graph_contract.graph_engine_projection(self.root)
        self.assertEqual(
            [row["path"] for row in projection["sources"]],
            list(LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES),
        )

    def test_missing_native_source_fails_closed(self) -> None:
        (self.root / LEAN_DECLARATION_GRAPH_PRODUCER_SOURCES[-1]).unlink()
        with self.assertRaisesRegex(ValueError, "producer source is unavailable"):
            self.identity()


if __name__ == "__main__":
    unittest.main()
