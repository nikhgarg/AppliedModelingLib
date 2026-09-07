#!/usr/bin/env python3
"""Regression tests for machine-independent durable evidence identities."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.portable_evidence_identity import (
    PortableEvidenceIdentityError,
    portable_evidence_sha256,
    portable_lean_closure_identity,
    portable_semantic_hash_tool_identity,
)


class PortableEvidenceIdentityTests(unittest.TestCase):
    HASH_TOOL = {
        "schema": "1",
        "command": "sha256sum",
        "resolved_path": "/usr/bin/sha256sum",
        "executable_sha256": "a" * 64,
        "version_stdout_sha256": "b" * 64,
        "version_banner": "sha256sum fixture",
        "known_vector": "sha256(abc)",
        "known_vector_sha256": (
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        ),
    }

    def test_hash_tool_install_location_is_not_durable_evidence(self) -> None:
        first = portable_semantic_hash_tool_identity(self.HASH_TOOL)
        relocated = dict(self.HASH_TOOL, resolved_path="/opt/tools/sha256sum")
        second = portable_semantic_hash_tool_identity(relocated)
        self.assertEqual(first, second)
        self.assertNotIn("resolved_path", first)
        self.assertEqual(portable_evidence_sha256(first), portable_evidence_sha256(second))

    def test_hash_tool_bytes_and_behavior_remain_semantic_inputs(self) -> None:
        first = portable_semantic_hash_tool_identity(self.HASH_TOOL)
        changed = dict(self.HASH_TOOL, executable_sha256="c" * 64)
        second = portable_semantic_hash_tool_identity(changed)
        self.assertNotEqual(first, second)
        self.assertNotEqual(
            portable_evidence_sha256(first), portable_evidence_sha256(second)
        )

    def test_lean_closure_drops_runtime_search_and_stat_envelope(self) -> None:
        closure = {
            "schema": 1,
            "state": "present",
            "lean_import_closure": {
                "schema": "fixture",
                "entrypoint": "papers/Fixture.lean",
                "entry_module": "Fixture",
                "sources": [
                    {
                        "module": "Fixture",
                        "path": "papers/Fixture.lean",
                        "byte_length": 4,
                        "sha256": "d" * 64,
                    }
                ],
                "external_module_artifacts_sha256": "e" * 64,
            },
            "external_artifact_stats": {
                "lean_path_roots": ["/machine/one/.lake/packages"],
                "modules": [
                    {
                        "module": "Init",
                        "candidates": [
                            {
                                "absolute_path": "/machine/one/Init.olean",
                                "state": "present",
                                "target_stat": [1, 2, 3, 4, 5],
                            }
                        ],
                    }
                ],
            },
        }
        relocated = {
            **closure,
            "external_artifact_stats": {
                "lean_path_roots": ["/other/root/.lake/packages"],
                "modules": [
                    {
                        "module": "Init",
                        "candidates": [
                            {
                                "absolute_path": "/other/root/Init.olean",
                                "state": "present",
                                "target_stat": [9, 8, 7, 6, 5],
                            }
                        ],
                    }
                ],
            },
        }
        first = portable_lean_closure_identity(closure)
        second = portable_lean_closure_identity(relocated)
        self.assertEqual(first, second)
        self.assertEqual(portable_evidence_sha256(first), portable_evidence_sha256(second))

    def test_generic_durable_hasher_rejects_path_objects(self) -> None:
        with self.assertRaises(PortableEvidenceIdentityError):
            portable_evidence_sha256({"runtime": Path("/tmp/fixture")})


if __name__ == "__main__":
    unittest.main()
