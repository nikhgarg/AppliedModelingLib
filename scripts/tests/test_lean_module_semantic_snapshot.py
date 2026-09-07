#!/usr/bin/env python3
"""Regression tests for Lean-owned physical-move semantic snapshots."""

from __future__ import annotations

import unittest
from pathlib import Path
from unittest.mock import patch

from scripts import lean_module_semantic_snapshot as snapshot


class LeanModuleSemanticSnapshotTests(unittest.TestCase):
    def test_full_project_closure_is_the_semantic_workspace(self) -> None:
        """A file split must not turn an outside-batch helper into an opaque name."""

        modules = (
            "AppliedModelingLib.Foundation",
            "AppliedModelingLib.Model",
        )
        workspace = (
            "AppliedModelingLib.Dependency",
            *modules,
        )
        declaration = "AppliedModelingLib.Model.sourceTheorem"
        discovery = {"source_declarations": [declaration]}
        signed = {
            "semantic_signatures": {
                "schema": "1",
                "items": [
                    {
                        "declaration": declaration,
                        "elaborated_signature_sha256": "a" * 64,
                    }
                ],
                "errors": [],
            },
            "declarations": [
                {
                    "declaration": declaration,
                    "declaration_kind": "theorem",
                    "module": "AppliedModelingLib.Model",
                    "source_presented": True,
                    "generated_from_owner": False,
                    "review_owner_declaration": declaration,
                }
            ],
        }

        class FakeProvider:
            def repository_source_snapshot(self, import_module: str):
                self.import_module = import_module
                return tuple(
                    (module, Path(module), b"", "a" * 64)
                    for module in workspace
                )

            def finalize_unchanged(self) -> bool:
                return True

        provider = FakeProvider()

        with (
            patch.object(
                snapshot,
                "RepositoryBuildInputSnapshotProvider",
                return_value=provider,
            ),
            patch.object(
                snapshot,
                "run_lean_declaration_inventory",
                side_effect=(discovery, signed),
            ) as inventory,
        ):
            result = snapshot.build_snapshot(
                Path("/repository"),
                "AppliedModelingLib.AllForSemanticInventory",
                modules,
                timeout_seconds=10,
                build_timeout_seconds=10,
            )

        self.assertEqual(inventory.call_count, 2)
        self.assertEqual(
            provider.import_module,
            "AppliedModelingLib.AllForSemanticInventory",
        )
        for call in inventory.call_args_list:
            self.assertEqual(call.kwargs["workspace_module_names"], workspace)
            self.assertEqual(call.kwargs["semantic_manifest_modules"], workspace)
        self.assertEqual(result["source_declaration_count"], 1)
        self.assertEqual(
            result["semantic_items"][0]["portable_name"],
            "$PROJECT.Model.sourceTheorem",
        )


if __name__ == "__main__":
    unittest.main()
