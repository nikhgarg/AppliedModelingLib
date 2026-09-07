from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.foundation_registry import (
    REGISTRY_RELATIVE_PATH,
    load_foundation_registry,
)

ROOT = Path(__file__).resolve().parents[2]


class FoundationRegistryTests(unittest.TestCase):
    def test_repository_registry_is_small_and_canonical(self) -> None:
        registry = load_foundation_registry(ROOT)
        self.assertEqual(registry.policy_id, "trusted-foundation-packages-v1")
        self.assertIn("Mathlib", registry.module_roots)
        self.assertNotIn("AppliedModelingLib", registry.module_roots)
        self.assertNotIn("Cslib", registry.module_roots)
        self.assertLessEqual(len(registry.packages), 8)
        self.assertEqual(len(registry.sha256), 64)

    def test_workspace_namespace_fails_closed(self) -> None:
        payload = json.loads((ROOT / REGISTRY_RELATIVE_PATH).read_text(encoding="utf-8"))
        payload["packages"].append(
            {
                "module_root": "AppliedModelingLib",
                "category": "trusted_mathematics_foundation",
                "semantic_policy": "default_trust_with_reviewable_semantic_expansion",
            }
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / REGISTRY_RELATIVE_PATH
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_foundation_registry(root)

    def test_unreviewed_policy_fails_closed(self) -> None:
        payload = json.loads((ROOT / REGISTRY_RELATIVE_PATH).read_text(encoding="utf-8"))
        payload["packages"][0]["semantic_policy"] = "trust_everything_by_name"
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / REGISTRY_RELATIVE_PATH
            path.parent.mkdir(parents=True)
            path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaises(ValueError):
                load_foundation_registry(root)



if __name__ == "__main__":
    unittest.main()
