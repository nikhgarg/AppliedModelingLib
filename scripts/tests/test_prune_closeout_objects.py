from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from scripts.closeout_content_store import store_closeout_object
from scripts.prune_closeout_objects import (
    reachable_closeout_object_paths,
    unreferenced_closeout_objects,
)


class PruneCloseoutObjectsTests(unittest.TestCase):
    def test_only_unreferenced_objects_are_selected(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            trace = root / "papers" / "Fixture" / ".review_traces" / "plan.json"
            trace.parent.mkdir(parents=True)
            child = store_closeout_object(root, {"child": True}, kind="child")
            parent = store_closeout_object(
                root, {"child_reference": child}, kind="parent"
            )
            orphan = store_closeout_object(root, {"orphan": True}, kind="orphan")
            trace.write_text(json.dumps({"root": parent}), encoding="utf-8")

            reachable = reachable_closeout_object_paths(root)
            self.assertEqual(reachable, {parent["path"], child["path"]})
            self.assertEqual(
                [path.relative_to(root).as_posix() for path in unreferenced_closeout_objects(root)],
                [orphan["path"]],
            )


if __name__ == "__main__":
    unittest.main()
