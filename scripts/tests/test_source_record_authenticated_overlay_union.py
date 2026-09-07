#!/usr/bin/env python3
"""Focused tests for loader-owned current overlay unioning."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_authenticated_overlay_union as UNION  # noqa: E402


class _LoadedItem(dict[str, object]):
    pass


def _module(
    loader_name: str,
    capability_name: str,
    items: dict[str, object],
) -> SimpleNamespace:
    def load(*_args: object, **_kwargs: object) -> dict[str, object]:
        return items

    def copy_loaded(
        value: object, updates: dict[str, object] | None = None
    ) -> _LoadedItem:
        copied = dict(value) if isinstance(value, dict) else {}
        if updates:
            copied.update(updates)
        return _LoadedItem(copied)

    return SimpleNamespace(
        **{
            loader_name: load,
            capability_name: lambda value: isinstance(value, _LoadedItem),
            capability_name.replace("is_", "copy_", 1): copy_loaded,
        }
    )


def _modules(
    *,
    differential: dict[str, object] | None = None,
    semantic_rebind: dict[str, object] | None = None,
    semantic_receipt_exists: bool = False,
    semantic_prepare: object | None = None,
) -> dict[str, SimpleNamespace]:
    semantic_path = SimpleNamespace(is_file=lambda: semantic_receipt_exists)
    semantic = _module(
        "load_current_source_record_semantic_rebind_items",
        "is_loaded_source_record_semantic_rebind_item",
        semantic_rebind or {},
    )
    semantic.source_record_semantic_rebind_overlay_path = lambda _paper_dir: semantic_path
    semantic.prepare_current_source_record_semantic_rebind_identity_context = (
        semantic_prepare if semantic_prepare is not None else lambda *_args: object()
    )
    return {
        "differential": _module(
            "load_current_source_record_differential_revalidation_items",
            "is_loaded_source_record_differential_revalidation_item",
            differential or {},
        ),
        "semantic_rebind": semantic,
    }


def _identity_evidence(
    *,
    context: object | None = None,
    prepare: object | None = None,
) -> SimpleNamespace:
    """Minimal neutral issuer fixture for synthetic overlay-lane tests."""

    issued = context if context is not None else object()

    def issue(*_args: object, **_kwargs: object) -> object:
        if callable(prepare):
            return prepare(*_args, **_kwargs)
        return issued

    return SimpleNamespace(
        prepare_current_source_record_identity_context=issue,
        current_source_record_identity_context_error=(
            lambda *_args, **_kwargs: ""
        ),
    )


class SourceRecordAuthenticatedOverlayUnionTests(unittest.TestCase):
    def test_protocol_inventory_and_marker_detection_are_data_only(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            paper_dir = Path(tmpdir) / "papers" / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            protocol = UNION.SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL["differential"]
            (audit_dir / protocol.filename).write_text("{}", encoding="utf-8")
            self.assertEqual(
                UNION.source_record_overlay_labels_with_artifacts(paper_dir),
                ("differential",),
            )
            self.assertEqual(
                UNION.serialized_source_record_overlay_labels(
                    {protocol.item_field: {"serialized": True}}
                ),
                ("differential",),
            )

    def test_strict_union_includes_distinct_semantic_rebind_lane(self) -> None:
        differential = {"current differential group": _LoadedItem({"id": 1})}
        semantic_rebind = {"current semantic rebind group": _LoadedItem({"id": 2})}
        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(
                    differential=differential,
                    semantic_rebind=semantic_rebind,
                    semantic_receipt_exists=True,
                ),
            ),
            patch.object(
                UNION,
                "source_record_overlay_labels_with_artifacts",
                return_value=("semantic_rebind",),
            ),
            patch.object(UNION, "_evidence_module", return_value=_identity_evidence()),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
            actual = UNION.strict_authenticated_current_overlay_union(lanes)
        self.assertEqual(set(actual), set(differential) | set(semantic_rebind))
        self.assertEqual(
            [lane.label for lane in lanes],
            [
                "semantic_rebind",
                "differential",
            ],
        )

    def test_strict_union_rejects_cross_lane_collision(self) -> None:
        shared = "one current semantic group"
        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(
                    differential={shared: _LoadedItem({"id": 1})},
                    semantic_rebind={shared: _LoadedItem({"id": 2})},
                    semantic_receipt_exists=True,
                ),
            ),
            patch.object(
                UNION,
                "source_record_overlay_labels_with_artifacts",
                return_value=("semantic_rebind",),
            ),
            patch.object(UNION, "_evidence_module", return_value=_identity_evidence()),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
            with self.assertRaisesRegex(
                UNION.SourceRecordAuthenticatedOverlayUnionError,
                "overlap at current semantic group",
            ):
                UNION.strict_authenticated_current_overlay_union(lanes)

    def test_lane_owned_copy_retains_capability_and_rejects_foreign_item(self) -> None:
        original = _LoadedItem({"id": 1})
        with patch.object(
            UNION,
            "_overlay_modules",
            return_value=_modules(differential={"current group": original}),
        ):
            lane = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"),
                "FixturePaper",
                {"paper": "FixturePaper"},
                lane_labels=("differential",),
            )[0]
        copied = UNION.copy_authenticated_current_overlay_item(
            lane, original, {"normalized": True}
        )
        self.assertTrue(lane._is_loaded(copied))
        self.assertTrue(copied["normalized"])
        with self.assertRaisesRegex(
            UNION.SourceRecordAuthenticatedOverlayUnionError,
            "outside its loaded lane",
        ):
            UNION.copy_authenticated_current_overlay_item(
                lane, _LoadedItem({"id": 2})
            )

    def test_union_rejects_a_plain_serialized_provenance_mapping(self) -> None:
        with patch.object(
            UNION,
            "_overlay_modules",
            return_value=_modules(
                differential={"current group": {"provenance": "forged"}},
            ),
        ), self.assertRaisesRegex(
            UNION.SourceRecordAuthenticatedOverlayUnionError,
            "without its private capability",
        ):
            UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )

    def test_strict_union_rejects_a_caller_constructed_lane(self) -> None:
        forged = UNION.AuthenticatedCurrentOverlayLane(
            label="differential",
            items={"current group": _LoadedItem({"id": 1})},
            _loader_token=object(),
            _is_loaded=lambda value: isinstance(value, _LoadedItem),
            _copy_loaded=lambda value, updates=None: _LoadedItem(
                {**dict(value), **dict(updates or {})}
            ),
            _issued_items=[],
        )
        with self.assertRaisesRegex(
            UNION.SourceRecordAuthenticatedOverlayUnionError,
                "without loader authority",
            ):
                UNION.strict_authenticated_current_overlay_union((forged,))

    def test_default_union_has_only_differential_without_artifacts(self) -> None:
        with patch.object(UNION, "_overlay_modules", return_value=_modules()):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
        self.assertEqual(
            [lane.label for lane in lanes],
            [
                "differential",
            ],
        )

    def test_neutral_identity_context_is_prepared_once_for_semantic_lane(
        self,
    ) -> None:
        context = object()
        calls: list[object] = []

        def prepare(*_args: object, **_kwargs: object) -> object:
            calls.append("prepare")
            return context

        modules = _modules(
            semantic_rebind={"exact rebound group": _LoadedItem({"id": 2})},
            semantic_receipt_exists=True,
        )
        semantic = modules["semantic_rebind"]
        original_load = semantic.load_current_source_record_semantic_rebind_items

        def load(*args: object, **kwargs: object) -> object:
            calls.append(kwargs.get("source_record_identity_context"))
            return original_load(*args, **kwargs)

        semantic.load_current_source_record_semantic_rebind_items = load
        with (
            patch.object(UNION, "_overlay_modules", return_value=modules),
            patch.object(
                UNION,
                "source_record_overlay_labels_with_artifacts",
                return_value=("semantic_rebind",),
            ),
            patch.object(
                UNION,
                "_evidence_module",
                return_value=_identity_evidence(context=context, prepare=prepare),
            ),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )
        self.assertEqual(calls.count("prepare"), 1)
        self.assertIn(context, calls)
        self.assertEqual(
            set(UNION.strict_authenticated_current_overlay_union(lanes)),
            {"exact rebound group"},
        )

    def test_unselected_semantic_lane_does_not_prepare_an_identity_context(self) -> None:
        calls: list[str] = []

        def prepare(*_args: object) -> object:
            calls.append("prepare")
            return object()

        with patch.object(
            UNION,
            "_overlay_modules",
            return_value=_modules(
                semantic_receipt_exists=True,
                semantic_prepare=prepare,
            ),
        ):
            lanes = UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"),
                "FixturePaper",
                {"paper": "FixturePaper"},
                lane_labels=("differential",),
            )
        self.assertEqual([lane.label for lane in lanes], ["differential"])
        self.assertEqual(calls, [])

    def test_deferred_semantic_identity_refuses_the_entire_overlay_union(self) -> None:
        """A busy identity gate must not look like an empty optional lane."""

        def deferred(*_args: object, **_kwargs: object) -> object:
            raise RuntimeError(
                "source-record identity revalidation deferred: source-record scan busy"
            )

        with (
            patch.object(
                UNION,
                "_overlay_modules",
                return_value=_modules(semantic_receipt_exists=True),
            ),
            patch.object(
                UNION,
                "source_record_overlay_labels_with_artifacts",
                return_value=("semantic_rebind",),
            ),
            patch.object(
                UNION,
                "_evidence_module",
                return_value=_identity_evidence(prepare=deferred),
            ),
            self.assertRaisesRegex(
                UNION.SourceRecordAuthenticatedOverlayUnionError,
                "identity revalidation deferred",
            ),
        ):
            UNION.load_authenticated_current_overlay_lanes(
                Path("/paper"), "FixturePaper", {"paper": "FixturePaper"}
            )

if __name__ == "__main__":
    unittest.main()
