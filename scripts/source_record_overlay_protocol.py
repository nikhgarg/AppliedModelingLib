#!/usr/bin/env python3
"""Data-only registry for current source-record overlay transports.

The filenames and item-marker fields below are serialization protocol, not
evidence.  A marker only tells a reader that an ordinary JSON item is trying
to use an overlay transport; it never authenticates that item.  Authentication
remains the private in-memory capability issued by the corresponding loader.

Keeping this registry independent of every loader lets ordinary sidecar
readers reject copied overlay JSON without importing thousands of lines of
historical migration code.  It also gives all consumers one artifact inventory
instead of five locally repeated filename/marker lists.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Mapping


@dataclass(frozen=True)
class SourceRecordOverlayProtocol:
    """One named serialized transport surface."""

    label: str
    module_name: str
    filename: str
    item_field: str
    loader_function: str
    capability_function: str
    copy_function: str
    replay_without_artifact: bool = False


SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME = (
    "source_record_differential_revalidation.json"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD = (
    "source_record_differential_revalidation"
)
SOURCE_RECORD_SEMANTIC_REBIND_FILENAME = "source_record_semantic_rebind.json"
SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD = "source_record_semantic_rebind"


# Registry order is loader order, not evidence precedence.  Every consumer
# that composes accepted responses must state its collision precedence
# explicitly after the selected loaders have authenticated their own lanes.
SOURCE_RECORD_OVERLAY_PROTOCOLS = (
    SourceRecordOverlayProtocol(
        "semantic_rebind",
        "source_record_semantic_rebind",
        SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
        SOURCE_RECORD_SEMANTIC_REBIND_ITEM_FIELD,
        "load_current_source_record_semantic_rebind_items",
        "is_loaded_source_record_semantic_rebind_item",
        "copy_loaded_source_record_semantic_rebind_item",
    ),
    SourceRecordOverlayProtocol(
        "differential",
        "source_record_differential_revalidation",
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME,
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD,
        "load_current_source_record_differential_revalidation_items",
        "is_loaded_source_record_differential_revalidation_item",
        "copy_loaded_source_record_differential_revalidation_item",
        replay_without_artifact=True,
    ),
)
SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL = {
    protocol.label: protocol for protocol in SOURCE_RECORD_OVERLAY_PROTOCOLS
}


def source_record_overlay_labels_with_artifacts(
    paper_dir: Path,
    *,
    lane_labels: Iterable[str] | None = None,
) -> tuple[str, ...]:
    """Return selected lanes whose canonical receipt artifact exists.

    This is a cheap inventory only.  It grants no evidence credit and does not
    parse a receipt.  A caller that needs current responses must still invoke
    the authenticated loader union.
    """

    requested = (
        set(SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL)
        if lane_labels is None
        else {str(label or "").strip() for label in lane_labels}
    )
    if "" in requested or not requested.issubset(SOURCE_RECORD_OVERLAY_PROTOCOL_BY_LABEL):
        raise ValueError("source-record overlay inventory names an unknown or empty lane")
    return tuple(
        protocol.label
        for protocol in SOURCE_RECORD_OVERLAY_PROTOCOLS
        if protocol.label in requested
        and (paper_dir / "audit" / protocol.filename).is_file()
    )


def serialized_source_record_overlay_labels(value: object) -> tuple[str, ...]:
    """Recognize serialized overlay markers without trusting them."""

    if not isinstance(value, Mapping):
        return ()
    return tuple(
        protocol.label
        for protocol in SOURCE_RECORD_OVERLAY_PROTOCOLS
        if isinstance(value.get(protocol.item_field), Mapping)
    )
