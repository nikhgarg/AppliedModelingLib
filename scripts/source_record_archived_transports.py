#!/usr/bin/env python3
"""Fail-closed identities for source-record transports retired to Git history.

No tracked paper artifact uses these transports.  Current consumers reject a
serialized item carrying either marker instead of preserving a dormant loader
that could grant historical evidence current acceptance credit.
"""

from __future__ import annotations

from pathlib import Path
from typing import Mapping


ARCHIVED_SOURCE_RECORD_TRANSPORT_ITEM_FIELDS = frozenset(
    {
        "source_record_attested_selected_semantic_reuse",
        "source_record_component_projection",
        "source_record_historical_descriptor_migration",
        "source_record_schema4_to5_migration",
        "source_record_scoped_receipt_rebind",
    }
)

ARCHIVED_SOURCE_RECORD_TRANSPORT_FILENAMES = frozenset(
    {
        "source_record_attested_selected_semantic_reuse.json",
        "source_record_component_projection.json",
        "source_record_historical_descriptor_migration.json",
        "source_record_schema4_to5_migration.json",
        "source_record_scoped_receipt_rebind.json",
    }
)


def archived_source_record_transport_item_field(value: object) -> str:
    """Return the exact retired capability marker on a serialized item."""

    if not isinstance(value, Mapping):
        return ""
    return next(
        (
            field
            for field in sorted(ARCHIVED_SOURCE_RECORD_TRANSPORT_ITEM_FIELDS)
            if field in value
        ),
        "",
    )


def archived_source_record_transport_artifacts(paper_dir: Path) -> tuple[Path, ...]:
    """Return retired transport artifacts that require a fresh evidence lane."""

    candidates = (
        paper_dir / filename
        for filename in sorted(ARCHIVED_SOURCE_RECORD_TRANSPORT_FILENAMES)
    )
    audit_candidates = (
        paper_dir / "audit" / filename
        for filename in sorted(ARCHIVED_SOURCE_RECORD_TRANSPORT_FILENAMES)
    )
    return tuple(path for path in (*candidates, *audit_candidates) if path.is_file())
