"""Shared fail-closed freshness predicate for source-record item judgments."""

from __future__ import annotations

from scripts.source_record_legacy_contract import SOURCE_RECORD_ITEM_DIGEST_SCHEMA

# Schema 5 binds the item-specific expanded premise/result surface. Schema 4
# omitted those fields, so several materially different premises of one
# theorem could receive the same reusable digest. The value lives in the
# data-only legacy contract so current-v11 callers need not import this reader.


def source_record_item_judgment_current(
    *,
    aggregate_current: bool,
    expected_item_digest: object,
    judgment_item_digest: object,
    judgment_item_digest_schema: object,
) -> bool:
    """Accept aggregate freshness or a versioned exact semantic item digest.

    Aggregate equality remains compatible with historical sidecars.  The
    narrower item-level fallback is intentionally schema-gated so an old digest
    that included an unrelated whole-map hash cannot be misread as the new
    scoped semantic projection.
    """

    if aggregate_current:
        return True
    return bool(
        judgment_item_digest_schema == SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        and str(expected_item_digest or "").strip()
        and str(judgment_item_digest or "").strip()
        == str(expected_item_digest or "").strip()
    )
