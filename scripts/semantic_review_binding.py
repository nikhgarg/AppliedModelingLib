"""Acceptance-neutral binding of reviewer judgments to current semantics.

Storage keys and declaration names are navigation.  This module provides the
small mutual one-to-one matcher and the common prerequisite identity rule used
by both reviewer-work writers and accepting graph consumers.  It owns no file
I/O, queue rendering, Lean discovery, or evidence issuance.
"""

from __future__ import annotations

import re
from collections.abc import Callable, Mapping
from typing import Any


_SHA256_RE = re.compile(r"[0-9a-f]{64}")
# A correction disposition is a reviewed semantic outcome, not a raw-source
# match.  Callers that may accept it additionally verify the source-map's
# current approval-pinned corrected target before treating the row as current.
_SEMANTIC_JUDGMENTS = frozenset(
    {"matches", "matches_approved_corrected_target", "mismatch", "uncertain"}
)


def reusable_semantic_judgment(
    prior: object,
    entry: Mapping[str, Any],
    *,
    target_protocol_field: str,
    target_protocol: str,
    prior_code_sha256_field: str,
    current_code_sha256_field: str,
    prior_target_sha256_field: str | None = None,
    current_target_sha256_field: str | None = None,
    additional_identity_field_pairs: tuple[tuple[str, str], ...] = (),
) -> dict[str, str] | None:
    """Reuse one verdict only under the common exact semantic identity rule."""

    if not isinstance(prior, Mapping):
        return None
    judgment = str(prior.get("judgment") or "").strip().lower()
    reason = str(prior.get("reason") or "").strip()
    validator = str(prior.get("validator") or "").strip()
    validator_type = str(prior.get("validator_type") or "").strip()
    validated_at = str(prior.get("validated_at") or "").strip()
    prior_signature = str(
        prior.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    current_signature = str(
        entry.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    prior_code = str(prior.get(prior_code_sha256_field) or "").strip().lower()
    current_code = str(entry.get(current_code_sha256_field) or "").strip().lower()
    prior_target = (
        str(prior.get(prior_target_sha256_field) or "").strip().lower()
        if prior_target_sha256_field
        else ""
    )
    current_target = (
        str(entry.get(current_target_sha256_field) or "").strip().lower()
        if current_target_sha256_field
        else ""
    )
    prior_source = str(
        prior.get("source_input_bundle_sha256") or ""
    ).strip().lower()
    current_source = str(
        entry.get("source_input_bundle_sha256") or ""
    ).strip().lower()
    prior_anchor = str(
        prior.get("source_anchor_bundle_sha256") or ""
    ).strip().lower()
    current_anchor = str(
        entry.get("source_anchor_bundle_sha256") or ""
    ).strip().lower()
    # An approved corrected target is reviewer-visible mathematical material,
    # not incidental source-map metadata.  It therefore belongs to the common
    # reuse identity for every source-to-Lean review lane.  In particular, an
    # archival ``matches`` row cannot silently survive when a source route is
    # changed to a distinct approved target.
    prior_corrected_target = str(
        prior.get("corrected_target_review_sha256") or ""
    ).strip().lower()
    current_corrected_target = str(
        entry.get("corrected_target_review_sha256") or ""
    ).strip().lower()
    corrected_target_current = (
        not prior_corrected_target
        and not current_corrected_target
    ) or (
        _SHA256_RE.fullmatch(prior_corrected_target)
        and prior_corrected_target == current_corrected_target
        and judgment == "matches_approved_corrected_target"
    )
    stable_identity_current = bool(
        _SHA256_RE.fullmatch(prior_signature)
        and _SHA256_RE.fullmatch(current_signature)
        and prior_signature == current_signature
    )
    legacy_exact_code_current = bool(
        not prior_signature
        and _SHA256_RE.fullmatch(prior_code)
        and prior_code == current_code
    )
    legacy_exact_target_current = bool(
        not prior_signature
        and prior_target_sha256_field
        and current_target_sha256_field
        and _SHA256_RE.fullmatch(prior_target)
        and prior_target == current_target
    )
    additional_identities_current = all(
        (
            not str(prior.get(prior_field) or "").strip()
            and not str(entry.get(current_field) or "").strip()
        )
        or (
            _SHA256_RE.fullmatch(
                str(prior.get(prior_field) or "").strip().lower()
            )
            and str(prior.get(prior_field) or "").strip().lower()
            == str(entry.get(current_field) or "").strip().lower()
        )
        for prior_field, current_field in additional_identity_field_pairs
    )
    # Attaching a maintainer-approved clarification changes the reviewer input
    # bundle deliberately, but it does not change the raw source, Lean target,
    # or declaration reviewed earlier.  Permit a one-way metadata rebind when
    # the current entry proves that its anchor-only identity is unchanged.  An
    # older ledger predating the explicit anchor field may use the schema-1
    # source-bundle digest, which is exactly that same anchor identity.
    source_identity_current = prior_source == current_source
    if (
        not source_identity_current
        and _SHA256_RE.fullmatch(current_anchor)
        and current_source != current_anchor
        and (
            prior_anchor == current_anchor
            or (not prior_anchor and prior_source == current_anchor)
        )
    ):
        source_identity_current = True
    if (
        judgment not in _SEMANTIC_JUDGMENTS
        or not reason
        or not validator
        or not validator_type
        or not validated_at
        or str(prior.get(target_protocol_field) or "").strip() != target_protocol
        or not (
            stable_identity_current
            or legacy_exact_target_current
            or legacy_exact_code_current
        )
        or not _SHA256_RE.fullmatch(prior_source)
        or not source_identity_current
        or not corrected_target_current
        or not additional_identities_current
    ):
        return None
    return {
        "judgment": judgment,
        "reason": reason,
        "validator": validator,
        "validator_type": validator_type,
        "validated_at": validated_at,
    }


def unique_reusable_judgment_bindings(
    current_entries: Mapping[str, Mapping[str, Any]],
    existing_items: Mapping[str, Any],
    *,
    reusable_judgment: Callable[
        [object, Mapping[str, Any]], dict[str, str] | None
    ],
) -> dict[str, tuple[str, dict[str, str]]]:
    """Bind current rows to prior judgments by exact semantic identity.

    Exact names are only a stable navigation preference.  Every remaining
    rename must be a mutual singleton: one current row and one unused prior
    row.  A collision remains unbound so callers fail closed or request
    reviewer work instead of guessing.
    """

    current = {
        str(name).strip(): entry
        for name, entry in current_entries.items()
        if str(name).strip() and isinstance(entry, Mapping)
    }
    prior = {
        str(name).strip(): row
        for name, row in existing_items.items()
        if str(name).strip() and isinstance(row, Mapping)
    }
    bindings: dict[str, tuple[str, dict[str, str]]] = {}
    used_prior: set[str] = set()

    for name in sorted(current):
        metadata = reusable_judgment(prior.get(name), current[name])
        if metadata is not None:
            bindings[name] = (name, metadata)
            used_prior.add(name)

    while True:
        candidates: dict[str, list[tuple[str, dict[str, str]]]] = {}
        reverse: dict[str, list[str]] = {}
        for current_name, entry in current.items():
            if current_name in bindings:
                continue
            matches: list[tuple[str, dict[str, str]]] = []
            for prior_name, row in prior.items():
                if prior_name in used_prior:
                    continue
                metadata = reusable_judgment(row, entry)
                if metadata is None:
                    continue
                matches.append((prior_name, metadata))
                reverse.setdefault(prior_name, []).append(current_name)
            candidates[current_name] = matches

        unique = [
            (current_name, matches[0])
            for current_name, matches in candidates.items()
            if len(matches) == 1 and len(reverse.get(matches[0][0], ())) == 1
        ]
        if not unique:
            break
        for current_name, (prior_name, metadata) in unique:
            bindings[current_name] = (prior_name, metadata)
            used_prior.add(prior_name)

    return bindings
