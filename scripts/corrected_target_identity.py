"""Orthogonal identities for approved corrected source targets.

A corrected target has two different audit roles:

* the complete record binds archival provenance, defect routing, and the
  approval artifact; and
* the review target identifies the mathematical text compared directly with
  the expanded Lean proposition.

Those roles must not share one freshness key.  In particular, changing an
unrelated paragraph in a multi-purpose approval memo must refresh the complete
record provenance without pretending that the source-to-Lean semantic
comparison changed.  Conversely, any change to the corrected mathematical
statement must invalidate that comparison.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from pathlib import PurePosixPath
from typing import Any


CORRECTED_TARGET_REVIEW_PROTOCOL = "approved_corrected_target_review_v1"
LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL = "approved_corrected_target_v1"
CORRECTED_TARGET_REVIEW_SHA256_FIELD = "corrected_target_review_sha256"
CORRECTED_TARGET_RECORD_SHA256_FIELD = "corrected_target_sha256"
CORRECTED_TARGET_APPROVAL_PROTOCOL = "unique_normalized_artifact_excerpt_v1"
CORRECTED_TARGET_APPROVAL_EXCERPT_SHA256_FIELD = "artifact_excerpt_sha256"
CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD = "original_artifact_path"
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _statement_sha256(value: object) -> str:
    normalized = re.sub(r"\s+", " ", str(value or "").strip())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def normalize_approval_excerpt(value: object) -> str:
    """Return the whitespace-stable text used as correction authority."""

    return re.sub(r"\s+", " ", str(value or "").strip())


def corrected_target_approval_excerpt_material(
    approval: object,
) -> tuple[str, str] | None:
    """Validate and return one current narrow approval authority."""

    if not isinstance(approval, Mapping) or str(
        approval.get("artifact_protocol") or ""
    ).strip() != CORRECTED_TARGET_APPROVAL_PROTOCOL:
        return None
    excerpt = normalize_approval_excerpt(approval.get("artifact_excerpt"))
    recorded = str(
        approval.get(CORRECTED_TARGET_APPROVAL_EXCERPT_SHA256_FIELD) or ""
    ).strip().lower()
    actual = hashlib.sha256(excerpt.encode("utf-8")).hexdigest()
    if len(excerpt) < 40 or recorded != actual:
        return None
    return excerpt, actual


def corrected_target_approval_artifact_error(
    approval: object,
    artifact_text: object,
) -> str:
    """Require the approved excerpt exactly once in its current artifact."""

    material = corrected_target_approval_excerpt_material(approval)
    if material is None:
        return "approval excerpt authority is malformed"
    excerpt, _digest = material
    normalized_artifact = normalize_approval_excerpt(artifact_text)
    occurrences = normalized_artifact.count(excerpt)
    if occurrences != 1:
        return (
            "approval excerpt must occur exactly once in its artifact "
            f"(found {occurrences})"
        )
    return ""


def _canonical_paper_relative_artifact_path_error(
    value: object, *, field: str
) -> str:
    if not isinstance(value, str):
        return f"{field} must be a string"
    if not value or value != value.strip():
        return f"{field} must be a nonempty canonical path without surrounding whitespace"
    if "\\" in value:
        return f"{field} must use forward slashes"
    components = value.split("/")
    if any(component in {"", ".", ".."} for component in components):
        return f"{field} must be a canonical paper-relative path"
    path = PurePosixPath(value)
    if path.is_absolute() or path.as_posix() != value:
        return f"{field} must be a canonical paper-relative path"
    return ""


def corrected_target_original_artifact_path_error(approval: object) -> str:
    """Validate the optional locator used only to replay an old approval path.

    The field is schema-owned by the narrow excerpt protocol. It identifies
    the location recorded in an authenticated historical source-item preimage;
    it is never an alternate place from which current approval is read.
    """

    if not isinstance(approval, Mapping) or (
        CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD not in approval
    ):
        return ""
    if str(approval.get("artifact_protocol") or "").strip() != (
        CORRECTED_TARGET_APPROVAL_PROTOCOL
    ):
        return (
            f"{CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD} requires "
            f"artifact_protocol {CORRECTED_TARGET_APPROVAL_PROTOCOL}"
        )
    original = approval.get(CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD)
    error = _canonical_paper_relative_artifact_path_error(
        original, field=CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
    )
    if error:
        return error
    current = approval.get("artifact_path")
    error = _canonical_paper_relative_artifact_path_error(
        current, field="artifact_path"
    )
    if error:
        return error
    assert isinstance(original, str) and isinstance(current, str)
    if original == current:
        return (
            f"{CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD} must differ from "
            "artifact_path"
        )
    return ""


def corrected_target_record_projection(raw: object) -> object:
    """Return the complete provenance record without derived digest fields."""

    payload: object = dict(raw) if isinstance(raw, Mapping) else raw
    if isinstance(payload, dict):
        payload.pop(CORRECTED_TARGET_RECORD_SHA256_FIELD, None)
        payload.pop(CORRECTED_TARGET_REVIEW_SHA256_FIELD, None)
        approval = payload.get("approval")
        if isinstance(approval, Mapping) and str(
            approval.get("artifact_protocol") or ""
        ).strip() == CORRECTED_TARGET_APPROVAL_PROTOCOL:
            # The paper-relative path is human navigation. The exact approved
            # passage, not its current filename, is the semantic authority.
            normalized_approval = dict(approval)
            normalized_approval.pop("artifact_path", None)
            if not corrected_target_original_artifact_path_error(approval):
                normalized_approval.pop(
                    CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD, None
                )
            payload["approval"] = normalized_approval
    return payload


def corrected_target_historical_record_projection(
    raw: object,
) -> tuple[object, str]:
    """Restore one authenticated historical approval locator representation.

    All fields other than the exact schema-owned locator are preserved,
    including the record's derived digests. A malformed locator is returned
    unchanged with an error so historical callers cannot mint a candidate from
    an ambiguous reconstruction.
    """

    payload: object = dict(raw) if isinstance(raw, Mapping) else raw
    if not isinstance(payload, dict):
        return payload, ""
    approval = payload.get("approval")
    if not isinstance(approval, Mapping) or (
        CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD not in approval
    ):
        return payload, ""
    error = corrected_target_original_artifact_path_error(approval)
    if error:
        return payload, error
    historical_approval = dict(approval)
    historical_approval["artifact_path"] = historical_approval.pop(
        CORRECTED_TARGET_ORIGINAL_ARTIFACT_PATH_FIELD
    )
    payload["approval"] = historical_approval
    return payload, ""


def corrected_target_record_digest(raw: object) -> str:
    """Digest the complete correction record, including approval provenance."""

    return _canonical_digest(corrected_target_record_projection(raw))


def corrected_target_review_projection(raw: object) -> object:
    """Return exactly the mathematical target a source-to-Lean reviewer sees.

    Approval kind, reference, path, timestamp, artifact bytes, and defect-ledger
    organization remain strict inputs to the complete record and accepted
    evidence graph.  They are intentionally absent here because they do not
    alter the proposition being compared with Lean.
    """

    if not isinstance(raw, Mapping):
        return raw
    return {
        "protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
        "statement_sha256": _statement_sha256(raw.get("statement")),
        "archival_equivalence_claimed": raw.get("archival_equivalence_claimed"),
    }


def corrected_target_review_digest(raw: object) -> str:
    """Digest the stable mathematical target used by semantic review."""

    return _canonical_digest(corrected_target_review_projection(raw))


def corrected_target_screening_binding_is_current(
    row: Mapping[str, Any],
    target: Mapping[str, Any],
) -> bool:
    """Check a semantic-screening row against its exact identity generation.

    Current rows use the stable review identity.  Historical rows remain
    readable, but retain their original stricter whole-record binding; this is
    fail-closed and does not manufacture compatibility between audit engines.
    """

    protocol = str(row.get("corrected_target_protocol") or "").strip()
    if protocol == CORRECTED_TARGET_REVIEW_PROTOCOL:
        return (
            str(row.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD) or "")
            .strip()
            .lower()
            == corrected_target_review_digest(target)
        )
    if protocol == LEGACY_CORRECTED_TARGET_REVIEW_PROTOCOL:
        recorded_target_digest = str(
            target.get(CORRECTED_TARGET_RECORD_SHA256_FIELD) or ""
        ).strip().lower()
        return (
            str(row.get(CORRECTED_TARGET_RECORD_SHA256_FIELD) or "")
            .strip()
            .lower()
            == recorded_target_digest
        )
    return False


def source_requires_approved_corrected_target(source_record: object) -> bool:
    """Whether a source route has a distinct, approved mathematical target."""

    return bool(
        isinstance(source_record, Mapping)
        and str(source_record.get("coverage_status") or "").strip()
        == "corrected_source_statement"
    )


def current_approved_corrected_target_metadata(
    source_record: object,
    reviewed_target: object,
) -> dict[str, str]:
    """Validate the correction worksheet that an independent reviewer saw.

    Both paper-local and reusable-library source-to-Lean lanes use this one
    binding.  It intentionally certifies the approved mathematical target,
    never an asserted equivalence with the archival source wording.
    """

    if not source_requires_approved_corrected_target(source_record):
        raise ValueError("source route has no approved corrected target")
    assert isinstance(source_record, Mapping)
    target = source_record.get("corrected_target")
    if (
        not isinstance(target, Mapping)
        or target.get("archival_equivalence_claimed") is not False
    ):
        raise ValueError(
            "source route has no non-equivalence approved corrected target"
        )
    current_digest = corrected_target_review_digest(target)
    recorded_digest = str(
        target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD) or ""
    ).strip().lower()
    if (
        not recorded_digest
        or recorded_digest != current_digest
        or not isinstance(reviewed_target, Mapping)
        or str(reviewed_target.get("corrected_target_protocol") or "").strip()
        != CORRECTED_TARGET_REVIEW_PROTOCOL
        or str(
            reviewed_target.get(CORRECTED_TARGET_REVIEW_SHA256_FIELD) or ""
        ).strip().lower()
        != current_digest
        or reviewed_target.get("archival_equivalence_claimed") is not False
    ):
        raise ValueError(
            "approved corrected target changed or was not present in the "
            "clean reviewer worksheet"
        )
    return {
        "corrected_target_protocol": CORRECTED_TARGET_REVIEW_PROTOCOL,
        CORRECTED_TARGET_REVIEW_SHA256_FIELD: current_digest,
    }
