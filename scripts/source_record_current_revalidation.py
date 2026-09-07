#!/usr/bin/env python3
"""Attested current revalidation for a complete v10 source-record sidecar.

This is deliberately *not* a semantic-reuse or schema-migration shortcut.
It handles the narrow case where a prior v10 manual review is useful evidence,
but its original raw receipt is unavailable, so schema-4 item pins cannot be
verified or migrated mechanically.  A reviewer must first inspect the current
raw v10 surface and write an attestation bound to that exact receipt.  This
tool then:

* requires complete, exact generated-key coverage;
* validates the current raw receipt and its current item-reuse metadata;
* preserves old schema-4 item receipts only as historical provenance, never
  as schema-5 item-level freshness; and
* reruns the shared source-target disposition checks before rebinding every
  judgment to the current aggregate receipt.

It never compares declarations, binders, map keys, or function names to infer
that an old decision remains sound.  The explicit attestation is the semantic
review step; the deterministic checks make that step auditable and prevent an
attestation for one raw surface from being applied to another one.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in tests.
    from scripts import audit_evidence_integrity as EVIDENCE
    from scripts import audit_repository as REPOSITORY
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.formalization_protocol import (
        CURRENT_SOURCE_RECORD_PROMPT_VERSION,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_protocol_receipt_matches,
        formalization_review_protocol_digest,
    )
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_audit_surface_view,
        source_record_item_reuse_eligible,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from scripts.source_record_target_disposition import (
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        project_source_record_response_association_pins,
        recursive_field_parent_route_record_digest,
        recursive_field_target_disposition_errors,
        semantic_association_record_digest,
        source_record_response_association_projection,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
        semantic_target_disposition_errors,
        source_input_target_disposition_errors,
    )
    from scripts.configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        load_configured_assumption_formalization_regularity_context,
    )
    from scripts.source_record_obligation_groups import raw_source_record_obligation_groups
    from scripts.source_record_overlay_protocol import (
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import audit_evidence_integrity as EVIDENCE
    import audit_repository as REPOSITORY
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from formalization_protocol import (
        CURRENT_SOURCE_RECORD_PROMPT_VERSION,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_protocol_receipt_matches,
        formalization_review_protocol_digest,
    )
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_audit_surface_view,
        source_record_item_reuse_eligible,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from source_record_target_disposition import (
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        project_source_record_response_association_pins,
        recursive_field_parent_route_record_digest,
        recursive_field_target_disposition_errors,
        semantic_association_record_digest,
        source_record_response_association_projection,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
        semantic_target_disposition_errors,
        source_input_target_disposition_errors,
    )
    from configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        load_configured_assumption_formalization_regularity_context,
    )
    from source_record_obligation_groups import raw_source_record_obligation_groups
    from source_record_overlay_protocol import (
        SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
CURRENT_REVALIDATION_SCHEMA = 1
CURRENT_REVALIDATION_POLICY_VERSION = (
    "source-record-current-manual-semantic-revalidation-v3"
)
CURRENT_REVALIDATION_ATTESTATION_KIND = (
    "source_record_current_semantic_revalidation_attestation"
)
CURRENT_REVALIDATION_FIELD = "current_semantic_revalidation"
PRIOR_ITEM_RECEIPT_FIELD = "prior_source_record_item_receipt"
ATTESTED_JUDGMENT_AMENDMENTS_FIELD = "judgment_amendments"
ATTESTED_JUDGMENT_REPLACEMENTS_FIELD = "judgment_replacements"
ATTESTED_JUDGMENT_REPLACEMENT_KEYS_FIELD = "judgment_replacement_keys_required"
SELECTED_JUDGMENT_REPLACEMENT_SCHEMA = 1
SELECTED_JUDGMENT_REPLACEMENT_FIELDS = frozenset(
    {
        "schema",
        "current_group_semantic_descriptor_sha256",
        "prior_response_semantic_sha256",
        "replacement_rationale",
        "response",
    }
)
ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD = (
    "semantic_model_content_amendments"
)
ATTESTED_SEMANTIC_MODEL_DIMENSION_AMENDMENTS_FIELD = (
    "semantic_model_dimension_amendments"
)
ATTESTED_SEMANTIC_MODEL_DIMENSION_ASSOCIATION_AMENDMENTS_FIELD = (
    "semantic_model_dimension_association_amendments"
)
ATTESTED_JUDGMENT_AMENDMENT_FIELDS = frozenset(
    {
        "classification",
        "lean_derivation",
        "reason",
        "source_evidence",
        "source_location",
        "semantic_association_sha256",
        "semantic_model_dimensions",
        "model_convention_sha256_by_id",
        "source_target_disposition",
    }
)
# A current semantic reviewer may correct the concrete evidence that connects a
# source probability law to an expanded Lean construction.  Keep this smaller
# than a whole-dimension rewrite: the pre-existing dimensional review remains
# immutable evidence, while the attestation records exactly the source-backed
# bridge fields that changed.  These are semantic record paths, not declaration
# or function-name heuristics.
ATTESTED_SEMANTIC_MODEL_CONTENT_PATHS = frozenset(
    {
        "joint_law_and_state_evolution.transformed_law_analysis.verdict",
        "joint_law_and_state_evolution.distribution_parameterization_analysis.law_equivalence_evidence",
        "joint_law_and_state_evolution.distribution_parameterization_analysis.parameter_translation",
    }
)
SELECTED_CURRENT_REVALIDATION_SCHEMA = 1
# Keep this exported v1 spelling as the legacy policy identifier.  Several
# historical recovery adapters deliberately accept only v1 evidence, so a
# newly issued selected-review union cannot accidentally be replayed through a
# recovery path that records only one differential artifact.
SELECTED_CURRENT_REVALIDATION_POLICY_VERSION = (
    "source-record-current-selected-semantic-revalidation-v1"
)
SELECTED_CURRENT_REVALIDATION_UNION_POLICY_VERSION = (
    "source-record-current-selected-semantic-revalidation-v2"
)
SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION = (
    "source-record-current-selected-semantic-revalidation-v3"
)
SELECTED_CURRENT_REVALIDATION_POLICY_VERSIONS = frozenset(
    {
        SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
        SELECTED_CURRENT_REVALIDATION_UNION_POLICY_VERSION,
        SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION,
    }
)
SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND = (
    "source_record_current_selected_semantic_revalidation_attestation"
)
SELECTED_CURRENT_REVALIDATION_FIELD = "current_selected_semantic_revalidation"
SELECTED_CURRENT_REVALIDATION_ITEM_FIELD = (
    "current_selected_semantic_revalidation_item"
)
SELECTED_CURRENT_REVALIDATION_SCOPE = (
    "all_current_generated_groups_not_authenticated_by_differential_overlay"
)
SELECTED_CURRENT_REVALIDATION_UNION_SCOPE = (
    "all_current_generated_groups_not_authenticated_by_current_overlay_union"
)
SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_SCOPE = (
    "all_current_generated_groups_not_authenticated_by_current_overlay_union_"
    "with_explicit_current_replacements"
)
SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD = (
    "authenticated_current_overlay_union"
)
SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_SCHEMA = 1
SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_POLICY_VERSION = (
    "source-record-current-authenticated-overlay-union-v1"
)
AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA = 1
AUTHENTICATED_EVIDENCE_COMPOSITION_POLICY_VERSION = (
    "source-record-v10-authenticated-overlay-selected-composition-v1"
)
AUTHENTICATED_EVIDENCE_COMPOSITION_FIELD = (
    "source_record_authenticated_evidence_composition"
)
AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD = (
    "source_record_authenticated_evidence_composition_item"
)
_SOURCE_TARGET_STATEMENT_MAP_UNSET = object()
# A selected current attestation establishes fresh evidence for its exact
# complement only after binding every response to the current raw descriptor.
# Earlier overlay receipts remain useful historical provenance, but cannot
# remain top-level response transport: the shared loader would correctly
# require their old overlay to authenticate again instead of accepting the
# selected current attestation.
_HISTORICAL_SELECTED_REBIND_TRANSPORT_FIELDS = frozenset(
    {
        "source_record_schema4_to5_migration",
        "source_record_differential_revalidation",
        "source_record_differential_revalidation_history",
        "source_record_attested_selected_semantic_reuse",
        AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD,
    }
)

# This is intentionally a planning aid, not another receipt or rebind lane.
# A new target-disposition field can be mechanically added only after the
# complete old/current group descriptors are equal.  In particular, it cannot
# repair an archived classification, source route, source convention, or a
# changed source/Lean statement.  The 2026-08-13 LG24 pre-v11/current pair has
# zero descriptor-equal groups (0/117), so it correctly cannot use this path.
EXACT_DESCRIPTOR_SCHEMA_TRANSPORT_NORMALIZATION = (
    "validated_source_assumption_add_literal_source_disposition"
)
_EXACT_DESCRIPTOR_SCHEMA_TRANSPORT_PROHIBITED_RESPONSE_FIELDS = frozenset(
    {
        # These fields select a non-literal target or a source-proof
        # convention.  A schema helper must never infer, rewrite, or re-pin
        # either one.
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "governing_defect_ids",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
    }
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LEAN_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.lean):(?P<line>\d+)"
)


class SourceRecordCurrentRevalidationError(ValueError):
    """Raised when an attested current revalidation is not admissible."""


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_json_bytes(value: object) -> bytes:
    """Serialize one deterministic generated sidecar exactly once."""

    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def write_rebound_sidecar_if_changed(path: Path, rebound: Mapping[str, Any]) -> bool:
    """Write a deterministic rebind only when its exact bytes are new.

    Re-running one accepted attestation must be observably idempotent.  The
    current sidecar already binds the same raw receipt and reviewer decision,
    so rewriting it would only create apparent receipt churn.  A byte mismatch
    still writes the complete current rebind; semantic validation remains the
    caller's responsibility before this transport helper is reached.
    """

    contents = _canonical_json_bytes(rebound)
    try:
        if path.read_bytes() == contents:
            return False
    except OSError:
        pass
    path.write_bytes(contents)
    return True


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _read_json_object_with_sha256(path: Path) -> tuple[dict[str, Any], str]:
    """Read, parse, and hash one JSON artifact from one immutable byte buffer."""

    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordCurrentRevalidationError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordCurrentRevalidationError(f"{path} is not a JSON object")
    return payload, hashlib.sha256(contents).hexdigest()


def _load_json_object(path: Path) -> dict[str, Any]:
    return _read_json_object_with_sha256(path)[0]


def generated_judgment_items(
    raw_audit: Mapping[str, Any],
) -> dict[str, list[tuple[str, Mapping[str, Any]]]]:
    """Return every generated evidence item grouped by its exact judgment key."""

    grouped: dict[str, list[tuple[str, Mapping[str, Any]]]] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        values = raw_audit.get(section)
        if values is None:
            continue
        if not isinstance(values, list):
            raise SourceRecordCurrentRevalidationError(
                f"current raw audit `{section}` is not a list"
            )
        for index, item in enumerate(values):
            if not isinstance(item, Mapping):
                raise SourceRecordCurrentRevalidationError(
                    f"current raw audit `{section}[{index}]` is not an object"
                )
            if source_record_item_is_nonreusable_theorem_facing_mirror(
                section, item
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            if not key:
                # Type-valued certificate results can be audit-relevant raw
                # artifacts without being a sidecar-review judgment. Their
                # complete raw content remains bound below by
                # ``generated_judgment_surface_sha256``; they simply cannot
                # demand a nonexistent response key.
                continue
            grouped.setdefault(key, []).append((section, item))
    if not grouped:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has no generated source-record judgment items"
        )
    return grouped


def generated_judgment_keys_sha256(raw_audit: Mapping[str, Any]) -> str:
    """Digest exact generated keys, not a declaration-name-derived inventory."""

    return _canonical_digest(sorted(generated_judgment_items(raw_audit)))


def generated_judgment_surface_sha256(raw_audit: Mapping[str, Any]) -> str:
    """Digest every reusable raw item, including keyless certificates.

    Keyless type-valued result artifacts do not have a sidecar judgment by
    design, but a manual attestation must still be tied to their current raw
    evidence surface.  The key ledger is checked separately.
    """

    surface: dict[str, list[dict[str, Any]]] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        values = raw_audit.get(section)
        if values is None:
            continue
        if not isinstance(values, list):
            raise SourceRecordCurrentRevalidationError(
                f"current raw audit `{section}` is not a list"
            )
        normalized: list[dict[str, Any]] = []
        for index, item in enumerate(values):
            if not isinstance(item, Mapping):
                raise SourceRecordCurrentRevalidationError(
                    f"current raw audit `{section}[{index}]` is not an object"
                )
            if source_record_item_is_nonreusable_theorem_facing_mirror(
                section, item
            ):
                continue
            normalized.append({"index": index, "item": dict(item)})
        surface[section] = normalized
    return _canonical_digest(surface)


def semantic_model_judgment_keys(raw_audit: Mapping[str, Any]) -> set[str]:
    """Return only generated groups with an actual semantic-model obligation."""

    raw_items = raw_audit.get("semantic_model_items", [])
    if raw_items is None:
        return set()
    if not isinstance(raw_items, list):
        raise SourceRecordCurrentRevalidationError(
            "current raw audit `semantic_model_items` is not a list"
        )
    keys: set[str] = set()
    for index, item in enumerate(raw_items):
        if not isinstance(item, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"current raw audit `semantic_model_items[{index}]` is not an object"
            )
        key = str(item.get("judgment_key") or "").strip()
        if key:
            keys.add(key)
    return keys


def _relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordCurrentRevalidationError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _raw_audit_error(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path | None = None,
    use_paper_local_semantic_contract_revalidation: bool = True,
) -> str:
    if raw_audit.get("paper") != paper:
        return (
            "current raw audit paper mismatch: "
            f"expected {paper!r}, found {raw_audit.get('paper')!r}"
        )
    if raw_audit.get("prompt_version") != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "current raw audit does not use the v10 source-record prompt"
    if raw_audit.get("source_record_policy_version") != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "current raw audit does not use the v10 source-record policy"
    if not _sha256(raw_audit.get("source_record_audit_sha256")):
        return "current raw audit has no valid aggregate source-record digest"
    receipt_error = source_record_audit_receipt_error(raw_audit)
    if receipt_error:
        return "current raw audit receipt is invalid: " + receipt_error
    # A current rebind must not turn a raw receipt that already reports an
    # unresolved semantic route into reusable current evidence.  When the
    # caller has a paper folder, consult the same authenticated structural
    # replay used by the final evidence consumer.  This permits only exact,
    # byte-pinned representation repairs; it does not treat an artifact or a
    # caller-supplied projection as a semantic judgment.
    raw_association_errors = raw_audit.get("source_contract_association_errors")
    raw_coverage_errors = raw_audit.get("source_coverage_route_errors")
    association_count = raw_audit.get("source_contract_association_error_count")
    if raw_association_errors not in (None, []) and not isinstance(
        raw_association_errors, list
    ):
        return "current raw audit has malformed source-contract association errors"
    if raw_coverage_errors not in (None, []) and not isinstance(
        raw_coverage_errors, list
    ):
        return "current raw audit has malformed source-coverage route errors"
    needs_structural_replay = bool(raw_association_errors) or bool(
        raw_coverage_errors
    )
    if paper_dir is None or not use_paper_local_semantic_contract_revalidation:
        # Preserve the legacy, folder-free validation surface for archived
        # callers and focused unit tests.  Such callers cannot authenticate a
        # paper-local structural replay, so they receive no correction credit.
        if association_count not in {0, None}:
            return "current raw audit recorded source-contract association errors"
        if raw_association_errors not in ([], None):
            return "current raw audit has nonempty source-contract association errors"
        if raw_coverage_errors not in ([], None):
            return "current raw audit has nonempty source-coverage route errors"
    else:
        if paper_dir.name != paper:
            return (
                "current raw audit paper directory mismatch: "
                f"expected folder for {paper!r}, found {paper_dir.name!r}"
            )
        projection = None
        if needs_structural_replay:
            try:
                projection, replay_error = (
                    EVIDENCE.source_record_semantic_contract_revalidation_context(
                        paper_dir, raw_audit
                    )
                )
            except Exception as exc:  # noqa: BLE001 - replay is a fail-closed gate.
                return (
                    "could not validate current raw semantic-contract replay: "
                    f"{type(exc).__name__}: {exc}"
                )
            if replay_error:
                return "current raw semantic-contract replay is invalid: " + replay_error
        semantic_error = EVIDENCE.source_record_effective_semantic_surface_error(
            raw_audit,
            semantic_contract_revalidation=projection,
        )
        if semantic_error:
            return "current raw audit has invalid effective semantic surface: " + semantic_error

        # The error-count field is generator-owned bookkeeping.  A structural
        # replay may suppress every listed association error, but never an
        # unpaired or malformed count.  This keeps the replay a correction of
        # exact raw diagnostics rather than a way to erase arbitrary metadata.
        if raw_association_errors:
            if association_count is not None and (
                isinstance(association_count, bool)
                or not isinstance(association_count, int)
                or association_count != len(raw_association_errors)
            ):
                return (
                    "current raw audit has inconsistent source-contract association "
                    "error bookkeeping"
                )
        elif association_count not in {0, None}:
            return "current raw audit recorded source-contract association errors"
    target_route_error = source_record_target_route_error(raw_audit)
    if target_route_error:
        return "current raw audit has invalid semantic target routing: " + target_route_error
    item_error = source_record_raw_reusable_item_metadata_error(
        raw_audit,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    if item_error:
        return "current raw audit item-reuse metadata is invalid: " + item_error
    lean_check = raw_audit.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return "current raw audit lacks a successful Lean check"
    try:
        generated_judgment_items(raw_audit)
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    return ""


def _sidecar_items(
    sidecar: Mapping[str, Any],
    *,
    paper: str,
    allow_empty: bool = False,
) -> dict[str, dict[str, Any]]:
    if sidecar.get("schema") != 1 or sidecar.get("paper") not in {None, paper}:
        raise SourceRecordCurrentRevalidationError(
            "prior judgment sidecar has an invalid schema or paper identity"
        )
    if sidecar.get("prompt_version") != SOURCE_RECORD_V10_PROMPT_VERSION:
        raise SourceRecordCurrentRevalidationError(
            "prior judgment sidecar does not use the v10 source-record prompt"
        )
    raw_items = sidecar.get("items")
    if not isinstance(raw_items, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "prior judgment sidecar has no object-valued items ledger"
        )
    items: dict[str, dict[str, Any]] = {}
    for raw_key, value in raw_items.items():
        key = str(raw_key or "").strip()
        if not key or not isinstance(value, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "prior judgment sidecar has an empty key or non-object judgment"
            )
        items[key] = dict(value)
    if not items and not allow_empty:
        raise SourceRecordCurrentRevalidationError("prior judgment sidecar has no judgments")
    return items


def _prior_sidecar_error(
    sidecar: Mapping[str, Any], items: Mapping[str, Mapping[str, Any]]
) -> str:
    """Validate an archived judgment ledger before complete current review.

    A differential-reuse ledger can legitimately contain judgments issued
    against several historical aggregate receipts.  The immutable sidecar
    snapshot preserves those per-item receipts, while the complete current
    attestation binds the exact snapshot bytes and every current generated
    judgment.  Requiring all historical receipts to equal the sidecar's most
    recent aggregate receipt would reject valid accumulated review work.
    """

    prior_digest = _sha256(sidecar.get("source_record_audit_sha256"))
    if not prior_digest:
        return "prior judgment sidecar has no aggregate source-record audit digest"
    for key, item in items.items():
        prompt = str(item.get("prompt_version") or sidecar.get("prompt_version") or "").strip()
        digest = _sha256(
            item.get("source_record_audit_sha256")
            or sidecar.get("source_record_audit_sha256")
        )
        validator = item.get("validator") or sidecar.get("validator") or sidecar.get("model")
        timestamp = (
            item.get("validated_at")
            or sidecar.get("validated_at")
            or sidecar.get("timestamp")
        )
        if prompt != SOURCE_RECORD_V10_PROMPT_VERSION:
            return f"prior judgment `{key}` does not use the v10 source-record prompt"
        if not digest:
            return f"prior judgment `{key}` has no valid historical aggregate digest"
        if not str(validator or "").strip() or not str(timestamp or "").strip():
            return f"prior judgment `{key}` lacks validator or timestamp metadata"
    return ""


def _attested_key_delta_error(
    attestation: Mapping[str, Any],
    *,
    prior_keys: set[str],
    current_keys: set[str],
) -> str:
    """Require an explicit, canonical ledger delta for complete review.

    The current raw receipt and immutable prior-sidecar hash authenticate the
    two ledgers.  These lists make additions and retirements explicit to the
    reviewer; they do not associate old and new obligations by key spelling.
    """

    expected = {
        "new_judgment_keys_required": sorted(current_keys - prior_keys),
        "retired_prior_judgment_keys": sorted(prior_keys - current_keys),
    }
    for field, expected_keys in expected.items():
        raw_keys = attestation.get(field, [])
        if not isinstance(raw_keys, list) or any(
            not isinstance(key, str) or not key.strip() for key in raw_keys
        ):
            return f"attestation `{field}` must be a list of nonempty strings"
        if raw_keys != expected_keys:
            return f"attestation `{field}` does not match the authenticated ledger delta"
    return ""


def _attestation_error(
    attestation: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
    prior_sidecar_sha256: str,
    prior_audit_sha256: str,
    raw_audit: Mapping[str, Any],
) -> str:
    if attestation.get("schema") != CURRENT_REVALIDATION_SCHEMA:
        return "attestation has an unsupported schema"
    if attestation.get("artifact_kind") != CURRENT_REVALIDATION_ATTESTATION_KIND:
        return "attestation has the wrong artifact_kind"
    if attestation.get("paper") != paper:
        return "attestation paper does not match the requested paper"
    if attestation.get("policy_version") != CURRENT_REVALIDATION_POLICY_VERSION:
        return "attestation has the wrong current-semantic-revalidation policy version"
    if not formalization_protocol_receipt_matches(attestation, scope="review"):
        return "attestation has no current formalization review-protocol receipt"
    if any(
        bool(attestation.get(marker))
        for marker in (
            "non_evidence_scaffold",
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
        )
    ):
        return "attestation is marked as a non-evidence scaffold"
    if attestation.get("reviewed_current_semantics") is not True:
        return "attestation must explicitly set reviewed_current_semantics: true"
    if str(attestation.get("review_scope") or "").strip() != (
        "all_current_generated_judgment_keys"
    ):
        return "attestation must cover all current generated judgment keys"
    if not str(attestation.get("reviewer") or "").strip() or not str(
        attestation.get("validated_at") or ""
    ).strip():
        return "attestation lacks reviewer or validated_at metadata"
    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(attestation.get("current_source_record_audit_sha256")) != current_digest:
        return "attestation is not bound to the current raw aggregate audit digest"
    if _sha256(attestation.get("prior_source_record_audit_sha256")) != prior_audit_sha256:
        return "attestation is not bound to the prior sidecar aggregate audit digest"
    if _sha256(attestation.get("prior_judgment_sidecar_sha256")) != prior_sidecar_sha256:
        return "attestation is not bound to the exact prior judgment sidecar bytes"
    if str(attestation.get("prior_judgment_sidecar_path") or "").strip() != _relative_path(
        prior_sidecar_path, paper_dir
    ):
        return "attestation records a different prior judgment sidecar path"
    if _sha256(attestation.get("generated_judgment_keys_sha256")) != (
        generated_judgment_keys_sha256(raw_audit)
    ):
        return "attestation does not bind the current exact judgment-key ledger"
    if _sha256(attestation.get("generated_judgment_surface_sha256")) != (
        generated_judgment_surface_sha256(raw_audit)
    ):
        return "attestation does not bind the current generated judgment surface"
    return ""


def _historical_item_receipt(item: dict[str, Any]) -> dict[str, Any]:
    """Archive old item/overlay transport before issuing a selected rebind.

    The caller has already checked the exact selected current descriptor
    complement.  Retain old transport in the archival receipt for provenance,
    but do not leave it active on the newly current response: a stale overlay
    must not be replayed as if it authenticated the new raw audit.
    """

    receipt = {
        key: item.pop(key)
        for key in list(item)
        if key.startswith("source_record_item_")
        or key in _HISTORICAL_SELECTED_REBIND_TRANSPORT_FIELDS
    }
    return receipt


def _attested_judgment_amendments(
    attestation: Mapping[str, Any], *, expected_keys: set[str]
) -> dict[str, dict[str, Any]]:
    """Read explicit semantic corrections authorized by the current review.

    Current freshness rebinding normally preserves an earlier judgment ledger.
    When a current semantic review corrects a decision, the correction belongs
    in the attestation rather than an untracked post-write sidecar edit.  The
    small allowlist intentionally excludes every freshness, digest, and
    validator field: those are generated from the current raw receipt.
    """

    raw = attestation.get(ATTESTED_JUDGMENT_AMENDMENTS_FIELD, {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation judgment_amendments must be an object"
        )
    amendments: dict[str, dict[str, Any]] = {}
    for raw_key, raw_value in raw.items():
        key = str(raw_key or "").strip()
        if not key or key not in expected_keys:
            raise SourceRecordCurrentRevalidationError(
                "attestation amendment names a missing or non-current judgment key"
            )
        if not isinstance(raw_value, Mapping) or not raw_value:
            raise SourceRecordCurrentRevalidationError(
                f"attestation amendment `{key}` must be a nonempty object"
            )
        fields = {str(field) for field in raw_value}
        unsupported = sorted(fields - ATTESTED_JUDGMENT_AMENDMENT_FIELDS)
        if unsupported:
            raise SourceRecordCurrentRevalidationError(
                f"attestation amendment `{key}` changes unsupported field(s): "
                + ", ".join(unsupported)
            )
        if "classification" in raw_value and not str(
            raw_value["classification"] or ""
        ).strip():
            raise SourceRecordCurrentRevalidationError(
                f"attestation amendment `{key}` has an empty classification"
            )
        if "lean_derivation" in raw_value:
            if str(raw_value.get("classification") or "").strip() != (
                "proved_from_primitives"
            ):
                raise SourceRecordCurrentRevalidationError(
                    f"attestation amendment `{key}` may amend lean_derivation only "
                    "when it explicitly classifies the item proved_from_primitives"
                )
            if not str(raw_value.get("lean_derivation") or "").strip():
                raise SourceRecordCurrentRevalidationError(
                    f"attestation amendment `{key}` has an empty lean_derivation"
                )
        amendments[key] = {str(field): value for field, value in raw_value.items()}
    return amendments


def _attested_semantic_model_content_amendments(
    attestation: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
    *,
    expected_keys: set[str],
    semantic_model_keys: set[str],
) -> dict[str, dict[str, str]]:
    """Read exact source-law bridge corrections without rewriting a review.

    A full ``semantic_model_dimensions`` replacement is intentionally still
    available through ``judgment_amendments`` for a genuinely new review.  This
    narrower lane is for a current reviewer who found that an archived response
    has a stale or generic law bridge, while every other dimension entry is
    already valid current evidence.  It makes the changed record paths explicit
    and leaves all other semantic fields byte-identical to the snapshot.
    """

    raw = attestation.get(ATTESTED_SEMANTIC_MODEL_CONTENT_AMENDMENTS_FIELD, {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation semantic_model_content_amendments must be an object"
        )
    amendments: dict[str, dict[str, str]] = {}
    for raw_key, raw_updates in raw.items():
        key = str(raw_key or "").strip()
        prior = prior_items.get(key)
        if not key or key not in expected_keys or not isinstance(prior, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "semantic-model content amendment names a missing or non-current judgment key"
            )
        if key not in semantic_model_keys:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model content amendment `{key}` has no generated semantic-model obligation"
            )
        if not isinstance(raw_updates, Mapping) or not raw_updates:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model content amendment `{key}` must be a nonempty object"
            )
        dimensions = prior.get("semantic_model_dimensions")
        joint = (
            dimensions.get("joint_law_and_state_evolution")
            if isinstance(dimensions, Mapping)
            else None
        )
        if not isinstance(joint, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model content amendment `{key}` has no joint-law dimension"
            )
        updates: dict[str, str] = {}
        for raw_path, raw_value in raw_updates.items():
            path = str(raw_path or "").strip()
            value = str(raw_value or "").strip()
            if path not in ATTESTED_SEMANTIC_MODEL_CONTENT_PATHS:
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model content amendment `{key}` changes unsupported path `{path}`"
                )
            if not value:
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model content amendment `{key}` has an empty value at `{path}`"
                )
            _, section, field = path.split(".", 2)
            nested = joint.get(section)
            if not isinstance(nested, Mapping) or field not in nested:
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model content amendment `{key}` path `{path}` is absent from the archived response"
                )
            updates[path] = value
        amendments[key] = updates
    return amendments


def _expanded_lean_route_location_error(folder: Path, value: object) -> str:
    """Check that an amendment's Lean-route locator is live and local.

    The route is provenance for a semantic descriptor, not the mechanism that
    decides whether two statements are equivalent.  Requiring a current local
    coordinate nevertheless prevents a reviewer from supplying an uncheckable
    declaration-name-only explanation for a law-bridge repair.
    """

    if not isinstance(value, str) or not value.strip():
        return "expanded Lean route has no source location"
    matches = list(_LEAN_FILE_LINE_RE.finditer(value))
    if not matches:
        return "expanded Lean route source location has no local .lean:line coordinate"
    for match in matches:
        try:
            path = (folder / match.group("path")).resolve()
            path.relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            return "expanded Lean route source location escapes the paper folder"
        if not path.is_file():
            return "expanded Lean route source location names no local Lean file"
        try:
            line_count = len(path.read_text(encoding="utf-8").splitlines())
        except OSError:
            return "expanded Lean route source location cannot be read"
        line = int(match.group("line"))
        if line < 1 or line > line_count:
            return (
                "expanded Lean route source location is outside its current Lean file"
            )
    return ""


def _attested_judgment_amendment_provenance_error(
    amendments: Mapping[str, Mapping[str, Any]], *, paper_dir: Path
) -> str:
    """Require live local Lean coordinates for a newly attested proof route.

    A complete current attestation may correct a legacy classification to
    ``proved_from_primitives``.  That correction must carry the actual checked
    route instead of relying on a free-form explanation or a declaration name.
    """

    for key, amendment in sorted(amendments.items()):
        if "lean_derivation" not in amendment:
            continue
        error = _expanded_lean_route_location_error(
            paper_dir, amendment.get("lean_derivation")
        )
        if error:
            return f"attestation amendment `{key}` {error}"
    return ""


def _source_identity_locator_ranges(value: object) -> list[tuple[str, int, int]]:
    """Extract source spans from generated association identities recursively."""

    ranges: list[tuple[str, int, int]] = []
    if isinstance(value, Mapping):
        identities = value.get("source_item_identities")
        if isinstance(identities, list):
            for identity in identities:
                if not isinstance(identity, Mapping):
                    continue
                location = identity.get("source_location")
                if isinstance(location, str):
                    for match in EVIDENCE.SOURCE_FILE_LINE_RE.finditer(location):
                        start = int(match.group("start"))
                        ranges.append(
                            (
                                match.group("path"),
                                start,
                                int(match.group("end") or start),
                            )
                        )
        for child in value.values():
            ranges.extend(_source_identity_locator_ranges(child))
    elif isinstance(value, list):
        for child in value:
            ranges.extend(_source_identity_locator_ranges(child))
    return ranges


def _source_anchor_overlaps_generated_identity(
    anchor: object, semantic_member: Mapping[str, Any]
) -> bool:
    if not isinstance(anchor, str):
        return False
    anchor_ranges = [
        (
            match.group("path"),
            int(match.group("start")),
            int(match.group("end") or match.group("start")),
        )
        for match in EVIDENCE.SOURCE_FILE_LINE_RE.finditer(anchor)
    ]
    identity_ranges = _source_identity_locator_ranges(semantic_member)
    return any(
        anchor_path == identity_path
        and not (anchor_end < identity_start or identity_end < anchor_start)
        for anchor_path, anchor_start, anchor_end in anchor_ranges
        for identity_path, identity_start, identity_end in identity_ranges
    )


def _semantic_model_content_amendment_provenance_error(
    attestation: Mapping[str, Any],
    amendments: Mapping[str, Mapping[str, str]],
    *,
    raw_audit: Mapping[str, Any],
    paper_dir: Path,
) -> str:
    """Authenticate the source/Lean evidence attached to a narrow text patch.

    A current semantic revalidation is still a human review.  This transport
    only permits its three narrowly scoped law-bridge fields to change, so the
    accompanying record must identify the exact current generated semantic
    group, a live source span, and a live expanded-Lean coordinate.  The group
    descriptor is the mathematical identity; judgment keys and declaration
    strings merely locate the already-generated record and cannot remap it.
    """

    if not amendments:
        return ""
    raw_provenance = attestation.get("judgment_amendment_provenance")
    if not isinstance(raw_provenance, Mapping):
        return "semantic-model content amendments lack amendment provenance"
    if raw_provenance.get("content_repair_count") != len(amendments):
        return "semantic-model content amendment provenance has the wrong repair count"
    repairs = raw_provenance.get("content_repairs")
    if not isinstance(repairs, list):
        return "semantic-model content amendment provenance has no content-repair list"
    groups, group_errors = raw_source_record_obligation_groups(raw_audit)
    seen: set[str] = set()
    for repair in repairs:
        if not isinstance(repair, Mapping):
            return "semantic-model content amendment provenance has a malformed repair"
        key = str(repair.get("judgment_key") or "").strip()
        if not key or key not in amendments or key in seen:
            return "semantic-model content amendment provenance does not cover each amended group exactly once"
        seen.add(key)
        if key in group_errors or not isinstance(groups.get(key), Mapping):
            return "semantic-model content amendment has no current generated group"
        group = groups[key]
        if _sha256(repair.get("current_group_descriptor_sha256")) != _sha256(
            group.get("descriptor_sha256")
        ):
            return "semantic-model content amendment descriptor does not match the current generated group"

        source_anchor = repair.get("source_anchor")
        if not EVIDENCE.concrete_source_locator(source_anchor):
            return "semantic-model content amendment lacks a concrete source anchor"
        source_errors = EVIDENCE.source_file_line_anchor_errors(
            paper_dir, source_anchor
        )
        if source_errors:
            return "semantic-model content amendment source anchor is not current: " + "; ".join(
                source_errors
            )

        semantic_members = group.get("semantic_model_items")
        if not isinstance(semantic_members, list) or len(semantic_members) != 1:
            return "semantic-model content amendment does not have one current semantic-model route"
        semantic_member = semantic_members[0]
        if not isinstance(semantic_member, Mapping):
            return "semantic-model content amendment has a malformed current semantic-model route"
        if not _source_anchor_overlaps_generated_identity(
            source_anchor, semantic_member
        ):
            return (
                "semantic-model content amendment source anchor does not overlap "
                "a current generated source association"
            )
        route = repair.get("expanded_lean_route")
        if not isinstance(route, Mapping):
            return "semantic-model content amendment lacks an expanded Lean route"
        direct_route = str(route.get("direct_declaration") or "").strip()
        if not direct_route or direct_route != str(
            semantic_member.get("qualified_declaration") or ""
        ).strip():
            return "semantic-model content amendment Lean route does not locate the generated endpoint"
        if route_error := _expanded_lean_route_location_error(
            paper_dir, route.get("source_location")
        ):
            return route_error

        failures = repair.get("validator_failures_before_repair")
        if not isinstance(failures, list) or not failures or any(
            not isinstance(value, str) or not value.strip() for value in failures
        ):
            return "semantic-model content amendment lacks concrete pre-repair validator findings"
        proposal = repair.get("proposed_semantic_repair")
        if not isinstance(proposal, Mapping):
            return "semantic-model content amendment lacks a source-to-Lean repair record"
        if (
            str(proposal.get("kind") or "").strip()
            != "source_backed_expanded_law_bridge_content_repair"
        ):
            return "semantic-model content amendment has the wrong repair kind"
        changed_fields = proposal.get("changed_fields")
        if not isinstance(changed_fields, Mapping) or {
            str(path): str(value)
            for path, value in changed_fields.items()
        } != dict(amendments[key]):
            return "semantic-model content amendment repair fields differ from the attested patch"
        if not EVIDENCE.meaningful_semantic_text(
            proposal.get("source_to_lean_bridge")
        ):
            return "semantic-model content amendment lacks a semantic source-to-Lean bridge"
    if seen != set(amendments):
        return "semantic-model content amendment provenance omits an amended group"
    return ""


def _apply_semantic_model_content_amendments(
    items: Mapping[str, Mapping[str, Any]],
    amendments: Mapping[str, Mapping[str, str]],
) -> None:
    """Apply a previously validated source-law bridge patch in place."""

    for key, updates in amendments.items():
        item = items.get(key)
        if not isinstance(item, dict):  # Defensive: callers validate the ledger.
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model content amendment `{key}` has no mutable response"
            )
        dimensions = item.get("semantic_model_dimensions")
        joint = (
            dimensions.get("joint_law_and_state_evolution")
            if isinstance(dimensions, dict)
            else None
        )
        if not isinstance(joint, dict):  # Defensive: validated against snapshot.
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model content amendment `{key}` has no mutable joint-law dimension"
            )
        for path, value in updates.items():
            _, section, field = path.split(".", 2)
            nested = joint.get(section)
            if not isinstance(nested, dict):  # Defensive: validated against snapshot.
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model content amendment `{key}` path `{path}` is no longer mutable"
                )
            nested[field] = value


def _attested_semantic_model_dimension_amendments(
    attestation: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
    *,
    expected_keys: set[str],
) -> dict[str, dict[str, dict[str, str]]]:
    """Authorize a narrow current re-pin of cited model-convention receipts.

    A current semantic reviewer may confirm that a convention wording update
    leaves a dimension's substantive comparison intact.  This transport cannot
    alter the cited convention IDs, verdict, source explanation, or any other
    semantic response content; it replaces only the current digest for an ID
    the archived response already cited.
    """

    raw = attestation.get(ATTESTED_SEMANTIC_MODEL_DIMENSION_AMENDMENTS_FIELD, {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation semantic_model_dimension_amendments must be an object"
        )
    out: dict[str, dict[str, dict[str, str]]] = {}
    for raw_key, raw_dimensions in raw.items():
        key = str(raw_key or "").strip()
        prior = prior_items.get(key)
        if not key or key not in expected_keys or not isinstance(prior, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "semantic-model dimension amendment names a missing or non-prior selected response"
            )
        prior_dimensions = prior.get("semantic_model_dimensions")
        if not isinstance(prior_dimensions, Mapping) or not isinstance(raw_dimensions, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension amendment `{key}` has no dimension ledger"
            )
        rewritten: dict[str, dict[str, str]] = {}
        for raw_dimension, raw_update in raw_dimensions.items():
            dimension = str(raw_dimension or "").strip()
            prior_dimension = prior_dimensions.get(dimension)
            if not dimension or not isinstance(prior_dimension, Mapping) or not isinstance(
                raw_update, Mapping
            ):
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension amendment `{key}` is malformed"
                )
            if set(raw_update) != {"model_convention_sha256_by_id"}:
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension amendment `{key}.{dimension}` may only re-pin model convention digests"
                )
            prior_ids = prior_dimension.get("model_convention_ids")
            prior_digests = prior_dimension.get("model_convention_sha256_by_id")
            supplied = raw_update.get("model_convention_sha256_by_id")
            if not isinstance(prior_ids, list) or not isinstance(prior_digests, Mapping) or not isinstance(
                supplied, Mapping
            ):
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension amendment `{key}.{dimension}` has no cited convention digest ledger"
                )
            ids = {str(value).strip() for value in prior_ids if str(value).strip()}
            supplied_digests = {
                str(convention_id).strip(): _sha256(digest)
                for convention_id, digest in supplied.items()
                if str(convention_id).strip()
            }
            if (
                not ids
                or set(supplied_digests) != ids
                or any(not digest for digest in supplied_digests.values())
            ):
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension amendment `{key}.{dimension}` must re-pin exactly its already cited convention IDs"
                )
            rewritten[dimension] = supplied_digests
        if not rewritten:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension amendment `{key}` must update at least one dimension"
            )
        out[key] = rewritten
    return out


def _apply_semantic_model_dimension_amendments(
    items: Mapping[str, Mapping[str, Any]],
    amendments: Mapping[str, Mapping[str, Mapping[str, str]]],
) -> None:
    """Apply already-validated convention-digest re-pins to semantic dimensions.

    The caller has parsed the attestation against the immutable prior response,
    so this only mutates the one generated response field that the compact
    amendment format permits.  Keeping this shared by complete and selected
    rebinds prevents the complete path from accepting an amendment that it
    then silently drops.
    """

    for key, dimensions_to_repin in amendments.items():
        item = items.get(key)
        if not isinstance(item, dict):  # Defensive after attestation parsing.
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension amendment `{key}` has no mutable response"
            )
        dimensions = item.get("semantic_model_dimensions")
        if not isinstance(dimensions, dict):  # Defensive after parser checks.
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension amendment `{key}` has no mutable dimension ledger"
            )
        for dimension, digests in dimensions_to_repin.items():
            dimension_response = dimensions.get(dimension)
            if not isinstance(dimension_response, dict):
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension amendment `{key}.{dimension}` is no longer mutable"
                )
            dimension_response["model_convention_sha256_by_id"] = copy.deepcopy(
                dict(digests)
            )


def _current_semantic_model_association_pin(
    group: Mapping[str, Any], *, expected_descriptor_sha256: str
) -> tuple[str, str]:
    """Return the one current schema-2 pin for a selected semantic group.

    This is a structural receipt check, not a lookup by a declaration or
    source-map name.  The caller has already resolved the group uniquely by
    its complete generated semantic descriptor.  We then follow the generated
    association container in the same fixed precedence used by the target
    disposition validator and recompute its semantic association digest.
    """

    if _sha256(group.get("descriptor_sha256")) != expected_descriptor_sha256:
        return "", "current semantic group descriptor differs from the attested descriptor"
    semantic_members = group.get("semantic_model_items")
    if not isinstance(semantic_members, list) or len(semantic_members) != 1:
        return "", "current semantic group does not have exactly one semantic-model item"
    item = semantic_members[0]
    if not isinstance(item, Mapping):
        return "", "current semantic group has a malformed semantic-model item"
    association: Mapping[str, Any] | None = None
    association_field = ""
    for field in (
        "statement_source_component_association",
        "source_statement_association",
        "semantic_contract_source_association",
        "semantic_contract_group",
    ):
        candidate = item.get(field)
        if isinstance(candidate, Mapping):
            association = candidate
            association_field = field
            break
    if association is None:
        return "", "current semantic group has no generated semantic source association"
    if association.get("schema") != 2:
        return "", "current semantic source association does not use schema 2"
    identities = association.get("source_item_identities")
    signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(identities, list) or not identities or not isinstance(signature, Mapping):
        return "", "current semantic source association lacks identities or elaborated signature"
    semantic_identities: list[str] = []
    for identity in identities:
        if not isinstance(identity, Mapping):
            return "", "current semantic source association has a malformed source identity"
        digest = _sha256(identity.get("source_semantic_sha256"))
        if not digest or digest in semantic_identities:
            return "", "current semantic source association has malformed or duplicate semantic identities"
        semantic_identities.append(digest)
    supplied = _sha256(association.get("semantic_association_sha256"))
    if association_field == "statement_source_component_association":
        component_pin, component_error = (
            statement_source_component_effective_semantic_pin(association)
        )
        if component_error or supplied != component_pin:
            return "", (
                "current statement source-component association pin is missing, "
                "malformed, or stale"
            )
        return component_pin, ""
    if (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        review_pin, review_error = statement_source_review_effective_semantic_pin(
            association
        )
        if review_error or supplied != review_pin:
            return "", (
                "current authenticated statement source-review association pin "
                "is missing, malformed, or stale"
            )
        return review_pin, ""
    expected = semantic_association_record_digest(semantic_identities, signature)
    if not supplied or not expected or supplied != expected:
        return "", "current semantic source association pin is missing, malformed, or stale"
    return supplied, ""


def _attested_semantic_model_dimension_association_amendments(
    attestation: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
    *,
    expected_keys: set[str],
    current_raw_audit: Mapping[str, Any] | None,
    selected_descriptors: Mapping[str, str] | None,
    judgment_amendments: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, str]]:
    """Read exact manual re-pins for semantic-model dimension associations.

    A selected current attestation can repair a stale per-dimension
    ``semantic_association_sha256`` only when the reviewer explicitly binds
    the repair to one *unique* current semantic descriptor, names every
    already-pinned dimension on that response, and supplies the pin generated
    by that exact current semantic association.  This is not descriptor reuse:
    it is a manual current-review amendment inside an attestation that already
    covers the complete selected complement.

    The amendment changes no source text, verdict, disposition, convention
    identifier, locator, or reason.  A full ``semantic_model_dimensions``
    rewrite must use the existing judgment-amendment lane instead and cannot
    be combined with this narrow re-pin.
    """

    raw = attestation.get(
        ATTESTED_SEMANTIC_MODEL_DIMENSION_ASSOCIATION_AMENDMENTS_FIELD, {}
    )
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation semantic_model_dimension_association_amendments must be an object"
        )
    if not raw:
        return {}
    if current_raw_audit is None or selected_descriptors is None:
        raise SourceRecordCurrentRevalidationError(
            "semantic-model dimension association amendments require the exact current raw descriptor ledger"
        )
    groups, group_errors = raw_source_record_obligation_groups(current_raw_audit)
    if group_errors:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has malformed groups for semantic-model association amendments"
        )
    descriptor_index: dict[str, list[tuple[str, Mapping[str, object]]]] = {}
    for current_key, group in groups.items():
        descriptor = _sha256(group.get("descriptor_sha256"))
        if descriptor:
            descriptor_index.setdefault(descriptor, []).append((current_key, group))

    out: dict[str, dict[str, str]] = {}
    for raw_key, raw_entry in raw.items():
        key = str(raw_key or "").strip()
        prior = prior_items.get(key)
        if not key or key not in expected_keys or not isinstance(prior, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "semantic-model dimension association amendment names a missing or non-prior selected response"
            )
        if key not in selected_descriptors:
            raise SourceRecordCurrentRevalidationError(
                "semantic-model dimension association amendment is absent from the selected descriptor ledger"
            )
        if not isinstance(raw_entry, Mapping) or set(raw_entry) != {
            "current_group_semantic_descriptor_sha256",
            "dimensions",
        }:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` has unsupported fields"
            )
        descriptor = _sha256(raw_entry.get("current_group_semantic_descriptor_sha256"))
        if not descriptor or descriptor != selected_descriptors[key]:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` has a stale current descriptor"
            )
        candidates = descriptor_index.get(descriptor, [])
        if len(candidates) != 1:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` does not identify exactly one current semantic group"
            )
        current_key, current_group = candidates[0]
        if current_key != key:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` descriptor resolves to a different current ledger address"
            )
        if "semantic_model_dimensions" in judgment_amendments.get(key, {}):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` cannot accompany a full dimension rewrite"
            )
        current_pin, pin_error = _current_semantic_model_association_pin(
            current_group, expected_descriptor_sha256=descriptor
        )
        if pin_error:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` {pin_error}"
            )
        prior_dimensions = prior.get("semantic_model_dimensions")
        raw_dimensions = raw_entry.get("dimensions")
        if not isinstance(prior_dimensions, Mapping) or not isinstance(raw_dimensions, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` has no dimension ledger"
            )
        prior_pinned: dict[str, str] = {}
        for raw_dimension, value in prior_dimensions.items():
            dimension = str(raw_dimension or "").strip()
            if not dimension or not isinstance(value, Mapping):
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension association amendment `{key}` has a malformed archived dimension"
                )
            old_pin = _sha256(value.get("semantic_association_sha256"))
            if old_pin:
                prior_pinned[dimension] = old_pin
        if not prior_pinned:
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` has no existing source-pinned dimensions"
            )
        supplied: dict[str, str] = {}
        for raw_dimension, raw_pin in raw_dimensions.items():
            dimension = str(raw_dimension or "").strip()
            pin = _sha256(raw_pin)
            if not dimension or not pin or dimension in supplied:
                raise SourceRecordCurrentRevalidationError(
                    f"semantic-model dimension association amendment `{key}` has a malformed dimension pin"
                )
            supplied[dimension] = pin
        if set(supplied) != set(prior_pinned):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` must enumerate exactly every existing source-pinned dimension"
            )
        if any(pin != current_pin for pin in supplied.values()):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` has a noncurrent association pin"
            )
        if any(old_pin == current_pin for old_pin in prior_pinned.values()):
            raise SourceRecordCurrentRevalidationError(
                f"semantic-model dimension association amendment `{key}` includes a dimension whose pin is already current"
            )
        out[key] = supplied
    return out


def _semantic_judgment_ledger(
    items: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Return sidecar decisions with generated transport removed."""

    ledger: dict[str, dict[str, Any]] = {}
    for raw_key, raw_value in items.items():
        key = str(raw_key)
        ledger[key] = {
            field: copy.deepcopy(value)
            for field, value in raw_value.items()
            if not field.startswith("source_record_")
            and field != PRIOR_ITEM_RECEIPT_FIELD
        }
    return ledger


def _exact_descriptor_group_ledger(
    raw_audit: Mapping[str, Any], *, label: str
) -> tuple[dict[str, str], dict[str, dict[str, object]]]:
    """Return one complete semantic-descriptor ledger for schema transport.

    A judgment key is only the storage address of a response.  It is never
    used to decide that an archived response is semantically reusable: every
    address below carries the complete, generator-derived group descriptor
    produced from its raw members.  Keeping the address fixed merely prevents
    an otherwise equal descriptor from being applied to a different saved
    response slot.
    """

    groups, group_errors = raw_source_record_obligation_groups(raw_audit)
    if group_errors:
        examples = ", ".join(sorted(group_errors)[:5])
        raise SourceRecordCurrentRevalidationError(
            f"{label} raw audit has malformed semantic descriptor group(s): {examples}"
        )
    ledger: dict[str, str] = {}
    for raw_key, group in groups.items():
        key = str(raw_key or "").strip()
        descriptor = _sha256(group.get("descriptor_sha256"))
        if not key or not descriptor or key in ledger:
            raise SourceRecordCurrentRevalidationError(
                f"{label} raw audit has an empty, duplicate, or unpinned semantic descriptor group"
            )
        ledger[key] = descriptor
    if not ledger:
        raise SourceRecordCurrentRevalidationError(
            f"{label} raw audit has no semantic descriptor groups"
        )
    return ledger, groups


def _exact_descriptor_schema_transport_update(
    raw_members: object, response: Mapping[str, Any]
) -> dict[str, str] | None:
    """Return one admissible legacy schema closure, or ``None``.

    ``validated_source_assumption`` already denotes literal source credit.
    Older v10 responses sometimes predate the explicit
    ``source_target_disposition`` field.  This helper may make that existing
    meaning syntactically explicit only for a generated direct schema-2 source
    route with retained source evidence.  It does not reinterpret a response:
    any convention, corrected-target, existing disposition (including an
    empty/invalid one), recursive route, semantic-model dimension, or changed
    classification stays out of this lane.
    """

    if str(response.get("classification") or "").strip() != (
        "validated_source_assumption"
    ):
        return None
    if "source_target_disposition" in response:
        return None
    if any(
        field in response
        for field in _EXACT_DESCRIPTOR_SCHEMA_TRANSPORT_PROHIBITED_RESPONSE_FIELDS
    ):
        return None
    if not (
        str(response.get("source_location") or "").strip()
        or str(response.get("source_evidence") or "").strip()
    ):
        return None
    projection, projection_error = source_record_response_association_projection(
        raw_members
    )
    if (
        projection_error
        or projection is None
        or not projection.top_level_semantic_association_sha256
    ):
        return None
    return {"source_target_disposition": "literal_source_match"}


def exact_descriptor_schema_transport_updates(
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, str]]:
    """Plan only exact-descriptor v10 schema transport, without issuing evidence.

    This side-effect-free helper is the narrow alternative to reissuing a
    whole judgment ledger when a validator introduces the explicit literal
    target-disposition field.  It first requires that *every* prior/current
    generated response group has the same complete semantic descriptor at the
    same saved response address.  The descriptor is built from raw semantic
    members, source associations, scoped source-model requirements, and the
    relevant expanded Lean obligation; neither a declaration name nor a
    function name establishes reuse.

    The only emitted update is
    ``validated_source_assumption_add_literal_source_disposition``.  It adds
    ``literal_source_match`` to a response which was already a direct,
    source-pinned ``validated_source_assumption`` and already retains source
    evidence.  It never changes prose, a classification, source association,
    source locator, convention digest, or corrected-target metadata.  A
    caller must still bind the resulting candidate to a current human review
    and run the shared target-disposition validators before it can become
    evidence.

    This is deliberately all-or-nothing on descriptor equality.  For example,
    LG24's 2026-08-13 pre-v11/current raw receipts have 0 descriptor-equal
    groups out of 117, so this helper rejects them rather than disguising a
    semantic re-review as a schema migration.
    """

    prior_ledger, prior_groups = _exact_descriptor_group_ledger(
        prior_raw_audit, label="prior"
    )
    current_ledger, current_groups = _exact_descriptor_group_ledger(
        current_raw_audit, label="current"
    )
    prior_keys = set(prior_ledger)
    current_keys = set(current_ledger)
    response_keys = {str(key or "").strip() for key in prior_items}
    if not response_keys or "" in response_keys:
        raise SourceRecordCurrentRevalidationError(
            "exact-descriptor schema transport has an empty or missing prior response key"
        )
    if response_keys != prior_keys or prior_keys != current_keys:
        raise SourceRecordCurrentRevalidationError(
            "exact-descriptor schema transport requires exact prior/current/raw response-key coverage"
        )
    changed = sorted(
        key
        for key in prior_keys
        if prior_ledger[key] != current_ledger[key]
    )
    if changed:
        raise SourceRecordCurrentRevalidationError(
            "exact-descriptor schema transport refuses semantic descriptor drift "
            f"({len(changed)} group(s); examples: " + ", ".join(changed[:5]) + ")"
        )

    updates: dict[str, dict[str, str]] = {}
    for key in sorted(prior_keys):
        response = prior_items.get(key)
        if not isinstance(response, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"exact-descriptor schema transport prior response `{key}` is not an object"
            )
        group = current_groups.get(key)
        if not isinstance(group, Mapping):  # defensive after exact-key check.
            raise SourceRecordCurrentRevalidationError(
                f"exact-descriptor schema transport current group `{key}` is missing"
            )
        update = _exact_descriptor_schema_transport_update(
            group.get("raw_members"), response
        )
        if update is not None:
            updates[key] = update
    return updates


def _reproject_current_generated_association_credentials(
    raw_audit: Mapping[str, Any],
    items: dict[str, dict[str, Any]],
    *,
    paper_dir: Path,
    reject_existing: bool = False,
    source_target_statement_map: Mapping[str, Any] | None | object = (
        _SOURCE_TARGET_STATEMENT_MAP_UNSET
    ),
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> None:
    """Refresh raw-derived source credentials from one authenticated source map.

    This intentionally does not infer semantic equivalence from a declaration
    spelling or a judgment key.  Each response is projected from the exact
    generated raw members for that response key.  The default source map is
    the live closeout context.  Historical-composition replay instead passes
    the byte-pinned archived map explicitly, so it cannot validate an old
    response against a later map revision.  This helper changes only
    credentials whose expected values are deterministically generated by the
    shared target-disposition contract.  A selected replacement first asks to
    reject reviewer-supplied credentials, then the ordinary current rebind may
    replay the generated values.
    """

    if source_target_statement_map is _SOURCE_TARGET_STATEMENT_MAP_UNSET:
        status_payload = _load_json_object(paper_dir / "status.json")
        review_surface = status_payload.get("review_surface")
        if not isinstance(review_surface, dict):
            raise SourceRecordCurrentRevalidationError(
                "status.json has no object-valued review_surface for current association projection"
            )
        statement_map, _source_proof_fidelity = (
            REPOSITORY.source_record_target_disposition_context(
                paper_dir, review_surface
            )
        )
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                paper_dir,
                raw_audit,
                status_payload=status_payload,
            )
        )
    else:
        if source_target_statement_map is not None and not isinstance(
            source_target_statement_map, Mapping
        ):
            raise SourceRecordCurrentRevalidationError(
                "source association projection received an invalid statement-map override"
            )
        statement_map = source_target_statement_map
        # An archived replay must not pull a live regularity ledger into its
        # credential projection.  A historical regularity claim therefore
        # fails closed unless its caller supplies an immutable context.
        regularity_context = configured_assumption_formalization_regularity_context
    current_groups = generated_judgment_items(raw_audit)
    for raw_key, response in list(items.items()):
        key = str(raw_key)
        members = current_groups.get(key)
        if members is None:
            raise SourceRecordCurrentRevalidationError(
                f"current association projection has no generated raw group for `{key}`"
            )
        projected, projection_error = project_source_record_response_association_pins(
            members,
            response,
            judgment_key=key,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=regularity_context,
            reject_existing=reject_existing,
            replace_generated_credentials=not reject_existing,
        )
        if projection_error or projected is None:
            raise SourceRecordCurrentRevalidationError(
                f"current association projection for `{key}` failed: "
                + (projection_error or "no projected response")
            )
        items[key] = projected


def _loaded_snapshot_matches(
    path: Path, supplied: Mapping[str, Any], *, label: str
) -> tuple[dict[str, Any], str]:
    """Read an immutable snapshot once and reject divergent caller input."""

    saved, saved_sha256 = _read_json_object_with_sha256(path)
    if _canonical_digest(saved) != _canonical_digest(supplied):
        raise SourceRecordCurrentRevalidationError(
            f"supplied {label} does not match the immutable snapshot file bytes"
        )
    return saved, saved_sha256


def _aggregate_bound_unkinded_recursive_field(
    section: str, item: Mapping[str, Any]
) -> bool:
    """Return whether one verified recursive raw member has no item-level kind.

    Recursive fields are generated consequences of an explicitly authenticated
    parent route, not independently classified source judgments.  A generator
    may therefore give one a schema-5 item receipt while deliberately omitting
    ``kind``.  It remains bound by the aggregate receipt: this helper permits
    no narrow pin for that one structural case.  It does not infer recursive
    status from a declaration, field, or judgment-key spelling.
    """

    if section != "recursive_field_items":
        return False
    if str(item.get("kind") or "").strip():
        return False
    # This establishes the exact current schema-5 item receipt, including its
    # generated semantic/context identities and reviewed Lean-route signature.
    if not source_record_item_reuse_eligible(
        item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return False
    route = item.get("recursive_field_explicit_parent_route")
    if not isinstance(route, Mapping):
        return False
    if (
        route.get("schema") != 1
        or str(route.get("inheritance_mode") or "").strip()
        != "explicit_parent_route_and_field_scope"
    ):
        return False
    route_digest = _sha256(route.get("association_sha256"))
    if not route_digest or route_digest != recursive_field_parent_route_record_digest(route):
        return False
    chain = route.get("field_chain")
    if not isinstance(chain, list) or not chain:
        return False
    for link in chain:
        if not isinstance(link, Mapping) or set(link) != {"structure", "field"}:
            return False
        if not str(link.get("structure") or "").strip() or not str(
            link.get("field") or ""
        ).strip():
            return False
    return True


def _current_item_pins(
    grouped_items: list[tuple[str, Mapping[str, Any]]],
) -> list[dict[str, Any]]:
    """Return a narrow current pin only for one complete eligible raw member.

    A response key can represent several raw views: a boundary premise plus a
    conclusion dependency, or an eligible view plus an aggregate-only one.
    Even equal-looking duplicate tuple pins do not prove the reviewer saw every
    member.  The current aggregate receipt is therefore mandatory whenever a
    group has more than one raw member or one nonreusable member.
    """

    if len(grouped_items) != 1:
        return []
    section, item = grouped_items[0]
    if not source_record_item_reuse_eligible(
        item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return []
    kind = str(item.get("kind") or "").strip()
    digest = _sha256(item.get("source_record_item_sha256"))
    if not kind:
        if _aggregate_bound_unkinded_recursive_field(section, item):
            return []
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has a reusable judgment item without kind"
        )
    if not digest:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has a reusable judgment item without digest"
        )
    return [
        {
            "kind": kind,
            "source_record_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            "source_record_item_sha256": digest,
        }
    ]


def rebound_sidecar(
    raw_audit: Mapping[str, Any],
    prior_sidecar: Mapping[str, Any],
    attestation: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
    attestation_path: Path,
    output_sidecar_path: Path,
) -> dict[str, Any]:
    """Return a sidecar rebound through an explicit complete current review.

    This function validates only generated/raw/attestation structure.  The
    caller must run ``validate_rebound_sidecar`` before writing its result so
    current source-target disposition and semantic-model checks also pass.
    """

    if prior_sidecar_path.resolve() == output_sidecar_path.resolve():
        raise SourceRecordCurrentRevalidationError(
            "prior sidecar must be an immutable snapshot distinct from the output sidecar"
        )
    saved_attestation, saved_attestation_sha256 = _read_json_object_with_sha256(
        attestation_path
    )
    if _canonical_digest(saved_attestation) != _canonical_digest(attestation):
        raise SourceRecordCurrentRevalidationError(
            "in-memory attestation does not match the attestation file bytes"
        )
    prior_sidecar, prior_sidecar_sha256 = _loaded_snapshot_matches(
        prior_sidecar_path, prior_sidecar, label="prior sidecar"
    )
    # All later validation and output use the exact bytes just read above;
    # caller-supplied mappings cannot substitute a different semantic object.
    attestation = saved_attestation
    raw_error = _raw_audit_error(raw_audit, paper=paper, paper_dir=paper_dir)
    if raw_error:
        raise SourceRecordCurrentRevalidationError(raw_error)
    prior_items = _sidecar_items(prior_sidecar, paper=paper)
    prior_error = _prior_sidecar_error(prior_sidecar, prior_items)
    if prior_error:
        raise SourceRecordCurrentRevalidationError(prior_error)
    generated_keys = set(generated_judgment_items(raw_audit))
    prior_keys = set(prior_items)
    if key_delta_error := _attested_key_delta_error(
        attestation, prior_keys=prior_keys, current_keys=generated_keys
    ):
        raise SourceRecordCurrentRevalidationError(key_delta_error)
    existing_keys = generated_keys & prior_keys
    new_judgments = _complete_new_judgments(
        attestation, required_keys=generated_keys - prior_keys
    )
    amendments = _attested_judgment_amendments(
        attestation, expected_keys=existing_keys
    )
    if amendment_provenance_error := _attested_judgment_amendment_provenance_error(
        amendments, paper_dir=paper_dir
    ):
        raise SourceRecordCurrentRevalidationError(amendment_provenance_error)
    content_amendments = _attested_semantic_model_content_amendments(
        attestation,
        prior_items,
        expected_keys=existing_keys,
        semantic_model_keys=semantic_model_judgment_keys(raw_audit),
    )
    dimension_amendments = _attested_semantic_model_dimension_amendments(
        attestation, prior_items, expected_keys=existing_keys
    )
    content_provenance_error = _semantic_model_content_amendment_provenance_error(
        attestation,
        content_amendments,
        raw_audit=raw_audit,
        paper_dir=paper_dir,
    )
    if content_provenance_error:
        raise SourceRecordCurrentRevalidationError(content_provenance_error)
    overlapping_amendments = sorted(set(amendments) & set(content_amendments))
    if overlapping_amendments:
        raise SourceRecordCurrentRevalidationError(
            "attestation cannot combine a whole-judgment and narrow semantic-model "
            "content amendment for the same key: "
            + ", ".join(overlapping_amendments[:5])
        )
    prior_audit_sha256 = _sha256(prior_sidecar.get("source_record_audit_sha256"))
    attestation_error = _attestation_error(
        attestation,
        paper=paper,
        paper_dir=paper_dir,
        prior_sidecar_path=prior_sidecar_path,
        prior_sidecar_sha256=prior_sidecar_sha256,
        prior_audit_sha256=prior_audit_sha256,
        raw_audit=raw_audit,
    )
    if attestation_error:
        raise SourceRecordCurrentRevalidationError(attestation_error)

    current_audit_sha256 = _sha256(raw_audit.get("source_record_audit_sha256"))
    current_groups = generated_judgment_items(raw_audit)
    result = copy.deepcopy(dict(prior_sidecar))
    result_items = {
        key: copy.deepcopy(prior_items[key]) for key in sorted(existing_keys)
    }
    result_items.update(
        {key: copy.deepcopy(value) for key, value in new_judgments.items()}
    )
    result["items"] = result_items
    for key, amendment in amendments.items():
        value = result_items.get(key)
        assert isinstance(value, dict)  # established by exact ledger equality above
        value.update(amendment)
    _apply_semantic_model_content_amendments(result_items, content_amendments)
    _apply_semantic_model_dimension_amendments(result_items, dimension_amendments)
    for raw_key, value in result_items.items():
        key = str(raw_key)
        assert isinstance(value, dict)
        if key in prior_items:
            historical_receipt = _historical_item_receipt(value)
            if historical_receipt:
                value[PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        value["source_record_audit_sha256"] = current_audit_sha256
        current_pins = _current_item_pins(current_groups[key])
        if current_pins:
            value["source_record_item_digest_schema"] = (
                SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            )
            value["source_record_item_sha256s"] = current_pins
            value["source_record_item_sha256"] = current_pins[0][
                "source_record_item_sha256"
            ]
    _reproject_current_generated_association_credentials(
        raw_audit, result_items, paper_dir=paper_dir
    )
    result["source_record_audit_sha256"] = current_audit_sha256
    result["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
    result[FORMALIZATION_REVIEW_PROTOCOL_FIELD] = str(
        attestation.get(FORMALIZATION_REVIEW_PROTOCOL_FIELD) or ""
    ).strip().lower()
    result["validator"] = str(attestation.get("reviewer") or "").strip()
    result["validated_at"] = str(attestation.get("validated_at") or "").strip()
    result[CURRENT_REVALIDATION_FIELD] = {
        "schema": CURRENT_REVALIDATION_SCHEMA,
        "policy_version": CURRENT_REVALIDATION_POLICY_VERSION,
        "attestation_path": _relative_path(attestation_path, paper_dir),
        "attestation_sha256": saved_attestation_sha256,
        "prior_judgment_sidecar_path": _relative_path(prior_sidecar_path, paper_dir),
        "prior_judgment_sidecar_sha256": prior_sidecar_sha256,
        "current_judgment_sidecar_path": _relative_path(output_sidecar_path, paper_dir),
        "prior_source_record_audit_sha256": prior_audit_sha256,
        "current_source_record_audit_sha256": current_audit_sha256,
        "generated_judgment_keys_sha256": generated_judgment_keys_sha256(raw_audit),
        "generated_judgment_surface_sha256": generated_judgment_surface_sha256(raw_audit),
        "new_judgment_keys": sorted(generated_keys - prior_keys),
        "retired_prior_judgment_keys": sorted(prior_keys - generated_keys),
        "review_scope": "all_current_generated_judgment_keys",
        "narrow_item_receipts": (
            "legacy pins retained only under prior_source_record_item_receipt; "
            "current schema-5 pin sets were regenerated from the attested raw receipt"
        ),
    }
    return result


def _archived_raw_target_context(
    raw_audit: Mapping[str, Any],
) -> tuple[Mapping[str, Any] | None, list[str]]:
    """Return the source context sealed inside one immutable raw receipt.

    This is only for replaying historical evidence before a differential
    descriptor comparison.  It intentionally does not make a historical
    judgment current: the subsequent current raw audit still rechecks every
    source-map/fidelity association.  The archived path instead verifies that
    the reviewed response is tied to the raw audit's own map fingerprint,
    generated source associations, and fidelity snapshot.
    """

    errors: list[str] = []
    surface = source_record_audit_surface_view(raw_audit)
    if not isinstance(surface, Mapping):
        return None, ["archived raw audit lacks source_record_audit_surface"]
    raw_map_digest = _sha256(raw_audit.get("paper_statement_map_sha256"))
    surface_map_digest = _sha256(surface.get("paper_statement_map_sha256"))
    if not raw_map_digest or raw_map_digest != surface_map_digest:
        errors.append(
            "archived raw audit lacks a self-consistent paper-statement-map identity"
        )
    raw_fidelity = raw_audit.get("source_proof_fidelity")
    surface_fidelity = surface.get("source_proof_fidelity")
    if not isinstance(raw_fidelity, Mapping) or not isinstance(surface_fidelity, Mapping):
        errors.append("archived raw audit lacks an embedded source-proof-fidelity snapshot")
        return None, errors
    if canonical_digest_payload(raw_fidelity) != canonical_digest_payload(surface_fidelity):
        errors.append(
            "archived raw audit source-proof-fidelity snapshot does not match its raw surface"
        )
    if raw_audit.get("source_contract_association_error_count") not in {0, None}:
        errors.append("archived raw audit recorded source-contract association errors")
    if raw_audit.get("source_contract_association_errors") not in ([], None):
        errors.append("archived raw audit has nonempty source-contract association errors")
    if raw_audit.get("source_coverage_route_errors") not in ([], None):
        errors.append("archived raw audit has nonempty source-coverage route errors")
    target_route_error = source_record_target_route_error(raw_audit)
    if target_route_error:
        errors.append(
            "archived raw audit has invalid semantic target routing: "
            + target_route_error
        )
    if str(raw_audit.get("source_premise_consistency_error") or "").strip():
        errors.append("archived raw audit recorded a source-premise consistency error")
    return (dict(surface_fidelity) if not errors else None), errors


def _target_disposition_errors(
    raw_audit: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper_dir: Path,
    historical_receipt_only: bool = False,
    historical_statement_map: Mapping[str, Any] | None = None,
) -> list[str]:
    """Run shared validators against either current or archived source context.

    The archived mode is confined to immutable-receipt replay.  It validates
    response pins against raw-generated associations and the raw fidelity
    snapshot, while current closeout validation keeps using live map/fidelity
    files.  Descriptor-authenticated transport into a new raw audit always
    takes the latter path.
    """

    if historical_receipt_only:
        source_proof_fidelity, context_errors = _archived_raw_target_context(raw_audit)
        if context_errors:
            return context_errors
        # An archived source-map snapshot is optional for ordinary literal
        # replay, but is the only admissible way for historical replay to
        # validate an approved corrected target.  The caller authenticates
        # its bytes against the raw audit before passing it here.
        statement_map = historical_statement_map
        status: object | None = None
        regularity_context = None
    else:
        status_payload = _load_json_object(paper_dir / "status.json")
        review_surface = status_payload.get("review_surface")
        if not isinstance(review_surface, dict):
            return ["status.json has no object-valued review_surface"]
        statement_map, source_proof_fidelity = REPOSITORY.source_record_target_disposition_context(
            paper_dir, review_surface
        )
        status = status_payload.get("status")
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                paper_dir,
                raw_audit,
                status_payload=status_payload,
            )
        )
    responses = sidecar.get("items")
    if not isinstance(responses, Mapping):  # defensive, checked earlier.
        return ["rebound sidecar has no object-valued items ledger"]
    errors: list[str] = []
    for key, grouped_items in sorted(generated_judgment_items(raw_audit).items()):
        response = responses.get(key)
        if not isinstance(response, Mapping):
            errors.append(f"{key}: no rebound response")
            continue
        for section, item in grouped_items:
            if section == "semantic_model_items":
                dimensions = item.get("dimensions")
                submitted = response.get("semantic_model_dimensions")
                if not isinstance(dimensions, list) or not isinstance(submitted, Mapping):
                    errors.append(f"{key}: semantic-model dimensions are incomplete")
                    continue
                for dimension in dimensions:
                    if not isinstance(dimension, Mapping):
                        errors.append(f"{key}: malformed generated semantic-model dimension")
                        continue
                    dimension_id = str(dimension.get("id") or "").strip()
                    dimension_response = submitted.get(dimension_id)
                    if not isinstance(dimension_response, Mapping):
                        errors.append(f"{key}.{dimension_id}: missing semantic-model response")
                        continue
                    for error in semantic_target_disposition_errors(
                        item,
                        dimension_response,
                        statement_map=statement_map,
                        source_proof_fidelity=source_proof_fidelity,
                        validated_vocabulary_binding_source_item_ids=(
                            raw_audit.get(
                                "source_coverage_validated_vocabulary_binding_source_items"
                            )
                        ),
                        validated_vocabulary_direct_route_source_item_ids=(
                            raw_audit.get(
                                "source_coverage_validated_vocabulary_direct_route_source_items"
                            )
                        ),
                        historical_receipt_only=historical_receipt_only,
                    ):
                        errors.append(f"{key}.{dimension_id}: {error}")
            elif section == "recursive_field_items":
                for error in recursive_field_target_disposition_errors(
                    item,
                    response,
                    statement_map=statement_map,
                    source_proof_fidelity=source_proof_fidelity,
                    historical_receipt_only=historical_receipt_only,
                ):
                    errors.append(f"{key}: {error}")
            else:
                for error in source_input_target_disposition_errors(
                    item,
                    response,
                    statement_map=statement_map,
                    source_proof_fidelity=source_proof_fidelity,
                    status=status,
                    configured_assumption_formalization_regularity_context=(
                        regularity_context
                    ),
                    historical_receipt_only=historical_receipt_only,
                ):
                    errors.append(f"{key}: {error}")
    return errors


def _boundary_classification_errors(
    raw_audit: Mapping[str, Any], sidecar: Mapping[str, Any]
) -> list[str]:
    """Reject recursive-data labels when a value is a visible theorem input.

    Recursive field reviews may legitimately classify a nested carrier or
    container as data.  The same spelling can occur as a PaperInterface
    binder, where it is a source-facing premise and must instead be sourced,
    derived, explicitly partial, or left open.  This distinction comes from
    the generated audit role, never from a binder or declaration name.
    """

    raw_expected = raw_audit.get("expected_input_judgment_keys")
    if isinstance(raw_expected, list):
        expected = {
            str(key).strip() for key in raw_expected if str(key).strip()
        }
    else:
        expected = {
            str(item.get("judgment_key") or "").strip()
            for item in raw_audit.get("boundary_input_items") or []
            if isinstance(item, Mapping)
            and str(item.get("judgment_key") or "").strip()
        }
    responses = sidecar.get("items")
    if not isinstance(responses, Mapping):
        return ["rebound sidecar has no object-valued items ledger"]
    recursive_only = {
        "container_recursively_audited",
        "nonpropositional_witness_data",
        "derived_from_visible_boundary",
        "visible_boundary_component",
    }
    errors: list[str] = []
    for key in sorted(expected):
        response = responses.get(key)
        if not isinstance(response, Mapping):
            continue
        classification = str(response.get("classification") or "").strip()
        if classification in recursive_only:
            errors.append(
                f"{key}: classification `{classification}` is valid only for "
                "recursive fields, not a generated theorem-boundary input"
            )
    return errors


def _rebound_attestation_errors(
    metadata: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path,
    sidecar_items: Mapping[str, Mapping[str, Any]],
) -> list[str]:
    """Check that the saved rebind still points at an unchanged attestation."""

    path_text = str(metadata.get("attestation_path") or "").strip()
    if not path_text:
        return ["rebound sidecar has no attestation path"]
    relative = Path(path_text)
    if relative.is_absolute():
        return ["rebound sidecar attestation path is not paper-relative"]
    try:
        path = (paper_dir / relative).resolve()
        path.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError):
        return ["rebound sidecar attestation path escapes the paper folder"]
    if not path.is_file():
        return ["rebound sidecar attestation file is missing"]
    try:
        attestation, attestation_sha256 = _read_json_object_with_sha256(path)
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    if _sha256(metadata.get("attestation_sha256")) != attestation_sha256:
        return ["rebound sidecar attestation bytes no longer match its recorded hash"]
    errors: list[str] = []
    if attestation.get("schema") != CURRENT_REVALIDATION_SCHEMA:
        errors.append("rebound attestation has an unsupported schema")
    if attestation.get("artifact_kind") != CURRENT_REVALIDATION_ATTESTATION_KIND:
        errors.append("rebound attestation has the wrong artifact_kind")
    if attestation.get("policy_version") != CURRENT_REVALIDATION_POLICY_VERSION:
        errors.append("rebound attestation has the wrong policy version")
    if not formalization_protocol_receipt_matches(attestation, scope="review"):
        errors.append(
            "rebound attestation has no current formalization review-protocol receipt"
        )
    if any(
        bool(attestation.get(marker))
        for marker in (
            "non_evidence_scaffold",
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
        )
    ):
        errors.append("rebound attestation is marked as a non-evidence scaffold")
    if attestation.get("paper") != paper:
        errors.append("rebound attestation paper does not match the current paper")
    if attestation.get("reviewed_current_semantics") is not True:
        errors.append("rebound attestation no longer affirms current semantic review")
    if str(attestation.get("review_scope") or "").strip() != (
        "all_current_generated_judgment_keys"
    ):
        errors.append("rebound attestation has incomplete generated-key scope")
    if not str(attestation.get("reviewer") or "").strip() or not str(
        attestation.get("validated_at") or ""
    ).strip():
        errors.append("rebound attestation lacks reviewer or validation time")
    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(attestation.get("current_source_record_audit_sha256")) != current_digest:
        errors.append("rebound attestation is not bound to the current raw receipt")
    if _sha256(attestation.get("generated_judgment_keys_sha256")) != (
        generated_judgment_keys_sha256(raw_audit)
    ):
        errors.append("rebound attestation has stale generated-key coverage")
    if _sha256(attestation.get("generated_judgment_surface_sha256")) != (
        generated_judgment_surface_sha256(raw_audit)
    ):
        errors.append("rebound attestation has stale generated-item surface")
    prior_path_text = str(attestation.get("prior_judgment_sidecar_path") or "").strip()
    prior_relative = Path(prior_path_text)
    if not prior_path_text or prior_relative.is_absolute():
        errors.append("rebound attestation has no paper-relative prior-sidecar snapshot")
        return errors
    try:
        prior_path = (paper_dir / prior_relative).resolve()
        prior_path.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError):
        errors.append("rebound attestation prior-sidecar path escapes the paper folder")
        return errors
    if prior_path == output_sidecar_path.resolve():
        errors.append("rebound attestation prior-sidecar snapshot aliases the output sidecar")
        return errors
    if not prior_path.is_file():
        errors.append("rebound attestation prior-sidecar snapshot is missing")
        return errors
    try:
        snapshot, snapshot_sha256 = _read_json_object_with_sha256(prior_path)
        snapshot_items = _sidecar_items(snapshot, paper=paper)
    except SourceRecordCurrentRevalidationError as exc:
        errors.append(str(exc))
        return errors
    if _sha256(attestation.get("prior_judgment_sidecar_sha256")) != snapshot_sha256:
        errors.append("rebound attestation prior-sidecar snapshot bytes no longer match")
    if _sha256(metadata.get("prior_judgment_sidecar_sha256")) != snapshot_sha256:
        errors.append("rebound sidecar metadata prior-sidecar snapshot bytes no longer match")
    if str(metadata.get("prior_judgment_sidecar_path") or "").strip() != prior_path_text:
        errors.append("rebound sidecar metadata names a different prior-sidecar snapshot")
    if _sha256(metadata.get("prior_judgment_sidecar_sha256")) != _sha256(
        attestation.get("prior_judgment_sidecar_sha256")
    ):
        errors.append("rebound sidecar metadata prior snapshot hash does not match attestation")
    if _sha256(snapshot.get("source_record_audit_sha256")) != _sha256(
        attestation.get("prior_source_record_audit_sha256")
    ):
        errors.append("rebound attestation prior-sidecar aggregate receipt no longer matches")
    if _sha256(metadata.get("prior_source_record_audit_sha256")) != _sha256(
        attestation.get("prior_source_record_audit_sha256")
    ):
        errors.append("rebound sidecar metadata prior aggregate receipt does not match attestation")
    current_keys = set(generated_judgment_items(raw_audit))
    prior_keys = set(snapshot_items)
    if key_delta_error := _attested_key_delta_error(
        attestation, prior_keys=prior_keys, current_keys=current_keys
    ):
        errors.append(key_delta_error)
        return errors
    expected_new_keys = sorted(current_keys - prior_keys)
    expected_retired_keys = sorted(prior_keys - current_keys)
    if metadata.get("new_judgment_keys", []) != expected_new_keys:
        errors.append("rebound sidecar metadata has a stale new-judgment ledger")
    if metadata.get("retired_prior_judgment_keys", []) != expected_retired_keys:
        errors.append("rebound sidecar metadata has a stale retired-judgment ledger")
    prior_error = _prior_sidecar_error(snapshot, snapshot_items)
    if prior_error:
        errors.append("rebound attestation prior-sidecar snapshot is invalid: " + prior_error)
    try:
        new_judgments = _complete_new_judgments(
            attestation, required_keys=current_keys - prior_keys
        )
        existing_keys = current_keys & prior_keys
        amendments = _attested_judgment_amendments(
            attestation, expected_keys=existing_keys
        )
        if amendment_provenance_error := _attested_judgment_amendment_provenance_error(
            amendments, paper_dir=paper_dir
        ):
            errors.append(amendment_provenance_error)
            return errors
        content_amendments = _attested_semantic_model_content_amendments(
            attestation,
            snapshot_items,
            expected_keys=existing_keys,
            semantic_model_keys=semantic_model_judgment_keys(raw_audit),
        )
        dimension_amendments = _attested_semantic_model_dimension_amendments(
            attestation, snapshot_items, expected_keys=existing_keys
        )
    except SourceRecordCurrentRevalidationError as exc:
        errors.append(str(exc))
        return errors
    if provenance_error := _semantic_model_content_amendment_provenance_error(
        attestation,
        content_amendments,
        raw_audit=raw_audit,
        paper_dir=paper_dir,
    ):
        errors.append(provenance_error)
        return errors
    overlapping_amendments = sorted(set(amendments) & set(content_amendments))
    if overlapping_amendments:
        errors.append(
            "rebound attestation combines whole-judgment and narrow semantic-model "
            "content amendments for the same key: "
            + ", ".join(overlapping_amendments[:5])
        )
        return errors
    expected_items = {
        key: copy.deepcopy(snapshot_items[key]) for key in sorted(existing_keys)
    }
    expected_items.update(
        {key: copy.deepcopy(value) for key, value in new_judgments.items()}
    )
    for key, amendment in amendments.items():
        expected_items[key].update(amendment)
    try:
        _apply_semantic_model_content_amendments(expected_items, content_amendments)
        _apply_semantic_model_dimension_amendments(
            expected_items, dimension_amendments
        )
        _reproject_current_generated_association_credentials(
            raw_audit, expected_items, paper_dir=paper_dir
        )
    except SourceRecordCurrentRevalidationError as exc:
        errors.append(str(exc))
        return errors
    if _canonical_digest(_semantic_judgment_ledger(expected_items)) != _canonical_digest(
        _semantic_judgment_ledger(sidecar_items)
    ):
        errors.append(
            "rebound sidecar semantic response ledger no longer matches its "
            "archived snapshot plus attested amendments"
        )
    return errors


def validate_rebound_sidecar(
    raw_audit: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path | None = None,
    include_runtime_semantic_checks: bool = True,
) -> list[str]:
    """Return deterministic failures after a proposed current rebind.

    Issuance must retain ``include_runtime_semantic_checks=True``: those
    checks establish that a newly rebound candidate satisfies the shared
    current source-target disposition rules.  A later immutable-evidence
    replay may set it false after exact raw/sidecar/attestation bytes have
    already been pinned by another authenticated transport.  That replay
    still validates every receipt and attested semantic ledger, but does not
    launch a fresh identity-only source audit for each consumer load.
    """

    output_sidecar_path = output_sidecar_path or (
        paper_dir / "audit" / "source_record_match_llm.json"
    )
    errors: list[str] = []
    raw_error = _raw_audit_error(raw_audit, paper=paper, paper_dir=paper_dir)
    if raw_error:
        return [raw_error]
    try:
        sidecar_items = _sidecar_items(sidecar, paper=paper)
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    expected = set(generated_judgment_items(raw_audit))
    if set(sidecar_items) != expected:
        errors.append("rebound sidecar no longer has exact current generated-key coverage")
    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(sidecar.get("source_record_audit_sha256")) != current_digest:
        errors.append("rebound sidecar is not bound to the current aggregate raw receipt")
    if not formalization_protocol_receipt_matches(sidecar, scope="review"):
        errors.append("rebound sidecar has no current formalization review-protocol receipt")
    metadata = sidecar.get(CURRENT_REVALIDATION_FIELD)
    if not isinstance(metadata, Mapping):
        errors.append("rebound sidecar lacks current semantic revalidation metadata")
    else:
        if metadata.get("schema") != CURRENT_REVALIDATION_SCHEMA:
            errors.append("rebound sidecar has unsupported current revalidation schema")
        if metadata.get("policy_version") != CURRENT_REVALIDATION_POLICY_VERSION:
            errors.append("rebound sidecar has wrong current revalidation policy")
        if _sha256(metadata.get("current_source_record_audit_sha256")) != current_digest:
            errors.append("rebound sidecar metadata is not bound to the current raw receipt")
        if _sha256(metadata.get("generated_judgment_keys_sha256")) != (
            generated_judgment_keys_sha256(raw_audit)
        ):
            errors.append("rebound sidecar metadata has stale generated-key coverage")
        if _sha256(metadata.get("generated_judgment_surface_sha256")) != (
            generated_judgment_surface_sha256(raw_audit)
        ):
            errors.append("rebound sidecar metadata has stale generated-item surface")
        if str(metadata.get("current_judgment_sidecar_path") or "").strip() != _relative_path(
            output_sidecar_path, paper_dir
        ):
            errors.append("rebound sidecar metadata names a different output sidecar")
        errors.extend(
            _rebound_attestation_errors(
                metadata,
                raw_audit,
                paper=paper,
                paper_dir=paper_dir,
                output_sidecar_path=output_sidecar_path,
                sidecar_items=sidecar_items,
            )
        )
    current_groups = generated_judgment_items(raw_audit)
    for key, item in sidecar_items.items():
        if _sha256(item.get("source_record_audit_sha256")) != current_digest:
            errors.append(f"{key}: response is not bound to the current aggregate raw receipt")
        if key not in current_groups:
            # Exact coverage was already reported above. Keep validating the
            # remaining current entries without indexing an attacker-supplied
            # or stale extra key into the generated group ledger.
            continue
        expected_pin_records = _current_item_pins(current_groups[key])
        expected_pins = frozenset(
            (
                str(pin["kind"]),
                SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                str(pin["source_record_item_sha256"]),
            )
            for pin in expected_pin_records
        )
        actual_pins = REPOSITORY.source_record_judgment_item_digest_pins(item)
        if expected_pins:
            if actual_pins != expected_pins:
                errors.append(f"{key}: rebound response has stale or incomplete current item pins")
            scalar = str(item.get("source_record_item_sha256") or "").strip()
            expected_scalar = str(
                expected_pin_records[0]["source_record_item_sha256"]
            )
            if (
                item.get("source_record_item_digest_schema")
                != SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                or scalar != expected_scalar
            ):
                errors.append(f"{key}: rebound response has a stale scalar item receipt")
        elif actual_pins is not None or any(
            field.startswith("source_record_item_") for field in item
        ):
            if actual_pins:
                errors.append(
                    f"{key}: rebound response has a partial pin for a multi-member or aggregate-only group"
                )
            elif any(field.startswith("source_record_item_") for field in item):
                errors.append(
                    f"{key}: rebound response exposes an ineligible narrow item receipt"
                )
    if include_runtime_semantic_checks:
        current_judgments = EVIDENCE.current_source_record_judgment_items(
            dict(raw_audit),
            dict(sidecar),
            folder=paper_dir,
        )
        if set(current_judgments) != expected:
            missing = sorted(expected - set(current_judgments))
            errors.append(
                "shared v10 current-judgment loader rejected current rebind"
                + (f"; missing={missing[:5]}" if missing else "")
            )
        errors.extend(_target_disposition_errors(raw_audit, sidecar, paper_dir=paper_dir))
        errors.extend(_boundary_classification_errors(raw_audit, sidecar))
    return errors


def attestation_template(
    raw_audit: Mapping[str, Any],
    prior_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
    use_paper_local_semantic_contract_revalidation: bool = True,
) -> dict[str, Any]:
    """Return a non-evidence template a reviewer must explicitly complete."""

    prior_sidecar, prior_sidecar_sha256 = _loaded_snapshot_matches(
        prior_sidecar_path, prior_sidecar, label="prior sidecar"
    )
    raw_error_kwargs: dict[str, Any] = {}
    if not use_paper_local_semantic_contract_revalidation:
        raw_error_kwargs["use_paper_local_semantic_contract_revalidation"] = False
    raw_error = _raw_audit_error(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        **raw_error_kwargs,
    )
    if raw_error:
        raise SourceRecordCurrentRevalidationError(raw_error)
    items = _sidecar_items(prior_sidecar, paper=paper)
    prior_error = _prior_sidecar_error(prior_sidecar, items)
    if prior_error:
        raise SourceRecordCurrentRevalidationError(prior_error)
    generated_keys = set(generated_judgment_items(raw_audit))
    prior_keys = set(items)
    return {
        "schema": CURRENT_REVALIDATION_SCHEMA,
        "artifact_kind": CURRENT_REVALIDATION_ATTESTATION_KIND,
        "policy_version": CURRENT_REVALIDATION_POLICY_VERSION,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: formalization_review_protocol_digest(),
        "paper": paper,
        "prior_judgment_sidecar_path": _relative_path(prior_sidecar_path, paper_dir),
        "prior_judgment_sidecar_sha256": prior_sidecar_sha256,
        "prior_source_record_audit_sha256": _sha256(
            prior_sidecar.get("source_record_audit_sha256")
        ),
        "current_source_record_audit_sha256": _sha256(
            raw_audit.get("source_record_audit_sha256")
        ),
        "generated_judgment_keys_sha256": generated_judgment_keys_sha256(raw_audit),
        "generated_judgment_surface_sha256": generated_judgment_surface_sha256(raw_audit),
        "review_scope": "all_current_generated_judgment_keys",
        "new_judgment_keys_required": sorted(generated_keys - prior_keys),
        "retired_prior_judgment_keys": sorted(prior_keys - generated_keys),
        "new_judgments": {},
        "judgment_amendments": {},
        "semantic_model_dimension_amendments": {},
        "reviewed_current_semantics": False,
        "reviewer": "",
        "validated_at": "",
        "review_notes": (
            "Complete only after manually reviewing the current raw v10 surface, "
            "all existing judgments, and every changed source/Lean target."
        ),
        "non_evidence_scaffold": True,
    }


def _selected_current_group_descriptors(
    raw_audit: Mapping[str, Any],
) -> dict[str, str]:
    """Return current group receipts produced from semantic, not name, content.

    A sidecar key identifies where an already-audited response is stored.  It
    never establishes that two obligations are the same: that role belongs to
    the descriptor hash generated from the complete raw semantic group.
    """

    groups, errors = raw_source_record_obligation_groups(raw_audit)
    if errors:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has malformed differential group(s): "
            + ", ".join(sorted(errors)[:5])
        )
    descriptors: dict[str, str] = {}
    for key, group in groups.items():
        digest = _sha256(group.get("descriptor_sha256"))
        if not digest:
            raise SourceRecordCurrentRevalidationError(
                f"current raw audit group `{key}` lacks a semantic descriptor receipt"
            )
        descriptors[key] = digest
    if not descriptors:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has no semantic differential groups"
        )
    return descriptors


def _authenticated_overlay_union_module() -> Any:
    """Load the transport registry only after current revalidation initializes.

    Historical descriptor migration imports this module's raw-audit helpers,
    while semantic-rebind is reached through that migration loader.  Keeping
    the registry lazy makes the dependency graph explicit rather than letting
    Python import order decide which transport capability is available.
    """

    try:
        from scripts import source_record_authenticated_overlay_union as overlay_union
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_authenticated_overlay_union as overlay_union
    return overlay_union


@dataclass(frozen=True)
class _SelectedCurrentOverlay:
    """A descriptor-bound current overlay with its transport lane partition.

    ``__iter__`` preserves the historical four-value private helper contract
    for focused tests and legacy callers.  New v2 selected attestations use
    ``lane_descriptors`` to bind the complete authenticated union rather than
    calling a special loader for a particular artifact filename.
    """

    items: dict[str, Mapping[str, Any]]
    descriptors: dict[str, str]
    differential_overlay_path: Path | None
    differential_overlay_sha256: str
    lane_descriptors: dict[str, dict[str, str]]

    def __iter__(self):
        yield self.items
        yield self.descriptors
        yield self.differential_overlay_path
        yield self.differential_overlay_sha256


def _selected_current_revalidation_policy_configuration(
    policy_version: object,
) -> dict[str, object]:
    """Return the frozen overlay scope selected by a serialized attestation."""

    if policy_version == SELECTED_CURRENT_REVALIDATION_POLICY_VERSION:
        return {
            "policy_version": SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            "scope": SELECTED_CURRENT_REVALIDATION_SCOPE,
            "uses_authenticated_overlay_union": False,
            "requires_differential_overlay": True,
            "requires_explicit_current_replacements": False,
        }
    if policy_version == SELECTED_CURRENT_REVALIDATION_UNION_POLICY_VERSION:
        return {
            "policy_version": SELECTED_CURRENT_REVALIDATION_UNION_POLICY_VERSION,
            "scope": SELECTED_CURRENT_REVALIDATION_UNION_SCOPE,
            "uses_authenticated_overlay_union": True,
            "requires_differential_overlay": False,
            "requires_explicit_current_replacements": False,
        }
    if policy_version == SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION:
        return {
            "policy_version": (
                SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION
            ),
            "scope": SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_SCOPE,
            "uses_authenticated_overlay_union": True,
            "requires_differential_overlay": False,
            # A selected current review is the manual route for descriptor
            # change.  v3 cannot infer that an archived same-key response
            # remains sound; every surviving historical row must carry one
            # complete replacement bound to its prior response and current
            # generated descriptor.
            "requires_explicit_current_replacements": True,
        }
    raise SourceRecordCurrentRevalidationError(
        "selected attestation has an unsupported policy version"
    )


def _coerce_selected_current_overlay(value: object) -> _SelectedCurrentOverlay:
    """Accept the legacy private helper tuple while preserving its v1 meaning."""

    if isinstance(value, _SelectedCurrentOverlay):
        return value
    try:
        items, descriptors, path, sha256 = value  # type: ignore[misc]
    except (TypeError, ValueError) as exc:
        raise SourceRecordCurrentRevalidationError(
            "selected current overlay helper returned an invalid result"
        ) from exc
    if (
        not isinstance(items, Mapping)
        or not isinstance(descriptors, Mapping)
        or not isinstance(path, Path)
    ):
        raise SourceRecordCurrentRevalidationError(
            "selected current overlay helper returned malformed legacy provenance"
        )
    normalized_items = {
        str(key): value
        for key, value in items.items()
        if str(key).strip() and isinstance(value, Mapping)
    }
    normalized_descriptors = {
        str(key): _sha256(digest)
        for key, digest in descriptors.items()
        if str(key).strip() and _sha256(digest)
    }
    if set(normalized_items) != set(items) or set(normalized_descriptors) != set(
        descriptors
    ):
        raise SourceRecordCurrentRevalidationError(
            "selected current overlay helper returned malformed legacy entries"
        )
    return _SelectedCurrentOverlay(
        items=normalized_items,
        descriptors=normalized_descriptors,
        differential_overlay_path=path,
        differential_overlay_sha256=_sha256(sha256),
        lane_descriptors={"differential": normalized_descriptors},
    )


def _selected_current_overlay_details(*args: Any, **kwargs: Any) -> _SelectedCurrentOverlay:
    return _coerce_selected_current_overlay(_selected_current_overlay(*args, **kwargs))


def _selected_authenticated_overlay_union_payload(
    overlay: _SelectedCurrentOverlay,
) -> dict[str, Any]:
    """Serialize only descriptor receipts for a union already loader-checked.

    The individual loaders retain and replay their own byte/source provenance.
    This selected-review receipt binds the complete *current* partition, so a
    lane may not silently add, remove, or replace an omitted manual group.
    """

    lanes = {
        str(label): dict(descriptors)
        for label, descriptors in sorted(overlay.lane_descriptors.items())
    }
    return {
        "schema": SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_SCHEMA,
        "policy_version": SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_POLICY_VERSION,
        "lane_current_group_descriptors": lanes,
        "lane_current_group_descriptors_sha256": _canonical_digest(lanes),
        "current_group_descriptors": dict(overlay.descriptors),
        "current_group_descriptors_sha256": _canonical_digest(overlay.descriptors),
    }


def _selected_authenticated_overlay_union_error(
    payload: object,
    *,
    overlay: _SelectedCurrentOverlay,
) -> str:
    """Check the persisted v2 union against freshly authenticated lane output."""

    if not isinstance(payload, Mapping):
        return "selected attestation has no authenticated-overlay union ledger"
    if payload.get("schema") != SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_SCHEMA:
        return "selected attestation authenticated-overlay union has unsupported schema"
    if (
        payload.get("policy_version")
        != SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_POLICY_VERSION
    ):
        return "selected attestation authenticated-overlay union has wrong policy version"
    raw_lanes = payload.get("lane_current_group_descriptors")
    if not isinstance(raw_lanes, Mapping):
        return "selected attestation authenticated-overlay union has no lane ledger"
    try:
        recorded_lanes = {
            str(label): _descriptor_ledger(descriptors, field=f"authenticated overlay lane `{label}`")
            for label, descriptors in raw_lanes.items()
            if str(label).strip()
        }
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    if len(recorded_lanes) != len(raw_lanes) or set(recorded_lanes) != set(
        overlay.lane_descriptors
    ):
        return "selected attestation authenticated-overlay union has stale lane coverage"
    if recorded_lanes != overlay.lane_descriptors:
        return "selected attestation authenticated-overlay union lane ledger is stale"
    if _sha256(payload.get("lane_current_group_descriptors_sha256")) != _canonical_digest(
        recorded_lanes
    ):
        return "selected attestation authenticated-overlay union lane-ledger digest is stale"
    try:
        recorded_union = _descriptor_ledger(
            payload.get("current_group_descriptors"),
            field="authenticated_current_overlay_union.current_group_descriptors",
        )
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    if recorded_union != overlay.descriptors:
        return "selected attestation authenticated-overlay union descriptor ledger is stale"
    if _sha256(payload.get("current_group_descriptors_sha256")) != _canonical_digest(
        recorded_union
    ):
        return "selected attestation authenticated-overlay union descriptor-ledger digest is stale"
    return ""


def _descriptor_ledger(value: object, *, field: str) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise SourceRecordCurrentRevalidationError(
            f"attestation `{field}` must be an object-valued descriptor ledger"
        )
    ledger: dict[str, str] = {}
    for raw_key, raw_digest in value.items():
        key = str(raw_key or "").strip()
        digest = _sha256(raw_digest)
        if not key or not digest or key in ledger:
            raise SourceRecordCurrentRevalidationError(
                f"attestation `{field}` has an empty, duplicate, or malformed receipt"
            )
        ledger[key] = digest
    return ledger


def _selected_current_overlay(
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    overlay_path: Path | None = None,
    overlay_provenance_path: Path | None = None,
    raw_audit_path: Path | None = None,
    raw_audit_provenance_path: Path | None = None,
    use_authenticated_overlay_union: bool = True,
    require_differential_overlay: bool = False,
) -> _SelectedCurrentOverlay:
    """Load the exact authenticated complement for a selected revalidation.

    Optional archive paths make an earlier selected-review receipt auditable
    in place.  They are byte-authentication inputs only; the complement is
    still derived from the raw semantic-descriptor ledger.  The v2 path asks
    a registry of loader-owned transports for the complete current union;
    schema-2 semantic rebind is a distinct stronger lane whose live identity
    context exists only inside that one registry invocation.  Neither an
    artifact name nor a response key is used as a match.
    """

    resolved_overlay_path = (
        overlay_path
        or paper_dir
        / "audit"
        / SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME
    )
    logical_overlay_path = overlay_provenance_path or resolved_overlay_path
    if (require_differential_overlay or overlay_path is not None) and not resolved_overlay_path.is_file():
        raise SourceRecordCurrentRevalidationError(
            "selected current revalidation requires a differential overlay artifact"
        )
    all_descriptors = _selected_current_group_descriptors(raw_audit)
    try:
        overlay_union = _authenticated_overlay_union_module()
        lane_labels = None if use_authenticated_overlay_union else ("differential",)
        lanes = overlay_union.load_authenticated_current_overlay_lanes(
            paper_dir,
            paper,
            raw_audit,
            lane_labels=lane_labels,
            differential_overlay_path=(
                resolved_overlay_path if resolved_overlay_path.is_file() else None
            ),
            differential_current_raw_audit_path=raw_audit_path,
            differential_current_raw_audit_provenance_path=(
                raw_audit_provenance_path
            ),
        )
        loaded = overlay_union.strict_authenticated_current_overlay_union(lanes)
    except Exception as exc:  # noqa: BLE001 - selected omission must fail closed.
        raise SourceRecordCurrentRevalidationError(
            "could not replay the authenticated current-overlay union: " + str(exc)
        ) from exc
    if require_differential_overlay and not loaded:
        raise SourceRecordCurrentRevalidationError(
            "selected current revalidation has no authenticated differential overlay items"
        )
    try:
        overlay_descriptors = {key: all_descriptors[key] for key in loaded}
        lane_descriptors = {
            lane.label: {key: all_descriptors[key] for key in lane.items}
            for lane in lanes
        }
    except KeyError as exc:  # defensive: loaders must only expose raw groups.
        raise SourceRecordCurrentRevalidationError(
            "authenticated current-overlay union names a missing current semantic group"
        ) from exc
    differential_sha256 = (
        _file_sha256(resolved_overlay_path) if resolved_overlay_path.is_file() else ""
    )
    return _SelectedCurrentOverlay(
        items=dict(loaded),
        descriptors=overlay_descriptors,
        differential_overlay_path=(
            logical_overlay_path if resolved_overlay_path.is_file() else None
        ),
        differential_overlay_sha256=differential_sha256,
        lane_descriptors=lane_descriptors,
    )


def _attested_new_judgments(
    attestation: Mapping[str, Any], *, required_keys: set[str]
) -> dict[str, dict[str, Any]]:
    raw = attestation.get("new_judgments", {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation new_judgments must be an object"
        )
    out: dict[str, dict[str, Any]] = {}
    for raw_key, raw_value in raw.items():
        key = str(raw_key or "").strip()
        if not key or key not in required_keys or not isinstance(raw_value, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "attestation new_judgments has a missing, unexpected, or malformed entry"
            )
        value = {str(field): copy.deepcopy(content) for field, content in raw_value.items()}
        if not str(value.get("classification") or "").strip():
            raise SourceRecordCurrentRevalidationError(
                f"attestation new judgment `{key}` has no classification"
            )
        forbidden = [
            field
            for field in value
            if field.startswith("source_record_")
            or field in {
                PRIOR_ITEM_RECEIPT_FIELD,
                SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
            }
        ]
        if forbidden:
            raise SourceRecordCurrentRevalidationError(
                f"attestation new judgment `{key}` supplies generated freshness transport"
            )
        out[key] = value
    if set(out) != required_keys:
        missing = sorted(required_keys - set(out))
        extra = sorted(set(out) - required_keys)
        raise SourceRecordCurrentRevalidationError(
            "attestation new_judgments does not exactly cover current groups absent "
            "from the archived sidecar"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    return out


def _complete_new_judgments(
    attestation: Mapping[str, Any], *, required_keys: set[str]
) -> dict[str, dict[str, Any]]:
    """Materialize new full-review responses with reviewer metadata generated.

    Selected-review artifacts historically allowed reviewer metadata inside a
    new response, so their parser remains backward compatible.  A complete
    current review has one authenticated reviewer and timestamp for the whole
    ledger; new responses may not override that transport independently.
    """

    out = _attested_new_judgments(attestation, required_keys=required_keys)
    forbidden = {"prompt_version", "validator", "validated_at"}
    for key, value in out.items():
        supplied = sorted(forbidden & set(value))
        if supplied:
            raise SourceRecordCurrentRevalidationError(
                f"attestation new judgment `{key}` supplies reviewer transport: "
                + ", ".join(supplied)
            )
        value["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
        value["validator"] = str(attestation.get("reviewer") or "").strip()
        value["validated_at"] = str(attestation.get("validated_at") or "").strip()
    return out


def _selected_response_semantic_payload(value: Mapping[str, Any]) -> dict[str, Any]:
    """Return one response without generated selected-rebind transport."""

    return {
        str(field): copy.deepcopy(content)
        for field, content in value.items()
        if not str(field).startswith("source_record_")
        and str(field)
        not in {
            PRIOR_ITEM_RECEIPT_FIELD,
            SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
        }
    }


def _selected_response_semantic_sha256(value: Mapping[str, Any]) -> str:
    """Digest the exact archived response content that a replacement supersedes."""

    return _canonical_digest(_selected_response_semantic_payload(value))


def _manual_replacement_transport_error(value: object, *, path: str = "response") -> str:
    """Reject freshness and source-association credentials from a manual replacement.

    A replacement is a new semantic judgment.  Its current receipt and source
    association pins must come from the exact current raw group below, rather
    than being copied from a prior sidecar or supplied by a reviewer.
    """

    if isinstance(value, Mapping):
        for raw_field, child in value.items():
            field = str(raw_field)
            child_path = f"{path}.{field}" if field else path
            if field.startswith("source_record_") or field in {
                PRIOR_ITEM_RECEIPT_FIELD,
                SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
            }:
                return f"{child_path} supplies generated revalidation transport"
            if field in {
                "semantic_association_sha256",
                "corrected_target_sha256_by_source_item",
                "corrected_target_sha256_by_source_semantic_sha256",
            }:
                return f"{child_path} supplies a generated source-association credential"
            if error := _manual_replacement_transport_error(child, path=child_path):
                return error
    elif isinstance(value, list):
        for index, child in enumerate(value):
            if error := _manual_replacement_transport_error(
                child, path=f"{path}[{index}]"
            ):
                return error
    return ""


def _attested_selected_judgment_replacements(
    attestation: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
    *,
    expected_keys: set[str],
    current_raw_audit: Mapping[str, Any],
    selected_descriptors: Mapping[str, str],
) -> dict[str, dict[str, Any]]:
    """Read full current responses that intentionally replace archived judgments.

    Judgment keys are only current-ledger addresses.  Each replacement is
    bound both to the immutable archived response it supersedes and to the
    exact current semantic descriptor at that address, so it cannot transport
    a decision across equal-looking binders, declarations, or record fields.
    """

    raw = attestation.get(ATTESTED_JUDGMENT_REPLACEMENTS_FIELD, {})
    if raw is None:
        raw = {}
    if not isinstance(raw, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation judgment_replacements must be an object"
        )
    if not raw:
        return {}

    groups, group_errors = raw_source_record_obligation_groups(current_raw_audit)
    if group_errors:
        raise SourceRecordCurrentRevalidationError(
            "current raw audit has malformed groups for judgment replacements"
        )

    replacements: dict[str, dict[str, Any]] = {}
    for raw_key, raw_entry in raw.items():
        key = str(raw_key or "").strip()
        prior = prior_items.get(key)
        if not key or key not in expected_keys or not isinstance(prior, Mapping):
            raise SourceRecordCurrentRevalidationError(
                "judgment replacement names a missing or non-prior selected response"
            )
        if not isinstance(raw_entry, Mapping) or set(raw_entry) != (
            SELECTED_JUDGMENT_REPLACEMENT_FIELDS
        ):
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` has unsupported fields"
            )
        if raw_entry.get("schema") != SELECTED_JUDGMENT_REPLACEMENT_SCHEMA:
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` has an unsupported schema"
            )
        descriptor = _sha256(raw_entry.get("current_group_semantic_descriptor_sha256"))
        expected_descriptor = _sha256(selected_descriptors.get(key))
        group = groups.get(key)
        group_descriptor = (
            _sha256(group.get("descriptor_sha256"))
            if isinstance(group, Mapping)
            else ""
        )
        if not descriptor or descriptor != expected_descriptor or descriptor != group_descriptor:
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` is not bound to its exact current semantic group"
            )
        prior_digest = _sha256(raw_entry.get("prior_response_semantic_sha256"))
        if prior_digest != _selected_response_semantic_sha256(prior):
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` does not match the archived response it replaces"
            )
        if not str(raw_entry.get("replacement_rationale") or "").strip():
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` lacks a replacement rationale"
            )
        response = raw_entry.get("response")
        if not isinstance(response, Mapping):
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` has no object-valued response"
            )
        value = {str(field): copy.deepcopy(content) for field, content in response.items()}
        if not str(value.get("classification") or "").strip():
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` has no classification"
            )
        if error := _manual_replacement_transport_error(value):
            raise SourceRecordCurrentRevalidationError(
                f"judgment replacement `{key}` {error}"
            )
        replacements[key] = value
    return replacements


def _attested_required_judgment_replacement_keys(
    attestation: Mapping[str, Any], *, expected_keys: set[str]
) -> set[str]:
    """Read the v3 replacement partition without silently normalizing it.

    The list is redundant with the replacement objects below, on purpose: it
    lets a non-evidence template state the exact work partition before a
    reviewer writes any response.  It is never authorization by itself.  The
    replacement parser still byte-binds each historical response and current
    semantic descriptor.
    """

    raw = attestation.get(ATTESTED_JUDGMENT_REPLACEMENT_KEYS_FIELD)
    if not isinstance(raw, list):
        raise SourceRecordCurrentRevalidationError(
            "selected attestation v3 has no replacement-key work partition"
        )
    keys: set[str] = set()
    for raw_key in raw:
        if not isinstance(raw_key, str):
            raise SourceRecordCurrentRevalidationError(
                "selected attestation v3 replacement-key work partition has a non-string key"
            )
        key = raw_key.strip()
        if not key or key in keys:
            raise SourceRecordCurrentRevalidationError(
                "selected attestation v3 replacement-key work partition has an empty or duplicate key"
            )
        keys.add(key)
    if keys != expected_keys:
        missing = sorted(expected_keys - keys)
        extra = sorted(keys - expected_keys)
        raise SourceRecordCurrentRevalidationError(
            "selected attestation v3 replacement-key work partition is stale"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    return keys


def _selected_replacement_overlap_error(
    replacements: Mapping[str, Mapping[str, Any]],
    *,
    judgment_amendments: Mapping[str, Mapping[str, Any]],
    dimension_amendments: Mapping[str, Mapping[str, Mapping[str, str]]],
    association_amendments: Mapping[str, Mapping[str, str]],
) -> str:
    """Reject ambiguous merge-plus-replace semantics for one current response."""

    overlaps = sorted(
        set(replacements)
        & (
            set(judgment_amendments)
            | set(dimension_amendments)
            | set(association_amendments)
        )
    )
    if overlaps:
        return (
            "judgment replacement cannot accompany another amendment for the same "
            "current semantic group: "
            + ", ".join(overlaps[:5])
        )
    return ""


def _selected_current_attestation_error(
    attestation: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
    prior_sidecar_sha256: str,
    raw_audit: Mapping[str, Any],
    prior_items: Mapping[str, Mapping[str, Any]],
    overlay_descriptors: Mapping[str, str],
    overlay_path: Path | None,
    overlay_sha256: str,
    overlay: _SelectedCurrentOverlay | None = None,
) -> str:
    if attestation.get("schema") != SELECTED_CURRENT_REVALIDATION_SCHEMA:
        return "selected attestation has an unsupported schema"
    if attestation.get("artifact_kind") != SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND:
        return "selected attestation has the wrong artifact_kind"
    if attestation.get("paper") != paper:
        return "selected attestation paper does not match the requested paper"
    try:
        policy = _selected_current_revalidation_policy_configuration(
            attestation.get("policy_version")
        )
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    if not formalization_protocol_receipt_matches(attestation, scope="review"):
        return "selected attestation has no current formalization review-protocol receipt"
    if any(
        bool(attestation.get(marker))
        for marker in (
            "non_evidence_scaffold",
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
        )
    ):
        return "selected attestation is marked as a non-evidence scaffold"
    if attestation.get("reviewed_current_semantics") is not True:
        return "selected attestation must explicitly affirm current semantic review"
    if str(attestation.get("review_scope") or "").strip() != policy["scope"]:
        return "selected attestation has the wrong review scope"
    if not str(attestation.get("reviewer") or "").strip() or not str(
        attestation.get("validated_at") or ""
    ).strip():
        return "selected attestation lacks reviewer or validated_at metadata"
    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(attestation.get("current_source_record_audit_sha256")) != current_digest:
        return "selected attestation is not bound to the current raw aggregate receipt"
    if _sha256(attestation.get("generated_judgment_keys_sha256")) != (
        generated_judgment_keys_sha256(raw_audit)
    ):
        return "selected attestation has stale generated-key coverage"
    if _sha256(attestation.get("generated_judgment_surface_sha256")) != (
        generated_judgment_surface_sha256(raw_audit)
    ):
        return "selected attestation has stale generated-item surface"
    if str(attestation.get("prior_judgment_sidecar_path") or "").strip() != _relative_path(
        prior_sidecar_path, paper_dir
    ):
        return "selected attestation names a different prior-sidecar snapshot"
    if _sha256(attestation.get("prior_judgment_sidecar_sha256")) != prior_sidecar_sha256:
        return "selected attestation is not bound to the exact prior-sidecar bytes"
    try:
        actual_all = _selected_current_group_descriptors(raw_audit)
        recorded_selected = _descriptor_ledger(
            attestation.get("selected_current_group_descriptors"),
            field="selected_current_group_descriptors",
        )
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    if bool(policy["uses_authenticated_overlay_union"]):
        if overlay is None:
            return "selected attestation has no authenticated current-overlay union"
        if union_error := _selected_authenticated_overlay_union_error(
            attestation.get(SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD),
            overlay=overlay,
        ):
            return union_error
        recorded_overlay = dict(overlay.descriptors)
    else:
        if overlay_path is None:
            return "selected attestation has no authenticated differential overlay"
        if str(attestation.get("differential_overlay_path") or "").strip() != _relative_path(
            overlay_path, paper_dir
        ):
            return "selected attestation names a different differential overlay"
        if _sha256(attestation.get("differential_overlay_sha256")) != overlay_sha256:
            return "selected attestation is not bound to the exact differential overlay bytes"
        try:
            recorded_overlay = _descriptor_ledger(
                attestation.get("differential_overlay_current_group_descriptors"),
                field="differential_overlay_current_group_descriptors",
            )
        except SourceRecordCurrentRevalidationError as exc:
            return str(exc)
        if recorded_overlay != dict(overlay_descriptors):
            return "selected attestation overlay descriptor ledger is not the authenticated current complement"
    expected_selected = {
        key: digest for key, digest in actual_all.items() if key not in overlay_descriptors
    }
    if recorded_selected != expected_selected:
        return "selected attestation does not cover exactly every current group outside the authenticated overlay"
    if _sha256(attestation.get("selected_current_group_descriptors_sha256")) != _canonical_digest(
        recorded_selected
    ):
        return "selected attestation has a stale selected-group descriptor ledger digest"
    if not bool(policy["uses_authenticated_overlay_union"]):
        if _sha256(attestation.get("differential_overlay_current_group_descriptors_sha256")) != _canonical_digest(
            recorded_overlay
        ):
            return "selected attestation has a stale overlay-group descriptor ledger digest"
    missing_prior = set(recorded_selected) - set(prior_items)
    existing_prior = set(recorded_selected) & set(prior_items)
    try:
        _attested_new_judgments(attestation, required_keys=missing_prior)
        replacements = _attested_selected_judgment_replacements(
            attestation,
            prior_items,
            expected_keys=existing_prior,
            current_raw_audit=raw_audit,
            selected_descriptors=recorded_selected,
        )
        judgment_amendments = _attested_judgment_amendments(
            attestation, expected_keys=set(recorded_selected) & set(prior_items)
        )
        if amendment_provenance_error := _attested_judgment_amendment_provenance_error(
            judgment_amendments, paper_dir=paper_dir
        ):
            return amendment_provenance_error
        dimension_amendments = _attested_semantic_model_dimension_amendments(
            attestation,
            prior_items,
            expected_keys=set(recorded_selected) & set(prior_items),
        )
        association_amendments = _attested_semantic_model_dimension_association_amendments(
            attestation,
            prior_items,
            expected_keys=set(recorded_selected) & set(prior_items),
            current_raw_audit=raw_audit,
            selected_descriptors=recorded_selected,
            judgment_amendments=judgment_amendments,
        )
    except SourceRecordCurrentRevalidationError as exc:
        return str(exc)
    if bool(policy["requires_explicit_current_replacements"]):
        try:
            _attested_required_judgment_replacement_keys(
                attestation, expected_keys=existing_prior
            )
        except SourceRecordCurrentRevalidationError as exc:
            return str(exc)
        if set(replacements) != existing_prior:
            missing = sorted(existing_prior - set(replacements))
            extra = sorted(set(replacements) - existing_prior)
            return (
                "selected attestation v3 lacks a complete explicit current replacement "
                "for every prior selected response"
                + (f"; missing={missing[:5]}" if missing else "")
                + (f"; extra={extra[:5]}" if extra else "")
            )
    if replacement_error := _selected_replacement_overlap_error(
        replacements,
        judgment_amendments=judgment_amendments,
        dimension_amendments=dimension_amendments,
        association_amendments=association_amendments,
    ):
        return replacement_error
    required_new_keys = {
        str(key).strip()
        for key in attestation.get("new_judgment_keys_required", [])
        if str(key).strip()
    }
    if required_new_keys != missing_prior:
        return "selected attestation has stale new-judgment key coverage"
    return ""


def selected_attestation_template(
    raw_audit: Mapping[str, Any],
    prior_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
) -> dict[str, Any]:
    """Create a non-evidence template for only the overlay complement.

    The selected ledger is computed from generated semantic descriptors.  It
    cannot be narrowed by declaration, binder, record, or storage-key naming.
    """

    prior_sidecar, prior_sidecar_sha256 = _loaded_snapshot_matches(
        prior_sidecar_path, prior_sidecar, label="prior sidecar"
    )
    raw_error = _raw_audit_error(raw_audit, paper=paper, paper_dir=paper_dir)
    if raw_error:
        raise SourceRecordCurrentRevalidationError(raw_error)
    prior_items = _sidecar_items(prior_sidecar, paper=paper)
    overlay = _selected_current_overlay_details(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        use_authenticated_overlay_union=True,
    )
    overlay_descriptors = overlay.descriptors
    all_descriptors = _selected_current_group_descriptors(raw_audit)
    selected = {
        key: digest for key, digest in all_descriptors.items() if key not in overlay_descriptors
    }
    return {
        "schema": SELECTED_CURRENT_REVALIDATION_SCHEMA,
        "artifact_kind": SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND,
        "policy_version": (
            SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_POLICY_VERSION
        ),
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: formalization_review_protocol_digest(),
        "paper": paper,
        "prior_judgment_sidecar_path": _relative_path(prior_sidecar_path, paper_dir),
        "prior_judgment_sidecar_sha256": prior_sidecar_sha256,
        "current_source_record_audit_sha256": _sha256(
            raw_audit.get("source_record_audit_sha256")
        ),
        "generated_judgment_keys_sha256": generated_judgment_keys_sha256(raw_audit),
        "generated_judgment_surface_sha256": generated_judgment_surface_sha256(raw_audit),
        SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD: (
            _selected_authenticated_overlay_union_payload(overlay)
        ),
        "selected_current_group_descriptors": selected,
        "selected_current_group_descriptors_sha256": _canonical_digest(selected),
        "new_judgment_keys_required": sorted(set(selected) - set(prior_items)),
        ATTESTED_JUDGMENT_REPLACEMENT_KEYS_FIELD: sorted(
            set(selected) & set(prior_items)
        ),
        "new_judgments": {},
        "judgment_amendments": {},
        "judgment_replacements": {},
        "semantic_model_dimension_amendments": {},
        "semantic_model_dimension_association_amendments": {},
        "review_scope": SELECTED_CURRENT_REVALIDATION_EXPLICIT_REPLACEMENT_SCOPE,
        "reviewed_current_semantics": False,
        "reviewer": "",
        "validated_at": "",
        "review_notes": (
            "Complete only after reviewing every current semantic group outside the "
            "authenticated current-overlay union. New groups need complete explicit "
            "responses, and every listed historical selected response needs a full "
            "current replacement bound to its old response hash and current descriptor; "
            "do not infer either from a name or declaration spelling."
        ),
        "non_evidence_scaffold": True,
    }


def _selected_semantic_judgment_ledger(
    items: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Drop generated transport before comparing a selected reviewed response."""

    return {
        str(raw_key): {
            field: copy.deepcopy(value)
            for field, value in raw_value.items()
            if not field.startswith("source_record_")
            and field
            not in {
                PRIOR_ITEM_RECEIPT_FIELD,
                SELECTED_CURRENT_REVALIDATION_ITEM_FIELD,
                "prompt_version",
                "validator",
                "validated_at",
            }
        }
        for raw_key, raw_value in items.items()
    }


def _selected_expected_semantic_items(
    prior_items: Mapping[str, Mapping[str, Any]],
    attestation: Mapping[str, Any],
    *,
    selected_keys: set[str],
    current_raw_audit: Mapping[str, Any] | None = None,
    selected_descriptors: Mapping[str, str] | None = None,
    paper_dir: Path | None = None,
    require_explicit_current_replacements: bool = False,
) -> dict[str, dict[str, Any]]:
    """Materialize the selected complement under its serialized policy.

    Legacy v1/v2 attestations retain their frozen historical transport: an
    explicitly reviewed same-key prior response can remain the semantic body.
    v3 deliberately has no such fallback.  Its existing selected keys are
    indexed only so the exact old response can be hash-bound to a complete
    current replacement.
    """

    existing_keys = selected_keys & set(prior_items)
    new_keys = selected_keys - set(prior_items)
    raw_replacements = attestation.get(ATTESTED_JUDGMENT_REPLACEMENTS_FIELD, {})
    if raw_replacements is None:
        raw_replacements = {}
    if not isinstance(raw_replacements, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "attestation judgment_replacements must be an object"
        )
    if raw_replacements and (
        current_raw_audit is None or selected_descriptors is None or paper_dir is None
    ):
        raise SourceRecordCurrentRevalidationError(
            "judgment replacements require the exact current raw descriptor ledger and paper context"
        )
    replacements = (
        _attested_selected_judgment_replacements(
            attestation,
            prior_items,
            expected_keys=existing_keys,
            current_raw_audit=current_raw_audit,
            selected_descriptors=selected_descriptors,
        )
        if raw_replacements
        else {}
    )
    amendments = _attested_judgment_amendments(
        attestation, expected_keys=existing_keys
    )
    dimension_amendments = _attested_semantic_model_dimension_amendments(
        attestation, prior_items, expected_keys=existing_keys
    )
    association_amendments = (
        _attested_semantic_model_dimension_association_amendments(
            attestation,
            prior_items,
            expected_keys=existing_keys,
            current_raw_audit=current_raw_audit,
            selected_descriptors=selected_descriptors,
            judgment_amendments=amendments,
        )
    )
    new_judgments = _attested_new_judgments(attestation, required_keys=new_keys)
    if require_explicit_current_replacements and set(replacements) != existing_keys:
        missing = sorted(existing_keys - set(replacements))
        extra = sorted(set(replacements) - existing_keys)
        raise SourceRecordCurrentRevalidationError(
            "selected attestation v3 lacks a complete explicit current replacement "
            "for every prior selected response"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    if replacement_error := _selected_replacement_overlap_error(
        replacements,
        judgment_amendments=amendments,
        dimension_amendments=dimension_amendments,
        association_amendments=association_amendments,
    ):
        raise SourceRecordCurrentRevalidationError(replacement_error)
    out: dict[str, dict[str, Any]] = {}
    for key in sorted(selected_keys):
        if key in existing_keys:
            if require_explicit_current_replacements:
                # v3 deliberately has no `prior_items[key]` fallback.  The
                # preceding exact-coverage check ensures this lookup is safe.
                value = copy.deepcopy(replacements[key])
            else:
                value = copy.deepcopy(replacements.get(key, prior_items[key]))
        else:
            value = copy.deepcopy(new_judgments[key])
        value.update(amendments.get(key, {}))
        out[key] = value
    _apply_semantic_model_dimension_amendments(out, dimension_amendments)
    for key in sorted(selected_keys):
        value = out[key]
        dimensions = value.get("semantic_model_dimensions")
        for dimension, association_pin in association_amendments.get(key, {}).items():
            assert isinstance(dimensions, dict)  # checked by amendment parser.
            dimension_response = dimensions.get(dimension)
            assert isinstance(dimension_response, dict)
            dimension_response["semantic_association_sha256"] = association_pin
    if replacements:
        assert current_raw_audit is not None and paper_dir is not None
        replacement_items = {key: out[key] for key in replacements}
        _reproject_current_generated_association_credentials(
            current_raw_audit,
            replacement_items,
            paper_dir=paper_dir,
            reject_existing=True,
        )
        out.update(replacement_items)
    return out


def selected_rebound_sidecar(
    raw_audit: Mapping[str, Any],
    prior_sidecar: Mapping[str, Any],
    attestation: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    prior_sidecar_path: Path,
    attestation_path: Path,
    output_sidecar_path: Path,
) -> dict[str, Any]:
    """Rebind only the current semantic groups absent from an authenticated overlay.

    This is intentionally a manual semantic attestation, not a descriptor-reuse
    mechanism. The overlay has already established its own exact descriptor
    equality. Every complement group is bound to the current receipt only after
    the attestation proves it is exactly the current descriptor complement.
    """

    if prior_sidecar_path.resolve() == output_sidecar_path.resolve():
        raise SourceRecordCurrentRevalidationError(
            "prior sidecar must be an immutable snapshot distinct from the output sidecar"
        )
    saved_attestation, saved_attestation_sha256 = _read_json_object_with_sha256(
        attestation_path
    )
    if _canonical_digest(saved_attestation) != _canonical_digest(attestation):
        raise SourceRecordCurrentRevalidationError(
            "in-memory selected attestation does not match the attestation file bytes"
        )
    prior_sidecar, prior_sidecar_sha256 = _loaded_snapshot_matches(
        prior_sidecar_path, prior_sidecar, label="prior sidecar"
    )
    raw_error = _raw_audit_error(raw_audit, paper=paper, paper_dir=paper_dir)
    if raw_error:
        raise SourceRecordCurrentRevalidationError(raw_error)
    prior_items = _sidecar_items(prior_sidecar, paper=paper)
    policy = _selected_current_revalidation_policy_configuration(
        saved_attestation.get("policy_version")
    )
    overlay = _selected_current_overlay_details(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        use_authenticated_overlay_union=bool(
            policy["uses_authenticated_overlay_union"]
        ),
        require_differential_overlay=bool(policy["requires_differential_overlay"]),
    )
    overlay_descriptors = overlay.descriptors
    attestation_error = _selected_current_attestation_error(
        saved_attestation,
        paper=paper,
        paper_dir=paper_dir,
        prior_sidecar_path=prior_sidecar_path,
        prior_sidecar_sha256=prior_sidecar_sha256,
        raw_audit=raw_audit,
        prior_items=prior_items,
        overlay_descriptors=overlay_descriptors,
        overlay_path=overlay.differential_overlay_path,
        overlay_sha256=overlay.differential_overlay_sha256,
        overlay=overlay,
    )
    if attestation_error:
        raise SourceRecordCurrentRevalidationError(attestation_error)

    selected_descriptors = _descriptor_ledger(
        saved_attestation.get("selected_current_group_descriptors"),
        field="selected_current_group_descriptors",
    )
    selected_keys = set(selected_descriptors)
    expected_semantic_items = _selected_expected_semantic_items(
        prior_items,
        saved_attestation,
        selected_keys=selected_keys,
        current_raw_audit=raw_audit,
        selected_descriptors=selected_descriptors,
        paper_dir=paper_dir,
        require_explicit_current_replacements=bool(
            policy["requires_explicit_current_replacements"]
        ),
    )
    current_groups = generated_judgment_items(raw_audit)
    current_audit_sha256 = _sha256(raw_audit.get("source_record_audit_sha256"))
    reviewer = str(saved_attestation.get("reviewer") or "").strip()
    validated_at = str(saved_attestation.get("validated_at") or "").strip()
    result_items: dict[str, dict[str, Any]] = {}
    for key in sorted(selected_keys):
        value = copy.deepcopy(expected_semantic_items[key])
        historical_receipt = _historical_item_receipt(value)
        if historical_receipt:
            value[PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        value["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
        value["validator"] = reviewer
        value["validated_at"] = validated_at
        value["source_record_audit_sha256"] = current_audit_sha256
        current_pins = _current_item_pins(current_groups[key])
        if current_pins:
            value["source_record_item_digest_schema"] = SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            value["source_record_item_sha256s"] = current_pins
            value["source_record_item_sha256"] = current_pins[0][
                "source_record_item_sha256"
            ]
        value[SELECTED_CURRENT_REVALIDATION_ITEM_FIELD] = {
            "schema": SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "attestation_sha256": saved_attestation_sha256,
            "current_group_semantic_descriptor_sha256": selected_descriptors[key],
        }
        result_items[key] = value

    _reproject_current_generated_association_credentials(
        raw_audit, result_items, paper_dir=paper_dir
    )

    result = copy.deepcopy(dict(prior_sidecar))
    result["paper"] = paper
    result["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
    result["validator"] = reviewer
    result["validated_at"] = validated_at
    result["source_record_audit_sha256"] = current_audit_sha256
    result[FORMALIZATION_REVIEW_PROTOCOL_FIELD] = str(
        saved_attestation.get(FORMALIZATION_REVIEW_PROTOCOL_FIELD) or ""
    ).strip().lower()
    result["items"] = result_items
    result.pop(CURRENT_REVALIDATION_FIELD, None)
    # This rebind owns the selected complement through the descriptor and
    # overlay ledgers below.  An inherited manual-complement marker refers to
    # the prior sidecar/raw receipt and would be stale, conflicting provenance.
    result.pop("manual_current_complement", None)
    metadata: dict[str, Any] = {
        "schema": SELECTED_CURRENT_REVALIDATION_SCHEMA,
        "policy_version": str(policy["policy_version"]),
        "attestation_path": _relative_path(attestation_path, paper_dir),
        "attestation_sha256": saved_attestation_sha256,
        "prior_judgment_sidecar_path": _relative_path(prior_sidecar_path, paper_dir),
        "prior_judgment_sidecar_sha256": prior_sidecar_sha256,
        "current_judgment_sidecar_path": _relative_path(output_sidecar_path, paper_dir),
        "current_source_record_audit_sha256": current_audit_sha256,
        "generated_judgment_keys_sha256": generated_judgment_keys_sha256(raw_audit),
        "generated_judgment_surface_sha256": generated_judgment_surface_sha256(raw_audit),
        "selected_current_group_descriptors": dict(selected_descriptors),
        "selected_current_group_descriptors_sha256": _canonical_digest(
            dict(selected_descriptors)
        ),
        "review_scope": str(policy["scope"]),
        "response_semantic_ledger_sha256": _canonical_digest(
            _selected_semantic_judgment_ledger(result_items)
        ),
    }
    if bool(policy["uses_authenticated_overlay_union"]):
        metadata[SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD] = (
            _selected_authenticated_overlay_union_payload(overlay)
        )
    else:
        assert overlay.differential_overlay_path is not None
        metadata.update(
            {
                "differential_overlay_path": _relative_path(
                    overlay.differential_overlay_path, paper_dir
                ),
                "differential_overlay_sha256": overlay.differential_overlay_sha256,
                "differential_overlay_current_group_descriptors": dict(
                    overlay_descriptors
                ),
                "differential_overlay_current_group_descriptors_sha256": _canonical_digest(
                    dict(overlay_descriptors)
                ),
            }
        )
    result[SELECTED_CURRENT_REVALIDATION_FIELD] = metadata
    return result


def _selected_rebound_attestation_errors(
    metadata: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path,
    sidecar_items: Mapping[str, Mapping[str, Any]],
    overlay_path: Path | None = None,
    overlay_provenance_path: Path | None = None,
    raw_audit_path: Path | None = None,
    raw_audit_provenance_path: Path | None = None,
) -> list[str]:
    """Validate persisted selected-review provenance and response equality."""

    errors: list[str] = []
    path_text = str(metadata.get("attestation_path") or "").strip()
    if not path_text:
        return ["selected rebound sidecar has no attestation path"]
    relative = Path(path_text)
    if relative.is_absolute():
        return ["selected rebound attestation path is not paper-relative"]
    try:
        attestation_path = (paper_dir / relative).resolve()
        attestation_path.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError):
        return ["selected rebound attestation path escapes the paper folder"]
    try:
        attestation, attestation_sha256 = _read_json_object_with_sha256(attestation_path)
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    if _sha256(metadata.get("attestation_sha256")) != attestation_sha256:
        return ["selected rebound attestation bytes no longer match its recorded hash"]
    try:
        metadata_policy = _selected_current_revalidation_policy_configuration(
            metadata.get("policy_version")
        )
        attestation_policy = _selected_current_revalidation_policy_configuration(
            attestation.get("policy_version")
        )
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    if attestation_policy["policy_version"] != metadata_policy["policy_version"]:
        return [
            "selected rebound sidecar metadata policy does not match its attestation"
        ]
    prior_text = str(metadata.get("prior_judgment_sidecar_path") or "").strip()
    prior_relative = Path(prior_text)
    if not prior_text or prior_relative.is_absolute():
        return ["selected rebound has no paper-relative prior-sidecar snapshot"]
    try:
        prior_path = (paper_dir / prior_relative).resolve()
        prior_path.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError):
        return ["selected rebound prior-sidecar snapshot escapes the paper folder"]
    if prior_path == output_sidecar_path.resolve():
        return ["selected rebound prior-sidecar snapshot aliases the output sidecar"]
    try:
        prior_sidecar, prior_sha256 = _read_json_object_with_sha256(prior_path)
        prior_items = _sidecar_items(prior_sidecar, paper=paper)
        overlay = _selected_current_overlay_details(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
            raw_audit_path=raw_audit_path,
            raw_audit_provenance_path=raw_audit_provenance_path,
            use_authenticated_overlay_union=bool(
                metadata_policy["uses_authenticated_overlay_union"]
            ),
            require_differential_overlay=bool(
                metadata_policy["requires_differential_overlay"]
            ),
        )
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    if _sha256(metadata.get("prior_judgment_sidecar_sha256")) != prior_sha256:
        errors.append("selected rebound prior-sidecar bytes no longer match its recorded hash")
    attestation_error = _selected_current_attestation_error(
        attestation,
        paper=paper,
        paper_dir=paper_dir,
        prior_sidecar_path=prior_path,
        prior_sidecar_sha256=prior_sha256,
        raw_audit=raw_audit,
        prior_items=prior_items,
        overlay_descriptors=overlay.descriptors,
        overlay_path=overlay.differential_overlay_path,
        overlay_sha256=overlay.differential_overlay_sha256,
        overlay=overlay,
    )
    if attestation_error:
        errors.append(attestation_error)
        return errors
    try:
        selected_descriptors = _descriptor_ledger(
            attestation.get("selected_current_group_descriptors"),
            field="selected_current_group_descriptors",
        )
        expected_items = _selected_expected_semantic_items(
            prior_items,
            attestation,
            selected_keys=set(selected_descriptors),
            current_raw_audit=raw_audit,
            selected_descriptors=selected_descriptors,
            paper_dir=paper_dir,
            require_explicit_current_replacements=bool(
                attestation_policy["requires_explicit_current_replacements"]
            ),
        )
        _reproject_current_generated_association_credentials(
            raw_audit, expected_items, paper_dir=paper_dir
        )
    except SourceRecordCurrentRevalidationError as exc:
        return errors + [str(exc)]
    if set(sidecar_items) != set(selected_descriptors):
        errors.append("selected rebound sidecar has stale selected-group key coverage")
    if _canonical_digest(_selected_semantic_judgment_ledger(sidecar_items)) != _canonical_digest(
        _selected_semantic_judgment_ledger(expected_items)
    ):
        errors.append(
            "selected rebound semantic response ledger no longer matches its archived "
            "responses plus attested amendments/new judgments"
        )
    try:
        metadata_selected_descriptors = _descriptor_ledger(
            metadata.get("selected_current_group_descriptors"),
            field="sidecar selected_current_group_descriptors",
        )
    except SourceRecordCurrentRevalidationError as exc:
        return errors + [str(exc)]
    if bool(metadata_policy["uses_authenticated_overlay_union"]):
        if union_error := _selected_authenticated_overlay_union_error(
            metadata.get(SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD),
            overlay=overlay,
        ):
            errors.append(union_error)
    else:
        if _sha256(metadata.get("differential_overlay_sha256")) != (
            overlay.differential_overlay_sha256
        ):
            errors.append("selected rebound differential overlay bytes no longer match")
        try:
            metadata_overlay_descriptors = _descriptor_ledger(
                metadata.get("differential_overlay_current_group_descriptors"),
                field="sidecar differential_overlay_current_group_descriptors",
            )
        except SourceRecordCurrentRevalidationError as exc:
            return errors + [str(exc)]
        if metadata_overlay_descriptors != dict(overlay.descriptors):
            errors.append("selected rebound overlay descriptor ledger no longer matches")
    if metadata_selected_descriptors != selected_descriptors:
        errors.append("selected rebound selected descriptor ledger no longer matches")
    if _sha256(metadata.get("response_semantic_ledger_sha256")) != _canonical_digest(
        _selected_semantic_judgment_ledger(sidecar_items)
    ):
        errors.append("selected rebound response semantic ledger digest is stale")
    return errors


def validate_selected_rebound_sidecar(
    raw_audit: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path | None = None,
    overlay_path: Path | None = None,
    overlay_provenance_path: Path | None = None,
    raw_audit_path: Path | None = None,
    raw_audit_provenance_path: Path | None = None,
    include_downstream_target_disposition: bool = True,
) -> list[str]:
    """Return deterministic failures for an overlay-complement current rebind.

    Archive-path overrides verify a historical selected rebind against its
    own immutable current receipt.  Defaults remain the live paper paths.

    ``include_downstream_target_disposition=False`` is for the canonical
    response-ledger coverage gate only.  That gate still replays the complete
    selected descriptor/attestation/overlay route and per-item current pins;
    it separately checks the exact effective union passed by its caller.
    Source-target disposition and boundary-classification checks remain owned
    by their ordinary downstream closeout consumers, as they are for a fully
    ordinary current sidecar.  Skipping that duplicate downstream pass keeps a
    summary refresh from re-running the whole paper-level target audit merely
    to count its already-authenticated response ledger.
    """

    output_sidecar_path = output_sidecar_path or (
        paper_dir / "audit" / "source_record_match_llm.json"
    )
    raw_error = _raw_audit_error(raw_audit, paper=paper, paper_dir=paper_dir)
    if raw_error:
        return [raw_error]
    metadata = sidecar.get(SELECTED_CURRENT_REVALIDATION_FIELD)
    if not isinstance(metadata, Mapping):
        return ["selected rebound sidecar lacks selected current revalidation metadata"]
    try:
        metadata_policy = _selected_current_revalidation_policy_configuration(
            metadata.get("policy_version")
        )
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    try:
        sidecar_items = _sidecar_items(sidecar, paper=paper, allow_empty=True)
        overlay = _selected_current_overlay_details(
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
            raw_audit_path=raw_audit_path,
            raw_audit_provenance_path=raw_audit_provenance_path,
            use_authenticated_overlay_union=bool(
                metadata_policy["uses_authenticated_overlay_union"]
            ),
            require_differential_overlay=bool(
                metadata_policy["requires_differential_overlay"]
            ),
        )
        all_descriptors = _selected_current_group_descriptors(raw_audit)
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    errors: list[str] = []
    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    if _sha256(sidecar.get("source_record_audit_sha256")) != current_digest:
        errors.append("selected rebound sidecar is not bound to the current raw receipt")
    if not formalization_protocol_receipt_matches(sidecar, scope="review"):
        errors.append(
            "selected rebound sidecar has no current formalization review-protocol receipt"
        )
    if metadata.get("schema") != SELECTED_CURRENT_REVALIDATION_SCHEMA:
        errors.append("selected rebound sidecar has unsupported selected-revalidation schema")
    if str(metadata.get("current_judgment_sidecar_path") or "").strip() != _relative_path(
        output_sidecar_path, paper_dir
    ):
        errors.append("selected rebound sidecar metadata names a different output sidecar")
    try:
        selected_descriptors = _descriptor_ledger(
            metadata.get("selected_current_group_descriptors"),
            field="sidecar selected_current_group_descriptors",
        )
    except SourceRecordCurrentRevalidationError as exc:
        return errors + [str(exc)]
    expected_selected = {
        key: digest for key, digest in all_descriptors.items() if key not in overlay.descriptors
    }
    if selected_descriptors != expected_selected:
        errors.append(
            "selected rebound metadata does not cover exactly the semantic complement of the authenticated overlay"
        )
    errors.extend(
        _selected_rebound_attestation_errors(
            metadata,
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            output_sidecar_path=output_sidecar_path,
            sidecar_items=sidecar_items,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
            raw_audit_path=raw_audit_path,
            raw_audit_provenance_path=raw_audit_provenance_path,
        )
    )
    current_groups = generated_judgment_items(raw_audit)
    for key, item in sidecar_items.items():
        if _sha256(item.get("source_record_audit_sha256")) != current_digest:
            errors.append(f"{key}: selected response is not bound to the current aggregate raw receipt")
        if str(item.get("validator") or "").strip() == "" or str(
            item.get("validated_at") or ""
        ).strip() == "":
            errors.append(f"{key}: selected response lacks reviewer metadata")
        expected_pin_records = _current_item_pins(current_groups[key])
        expected_pins = frozenset(
            (
                str(pin["kind"]),
                SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                str(pin["source_record_item_sha256"]),
            )
            for pin in expected_pin_records
        )
        actual_pins = REPOSITORY.source_record_judgment_item_digest_pins(item)
        if expected_pins and actual_pins != expected_pins:
            errors.append(f"{key}: selected response has stale or incomplete current item pins")
        if not expected_pins and actual_pins:
            errors.append(f"{key}: selected response has a partial item pin")
        item_metadata = item.get(SELECTED_CURRENT_REVALIDATION_ITEM_FIELD)
        if not isinstance(item_metadata, Mapping):
            errors.append(f"{key}: selected response lacks per-item attestation metadata")
        elif (
            item_metadata.get("schema") != SELECTED_CURRENT_REVALIDATION_SCHEMA
            or _sha256(item_metadata.get("current_group_semantic_descriptor_sha256"))
            != selected_descriptors.get(key)
        ):
            errors.append(f"{key}: selected response has stale per-item semantic descriptor metadata")

    if not include_downstream_target_disposition:
        return errors

    current_judgments = EVIDENCE.current_source_record_judgment_items(
        dict(raw_audit),
        dict(sidecar),
        folder=paper_dir,
        differential_overlay_path=overlay_path,
        differential_current_raw_audit_path=raw_audit_path,
        differential_current_raw_audit_provenance_path=(
            raw_audit_provenance_path
        ),
        allow_archived_raw_identity=(
            raw_audit_path is not None and raw_audit_provenance_path is not None
        ),
    )
    expected_keys = set(all_descriptors)
    if set(current_judgments) != expected_keys:
        missing = sorted(expected_keys - set(current_judgments))
        extra = sorted(set(current_judgments) - expected_keys)
        errors.append(
            "shared v10 current-judgment loader rejected selected rebind"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    effective_sidecar = dict(sidecar)
    effective_sidecar["items"] = {**sidecar_items, **overlay.items}
    errors.extend(
        _target_disposition_errors(
            raw_audit,
            effective_sidecar,
            paper_dir=paper_dir,
            historical_receipt_only=(
                raw_audit_path is not None
                and raw_audit_provenance_path is not None
            ),
        )
    )
    errors.extend(_boundary_classification_errors(raw_audit, effective_sidecar))
    return errors


def materialize_authenticated_selected_evidence(
    raw_audit: Mapping[str, Any],
    selected_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    selected_sidecar_path: Path,
    raw_audit_path: Path,
    overlay_path: Path,
    overlay_provenance_path: Path | None = None,
    raw_audit_provenance_path: Path | None = None,
    output_sidecar_path: Path | None = None,
) -> dict[str, Any]:
    """Materialize one verified overlay-plus-selected current evidence ledger.

    This is a receipt-preserving composition, not a new semantic review.  It
    first replays the selected-sidecar validation against the exact historical
    raw receipt and differential overlay.  It then combines only the two
    descriptor-complement ledgers.  Differential items receive the historical
    item receipts under an explicit composition marker and current item pins
    generated from the checked historical raw receipt, so a later differential
    closeout can use the materialized ledger as ordinary prior evidence.

    The storage keys are checked only as the complete current generated-key
    ledger.  Which entries form the overlay complement is determined by the
    authenticated semantic descriptor receipts, not by their names.
    """

    output_sidecar_path = output_sidecar_path or (
        paper_dir / "audit" / "source_record_match_llm.json"
    )
    saved_selected, selected_sha256 = _loaded_snapshot_matches(
        selected_sidecar_path, selected_sidecar, label="selected current sidecar"
    )
    errors = validate_selected_rebound_sidecar(
        raw_audit,
        saved_selected,
        paper=paper,
        paper_dir=paper_dir,
        output_sidecar_path=output_sidecar_path,
        overlay_path=overlay_path,
        overlay_provenance_path=overlay_provenance_path,
        raw_audit_path=raw_audit_path,
        raw_audit_provenance_path=raw_audit_provenance_path,
    )
    if errors:
        raise SourceRecordCurrentRevalidationError(
            "cannot materialize selected current evidence: " + "; ".join(errors)
        )
    selected_items = _sidecar_items(saved_selected, paper=paper, allow_empty=True)
    selected_metadata = saved_selected.get(SELECTED_CURRENT_REVALIDATION_FIELD)
    if not isinstance(selected_metadata, Mapping):
        raise SourceRecordCurrentRevalidationError(
            "selected current sidecar lacks selected-revalidation metadata"
        )
    policy = _selected_current_revalidation_policy_configuration(
        selected_metadata.get("policy_version")
    )
    overlay = _selected_current_overlay_details(
        raw_audit,
        paper=paper,
        paper_dir=paper_dir,
        overlay_path=overlay_path,
        overlay_provenance_path=overlay_provenance_path,
        raw_audit_path=raw_audit_path,
        raw_audit_provenance_path=raw_audit_provenance_path,
        use_authenticated_overlay_union=bool(
            policy["uses_authenticated_overlay_union"]
        ),
        require_differential_overlay=bool(policy["requires_differential_overlay"]),
    )
    loaded_overlay = overlay.items
    overlay_descriptors = overlay.descriptors
    all_descriptors = _selected_current_group_descriptors(raw_audit)
    current_groups = generated_judgment_items(raw_audit)
    expected_selected = {
        key: descriptor
        for key, descriptor in all_descriptors.items()
        if key not in overlay_descriptors
    }
    if set(selected_items) != set(expected_selected):
        raise SourceRecordCurrentRevalidationError(
            "selected current sidecar does not exactly cover the authenticated "
            "overlay complement"
        )
    if set(selected_items) & set(loaded_overlay):
        raise SourceRecordCurrentRevalidationError(
            "selected current sidecar overlaps the authenticated overlay"
        )
    if set(selected_items) | set(loaded_overlay) != set(current_groups):
        raise SourceRecordCurrentRevalidationError(
            "selected and overlay ledgers do not cover every historical current group"
        )

    current_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    items: dict[str, dict[str, Any]] = {
        key: copy.deepcopy(value) for key, value in selected_items.items()
    }
    for key, raw_value in loaded_overlay.items():
        value = copy.deepcopy(dict(raw_value))
        prior_audit_digest = _sha256(value.get("source_record_audit_sha256"))
        historical_receipt = _historical_item_receipt(value)
        if historical_receipt:
            existing = value.get(PRIOR_ITEM_RECEIPT_FIELD)
            if isinstance(existing, Mapping):
                value[PRIOR_ITEM_RECEIPT_FIELD] = {
                    "prior": copy.deepcopy(dict(existing)),
                    (
                        "authenticated_overlay"
                        if bool(policy["uses_authenticated_overlay_union"])
                        else "differential"
                    ): historical_receipt,
                }
            else:
                value[PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        value["source_record_audit_sha256"] = current_digest
        current_pins = _current_item_pins(current_groups[key])
        if current_pins:
            value["source_record_item_digest_schema"] = SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            value["source_record_item_sha256s"] = current_pins
            value["source_record_item_sha256"] = current_pins[0][
                "source_record_item_sha256"
            ]
        item_composition: dict[str, Any] = {
            "schema": AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA,
            "prior_source_record_audit_sha256": prior_audit_digest,
            "current_source_record_audit_sha256": current_digest,
            "current_group_semantic_descriptor_sha256": all_descriptors[key],
        }
        if bool(policy["uses_authenticated_overlay_union"]):
            item_composition["authenticated_overlay_union_sha256"] = _canonical_digest(
                _selected_authenticated_overlay_union_payload(overlay)
            )
        else:
            item_composition["differential_overlay_sha256"] = (
                overlay.differential_overlay_sha256
            )
        value[AUTHENTICATED_EVIDENCE_COMPOSITION_ITEM_FIELD] = item_composition
        items[key] = value

    result = copy.deepcopy(dict(saved_selected))
    result["paper"] = paper
    result["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
    result["source_record_audit_sha256"] = current_digest
    result["items"] = items
    composition_metadata: dict[str, Any] = {
        "schema": AUTHENTICATED_EVIDENCE_COMPOSITION_SCHEMA,
        "policy_version": AUTHENTICATED_EVIDENCE_COMPOSITION_POLICY_VERSION,
        "historical_raw_audit_path": _relative_path(raw_audit_path, paper_dir),
        "historical_raw_audit_sha256": current_digest,
        "historical_raw_audit_file_sha256": _file_sha256(raw_audit_path),
        "selected_current_sidecar_path": _relative_path(
            selected_sidecar_path, paper_dir
        ),
        "selected_current_sidecar_sha256": selected_sha256,
        "selected_current_group_descriptors": expected_selected,
        "generated_judgment_keys_sha256": generated_judgment_keys_sha256(raw_audit),
        "generated_judgment_surface_sha256": generated_judgment_surface_sha256(raw_audit),
        "response_semantic_ledger_sha256": _canonical_digest(
            _semantic_judgment_ledger(items)
        ),
    }
    if bool(policy["uses_authenticated_overlay_union"]):
        composition_metadata[SELECTED_CURRENT_AUTHENTICATED_OVERLAY_UNION_FIELD] = (
            _selected_authenticated_overlay_union_payload(overlay)
        )
    else:
        assert overlay.differential_overlay_path is not None
        composition_metadata.update(
            {
                "differential_overlay_path": _relative_path(
                    overlay.differential_overlay_path, paper_dir
                ),
                "differential_overlay_archive_path": _relative_path(
                    overlay_path, paper_dir
                ),
                "differential_overlay_sha256": overlay.differential_overlay_sha256,
                "differential_overlay_current_group_descriptors": dict(
                    overlay_descriptors
                ),
            }
        )
    result[AUTHENTICATED_EVIDENCE_COMPOSITION_FIELD] = composition_metadata
    return result


def materialized_authenticated_selected_evidence_errors(
    materialized: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    selected_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    selected_sidecar_path: Path,
    raw_audit_path: Path,
    overlay_path: Path,
    overlay_provenance_path: Path | None = None,
    raw_audit_provenance_path: Path | None = None,
    output_sidecar_path: Path | None = None,
) -> list[str]:
    """Return failures when a materialized composition no longer replays.

    Reconstructing the result from immutable inputs is intentionally stronger
    than checking a summary hash.  A changed source, overlay, selected review,
    descriptor ledger, or materialized response becomes a deterministic
    failure before the artifact is used as prior evidence.
    """

    try:
        expected = materialize_authenticated_selected_evidence(
            raw_audit,
            selected_sidecar,
            paper=paper,
            paper_dir=paper_dir,
            selected_sidecar_path=selected_sidecar_path,
            raw_audit_path=raw_audit_path,
            overlay_path=overlay_path,
            overlay_provenance_path=overlay_provenance_path,
            raw_audit_provenance_path=raw_audit_provenance_path,
            output_sidecar_path=output_sidecar_path,
        )
    except SourceRecordCurrentRevalidationError as exc:
        return [str(exc)]
    if _canonical_digest(materialized) != _canonical_digest(expected):
        return [
            "materialized authenticated evidence no longer matches the exact "
            "selected-sidecar and differential-overlay replay"
        ]
    return []


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Attested aggregate-current rebind of a complete v10 source-record "
            "judgment sidecar."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--judgments", type=Path)
    parser.add_argument(
        "--prior-judgments",
        type=Path,
        help="immutable snapshot of the prior v10 sidecar, distinct from --judgments",
    )
    parser.add_argument("--attestation", type=Path)
    parser.add_argument(
        "--write-attestation-template",
        type=Path,
        help="write a non-evidence template; cannot be combined with --write",
    )
    parser.add_argument(
        "--selected-attestation",
        type=Path,
        help=(
            "attestation for only groups outside the authenticated current-overlay "
            "union; cannot be combined with --attestation"
        ),
    )
    parser.add_argument(
        "--write-selected-attestation-template",
        type=Path,
        help=(
            "write a non-evidence selected-review template; cannot be combined "
            "with --write"
        ),
    )
    parser.add_argument(
        "--archive-current-judgments-to",
        type=Path,
        help="copy --judgments once to an immutable paper-local prior-sidecar snapshot",
    )
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    raw_path = args.raw_audit or paper_dir / "audit" / "source_record_audit.json"
    judgments_path = args.judgments or paper_dir / "audit" / "source_record_match_llm.json"
    if args.archive_current_judgments_to is not None:
        archive_path = args.archive_current_judgments_to
        try:
            archive_path.resolve().relative_to(paper_dir.resolve())
        except (OSError, RuntimeError, ValueError) as exc:
            raise SystemExit("--archive-current-judgments-to must remain inside the paper") from exc
        if archive_path.resolve() == judgments_path.resolve():
            raise SystemExit("prior-sidecar archive path must differ from --judgments")
        if archive_path.exists():
            raise SystemExit(f"refusing to overwrite existing prior-sidecar snapshot: {archive_path}")
        try:
            archive_path.write_bytes(judgments_path.read_bytes())
        except OSError as exc:
            raise SystemExit(f"could not archive current judgments: {exc}") from exc
        print(
            f"archived prior v10 sidecar: {archive_path} "
            f"({_file_sha256(archive_path)})"
        )
        return 0
    if args.prior_judgments is None:
        raise SystemExit("--prior-judgments immutable snapshot is required")
    prior_path = args.prior_judgments
    if prior_path.resolve() == judgments_path.resolve():
        raise SystemExit("--prior-judgments must differ from the output --judgments path")
    raw_audit = _load_json_object(raw_path)
    prior_sidecar = _load_json_object(prior_path)
    if args.write_selected_attestation_template:
        if args.write or args.write_attestation_template or args.selected_attestation:
            raise SystemExit(
                "--write-selected-attestation-template cannot be combined with --write or another attestation mode"
            )
        template = selected_attestation_template(
            raw_audit,
            prior_sidecar,
            paper=args.paper,
            paper_dir=paper_dir,
            prior_sidecar_path=prior_path,
        )
        args.write_selected_attestation_template.write_text(
            json.dumps(template, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(
            "wrote non-evidence selected current-revalidation attestation template: "
            f"{args.write_selected_attestation_template}"
        )
        return 0
    if args.write_attestation_template:
        if args.write or args.selected_attestation:
            raise SystemExit("--write-attestation-template cannot be combined with --write")
        template = attestation_template(
            raw_audit,
            prior_sidecar,
            paper=args.paper,
            paper_dir=paper_dir,
            prior_sidecar_path=prior_path,
            use_paper_local_semantic_contract_revalidation=(
                raw_path.resolve()
                == (paper_dir / "audit" / "source_record_audit.json").resolve()
            ),
        )
        args.write_attestation_template.write_text(
            json.dumps(template, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"wrote non-evidence attestation template: {args.write_attestation_template}")
        return 0
    if args.selected_attestation is not None:
        if args.attestation is not None:
            raise SystemExit("--selected-attestation cannot be combined with --attestation")
        attestation = _load_json_object(args.selected_attestation)
        try:
            rebound = selected_rebound_sidecar(
                raw_audit,
                prior_sidecar,
                attestation,
                paper=args.paper,
                paper_dir=paper_dir,
                prior_sidecar_path=prior_path,
                attestation_path=args.selected_attestation,
                output_sidecar_path=judgments_path,
            )
        except SourceRecordCurrentRevalidationError as exc:
            print(f"{args.paper}: selected revalidation refused: {exc}", file=sys.stderr)
            return 1
        errors = validate_selected_rebound_sidecar(
            raw_audit,
            rebound,
            paper=args.paper,
            paper_dir=paper_dir,
            output_sidecar_path=judgments_path,
        )
        if errors:
            print(f"{args.paper}: selected revalidation refused:", file=sys.stderr)
            for error in errors:
                print(f"- {error}", file=sys.stderr)
            return 1
        if args.write:
            if write_rebound_sidecar_if_changed(judgments_path, rebound):
                print(
                    f"{args.paper}: wrote selected attested current v10 rebind to {judgments_path}"
                )
            else:
                print(
                    f"{args.paper}: selected attested current v10 rebind already "
                    "materialized; no receipt was rewritten"
                )
        else:
            print(
                f"{args.paper}: selected attested current v10 rebind validates; rerun "
                "with --write to update the judgment sidecar"
            )
        return 0
    if args.attestation is None:
        raise SystemExit("--attestation is required unless writing a template")
    attestation = _load_json_object(args.attestation)
    try:
        rebound = rebound_sidecar(
            raw_audit,
            prior_sidecar,
            attestation,
            paper=args.paper,
            paper_dir=paper_dir,
            prior_sidecar_path=prior_path,
            attestation_path=args.attestation,
            output_sidecar_path=judgments_path,
        )
    except SourceRecordCurrentRevalidationError as exc:
        print(f"{args.paper}: revalidation refused: {exc}", file=sys.stderr)
        return 1
    errors = validate_rebound_sidecar(
        raw_audit,
        rebound,
        paper=args.paper,
        paper_dir=paper_dir,
        output_sidecar_path=judgments_path,
    )
    if errors:
        print(f"{args.paper}: revalidation refused:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    if args.write:
        if write_rebound_sidecar_if_changed(judgments_path, rebound):
            print(f"{args.paper}: wrote attested current v10 rebind to {judgments_path}")
        else:
            print(
                f"{args.paper}: attested current v10 rebind already materialized; "
                "no receipt was rewritten"
            )
    else:
        print(
            f"{args.paper}: attested current v10 rebind validates; rerun with --write "
            "to update the judgment sidecar"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
