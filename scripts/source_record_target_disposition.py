"""Validate source-record semantic target dispositions.

The source-record generator emits a fully-qualified, source-map association for
some expanded semantic-model rows.  That association is provenance, not a
proof: this module checks that a human semantic judgment labels the *kind* of
target it reviewed using the current source map and source-proof ledger.

In particular, a statement whose archival source target has been corrected may
not receive ordinary literal-source credit merely because the surrounding Lean
surface still resembles the original paper.  The checks are deliberately
driven by explicit source-map identities and pinned ledger ids. Lean row,
declaration, and function names are never used as source evidence. A schema-2
fully-qualified declaration appears only as the coordinate for the current
elaborated Lean signature pin; it cannot select or replace a source statement
on its own.
"""

from __future__ import annotations

import copy
import hashlib
import json
import re
from collections.abc import Mapping
from dataclasses import dataclass
from pathlib import Path

try:
    from corrected_target_identity import (
        corrected_target_record_digest as _shared_corrected_target_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - supports package imports.
    from scripts.corrected_target_identity import (
        corrected_target_record_digest as _shared_corrected_target_record_digest,
    )

try:
    from source_record_legacy_contract import (
        EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN,
        EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
    )
except ModuleNotFoundError:  # pragma: no cover - supports package imports.
    from scripts.source_record_legacy_contract import (
        EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN,
        EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
    )

try:
    from configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        configured_assumption_formalization_regularity_response_errors,
        project_configured_assumption_formalization_regularity_pin,
        response_claims_configured_assumption_formalization_regularity,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        configured_assumption_formalization_regularity_response_errors,
        project_configured_assumption_formalization_regularity_pin,
        response_claims_configured_assumption_formalization_regularity,
    )

try:
    from source_coverage_scope import (
        LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        SOURCE_DOMAIN_PRESENTATION_KINDS,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        filter_source_map_items_for_coverage,
        legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_named_result_environment_kinds_from_map,
        source_coverage_mode_from_map,
        source_item_in_coverage_scope,
        source_item_coverage_sha256,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_coverage_scope import (
        LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        SOURCE_DOMAIN_PRESENTATION_KINDS,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        filter_source_map_items_for_coverage,
        legacy_source_item_coverage_sha256_before_direct_source_status_exclusion,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_named_result_environment_kinds_from_map,
        source_coverage_mode_from_map,
        source_item_in_coverage_scope,
        source_item_coverage_sha256,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )

try:
    from source_record_assumption_association import (
        SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
        SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN,
        SOURCE_ASSUMPTION_ASSOCIATION_ROLE,
        source_assumption_effective_semantic_pin,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from scripts.source_record_assumption_association import (
        SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
        SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN,
        SOURCE_ASSUMPTION_ASSOCIATION_ROLE,
        source_assumption_effective_semantic_pin,
    )


SOURCE_TARGET_DISPOSITION_FIELD = "source_target_disposition"
_BYTE_OVERRIDE_UNSET = object()
SOURCE_TARGET_DISPOSITIONS = frozenset(
    {
        "literal_source_match",
        "approved_source_convention",
        "approved_corrected_target",
    }
)
SOURCE_TARGET_MATCH_VERDICTS = {
    "literal_source_match": "matches_literal_source",
    "approved_source_convention": "matches_approved_source_convention",
    "approved_corrected_target": "matches_approved_corrected_target",
}
SOURCE_CONTRACT_ASSOCIATION_FIELD = "source_contract_association"
SOURCE_CONTRACT_ASSOCIATION_SHA256_FIELD = "source_contract_association_sha256"
RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD = (
    "recursive_field_explicit_parent_route"
)
RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_SCHEMA = 1
RECURSIVE_FIELD_CONTAINER_CLASSIFICATION = "container_recursively_audited"
# A recursive field scope is a narrow source-model provenance route, not a
# general way to approve arbitrary source-record classifications.  In
# particular, a claim of a Lean derivation, a corrected source target, or an
# external boundary must still use its ordinary evidence contract.  These are
# the only two leaf dispositions that can be closed by the scoped parent
# receipt below.
RECURSIVE_FIELD_SOURCE_CREDIT_CLASSIFICATIONS = frozenset(
    {"validated_source_assumption", "approved_source_convention"}
)
RECURSIVE_FIELD_SCOPE_PERMITTED_CLASSIFICATIONS = (
    RECURSIVE_FIELD_SOURCE_CREDIT_CLASSIFICATIONS
    | frozenset({RECURSIVE_FIELD_CONTAINER_CLASSIFICATION})
)
_RECURSIVE_FIELD_SOURCE_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>\d+)(?:-(?P<end>\d+))?",
    re.I,
)
RECURSIVE_FIELD_DIRECT_SEMANTIC_CONTRACT_PARENT_ROLES = frozenset(
    {"direct_evidence", "transparent_spec"}
)
SEMANTIC_ASSOCIATION_SHA256_FIELD = "semantic_association_sha256"
SEMANTIC_ASSOCIATION_SCHEMA = 2
REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD = (
    "reviewed_elaborated_signature_identity"
)
SOURCE_SEMANTIC_SHA256_FIELD = "source_semantic_sha256"
SOURCE_MAP_ITEM_SHA256_FIELD = "source_map_item_sha256_by_key"
SOURCE_MAP_ITEM_KEYS_SHA256_FIELD = "source_map_item_keys_sha256"
INPUT_SOURCE_CREDIT_CLASSIFICATIONS = frozenset(
    {
        "validated_source_assumption",
        "approved_source_convention",
        "approved_corrected_condition",
    }
)
FULL_CLOSEOUT_STATUSES = frozenset({"formalized", "formalized with caveat"})
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
CORRECTED_SOURCE_STATEMENT_RESOLUTION = "corrected_source_statement"
EXPLICIT_DIRECT_SOURCE_ROUTE_FIELDS = (
    "lean_declarations",
    "proof_lean_declarations",
    "spec_lean_declarations",
)
STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD = (
    "statement_source_component_association"
)
STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN = (
    "authenticated_v10_statement_source_component"
)
STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE = (
    "source_definition_component_semantic_route"
)
STATEMENT_SOURCE_COMPONENT_IDENTITY_FIELD = (
    "source_definition_component_semantic_identity"
)
STATEMENT_SOURCE_COMPONENT_SEMANTIC_ASSOCIATION_FIELD = (
    "component_semantic_association_sha256"
)
STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN = (
    "authenticated_v10_whole_definition_statement_source_routes"
)
STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE = "whole_definition_semantic_route"
STATEMENT_SOURCE_REVIEW_IDENTITY_FIELD = "statement_source_review_identity"
STATEMENT_SOURCE_REVIEW_IDENTITY_SCHEMA = 1
STATEMENT_SOURCE_COMPONENT_IDENTITY_SCHEMA = 1
_TARGET_SHA256_FIELD = "corrected_target_sha256_by_source_item"
_TARGET_SEMANTIC_SHA256_FIELD = "corrected_target_sha256_by_source_semantic_sha256"
_CONVENTION_SHA256_FIELD = "model_convention_sha256_by_id"
_SHA256_RE = re.compile(r"[0-9a-f]{64}")

# A source-record association generated before direct ``source_status`` was
# removed from the per-item semantic projection cannot be silently treated as
# current.  The explicit receipt below is the only bridge: it binds the exact
# raw audit bytes, current statement-map bytes, every original association,
# and the deterministic replacement association produced by that one
# projection change.  It never permits a source/target/route edit.
SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_SCHEMA = 2
SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_POLICY_VERSION = (
    "source-record-v10-schema4-to5-source-status-projection-rebind-v2"
)
SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_ARTIFACT_KIND = (
    "source_record_v10_direct_source_status_projection_rebind"
)
_STATUS_INCLUDED_TO_EXCLUDED_TRANSITION = (
    "schema4_direct_source_status_included_to_schema5_excluded"
)
_STATUS_EXCLUDED_SCHEMA_ONLY_TRANSITION = (
    "schema4_direct_source_status_excluded_to_schema5_excluded"
)


@dataclass(frozen=True)
class ValidatedAdministrativeProjectionRebind:
    """In-memory authority for one receipt-checked transport rebind.

    This object is intentionally constructed only by
    :func:`validate_administrative_projection_rebind`.  Callers cannot turn a
    claimed legacy hash into current source credit by passing an arbitrary
    mapping to a target-disposition validator.
    """

    # Map both raw and rebounded association records to the one receipt binding.
    # The latter lets a freshly generated schema-5 association accept only the
    # same response transport that is already proved for its exact schema-4
    # predecessor.  It does not relax source-record currentness elsewhere.
    association_rebinds: Mapping[str, Mapping[str, object]]
    association_bindings: Mapping[str, Mapping[str, object]]
    rebound_association_bindings: Mapping[str, Mapping[str, object]]


def _paper_local_relative_path(path: Path, paper_dir: Path, *, label: str) -> tuple[str, str]:
    """Return one paper-local path for a receipt or a fail-closed error."""

    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix(), ""
    except (OSError, RuntimeError, ValueError):
        return "", f"{label} must remain inside the paper directory"


def _canonical_digest_payload(payload: object) -> object:
    """Mirror source-record's order-insensitive digest representation."""

    if isinstance(payload, Mapping):
        return {
            str(key): _canonical_digest_payload(value)
            for key, value in sorted(payload.items(), key=lambda item: str(item[0]))
        }
    if isinstance(payload, list):
        canonical_items = [_canonical_digest_payload(item) for item in payload]
        return sorted(
            canonical_items,
            key=lambda item: json.dumps(item, ensure_ascii=True, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(payload, tuple):
        return _canonical_digest_payload(list(payload))
    return payload


def source_map_item_record_digest(raw: object) -> str:
    """Return the generator-compatible digest for one source-map item."""

    encoded = json.dumps(
        _canonical_digest_payload(raw),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def source_contract_association_record_digest(raw: object) -> str:
    """Return the immutable digest for a generated input association."""

    payload: object = dict(raw) if isinstance(raw, Mapping) else raw
    if isinstance(payload, dict):
        payload.pop("association_sha256", None)
    return source_map_item_record_digest(payload)


def semantic_association_record_digest(
    source_semantic_sha256: object,
    reviewed_elaborated_signature_identity: object,
) -> str:
    """Return the schema-2 semantic association pin.

    This is intentionally narrower than ``association_sha256``. It is the
    only association pin that can survive a source-map key or navigation-only
    route refresh, and it therefore binds the source-only identities and
    Lean's name-independent elaborated signature. The current fully-qualified
    declaration remains a separately validated coordinate: it must still be
    the source map's explicit route and match the generated semantic item, but
    its spelling cannot manufacture or invalidate semantic reuse. Full
    association and source-map digests remain independently required on the
    generated audit artifact for aggregate freshness.

    Invalid or ambiguous input has no semantic pin and returns the empty
    string.  Callers must reject that case rather than falling back to a route
    name or map key.
    """

    if not isinstance(source_semantic_sha256, list):
        return ""
    semantic_digests = [
        str(value or "").strip().lower() for value in source_semantic_sha256
    ]
    if (
        not semantic_digests
        or any(not _SHA256_RE.fullmatch(value) for value in semantic_digests)
        or len(set(semantic_digests)) != len(semantic_digests)
    ):
        return ""
    if not isinstance(reviewed_elaborated_signature_identity, Mapping):
        return ""
    qualified = str(
        reviewed_elaborated_signature_identity.get("qualified_declaration") or ""
    ).strip()
    elaborated_signature = str(
        reviewed_elaborated_signature_identity.get(
            "elaborated_signature_sha256"
        )
        or ""
    ).strip().lower()
    if (
        not qualified
        or "." not in qualified
        or not _SHA256_RE.fullmatch(elaborated_signature)
    ):
        return ""
    return source_map_item_record_digest(
        {
            "schema": SEMANTIC_ASSOCIATION_SCHEMA,
            "source_item_semantic_sha256": sorted(semantic_digests),
            "elaborated_signature_sha256": elaborated_signature,
        }
    )


@dataclass(frozen=True)
class SourceRecordResponseAssociationProjection:
    """Current generated association pins needed by one response group.

    A saved review response is not allowed to choose a source association.  The
    raw audit has already grouped the exact current members of a response slot;
    this value is reconstructed from that group before a response is admitted.
    The projection intentionally contains only generated schema-2 pins.  A
    legacy/no-association group therefore remains untouched rather than being
    assigned a synthetic source identity.
    """

    top_level_semantic_association_sha256: str
    semantic_dimension_association_sha256: Mapping[str, str]
    nested_dimension_association_sha256: Mapping[str, Mapping[str, str]]
    top_level_corrected_target_sha256_by_source_semantic_sha256: Mapping[str, str]
    semantic_dimension_corrected_target_sha256_by_source_semantic_sha256: Mapping[
        str, Mapping[str, str]
    ]

    @property
    def has_injections(self) -> bool:
        return bool(
            self.top_level_semantic_association_sha256
            or self.semantic_dimension_association_sha256
            or self.nested_dimension_association_sha256
            or self.top_level_corrected_target_sha256_by_source_semantic_sha256
            or self.semantic_dimension_corrected_target_sha256_by_source_semantic_sha256
        )


def _source_record_projection_association_pin(
    association: Mapping[str, object], *, field: str
) -> tuple[str, bool, str]:
    """Return one independently recomputed schema-2 association pin.

    ``bool`` reports that the association is schema 2.  The function never
    falls back to a declaration spelling, source-map key, or saved response.
    """

    schema = association.get("schema")
    if schema != SEMANTIC_ASSOCIATION_SCHEMA:
        return "", False, ""
    if (
        str(association.get("association_origin") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
        and str(association.get("role") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ROLE
    ):
        assumption_pin, assumption_error = (
            source_assumption_effective_semantic_pin(association)
        )
        if assumption_error:
            return "", True, f"{field} " + assumption_error
        return assumption_pin, True, ""
    if (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    ):
        component_pin, component_error = (
            statement_source_component_effective_semantic_pin(association)
        )
        if component_error:
            return "", True, f"{field} " + component_error
        return component_pin, True, ""
    if (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        review_pin, review_error = statement_source_review_effective_semantic_pin(
            association
        )
        if review_error:
            return "", True, f"{field} " + review_error
        return review_pin, True, ""

    raw_identities = association.get("source_item_identities")
    raw_semantic_digests: object
    if isinstance(raw_identities, list):
        if not raw_identities:
            return "", True, f"{field} has no source_item_identities"
        semantic_digests: list[str] = []
        for index, identity in enumerate(raw_identities):
            if not isinstance(identity, Mapping):
                return (
                    "",
                    True,
                    f"{field}.source_item_identities[{index}] is not an object",
                )
            semantic_digests.append(
                str(identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "")
                .strip()
                .lower()
            )
        raw_semantic_digests = semantic_digests
    else:
        raw_semantic_digests = association.get("source_item_semantic_sha256")

    if not isinstance(raw_semantic_digests, list) or not raw_semantic_digests:
        return "", True, f"{field} has no source semantic identities"
    semantic_digests = [
        str(value or "").strip().lower() for value in raw_semantic_digests
    ]
    if (
        any(not _SHA256_RE.fullmatch(value) for value in semantic_digests)
        or len(semantic_digests) != len(set(semantic_digests))
    ):
        return "", True, f"{field} has malformed or duplicate source semantic identities"

    signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
    expected = semantic_association_record_digest(semantic_digests, signature)
    supplied = str(
        association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or ""
    ).strip().lower()
    if not expected or supplied != expected:
        return (
            "",
            True,
            f"{field}.{SEMANTIC_ASSOCIATION_SHA256_FIELD} is missing, malformed, or stale",
        )
    return expected, True, ""


def _source_record_projection_corrected_target_digests(
    association: Mapping[str, object],
    statement_map: Mapping[str, object] | None,
    *,
    field: str,
) -> tuple[dict[str, str], str]:
    """Return current corrected-target digests selected by raw schema-2 IDs.

    A corrected-target response map is source-map provenance.  It must be
    reconstructed from the exact generated association identities and the
    current source map; a response cannot supply or select its own keys.
    ``None`` preserves direct unit callers that have no source map.  Evidence
    and materialization entry points always provide the current map.
    """

    if statement_map is None or association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
        return {}, ""
    raw_identities = association.get("source_item_identities")
    if not isinstance(raw_identities, list) or not raw_identities:
        return {}, f"{field} has no source_item_identities for corrected-target projection"
    map_items, map_errors = _source_map_items(statement_map)
    if map_errors:
        return {}, "; ".join(map_errors)
    corrected: dict[str, str] = {}
    seen_source_keys: set[str] = set()
    for index, raw_identity in enumerate(raw_identities):
        if not isinstance(raw_identity, Mapping):
            return {}, f"{field}.source_item_identities[{index}] is not an object"
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_semantic_digest = str(
            raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
        ).strip().lower()
        source_location = _normalized_text(raw_identity.get("source_location"))
        source_map_digest = str(
            raw_identity.get("source_map_item_sha256") or ""
        ).strip().lower()
        if (
            not source_key
            or source_key in seen_source_keys
            or not _SHA256_RE.fullmatch(source_semantic_digest)
            or not source_location
            or not _SHA256_RE.fullmatch(source_map_digest)
        ):
            return (
                {},
                f"{field}.source_item_identities[{index}] is malformed or duplicates a source identity",
            )
        seen_source_keys.add(source_key)
        source_item = map_items.get(source_key)
        if source_item is None:
            return {}, f"{field} source identity `{source_key}` is absent from the current source map"
        if (
            _normalized_text(source_item.get("source_location")) != source_location
            or source_record_source_item_record_sha256(source_item)
            != source_map_digest
            or source_record_source_item_semantic_sha256(dict(source_item), "")
            != source_semantic_digest
        ):
            return (
                {},
                f"{field} source identity `{source_key}` does not match the current source map",
            )
        if (
            str(source_item.get("coverage_status") or "").strip().lower()
            != CORRECTED_SOURCE_STATEMENT_STATUS
        ):
            continue
        target = source_item.get("corrected_target")
        if not isinstance(target, Mapping):
            return {}, f"current corrected source-map item `{source_key}` has no corrected_target object"
        digest = corrected_target_record_digest(target)
        recorded = str(target.get("corrected_target_sha256") or "").strip().lower()
        if recorded != digest:
            return {}, f"current corrected source-map item `{source_key}` has a stale corrected_target_sha256"
        prior = corrected.get(source_semantic_digest)
        if prior is not None and prior != digest:
            return (
                {},
                "current raw association has conflicting corrected-target digests for one source semantic identity",
            )
        corrected[source_semantic_digest] = digest
    return dict(sorted(corrected.items())), ""


def _source_record_nested_projection_pin(
    raw_dimension: Mapping[str, object], *, association_field: str
) -> tuple[str, str]:
    """Return one nested-analysis association pin, rejecting malformed input."""

    association = raw_dimension.get(association_field)
    if association is None:
        return "", ""
    if not isinstance(association, Mapping):
        return "", f"{association_field} is not an object"
    pin, schema_two, error = _source_record_projection_association_pin(
        association, field=association_field
    )
    if error:
        return "", error
    if not schema_two:
        return "", f"{association_field} must use schema 2"
    return pin, ""


def source_record_response_association_projection(
    raw_members: object,
    *,
    judgment_key: object | None = None,
    statement_map: Mapping[str, object] | None = None,
) -> tuple[SourceRecordResponseAssociationProjection | None, str]:
    """Reconstruct the sole current source-association projection for a group.

    The caller supplies the exact current members from
    ``source_record_obligation_groups.raw_source_record_obligation_groups``.  Every
    member is checked against the target response key.  Source associations
    are selected solely by their generated structural role: semantic-model
    associations use the established explicit precedence, while theorem-facing,
    boundary, and conclusion members use ``source_contract_association``. A group
    with conflicting or mixed schema-2/legacy source associations is rejected
    rather than allowing a response to smuggle a chosen pin into one branch.
    """

    if not isinstance(raw_members, list) or not raw_members:
        return None, "current raw group has no members"
    expected_key = str(judgment_key or "").strip()
    source_pins: set[str] = set()
    saw_schema_two = False
    saw_legacy_association = False
    has_top_level_member = False
    semantic_dimension_ids: set[str] = set()
    nested: dict[str, dict[str, str]] = {}
    corrected_target_maps: list[dict[str, str]] = []

    try:
        from scripts.source_record_projection_contract import (
            SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELD,
            SOURCE_EQUALITY_PARTITION_ASSOCIATION_FIELD,
            SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD,
            SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD,
            SOURCE_MODEL_DERIVATION_ANALYSIS_FIELD,
            SOURCE_MODEL_DERIVATION_ASSOCIATION_FIELD,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        from source_record_projection_contract import (
            SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELD,
            SOURCE_EQUALITY_PARTITION_ASSOCIATION_FIELD,
            SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD,
            SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD,
            SOURCE_MODEL_DERIVATION_ANALYSIS_FIELD,
            SOURCE_MODEL_DERIVATION_ASSOCIATION_FIELD,
        )

    for index, member in enumerate(raw_members):
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, f"current raw group member {index} is malformed"
        section, item = member
        item_key = str(item.get("judgment_key") or "").strip()
        if not item_key or (expected_key and item_key != expected_key):
            return None, f"current raw group member {index} does not match its response key"

        association: Mapping[str, object] | None = None
        association_field = ""
        if section == "semantic_model_items":
            association, has_association = _semantic_source_association(item)
            if has_association:
                association_field = "semantic source association"
            raw_dimensions = item.get("dimensions")
            if not isinstance(raw_dimensions, list):
                return None, f"current semantic-model member {index} dimensions are not a list"
            # A source-less semantic model item can be an expanded-surface
            # review obligation without any source-association transport to
            # project.  Preserve it untouched here; the semantic review gate
            # separately reports missing dimensions if that item needs a
            # substantive response.  Once a schema-2 association exists,
            # dimensions are mandatory because each current raw pin must be
            # assigned to an exact generated dimension rather than guessed
            # from a name.
            if not raw_dimensions:
                if association is None:
                    continue
                _pin, schema_two, association_error = (
                    _source_record_projection_association_pin(
                        association, field=association_field
                    )
                )
                if association_error:
                    return None, association_error
                if schema_two:
                    return None, f"current semantic-model member {index} has no dimensions"
                saw_legacy_association = True
                continue
            for dimension_index, raw_dimension in enumerate(raw_dimensions):
                if not isinstance(raw_dimension, Mapping):
                    return (
                        None,
                        f"current semantic-model member {index} dimension {dimension_index} is not an object",
                    )
                dimension = str(raw_dimension.get("id") or "").strip()
                if not dimension:
                    return (
                        None,
                        f"current semantic-model member {index} dimension {dimension_index} has no id",
                    )
                semantic_dimension_ids.add(dimension)
                for nested_association_field, analysis_field in (
                    (
                        SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD,
                        SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD,
                    ),
                    (
                        SOURCE_EQUALITY_PARTITION_ASSOCIATION_FIELD,
                        SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELD,
                    ),
                    (
                        SOURCE_MODEL_DERIVATION_ASSOCIATION_FIELD,
                        SOURCE_MODEL_DERIVATION_ANALYSIS_FIELD,
                    ),
                ):
                    nested_pin, nested_error = _source_record_nested_projection_pin(
                        raw_dimension, association_field=nested_association_field
                    )
                    if nested_error:
                        return (
                            None,
                            f"current semantic-model dimension `{dimension}` {nested_error}",
                        )
                    if not nested_pin:
                        continue
                    existing = nested.setdefault(dimension, {}).get(analysis_field)
                    if existing is not None and existing != nested_pin:
                        return (
                            None,
                            f"current semantic-model dimension `{dimension}` has conflicting {analysis_field} association pins",
                        )
                    nested[dimension][analysis_field] = nested_pin
        elif section in {
            "theorem_facing_input_items",
            "boundary_input_items",
            "conclusion_dependency_items",
            "type_valued_certificate_result_items",
        }:
            has_top_level_member = True
            raw_association = item.get(SOURCE_CONTRACT_ASSOCIATION_FIELD)
            if raw_association is not None and not isinstance(raw_association, Mapping):
                return None, f"current {section} member {index} source_contract_association is not an object"
            association = raw_association if isinstance(raw_association, Mapping) else None
            if association is not None:
                association_field = SOURCE_CONTRACT_ASSOCIATION_FIELD
        elif section == "recursive_field_items":
            # Mapless recursive groups have no source association projection.
            # They remain byte-for-byte response-compatible with prior reviews.
            continue
        else:
            return None, f"current raw group member {index} has unsupported section `{section}`"

        if association is None:
            continue
        pin, schema_two, association_error = _source_record_projection_association_pin(
            association, field=association_field
        )
        if association_error:
            return None, association_error
        if schema_two:
            saw_schema_two = True
            source_pins.add(pin)
            corrected_targets, corrected_target_error = (
                _source_record_projection_corrected_target_digests(
                    association, statement_map, field=association_field
                )
            )
            if corrected_target_error:
                return None, corrected_target_error
            corrected_target_maps.append(corrected_targets)
        else:
            saw_legacy_association = True

    if saw_schema_two and saw_legacy_association:
        return None, "current raw group mixes schema-2 and legacy source associations"
    if len(source_pins) > 1:
        return None, "current raw group has conflicting source association pins"
    pin = next(iter(source_pins), "")
    corrected_target_map: dict[str, str] = {}
    unique_corrected_target_maps = {
        tuple(sorted(values.items())) for values in corrected_target_maps
    }
    if len(unique_corrected_target_maps) > 1:
        return None, "current raw group has conflicting corrected-target digest maps"
    if unique_corrected_target_maps:
        corrected_target_map = dict(next(iter(unique_corrected_target_maps)))
    return (
        SourceRecordResponseAssociationProjection(
            top_level_semantic_association_sha256=(
                pin if pin and has_top_level_member else ""
            ),
            semantic_dimension_association_sha256=(
                {dimension: pin for dimension in sorted(semantic_dimension_ids)}
                if pin
                else {}
            ),
            nested_dimension_association_sha256={
                dimension: dict(sorted(analysis_pins.items()))
                for dimension, analysis_pins in sorted(nested.items())
            },
            top_level_corrected_target_sha256_by_source_semantic_sha256=(
                corrected_target_map if corrected_target_map and has_top_level_member else {}
            ),
            semantic_dimension_corrected_target_sha256_by_source_semantic_sha256=(
                {
                    dimension: dict(corrected_target_map)
                    for dimension in sorted(semantic_dimension_ids)
                }
                if corrected_target_map
                else {}
            ),
        ),
        "",
    )


def _source_record_response_pin_error(
    target: Mapping[str, object],
    *,
    expected: str,
    path: str,
    reject_existing: bool,
    replace_generated_credentials: bool,
) -> str:
    """Reject reviewer-supplied or conflicting generated association pins.

    ``replace_generated_credentials`` is reserved for a materializer that is
    already bound to an explicit current semantic attestation.  In that one
    path, this generated field is transport rather than reviewer content, so
    the current raw association replaces a stale historical credential.  The
    default remains fail-closed for ordinary projection and validation.
    """

    if SEMANTIC_ASSOCIATION_SHA256_FIELD not in target:
        return ""
    if reject_existing:
        return f"{path} must not carry a reviewer-supplied {SEMANTIC_ASSOCIATION_SHA256_FIELD}"
    if replace_generated_credentials:
        return ""
    supplied = str(target.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or "").strip().lower()
    if supplied != expected:
        return f"{path}.{SEMANTIC_ASSOCIATION_SHA256_FIELD} conflicts with the current raw association pin"
    return ""


def _source_record_response_corrected_target_map_error(
    target: Mapping[str, object],
    *,
    expected: Mapping[str, str],
    path: str,
    reject_existing: bool,
    replace_generated_credentials: bool,
) -> str:
    """Reject a reviewer-selected or conflicting corrected-target digest map.

    As with association pins, a current-attestation materializer may replace
    this generated source-map transport.  Normal callers continue to reject a
    conflicting serialized map rather than silently accepting it.
    """

    if _TARGET_SEMANTIC_SHA256_FIELD not in target:
        return ""
    if reject_existing:
        return (
            f"{path} must not carry a reviewer-supplied "
            f"{_TARGET_SEMANTIC_SHA256_FIELD}"
        )
    if replace_generated_credentials:
        return ""
    supplied_raw = target.get(_TARGET_SEMANTIC_SHA256_FIELD)
    if not isinstance(supplied_raw, Mapping):
        return f"{path}.{_TARGET_SEMANTIC_SHA256_FIELD} conflicts with the current raw corrected-target map"
    supplied = {
        str(key).strip().lower(): str(value).strip().lower()
        for key, value in supplied_raw.items()
        if str(key).strip()
    }
    if supplied != dict(expected):
        return f"{path}.{_TARGET_SEMANTIC_SHA256_FIELD} conflicts with the current raw corrected-target map"
    return ""


def _response_uses_approved_corrected_target(response: Mapping[str, object]) -> bool:
    return (
        str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
        == "approved_corrected_target"
    )


def project_source_record_response_association_pins(
    raw_members: object,
    response: Mapping[str, object],
    *,
    judgment_key: object | None = None,
    reject_existing: bool = False,
    replace_generated_credentials: bool = False,
    statement_map: Mapping[str, object] | None = None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> tuple[dict[str, object] | None, str]:
    """Inject only raw-derived source pins into one current response.

    Existing matching pins are retained for authenticated historical and
    differential overlays.  A manual template passes ``reject_existing`` so a
    reviewer cannot claim a generated pin.  An explicitly attested current
    materializer may pass ``replace_generated_credentials`` to replace only
    stale generated association/target transport from exact current raw
    members; ordinary callers remain fail-closed by default.
    """

    if not isinstance(response, Mapping):
        return None, "response is not an object"
    if reject_existing and replace_generated_credentials:
        return (
            None,
            "reject_existing cannot be combined with replace_generated_credentials",
        )
    # A configured-assumption formalization regularity is deliberately not a
    # source association. Bind its separate structural ledger pin and stop:
    # normal association projection must never attach source-credit transport
    # fields to this non-credit classification.
    if response_claims_configured_assumption_formalization_regularity(response):
        regularity_projected, regularity_error = (
            project_configured_assumption_formalization_regularity_pin(
                raw_members,
                response,
                context=configured_assumption_formalization_regularity_context,
                reject_existing=reject_existing,
            )
        )
        if regularity_error or regularity_projected is None:
            return None, regularity_error or "could not project current formalization-regularity pin"
        return regularity_projected, ""
    projection, error = source_record_response_association_projection(
        raw_members, judgment_key=judgment_key, statement_map=statement_map
    )
    if error or projection is None:
        return None, error or "could not construct current raw association projection"
    if not projection.has_injections:
        return copy.deepcopy(dict(response)), ""

    projected = copy.deepcopy(dict(response))
    if reject_existing and _TARGET_SEMANTIC_SHA256_FIELD in projected:
        return (
            None,
            f"response must not carry a reviewer-supplied {_TARGET_SEMANTIC_SHA256_FIELD}",
        )
    if reject_existing:
        raw_review_dimensions = projected.get("semantic_model_dimensions")
        if isinstance(raw_review_dimensions, Mapping):
            for raw_dimension, raw_dimension_response in raw_review_dimensions.items():
                if (
                    isinstance(raw_dimension_response, Mapping)
                    and _TARGET_SEMANTIC_SHA256_FIELD in raw_dimension_response
                ):
                    return (
                        None,
                        "response.semantic_model_dimensions."
                        + str(raw_dimension)
                        + f" must not carry a reviewer-supplied {_TARGET_SEMANTIC_SHA256_FIELD}",
                    )
    if projection.top_level_semantic_association_sha256:
        if error := _source_record_response_pin_error(
            projected,
            expected=projection.top_level_semantic_association_sha256,
            path="response",
            reject_existing=reject_existing,
            replace_generated_credentials=replace_generated_credentials,
        ):
            return None, error
        projected[SEMANTIC_ASSOCIATION_SHA256_FIELD] = (
            projection.top_level_semantic_association_sha256
        )
    if (
        projection.top_level_corrected_target_sha256_by_source_semantic_sha256
        and _response_uses_approved_corrected_target(projected)
    ):
        expected_targets = (
            projection.top_level_corrected_target_sha256_by_source_semantic_sha256
        )
        if error := _source_record_response_corrected_target_map_error(
            projected,
            expected=expected_targets,
            path="response",
            reject_existing=reject_existing,
            replace_generated_credentials=replace_generated_credentials,
        ):
            return None, error
        projected[_TARGET_SEMANTIC_SHA256_FIELD] = dict(expected_targets)

    dimension_pins = projection.semantic_dimension_association_sha256
    nested_pins = projection.nested_dimension_association_sha256
    dimension_target_maps = (
        projection.semantic_dimension_corrected_target_sha256_by_source_semantic_sha256
    )
    if not dimension_pins and not nested_pins and not dimension_target_maps:
        return projected, ""
    raw_dimensions = projected.get("semantic_model_dimensions")
    if not isinstance(raw_dimensions, Mapping):
        return None, "response has no semantic_model_dimensions object for its current raw semantic group"
    dimensions = copy.deepcopy(dict(raw_dimensions))
    for dimension in sorted(
        set(dimension_pins) | set(nested_pins) | set(dimension_target_maps)
    ):
        raw_dimension_response = dimensions.get(dimension)
        if not isinstance(raw_dimension_response, Mapping):
            return None, f"response.semantic_model_dimensions.{dimension} is not an object"
        dimension_response = copy.deepcopy(dict(raw_dimension_response))
        if expected := dimension_pins.get(dimension):
            if error := _source_record_response_pin_error(
                dimension_response,
                expected=expected,
                path=f"response.semantic_model_dimensions.{dimension}",
                reject_existing=reject_existing,
                replace_generated_credentials=replace_generated_credentials,
            ):
                return None, error
            dimension_response[SEMANTIC_ASSOCIATION_SHA256_FIELD] = expected
        if expected_targets := dimension_target_maps.get(dimension):
            if _response_uses_approved_corrected_target(dimension_response):
                if error := _source_record_response_corrected_target_map_error(
                    dimension_response,
                    expected=expected_targets,
                    path=f"response.semantic_model_dimensions.{dimension}",
                    reject_existing=reject_existing,
                    replace_generated_credentials=replace_generated_credentials,
                ):
                    return None, error
                dimension_response[_TARGET_SEMANTIC_SHA256_FIELD] = dict(
                    expected_targets
                )
        for analysis_field, expected in sorted(nested_pins.get(dimension, {}).items()):
            raw_analysis = dimension_response.get(analysis_field)
            if not isinstance(raw_analysis, Mapping):
                return (
                    None,
                    f"response.semantic_model_dimensions.{dimension}.{analysis_field} is not an object",
                )
            analysis = copy.deepcopy(dict(raw_analysis))
            if error := _source_record_response_pin_error(
                analysis,
                expected=expected,
                path=(
                    f"response.semantic_model_dimensions.{dimension}.{analysis_field}"
                ),
                reject_existing=reject_existing,
                replace_generated_credentials=replace_generated_credentials,
            ):
                return None, error
            analysis[SEMANTIC_ASSOCIATION_SHA256_FIELD] = expected
            dimension_response[analysis_field] = analysis
        dimensions[dimension] = dimension_response
    projected["semantic_model_dimensions"] = dimensions
    return projected, ""


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _valid_sha256(value: object) -> str:
    digest = str(value or "").strip().lower()
    return digest if _SHA256_RE.fullmatch(digest) else ""


def _direct_source_status_fields(item: Mapping[str, object]) -> list[str]:
    """Return direct administrative fields eligible for this one rebind.

    The rebind is intentionally not a recursive metadata normalizer.  A
    nested ``source_status`` can be part of a corrected target or another
    source-semantic structure, so it remains in both projections and is
    protected by the complete current raw source-map item digest.
    """

    return [
        key
        for key in item
        if key == "source_status"
    ]


def _administrative_projection_association_structure_digest(
    association: Mapping[str, object],
) -> str:
    """Pin every association field except the three derived transport pins."""

    projected = copy.deepcopy(dict(association))
    projected.pop("association_sha256", None)
    projected.pop(SEMANTIC_ASSOCIATION_SHA256_FIELD, None)
    raw_identities = projected.get("source_item_identities")
    if isinstance(raw_identities, list):
        for raw_identity in raw_identities:
            if isinstance(raw_identity, dict):
                raw_identity.pop(SOURCE_SEMANTIC_SHA256_FIELD, None)
    return source_map_item_record_digest(projected)


def _schema_two_association_rebind(
    association: Mapping[str, object],
    statement_map: Mapping[str, object],
) -> tuple[dict[str, object] | None, dict[str, object] | None, str]:
    """Derive one exact direct-source-status transport rebind.

    The returned association has the same route, source locations, source-map
    item identities, declaration identity, signature, and contract structure
    as the raw association.  It changes only the direct-status-free semantic
    source hashes and the two association hashes derived from them.
    """

    if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
        return None, None, "association is not schema 2"
    if "source_item_semantic_sha256" in association:
        return (
            None,
            None,
            "association carries unsupported top-level source semantic transport metadata",
        )
    raw_identities = association.get("source_item_identities")
    if not isinstance(raw_identities, list) or not raw_identities:
        return None, None, "association has no source_item_identities"
    signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
    prior_semantic_digests: list[str] = []
    current_semantic_digests: list[str] = []
    identity_rebinds: list[dict[str, str]] = []
    rebound_identities: list[dict[str, object]] = []
    map_items, map_errors = _source_map_items(statement_map)
    if map_errors:
        return None, None, "; ".join(map_errors)

    changed = False
    for index, raw_identity in enumerate(raw_identities):
        if not isinstance(raw_identity, Mapping):
            return None, None, f"source_item_identities[{index}] is not an object"
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_location = _normalized_text(raw_identity.get("source_location"))
        source_map_digest = _valid_sha256(raw_identity.get("source_map_item_sha256"))
        prior_semantic_digest = _valid_sha256(
            raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD)
        )
        if not source_key or not source_location or not source_map_digest or not prior_semantic_digest:
            return (
                None,
                None,
                f"source_item_identities[{index}] lacks an exact source key, location, raw digest, or semantic digest",
            )
        source_item = map_items.get(source_key)
        if source_item is None:
            return None, None, f"source item `{source_key}` is absent from the current map"
        if _normalized_text(source_item.get("source_location")) != source_location:
            return (
                None,
                None,
                f"source item `{source_key}` no longer has the recorded source location",
            )
        if source_record_source_item_record_sha256(source_item) != source_map_digest:
            return (
                None,
                None,
                f"source item `{source_key}` no longer has the recorded raw source-map item digest",
            )
        current_semantic_digest = source_record_source_item_semantic_sha256(
            source_item, ""
        )
        legacy_status_included_digest = (
            legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                source_item, ""
            )
        )
        legacy_status_excluded_digest = (
            legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                source_item, ""
            )
        )
        transition_kind = "already_schema5_current"
        if prior_semantic_digest == current_semantic_digest:
            rebound_identity = copy.deepcopy(dict(raw_identity))
        else:
            direct_status_fields = _direct_source_status_fields(source_item)
            if len(direct_status_fields) != 1:
                return (
                    None,
                    None,
                    f"source item `{source_key}` is not an exact direct source_status projection transition",
                )
            if prior_semantic_digest == legacy_status_included_digest:
                transition_kind = _STATUS_INCLUDED_TO_EXCLUDED_TRANSITION
            elif prior_semantic_digest == legacy_status_excluded_digest:
                transition_kind = _STATUS_EXCLUDED_SCHEMA_ONLY_TRANSITION
            else:
                return (
                    None,
                    None,
                    f"source item `{source_key}` is not an exact schema-4 direct source_status projection transition",
                )
            if current_semantic_digest in {
                legacy_status_included_digest,
                legacy_status_excluded_digest,
            }:
                return (
                    None,
                    None,
                    f"source item `{source_key}` has no distinct schema-5 source semantic transition",
                )
            rebound_identity = copy.deepcopy(dict(raw_identity))
            rebound_identity[SOURCE_SEMANTIC_SHA256_FIELD] = current_semantic_digest
            changed = True
        prior_semantic_digests.append(prior_semantic_digest)
        current_semantic_digests.append(current_semantic_digest)
        identity_rebinds.append(
            {
                "source_key": source_key,
                "source_location": source_location,
                "source_map_item_sha256": source_map_digest,
                "prior_source_semantic_sha256": prior_semantic_digest,
                "rebound_source_semantic_sha256": current_semantic_digest,
                "transition_kind": transition_kind,
            }
        )
        rebound_identities.append(rebound_identity)

    if not changed:
        return None, None, "association has no eligible schema-4 direct source_status semantic identity"
    expected_prior_semantic_association = semantic_association_record_digest(
        prior_semantic_digests, signature
    )
    supplied_prior_semantic_association = _valid_sha256(
        association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
    )
    if (
        not expected_prior_semantic_association
        or supplied_prior_semantic_association != expected_prior_semantic_association
    ):
        return None, None, "association has a stale prior semantic association pin"
    if "association_sha256" in association and _valid_sha256(
        association.get("association_sha256")
    ) != source_contract_association_record_digest(association):
        return None, None, "association has a stale prior association_sha256"

    rebound = copy.deepcopy(dict(association))
    rebound["source_item_identities"] = rebound_identities
    rebound_semantic_association = semantic_association_record_digest(
        current_semantic_digests, signature
    )
    if not rebound_semantic_association:
        return None, None, "rebound semantic association pin is malformed or ambiguous"
    rebound[SEMANTIC_ASSOCIATION_SHA256_FIELD] = rebound_semantic_association
    if "association_sha256" in rebound:
        rebound["association_sha256"] = source_contract_association_record_digest(rebound)

    binding = {
        "prior_association_sha256": source_map_item_record_digest(association),
        "association_structure_sha256": _administrative_projection_association_structure_digest(
            association
        ),
        "rebound_association_sha256": source_map_item_record_digest(rebound),
        "prior_semantic_association_sha256": supplied_prior_semantic_association,
        "rebound_semantic_association_sha256": rebound_semantic_association,
        "source_identity_rebinds": sorted(
            identity_rebinds,
            key=lambda entry: (
                entry["source_key"],
                entry["source_map_item_sha256"],
            ),
        ),
    }
    return binding, rebound, ""


def _raw_schema_two_source_associations(
    raw_audit: Mapping[str, object],
) -> list[Mapping[str, object]]:
    """Return every target-disposition association emitted in a raw audit.

    These are generated provenance containers, selected by their artifact
    fields and schema rather than theorem, binder, source-map, or Lean names.
    """

    associations: list[Mapping[str, object]] = []
    seen: set[str] = set()
    for section, fields in (
        (
            "semantic_model_items",
            (
                "source_statement_association",
                "semantic_contract_source_association",
                "semantic_contract_group",
            ),
        ),
        (
            "boundary_input_items",
            (SOURCE_CONTRACT_ASSOCIATION_FIELD,),
        ),
        (
            "conclusion_dependency_items",
            (SOURCE_CONTRACT_ASSOCIATION_FIELD,),
        ),
    ):
        raw_items = raw_audit.get(section)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                continue
            for field in fields:
                association = raw_item.get(field)
                if not isinstance(association, Mapping):
                    continue
                if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
                    continue
                digest = source_map_item_record_digest(association)
                if digest in seen:
                    continue
                seen.add(digest)
                associations.append(association)
    return associations


def _legacy_recursive_route_rebind_error(
    raw_audit: Mapping[str, object], statement_map: Mapping[str, object]
) -> str:
    """Fail closed until recursive-field routes receive their own receipt form."""

    raw_items = raw_audit.get("recursive_field_items")
    if not isinstance(raw_items, list):
        return ""
    map_items, map_errors = _source_map_items(statement_map)
    if map_errors:
        return "; ".join(map_errors)
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            continue
        route = raw_item.get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD)
        if not isinstance(route, Mapping):
            continue
        identities = route.get("source_item_identities")
        if not isinstance(identities, list):
            continue
        for identity in identities:
            if not isinstance(identity, Mapping):
                continue
            source_key = str(identity.get("source_key") or "").strip()
            source_item = map_items.get(source_key)
            if source_item is None:
                continue
            supplied = _valid_sha256(identity.get(SOURCE_SEMANTIC_SHA256_FIELD))
            legacy_status_included = (
                legacy_source_item_coverage_sha256_before_direct_source_status_exclusion(
                    source_item, ""
                )
            )
            legacy_status_excluded = (
                legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                    source_item, ""
                )
            )
            current = source_item_coverage_sha256(source_item, "")
            if (
                supplied
                and supplied in {legacy_status_included, legacy_status_excluded}
                and supplied != current
            ):
                return (
                    "legacy direct source_status semantics occur in a recursive-field "
                    "route, which requires a dedicated recursive receipt rebind"
                )
    return ""


def _administrative_projection_rebind_entries(
    raw_audit: Mapping[str, object], statement_map: Mapping[str, object]
) -> tuple[list[dict[str, object]], dict[str, dict[str, object]], str]:
    """Derive the complete deterministic association rebind set."""

    if error := _legacy_recursive_route_rebind_error(raw_audit, statement_map):
        return [], {}, error
    bindings: list[dict[str, object]] = []
    rebound_by_prior_digest: dict[str, dict[str, object]] = {}
    for association in _raw_schema_two_source_associations(raw_audit):
        binding, rebound, error = _schema_two_association_rebind(
            association, statement_map
        )
        if error == "association has no eligible schema-4 direct source_status semantic identity":
            continue
        if error:
            return [], {}, error
        assert binding is not None and rebound is not None
        prior_digest = str(binding["prior_association_sha256"])
        if prior_digest in rebound_by_prior_digest:
            return [], {}, "raw audit has ambiguous duplicate association rebind identities"
        bindings.append(binding)
        rebound_by_prior_digest[prior_digest] = rebound
    if not bindings:
        return [], {}, "raw audit has no eligible schema-4 direct source_status projection rebinds"
    return (
        sorted(bindings, key=lambda entry: str(entry["prior_association_sha256"])),
        rebound_by_prior_digest,
        "",
    )


def administrative_projection_rebind_receipt_digest(raw: object) -> str:
    """Return the immutable digest of a rebind receipt excluding its self-pin."""

    payload: object = copy.deepcopy(raw)
    if isinstance(payload, dict):
        payload.pop("receipt_sha256", None)
    return source_map_item_record_digest(payload)


def build_administrative_projection_rebind(
    *,
    paper: str,
    raw_audit: Mapping[str, object],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, object],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
) -> tuple[dict[str, object] | None, str]:
    """Build a fully deterministic direct-status projection rebind receipt.

    This performs no Lean work and does not alter a raw audit or judgment
    sidecar.  It is valid only when every transformed association can be
    reconstructed from the exact current raw source-map item descriptor.
    """

    if not paper or str(raw_audit.get("paper") or "").strip() != paper:
        return None, "raw audit paper does not match the requested paper"
    raw_audit_digest = _valid_sha256(raw_audit.get("source_record_audit_sha256"))
    if not raw_audit_digest:
        return None, "raw audit lacks a valid source_record_audit_sha256"
    if not raw_audit_relative_path or not statement_map_relative_path:
        return None, "rebind receipt paths must be nonempty paper-relative paths"
    bindings, _rebound_by_prior_digest, error = _administrative_projection_rebind_entries(
        raw_audit, statement_map
    )
    if error:
        return None, error
    identity_transition_kinds = sorted(
        {
            str(identity.get("transition_kind") or "").strip()
            for binding in bindings
            for identity in binding.get("source_identity_rebinds") or []
            if isinstance(identity, Mapping)
            and str(identity.get("transition_kind") or "").strip()
            != "already_schema5_current"
        }
    )
    if not identity_transition_kinds:
        return None, "rebind receipt has no schema-4 source identity transition"
    receipt: dict[str, object] = {
        "schema": SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_SCHEMA,
        "artifact_kind": SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_POLICY_VERSION,
        "paper": paper,
        "raw_audit_relative_path": raw_audit_relative_path,
        "raw_audit_bytes_sha256": _sha256_bytes(raw_audit_bytes),
        "raw_source_record_audit_sha256": raw_audit_digest,
        "statement_map_relative_path": statement_map_relative_path,
        "statement_map_bytes_sha256": _sha256_bytes(statement_map_bytes),
        "projection_transition": {
            "kind": "source_item_coverage_schema4_to5_direct_source_status",
            "legacy_source_item_coverage_digest_schema": (
                LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            ),
            "current_source_item_coverage_digest_schema": (
                SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            ),
            "legacy_projection": "one of the receipt-bound schema-4 direct-source-status projections",
            "current_projection": "source-item-coverage-schema-5-without-direct-source-status",
            "permitted_direct_field": "source_status",
            "receipt_identity_transition_kinds": identity_transition_kinds,
        },
        "association_rebinds": bindings,
    }
    receipt["receipt_sha256"] = administrative_projection_rebind_receipt_digest(receipt)
    return receipt, ""


def validate_administrative_projection_rebind(
    receipt: object,
    *,
    paper: str,
    raw_audit: Mapping[str, object],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, object],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
) -> tuple[ValidatedAdministrativeProjectionRebind | None, str]:
    """Validate a complete rebind receipt against live raw/map bytes.

    Recomputing the expected receipt makes this an exact descriptor proof,
    not a claimed mapping from a legacy digest to a current digest.  Any raw
    audit, association, source map, source note, corrected target, route, or
    nested metadata change causes the receipt to fail closed.
    """

    if not isinstance(receipt, Mapping):
        return None, "administrative projection rebind is not a JSON object"
    supplied = copy.deepcopy(dict(receipt))
    supplied_digest = _valid_sha256(supplied.get("receipt_sha256"))
    if not supplied_digest or supplied_digest != administrative_projection_rebind_receipt_digest(
        supplied
    ):
        return None, "administrative projection rebind has a stale receipt_sha256"
    expected, error = build_administrative_projection_rebind(
        paper=paper,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_audit_bytes,
        raw_audit_relative_path=raw_audit_relative_path,
        statement_map=statement_map,
        statement_map_bytes=statement_map_bytes,
        statement_map_relative_path=statement_map_relative_path,
    )
    if error:
        return None, "administrative projection rebind cannot be reconstructed: " + error
    assert expected is not None
    if supplied != expected:
        return (
            None,
            "administrative projection rebind does not exactly match the current raw audit, "
            "raw source-map descriptors, and direct source_status projection transition",
        )
    bindings, rebound_by_prior_digest, error = _administrative_projection_rebind_entries(
        raw_audit, statement_map
    )
    if error:  # pragma: no cover - already checked by build above.
        return None, "administrative projection rebind cannot be reconstructed: " + error
    binding_by_prior_digest = {
        str(binding["prior_association_sha256"]): binding
        for binding in bindings
    }
    binding_by_rebound_digest = {
        str(binding["rebound_association_sha256"]): binding
        for binding in bindings
    }
    if (
        len(binding_by_prior_digest) != len(bindings)
        or len(binding_by_rebound_digest) != len(bindings)
        or any(
            source_map_item_record_digest(rebound_by_prior_digest[prior])
            != str(binding["rebound_association_sha256"])
            for prior, binding in binding_by_prior_digest.items()
        )
    ):
        return None, "administrative projection rebind has ambiguous association transport"
    return (
        ValidatedAdministrativeProjectionRebind(
            rebound_by_prior_digest,
            binding_by_prior_digest,
            binding_by_rebound_digest,
        ),
        "",
    )


def load_administrative_projection_rebind_context(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit_path: Path,
    raw_audit: Mapping[str, object],
    statement_map_path: Path,
    statement_map: Mapping[str, object] | None,
    receipt_path: Path | None = None,
    receipt_bytes_override: bytes | None | object = _BYTE_OVERRIDE_UNSET,
    raw_audit_bytes_override: bytes | None | object = _BYTE_OVERRIDE_UNSET,
    statement_map_bytes_override: bytes | None | object = _BYTE_OVERRIDE_UNSET,
) -> tuple[ValidatedAdministrativeProjectionRebind | None, Path | None, str]:
    """Load one exact paper-local administrative projection receipt.

    This is the shared path-oriented loader for consumers that do not need a
    status-file configuration.  A caller may choose a configured receipt path,
    but the default is the canonical paper-local sidecar.  The receipt is
    reconstructed from the exact raw-audit and statement-map *bytes* supplied
    by the caller, so it cannot turn a source-status label, source note,
    corrected target, route, nested metadata field, or unrelated raw audit
    into an administrative change.

    A missing optional receipt is not an error: callers then run their normal
    current validation.  A present but invalid receipt returns an error and
    must never be treated as a fallback permission.
    """

    canonical_receipt_path = (
        receipt_path
        if receipt_path is not None
        else paper_dir / "audit" / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
    )
    if not paper or paper_dir.name != paper:
        return (
            None,
            canonical_receipt_path,
            "paper identifier does not match the receipt's paper directory",
        )
    raw_relative, raw_path_error = _paper_local_relative_path(
        raw_audit_path, paper_dir, label="raw-audit path"
    )
    if raw_path_error:
        return None, canonical_receipt_path, raw_path_error
    map_relative, map_path_error = _paper_local_relative_path(
        statement_map_path, paper_dir, label="statement-map path"
    )
    if map_path_error:
        return None, canonical_receipt_path, map_path_error
    _receipt_relative, receipt_path_error = _paper_local_relative_path(
        canonical_receipt_path, paper_dir, label="receipt path"
    )
    if receipt_path_error:
        return None, canonical_receipt_path, receipt_path_error
    using_overrides = receipt_bytes_override is not _BYTE_OVERRIDE_UNSET
    if using_overrides:
        if receipt_bytes_override is None:
            return None, canonical_receipt_path, ""
        if not isinstance(receipt_bytes_override, bytes):
            return None, canonical_receipt_path, "invalid exact receipt bytes"
        if not isinstance(raw_audit_bytes_override, bytes):
            return None, canonical_receipt_path, "invalid exact raw-audit bytes"
        if not isinstance(statement_map_bytes_override, bytes):
            return None, canonical_receipt_path, "invalid exact statement-map bytes"
        receipt_bytes = receipt_bytes_override
        raw_bytes = raw_audit_bytes_override
        map_bytes = statement_map_bytes_override
    else:
        if not canonical_receipt_path.exists():
            return None, canonical_receipt_path, ""
        try:
            receipt_bytes = canonical_receipt_path.read_bytes()
            raw_bytes = raw_audit_path.read_bytes()
            map_bytes = statement_map_path.read_bytes()
        except OSError as exc:
            return (
                None,
                canonical_receipt_path,
                "could not load current rebind inputs: " + str(exc),
            )
    if not isinstance(statement_map, Mapping):
        return (
            None,
            canonical_receipt_path,
            "current paper_statement_map.json is missing or invalid",
        )
    try:
        receipt = json.loads(receipt_bytes)
        raw_from_bytes = json.loads(raw_bytes)
        map_from_bytes = json.loads(map_bytes)
    except json.JSONDecodeError as exc:
        return (
            None,
            canonical_receipt_path,
            "could not load current rebind inputs: " + str(exc),
        )
    if not isinstance(receipt, Mapping):
        return (
            None,
            canonical_receipt_path,
            "administrative projection rebind is missing or invalid JSON",
        )
    if raw_from_bytes != raw_audit or map_from_bytes != statement_map:
        return (
            None,
            canonical_receipt_path,
            "current rebind inputs changed while loading evidence",
        )
    context, error = validate_administrative_projection_rebind(
        receipt,
        paper=paper,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_bytes,
        raw_audit_relative_path=raw_relative,
        statement_map=statement_map,
        statement_map_bytes=map_bytes,
        statement_map_relative_path=map_relative,
    )
    return context, canonical_receipt_path, error


def _rebound_association_and_binding(
    association: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> tuple[Mapping[str, object], Mapping[str, object] | None]:
    """Return the receipt-derived association only for an exact raw match."""

    if administrative_projection_rebind is None:
        return association, None
    prior_digest = source_map_item_record_digest(association)
    rebound = administrative_projection_rebind.association_rebinds.get(prior_digest)
    if isinstance(rebound, Mapping):
        binding = administrative_projection_rebind.association_bindings.get(
            prior_digest
        )
        return rebound, binding if isinstance(binding, Mapping) else None
    # A fresh raw audit may already carry the exact receipt-derived schema-5
    # association.  Its old human response can be transported only when the
    # full association record equals that deterministic rebound, never merely
    # because a source semantic digest looks similar.
    binding = administrative_projection_rebind.rebound_association_bindings.get(
        prior_digest
    )
    return association, binding if isinstance(binding, Mapping) else None


def administrative_projection_rebound_association(
    association: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> Mapping[str, object]:
    """Return only the exact receipt-derived current association projection.

    This is deliberately a narrow projection helper for semantic consumers
    such as differential reuse.  It never identifies an association by a
    function, theorem, source key, or hash fragment; the typed context can
    replace it only after the receipt validator bound its complete raw record.
    """

    rebound, _binding = _rebound_association_and_binding(
        association, administrative_projection_rebind
    )
    return rebound


def administrative_projection_rebound_response(
    response: Mapping[str, object],
    association: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> Mapping[str, object]:
    """Transport a response only through the exact association receipt.

    The response is copied only when its association is one of the complete
    receipt-bound records.  In particular, a matching source key, declaration
    spelling, or individual legacy digest cannot cause a response pin to move.
    """

    _rebound, binding = _rebound_association_and_binding(
        association, administrative_projection_rebind
    )
    return _rebound_response_transport(response, binding)


def _rebound_response_transport(
    response: Mapping[str, object], binding: Mapping[str, object] | None
) -> Mapping[str, object]:
    """Translate only receipt-proved semantic association transport fields."""

    if binding is None:
        return response
    rebound = copy.deepcopy(dict(response))
    prior_association = str(
        binding.get("prior_semantic_association_sha256") or ""
    ).strip().lower()
    current_association = str(
        binding.get("rebound_semantic_association_sha256") or ""
    ).strip().lower()
    if rebound.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) == prior_association:
        rebound[SEMANTIC_ASSOCIATION_SHA256_FIELD] = current_association

    raw_targets = rebound.get(_TARGET_SEMANTIC_SHA256_FIELD)
    if isinstance(raw_targets, Mapping):
        targets = dict(raw_targets)
        for entry in binding.get("source_identity_rebinds") or []:
            if not isinstance(entry, Mapping):
                continue
            prior = str(entry.get("prior_source_semantic_sha256") or "").strip().lower()
            current = str(entry.get("rebound_source_semantic_sha256") or "").strip().lower()
            if prior != current and prior in targets and current not in targets:
                targets[current] = targets.pop(prior)
        rebound[_TARGET_SEMANTIC_SHA256_FIELD] = targets
    return rebound


def corrected_target_record_digest(raw: object) -> str:
    """Return the digest of a structured corrected-target record.

    This mirrors the corrected-target route's digest convention but is kept in
    this dependency-free module so both audit entry points validate the same
    immutable target identity.
    """

    return _shared_corrected_target_record_digest(raw)


def model_convention_record_digest(raw: object) -> str:
    """Return the complete stable digest for one source-proof convention.

    This is the route-level identity.  In particular, it retains an optional
    ``recursive_field_source_scope`` because a field route must become stale
    if its exact authorizing scope is changed or removed.
    """

    encoded = json.dumps(
        raw,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def model_convention_semantic_digest(raw: object) -> str:
    """Return the mathematical-model identity of one source convention.

    A recursive-field scope is audit routing metadata: it selects which
    already-generated structural field may inherit a source route, but does
    not alter the source convention's mathematical meaning.  Excluding that
    one field lets an unchanged semantic-model review remain reusable when a
    closeout adds or adjusts a field-level receipt.  The route itself remains
    protected by :func:`model_convention_record_digest` and its own exact
    field-scope digest, so this is not a route-authority relaxation.
    """

    if isinstance(raw, Mapping):
        raw = {
            key: value
            for key, value in raw.items()
            if key != "recursive_field_source_scope"
        }
    return model_convention_record_digest(raw)


def recursive_field_parent_route_record_digest(raw: object) -> str:
    """Return the order-preserving digest for a recursive-field route receipt.

    Field-chain and permitted-classification order are part of the declared
    scope.  Unlike the ordinary source-map digest, do not sort lists here: an
    ancestor chain is a path, not an unordered inventory.
    """

    payload: object = dict(raw) if isinstance(raw, Mapping) else raw
    if isinstance(payload, dict):
        payload.pop("association_sha256", None)
    encoded = json.dumps(
        payload,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def recursive_field_source_scope_record_digest(raw: object) -> str:
    """Return the ordered identity of one declared recursive field scope.

    The raw-audit producer and the closeout consumer both need this narrow
    encoding.  Its list order is intentional: the field chain is a structural
    path, not an unordered inventory.  A route is accepted only after this
    digest identifies one *current* ledger entry.
    """

    encoded = json.dumps(
        raw,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _recursive_field_source_locator_spans(
    locator: object,
) -> list[tuple[str, int, int]] | None:
    """Parse a complete semicolon-separated source locator into line spans."""

    if not isinstance(locator, str) or not locator.strip():
        return None
    matches = list(_RECURSIVE_FIELD_SOURCE_FILE_LINE_RE.finditer(locator))
    if not matches:
        return None
    remainder = _RECURSIVE_FIELD_SOURCE_FILE_LINE_RE.sub("", locator)
    if re.sub(r"[\s;,]+", "", remainder):
        return None
    spans: list[tuple[str, int, int]] = []
    for match in matches:
        path = str(match.group("path") or "").strip()
        try:
            start = int(str(match.group("start") or ""))
            end = int(str(match.group("end") or match.group("start") or ""))
        except ValueError:
            return None
        if not path or start <= 0 or end < start:
            return None
        spans.append((path, start, end))
    return spans


def recursive_field_scope_locator_anchor_error(
    scope_locator: object,
    *,
    source_item_locator: object,
    convention_locator: object,
) -> str:
    """Require a scoped field locator to remain in its declared anchor union.

    This is used both when generating a recursive route and when consuming it
    at closeout.  Exact route/ledger digests alone cannot establish that a
    self-consistent current scope still refers to the paper-facing source
    fragment.  A field scope may cite a source-item span or a span explicitly
    supplied by its selected convention, but nothing else.
    """

    scope_spans = _recursive_field_source_locator_spans(scope_locator)
    convention_spans = _recursive_field_source_locator_spans(convention_locator)
    source_item_spans = _recursive_field_source_locator_spans(source_item_locator)
    if scope_spans is None:
        return "has an unparsable exact field-scope source_locator"
    if convention_spans is None:
        return "has an unparsable selected convention source_locator"
    if source_item_spans is None:
        return "has a selected source item without an exact parsable source_location"
    allowed = convention_spans + source_item_spans
    for path, start, end in scope_spans:
        if not any(
            path == allowed_path and allowed_start <= start and end <= allowed_end
            for allowed_path, allowed_start, allowed_end in allowed
        ):
            return (
                "source_locator span "
                f"`{path}:{start}-{end}` is outside the selected source item and "
                "model-convention anchors"
            )
    return ""


def _normalized_text(value: object) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def _unique_string_list(value: object, *, field: str) -> tuple[list[str], list[str]]:
    """Return a nonempty unique string list and structural diagnostics."""

    if not isinstance(value, list):
        return [], [f"{field} must be a nonempty list of unique strings"]
    values = [entry.strip() for entry in value if isinstance(entry, str) and entry.strip()]
    if len(values) != len(value) or not values or len(set(values)) != len(values):
        return [], [f"{field} must be a nonempty list of unique strings"]
    return values, []


def _semantic_source_association(
    item: Mapping[str, object],
) -> tuple[Mapping[str, object] | None, bool]:
    """Return the generated source association used by a semantic item.

    The generator uses either an individual direct/Spec association, an exact
    direct/Spec group, or a source-presentation-selected direct statement
    association. All are generated provenance containers; none is inferred
    from a row, declaration suffix, or source-map key.
    """

    association = item.get(SOURCE_ASSUMPTION_ASSOCIATION_FIELD)
    if isinstance(association, Mapping):
        return association, True
    association = item.get(STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD)
    if isinstance(association, Mapping):
        return association, True
    association = item.get("source_statement_association")
    if isinstance(association, Mapping):
        return association, True
    association = item.get("semantic_contract_source_association")
    if isinstance(association, Mapping):
        return association, True
    association = item.get("semantic_contract_group")
    if isinstance(association, Mapping):
        return association, True
    association = item.get(SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD)
    if isinstance(association, Mapping):
        # Claim-atom routes are source-first generated provenance, not a
        # declaration-name lookup.  They predate the schema-2 response-pin
        # convention, so derive that pin only from their exact current source
        # identities and reviewed elaborated signature.  A malformed route is
        # still returned as a schema-2-shaped association with missing pins;
        # downstream validation then fails closed rather than silently treating
        # it as an unassociated semantic item.
        derived: dict[str, object] = {
            "schema": SEMANTIC_ASSOCIATION_SCHEMA,
            "association_origin": association.get("association_origin"),
            "role": association.get("role"),
            "reviewed_declaration_identity": association.get(
                "reviewed_declaration_identity"
            ),
            REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD: association.get(
                REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD
            ),
            "source_item_identities": association.get("source_item_identities"),
        }
        valid_route = (
            association.get("schema") == 1
            and str(association.get("association_origin") or "").strip()
            == SOURCE_CLAIM_ATOM_ROUTE_ORIGIN
            and str(association.get("role") or "").strip()
            == SOURCE_CLAIM_ATOM_ROUTE_ROLE
        )
        identities = association.get("source_item_identities")
        signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
        semantic_digests: list[str] = []
        if valid_route and isinstance(identities, list) and isinstance(signature, Mapping):
            for identity in identities:
                if not isinstance(identity, Mapping):
                    semantic_digests = []
                    break
                digest = str(
                    identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(digest):
                    semantic_digests = []
                    break
                semantic_digests.append(digest)
            if semantic_digests and len(set(semantic_digests)) == len(semantic_digests):
                derived[SEMANTIC_ASSOCIATION_SHA256_FIELD] = (
                    semantic_association_record_digest(semantic_digests, signature)
                )
        return derived, True
    return None, False


def _statement_source_component_association_errors(
    association: Mapping[str, object],
) -> tuple[Mapping[str, object] | None, list[str]]:
    """Validate the name-free clause identity inside a component association."""

    errors: list[str] = []
    if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
        errors.append(
            "generated statement source-component association must use schema 2"
        )
    if (
        str(association.get("association_origin") or "").strip()
        != STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
    ):
        errors.append("generated statement source-component association has an invalid origin")
    if (
        str(association.get("role") or "").strip()
        != STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    ):
        errors.append("generated statement source-component association has an invalid role")
    component = association.get(STATEMENT_SOURCE_COMPONENT_IDENTITY_FIELD)
    if not isinstance(component, Mapping):
        return None, errors + [
            "generated statement source-component association has no component identity"
        ]
    if component.get("schema") != STATEMENT_SOURCE_COMPONENT_IDENTITY_SCHEMA:
        errors.append("generated statement source-component identity has an invalid schema")
    for field in (
        "source_component_semantic_sha256",
        "source_statement_sha256",
        "source_anchor_quote_identity_sha256",
        "source_target_sha256",
        "source_definition_partition_sha256",
        "source_definition_component_sha256",
        "source_component_anchor_sha256",
        "statement_manifest_structure_sha256",
        "statement_semantic_dependency_sha256",
        "statement_review_validator_identity_sha256",
        "statement_review_protocol_sha256",
        "statement_source_route_semantic_sha256",
    ):
        if not _SHA256_RE.fullmatch(
            str(component.get(field) or "").strip().lower()
        ):
            errors.append(
                "generated statement source-component identity has no valid " + field
            )
    if component.get("statement_obligation_ledger_validated") is not True:
        errors.append(
            "generated statement source-component identity lacks a complete obligation-ledger receipt"
        )
    if component.get("statement_source_definition_semantics_validated") is not True:
        errors.append(
            "generated statement source-component identity lacks a source-definition semantics receipt"
        )
    component_disposition = component.get("source_target_disposition")
    if not isinstance(component_disposition, Mapping) or str(
        component_disposition.get("kind") or ""
    ).strip() != "ordinary_or_convention":
        errors.append(
            "generated statement source-component identity is outside the current "
            "ordinary/convention target contract"
        )
    signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
    signature_digest = (
        str(signature.get("elaborated_signature_sha256") or "").strip().lower()
        if isinstance(signature, Mapping)
        else ""
    )
    expected_component_pin = (
        source_map_item_record_digest(
            {
                "schema": STATEMENT_SOURCE_COMPONENT_IDENTITY_SCHEMA,
                "source_definition_component_semantic_identity": dict(component),
                "elaborated_signature_sha256": signature_digest,
            }
        )
        if _SHA256_RE.fullmatch(signature_digest)
        else ""
    )
    supplied_component_pin = str(
        association.get(STATEMENT_SOURCE_COMPONENT_SEMANTIC_ASSOCIATION_FIELD)
        or ""
    ).strip().lower()
    if not expected_component_pin or supplied_component_pin != expected_component_pin:
        errors.append(
            "generated statement source-component semantic pin is missing or stale"
        )
    if (
        str(association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or "")
        .strip()
        .lower()
        != supplied_component_pin
    ):
        errors.append(
            "generated statement source-component response pin does not equal its "
            "component semantic discriminator"
        )
    raw_parent_identities = association.get("source_item_identities")
    parent_digests: list[str] = []
    if isinstance(raw_parent_identities, list):
        parent_digests = [
            str(identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "").strip().lower()
            for identity in raw_parent_identities
            if isinstance(identity, Mapping)
        ]
    expected_parent_pin = semantic_association_record_digest(
        parent_digests, signature
    )
    if (
        not expected_parent_pin
        or str(association.get("parent_semantic_association_sha256") or "")
        .strip()
        .lower()
        != expected_parent_pin
    ):
        errors.append(
            "generated statement source-component parent association pin is missing or stale"
        )
    supplied_full_pin = str(association.get("association_sha256") or "").strip().lower()
    if supplied_full_pin != source_contract_association_record_digest(association):
        errors.append(
            "generated statement source-component full association pin is missing or stale"
        )
    convention_pins = component.get("source_model_convention_pins")
    if convention_pins is not None:
        if not isinstance(convention_pins, Mapping):
            errors.append(
                "generated statement source-component convention pins are not an object"
            )
        else:
            ids = convention_pins.get("model_convention_ids")
            digests = convention_pins.get("record_sha256_by_id")
            if (
                convention_pins.get("schema") != 2
                or not isinstance(ids, list)
                or not ids
                or len(ids) != len(set(str(value) for value in ids))
                or not isinstance(digests, Mapping)
                or set(str(value) for value in ids) != set(str(key) for key in digests)
                or any(
                    not _SHA256_RE.fullmatch(str(value or "").strip().lower())
                    for value in digests.values()
                )
            ):
                errors.append(
                    "generated statement source-component convention pins are malformed"
                )
    return component, errors


def statement_source_component_effective_semantic_pin(
    association: Mapping[str, object],
) -> tuple[str, str]:
    """Return the validated component-scoped response/currentness pin."""

    _component, errors = _statement_source_component_association_errors(association)
    if errors:
        return "", "; ".join(errors)
    pin = str(
        association.get(STATEMENT_SOURCE_COMPONENT_SEMANTIC_ASSOCIATION_FIELD)
        or ""
    ).strip().lower()
    return (pin, "") if _SHA256_RE.fullmatch(pin) else (
        "",
        "statement source-component association has no effective semantic pin",
    )


def statement_source_review_semantic_association_digest(
    review_identity: Mapping[str, object],
    source_identities: object,
    reviewed_signature_identity: object,
) -> str:
    """Bind a whole-definition v10 review without using route names as semantics."""

    if not isinstance(source_identities, list) or not isinstance(
        reviewed_signature_identity, Mapping
    ):
        return ""
    signature_digest = str(
        reviewed_signature_identity.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    source_digests = sorted(
        str(identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "").strip().lower()
        for identity in source_identities
        if isinstance(identity, Mapping)
    )
    if (
        not _SHA256_RE.fullmatch(signature_digest)
        or len(source_digests) != len(source_identities)
        or not source_digests
        or len(source_digests) != len(set(source_digests))
        or any(not _SHA256_RE.fullmatch(digest) for digest in source_digests)
    ):
        return ""
    return source_map_item_record_digest(
        {
            "schema": SEMANTIC_ASSOCIATION_SCHEMA,
            STATEMENT_SOURCE_REVIEW_IDENTITY_FIELD: dict(review_identity),
            "source_item_semantic_sha256": source_digests,
            "elaborated_signature_sha256": signature_digest,
        }
    )


def _statement_source_review_association_errors(
    association: Mapping[str, object],
) -> list[str]:
    """Validate a current, content-pinned whole-definition review route."""

    errors: list[str] = []
    if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
        errors.append("statement source-review association must use schema 2")
    if (
        str(association.get("association_origin") or "").strip()
        != STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
    ):
        errors.append("statement source-review association has an invalid origin")
    if (
        str(association.get("role") or "").strip()
        != STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        errors.append("statement source-review association has an invalid role")

    declaration = association.get("reviewed_declaration_identity")
    signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
    declaration_name = (
        str(declaration.get("qualified_declaration") or "").strip()
        if isinstance(declaration, Mapping)
        else ""
    )
    declaration_sha = (
        str(declaration.get("declaration_sha256") or "").strip().lower()
        if isinstance(declaration, Mapping)
        else ""
    )
    signature_name = (
        str(signature.get("qualified_declaration") or "").strip()
        if isinstance(signature, Mapping)
        else ""
    )
    signature_sha = (
        str(signature.get("elaborated_signature_sha256") or "").strip().lower()
        if isinstance(signature, Mapping)
        else ""
    )
    if (
        not declaration_name
        or not _SHA256_RE.fullmatch(declaration_sha)
        or signature_name != declaration_name
        or not _SHA256_RE.fullmatch(signature_sha)
    ):
        errors.append(
            "statement source-review association lacks an exact declaration/signature identity"
        )

    raw_source_identities = association.get("source_item_identities")
    source_identities = (
        raw_source_identities if isinstance(raw_source_identities, list) else []
    )
    source_semantic_digests: list[str] = []
    for index, raw_identity in enumerate(source_identities):
        if not isinstance(raw_identity, Mapping):
            errors.append(
                f"statement source-review source_item_identities[{index}] is malformed"
            )
            continue
        source_kind = str(raw_identity.get("source_kind") or "").strip().lower()
        source_semantic_sha = str(
            raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
        ).strip().lower()
        source_map_sha = str(
            raw_identity.get("source_map_item_sha256") or ""
        ).strip().lower()
        if source_kind not in SOURCE_DOMAIN_PRESENTATION_KINDS:
            errors.append(
                "statement source-review association may cite only definition, predicate, or model vocabulary"
            )
        if (
            not _SHA256_RE.fullmatch(source_semantic_sha)
            or not _SHA256_RE.fullmatch(source_map_sha)
        ):
            errors.append(
                f"statement source-review source_item_identities[{index}] lacks current content pins"
            )
        source_semantic_digests.append(source_semantic_sha)
    if (
        not source_identities
        or len(source_semantic_digests) != len(set(source_semantic_digests))
    ):
        errors.append(
            "statement source-review association has no unique source semantic identities"
        )

    review_identity = association.get(STATEMENT_SOURCE_REVIEW_IDENTITY_FIELD)
    if not isinstance(review_identity, Mapping) or review_identity.get(
        "schema"
    ) != STATEMENT_SOURCE_REVIEW_IDENTITY_SCHEMA:
        errors.append("statement source-review association has no review identity")
        review_identity = {}
    for field in (
        "declaration_content_sha256",
        "elaborated_signature_sha256",
        "manifest_structure_sha256",
        "semantic_dependency_sha256",
        "review_validator_identity_sha256",
        "review_protocol_sha256",
        "paper_statement_sha256",
        "tex_statement_sha256",
    ):
        if not _SHA256_RE.fullmatch(
            str(review_identity.get(field) or "").strip().lower()
        ):
            errors.append("statement source-review identity has no valid " + field)
    if str(review_identity.get("declaration_content_sha256") or "").strip().lower() != declaration_sha:
        errors.append(
            "statement source-review identity does not bind the reviewed declaration content"
        )
    if str(review_identity.get("elaborated_signature_sha256") or "").strip().lower() != signature_sha:
        errors.append(
            "statement source-review identity does not bind the elaborated signature"
        )

    raw_routes = review_identity.get("source_route_receipts")
    routes = raw_routes if isinstance(raw_routes, list) else []
    route_semantic_digests: list[str] = []
    route_parent_digests: list[str] = []
    for index, raw_route in enumerate(routes):
        if not isinstance(raw_route, Mapping):
            errors.append(
                f"statement source-review route receipt {index} is malformed"
            )
            continue
        route_semantic_sha = str(
            raw_route.get("route_semantic_sha256") or ""
        ).strip().lower()
        parent_semantic_sha = str(
            raw_route.get("source_parent_semantic_sha256") or ""
        ).strip().lower()
        source_reuse_pin = raw_route.get("source_reuse_pin")
        source_reuse_pin_sha = str(
            raw_route.get("source_reuse_pin_sha256") or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(route_semantic_sha):
            errors.append(
                f"statement source-review route receipt {index} has no semantic pin"
            )
        if not _SHA256_RE.fullmatch(parent_semantic_sha):
            errors.append(
                f"statement source-review route receipt {index} has no parent semantic pin"
            )
        if (
            not isinstance(source_reuse_pin, Mapping)
            or not _SHA256_RE.fullmatch(source_reuse_pin_sha)
            or source_reuse_pin_sha
            != source_map_item_record_digest(dict(source_reuse_pin))
        ):
            errors.append(
                f"statement source-review route receipt {index} has a stale source reuse pin"
            )
        route_semantic_digests.append(route_semantic_sha)
        route_parent_digests.append(parent_semantic_sha)
    if (
        not routes
        or len(route_semantic_digests) != len(set(route_semantic_digests))
        or set(route_parent_digests) != set(source_semantic_digests)
    ):
        errors.append(
            "statement source-review route receipts do not cover exactly their source parents"
        )

    expected_pin = statement_source_review_semantic_association_digest(
        review_identity, source_identities, signature
    )
    supplied_pin = str(
        association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or ""
    ).strip().lower()
    if not expected_pin or supplied_pin != expected_pin:
        errors.append(
            "statement source-review semantic association pin is missing or stale"
        )
    if str(association.get("association_sha256") or "").strip().lower() != source_contract_association_record_digest(association):
        errors.append("statement source-review full association pin is missing or stale")
    return errors


def statement_source_review_effective_semantic_pin(
    association: Mapping[str, object],
) -> tuple[str, str]:
    """Return the validated whole-definition review/currentness pin."""

    errors = _statement_source_review_association_errors(association)
    if errors:
        return "", "; ".join(errors)
    pin = str(
        association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or ""
    ).strip().lower()
    return (pin, "") if _SHA256_RE.fullmatch(pin) else (
        "",
        "statement source-review association has no effective semantic pin",
    )


def _explicit_source_identities(
    item: Mapping[str, object],
    *,
    association_override: Mapping[str, object] | None = None,
) -> tuple[list[dict[str, str]], list[str], bool]:
    """Read source-map identities from a generated association, if present.

    A direct/Spec group and an individual association are both generator-owned
    explicit identity containers.  If neither exists, the target-disposition
    lane is intentionally inapplicable; this preserves historical records and
    semantic rows that have no source-map route.
    """

    if association_override is not None:
        association = association_override
        has_association = True
    else:
        association, has_association = _semantic_source_association(item)
    if not has_association or association is None:
        return [], [], False
    identities: object | None = association.get("source_item_identities")

    if not isinstance(identities, list) or not identities:
        return [], ["generated semantic source association has no source_item_identities"], True

    parsed: list[dict[str, str]] = []
    errors: list[str] = []
    keys: set[str] = set()
    for index, raw_identity in enumerate(identities):
        if not isinstance(raw_identity, Mapping):
            errors.append(f"source_item_identities[{index}] must be an object")
            continue
        key = str(raw_identity.get("source_key") or "").strip()
        locator = _normalized_text(raw_identity.get("source_location"))
        source_map_digest = str(
            raw_identity.get("source_map_item_sha256") or ""
        ).strip().lower()
        source_semantic_digest = str(
            raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
        ).strip().lower()
        if not key:
            errors.append(f"source_item_identities[{index}].source_key is missing")
            continue
        if not locator:
            errors.append(f"source_item_identities[{index}].source_location is missing")
            continue
        if key in keys:
            errors.append(f"source_item_identities duplicates source-map key `{key}`")
            continue
        keys.add(key)
        parsed_identity = {"source_key": key, "source_location": locator}
        if source_map_digest:
            parsed_identity["source_map_item_sha256"] = source_map_digest
        if source_semantic_digest:
            parsed_identity[SOURCE_SEMANTIC_SHA256_FIELD] = source_semantic_digest
        parsed.append(parsed_identity)
    return parsed, errors, True


def _association_schema(
    association: Mapping[str, object], *, field: str, errors: list[str]
) -> int | None:
    """Validate the generated association schema without route fallbacks."""

    schema = association.get("schema")
    if (
        isinstance(schema, int)
        and not isinstance(schema, bool)
        and schema in {1, SEMANTIC_ASSOCIATION_SCHEMA}
    ):
        return schema
    errors.append(
        f"generated {field}.schema must be 1 (legacy exact route) or "
        f"{SEMANTIC_ASSOCIATION_SCHEMA} (semantic association pin)"
    )
    return None


def _schema_two_semantic_association_errors(
    association: Mapping[str, object],
    identities: list[dict[str, str]],
    *,
    reviewed_qualified_declaration: str,
    field: str,
) -> list[str]:
    """Validate a generated schema-2 semantic association pin.

    This validates the *current* generated association only.  A human response
    can subsequently reuse its semantic hash, but it cannot use an old map key
    or a claimed Lean route to manufacture a current pin.
    """

    errors: list[str] = []
    semantic_digests: list[str] = []
    for index, identity in enumerate(identities):
        digest = str(identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "").strip().lower()
        if not _SHA256_RE.fullmatch(digest):
            errors.append(
                f"generated {field}.source_item_identities[{index}]."
                f"{SOURCE_SEMANTIC_SHA256_FIELD} is missing or malformed"
            )
            continue
        semantic_digests.append(digest)
    if semantic_digests and len(set(semantic_digests)) != len(semantic_digests):
        errors.append(
            f"generated {field} has ambiguous duplicate source semantic SHA-256 identities"
        )

    signature = association.get(REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD)
    if not isinstance(signature, Mapping):
        errors.append(
            f"generated {field} lacks {REVIEWED_ELABORATED_SIGNATURE_IDENTITY_FIELD}"
        )
        return errors
    qualified = str(signature.get("qualified_declaration") or "").strip()
    signature_digest = str(
        signature.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    if not qualified or "." not in qualified:
        errors.append(
            f"generated {field} semantic association signature is not fully qualified"
        )
    if not _SHA256_RE.fullmatch(signature_digest):
        errors.append(
            f"generated {field} semantic association elaborated signature SHA-256 is missing or malformed"
        )
    if reviewed_qualified_declaration and qualified != reviewed_qualified_declaration:
        errors.append(
            f"generated {field} semantic association signature does not match the reviewed declaration"
        )

    is_statement_component = (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    )
    is_statement_review = (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    )
    is_assumption_review = (
        str(association.get("association_origin") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
        and str(association.get("role") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ROLE
    )
    if is_assumption_review:
        expected_pin, assumption_error = source_assumption_effective_semantic_pin(
            association
        )
        if assumption_error:
            errors.append(
                f"generated {field} authenticated assumption review is invalid: "
                + assumption_error
            )
    elif is_statement_component:
        expected_pin = str(
            association.get(STATEMENT_SOURCE_COMPONENT_SEMANTIC_ASSOCIATION_FIELD)
            or ""
        ).strip().lower()
    elif is_statement_review:
        expected_pin, review_error = statement_source_review_effective_semantic_pin(
            association
        )
        if review_error:
            errors.append(
                f"generated {field} authenticated statement review is invalid: "
                + review_error
            )
    else:
        expected_pin = semantic_association_record_digest(semantic_digests, signature)
    supplied_pin = str(
        association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or ""
    ).strip().lower()
    if not expected_pin or supplied_pin != expected_pin:
        errors.append(
            f"generated {field}.{SEMANTIC_ASSOCIATION_SHA256_FIELD} is missing, malformed, or stale"
        )
    return errors


def _response_semantic_association_errors(
    response: Mapping[str, object], association: Mapping[str, object], *, field: str
) -> list[str]:
    """Require the human response to echo the current schema-2 semantic pin."""

    expected = str(association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or "").strip().lower()
    supplied = str(response.get(SEMANTIC_ASSOCIATION_SHA256_FIELD) or "").strip().lower()
    if not _SHA256_RE.fullmatch(expected) or supplied != expected:
        return [
            f"{SEMANTIC_ASSOCIATION_SHA256_FIELD} must equal the current generated "
            f"{field} semantic association pin"
        ]
    return []


def _source_map_items(
    statement_map: Mapping[str, object] | None,
) -> tuple[dict[str, Mapping[str, object]], list[str]]:
    if not isinstance(statement_map, Mapping):
        return {}, ["current paper_statement_map.json is missing or invalid"]
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return {}, ["current paper_statement_map.json has no object-valued items map"]
    items: dict[str, Mapping[str, object]] = {}
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key or "").strip()
        if key and isinstance(raw_item, Mapping):
            items[key] = raw_item
    return items, []


def _recursive_field_scope_source_item_keys(
    source_proof_fidelity: Mapping[str, object] | None,
) -> set[str]:
    """Return exact supplemental source keys selected by convention scopes.

    These keys are provenance selectors, not ordinary coverage credit.  Only
    the canonical schema-1 container and its explicit ``source_item`` strings
    participate; missing or malformed ledger data selects nothing.  The caller
    still checks the selected map item against the source-presentation scope.
    """

    if not isinstance(source_proof_fidelity, Mapping):
        return set()
    raw_conventions = source_proof_fidelity.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return set()
    source_keys: set[str] = set()
    for raw_convention in raw_conventions:
        if not isinstance(raw_convention, Mapping):
            continue
        raw_scope = raw_convention.get("recursive_field_source_scope")
        if (
            not isinstance(raw_scope, Mapping)
            or set(raw_scope) != {"schema", "entries"}
            or raw_scope.get("schema") != 1
        ):
            continue
        raw_entries = raw_scope.get("entries")
        if not isinstance(raw_entries, list):
            continue
        for raw_entry in raw_entries:
            if not isinstance(raw_entry, Mapping):
                continue
            raw_source_key = raw_entry.get("source_item")
            if not isinstance(raw_source_key, str):
                continue
            source_key = raw_source_key.strip()
            if source_key:
                source_keys.add(source_key)
    return source_keys


def _validated_vocabulary_selector_source_item_keys(
    value: object,
    *,
    selector_name: str,
) -> tuple[set[str], list[str]]:
    """Read one generated source-domain vocabulary selector receipt.

    Vocabulary bindings and their one-route direct subset have different
    roles.  Keep both opaque source-item selectors explicit so revalidation
    can reproduce raw generation without elevating an ordinarily selected
    multi-route definition to one-to-one direct provenance.
    """

    if value is None:
        return set(), []
    if not isinstance(value, list):
        return set(), [
            f"generated {selector_name} selector must be a list"
        ]
    source_keys: set[str] = set()
    errors: list[str] = []
    for index, raw_source_key in enumerate(value):
        if not isinstance(raw_source_key, str) or not raw_source_key.strip():
            errors.append(
                f"generated {selector_name} selector[{index}] must be a "
                "nonempty source-map item id"
            )
            continue
        source_key = raw_source_key.strip()
        if source_key in source_keys:
            errors.append(
                f"generated {selector_name} selector has duplicate item id "
                f"`{source_key}`"
            )
            continue
        source_keys.add(source_key)
    return source_keys, errors


def _validated_vocabulary_binding_source_item_keys(
    value: object,
) -> tuple[set[str], list[str]]:
    """Read the broad source-validated vocabulary-binding selector."""

    return _validated_vocabulary_selector_source_item_keys(
        value,
        selector_name="validated vocabulary binding",
    )


def _validated_vocabulary_direct_route_source_item_keys(
    value: object,
) -> tuple[set[str], list[str]]:
    """Read the generated one-route vocabulary direct subset."""

    return _validated_vocabulary_selector_source_item_keys(
        value,
        selector_name="validated vocabulary direct-route",
    )


def _explicit_direct_source_statement_association_errors(
    association: Mapping[str, object],
    identities: list[dict[str, str]],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    validated_vocabulary_binding_source_item_ids: object | None,
    validated_vocabulary_direct_route_source_item_ids: object | None,
    reviewed_qualified_declaration: str,
    historical_receipt_only: bool = False,
) -> list[str]:
    """Validate a source-presentation-selected direct statement route.

    This is not a declaration-name classifier. The current source map must
    explicitly route each selected source presentation to exactly the reviewed
    fully-qualified declaration. The association itself additionally carries
    the current elaborated-signature pin checked by the common schema-2 lane.
    """

    errors: list[str] = []
    if (
        str(association.get("association_origin") or "").strip()
        != EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN
    ):
        errors.append(
            "generated source_statement_association must declare the explicit direct-route origin"
        )
    if (
        str(association.get("role") or "").strip()
        != EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE
    ):
        errors.append(
            "generated source_statement_association must declare the direct-source-route role"
        )
    if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
        errors.append(
            "generated source_statement_association requires schema 2 with an elaborated-signature pin"
        )
    if (
        str(association.get("structural_pairing") or "").strip()
        != "not_applicable_direct_source_route"
    ):
        errors.append(
            "generated source_statement_association must not claim a direct/Spec structural pairing"
        )
    if not reviewed_qualified_declaration:
        errors.append(
            "generated source_statement_association has no reviewed fully-qualified declaration"
        )
        return errors
    if historical_receipt_only and statement_map is None:
        return errors
    if not isinstance(statement_map, Mapping):
        return errors + [
            "generated source_statement_association cannot validate its source-presentation scope without the current source map"
        ]
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return errors + [
            "generated source_statement_association cannot validate its source-presentation scope without source-map items"
        ]
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return errors + [
            "generated source_statement_association cannot validate its source-presentation scope: "
            + mode_error
        ]
    declared_environment_kinds = source_named_result_environment_kinds_from_map(
        statement_map
    )
    selected_items = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=declared_environment_kinds,
    )
    supplemental_source_keys = _recursive_field_scope_source_item_keys(
        source_proof_fidelity
    )
    for source_key in supplemental_source_keys:
        source_item = raw_items.get(source_key)
        if isinstance(source_item, dict):
            selected_items[source_key] = source_item
    (
        validated_vocabulary_binding_source_keys,
        vocabulary_binding_selector_errors,
    ) = _validated_vocabulary_binding_source_item_keys(
        validated_vocabulary_binding_source_item_ids
    )
    (
        validated_vocabulary_direct_route_source_keys,
        vocabulary_direct_route_selector_errors,
    ) = _validated_vocabulary_direct_route_source_item_keys(
        validated_vocabulary_direct_route_source_item_ids
    )
    invalid_direct_source_keys = (
        validated_vocabulary_direct_route_source_keys
        - validated_vocabulary_binding_source_keys
    )
    if invalid_direct_source_keys:
        vocabulary_direct_route_selector_errors.extend(
            "generated validated vocabulary direct-route selector names source "
            f"item `{source_key}` absent from the validated vocabulary binding selector"
            for source_key in sorted(invalid_direct_source_keys)
        )
        validated_vocabulary_direct_route_source_keys -= invalid_direct_source_keys
    errors.extend(vocabulary_binding_selector_errors)
    errors.extend(vocabulary_direct_route_selector_errors)
    # Match raw generation: a broad vocabulary definition can be selected for
    # source coverage but not treated as a one-to-one direct route unless the
    # source-domain reconciliation emitted it in the narrow direct subset. An
    # independent recursive scope remains authoritative and is never removed.
    for source_key in (
        validated_vocabulary_binding_source_keys
        - validated_vocabulary_direct_route_source_keys
        - supplemental_source_keys
    ):
        source_item = raw_items.get(source_key)
        # Mirror raw generation: a semantic contract remains authoritative
        # even if malformed, so its existing contract/direct-route validation
        # must surface instead of being hidden by vocabulary suppression.
        if isinstance(source_item, Mapping) and source_item.get("semantic_contract") is None:
            selected_items.pop(source_key, None)
    for source_key in validated_vocabulary_direct_route_source_keys:
        source_item = raw_items.get(source_key)
        if not isinstance(source_item, Mapping):
            errors.append(
                "generated validated vocabulary direct-route selector names "
                f"missing source-map item `{source_key}`"
            )
            continue
        selected_items[source_key] = source_item
    for identity in identities:
        source_key = identity["source_key"]
        source_item = selected_items.get(source_key)
        if not isinstance(source_item, Mapping):
            errors.append(
                f"generated source_statement_association source item `{source_key}` is not selected by the current source-presentation scope, an exact supplemental convention scope, or the generated validated vocabulary one-route selector"
            )
            continue
        if source_item.get("claim_bearing") is False:
            supplemental_nonclaim_context = (
                source_key in supplemental_source_keys
                and not source_item_in_coverage_scope(
                    source_item,
                    mode,
                    declared_environment_kinds=declared_environment_kinds,
                )
            )
            if not supplemental_nonclaim_context:
                errors.append(
                    f"generated source_statement_association source item `{source_key}` sets claim_bearing: false without an exact supplemental convention selection outside ordinary source-presentation scope"
                )
        if source_item.get("semantic_contract") is not None:
            errors.append(
                f"generated source_statement_association source item `{source_key}` supplies semantic_contract metadata and cannot use direct-route provenance"
            )
            continue
        routes: list[str] = []
        malformed_route_metadata = False
        for field in EXPLICIT_DIRECT_SOURCE_ROUTE_FIELDS:
            raw_routes = source_item.get(field)
            if raw_routes is None:
                continue
            if not isinstance(raw_routes, list):
                malformed_route_metadata = True
                continue
            for raw_route in raw_routes:
                route = str(raw_route or "").strip()
                if not route:
                    malformed_route_metadata = True
                    continue
                routes.append(route)
        # A source-map item may expose the same checked declaration through
        # both its presentation and proof-routing metadata.  That is one
        # direct route, not two competing routes.  Preserve order while still
        # rejecting every genuinely distinct or malformed route collection.
        routes = list(dict.fromkeys(routes))
        if malformed_route_metadata:
            errors.append(
                f"generated source_statement_association source item `{source_key}` has malformed direct-route metadata"
            )
        if routes != [reviewed_qualified_declaration]:
            errors.append(
                f"generated source_statement_association source item `{source_key}` must have exactly one explicit direct route equal to the reviewed declaration"
            )
    return errors


def _defect_index(
    source_proof_fidelity: Mapping[str, object] | None,
) -> tuple[dict[str, Mapping[str, object]], list[str]]:
    if not isinstance(source_proof_fidelity, Mapping):
        return {}, ["current source_proof_fidelity ledger is missing or invalid"]
    raw_defects = source_proof_fidelity.get("defects")
    if not isinstance(raw_defects, list):
        return {}, ["source_proof_fidelity.defects must be a list for corrected-target review"]
    defects: dict[str, Mapping[str, object]] = {}
    errors: list[str] = []
    for index, raw_defect in enumerate(raw_defects):
        if not isinstance(raw_defect, Mapping):
            continue
        defect_id = str(raw_defect.get("id") or "").strip()
        if not defect_id:
            continue
        if defect_id in defects:
            errors.append(f"source_proof_fidelity.defects duplicates id `{defect_id}`")
            continue
        defects[defect_id] = raw_defect
    return defects, errors


def _convention_index(
    source_proof_fidelity: Mapping[str, object] | None,
) -> tuple[dict[str, Mapping[str, object]], list[str]]:
    if not isinstance(source_proof_fidelity, Mapping):
        return {}, ["current source_proof_fidelity ledger is missing or invalid"]
    raw_conventions = source_proof_fidelity.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return {}, ["source_proof_fidelity.model_conventions must be a list for convention review"]
    conventions: dict[str, Mapping[str, object]] = {}
    errors: list[str] = []
    for index, raw_convention in enumerate(raw_conventions):
        if not isinstance(raw_convention, Mapping):
            continue
        convention_id = str(raw_convention.get("id") or "").strip()
        if not convention_id:
            continue
        if convention_id in conventions:
            errors.append(
                f"source_proof_fidelity.model_conventions duplicates id `{convention_id}`"
            )
            continue
        conventions[convention_id] = raw_convention
    return conventions, errors


def _response_source_map_keys(
    response: Mapping[str, object], expected: set[str]
) -> list[str]:
    keys, errors = _unique_string_list(
        response.get("source_map_item_keys"), field="source_map_item_keys"
    )
    if errors:
        return errors
    if set(keys) != expected:
        return [
            "source_map_item_keys must exactly name the generated source-map "
            "identities for this semantic item"
        ]
    return []


def _model_convention_errors(
    response: Mapping[str, object],
    source_proof_fidelity: Mapping[str, object] | None,
) -> list[str]:
    ids, errors = _unique_string_list(
        response.get("model_convention_ids"), field="model_convention_ids"
    )
    if errors:
        return errors
    conventions, index_errors = _convention_index(source_proof_fidelity)
    errors.extend(index_errors)
    expected_digests: dict[str, str] = {}
    for convention_id in ids:
        convention = conventions.get(convention_id)
        if convention is None:
            errors.append(
                f"model_convention_ids cites unknown source_proof_fidelity.model_conventions id `{convention_id}`"
            )
            continue
        for field in ("source_locator", "classification", "formal_meaning", "why_needed", "checked_scope"):
            if not _normalized_text(convention.get(field)):
                errors.append(
                    f"model convention `{convention_id}` lacks required semantic field `{field}`"
                )
        expected_digests[convention_id] = model_convention_semantic_digest(convention)
    response_digests = response.get(_CONVENTION_SHA256_FIELD)
    if not isinstance(response_digests, Mapping):
        errors.append(
            f"{_CONVENTION_SHA256_FIELD} must map each cited model convention id to its digest"
        )
    else:
        supplied = {
            str(key).strip(): str(value).strip().lower()
            for key, value in response_digests.items()
            if str(key).strip()
        }
        if set(supplied) != set(expected_digests):
            errors.append(
                f"{_CONVENTION_SHA256_FIELD} must cover exactly model_convention_ids"
            )
        for convention_id, expected_digest in expected_digests.items():
            if supplied.get(convention_id) != expected_digest:
                errors.append(
                    f"{_CONVENTION_SHA256_FIELD}.{convention_id} is not the current model-convention digest"
                )
    return errors


def approved_source_convention_metadata_errors(
    response: Mapping[str, object],
    *,
    source_proof_fidelity: Mapping[str, object] | None,
) -> list[str]:
    """Validate convention metadata independent of one direct source route.

    Most convention credit is attached to a generated direct source association
    or an explicitly scoped recursive-field parent route.  A separately
    audited semantic-model record binding may also establish the parent route
    for every field in one generated record closure.  That caller still needs
    this narrow metadata check: it must state the convention disposition,
    carry only current convention digests, cite source evidence, and never
    smuggle corrected-target metadata into a convention judgment.

    This helper deliberately does *not* decide whether the response has a
    valid source route.  Callers must establish that independently from
    generated semantic-model identities and a checked record binding.
    """

    errors: list[str] = []
    if str(response.get("classification") or "").strip() != "approved_source_convention":
        return ["accepted convention field must be classified approved_source_convention"]
    if (
        str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
        != "approved_source_convention"
    ):
        errors.append(
            "approved_source_convention must use source_target_disposition approved_source_convention"
        )
    if not _input_source_locator(response):
        errors.append("approved_source_convention needs an exact source location/evidence")
    errors.extend(_model_convention_errors(response, source_proof_fidelity))
    if (
        response.get("governing_defect_ids")
        or response.get(_TARGET_SHA256_FIELD)
        or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
    ):
        errors.append(
            "approved_source_convention cannot carry corrected-target defect or digest metadata"
        )
    return errors


def _corrected_target_errors(
    response: Mapping[str, object],
    corrected_items: dict[str, Mapping[str, object]],
    source_proof_fidelity: Mapping[str, object] | None,
    *,
    source_semantic_sha256_by_key: Mapping[str, str] | None = None,
) -> list[str]:
    errors: list[str] = []
    expected_governing_ids: set[str] = set()
    expected_digests: dict[str, str] = {}
    defects, defect_index_errors = _defect_index(source_proof_fidelity)
    errors.extend(defect_index_errors)

    for source_key, source_item in sorted(corrected_items.items()):
        target = source_item.get("corrected_target")
        if not isinstance(target, Mapping):
            errors.append(
                f"source-map item `{source_key}` is corrected_source_statement but has no corrected_target object"
            )
            continue
        if target.get("archival_equivalence_claimed") is not False:
            errors.append(
                f"source-map corrected target `{source_key}` must explicitly reject archival equivalence"
            )
        governing_ids, governing_errors = _unique_string_list(
            target.get("governing_defect_ids"),
            field=f"source-map corrected target `{source_key}`.governing_defect_ids",
        )
        errors.extend(governing_errors)
        expected_governing_ids.update(governing_ids)
        routed_ids = {
            value.strip()
            for value in source_item.get("source_defect_ids", [])
            if isinstance(value, str) and value.strip()
        }
        if governing_ids and not set(governing_ids).issubset(routed_ids):
            errors.append(
                f"source-map corrected target `{source_key}` governing_defect_ids are not routed by source_defect_ids"
            )
        for defect_id in governing_ids:
            defect = defects.get(defect_id)
            if defect is None:
                errors.append(
                    f"source-map corrected target `{source_key}` cites unknown source-proof defect `{defect_id}`"
                )
                continue
            if str(defect.get("resolution") or "").strip() != CORRECTED_SOURCE_STATEMENT_RESOLUTION:
                errors.append(
                    f"source-proof defect `{defect_id}` must resolve as corrected_source_statement"
                )
            if str(defect.get("statement_impact") or "").strip() != "source_statement":
                errors.append(
                    f"source-proof defect `{defect_id}` must have statement_impact source_statement"
                )

        recorded_digest = str(target.get("corrected_target_sha256") or "").strip().lower()
        actual_digest = corrected_target_record_digest(target)
        if recorded_digest != actual_digest:
            errors.append(
                f"source-map corrected target `{source_key}` has a stale corrected_target_sha256"
            )
        expected_digests[source_key] = actual_digest

    response_ids, response_id_errors = _unique_string_list(
        response.get("governing_defect_ids"), field="governing_defect_ids"
    )
    errors.extend(response_id_errors)
    if response_ids and set(response_ids) != expected_governing_ids:
        errors.append(
            "governing_defect_ids must exactly match the corrected source-map target(s)"
        )

    if source_semantic_sha256_by_key is None:
        response_digests = response.get(_TARGET_SHA256_FIELD)
        if not isinstance(response_digests, Mapping):
            errors.append(f"{_TARGET_SHA256_FIELD} must map each corrected source-map item to its digest")
        else:
            supplied = {
                str(key).strip(): str(value).strip().lower()
                for key, value in response_digests.items()
                if str(key).strip()
            }
            if set(supplied) != set(expected_digests):
                errors.append(
                    f"{_TARGET_SHA256_FIELD} must cover exactly the corrected source-map item identities"
                )
            for source_key, expected_digest in expected_digests.items():
                if supplied.get(source_key) != expected_digest:
                    errors.append(
                        f"{_TARGET_SHA256_FIELD}.{source_key} is not the current corrected-target digest"
                    )
        return errors

    expected_semantic_digests: dict[str, str] = {}
    for source_key, expected_digest in expected_digests.items():
        source_semantic_digest = str(
            source_semantic_sha256_by_key.get(source_key) or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(source_semantic_digest):
            errors.append(
                f"corrected source-map item `{source_key}` has no current source semantic SHA-256"
            )
            continue
        if source_semantic_digest in expected_semantic_digests:
            errors.append(
                "corrected source-map items have ambiguous duplicate source semantic SHA-256 identities"
            )
            continue
        expected_semantic_digests[source_semantic_digest] = expected_digest

    response_digests = response.get(_TARGET_SEMANTIC_SHA256_FIELD)
    if not isinstance(response_digests, Mapping):
        errors.append(
            f"{_TARGET_SEMANTIC_SHA256_FIELD} must map each corrected source semantic SHA-256 to its digest"
        )
    else:
        supplied = {
            str(key).strip().lower(): str(value).strip().lower()
            for key, value in response_digests.items()
            if str(key).strip()
        }
        if set(supplied) != set(expected_semantic_digests):
            errors.append(
                f"{_TARGET_SEMANTIC_SHA256_FIELD} must cover exactly the corrected source semantic identities"
            )
        for source_semantic_digest, expected_digest in expected_semantic_digests.items():
            if supplied.get(source_semantic_digest) != expected_digest:
                errors.append(
                    f"{_TARGET_SEMANTIC_SHA256_FIELD}.{source_semantic_digest} is not the current corrected-target digest"
                )
    return errors


def current_source_correction_identity_by_key(
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
) -> dict[str, Mapping[str, object] | None]:
    """Return every current source item with its validated correction identity.

    ``None`` is a positive receipt that the current item is not a corrected
    target. A corrected-looking but malformed item is omitted entirely, so a
    theorem-realization contract cannot interpret a broken correction ledger
    as an ordinary literal source statement.
    """

    source_items, map_errors = _source_map_items(statement_map)
    if map_errors:
        return {}
    identities: dict[str, Mapping[str, object] | None] = {}
    for source_key, source_item in source_items.items():
        corrected_status = (
            str(source_item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        )
        target = source_item.get("corrected_target")
        target_present = target is not None
        if not corrected_status and not target_present:
            identities[source_key] = None
            continue
        if not corrected_status or not isinstance(target, Mapping):
            continue

        governing_ids_raw = target.get("governing_defect_ids")
        if not isinstance(governing_ids_raw, list):
            continue
        governing_ids = [
            value.strip()
            for value in governing_ids_raw
            if isinstance(value, str) and value.strip()
        ]
        target_sha = str(target.get("corrected_target_sha256") or "").strip().lower()
        response: dict[str, object] = {
            "governing_defect_ids": governing_ids,
            _TARGET_SHA256_FIELD: {source_key: target_sha},
        }
        if _corrected_target_errors(
            response,
            {source_key: source_item},
            source_proof_fidelity,
        ):
            continue
        identities[source_key] = {
            "corrected_target_sha256": target_sha,
            "governing_defect_ids": tuple(sorted(governing_ids)),
        }
    return identities


def _source_contract_association_context(
    item: Mapping[str, object],
    statement_map: Mapping[str, object] | None,
    *,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    historical_receipt_only: bool = False,
) -> tuple[
    Mapping[str, object] | None,
    list[dict[str, str]],
    dict[str, Mapping[str, object]],
    list[str],
    bool,
    Mapping[str, object] | None,
]:
    """Validate an input's generated declaration-content association.

    This intentionally reads no row, binder, short declaration, or function
    name.  The association has already been projected by the generator using
    fully-qualified declaration pins; schema 2 additionally carries the
    current elaborated signature. This layer verifies current source-map and
    semantic pins before a human response can claim source credit through it.
    """

    association_field = SOURCE_CONTRACT_ASSOCIATION_FIELD
    raw_association = item.get(association_field)
    if not isinstance(raw_association, Mapping):
        association_field = SOURCE_ASSUMPTION_ASSOCIATION_FIELD
        raw_association = item.get(association_field)
    if not isinstance(raw_association, Mapping):
        return None, [], {}, [], False, None
    association, rebind_binding = _rebound_association_and_binding(
        raw_association, administrative_projection_rebind
    )
    errors: list[str] = []
    schema = _association_schema(
        association,
        field=association_field,
        errors=errors,
    )
    association_digest = str(association.get("association_sha256") or "").strip().lower()
    expected_association_digest = source_contract_association_record_digest(association)
    if association_digest != expected_association_digest:
        errors.append("generated source_contract_association has a stale association_sha256")
    reviewed_identity = association.get("reviewed_declaration_identity")
    reviewed_qualified_declaration = ""
    if not isinstance(reviewed_identity, Mapping):
        errors.append("generated source_contract_association lacks reviewed_declaration_identity")
    else:
        qualified = str(reviewed_identity.get("qualified_declaration") or "").strip()
        reviewed_qualified_declaration = qualified
        declaration_digest = str(
            reviewed_identity.get("declaration_sha256") or ""
        ).strip().lower()
        if not qualified or "." not in qualified:
            errors.append(
                "generated source_contract_association reviewed declaration is not fully qualified"
            )
        if not re.fullmatch(r"[0-9a-f]{64}", declaration_digest):
            errors.append(
                "generated source_contract_association reviewed declaration SHA-256 is missing or malformed"
            )

    raw_identities = association.get("source_item_identities")
    identities: list[dict[str, str]] = []
    seen_keys: set[str] = set()
    if not isinstance(raw_identities, list) or not raw_identities:
        errors.append("generated source_contract_association has no source_item_identities")
    else:
        for index, raw_identity in enumerate(raw_identities):
            if not isinstance(raw_identity, Mapping):
                errors.append(
                    f"generated source_contract_association.source_item_identities[{index}] must be an object"
                )
                continue
            source_key = str(raw_identity.get("source_key") or "").strip()
            source_location = _normalized_text(raw_identity.get("source_location"))
            source_digest = str(
                raw_identity.get("source_map_item_sha256") or ""
            ).strip().lower()
            source_semantic_digest = str(
                raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
            ).strip().lower()
            if not source_key:
                errors.append(
                    f"generated source_contract_association.source_item_identities[{index}].source_key is missing"
                )
                continue
            if source_key in seen_keys:
                errors.append(
                    f"generated source_contract_association duplicates source-map key `{source_key}`"
                )
                continue
            seen_keys.add(source_key)
            if not source_location:
                errors.append(
                    f"generated source_contract_association source-map key `{source_key}` has no source_location"
                )
            if not re.fullmatch(r"[0-9a-f]{64}", source_digest):
                errors.append(
                    f"generated source_contract_association source-map key `{source_key}` has no valid source_map_item_sha256"
                )
            identities.append(
                {
                    "source_key": source_key,
                    "source_location": source_location,
                    "source_map_item_sha256": source_digest,
                    **(
                        {SOURCE_SEMANTIC_SHA256_FIELD: source_semantic_digest}
                        if source_semantic_digest
                        else {}
                    ),
                }
            )

    expected_keys = {identity["source_key"] for identity in identities}
    association_keys, association_key_errors = _unique_string_list(
        association.get("source_map_item_keys"), field="generated source_contract_association.source_map_item_keys"
    )
    errors.extend(association_key_errors)
    if association_keys and set(association_keys) != expected_keys:
        errors.append(
            "generated source_contract_association.source_map_item_keys must exactly name its source_item_identities"
        )
    expected_identity_digests = {
        identity["source_key"]: identity["source_map_item_sha256"]
        for identity in identities
    }
    association_digests = association.get(SOURCE_MAP_ITEM_SHA256_FIELD)
    if not isinstance(association_digests, Mapping):
        errors.append(
            f"generated source_contract_association.{SOURCE_MAP_ITEM_SHA256_FIELD} must map every source key to its digest"
        )
    else:
        supplied_digests = {
            str(key).strip(): str(value).strip().lower()
            for key, value in association_digests.items()
            if str(key).strip()
        }
        if supplied_digests != expected_identity_digests:
            errors.append(
                f"generated source_contract_association.{SOURCE_MAP_ITEM_SHA256_FIELD} must exactly match its source_item_identities"
            )
    association_keys_digest = str(
        association.get(SOURCE_MAP_ITEM_KEYS_SHA256_FIELD) or ""
    ).strip().lower()
    if association_keys_digest != source_map_item_record_digest(sorted(expected_keys)):
        errors.append(
            f"generated source_contract_association.{SOURCE_MAP_ITEM_KEYS_SHA256_FIELD} is stale"
        )

    corrected_items: dict[str, Mapping[str, object]] = {}
    if not historical_receipt_only or statement_map is not None:
        map_items, map_errors = _source_map_items(statement_map)
        errors.extend(map_errors)
        for identity in identities:
            source_key = identity["source_key"]
            source_item = map_items.get(source_key)
            if source_item is None:
                errors.append(
                    f"generated source-contract identity `{source_key}` is absent from current paper_statement_map.json"
                )
                continue
            if _normalized_text(source_item.get("source_location")) != identity["source_location"]:
                errors.append(
                    f"generated source-contract identity `{source_key}` no longer matches the current source_location"
                )
            if (
                source_record_source_item_record_sha256(source_item)
                != identity["source_map_item_sha256"]
            ):
                errors.append(
                    f"generated source-contract identity `{source_key}` no longer matches the current source-map item SHA-256"
                )
            if schema == SEMANTIC_ASSOCIATION_SCHEMA:
                expected_source_semantic_digest = (
                    source_record_source_item_semantic_sha256(
                        dict(source_item), ""
                    )
                )
                supplied_source_semantic_digest = str(
                    identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
                ).strip().lower()
                if supplied_source_semantic_digest != expected_source_semantic_digest:
                    errors.append(
                        f"generated source-contract identity `{source_key}` no longer matches the current source semantic SHA-256"
                    )
            if (
                str(source_item.get("coverage_status") or "").strip().lower()
                == CORRECTED_SOURCE_STATEMENT_STATUS
            ):
                corrected_items[source_key] = source_item
    if schema == SEMANTIC_ASSOCIATION_SCHEMA:
        errors.extend(
            _schema_two_semantic_association_errors(
                association,
                identities,
                reviewed_qualified_declaration=reviewed_qualified_declaration,
                field=association_field,
            )
        )
    return association, identities, corrected_items, errors, True, rebind_binding


def _response_source_map_item_digest_errors(
    response: Mapping[str, object], identities: list[dict[str, str]]
) -> list[str]:
    expected_digests = {
        identity["source_key"]: identity["source_map_item_sha256"]
        for identity in identities
    }
    raw_digests = response.get(SOURCE_MAP_ITEM_SHA256_FIELD)
    if not isinstance(raw_digests, Mapping):
        return [
            f"{SOURCE_MAP_ITEM_SHA256_FIELD} must map every generated source-map item key to its current digest"
        ]
    supplied = {
        str(key).strip(): str(value).strip().lower()
        for key, value in raw_digests.items()
        if str(key).strip()
    }
    if supplied != expected_digests:
        return [
            f"{SOURCE_MAP_ITEM_SHA256_FIELD} must exactly match the generated source-contract association"
        ]
    return []


def _source_semantic_sha256_by_key(
    identities: list[dict[str, str]],
) -> dict[str, str]:
    """Return source semantic IDs only when they are unique and well formed."""

    result: dict[str, str] = {}
    seen: set[str] = set()
    for identity in identities:
        source_key = str(identity.get("source_key") or "").strip()
        digest = str(identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "").strip().lower()
        if not source_key or not _SHA256_RE.fullmatch(digest) or digest in seen:
            return {}
        result[source_key] = digest
        seen.add(digest)
    return result


def _input_source_locator(response: Mapping[str, object]) -> str:
    return _normalized_text(
        response.get("source_location")
        or response.get("source_evidence")
        or response.get("source_key")
        or response.get("paper_statement_key")
    )


def _recursive_field_parent_route_context(
    item: Mapping[str, object],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    historical_receipt_only: bool = False,
) -> tuple[Mapping[str, object] | None, list[str], bool]:
    """Validate a generated recursive-field source route without name fallbacks.

    The receipt is emitted only after the generator joined a source-map item,
    source-ledger convention, exact recursive path, and direct semantic parent
    route.  Saved artifacts must recheck those pins rather than treating the
    field's display name or its parent declaration as evidence.
    """

    receipt = item.get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD)
    if not isinstance(receipt, Mapping):
        return None, [], False

    errors: list[str] = []
    if receipt.get("schema") != RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_SCHEMA:
        errors.append("generated recursive-field parent route has unsupported schema")
    if (
        str(receipt.get("inheritance_mode") or "").strip()
        != "explicit_parent_route_and_field_scope"
    ):
        errors.append("generated recursive-field parent route has unsupported inheritance mode")
    supplied_route_digest = str(receipt.get("association_sha256") or "").strip().lower()
    if (
        not _SHA256_RE.fullmatch(supplied_route_digest)
        or supplied_route_digest != recursive_field_parent_route_record_digest(receipt)
    ):
        errors.append(
            "generated recursive-field parent route has a missing, malformed, or stale association_sha256"
        )

    source_key = str(receipt.get("source_item") or "").strip()
    if not source_key:
        errors.append("generated recursive-field parent route has no source_item")
    root_record = str(receipt.get("root_record") or "").strip()
    if not root_record or "." not in root_record:
        errors.append("generated recursive-field parent route root_record is not fully qualified")
    root_input_type = _normalized_text(receipt.get("root_input_type_canonical"))
    if not root_input_type:
        errors.append("generated recursive-field parent route has no root_input_type_canonical")
    source_locator = _normalized_text(receipt.get("source_locator"))
    if not source_locator:
        errors.append("generated recursive-field parent route has no exact source_locator")

    raw_chain = receipt.get("field_chain")
    if not isinstance(raw_chain, list) or not raw_chain:
        errors.append("generated recursive-field parent route has no nonempty field_chain")
    else:
        for index, raw_link in enumerate(raw_chain):
            if not isinstance(raw_link, Mapping) or set(raw_link) != {"structure", "field"}:
                errors.append(
                    "generated recursive-field parent route field_chain["
                    + str(index)
                    + "] must contain exactly structure and field"
                )
                continue
            structure = str(raw_link.get("structure") or "").strip()
            field = str(raw_link.get("field") or "").strip()
            if not structure or "." not in structure or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*", field
            ):
                errors.append(
                    "generated recursive-field parent route field_chain["
                    + str(index)
                    + "] has malformed fully-qualified structure/field data"
                )
        if isinstance(raw_chain[0], Mapping) and str(
            raw_chain[0].get("structure") or ""
        ).strip() != root_record:
            errors.append(
                "generated recursive-field parent route field_chain does not begin at root_record"
            )

    permitted, permitted_errors = _unique_string_list(
        receipt.get("permitted_classifications"),
        field="generated recursive-field parent route permitted_classifications",
    )
    errors.extend(permitted_errors)
    raw_nested = item.get("nested_structures")
    if not isinstance(raw_nested, list):
        errors.append(
            "generated recursive-field parent route field lacks nested_structures data"
        )
    else:
        has_nested_record = any(str(value or "").strip() for value in raw_nested)
        if has_nested_record:
            if permitted != [RECURSIVE_FIELD_CONTAINER_CLASSIFICATION]:
                errors.append(
                    "a recursive-field scope for a nested record must permit only "
                    "container_recursively_audited"
                )
        elif RECURSIVE_FIELD_CONTAINER_CLASSIFICATION in permitted:
            errors.append(
                "a recursive-field scope for a non-container leaf cannot permit "
                "container_recursively_audited"
            )

    convention_id = str(receipt.get("convention_id") or "").strip()
    convention_digest = str(receipt.get("convention_sha256") or "").strip().lower()
    if not convention_id:
        errors.append("generated recursive-field parent route has no convention_id")
    if not _SHA256_RE.fullmatch(convention_digest):
        errors.append("generated recursive-field parent route has no valid convention_sha256")
    field_scope_digest = str(receipt.get("field_scope_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(field_scope_digest):
        errors.append("generated recursive-field parent route has no valid field_scope_sha256")

    identities = receipt.get("source_item_identities")
    source_semantic_digests: list[str] = []
    if not isinstance(identities, list) or len(identities) != 1:
        errors.append(
            "generated recursive-field parent route must contain exactly one source_item_identity"
        )
    else:
        raw_identity = identities[0]
        if not isinstance(raw_identity, Mapping):
            errors.append(
                "generated recursive-field parent route source_item_identity must be an object"
            )
        else:
            identity_key = str(raw_identity.get("source_key") or "").strip()
            map_digest = str(
                raw_identity.get("source_map_item_sha256") or ""
            ).strip().lower()
            semantic_digest = str(
                raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
            ).strip().lower()
            if identity_key != source_key:
                errors.append(
                    "generated recursive-field parent route source identity does not match source_item"
                )
            if not _SHA256_RE.fullmatch(map_digest):
                errors.append(
                    "generated recursive-field parent route source identity has no valid source-map digest"
                )
            if not _SHA256_RE.fullmatch(semantic_digest):
                errors.append(
                    "generated recursive-field parent route source identity has no valid source semantic digest"
                )
            else:
                source_semantic_digests.append(semantic_digest)

    parent_identity = receipt.get("parent_reviewed_declaration_identity")
    parent_signature = receipt.get("parent_elaborated_signature_identity")
    parent_qualified = ""
    if not isinstance(parent_identity, Mapping):
        errors.append(
            "generated recursive-field parent route has no parent reviewed declaration identity"
        )
    else:
        parent_qualified = str(
            parent_identity.get("qualified_declaration") or ""
        ).strip()
        parent_declaration_digest = str(
            parent_identity.get("declaration_sha256") or ""
        ).strip().lower()
        if not parent_qualified or "." not in parent_qualified:
            errors.append(
                "generated recursive-field parent route parent declaration is not fully qualified"
            )
        if not _SHA256_RE.fullmatch(parent_declaration_digest):
            errors.append(
                "generated recursive-field parent route parent declaration has no valid SHA-256"
            )
    if not isinstance(parent_signature, Mapping):
        errors.append(
            "generated recursive-field parent route has no parent elaborated signature identity"
        )
    else:
        signature_qualified = str(
            parent_signature.get("qualified_declaration") or ""
        ).strip()
        signature_digest = str(
            parent_signature.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        if signature_qualified != parent_qualified or not _SHA256_RE.fullmatch(
            signature_digest
        ):
            errors.append(
                "generated recursive-field parent route parent signature is malformed or does not match its parent declaration"
            )
    parent_association_field = str(
        receipt.get("parent_association_field") or ""
    ).strip()
    parent_semantic_model_judgment_key = str(
        receipt.get("parent_semantic_model_judgment_key") or ""
    ).strip()
    if not parent_semantic_model_judgment_key:
        errors.append(
            "generated recursive-field parent route has no parent semantic-model judgment key"
        )
    parent_role = str(receipt.get("parent_source_association_role") or "").strip()
    parent_origin = str(
        receipt.get("parent_source_association_origin") or ""
    ).strip()
    if parent_association_field == "source_statement_association":
        if (
            parent_origin != EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN
            or parent_role != EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE
        ):
            errors.append(
                "generated recursive-field source-statement parent route must retain the exact direct origin and role"
            )
    elif parent_association_field == SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD:
        if (
            parent_origin != SOURCE_CLAIM_ATOM_ROUTE_ORIGIN
            or parent_role != SOURCE_CLAIM_ATOM_ROUTE_ROLE
        ):
            errors.append(
                "generated recursive-field source-claim-atom parent route must retain the exact atom-route origin and role"
            )
    elif parent_association_field == "semantic_contract_source_association":
        if (
            parent_role
            not in RECURSIVE_FIELD_DIRECT_SEMANTIC_CONTRACT_PARENT_ROLES
            or parent_origin
        ):
            errors.append(
                "generated recursive-field semantic-contract parent route must use a direct evidence/spec role with no support origin"
            )
    else:
        errors.append(
            "generated recursive-field parent route has an unsupported parent association field"
        )
    parent_association_digest = str(
        receipt.get("parent_source_association_sha256") or ""
    ).strip().lower()
    expected_parent_association_digest = semantic_association_record_digest(
        source_semantic_digests,
        parent_signature,
    )
    if (
        not _SHA256_RE.fullmatch(parent_association_digest)
        or not expected_parent_association_digest
        or parent_association_digest != expected_parent_association_digest
    ):
        errors.append(
            "generated recursive-field parent route parent source association pin is missing, malformed, or stale"
        )

    current_source_item: Mapping[str, object] | None = None
    if not historical_receipt_only or statement_map is not None:
        map_items, map_errors = _source_map_items(statement_map)
        errors.extend(map_errors)
        source_item = map_items.get(source_key)
        if source_key and source_item is None:
            errors.append(
                f"generated recursive-field parent route source item `{source_key}` is absent from the current source map"
            )
        elif isinstance(source_item, Mapping) and isinstance(identities, list) and len(identities) == 1:
            current_source_item = source_item
            raw_identity = identities[0]
            if isinstance(raw_identity, Mapping):
                if (
                    str(raw_identity.get("source_map_item_sha256") or "")
                    .strip()
                    .lower()
                    != source_record_source_item_record_sha256(source_item)
                ):
                    errors.append(
                        "generated recursive-field parent route source item no longer matches the current source-map digest"
                    )
                if (
                    str(raw_identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or "")
                    .strip()
                    .lower()
                    != source_record_source_item_semantic_sha256(source_item, "")
                ):
                    errors.append(
                        "generated recursive-field parent route source item no longer matches the current source semantic digest"
                    )
            source_convention_ids, source_convention_errors = _unique_string_list(
                source_item.get("model_convention_ids"),
                field="recursive-field source item's model_convention_ids",
            )
            errors.extend(source_convention_errors)
            if convention_id and convention_id not in source_convention_ids:
                errors.append(
                    "generated recursive-field parent route convention_id is not explicitly listed by its source item"
                )

    conventions, convention_errors = _convention_index(source_proof_fidelity)
    errors.extend(convention_errors)
    convention = conventions.get(convention_id)
    if convention_id and convention is None:
        errors.append(
            f"generated recursive-field parent route convention `{convention_id}` is absent from the current source-proof ledger"
        )
    elif isinstance(convention, Mapping):
        if convention_digest != model_convention_record_digest(convention):
            errors.append(
                "generated recursive-field parent route convention_sha256 no longer matches the current source-proof ledger"
            )

        # A route digest proves only that its own JSON was not edited.  Rejoin
        # it to exactly one *current* schema-1 ledger entry as well, so a
        # self-consistent stale route cannot choose a different field,
        # locator, or classification list after generation.
        raw_scope_container = convention.get("recursive_field_source_scope")
        matching_scopes: list[Mapping[str, object]] = []
        if (
            not isinstance(raw_scope_container, Mapping)
            or set(raw_scope_container) != {"schema", "entries"}
            or raw_scope_container.get("schema") != 1
            or not isinstance(raw_scope_container.get("entries"), list)
        ):
            errors.append(
                "generated recursive-field parent route convention has no current schema-1 recursive_field_source_scope"
            )
        else:
            for raw_scope in raw_scope_container["entries"]:
                if not isinstance(raw_scope, Mapping):
                    continue
                if set(raw_scope) != {
                    "source_item",
                    "root_record",
                    "field_chain",
                    "source_locator",
                    "permitted_classifications",
                }:
                    continue
                candidate = {
                    "source_item": str(raw_scope.get("source_item") or "").strip(),
                    "root_record": str(raw_scope.get("root_record") or "").strip(),
                    "field_chain": raw_scope.get("field_chain"),
                    "source_locator": str(raw_scope.get("source_locator") or "").strip(),
                    "permitted_classifications": raw_scope.get(
                        "permitted_classifications"
                    ),
                }
                if (
                    recursive_field_source_scope_record_digest(candidate)
                    == field_scope_digest
                    and candidate["source_item"] == source_key
                    and candidate["root_record"] == root_record
                    and candidate["field_chain"] == raw_chain
                    and candidate["source_locator"] == str(
                        receipt.get("source_locator") or ""
                    ).strip()
                    and candidate["permitted_classifications"]
                    == receipt.get("permitted_classifications")
                ):
                    matching_scopes.append(raw_scope)
            if len(matching_scopes) != 1:
                errors.append(
                    "generated recursive-field parent route does not resolve to exactly one current convention field scope"
                )
            elif current_source_item is not None:
                anchor_error = recursive_field_scope_locator_anchor_error(
                    receipt.get("source_locator"),
                    source_item_locator=current_source_item.get("source_location"),
                    convention_locator=convention.get("source_locator"),
                )
                if anchor_error:
                    errors.append(
                        "generated recursive-field parent route " + anchor_error
                    )

    return receipt, errors, True


def _recursive_field_parent_route_generated_path_errors(
    item: Mapping[str, object], receipt: Mapping[str, object]
) -> list[str]:
    """Check that a persisted route still names this generated field path.

    ``recursive_field_explicit_parent_route`` is generated from a structural
    traversal, rather than from a reviewer-selected field name.  Rechecking
    that traversal here prevents a later edit from moving a valid route onto a
    neighboring field while retaining a self-consistent receipt digest.
    """

    errors: list[str] = []
    root_record = str(receipt.get("root_record") or "").strip()
    raw_chain = receipt.get("field_chain")
    if not root_record or not isinstance(raw_chain, list) or not raw_chain:
        # The parent-route context reports the malformed receipt itself.  Do
        # not manufacture a second, less useful path diagnostic here.
        return errors

    path = str(item.get("path") or "").strip()
    segments = [segment.strip() for segment in path.split(" -> ")]
    if len(segments) < 2 or any(not segment for segment in segments):
        return [
            "generated recursive-field item has no complete structural path for its parent route"
        ]
    if segments[0] != root_record:
        errors.append(
            "generated recursive-field path root does not match its explicit parent route"
        )
        return errors

    generated_chain: list[dict[str, str]] = []
    for segment in segments[1:]:
        if "." not in segment:
            return [
                "generated recursive-field path has a malformed selector for its parent route"
            ]
        structure, field = (part.strip() for part in segment.rsplit(".", 1))
        generated_chain.append({"structure": structure, "field": field})
    if generated_chain != raw_chain:
        errors.append(
            "generated recursive-field path does not match the explicit parent-route field chain"
        )

    final_link = raw_chain[-1]
    if not isinstance(final_link, Mapping):
        return errors
    if (
        str(item.get("structure") or "").strip()
        != str(final_link.get("structure") or "").strip()
        or str(item.get("field") or "").strip()
        != str(final_link.get("field") or "").strip()
    ):
        errors.append(
            "generated recursive-field coordinate does not match the explicit parent-route leaf"
        )
    root_input_type = _normalized_text(receipt.get("root_input_type_canonical"))
    if root_input_type and not (
        root_input_type == root_record
        or root_input_type.startswith(root_record + " ")
        or root_input_type.startswith(root_record + "(")
        or root_input_type.startswith("@" + root_record + " ")
        or root_input_type.startswith("@" + root_record + "(")
    ):
        errors.append(
            "explicit parent-route root input type is not headed by its generated root record"
        )
    return errors


def recursive_field_target_disposition_errors(
    item: Mapping[str, object],
    response: Mapping[str, object],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    historical_receipt_only: bool = False,
) -> list[str]:
    """Validate source credit on an explicitly scoped recursive field.

    This applies only when the generator emitted a parent-route receipt.  It
    never derives a route from a field/record name.  In particular, convention
    credit must name the sole convention pinned by that receipt, so another
    ledger convention cannot be smuggled in through a visually similar leaf.
    """

    receipt, errors, has_receipt = _recursive_field_parent_route_context(
        item,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        historical_receipt_only=historical_receipt_only,
    )
    if not has_receipt:
        return []
    if errors:
        return errors
    assert receipt is not None

    errors.extend(_recursive_field_parent_route_generated_path_errors(item, receipt))
    if errors:
        return errors

    classification = str(response.get("classification") or "").strip()
    permitted = [
        str(value).strip()
        for value in receipt.get("permitted_classifications") or []
        if isinstance(value, str) and value.strip()
    ]
    if any(
        classification_name not in RECURSIVE_FIELD_SCOPE_PERMITTED_CLASSIFICATIONS
        for classification_name in permitted
    ):
        return [
            "recursive-field parent route permits a classification outside the source-credit protocol"
        ]
    if classification not in permitted:
        return [
            "recursive-field classification must be one of its generated parent-route "
            "permitted_classifications"
        ]
    # A container receipt documents the structural traversal only.  It never
    # closes a material source-claim occurrence; the occurrence issuer below
    # also refuses it.  Preserve the benign structural disposition for normal
    # recursive-audit callers without turning it into source credit.
    if classification == RECURSIVE_FIELD_CONTAINER_CLASSIFICATION:
        return []
    if classification not in RECURSIVE_FIELD_SOURCE_CREDIT_CLASSIFICATIONS:
        return [
            "recursive-field source-credit route can discharge only validated_source_assumption or approved_source_convention"
        ]
    # A scoped source-model field is source credit only at the source fragment
    # recorded by its generated route.  This applies to literal assumptions as
    # well as conventions/corrections; otherwise a current classification could
    # silently retarget a structural field to a nearby source assertion.
    if _normalized_text(_input_source_locator(response)) != _normalized_text(
        receipt.get("source_locator")
    ):
        return [
            "recursive-field source location must equal the generated parent-route source_locator"
        ]
    if classification == "validated_source_assumption":
        if (
            str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
            != "literal_source_match"
        ):
            return [
                "validated_source_assumption on a recursive field must use source_target_disposition literal_source_match"
            ]
        if (
            response.get("model_convention_ids")
            or response.get("governing_defect_ids")
            or response.get(_TARGET_SHA256_FIELD)
            or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
        ):
            return [
                "literal recursive-field source credit cannot carry convention or corrected-target metadata"
            ]
        if isinstance(statement_map, Mapping):
            raw_items = statement_map.get("items")
            if isinstance(raw_items, Mapping):
                source_item = raw_items.get(str(receipt.get("source_item") or ""))
                if isinstance(source_item, Mapping) and str(
                    source_item.get("coverage_status") or ""
                ).strip().lower() == CORRECTED_SOURCE_STATEMENT_STATUS:
                    return [
                        "validated_source_assumption cannot claim literal recursive-field credit for a corrected source item"
                    ]
        return []

    if (
        str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
        != "approved_source_convention"
    ):
        return [
            "approved_source_convention on a recursive field must use source_target_disposition approved_source_convention"
        ]
    convention_id = str(receipt.get("convention_id") or "").strip()
    response_ids, response_id_errors = _unique_string_list(
        response.get("model_convention_ids"), field="model_convention_ids"
    )
    errors = list(response_id_errors)
    if response_ids != [convention_id]:
        errors.append(
            "recursive-field approved_source_convention must cite exactly the generated parent-route convention_id"
        )
    errors.extend(_model_convention_errors(response, source_proof_fidelity))
    if (
        response.get("governing_defect_ids")
        or response.get(_TARGET_SHA256_FIELD)
        or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
    ):
        errors.append(
            "recursive-field approved_source_convention cannot carry corrected-target defect or digest metadata"
        )
    return errors


def approved_source_convention_antecedent_errors(
    item: Mapping[str, object],
    response: Mapping[str, object],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    status: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
) -> list[str]:
    """Validate a convention only when it is an assumed model antecedent.

    This is intentionally narrower than ordinary target-disposition validation.
    A current approved convention can discharge an explicit model premise, but
    it must never turn a record/conclusion package or a constructor result into
    a source antecedent.  The caller still decides whether the surrounding
    dependency is semantically non-result-bearing.
    """

    if str(response.get("classification") or "").strip() != "approved_source_convention":
        return ["accepted convention antecedent must be classified approved_source_convention"]
    if item.get("kind") == "record_conclusion_input":
        return [
            "approved_source_convention cannot credit a conclusion-bearing record or result package"
        ]
    if item.get("conclusion_fields"):
        return [
            "approved_source_convention cannot credit a conclusion-bearing record or result package"
        ]
    for field in (
        "valid_constructors",
        "conditional_constructors",
        "rejected_constructors",
    ):
        if item.get(field):
            return [
                "approved_source_convention cannot credit a constructor-derived input or result"
            ]
    if isinstance(item.get(RECURSIVE_FIELD_EXPLICIT_PARENT_ROUTE_FIELD), Mapping):
        return recursive_field_target_disposition_errors(
            item,
            response,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            administrative_projection_rebind=administrative_projection_rebind,
        )
    return source_input_target_disposition_errors(
        item,
        response,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
    )


def source_input_target_disposition_errors(
    item: Mapping[str, object],
    response: Mapping[str, object],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    status: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
    historical_receipt_only: bool = False,
) -> list[str]:
    """Validate source-credit classifications on boundary/conclusion inputs.

    ``validated_source_assumption`` is archival literal credit unless its
    declared target disposition explicitly switches it to an approved corrected
    target.  New convention/corrected-condition classifications are stronger:
    each must echo the exact generated association and the relevant current
    ledger/target pin.  This makes a changed source target invalidate input
    credit without relying on any Lean identifier spelling.
    """

    classification = str(response.get("classification") or "").strip()
    if response_claims_configured_assumption_formalization_regularity(response):
        if historical_receipt_only:
            return [
                "archived receipt replay cannot validate a configured-assumption "
                "formalization regularity without its current structural ledger"
            ]
        return configured_assumption_formalization_regularity_response_errors(
            item,
            response,
            context=configured_assumption_formalization_regularity_context,
        )
    if (
        not historical_receipt_only
        and
        classification == "approved_external_boundary"
        and str(status or "").strip() in FULL_CLOSEOUT_STATUSES
    ):
        return [
            "approved_external_boundary is partial-only and cannot credit a full-closeout source-record input"
        ]

    (
        association,
        identities,
        corrected_items,
        errors,
        has_association,
        rebind_binding,
    ) = (
        _source_contract_association_context(
            item,
            statement_map,
            administrative_projection_rebind=administrative_projection_rebind,
            historical_receipt_only=historical_receipt_only,
        )
    )
    response = _rebound_response_transport(response, rebind_binding)
    if classification not in INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
        return errors if has_association and errors else []
    if not has_association:
        if classification == "validated_source_assumption":
            # Historical/unrouted source assumptions remain subject to the
            # ordinary exact-locator gate. This stricter lane applies once the
            # generator has an explicit direct semantic-contract route.
            return []
        return [
            f"classification `{classification}` requires a generated source_contract_association"
        ]
    if errors:
        return errors
    assert association is not None

    schema = association.get("schema")
    source_semantic_sha256_by_key: Mapping[str, str] | None = None
    if schema == SEMANTIC_ASSOCIATION_SCHEMA:
        errors.extend(
            _response_semantic_association_errors(
                response,
                association,
                field=SOURCE_CONTRACT_ASSOCIATION_FIELD,
            )
        )
        source_semantic_sha256_by_key = _source_semantic_sha256_by_key(identities)
        if not source_semantic_sha256_by_key:
            errors.append(
                "generated source_contract_association has ambiguous or malformed source semantic identities"
            )
    else:
        expected_keys = {identity["source_key"] for identity in identities}
        errors.extend(_response_source_map_keys(response, expected_keys))
        errors.extend(_response_source_map_item_digest_errors(response, identities))
        response_association_digest = str(
            response.get(SOURCE_CONTRACT_ASSOCIATION_SHA256_FIELD) or ""
        ).strip().lower()
        if response_association_digest != str(
            association.get("association_sha256") or ""
        ).strip().lower():
            errors.append(
                f"{SOURCE_CONTRACT_ASSOCIATION_SHA256_FIELD} must equal the generated source-contract association digest"
            )
    if not _input_source_locator(response):
        errors.append(
            f"classification `{classification}` needs an exact source location/evidence"
        )
    if errors:
        return errors

    disposition = str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
    if disposition not in SOURCE_TARGET_DISPOSITIONS:
        return [
            f"{SOURCE_TARGET_DISPOSITION_FIELD} must be one of: "
            + ", ".join(sorted(SOURCE_TARGET_DISPOSITIONS))
        ]
    if historical_receipt_only and statement_map is None and (
        classification == "approved_corrected_condition"
        or disposition == "approved_corrected_target"
    ):
        return [
            "archived receipt replay cannot validate corrected-target credit without "
            "a full archived source-map target snapshot"
        ]
    if classification == "approved_source_convention":
        if disposition != "approved_source_convention":
            return [
                "approved_source_convention must use source_target_disposition approved_source_convention"
            ]
        if corrected_items:
            return [
                "approved_source_convention cannot replace an approved corrected target for "
                + ", ".join(sorted(corrected_items))
            ]
        errors = _model_convention_errors(response, source_proof_fidelity)
        if (
            response.get("governing_defect_ids")
            or response.get(_TARGET_SHA256_FIELD)
            or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
        ):
            errors.append(
                "approved_source_convention cannot carry corrected-target defect or digest metadata"
            )
        return errors
    if classification == "approved_corrected_condition":
        if disposition != "approved_corrected_target":
            return [
                "approved_corrected_condition must use source_target_disposition approved_corrected_target"
            ]
        if not corrected_items:
            return [
                "approved_corrected_condition requires an associated corrected_source_statement target"
            ]
        errors = _corrected_target_errors(
            response,
            corrected_items,
            source_proof_fidelity,
            source_semantic_sha256_by_key=source_semantic_sha256_by_key,
        )
        if response.get("model_convention_ids"):
            errors.extend(_model_convention_errors(response, source_proof_fidelity))
        return errors

    # A source assumption label can still review an approved replacement, but
    # only if the response explicitly names that replacement.  A literal
    # disposition is never source-creditable for a corrected source item.
    if disposition == "approved_source_convention":
        return [
            "validated_source_assumption cannot use approved_source_convention; use classification approved_source_convention"
        ]
    if disposition == "literal_source_match":
        if corrected_items:
            return [
                "validated_source_assumption cannot claim archival literal source credit for corrected source item(s) "
                + ", ".join(sorted(corrected_items))
                + "; use approved_corrected_condition or explicitly state approved_corrected_target"
            ]
        if (
            response.get("model_convention_ids")
            or response.get("governing_defect_ids")
            or response.get(_TARGET_SHA256_FIELD)
            or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
        ):
            return [
                "literal_source_match cannot carry convention or corrected-target metadata"
            ]
        return []
    if not corrected_items:
        return [
            "approved_corrected_target on validated_source_assumption requires an associated corrected_source_statement target"
        ]
    return _corrected_target_errors(
        response,
        corrected_items,
        source_proof_fidelity,
        source_semantic_sha256_by_key=source_semantic_sha256_by_key,
    )


def semantic_target_disposition_errors(
    item: Mapping[str, object],
    response: Mapping[str, object],
    *,
    statement_map: Mapping[str, object] | None,
    source_proof_fidelity: Mapping[str, object] | None,
    validated_vocabulary_binding_source_item_ids: object | None = None,
    validated_vocabulary_direct_route_source_item_ids: object | None = None,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    historical_receipt_only: bool = False,
) -> list[str]:
    """Validate a per-dimension source target disposition.

    This is intentionally a semantic provenance check, not a Lean route check.
    It starts with an explicit generated source-map identity, follows the
    current source map, and then follows the current source-proof ledger when
    a convention or correction is claimed.  An item without such an identity
    is outside this narrow lane and remains subject to the ordinary expanded
    surface checks.
    """

    raw_association, _ = _semantic_source_association(item)
    association: Mapping[str, object] | None = raw_association
    rebind_binding: Mapping[str, object] | None = None
    if isinstance(raw_association, Mapping):
        association, rebind_binding = _rebound_association_and_binding(
            raw_association, administrative_projection_rebind
        )
    response = _rebound_response_transport(response, rebind_binding)
    direct_source_statement_association = isinstance(
        item.get("source_statement_association"), Mapping
    )
    statement_source_component_association = isinstance(
        item.get(STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD), Mapping
    )
    identities, errors, has_association = _explicit_source_identities(
        item,
        association_override=association,
    )
    disposition = str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
    if not has_association:
        verdict = str(response.get("verdict") or "").strip()
        if disposition or verdict in set(SOURCE_TARGET_MATCH_VERDICTS.values()):
            return [
                "literal/convention/corrected target credit requires generated "
                "explicit source-map identities"
            ]
        return []
    if not identities:
        return errors
    if disposition not in SOURCE_TARGET_DISPOSITIONS:
        return errors + [
            f"{SOURCE_TARGET_DISPOSITION_FIELD} must be one of: "
            + ", ".join(sorted(SOURCE_TARGET_DISPOSITIONS))
        ]
    assert association is not None

    schema = _association_schema(
        association,
        field="semantic source association",
        errors=errors,
    )
    reviewed_qualified_declaration = ""
    statement_component_identity: Mapping[str, object] | None = None
    if statement_source_component_association:
        (
            statement_component_identity,
            statement_component_errors,
        ) = _statement_source_component_association_errors(association)
        errors.extend(statement_component_errors)
    if schema == SEMANTIC_ASSOCIATION_SCHEMA:
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, Mapping):
            errors.append(
                "generated semantic source association lacks reviewed_declaration_identity"
            )
        else:
            reviewed_qualified_declaration = str(
                reviewed_identity.get("qualified_declaration") or ""
            ).strip()
            item_qualified_declaration = str(
                item.get("qualified_declaration") or ""
            ).strip()
            if (
                item_qualified_declaration
                and reviewed_qualified_declaration != item_qualified_declaration
            ):
                errors.append(
                    "generated semantic source association reviewed declaration does not match the current semantic item"
                )

    corrected_items: dict[str, Mapping[str, object]] = {}
    if not historical_receipt_only or statement_map is not None:
        map_items, map_errors = _source_map_items(statement_map)
        errors.extend(map_errors)
        for identity in identities:
            source_key = identity["source_key"]
            source_item = map_items.get(source_key)
            if source_item is None:
                errors.append(
                    f"generated source-map identity `{source_key}` is absent from current paper_statement_map.json"
                )
                continue
            if _normalized_text(source_item.get("source_location")) != identity["source_location"]:
                errors.append(
                    f"generated source-map identity `{source_key}` no longer matches the current source_location"
                )
            if schema == SEMANTIC_ASSOCIATION_SCHEMA:
                supplied_source_map_digest = str(
                    identity.get("source_map_item_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(supplied_source_map_digest):
                    errors.append(
                        f"generated source-map identity `{source_key}` has no valid source_map_item_sha256"
                    )
                elif (
                    source_record_source_item_record_sha256(source_item)
                    != supplied_source_map_digest
                ):
                    errors.append(
                        f"generated source-map identity `{source_key}` no longer matches the current source-map item SHA-256"
                    )
                supplied_source_semantic_digest = str(
                    identity.get(SOURCE_SEMANTIC_SHA256_FIELD) or ""
                ).strip().lower()
                expected_source_semantic_digest = (
                    source_record_source_item_semantic_sha256(
                        dict(source_item), ""
                    )
                )
                if supplied_source_semantic_digest != expected_source_semantic_digest:
                    errors.append(
                        f"generated source-map identity `{source_key}` no longer matches the current source semantic SHA-256"
                    )
            if (
                str(source_item.get("coverage_status") or "").strip().lower()
                == CORRECTED_SOURCE_STATEMENT_STATUS
            ):
                corrected_items[source_key] = source_item

    if statement_component_identity is not None:
        # The parent item authenticates bytes, context, and ledger scope only.
        # It cannot turn a component into a corrected target merely because a
        # sibling or parent presentation has correction metadata.
        corrected_items = {}

    source_semantic_sha256_by_key: Mapping[str, str] | None = None
    if schema == SEMANTIC_ASSOCIATION_SCHEMA:
        errors.extend(
            _schema_two_semantic_association_errors(
                association,
                identities,
                reviewed_qualified_declaration=reviewed_qualified_declaration,
                field="semantic source association",
            )
        )
        errors.extend(
            _response_semantic_association_errors(
                response,
                association,
                field="semantic source association",
            )
        )
        source_semantic_sha256_by_key = _source_semantic_sha256_by_key(identities)
        if not source_semantic_sha256_by_key:
            errors.append(
                "generated semantic source association has ambiguous or malformed source semantic identities"
            )
    else:
        expected_keys = {identity["source_key"] for identity in identities}
        errors.extend(_response_source_map_keys(response, expected_keys))
    authenticated_statement_review = (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        and str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    )
    if direct_source_statement_association and not authenticated_statement_review:
        errors.extend(
            _explicit_direct_source_statement_association_errors(
                association,
                identities,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                validated_vocabulary_binding_source_item_ids=(
                    validated_vocabulary_binding_source_item_ids
                ),
                validated_vocabulary_direct_route_source_item_ids=(
                    validated_vocabulary_direct_route_source_item_ids
                ),
                reviewed_qualified_declaration=reviewed_qualified_declaration,
                historical_receipt_only=historical_receipt_only,
            )
        )
    if errors:
        # Do not treat a malformed/stale source association as a literal source
        # match merely because the response chose the literal verdict.
        return errors

    if statement_component_identity is not None:
        component_disposition = statement_component_identity.get(
            "source_target_disposition"
        )
        component_disposition = (
            component_disposition
            if isinstance(component_disposition, Mapping)
            else {}
        )
        component_convention_pins = statement_component_identity.get(
            "source_model_convention_pins"
        )
        expected_component_disposition = (
            "approved_source_convention"
            if isinstance(component_convention_pins, Mapping)
            else "literal_source_match"
        )
        if disposition != expected_component_disposition:
            return [
                "semantic response source_target_disposition does not match the "
                "authenticated statement source-component target scope"
            ]

    # A successful semantic-model verdict must name the target it matched.
    # Leaving matches_source_model on a correction would make dashboards and
    # downstream readers see archival-source credit even when the structured
    # disposition says otherwise. Open or inapplicable dimensions retain their
    # ordinary verdicts because they do not claim a successful source match.
    verdict = str(response.get("verdict") or "").strip()
    expected_verdict = SOURCE_TARGET_MATCH_VERDICTS[disposition]
    if verdict not in {
        expected_verdict,
        "not_applicable",
        "mismatch_or_open",
        "documented_partial_boundary",
    }:
        errors.append(
            f"successful disposition {disposition!r} must use semantic verdict "
            f"{expected_verdict!r}, not {verdict or 'missing'!r}"
        )

    if historical_receipt_only and statement_map is None and disposition == "approved_corrected_target":
        return errors + [
            "archived receipt replay cannot validate corrected-target credit without "
            "a full archived source-map target snapshot"
        ]

    if disposition == "literal_source_match":
        if corrected_items:
            errors.append(
                "literal_source_match cannot discharge source-map identity/identities "
                + ", ".join(sorted(corrected_items))
                + " because their archival statements have approved corrected targets; "
                "use approved_corrected_target"
            )
            return errors
        if response.get("model_convention_ids"):
            errors.append(
                "literal_source_match cannot also cite model_convention_ids; use approved_source_convention"
            )
            return errors
        if (
            response.get("governing_defect_ids")
            or response.get(_TARGET_SHA256_FIELD)
            or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
        ):
            errors.append(
                "literal_source_match cannot carry corrected-target defect or digest metadata"
            )
        return errors

    if disposition == "approved_source_convention":
        if corrected_items:
            errors.append(
                "approved_source_convention cannot replace an approved corrected target for "
                + ", ".join(sorted(corrected_items))
                + "; use approved_corrected_target"
            )
            return errors
        if (
            response.get("governing_defect_ids")
            or response.get(_TARGET_SHA256_FIELD)
            or response.get(_TARGET_SEMANTIC_SHA256_FIELD)
        ):
            errors.append(
                "approved_source_convention cannot carry corrected-target defect or digest metadata"
            )
            return errors
        errors.extend(_model_convention_errors(response, source_proof_fidelity))
        if statement_component_identity is not None:
            component_convention_pins = statement_component_identity.get(
                "source_model_convention_pins"
            )
            permitted_ids = (
                {
                    str(value).strip()
                    for value in component_convention_pins.get(
                        "model_convention_ids", []
                    )
                    if str(value).strip()
                }
                if isinstance(component_convention_pins, Mapping)
                else set()
            )
            response_ids = {
                str(value).strip()
                for value in response.get("model_convention_ids", [])
                if str(value).strip()
            } if isinstance(response.get("model_convention_ids"), list) else set()
            if not response_ids or not response_ids.issubset(permitted_ids):
                errors.append(
                    "approved source convention cites a convention outside the "
                    "generated statement source-component scope"
                )
        return errors

    # The enum check above makes this the approved_corrected_target branch.
    if not corrected_items:
        errors.append(
            "approved_corrected_target requires at least one associated source-map item "
            "with coverage_status corrected_source_statement"
        )
        return errors
    errors.extend(
        _corrected_target_errors(
            response,
            corrected_items,
            source_proof_fidelity,
            source_semantic_sha256_by_key=source_semantic_sha256_by_key,
        )
    )
    if response.get("model_convention_ids"):
        errors.extend(_model_convention_errors(response, source_proof_fidelity))
    return errors
