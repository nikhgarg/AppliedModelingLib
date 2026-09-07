#!/usr/bin/env python3
"""Canonical semantic descriptors for raw source-record obligations.

This module owns the transport-independent grouping of generated raw audit
items. It contains no historical overlay reader or writer. Current closeout,
semantic reuse and historical readers all consume this
single descriptor authority.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any, Mapping

try:
    from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from scripts.source_record_target_disposition import (
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from source_record_target_disposition import (
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
    )

_SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")

SOURCE_RECORD_V10_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION

SOURCE_RECORD_OBLIGATION_DESCRIPTOR_SCHEMA = 1

PRESENTATION_NORMALIZER_SCHEMA = 1

_NAVIGATION_FIELDS = frozenset(
    {
        "row",
        "judgment_key",
        "binder",
        "reviewed_binder",
        "lean_source_declaration",
        "effective_lean_source_declaration",
        "qualified_declaration",
        "effective_qualified_declaration",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identities",
        "reviewed_elaborated_signature_identity",
        "paper_statement_map_sha256",
        "source_contract_association",
        "semantic_contract_source_association",
        "source_statement_association",
        "statement_source_component_association",
        "semantic_contract_group",
        "recursive_field_explicit_parent_route",
        "source_file",
        "source_location",
        "source_key",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "association_sha256",
        "paired_qualified_declaration",
        "declaration",
        "local_type_head",
        "record",
        "record_aliases",
        "structure",
        "field",
        "path",
        "line",
        "names",
        "required_check",
        "semantic_context_requirements_sha256",
    }
)

_RECEIPT_ONLY_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        "source_record_item_semantic_context_requirements_sha256",
        "source_record_item_source_proof_fidelity_records_sha256",
    }
)

_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "statement_source_component_association",
    "semantic_contract_group",
)

_ASSOCIATION_NAME_FIELDS = frozenset(
    {
        "qualified_declaration",
        "paired_qualified_declaration",
        "semantic_model_judgment_key",
        "evidence_declaration",
        "spec_declaration",
        "row",
        "source_key",
        "source_location",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "association_sha256",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identity",
        "reviewed_elaborated_signature_identities",
    }
)

def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()

def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""

def _raw_audit_error(payload: object, *, paper: str, label: str) -> str:
    if not isinstance(payload, Mapping):
        return f"{label} raw audit is not an object"
    if payload.get("paper") != paper:
        return f"{label} raw audit does not record the requested paper"
    if str(payload.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the v10 source-record prompt"
    if (
        str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return f"{label} raw audit does not use the v10 source-record policy"
    if not _sha256(payload.get("source_record_audit_sha256")):
        return f"{label} raw audit has no aggregate source-record receipt"
    receipt_error = source_record_audit_receipt_error(payload)
    if receipt_error:
        return f"{label} raw audit receipt is invalid: {receipt_error}"
    metadata_error = source_record_raw_reusable_item_metadata_error(
        payload, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    )
    if metadata_error:
        return f"{label} raw audit item metadata is invalid: {metadata_error}"
    lean_check = payload.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return f"{label} raw audit lacks a successful Lean check"
    if int(payload.get("recursion_failure_count") or 0) != 0:
        return f"{label} raw audit has recursion failures"
    target_route_error = source_record_target_route_error(payload)
    if target_route_error:
        return f"{label} raw audit has invalid semantic target routing: {target_route_error}"
    return ""

def _canonical_projection_sort_key(value: object) -> str:
    """Return a deterministic order key for a projected unordered inventory."""

    return json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    )

def _complete_review_alias_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project a complete thin-alias trace without its route spellings.

    The generated elaborated-signature and source-association receipts bind the
    actual reviewed endpoint.  Once the alias resolver has completed, the
    declaration/FQN strings, local reference spelling, and source locations
    merely explain how that endpoint was found.  Retain the ordered alias-kind
    trace, because a changed route shape still warrants a fresh review.

    Incomplete or unfamiliar routes deliberately return their raw surface:
    the current generator has no name-free identity for an unresolved target.
    """

    blocked_routes = value.get("blocked_routes")
    steps = value.get("steps")
    if (
        value.get("schema") != 1
        or value.get("complete") is not True
        or not isinstance(blocked_routes, list)
        or blocked_routes
        or not isinstance(steps, list)
        or not all(isinstance(step, Mapping) for step in steps)
    ):
        return dict(value)

    known_route_fields = {
        "schema",
        "reviewed_declaration",
        "effective_declaration",
        "alias_present",
        "complete",
        "effective_kind",
        "steps",
        "blocked_routes",
    }
    known_step_fields = {"from", "reference", "to", "target_kind", "source_file", "line"}
    projected_steps: list[dict[str, object]] = []
    for step in steps:
        assert isinstance(step, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in step.items()
            if str(key) not in known_step_fields
        }
        projected_step: dict[str, object] = {
            "target_kind": step.get("target_kind"),
        }
        if extras:
            # Unknown generator fields are semantic until deliberately
            # classified, so an extension remains fail-closed by default.
            projected_step["unknown_fields"] = extras
        projected_steps.append(projected_step)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_route_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "schema": value.get("schema"),
        "alias_present": value.get("alias_present"),
        "complete": value.get("complete"),
        "effective_kind": value.get("effective_kind"),
        "steps": projected_steps,
        "blocked_routes": [],
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected

def _complete_proposition_alias_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project complete transparent proposition-alias steps without FQNs.

    ``expanded_type`` remains the reviewed proposition.  A transparent step's
    declaration/location is explanatory once that expansion is available, but
    its kind and ordered count remain part of the review surface.  Any blocked
    or malformed expansion has no equivalent canonical endpoint artifact, so
    it retains its raw presentation and cannot gain reuse from this helper.
    """

    blocked_routes = value.get("blocked_routes")
    steps = value.get("transparent_steps")
    if (
        not isinstance(blocked_routes, list)
        or blocked_routes
        or not isinstance(steps, list)
        or not all(isinstance(step, Mapping) for step in steps)
        or "expanded_type" not in value
    ):
        return dict(value)

    known_route_fields = {"expanded_type", "transparent_steps", "blocked_routes"}
    known_step_fields = {"declaration", "kind", "source_file", "line"}
    projected_steps: list[dict[str, object]] = []
    for step in steps:
        assert isinstance(step, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in step.items()
            if str(key) not in known_step_fields
        }
        projected_step: dict[str, object] = {"kind": step.get("kind")}
        if extras:
            projected_step["unknown_fields"] = extras
        projected_steps.append(projected_step)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_route_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "expanded_type": value.get("expanded_type"),
        "transparent_steps": projected_steps,
        "blocked_routes": [],
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected

def _complete_terminal_dependency_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project a complete transparent term closure without declaration paths.

    A transparent dependency has existing content-bearing artifacts: its body
    digest, typed surfaces, semantic flags/fragments, and relevance status.
    Its declaration name, source location, declaration-text digest, and
    dependency-chain names are presentation/navigation data.  Do not normalize
    incomplete closures or opaque local heads: those lack a canonical local
    identity and must remain fail-closed.
    """

    definitions = value.get("transparent_definitions")
    incomplete_reasons = value.get("incomplete_reasons")
    unexpanded_heads = value.get("unexpanded_local_term_heads")
    if (
        value.get("schema") != 1
        or value.get("scan_complete") is not True
        or not isinstance(definitions, list)
        or not all(isinstance(node, Mapping) for node in definitions)
        or not isinstance(incomplete_reasons, list)
        or incomplete_reasons
        or not isinstance(unexpanded_heads, list)
        or unexpanded_heads
    ):
        return dict(value)

    known_surface_fields = {
        "schema",
        "scan_complete",
        "scan_limits",
        "incomplete_reasons",
        "terminal_result_semantic_construct_flags",
        "terminal_result_semantic_fragments",
        "transparent_definitions",
        "unexpanded_local_term_heads",
        "semantic_construct_flags",
    }
    known_node_fields = {
        "declaration",
        "kind",
        "source_file",
        "line",
        "declaration_sha256",
        "body_sha256",
        "parameter_types",
        "result_type",
        "semantic_construct_flags",
        "semantic_fragments",
        "body_surface_inspectable",
        "direct_local_dependencies",
        "dependency_chain",
        "semantic_relevant",
    }
    projected_definitions: list[dict[str, object]] = []
    for node in definitions:
        assert isinstance(node, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in node.items()
            if str(key) not in known_node_fields
        }
        projected_node: dict[str, object] = {
            "kind": node.get("kind"),
            "body_sha256": node.get("body_sha256"),
            "parameter_types": _semantic_projection(
                node.get("parameter_types"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "result_type": _semantic_projection(
                node.get("result_type"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "semantic_construct_flags": _semantic_projection(
                node.get("semantic_construct_flags"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "semantic_fragments": _semantic_projection(
                node.get("semantic_fragments"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "body_surface_inspectable": node.get("body_surface_inspectable"),
            "semantic_relevant": node.get("semantic_relevant"),
        }
        if extras:
            projected_node["unknown_fields"] = extras
        projected_definitions.append(projected_node)
    projected_definitions.sort(key=_canonical_projection_sort_key)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_surface_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "schema": value.get("schema"),
        "scan_complete": value.get("scan_complete"),
        "scan_limits": _semantic_projection(
            value.get("scan_limits"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "incomplete_reasons": [],
        "terminal_result_semantic_construct_flags": _semantic_projection(
            value.get("terminal_result_semantic_construct_flags"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "terminal_result_semantic_fragments": _semantic_projection(
            value.get("terminal_result_semantic_fragments"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "transparent_definitions": projected_definitions,
        "unexpanded_local_term_heads": [],
        "semantic_construct_flags": _semantic_projection(
            value.get("semantic_construct_flags"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected

def _semantic_projection(
    value: object,
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool = False,
    normalize_presentation_routes: bool = False,
) -> object:
    """Project one generated obligation without receipt transport.

    Input/field dispositions need the local type/record/source surface, not an
    enclosing theorem's conclusion.  A semantic-model item is the opposite: it
    is the result-level review lane, so retain its full expanded surface.

    Alias/dependency route strings are normalized only after the caller has an
    independent semantic source or full-result endpoint identity.  Without
    that identity, their display route remains a fail-closed discriminator;
    the current generator has no canonical local binder/field atom to replace
    it.
    """

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if normalized in _NAVIGATION_FIELDS or normalized in _RECEIPT_ONLY_FIELDS:
                continue
            if (
                normalize_presentation_routes
                and normalized == "review_alias_expansion"
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_review_alias_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if (
                normalize_presentation_routes
                and normalized
                in {
                    "proposition_alias_expansion",
                    "subtype_predicate_proposition_alias_expansion",
                }
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_proposition_alias_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if (
                normalize_presentation_routes
                and normalized == "terminal_term_dependency_surface"
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_terminal_dependency_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if omit_recursive_structural_coordinates and normalized == "nested_structures":
                # Recursive field and nested-record spellings are navigation.
                # A generated direct semantic parent receipt is projected
                # separately for the only reusable recursive-field path.
                continue
            if not full_result_surface and normalized in {
                "row_result_type",
                "result_type",
                "result_type_compatibility",
                "reviewed_result_type",
            }:
                continue
            projected[key] = _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                normalize_presentation_routes=normalize_presentation_routes,
            )
        return projected
    if isinstance(value, list):
        return [
            _semantic_projection(
                item,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                normalize_presentation_routes=normalize_presentation_routes,
            )
            for item in value
        ]
    if isinstance(value, tuple):
        return [
            _semantic_projection(
                item,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for item in value
        ]
    return value

def _association_mappings(item: Mapping[str, Any]) -> list[tuple[str, Mapping[str, Any]]]:
    return [
        (field, association)
        for field in _ASSOCIATION_FIELDS
        if isinstance((association := item.get(field)), Mapping)
    ]

def _source_semantic_identities(item: Mapping[str, Any]) -> list[str]:
    identities: set[str] = set()
    for _field, association in _association_mappings(item):
        raw_identities = association.get("source_item_identities")
        if not isinstance(raw_identities, list):
            continue
        for raw_identity in raw_identities:
            if not isinstance(raw_identity, Mapping):
                continue
            digest = _sha256(raw_identity.get("source_semantic_sha256"))
            if digest:
                identities.add(digest)
    return sorted(identities)

def _association_semantic_digests(item: Mapping[str, Any]) -> list[str]:
    return sorted(
        {
            digest
            for _field, association in _association_mappings(item)
            if (digest := _sha256(association.get("semantic_association_sha256")))
        }
    )

def _association_role_projection(value: object) -> object:
    """Keep source-route roles while dropping route/declaration spelling."""

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if normalized in _ASSOCIATION_NAME_FIELDS:
                continue
            if normalized == "source_item_identities":
                identities: set[str] = set()
                if isinstance(raw_value, list):
                    for identity in raw_value:
                        if isinstance(identity, Mapping):
                            digest = _sha256(identity.get("source_semantic_sha256"))
                            if digest:
                                identities.add(digest)
                projected["source_item_semantic_identities"] = sorted(identities)
                continue
            if normalized == "semantic_association_sha256":
                # The full row descriptor retains this source+endpoint pin.
                # Input-local reuse instead retains source content and the
                # route role independently, so a changed theorem result does
                # not erase an unchanged antecedent review.
                continue
            projected[key] = _association_role_projection(raw_value)
        return projected
    if isinstance(value, list):
        return sorted(
            [_association_role_projection(item) for item in value],
            key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(value, tuple):
        return _association_role_projection(list(value))
    return value

def _association_roles(item: Mapping[str, Any]) -> list[dict[str, object]]:
    return sorted(
        [
            {
                "association_field": field,
                "role": _association_role_projection(association),
            }
            for field, association in _association_mappings(item)
        ],
        key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":")),
    )

def _signature_digests(item: Mapping[str, Any]) -> list[str]:
    signatures: list[Mapping[str, Any]] = []
    direct = item.get("reviewed_elaborated_signature_identities")
    if isinstance(direct, list):
        signatures.extend(entry for entry in direct if isinstance(entry, Mapping))
    for _field, association in _association_mappings(item):
        identity = association.get("reviewed_elaborated_signature_identity")
        if isinstance(identity, Mapping):
            signatures.append(identity)
    return sorted(
        {
            digest
            for signature in signatures
            if (digest := _sha256(signature.get("elaborated_signature_sha256")))
        }
    )

def _recursive_field_parent_route_semantic_scope(
    item: Mapping[str, Any],
) -> dict[str, object] | None:
    """Return a name-free direct semantic parent receipt for one field.

    A recursive field cannot receive automatic differential reuse merely
    because its Lean structure, field, or nested-record spelling is stable.
    It needs a generated, locally authenticated direct parent route. This
    projection retains only source semantic identity, source-convention scope,
    semantic classification, and the checked parent association receipt. It
    never uses a record/field chain or declaration/binder spelling to identify
    a match, and performs no global parent lookup.
    """

    route = item.get("recursive_field_explicit_parent_route")
    if not isinstance(route, Mapping):
        return None
    if (
        route.get("schema") != 1
        or str(route.get("inheritance_mode") or "").strip()
        != "explicit_parent_route_and_field_scope"
    ):
        return None
    route_digest = _sha256(route.get("association_sha256"))
    if not route_digest or route_digest != recursive_field_parent_route_record_digest(route):
        return None
    # Require an actual generated route edge, but deliberately do not project
    # the edge's Lean strings into the reusable semantic identity.
    field_chain = route.get("field_chain")
    if not isinstance(field_chain, list) or not field_chain or not all(
        isinstance(link, Mapping) for link in field_chain
    ):
        return None
    field_scope = _sha256(route.get("field_scope_sha256"))
    convention = _sha256(route.get("convention_sha256"))
    if not field_scope or not convention:
        return None
    classifications = route.get("permitted_classifications")
    if not isinstance(classifications, list) or not classifications:
        return None
    classification_values = [
        str(value).strip() for value in classifications if str(value).strip()
    ]
    if (
        len(classification_values) != len(classifications)
        or len(set(classification_values)) != len(classification_values)
    ):
        return None
    identities = route.get("source_item_identities")
    if not isinstance(identities, list) or len(identities) != 1:
        return None
    identity = identities[0]
    if not isinstance(identity, Mapping):
        return None
    source_semantic = _sha256(identity.get("source_semantic_sha256"))
    if not source_semantic:
        return None
    parent_signature = route.get("parent_elaborated_signature_identity")
    parent_association = _sha256(route.get("parent_source_association_sha256"))
    if (
        not isinstance(parent_signature, Mapping)
        or not parent_association
        or parent_association
        != semantic_association_record_digest([source_semantic], parent_signature)
    ):
        return None
    parent_field = str(route.get("parent_association_field") or "").strip()
    parent_role = str(route.get("parent_source_association_role") or "").strip()
    parent_origin = str(route.get("parent_source_association_origin") or "").strip()
    if parent_field == "source_statement_association":
        if (
            parent_role != "direct_source_route"
            or parent_origin != "explicit_source_map_direct_route"
        ):
            return None
    elif parent_field == SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD:
        if (
            parent_role != SOURCE_CLAIM_ATOM_ROUTE_ROLE
            or parent_origin != SOURCE_CLAIM_ATOM_ROUTE_ORIGIN
        ):
            return None
    elif parent_field == "semantic_contract_source_association":
        if parent_role not in {"direct_evidence", "transparent_spec"} or parent_origin:
            return None
    else:
        return None
    if not str(route.get("root_input_type_canonical") or "").strip():
        return None
    return {
        "schema": 1,
        "field_scope_sha256": field_scope,
        "source_item_semantic_sha256": source_semantic,
        "convention_sha256": convention,
        "permitted_classifications": sorted(classification_values),
        "parent_association_kind": parent_field,
        "parent_source_association_role": parent_role,
        "parent_source_association_origin": parent_origin,
        "parent_source_association_sha256": parent_association,
    }

_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA = 1

_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD = (
    "recursive_field_direct_source_domain_parent_contracts"
)

def _optional_source_domain_fingerprint(value: object) -> dict[str, str] | None:
    """Return one explicit optional semantic-context/ledger fingerprint.

    A missing scoped context is materially different from a malformed one.  A
    direct source-domain contract may say that no scoped context applies, but
    it must not silently treat an unfamiliar value as absence.
    """

    text = str(value or "").strip().lower()
    if not text:
        return {"state": "absent"}
    if not _SHA256_RE.fullmatch(text):
        return None
    return {"state": "present", "sha256": text}

def _direct_source_domain_record_input_projection(value: object) -> object:
    """Project a parent record input without its human-facing binder spelling.

    The fully-qualified instantiated input type, elaborated binder atom, and
    every unknown generated field remain.  Display binders, source-text
    spellings, and record-root navigation names are deliberately excluded:
    the generated route's canonical instantiated type selects this binding.
    Retaining an unfamiliar future field keeps this route fail-closed by
    default.
    """

    if isinstance(value, Mapping):
        return {
            str(key): _direct_source_domain_record_input_projection(child)
            for key, child in value.items()
            if str(key).strip().lower()
            not in {"binder_names", "source_type_canonical", "record_roots"}
        }
    if isinstance(value, list):
        return [_direct_source_domain_record_input_projection(child) for child in value]
    if isinstance(value, tuple):
        return [_direct_source_domain_record_input_projection(child) for child in value]
    return value

def _recursive_field_direct_source_domain_parent_contract(
    item: Mapping[str, Any],
    *,
    semantic_model_items: object,
) -> dict[str, object] | None:
    """Return a name-independent direct source-domain contract for one field.

    An explicit recursive-field route proves that the field belongs to a
    source-selected model input.  The parent association's elaborated
    signature necessarily changes when a theorem conclusion changes, even
    when the model input and its source domain do not.  For a *child* review,
    compare the complete parent input-domain surface instead: source-map and
    source-content pins, all parent input domains, the exact instantiated
    record input, scoped context/ledger fingerprints, and the declared field
    scope/convention.  The parent semantic-model row still compares its full
    result surface elsewhere, so this never transports a changed direct result
    review.

    This function deliberately requires a unique current semantic-model
    parent selected by the generated association pin.  It does not look up a
    declaration, source-map key, binder, record, or field by spelling.
    """

    scope = _recursive_field_parent_route_semantic_scope(item)
    route = item.get("recursive_field_explicit_parent_route")
    if scope is None or not isinstance(route, Mapping):
        return None
    if not isinstance(semantic_model_items, list):
        return None

    raw_identities = route.get("source_item_identities")
    if not isinstance(raw_identities, list) or len(raw_identities) != 1:
        return None
    raw_identity = raw_identities[0]
    if not isinstance(raw_identity, Mapping):
        return None
    source_map_item_sha = _sha256(raw_identity.get("source_map_item_sha256"))
    source_semantic_sha = _sha256(raw_identity.get("source_semantic_sha256"))
    if not source_map_item_sha or not source_semantic_sha:
        return None

    parent_association_field = str(
        route.get("parent_association_field") or ""
    ).strip()
    parent_association_pin = _sha256(
        route.get("parent_source_association_sha256")
    )
    parent_role = str(route.get("parent_source_association_role") or "").strip()
    parent_origin = str(
        route.get("parent_source_association_origin") or ""
    ).strip()
    root_input_type = " ".join(
        str(route.get("root_input_type_canonical") or "").split()
    )
    if (
        parent_association_field not in _ASSOCIATION_FIELDS
        or not parent_association_pin
        or not parent_role
        or not root_input_type
    ):
        return None

    candidates: list[dict[str, object]] = []
    for parent in semantic_model_items:
        if not isinstance(parent, Mapping):
            continue
        if str(parent.get("kind") or "").strip() != "semantic_model_comparison":
            continue
        association = parent.get(parent_association_field)
        if not isinstance(association, Mapping):
            continue
        if _sha256(association.get("semantic_association_sha256")) != parent_association_pin:
            continue
        if association.get("schema") != 2:
            continue
        if str(association.get("role") or "").strip() != parent_role:
            continue
        if str(association.get("association_origin") or "").strip() != parent_origin:
            continue
        association_identities = association.get("source_item_identities")
        if not isinstance(association_identities, list) or len(association_identities) != 1:
            continue
        association_identity = association_identities[0]
        if not isinstance(association_identity, Mapping):
            continue
        if (
            _sha256(association_identity.get("source_map_item_sha256"))
            != source_map_item_sha
            or _sha256(association_identity.get("source_semantic_sha256"))
            != source_semantic_sha
        ):
            continue
        signature = association.get("reviewed_elaborated_signature_identity")
        if not isinstance(signature, Mapping):
            continue
        if parent_association_pin != semantic_association_record_digest(
            [source_semantic_sha], signature
        ):
            continue

        expanded_surface = parent.get("expanded_lean_surface")
        if not isinstance(expanded_surface, Mapping):
            continue
        binder_domains = expanded_surface.get("binder_domains")
        if (
            not isinstance(binder_domains, list)
            or not binder_domains
            or not all(isinstance(domain, Mapping) for domain in binder_domains)
        ):
            continue
        raw_bindings = parent.get("record_input_bindings")
        if not isinstance(raw_bindings, list):
            continue
        matching_bindings: list[Mapping[str, Any]] = []
        for binding in raw_bindings:
            if not isinstance(binding, Mapping):
                continue
            binding_type = " ".join(
                str(binding.get("fully_qualified_expanded_type_canonical") or "").split()
            )
            if binding_type == root_input_type:
                matching_bindings.append(binding)
        if len(matching_bindings) != 1:
            continue

        context_fingerprint = _optional_source_domain_fingerprint(
            parent.get("source_record_item_semantic_context_requirements_sha256")
        )
        ledger_fingerprint = _optional_source_domain_fingerprint(
            parent.get("source_record_item_source_proof_fidelity_records_sha256")
        )
        if context_fingerprint is None or ledger_fingerprint is None:
            continue
        candidates.append(
            {
                "schema": _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA,
                "source_item_anchor_pins": [
                    {
                        "source_map_item_sha256": source_map_item_sha,
                        "source_semantic_sha256": source_semantic_sha,
                    }
                ],
                "parent_source_association": {
                    "field": parent_association_field,
                    "role": parent_role,
                    "origin": parent_origin,
                },
                # This is the entire proposition-input domain, deliberately
                # excluding the result surface.  It changes for a changed
                # hypothesis but not for a conclusion-only repair.
                "parent_input_domains": _semantic_projection(
                    binder_domains, full_result_surface=False
                ),
                "parent_record_input": _direct_source_domain_record_input_projection(
                    matching_bindings[0]
                ),
                "parent_semantic_context_requirements": context_fingerprint,
                "parent_source_proof_fidelity_records": ledger_fingerprint,
                "field_scope_sha256": scope["field_scope_sha256"],
                "convention_sha256": scope["convention_sha256"],
                "permitted_classifications": scope["permitted_classifications"],
            }
        )

    # Two candidates may be textually identical, but their coexistence still
    # means the raw semantic parent is not uniquely established.
    return candidates[0] if len(candidates) == 1 else None

def _recursive_field_direct_source_domain_parent_contracts(
    payload: Mapping[str, Any],
) -> dict[int, dict[str, object]]:
    """Index only uniquely authenticated direct parent contracts by raw item.

    The object identity is local in-memory bookkeeping, never a serialized or
    semantic selector.  The resulting contract itself is fully name-free and
    becomes part of the generated group descriptor below.
    """

    raw_fields = payload.get("recursive_field_items")
    semantic_model_items = payload.get("semantic_model_items")
    if not isinstance(raw_fields, list) or not isinstance(semantic_model_items, list):
        return {}
    contracts: dict[int, dict[str, object]] = {}
    for item in raw_fields:
        if not isinstance(item, Mapping):
            continue
        contract = _recursive_field_direct_source_domain_parent_contract(
            item, semantic_model_items=semantic_model_items
        )
        if contract is not None:
            contracts[id(item)] = contract
    return contracts

def source_record_obligation_descriptor(
    item: Mapping[str, Any],
    *,
    section: str,
    recursive_field_direct_source_domain_parent_contract: Mapping[str, object]
    | None = None,
) -> dict[str, object]:
    """Return the semantic comparison descriptor for one generated item.

    This is intentionally public for focused regression tests and audit tools.
    The descriptor is an equality witness, not a key for finding a match.
    """

    full_result_surface = section == "semantic_model_items"
    source_semantic_identities = _source_semantic_identities(item)
    signature_digests = _signature_digests(item)
    # A local input with no source semantic identity has no emitted canonical
    # atom that distinguishes two equal-looking binders. Keep its route data
    # fail-closed rather than merging it merely because a presentation rename
    # erased the only available discriminator. Full result rows can also use
    # their elaborated endpoint signature as that independent identity.
    normalize_presentation_routes = bool(source_semantic_identities) or (
        full_result_surface and bool(signature_digests)
    )
    descriptor: dict[str, object] = {
        "schema": SOURCE_RECORD_OBLIGATION_DESCRIPTOR_SCHEMA,
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "comparison_scope": (
            "full_result_surface" if full_result_surface else "input_or_field_local"
        ),
        "generated_item_kind": str(item.get("kind") or "").strip(),
        "generated_obligation": _semantic_projection(
            item,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=(section == "recursive_field_items"),
            normalize_presentation_routes=normalize_presentation_routes,
        ),
        "source_item_semantic_identities": source_semantic_identities,
        "source_association_roles": _association_roles(item),
        "scoped_semantic_context_requirements_sha256": _sha256(
            item.get("source_record_item_semantic_context_requirements_sha256")
        ),
        "source_proof_fidelity_records_sha256": _sha256(
            item.get("source_record_item_source_proof_fidelity_records_sha256")
        ),
    }
    if full_result_surface:
        descriptor["source_association_semantic_sha256"] = (
            _association_semantic_digests(item)
        )
        descriptor["reviewed_elaborated_signature_sha256"] = signature_digests
    if section == "recursive_field_items":
        if recursive_field_direct_source_domain_parent_contract is not None:
            descriptor["recursive_field_direct_source_domain_parent_contract"] = (
                dict(recursive_field_direct_source_domain_parent_contract)
            )
        else:
            # Preserve the older exact-parent-signature lane when a raw audit
            # lacks the stronger input-domain witness.  It remains safe, just
            # more conservative; no old field approval gains the new route by
            # resemblance.
            descriptor["recursive_field_direct_semantic_parent"] = (
                _recursive_field_parent_route_semantic_scope(item)
            )
    return descriptor

def source_record_obligation_descriptor_sha256(
    item: Mapping[str, Any], *, section: str
) -> str:
    return _canonical_digest(source_record_obligation_descriptor(item, section=section))

def _raw_formalization_scope_descriptor(
    payload: Mapping[str, Any],
) -> dict[str, str]:
    """Bind every differential group to the raw formalization-scope surface.

    Scope is a paper-level semantic boundary rather than an item receipt. A
    local input may look unchanged while its governing scope has changed, so a
    scope refresh must trigger narrow manual review. Preserve the distinction
    between an explicit null scope and a legacy raw audit that omits it.
    """

    if "formalization_scope" not in payload:
        return {"state": "absent"}
    scope = payload.get("formalization_scope")
    if scope is None:
        return {"state": "explicit_null"}
    return {"state": "present", "sha256": _canonical_digest(scope)}

def raw_source_record_obligation_groups(
    payload: Mapping[str, Any],
) -> tuple[dict[str, dict[str, object]], dict[str, str]]:
    """Collect every response group, including aggregate-only raw members."""

    recursive_parent_contracts = (
        _recursive_field_direct_source_domain_parent_contracts(payload)
    )
    grouped: dict[str, list[tuple[str, Mapping[str, Any]]]] = {}
    errors: dict[str, str] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = payload.get(section)
        if raw_items is None:
            continue
        if not isinstance(raw_items, list):
            errors[f"<section:{section}>"] = "raw audit section is not a list"
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                errors[f"<section:{section}>"] = "raw audit contains a non-object item"
                continue
            if source_record_item_is_nonreusable_theorem_facing_mirror(
                section, raw_item
            ):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            if not key:
                # Keyless generated artifacts remain tied to the raw aggregate
                # receipt.  They cannot consume a response and therefore do
                # not belong to a sidecar differential group.
                continue
            grouped.setdefault(key, []).append((section, raw_item))

    groups: dict[str, dict[str, object]] = {}
    for key, members in grouped.items():
        member_descriptors = [
            {
                "section": section,
                "descriptor": source_record_obligation_descriptor(
                    item,
                    section=section,
                    recursive_field_direct_source_domain_parent_contract=(
                        recursive_parent_contracts.get(id(item))
                        if section == "recursive_field_items"
                        else None
                    ),
                ),
            }
            for section, item in members
        ]
        member_descriptors.sort(
            key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":"))
        )
        descriptor: dict[str, object] = {
            "schema": SOURCE_RECORD_OBLIGATION_DESCRIPTOR_SCHEMA,
            "raw_formalization_scope": _raw_formalization_scope_descriptor(payload),
            "members": member_descriptors,
        }
        groups[key] = {
            "descriptor": descriptor,
            "descriptor_sha256": _canonical_digest(descriptor),
            # Retained in memory only.  The serialized overlay carries the
            # descriptor, while a loader must inspect these generated current
            # associations before it can rebind a response provenance pin.
            "raw_members": list(members),
            "semantic_model_items": [
                dict(item)
                for section, item in members
                if section == "semantic_model_items"
            ],
            # Kept only in memory.  The descriptor contains the full
            # name-independent contract, while association-pin transport
            # needs the same derived contract to be recomputed by the loader.
            _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD: {
                id(item): recursive_parent_contracts[id(item)]
                for section, item in members
                if section == "recursive_field_items"
                and id(item) in recursive_parent_contracts
            },
        }
    return groups, errors
