#!/usr/bin/env python3
"""Replay narrow structural repairs for immutable source-record receipts.

The source-record producer deliberately records every theorem-facing input and
then associates it with a whole-statement semantic review.  Two representation
failures can arise without any change to the paper mathematics:

* a grouped direct-evidence/transparent-Spec contract stores member identities
  on the group, while an older consumer compares an input to the group's
  top-level direct-evidence identity first; and
* a source-written transparent Spec omits an implicit binder that the text
  parser cannot reconstruct, although Lean's complete elaborated graphs prove
  that the theorem result and Spec value are the same proposition.

This module repairs only those *structurally demonstrated* cases.  It never
edits, reseals, or copies a raw audit receipt, and it never creates a human
judgment.  Group-member coverage is recomputed directly from the authenticated
raw payload.  The parser fallback additionally requires a small, immutable
full-manifest witness: each embedded manifest is checked against a current
tracked authority entry and the raw configured-row signature/dependency/graph
pins.  Ordinary evidence replay therefore reads a compact fragment rather
than the large ignored manifest carrier.

All predicates are driven by generated roles, declaration-content hashes,
source-contract records, and Lean-owned semantic graphs.  Declaration spelling
is a coordinate only; no suffix, row name, or function name selects a repair.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
import tempfile
import weakref
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports package imports and direct focused CLI execution.
    from scripts.authenticated_manifest_store import (
        AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA,
        _validated_store_entries,
        elaborated_proposition_graph_sha256,
    )
    from scripts.lean_signature_manifest import signature_manifest_digest
    from scripts.source_record_target_disposition import (
        semantic_association_record_digest,
        source_contract_association_record_digest,
    )
    from scripts.source_coverage_scope import (
        source_coverage_mode_from_map,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
        source_record_source_item_supported_identity_sha256s,
    )
    from scripts.obligation_preflight import structural_obligation_preflight
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from authenticated_manifest_store import (  # type: ignore
        AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA,
        _validated_store_entries,
        elaborated_proposition_graph_sha256,
    )
    from lean_signature_manifest import signature_manifest_digest  # type: ignore
    from source_record_target_disposition import (  # type: ignore
        semantic_association_record_digest,
        source_contract_association_record_digest,
    )
    from source_coverage_scope import (  # type: ignore
        source_coverage_mode_from_map,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
        source_record_source_item_supported_identity_sha256s,
    )
    from obligation_preflight import structural_obligation_preflight  # type: ignore


SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_SCHEMA = 3
SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_POLICY_VERSION = (
    "source-record-semantic-contract-revalidation-v3"
)
SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_ARTIFACT_KIND = (
    "source_record_semantic_contract_revalidation"
)
SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_FILENAME = (
    "source_record_semantic_contract_revalidation.json"
)
SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD = (
    "source_record_semantic_contract_revalidation_sha256"
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_GROUP_MEMBER_ERROR_TEMPLATE = (
    "theorem-facing item `{key}` has a source-contract association that does "
    "not resolve to the same generated whole-statement semantic review"
)
_COMPANION_ERROR_TEMPLATE = (
    "semantic-contract companion is not an exact transparent evidence/Spec "
    "structural pair: {evidence} / {spec}"
)
_SOURCE_DECLARED_OPEN_NONRESULT_ERROR_PREFIX = (
    "selected source-coverage item has no explicit direct/Spec Lean route: "
)
_SOURCE_DECLARED_OPEN_NONRESULT_CLASSIFICATION = (
    "source_declared_open_nonresult_observation"
)
_AUTHORITY_ENTRY_FIELDS = frozenset(
    {
        "qualified_declaration",
        "context_id",
        "elaborated_signature_sha256",
        "semantic_dependency_sha256",
        "elaborated_proposition_graph_sha256",
        "manifest_payload_sha256",
        "authority_binding_sha256",
    }
)
_AUTHORITY_CONTEXT_FIELDS = frozenset(
    {
        "context_id",
        "import_module",
        "semantic_dependency_modules",
        "manifest_cache_context_sha256",
    }
)
_V10_DIRECT_ROUTE_RE = re.compile(
    r"^current v10 direct source-map route for fully-qualified declaration "
    r"`([^`]+)` has no generated semantic-contract member identity$"
)
_V10_SELECTED_ITEM_MISSING_RE = re.compile(
    r"^selected source item `([^`]+)` has no exact explicit direct-route declaration$"
)
_V10_SELECTED_ITEM_ROUTE_RE = re.compile(
    r"^selected source item `([^`]+)` routes to `([^`]+)`, which is not an "
    r"exact configured review declaration$"
)
_V10_COVERAGE_ITEM_RE = re.compile(
    r"^selected source-coverage item '([^']+)' (?:routes .+ to '[^']+', which "
    r"is not an exact configured PaperInterface review declaration|atom contract "
    r"companion requires every source-claim atom to route to its one exact evidence "
    r"declaration)$"
)
_V10_SOURCE_ATOM_RE = re.compile(
    r"^source atom `([^`]+)` route `[^`]+` is not an exact configured review "
    r"declaration$"
)
_V10_COMPANION_RE = re.compile(
    r"^semantic-contract companion is not an exact transparent evidence/Spec "
    r"structural pair: (\S+) / (\S+)$"
)


@dataclass(frozen=True, eq=False)
class SemanticContractRevalidationProjection:
    """The only consumer-visible effects of a successful structural replay."""

    suppressed_source_contract_association_errors: frozenset[str]
    suppressed_source_coverage_route_errors: frozenset[str]
    suppressed_expected_input_keys: frozenset[str]
    typed_route_reconciliation_sha256: str = ""


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_json(value: object) -> str:
    try:
        return json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    except (TypeError, ValueError):
        return ""


def _canonical_json_sha256(value: object) -> str:
    encoded = _canonical_json(value)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest() if encoded else ""


def _bytes_sha256(value: bytes | None) -> str:
    return hashlib.sha256(value).hexdigest() if isinstance(value, bytes) else ""


def _json_bytes_match_payload(raw_bytes: bytes | None, payload: object) -> bool:
    """Require a supplied snapshot payload to be the supplied exact bytes."""

    if not isinstance(raw_bytes, bytes):
        return False
    try:
        return json.loads(raw_bytes) == payload
    except (UnicodeDecodeError, json.JSONDecodeError):
        return False


def _typed_route_reconciliation_projection(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    statement_map: object,
    paper_prerequisites: object,
    library_semantic_review: object,
    status_payload: object,
) -> tuple[set[str], set[str], str, str]:
    """Project obsolete v10 route errors through the current typed graph.

    This is deliberately an engine-pair-agnostic reconstruction, not a bridge
    between two named audit versions.  It grants credit only when the current
    schema-2 route graph is structurally complete, every source definition or
    premise is bound by the current semantic-prerequisite ledgers, every result
    atom routes to its explicit proof endpoint, and the raw receipt carries the
    same byte-pinned source artifact.  All semantic judgments and Lean proof
    checks remain independent closeout obligations.
    """

    if not isinstance(statement_map, Mapping) or statement_map.get(
        "semantic_route_schema"
    ) != 2:
        return set(), set(), "", ""
    if raw_audit.get("paper") != paper:
        return set(), set(), "", "typed route reconciliation raw receipt belongs to another paper"
    preflight = structural_obligation_preflight(
        statement_map,
        paper=paper,
        paper_prerequisites=paper_prerequisites,
        library_semantic_review=library_semantic_review,
        require_theorem_endpoints=True,
        require_source_spec_correspondence=False,
    )
    if not preflight.current or preflight.route_set is None:
        detail = "; ".join(preflight.errors[:8])
        if len(preflight.errors) > 8:
            detail += f"; ... ({len(preflight.errors) - 8} more)"
        return set(), set(), "", "typed route reconciliation preflight failed: " + detail
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    source_identities = (
        fingerprint.get("source_artifact_identities")
        if isinstance(fingerprint, Mapping)
        else None
    )
    raw_source_sha256s = {
        _sha256(identity.get("sha256"))
        for identity in source_identities
        if isinstance(identity, Mapping)
        and str(identity.get("status") or "present").strip() == "present"
    } if isinstance(source_identities, list) else set()
    if preflight.source_artifact_sha256 not in raw_source_sha256s:
        return set(), set(), "", (
            "typed route reconciliation source artifact disagrees with the raw receipt"
        )

    source_item_ids = {
        route.source_item_id for route in preflight.route_set.routes
    }
    declarations: set[str] = set()
    semantic_pairs: set[tuple[str, str]] = set()
    for route in preflight.route_set.routes:
        declarations.update(route.semantic_declarations)
        declarations.update(
            value
            for value in (
                route.spec_declaration,
                route.evidence_declaration,
                route.semantic_review_declaration,
            )
            if value
        )
        if route.evidence_declaration and route.spec_declaration:
            semantic_pairs.add(
                (route.evidence_declaration, route.spec_declaration)
            )
    review_surface = (
        status_payload.get("review_surface")
        if isinstance(status_payload, Mapping)
        else None
    )
    proof_pairs = (
        review_surface.get("proposition_spec_proofs")
        if isinstance(review_surface, Mapping)
        else None
    )
    if not isinstance(proof_pairs, Mapping):
        return set(), set(), "", (
            "typed route reconciliation status has no proposition_spec_proofs map"
        )
    for route in preflight.route_set.routes:
        if not route.spec_declaration or not route.evidence_declaration:
            continue
        spec_short = route.spec_declaration.rsplit(".", maxsplit=1)[-1]
        evidence_short = route.evidence_declaration.rsplit(".", maxsplit=1)[-1]
        if str(proof_pairs.get(spec_short) or "").strip() != evidence_short:
            return set(), set(), "", (
                "typed route reconciliation status does not bind "
                f"{route.spec_declaration} to {route.evidence_declaration}"
            )
    atom_coordinates: set[str] = set()
    raw_items = statement_map.get("items")
    if isinstance(raw_items, Mapping):
        for source_item_id, raw_item in raw_items.items():
            atoms = raw_item.get("source_claim_atoms") if isinstance(raw_item, Mapping) else None
            if not isinstance(atoms, list):
                continue
            for atom in atoms:
                atom_id = str(atom.get("id") or "").strip() if isinstance(atom, Mapping) else ""
                if atom_id:
                    atom_coordinates.add(f"{source_item_id}:{atom_id}")

    def is_obsolete_v10_route_error(error: object) -> bool:
        if not isinstance(error, str):
            return False
        match = _V10_DIRECT_ROUTE_RE.fullmatch(error)
        if match:
            return match.group(1) in declarations
        match = _V10_SELECTED_ITEM_MISSING_RE.fullmatch(error)
        if match:
            return match.group(1) in source_item_ids
        match = _V10_SELECTED_ITEM_ROUTE_RE.fullmatch(error)
        if match:
            return match.group(1) in source_item_ids
        match = _V10_COVERAGE_ITEM_RE.fullmatch(error)
        if match:
            return match.group(1) in source_item_ids
        prefix = _SOURCE_DECLARED_OPEN_NONRESULT_ERROR_PREFIX
        if error.startswith(prefix):
            return error[len(prefix):] in source_item_ids
        match = _V10_SOURCE_ATOM_RE.fullmatch(error)
        if match:
            return match.group(1) in atom_coordinates
        match = _V10_COMPANION_RE.fullmatch(error)
        return bool(match and (match.group(1), match.group(2)) in semantic_pairs)

    association_errors = {
        error
        for error in raw_audit.get("source_contract_association_errors") or []
        if is_obsolete_v10_route_error(error)
    }
    coverage_errors = {
        error
        for error in raw_audit.get("source_coverage_route_errors") or []
        if is_obsolete_v10_route_error(error)
    }
    reconciliation_sha256 = _canonical_json_sha256(
        {
            "schema": 1,
            "paper": paper,
            "source_artifact_sha256": preflight.source_artifact_sha256,
            "structural_preflight_sha256": preflight.structural_preflight_sha256,
            "paper_semantic_prerequisites_sha256": _canonical_json_sha256(
                paper_prerequisites
            ),
            "library_semantic_review_sha256": _canonical_json_sha256(
                library_semantic_review
            ),
            "proposition_spec_proofs": dict(
                sorted((str(key), str(value)) for key, value in proof_pairs.items())
            ),
        }
    )
    return association_errors, coverage_errors, reconciliation_sha256, ""


def semantic_contract_revalidation_artifact_path(paper_dir: Path) -> Path:
    """Return the fixed, paper-local optional witness path."""

    return paper_dir / "audit" / SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_FILENAME


def _read_json_bytes(path: Path) -> tuple[dict[str, Any] | None, bytes | None, str]:
    try:
        raw = path.read_bytes()
    except OSError as error:
        if isinstance(error, FileNotFoundError):
            return None, None, ""
        return None, None, f"could not read {path}: {error}"
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        return None, raw, f"{path} is not valid JSON: {error}"
    if not isinstance(payload, dict):
        return None, raw, f"{path} is not a JSON object"
    return payload, raw, ""


def _source_record_digest(raw: Mapping[str, Any], field: str) -> str:
    return _sha256(raw.get(field))


def _identity(value: object, *, qualified: str | None = None) -> tuple[str, str] | None:
    if not isinstance(value, Mapping):
        return None
    declaration = str(value.get("qualified_declaration") or "").strip()
    digest = _sha256(value.get("declaration_sha256"))
    if not declaration or not digest or (qualified is not None and declaration != qualified):
        return None
    return declaration, digest


def _signature_identity(
    value: object, *, qualified: str | None = None, require_dependency: bool = True
) -> tuple[str, str, str] | None:
    if not isinstance(value, Mapping):
        return None
    declaration = str(value.get("qualified_declaration") or "").strip()
    signature = _sha256(value.get("elaborated_signature_sha256"))
    dependency = _sha256(value.get("semantic_dependency_sha256"))
    if (
        not declaration
        or not signature
        or (require_dependency and not dependency)
        or (qualified is not None and declaration != qualified)
    ):
        return None
    return declaration, signature, dependency


def _item_signature_identity(
    item: Mapping[str, Any], *, qualified: str
) -> tuple[str, str, str] | None:
    """Select one exact signature record for one reviewed declaration.

    A type-valued result occurrence can retain signatures for both a direct
    theorem and its transparent Spec.  Its source-contract association names
    the reviewed member, so select by that explicit identity rather than
    rejecting the whole occurrence for carrying another generated signature.
    """

    raw_signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list):
        return None
    matches = [
        signature
        for raw_signature in raw_signatures
        if (
            isinstance(raw_signature, Mapping)
            and (
                signature := _signature_identity(
                    raw_signature, qualified=qualified
                )
            )
            is not None
        )
    ]
    return matches[0] if len(matches) == 1 else None


def _source_contract_identities(
    value: object, *, evidence: str, spec: str, evidence_mode: str = "proves"
) -> tuple[list[dict[str, Any]], list[str]] | None:
    """Validate exact current source-contract records without route heuristics."""

    if not isinstance(value, list) or not value:
        return None
    records: list[dict[str, Any]] = []
    source_keys: set[str] = set()
    semantic_digests: set[str] = set()
    for raw_record in value:
        if not isinstance(raw_record, Mapping):
            return None
        record = dict(raw_record)
        source_key = str(record.get("source_key") or "").strip()
        map_digest = _sha256(record.get("source_map_item_sha256"))
        semantic_digest = _sha256(record.get("source_semantic_sha256"))
        contract = record.get("semantic_contract")
        if (
            not source_key
            or source_key in source_keys
            or not map_digest
            or not semantic_digest
            or semantic_digest in semantic_digests
            or not isinstance(contract, Mapping)
            or str(contract.get("evidence_declaration") or "").strip() != evidence
            or str(contract.get("spec_declaration") or "").strip() != spec
            or str(contract.get("evidence_mode") or "").strip() != evidence_mode
            or not str(contract.get("semantic_shape") or "").strip()
        ):
            return None
        source_keys.add(source_key)
        semantic_digests.add(semantic_digest)
        records.append(record)
    canonical = _canonical_json(records)
    return records, sorted(semantic_digests) if canonical else None


def _semantic_item_identity(
    item: Mapping[str, Any], *, qualified: str
) -> tuple[tuple[str, str], tuple[str, str, str]] | None:
    identity = _identity(item.get("reviewed_declaration_identity"), qualified=qualified)
    signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(signatures, list) or len(signatures) != 1:
        return None
    signature = _signature_identity(signatures[0], qualified=qualified)
    if identity is None or signature is None:
        return None
    if str(item.get("qualified_declaration") or "").strip() != qualified:
        return None
    return identity, signature


def _association_matches_item(
    association: object,
    *,
    identity: tuple[str, str],
    signature: tuple[str, str, str],
    role: str,
    paired: str,
    evidence_mode: str = "proves",
    expected_source_identities: list[dict[str, Any]] | None = None,
) -> list[dict[str, Any]] | None:
    if not isinstance(association, Mapping) or association.get("schema") != 2:
        return None
    if (
        str(association.get("role") or "").strip() != role
        or str(association.get("paired_qualified_declaration") or "").strip()
        != paired
        or _identity(association.get("reviewed_declaration_identity"), qualified=identity[0])
        != identity
    ):
        return None
    association_signature = _signature_identity(
        association.get("reviewed_elaborated_signature_identity"),
        qualified=identity[0],
        require_dependency=False,
    )
    if association_signature is None or association_signature[1] != signature[1]:
        return None
    # Association identities intentionally carry only the elaborated signature.
    if association_signature[2]:
        return None
    source_identity_result = _source_contract_identities(
        association.get("source_item_identities"),
        evidence=(identity[0] if role == "direct_evidence" else paired),
        spec=(paired if role == "direct_evidence" else identity[0]),
        evidence_mode=evidence_mode,
    )
    if source_identity_result is None:
        return None
    source_identities, semantic_digests = source_identity_result
    if expected_source_identities is not None and _canonical_json(source_identities) != _canonical_json(
        expected_source_identities
    ):
        return None
    if _sha256(association.get("semantic_association_sha256")) != semantic_association_record_digest(
        semantic_digests,
        association.get("reviewed_elaborated_signature_identity"),
    ):
        return None
    return source_identities


def _group_member_association_matches_item(
    association: object,
    *,
    identity: tuple[str, str],
    signature: tuple[str, str, str],
    member_role: str,
    evidence: str,
    spec: str,
    expected_source_identities: list[dict[str, Any]],
) -> bool:
    """Validate an input occurrence attached to a grouped contract member.

    Unlike the top-level semantic row, a member association intentionally has
    ``association_mode`` and ``semantic_contract_member_role`` rather than a
    top-level ``role``.  Treating the two record shapes as interchangeable was
    the original consumer defect.
    """

    if not isinstance(association, Mapping) or association.get("schema") != 2:
        return False
    if (
        association.get("association_mode") != "semantic_contract_group_member"
        or str(association.get("semantic_contract_member_role") or "").strip()
        != member_role
        or _identity(association.get("reviewed_declaration_identity"), qualified=identity[0])
        != identity
    ):
        return False
    association_signature = _signature_identity(
        association.get("reviewed_elaborated_signature_identity"),
        qualified=identity[0],
        require_dependency=False,
    )
    if (
        association_signature is None
        or association_signature[1] != signature[1]
        or association_signature[2]
    ):
        return False
    source_identity_result = _source_contract_identities(
        association.get("source_item_identities"), evidence=evidence, spec=spec
    )
    if source_identity_result is None:
        return False
    source_identities, semantic_digests = source_identity_result
    if _canonical_json(source_identities) != _canonical_json(expected_source_identities):
        return False
    if (
        _sha256(association.get("semantic_association_sha256"))
        != semantic_association_record_digest(
            semantic_digests,
            association.get("reviewed_elaborated_signature_identity"),
        )
        or _sha256(association.get("association_sha256"))
        != source_contract_association_record_digest(association)
    ):
        return False
    return True


def _configured_row(
    raw: Mapping[str, Any], *, qualified: str, signature: tuple[str, str, str]
) -> Mapping[str, Any] | None:
    rows = raw.get("configured_review_rows")
    if not isinstance(rows, list):
        return None
    matches = [
        row
        for row in rows
        if isinstance(row, Mapping)
        and str(row.get("qualified_declaration") or "").strip() == qualified
    ]
    if len(matches) != 1:
        return None
    row = matches[0]
    if (
        _sha256(row.get("elaborated_signature_sha256")) != signature[1]
        or _sha256(row.get("semantic_dependency_sha256")) != signature[2]
        or not _sha256(row.get("elaborated_proposition_graph_sha256"))
    ):
        return None
    return row


_GroupSemanticParent = tuple[
    Mapping[str, Any],
    tuple[str, str],
    tuple[str, str, str],
    Mapping[str, Any],
    list[dict[str, Any]],
]


def _group_semantic_parent(
    semantic_items: Mapping[str, Mapping[str, Any]],
    semantic_key: str,
    *,
    statement_map: object,
) -> _GroupSemanticParent | None:
    parent = semantic_items.get(semantic_key)
    if not isinstance(parent, Mapping):
        return None
    qualified = str(parent.get("qualified_declaration") or "").strip()
    parent_identity_signature = _semantic_item_identity(parent, qualified=qualified)
    group = parent.get("semantic_contract_group")
    association = parent.get("semantic_contract_source_association")
    if (
        not qualified
        or parent_identity_signature is None
        or not isinstance(group, Mapping)
        or group.get("schema") != 1
        or group.get("structural_alpha_normalized_equal") is not True
        or not isinstance(association, Mapping)
    ):
        return None
    identity, signature = parent_identity_signature
    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list) or len(raw_members) < 2:
        return None
    members: dict[tuple[str, str], tuple[str, Mapping[str, Any]]] = {}
    roles: set[str] = set()
    for raw_member in raw_members:
        member_identity = _identity(
            raw_member.get("reviewed_declaration_identity")
            if isinstance(raw_member, Mapping)
            else None
        )
        role = str(raw_member.get("role") or "").strip() if isinstance(raw_member, Mapping) else ""
        if (
            not isinstance(raw_member, Mapping)
            or member_identity is None
            or not role
            or role in roles
            or member_identity in members
            or str(raw_member.get("qualified_declaration") or "").strip()
            != member_identity[0]
        ):
            return None
        roles.add(role)
        members[member_identity] = (role, raw_member)
    # The source-record group itself is a direct proof of one transparent Spec.
    if roles != {"direct_evidence", "transparent_spec"}:
        return None
    direct_member = next(
        (member for member, value in members.items() if value[0] == "direct_evidence"),
        None,
    )
    spec_member = next(
        (member for member, value in members.items() if value[0] == "transparent_spec"),
        None,
    )
    if direct_member != identity or spec_member is None:
        return None
    direct_surface = group.get("direct_evidence_type")
    spec_surface = group.get("surface_root")
    if (
        not isinstance(direct_surface, Mapping)
        or not isinstance(spec_surface, Mapping)
        or str(direct_surface.get("qualified_declaration") or "").strip() != qualified
        or str(spec_surface.get("qualified_declaration") or "").strip()
        != spec_member[0]
        or str(spec_surface.get("kind") or "").strip() != "transparent_spec_body"
        or direct_surface.get("structural_alpha_normalized_surface")
        != spec_surface.get("structural_alpha_normalized_surface")
    ):
        return None
    source_identity_result = _source_contract_identities(
        group.get("source_item_identities"), evidence=qualified, spec=spec_member[0]
    )
    if source_identity_result is None:
        return None
    source_identities, _semantic_digests = source_identity_result
    # The group is allowed to repair only a representation mismatch, never a
    # missing or invented source claim.  Recompute every source identity from
    # the current byte-pinned map before accepting its member associations.
    if not _source_map_declares_exact_pair(
        statement_map,
        evidence=qualified,
        spec=spec_member[0],
        source_identities=source_identities,
    ):
        return None
    if _association_matches_item(
        association,
        identity=identity,
        signature=signature,
        role="direct_evidence",
        paired=spec_member[0],
        expected_source_identities=source_identities,
    ) is None:
        return None
    return parent, identity, signature, group, source_identities


def _group_member_occurrence_is_valid(
    item: Mapping[str, Any],
    *,
    semantic_items: Mapping[str, Mapping[str, Any]],
    statement_map: object,
    group_parent_cache: dict[str, _GroupSemanticParent | None],
) -> bool:
    association = item.get("source_contract_association")
    if not isinstance(association, Mapping):
        return False
    if association.get("association_mode") != "semantic_contract_group_member":
        return False
    semantic_key = str(association.get("semantic_model_judgment_key") or "").strip()
    if semantic_key not in group_parent_cache:
        group_parent_cache[semantic_key] = _group_semantic_parent(
            semantic_items,
            semantic_key,
            statement_map=statement_map,
        )
    parent_result = group_parent_cache[semantic_key]
    if parent_result is None:
        return False
    parent, _parent_identity, _parent_signature, group, source_identities = parent_result
    identity = _identity(item.get("reviewed_declaration_identity"))
    if identity is None:
        return False
    signature = _item_signature_identity(item, qualified=identity[0])
    if signature is None:
        return False
    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list):
        return False
    matching_members = [
        member
        for member in raw_members
        if isinstance(member, Mapping)
        and _identity(member.get("reviewed_declaration_identity")) == identity
    ]
    if len(matching_members) != 1:
        return False
    # A generated input may retain the direct evidence declaration as its
    # effective source surface while its reviewed identity is the Spec member.
    # It must still remain inside this exact group; no free alias route is
    # admitted here.
    item_coordinate = str(
        item.get("effective_qualified_declaration")
        or item.get("qualified_declaration")
        or ""
    ).strip()
    member_declarations = {
        str(member.get("qualified_declaration") or "").strip()
        for member in raw_members
        if isinstance(member, Mapping)
    }
    if item_coordinate and item_coordinate not in member_declarations:
        return False
    member_role = str(matching_members[0].get("role") or "").strip()
    evidence = str(parent.get("qualified_declaration") or "").strip()
    spec = str(
        next(
            (
                member.get("qualified_declaration")
                for member in raw_members
                if isinstance(member, Mapping)
                and str(member.get("role") or "").strip() == "transparent_spec"
            ),
            "",
        )
        or ""
    )
    if (
        not member_role
        or not evidence
        or not spec
        or not _group_member_association_matches_item(
            association,
            identity=identity,
            signature=signature,
            member_role=member_role,
            evidence=evidence,
            spec=spec,
            expected_source_identities=source_identities,
        )
    ):
        return False
    return True


def _group_member_projection(
    raw: Mapping[str, Any], *, statement_map: object
) -> tuple[set[str], set[str]]:
    """Return structurally corrected error strings and redundant input keys.

    Every affected occurrence must validate independently. The raw association
    error is suppressed only if theorem/type and any same-key
    boundary/conclusion occurrences are all valid group members. A shared key
    loses its independent input obligation only when it has no
    boundary/conclusion occurrence.
    """

    raw_semantic = raw.get("semantic_model_items")
    if not isinstance(raw_semantic, list):
        return set(), set()
    semantic_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in raw_semantic
        if isinstance(item, Mapping) and str(item.get("judgment_key") or "").strip()
    }
    if len(semantic_items) != len(
        [
            item
            for item in raw_semantic
            if isinstance(item, Mapping) and str(item.get("judgment_key") or "").strip()
        ]
    ):
        return set(), set()
    occurrences_by_key: dict[str, list[Mapping[str, Any]]] = {}
    for item_field in (
        "theorem_facing_input_items",
        "type_valued_certificate_result_items",
    ):
        items = raw.get(item_field)
        if not isinstance(items, list):
            return set(), set()
        for item in items:
            if not isinstance(item, Mapping):
                return set(), set()
            key = str(item.get("source_judgment_key") or item.get("judgment_key") or "").strip()
            if key:
                occurrences_by_key.setdefault(key, []).append(item)
    boundary_or_conclusion_occurrences: dict[str, list[Mapping[str, Any]]] = {}
    for item_field in ("boundary_input_items", "conclusion_dependency_items"):
        items = raw.get(item_field)
        if not isinstance(items, list):
            return set(), set()
        for item in items:
            if not isinstance(item, Mapping):
                return set(), set()
            key = str(item.get("source_judgment_key") or item.get("judgment_key") or "").strip()
            if key:
                boundary_or_conclusion_occurrences.setdefault(key, []).append(item)
    valid_keys: set[str] = set()
    corrected_errors: set[str] = set()
    group_parent_cache: dict[str, _GroupSemanticParent | None] = {}
    raw_errors = raw.get("source_contract_association_errors")
    present_errors = set(raw_errors) if isinstance(raw_errors, list) else set()
    boundary_or_conclusion_keys = set(boundary_or_conclusion_occurrences)
    for key, occurrences in occurrences_by_key.items():
        all_occurrences = occurrences + boundary_or_conclusion_occurrences.get(
            key, []
        )
        if not all_occurrences or not all(
            _group_member_occurrence_is_valid(
                item,
                semantic_items=semantic_items,
                statement_map=statement_map,
                group_parent_cache=group_parent_cache,
            )
            for item in all_occurrences
        ):
            continue
        expected_error = _GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        # A future producer that fixes its group logic may keep a valid group
        # but intentionally retain the ordinary input obligation.  Never
        # suppress that obligation merely because the current raw shape looks
        # grouped; this lane repairs only the demonstrated false rejection.
        if expected_error not in present_errors:
            continue
        corrected_errors.add(expected_error)
        # The association failure is independently disproved by the group
        # structure, but a key that also occurs as a boundary/conclusion input
        # still needs its own human judgment and cannot be removed from the
        # required-input ledger.
        if key not in boundary_or_conclusion_keys:
            valid_keys.add(key)
    return corrected_errors, valid_keys


def _authority_entries(
    authority: object, *, paper: str
) -> tuple[dict[str, Mapping[str, Any]], str]:
    if not isinstance(authority, Mapping):
        return {}, "manifest authority is not a JSON object"
    if (
        authority.get("schema") != AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA
        or authority.get("paper") != paper
        or set(authority)
        != {"schema", "paper", "contexts", "contexts_sha256", "entries", "entries_sha256"}
    ):
        return {}, "manifest authority has incompatible schema, paper, or fields"
    contexts = authority.get("contexts")
    entries = authority.get("entries")
    if (
        not isinstance(contexts, list)
        or not isinstance(entries, list)
        or _sha256(authority.get("contexts_sha256")) != _canonical_json_sha256(contexts)
        or _sha256(authority.get("entries_sha256")) != _canonical_json_sha256(entries)
    ):
        return {}, "manifest authority aggregate integrity is invalid"
    context_ids: set[str] = set()
    for raw_context in contexts:
        if not isinstance(raw_context, Mapping) or set(raw_context) != _AUTHORITY_CONTEXT_FIELDS:
            return {}, "manifest authority has a malformed context"
        context_id = _sha256(raw_context.get("context_id"))
        projection = {
            key: raw_context.get(key)
            for key in _AUTHORITY_CONTEXT_FIELDS
            if key != "context_id"
        }
        if (
            not context_id
            or context_id in context_ids
            or _canonical_json_sha256(projection) != context_id
            or not str(raw_context.get("import_module") or "").strip()
            or not isinstance(raw_context.get("semantic_dependency_modules"), list)
            or not _sha256(raw_context.get("manifest_cache_context_sha256"))
        ):
            return {}, "manifest authority has an invalid context identity"
        context_ids.add(context_id)
    selected: dict[str, Mapping[str, Any]] = {}
    for raw_entry in entries:
        if not isinstance(raw_entry, Mapping) or set(raw_entry) != _AUTHORITY_ENTRY_FIELDS:
            return {}, "manifest authority has a malformed entry"
        qualified = str(raw_entry.get("qualified_declaration") or "").strip()
        if (
            not qualified
            or qualified in selected
            or _sha256(raw_entry.get("context_id")) not in context_ids
            or any(
                not _sha256(raw_entry.get(field))
                for field in _AUTHORITY_ENTRY_FIELDS
                - {"qualified_declaration", "context_id"}
            )
        ):
            return {}, "manifest authority has an invalid or ambiguous entry"
        selected[qualified] = raw_entry
    return selected, ""


def _outer_atoms(manifest: Mapping[str, Any]) -> list[dict[str, Any]] | None:
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return None
    normalized: list[dict[str, Any]] = []
    for index, atom in enumerate(atoms):
        if not isinstance(atom, Mapping):
            return None
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip()
        canonical = atom.get("canonical")
        if not ref or not role or not _canonical_json(canonical):
            return None
        if index == len(atoms) - 1:
            if ref != "result" or role != "conclusion":
                return None
            continue
        if ref != f"b/{index}" or role not in {"parameter", "assumption"}:
            return None
        binder_info = str(atom.get("binder_info") or "").strip()
        if binder_info not in {"explicit", "implicit", "strictImplicit", "instImplicit"}:
            return None
        normalized.append(
            {
                "ref": ref,
                "role": role,
                "binder_info": binder_info,
                "canonical": canonical,
            }
        )
    return normalized


def _complete_graph(value: object) -> tuple[dict[str, Mapping[str, Any]], list[Mapping[str, Any]]] | None:
    if not isinstance(value, Mapping) or value.get("complete") is not True:
        return None
    nodes = value.get("nodes")
    edges = value.get("edges")
    failures = value.get("failures")
    if not isinstance(nodes, list) or not isinstance(edges, list) or failures not in ([], None):
        return None
    indexed: dict[str, Mapping[str, Any]] = {}
    for node in nodes:
        if not isinstance(node, Mapping):
            return None
        path = str(node.get("path") or "").strip()
        semantic_sha = _sha256(node.get("semantic_sha256"))
        if not path or not semantic_sha or path in indexed:
            return None
        indexed[path] = node
    normalized_edges: list[Mapping[str, Any]] = []
    for edge in edges:
        if not isinstance(edge, Mapping):
            return None
        source = str(edge.get("source") or "").strip()
        target = str(edge.get("target") or "").strip()
        role = str(edge.get("role") or "").strip()
        if not source or not target or not role or source not in indexed or target not in indexed:
            return None
        normalized_edges.append(edge)
    return indexed, normalized_edges


def _manifest_matches_raw_authority(
    manifest: object,
    *,
    qualified: str,
    row: Mapping[str, Any],
    signature: tuple[str, str, str],
    authority_entry: Mapping[str, Any],
) -> bool:
    if not isinstance(manifest, Mapping):
        return False
    if (
        str(authority_entry.get("qualified_declaration") or "").strip() != qualified
        or _canonical_json_sha256(manifest)
        != _sha256(authority_entry.get("manifest_payload_sha256"))
        or signature_manifest_digest(dict(manifest)) != signature[1]
        or _sha256(manifest.get("sha256")) != signature[1]
        or _sha256(authority_entry.get("elaborated_signature_sha256")) != signature[1]
        or _sha256(row.get("elaborated_signature_sha256")) != signature[1]
    ):
        return False
    dependency = manifest.get("semantic_dependency_manifest")
    if (
        not isinstance(dependency, Mapping)
        or _sha256(dependency.get("semantic_dependency_sha256")) != signature[2]
        or _sha256(authority_entry.get("semantic_dependency_sha256")) != signature[2]
        or _sha256(row.get("semantic_dependency_sha256")) != signature[2]
    ):
        return False
    graph = manifest.get("elaborated_proposition_graph")
    graph_sha = elaborated_proposition_graph_sha256(graph)
    if (
        not graph_sha
        or graph_sha != _sha256(authority_entry.get("elaborated_proposition_graph_sha256"))
        or graph_sha != _sha256(row.get("elaborated_proposition_graph_sha256"))
    ):
        return False
    return _outer_atoms(manifest) is not None


def _companion_error(evidence: str, spec: str) -> str:
    return _COMPANION_ERROR_TEMPLATE.format(evidence=evidence, spec=spec)


def _source_map_declares_exact_pair(
    statement_map: object,
    *,
    evidence: str,
    spec: str,
    evidence_mode: str = "proves",
    source_identities: list[dict[str, Any]],
) -> bool:
    """Require the current selected source map to declare this exact route."""

    if not isinstance(statement_map, Mapping):
        return False
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return False
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return False
    expected_by_key = {
        str(record.get("source_key") or "").strip(): record
        for record in source_identities
    }
    expected_keys = set(expected_by_key)
    if not expected_keys or "" in expected_keys:
        return False
    matches: set[str] = set()
    for key, raw_item in raw_items.items():
        source_key = str(key or "").strip()
        if source_key not in expected_keys or not isinstance(raw_item, Mapping):
            continue
        contract = raw_item.get("semantic_contract")
        if (
            raw_item.get("claim_bearing") is True
            and isinstance(contract, Mapping)
            and str(contract.get("evidence_declaration") or "").strip() == evidence
            and str(contract.get("spec_declaration") or "").strip() == spec
            and str(contract.get("evidence_mode") or "").strip() == evidence_mode
            and str(contract.get("semantic_shape") or "").strip()
            and (
                _sha256(
                    expected_by_key[source_key].get("source_map_item_sha256")
                ),
                _sha256(
                    expected_by_key[source_key].get("source_semantic_sha256")
                ),
            )
            in source_record_source_item_supported_identity_sha256s(
                raw_item, mode
            )
        ):
            matches.add(source_key)
    return matches == expected_keys


def _raw_pair(
    raw: Mapping[str, Any],
    *,
    statement_map: object,
    evidence: str,
    spec: str,
    evidence_mode: str,
) -> tuple[
    Mapping[str, Any],
    Mapping[str, Any],
    tuple[str, str, str],
    tuple[str, str, str],
    Mapping[str, Any],
    Mapping[str, Any],
] | None:
    semantic_items = raw.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        return None
    by_name: dict[str, Mapping[str, Any]] = {}
    for item in semantic_items:
        if not isinstance(item, Mapping):
            return None
        qualified = str(item.get("qualified_declaration") or "").strip()
        if qualified in {evidence, spec}:
            if qualified in by_name:
                return None
            by_name[qualified] = item
    evidence_item = by_name.get(evidence)
    spec_item = by_name.get(spec)
    if evidence_item is None or spec_item is None:
        return None
    evidence_identity_signature = _semantic_item_identity(evidence_item, qualified=evidence)
    spec_identity_signature = _semantic_item_identity(spec_item, qualified=spec)
    if evidence_identity_signature is None or spec_identity_signature is None:
        return None
    _evidence_identity, evidence_signature = evidence_identity_signature
    _spec_identity, spec_signature = spec_identity_signature
    if evidence_item.get("semantic_contract_group") is not None or spec_item.get("semantic_contract_group") is not None:
        return None
    evidence_association = evidence_item.get("semantic_contract_source_association")
    spec_association = spec_item.get("semantic_contract_source_association")
    evidence_sources = _association_matches_item(
        evidence_association,
        identity=evidence_identity_signature[0],
        signature=evidence_signature,
        role="direct_evidence",
        paired=spec,
        evidence_mode=evidence_mode,
    )
    spec_sources = _association_matches_item(
        spec_association,
        identity=spec_identity_signature[0],
        signature=spec_signature,
        role="transparent_spec",
        paired=evidence,
        evidence_mode=evidence_mode,
        expected_source_identities=evidence_sources,
    )
    if evidence_sources is None or spec_sources is None:
        return None
    if not _source_map_declares_exact_pair(
        statement_map,
        evidence=evidence,
        spec=spec,
        evidence_mode=evidence_mode,
        source_identities=evidence_sources,
    ):
        return None
    evidence_row = _configured_row(raw, qualified=evidence, signature=evidence_signature)
    spec_row = _configured_row(raw, qualified=spec, signature=spec_signature)
    if evidence_row is None or spec_row is None:
        return None
    return (
        evidence_item,
        spec_item,
        evidence_signature,
        spec_signature,
        evidence_row,
        spec_row,
    )


def _expanded_body_reaches_semantic_root(
    *,
    start: str,
    nodes: Mapping[str, Mapping[str, Any]],
    edges: list[Mapping[str, Any]],
    target_sha256: str,
) -> bool:
    """Follow only transparent unfolding edges to one authenticated root."""

    current = start
    seen: set[str] = set()
    expanded = False
    while current not in seen:
        seen.add(current)
        node = nodes.get(current)
        if node is None:
            return False
        if expanded and _sha256(node.get("semantic_sha256")) == target_sha256:
            return True
        if str(node.get("kind") or "").strip() != "transparent_wrapper":
            return False
        outgoing = [edge for edge in edges if edge.get("source") == current]
        if (
            len(outgoing) != 1
            or str(outgoing[0].get("role") or "").strip() != "expanded_body"
        ):
            return False
        current = str(outgoing[0].get("target") or "").strip()
        expanded = True
    return False


def _pair_witness_is_valid(
    witness: object,
    *,
    raw: Mapping[str, Any],
    statement_map: object,
    authority_entries: Mapping[str, Mapping[str, Any]],
) -> tuple[str, str, str] | None:
    if not isinstance(witness, Mapping) or set(witness) != {
        "evidence_declaration",
        "spec_declaration",
        "evidence_mode",
        "evidence_manifest",
        "spec_manifest",
    }:
        return None
    evidence = str(witness.get("evidence_declaration") or "").strip()
    spec = str(witness.get("spec_declaration") or "").strip()
    evidence_mode = str(witness.get("evidence_mode") or "").strip()
    if (
        not evidence
        or not spec
        or evidence == spec
        or evidence_mode not in {"proves", "definitionally_realizes"}
    ):
        return None
    raw_pair = _raw_pair(
        raw,
        statement_map=statement_map,
        evidence=evidence,
        spec=spec,
        evidence_mode=evidence_mode,
    )
    if raw_pair is None:
        return None
    (
        _evidence_item,
        _spec_item,
        evidence_signature,
        spec_signature,
        evidence_row,
        spec_row,
    ) = raw_pair
    evidence_authority = authority_entries.get(evidence)
    spec_authority = authority_entries.get(spec)
    if evidence_authority is None or spec_authority is None:
        return None
    evidence_manifest = witness.get("evidence_manifest")
    spec_manifest = witness.get("spec_manifest")
    if not _manifest_matches_raw_authority(
        evidence_manifest,
        qualified=evidence,
        row=evidence_row,
        signature=evidence_signature,
        authority_entry=evidence_authority,
    ) or not _manifest_matches_raw_authority(
        spec_manifest,
        qualified=spec,
        row=spec_row,
        signature=spec_signature,
        authority_entry=spec_authority,
    ):
        return None
    assert isinstance(evidence_manifest, Mapping) and isinstance(spec_manifest, Mapping)
    if (
        evidence_manifest.get("declaration_kind") != "theorem"
        or evidence_manifest.get("conclusion_mode") != "type_only"
        or spec_manifest.get("declaration_kind") != "definition"
        or spec_manifest.get("conclusion_mode") != "type_and_value"
    ):
        return None
    evidence_atoms = _outer_atoms(evidence_manifest)
    spec_atoms = _outer_atoms(spec_manifest)
    if evidence_atoms is None or evidence_atoms != spec_atoms:
        return None
    evidence_graph = _complete_graph(evidence_manifest.get("elaborated_proposition_graph"))
    spec_graph = _complete_graph(
        spec_manifest.get("elaborated_transparent_result_value_graph")
    )
    if evidence_graph is None or spec_graph is None:
        return None
    evidence_nodes, evidence_edges = evidence_graph
    spec_nodes, _spec_edges = spec_graph
    spec_root = spec_nodes.get("result")
    spec_root_sha256 = (
        _sha256(spec_root.get("semantic_sha256"))
        if isinstance(spec_root, Mapping)
        else ""
    )
    result_node = evidence_nodes.get("result")
    if result_node is None or not spec_root_sha256:
        return None
    result_edges = [edge for edge in evidence_edges if edge.get("source") == "result"]
    if evidence_mode == "proves":
        if (
            str(result_node.get("kind") or "").strip() != "transparent_wrapper"
            or len(result_edges) != 1
            or str(result_edges[0].get("role") or "").strip() != "expanded_body"
        ):
            return None
        expanded_path = str(result_edges[0].get("target") or "").strip()
        expanded_node = evidence_nodes.get(expanded_path)
        if (
            expanded_node is None
            or _sha256(expanded_node.get("semantic_sha256")) != spec_root_sha256
        ):
            return None
    else:
        if str(result_node.get("kind") or "").strip() != "iff":
            return None
        by_role = {
            str(edge.get("role") or "").strip(): str(edge.get("target") or "").strip()
            for edge in result_edges
        }
        if set(by_role) != {"left", "right"} or len(result_edges) != 2:
            return None
        if not all(
            _expanded_body_reaches_semantic_root(
                start=by_role[role],
                nodes=evidence_nodes,
                edges=evidence_edges,
                target_sha256=spec_root_sha256,
            )
            for role in ("left", "right")
        ):
            return None
    return evidence, spec, evidence_mode


def _artifact_error(
    artifact: object,
    *,
    paper: str,
    raw: Mapping[str, Any],
    raw_audit_raw_bytes: bytes,
    statement_map: object,
    statement_map_raw_bytes: bytes,
    authority: object,
) -> tuple[set[str], str]:
    if not isinstance(artifact, Mapping):
        return set(), "semantic-contract revalidation artifact is not a JSON object"
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "source_record_audit_file_sha256",
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
        "paper_statement_map_file_sha256",
        "paper_statement_map_sha256",
        "transparent_spec_pair_witnesses",
        "source_declared_open_nonresult_witnesses",
        SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD,
    }
    if set(artifact) != expected_fields:
        return set(), "semantic-contract revalidation artifact has unsupported fields"
    if (
        artifact.get("schema") != SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_SCHEMA
        or artifact.get("artifact_kind")
        != SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_ARTIFACT_KIND
        or artifact.get("policy_version")
        != SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_POLICY_VERSION
        or artifact.get("paper") != paper
    ):
        return set(), "semantic-contract revalidation artifact has incompatible schema, policy, or paper"
    receipt = _sha256(
        artifact.get(SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD)
    )
    body = {
        key: value
        for key, value in artifact.items()
        if key != SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD
    }
    if not receipt or receipt != _canonical_json_sha256(body):
        return set(), "semantic-contract revalidation artifact digest is invalid"
    for digest_field in (
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
        "paper_statement_map_sha256",
    ):
        if (
            _sha256(artifact.get(digest_field))
            != _source_record_digest(raw, digest_field)
        ):
            return set(), (
                "semantic-contract revalidation artifact has stale "
                f"{digest_field}"
            )
    if (
        _sha256(artifact.get("source_record_audit_file_sha256"))
        != _bytes_sha256(raw_audit_raw_bytes)
    ):
        return set(), "semantic-contract revalidation artifact has stale source-record audit bytes"
    if (
        _sha256(artifact.get("paper_statement_map_file_sha256"))
        != _bytes_sha256(statement_map_raw_bytes)
    ):
        return set(), "semantic-contract revalidation artifact has stale paper-statement-map bytes"
    witnesses = artifact.get("transparent_spec_pair_witnesses")
    if not isinstance(witnesses, list):
        return set(), "semantic-contract revalidation artifact has malformed pair witnesses"
    authority_entries: Mapping[str, Mapping[str, Any]] = {}
    if witnesses:
        authority_entries, authority_error = _authority_entries(authority, paper=paper)
        if authority_error:
            return set(), authority_error
    accepted_pairs: set[tuple[str, str, str]] = set()
    corrected_errors: set[str] = set()
    for witness in witnesses:
        pair = _pair_witness_is_valid(
            witness,
            raw=raw,
            statement_map=statement_map,
            authority_entries=authority_entries,
        )
        if pair is None or pair in accepted_pairs:
            return set(), "semantic-contract revalidation artifact has an invalid or duplicate pair witness"
        accepted_pairs.add(pair)
        corrected_errors.add(_companion_error(pair[0], pair[1]))
    canonical_pairs = sorted(accepted_pairs)
    serialized_pairs = [
        (
            str(witness.get("evidence_declaration") or "").strip(),
            str(witness.get("spec_declaration") or "").strip(),
            str(witness.get("evidence_mode") or "").strip(),
        )
        for witness in witnesses
        if isinstance(witness, Mapping)
    ]
    if serialized_pairs != canonical_pairs:
        return set(), "semantic-contract revalidation pair witnesses are not in canonical order"
    open_witnesses = artifact.get("source_declared_open_nonresult_witnesses")
    if not isinstance(open_witnesses, list):
        return set(), "semantic-contract revalidation artifact has malformed open-nonresult witnesses"
    open_corrections: set[str] = set()
    open_source_keys: set[str] = set()
    raw_selected = raw.get("source_coverage_selected_source_items")
    raw_unrouted = raw.get("source_coverage_unrouted_source_items")
    selected = {
        str(value).strip()
        for value in raw_selected
        if isinstance(value, str) and value.strip()
    } if isinstance(raw_selected, list) else set()
    unrouted = {
        str(value).strip()
        for value in raw_unrouted
        if isinstance(value, str) and value.strip()
    } if isinstance(raw_unrouted, list) else set()
    map_items = statement_map.get("items") if isinstance(statement_map, Mapping) else None
    for witness in open_witnesses:
        if not isinstance(witness, Mapping) or set(witness) != {
            "source_item",
            "source_item_record_sha256",
        }:
            return set(), "semantic-contract revalidation artifact has malformed open-nonresult witness"
        source_key = str(witness.get("source_item") or "").strip()
        source_item = map_items.get(source_key) if isinstance(map_items, Mapping) else None
        anchors = source_item.get("source_anchor_evidence") if isinstance(source_item, Mapping) else None
        if (
            not source_key
            or source_key in open_source_keys
            or source_key not in selected
            or source_key not in unrouted
            or not isinstance(source_item, Mapping)
            or str(source_item.get("source_kind") or "").strip().lower() != "open_problem"
            or source_item.get("claim_bearing") is not False
            or str(source_item.get("source_scope_classification") or "").strip().lower()
            != _SOURCE_DECLARED_OPEN_NONRESULT_CLASSIFICATION
            or str(source_item.get("coverage_status") or "").strip().lower()
            != "source_declared_open"
            or str(source_item.get("protocol_role") or "").strip().lower()
            != "source_declared_open"
            or source_item.get("semantic_contract") is not None
            or source_item.get("source_claim_atoms") is not None
            or not isinstance(anchors, list)
            or not anchors
            or any(
                not isinstance(anchor, Mapping)
                or not str(anchor.get("path") or "").strip()
                or not isinstance(anchor.get("line_start"), int)
                or not isinstance(anchor.get("line_end"), int)
                or int(anchor.get("line_start")) < 1
                or int(anchor.get("line_end")) < int(anchor.get("line_start"))
                or not str(anchor.get("quoted_text") or "")
                or _sha256(anchor.get("quoted_text_sha256"))
                != hashlib.sha256(
                    str(anchor.get("quoted_text") or "").encode("utf-8")
                ).hexdigest()
                for anchor in anchors
            )
            or _sha256(witness.get("source_item_record_sha256"))
            != source_record_source_item_record_sha256(dict(source_item))
        ):
            return set(), "semantic-contract revalidation artifact has an invalid open-nonresult witness"
        open_source_keys.add(source_key)
        open_corrections.add(_SOURCE_DECLARED_OPEN_NONRESULT_ERROR_PREFIX + source_key)

    raw_association_errors = raw.get("source_contract_association_errors")
    raw_coverage_errors = raw.get("source_coverage_route_errors")
    all_raw_errors = set(
        value
        for values in (raw_association_errors, raw_coverage_errors)
        if isinstance(values, list)
        for value in values
        if isinstance(value, str)
    )
    corrected_errors |= open_corrections
    if not corrected_errors <= all_raw_errors:
        return set(), "semantic-contract revalidation witness has no exact current raw companion error"
    return corrected_errors, ""


def _semantic_contract_revalidation_projection_impl(
    *,
    paper_dir: Path,
    paper: str,
    raw_audit: Mapping[str, Any],
    raw_audit_raw_bytes: bytes | None = None,
    statement_map_payload: object | None = None,
    statement_map_raw_bytes: bytes | None = None,
    paper_prerequisites_payload: object | None = None,
    paper_prerequisites_raw_bytes: bytes | None = None,
    library_semantic_review_payload: object | None = None,
    library_semantic_review_raw_bytes: bytes | None = None,
    status_payload: object | None = None,
    status_raw_bytes: bytes | None = None,
    artifact_payload: object | None = None,
    artifact_raw_bytes: bytes | None = None,
    authority_payload: object | None = None,
    authority_raw_bytes: bytes | None = None,
    _issue_projection: Callable[
        [
            set[str] | frozenset[str],
            set[str] | frozenset[str],
            set[str] | frozenset[str],
            str,
        ],
        SemanticContractRevalidationProjection,
    ],
) -> tuple[SemanticContractRevalidationProjection, str]:
    """Replay current structural corrections without mutating the raw receipt.

    Supplying raw/map bytes and payloads is intended for an evidence
    transaction that has already snapshotted every input. Omitting them loads
    the fixed paper-local files for standalone diagnostics. An absent
    correction artifact grants no historical pair-repair credit. A complete
    current typed route graph can independently project obsolete v10 routing
    diagnostics; all other raw errors remain fatal.
    """

    def empty_projection() -> SemanticContractRevalidationProjection:
        return _issue_projection(set(), set(), set())

    artifact_path = semantic_contract_revalidation_artifact_path(paper_dir)
    authority_path = paper_dir / "audit" / "lean_signature_manifest_cache_authority.json"
    raw_path = paper_dir / "audit" / "source_record_audit.json"
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    paper_prerequisites_path = paper_dir / "audit" / "paper_semantic_prerequisites.json"
    library_semantic_review_path = paper_dir / "audit" / "library_semantic_review.json"
    status_path = paper_dir / "status.json"
    if raw_audit_raw_bytes is None:
        loaded_raw, loaded_raw_bytes, raw_load_error = _read_json_bytes(raw_path)
        if raw_load_error or not isinstance(loaded_raw, Mapping):
            return empty_projection(), (
                raw_load_error or "source-record audit is unreadable"
            )
        if loaded_raw != raw_audit:
            return empty_projection(), (
                "source-record audit payload disagrees with its exact bytes"
            )
        raw_audit_raw_bytes = loaded_raw_bytes
    if not _json_bytes_match_payload(raw_audit_raw_bytes, raw_audit):
        return empty_projection(), (
            "source-record audit snapshot bytes are malformed or disagree with its payload"
        )
    if statement_map_payload is None and statement_map_raw_bytes is None:
        loaded_map, loaded_map_bytes, map_load_error = _read_json_bytes(statement_map_path)
        if map_load_error or not isinstance(loaded_map, Mapping):
            return empty_projection(), (
                map_load_error or "paper statement map is unreadable"
            )
        statement_map_payload = loaded_map
        statement_map_raw_bytes = loaded_map_bytes
    if not _json_bytes_match_payload(statement_map_raw_bytes, statement_map_payload):
        return empty_projection(), (
            "paper-statement-map snapshot bytes are malformed or disagree with its payload"
        )
    if (
        isinstance(statement_map_payload, Mapping)
        and statement_map_payload.get("semantic_route_schema") == 2
    ):
        if paper_prerequisites_payload is None and paper_prerequisites_raw_bytes is None:
            (
                paper_prerequisites_payload,
                paper_prerequisites_raw_bytes,
                prerequisites_load_error,
            ) = _read_json_bytes(paper_prerequisites_path)
            if prerequisites_load_error:
                return empty_projection(), prerequisites_load_error
        if library_semantic_review_payload is None and library_semantic_review_raw_bytes is None:
            (
                library_semantic_review_payload,
                library_semantic_review_raw_bytes,
                library_review_load_error,
            ) = _read_json_bytes(library_semantic_review_path)
            if library_review_load_error:
                return empty_projection(), library_review_load_error
        if not _json_bytes_match_payload(
            paper_prerequisites_raw_bytes, paper_prerequisites_payload
        ):
            return empty_projection(), (
                "paper semantic-prerequisite snapshot bytes are malformed or disagree "
                "with its payload"
            )
        if not _json_bytes_match_payload(
            library_semantic_review_raw_bytes, library_semantic_review_payload
        ):
            return empty_projection(), (
                "library semantic-review snapshot bytes are malformed or disagree with "
                "its payload"
            )
        if status_payload is None and status_raw_bytes is None:
            status_payload, status_raw_bytes, status_load_error = _read_json_bytes(
                status_path
            )
            if status_load_error:
                return empty_projection(), status_load_error
        if not _json_bytes_match_payload(status_raw_bytes, status_payload):
            return empty_projection(), (
                "status snapshot bytes are malformed or disagree with its payload"
            )
    (
        typed_association_errors,
        typed_coverage_errors,
        typed_route_reconciliation_sha256,
        typed_error,
    ) = (
        _typed_route_reconciliation_projection(
            paper=paper,
            raw_audit=raw_audit,
            statement_map=statement_map_payload,
            paper_prerequisites=paper_prerequisites_payload,
            library_semantic_review=library_semantic_review_payload,
            status_payload=status_payload,
        )
    )
    if typed_error:
        return empty_projection(), typed_error
    raw_association_errors = raw_audit.get("source_contract_association_errors")
    raw_coverage_errors = raw_audit.get("source_coverage_route_errors")
    typed_graph_accounts_for_every_raw_error = (
        isinstance(raw_association_errors, list)
        and isinstance(raw_coverage_errors, list)
        and all(isinstance(error, str) for error in raw_association_errors)
        and all(isinstance(error, str) for error in raw_coverage_errors)
        and set(raw_association_errors).issubset(typed_association_errors)
        and set(raw_coverage_errors).issubset(typed_coverage_errors)
    )
    if typed_graph_accounts_for_every_raw_error:
        # A complete current typed route graph is the structural authority for
        # these exact historical diagnostics.  Do not let an optional legacy
        # evidence/Spec-pair witness veto it merely because current map bytes
        # changed.  Any unmatched raw error still falls through to the narrow
        # historical revalidation path below and remains fail-closed.
        return _issue_projection(
            typed_association_errors,
            typed_coverage_errors,
            set(),
            typed_route_reconciliation_sha256,
        ), ""
    if artifact_payload is None and artifact_raw_bytes is None:
        loaded_artifact, loaded_artifact_bytes, artifact_load_error = _read_json_bytes(
            artifact_path
        )
        if artifact_load_error:
            return empty_projection(), artifact_load_error
        artifact_payload = loaded_artifact
        artifact_raw_bytes = loaded_artifact_bytes
    if artifact_raw_bytes is None:
        if artifact_payload is not None:
            return empty_projection(), (
                "semantic-contract revalidation artifact has no exact bytes"
            )
        # The typed obligation graph is itself the current route authority.
        # The older optional artifact remains available only for its two narrow
        # historical structural repairs.
        return _issue_projection(
            typed_association_errors,
            typed_coverage_errors,
            set(),
            typed_route_reconciliation_sha256,
        ), ""
    if not isinstance(artifact_payload, Mapping) or not _json_bytes_match_payload(
        artifact_raw_bytes, artifact_payload
    ):
        return empty_projection(), (
            "semantic-contract revalidation artifact is unreadable or malformed"
        )
    assert isinstance(raw_audit_raw_bytes, bytes)
    assert isinstance(statement_map_raw_bytes, bytes)
    # The artifact deliberately binds both immutable inputs: the canonical raw
    # receipt (including its historical map-file coordinate) and the exact
    # current statement-map bytes. Requiring those two map hashes to be equal
    # here would defeat the purpose of structural revalidation after a
    # machine-only correspondence refresh. Every accepted correction below
    # still reconstructs its source item and semantic contract from the current
    # map and matches the raw association through a supported identity normal
    # form; arbitrary map drift therefore remains a fail-closed pair miss.
    witnesses = artifact_payload.get("transparent_spec_pair_witnesses")
    if isinstance(witnesses, list) and witnesses and authority_payload is None and authority_raw_bytes is None:
        loaded_authority, loaded_authority_bytes, authority_load_error = _read_json_bytes(
            authority_path
        )
        if authority_load_error:
            return empty_projection(), authority_load_error
        authority_payload = loaded_authority
        authority_raw_bytes = loaded_authority_bytes
    if isinstance(witnesses, list) and witnesses and (
        authority_raw_bytes is None
        or not isinstance(authority_payload, Mapping)
        or not _json_bytes_match_payload(authority_raw_bytes, authority_payload)
    ):
        return empty_projection(), (
            "semantic-contract revalidation requires a readable manifest authority"
        )
    structural_errors, error = _artifact_error(
        artifact_payload,
        paper=paper,
        raw=raw_audit,
        raw_audit_raw_bytes=raw_audit_raw_bytes,
        statement_map=statement_map_payload,
        statement_map_raw_bytes=statement_map_raw_bytes,
        authority=authority_payload,
    )
    if error:
        return empty_projection(), error
    group_errors, suppressed_keys = _group_member_projection(
        raw_audit, statement_map=statement_map_payload
    )
    if (
        not group_errors
        and not structural_errors
        and not typed_association_errors
        and not typed_coverage_errors
    ):
        return empty_projection(), (
            "semantic-contract revalidation artifact has no exact current raw correction"
        )
    return (
        _issue_projection(
            group_errors | structural_errors | typed_association_errors,
            structural_errors | typed_coverage_errors,
            suppressed_keys,
            typed_route_reconciliation_sha256,
        ),
        "",
    )


def _make_semantic_contract_revalidation_api() -> tuple[
    Callable[..., tuple[SemanticContractRevalidationProjection, str]],
    Callable[[object], bool],
]:
    """Close the issuance registry over the public validator and predicate.

    A projection is an in-process capability, not an input data format.  Keep
    both the registry and issuer out of module globals so ordinary consumers
    can neither mint nor register a caller-constructed projection.
    """

    issued: weakref.WeakSet[SemanticContractRevalidationProjection] = weakref.WeakSet()

    def issue(
        suppressed_source_contract_association_errors: set[str] | frozenset[str],
        suppressed_source_coverage_route_errors: set[str] | frozenset[str],
        suppressed_expected_input_keys: set[str] | frozenset[str],
        typed_route_reconciliation_sha256: str = "",
    ) -> SemanticContractRevalidationProjection:
        projection = SemanticContractRevalidationProjection(
            frozenset(suppressed_source_contract_association_errors),
            frozenset(suppressed_source_coverage_route_errors),
            frozenset(suppressed_expected_input_keys),
            _sha256(typed_route_reconciliation_sha256),
        )
        issued.add(projection)
        return projection

    def validate(
        *,
        paper_dir: Path,
        paper: str,
        raw_audit: Mapping[str, Any],
        raw_audit_raw_bytes: bytes | None = None,
        statement_map_payload: object | None = None,
        statement_map_raw_bytes: bytes | None = None,
        paper_prerequisites_payload: object | None = None,
        paper_prerequisites_raw_bytes: bytes | None = None,
        library_semantic_review_payload: object | None = None,
        library_semantic_review_raw_bytes: bytes | None = None,
        status_payload: object | None = None,
        status_raw_bytes: bytes | None = None,
        artifact_payload: object | None = None,
        artifact_raw_bytes: bytes | None = None,
        authority_payload: object | None = None,
        authority_raw_bytes: bytes | None = None,
    ) -> tuple[SemanticContractRevalidationProjection, str]:
        return _semantic_contract_revalidation_projection_impl(
            paper_dir=paper_dir,
            paper=paper,
            raw_audit=raw_audit,
            raw_audit_raw_bytes=raw_audit_raw_bytes,
            statement_map_payload=statement_map_payload,
            statement_map_raw_bytes=statement_map_raw_bytes,
            paper_prerequisites_payload=paper_prerequisites_payload,
            paper_prerequisites_raw_bytes=paper_prerequisites_raw_bytes,
            library_semantic_review_payload=library_semantic_review_payload,
            library_semantic_review_raw_bytes=library_semantic_review_raw_bytes,
            status_payload=status_payload,
            status_raw_bytes=status_raw_bytes,
            artifact_payload=artifact_payload,
            artifact_raw_bytes=artifact_raw_bytes,
            authority_payload=authority_payload,
            authority_raw_bytes=authority_raw_bytes,
            _issue_projection=issue,
        )

    def authenticated(value: object) -> bool:
        return (
            isinstance(value, SemanticContractRevalidationProjection)
            and value in issued
        )

    return validate, authenticated


semantic_contract_revalidation_projection, projection_is_authenticated = (
    _make_semantic_contract_revalidation_api()
)
del _make_semantic_contract_revalidation_api


def effective_source_record_semantic_errors(
    raw_audit: Mapping[str, Any],
    projection: SemanticContractRevalidationProjection | None,
) -> dict[str, list[str]]:
    """Return raw semantic errors after an authenticated structural replay."""

    if not projection_is_authenticated(projection):
        projection = None
    suppressed_association = (
        projection.suppressed_source_contract_association_errors
        if projection is not None
        else frozenset()
    )
    suppressed_coverage = (
        projection.suppressed_source_coverage_route_errors
        if projection is not None
        else frozenset()
    )
    result: dict[str, list[str]] = {}
    for error_field, suppressed in (
        ("source_contract_association_errors", suppressed_association),
        ("source_coverage_route_errors", suppressed_coverage),
    ):
        values = raw_audit.get(error_field)
        if isinstance(values, list):
            result[error_field] = [
                value for value in values if not isinstance(value, str) or value not in suppressed
            ]
    return result


def _atomic_write_json(path: Path, payload: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, ensure_ascii=True, sort_keys=True, indent=2) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def issue_semantic_contract_revalidation_artifact(
    *, paper_dir: Path, paper: str
) -> tuple[Path | None, str]:
    """Issue a compact fragment from the authenticated carrier once.

    This is intentionally a slow, explicit issuer.  It validates the current
    authority/carrier pair through the authenticated store, extracts only raw
    companion errors with exact reciprocal source associations, and writes the
    resulting witness atomically.  Gates never call this function.
    """

    raw_path = paper_dir / "audit" / "source_record_audit.json"
    raw_payload, raw_bytes, raw_error = _read_json_bytes(raw_path)
    if raw_error or raw_bytes is None or not isinstance(raw_payload, Mapping):
        return None, raw_error or "source-record raw audit is unavailable"
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    statement_map, statement_map_bytes, map_error = _read_json_bytes(statement_map_path)
    if map_error or statement_map_bytes is None or not isinstance(statement_map, Mapping):
        return None, map_error or "paper statement map is unavailable"
    association_errors = raw_payload.get("source_contract_association_errors")
    coverage_errors = raw_payload.get("source_coverage_route_errors")
    present_errors = {
        error
        for values in (association_errors, coverage_errors)
        if isinstance(values, list)
        for error in values
        if isinstance(error, str)
    }
    candidate_pairs: list[tuple[str, str, str]] = []
    raw_unrouted = raw_payload.get("source_coverage_unrouted_source_items")
    open_witnesses: list[dict[str, str]] = []
    map_items = statement_map.get("items")
    if isinstance(raw_unrouted, list) and isinstance(map_items, Mapping):
        for raw_source_key in raw_unrouted:
            source_key = str(raw_source_key or "").strip()
            source_item = map_items.get(source_key)
            error = _SOURCE_DECLARED_OPEN_NONRESULT_ERROR_PREFIX + source_key
            if not source_key or error not in present_errors or not isinstance(source_item, Mapping):
                continue
            route_policy_open = bool(
                str(source_item.get("source_kind") or "").strip().lower() == "open_problem"
                and source_item.get("claim_bearing") is False
                and str(source_item.get("source_scope_classification") or "").strip().lower()
                == _SOURCE_DECLARED_OPEN_NONRESULT_CLASSIFICATION
                and str(source_item.get("coverage_status") or "").strip().lower()
                == "source_declared_open"
                and str(source_item.get("protocol_role") or "").strip().lower()
                == "source_declared_open"
            )
            if route_policy_open:
                open_witnesses.append(
                    {
                        "source_item": source_key,
                        "source_item_record_sha256": source_record_source_item_record_sha256(
                            dict(source_item)
                        ),
                    }
                )
    semantic_items = raw_payload.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        return None, "source-record raw audit has no semantic-model items"
    for item in semantic_items:
        if not isinstance(item, Mapping):
            continue
        association = item.get("semantic_contract_source_association")
        if not isinstance(association, Mapping) or association.get("role") != "direct_evidence":
            continue
        evidence = str(item.get("qualified_declaration") or "").strip()
        spec = str(association.get("paired_qualified_declaration") or "").strip()
        if not evidence or not spec or _companion_error(evidence, spec) not in present_errors:
            continue
        source_identities = association.get("source_item_identities")
        modes = {
            str(contract.get("evidence_mode") or "").strip()
            for source_identity in (
                source_identities if isinstance(source_identities, list) else []
            )
            if isinstance(source_identity, Mapping)
            and isinstance((contract := source_identity.get("semantic_contract")), Mapping)
        }
        if len(modes) != 1:
            continue
        evidence_mode = next(iter(modes))
        if evidence_mode not in {"proves", "definitionally_realizes"}:
            continue
        raw_pair = _raw_pair(
            raw_payload,
            statement_map=statement_map,
            evidence=evidence,
            spec=spec,
            evidence_mode=evidence_mode,
        )
        if raw_pair is None:
            continue
        candidate_pairs.append((evidence, spec, evidence_mode))
    candidate_pairs = sorted(set(candidate_pairs))
    group_errors, _suppressed_keys = _group_member_projection(
        raw_payload, statement_map=statement_map
    )
    if not candidate_pairs and not group_errors and not open_witnesses:
        return None, "no current raw semantic-contract error has a structural correction"
    entries: Mapping[str, tuple[Mapping[str, Any], Mapping[str, Any]]] = {}
    if candidate_pairs:
        stored_paper, _contexts, entries = _validated_store_entries(paper_dir)
        if stored_paper != paper:
            return None, "authenticated manifest store is unavailable or invalid"
    witnesses: list[dict[str, Any]] = []
    for evidence, spec, evidence_mode in candidate_pairs:
        evidence_entry = entries.get(evidence)
        spec_entry = entries.get(spec)
        if evidence_entry is None or spec_entry is None:
            return None, "authenticated manifest entry disappeared during issuance"
        _evidence_authority, evidence_manifest = evidence_entry
        _spec_authority, spec_manifest = spec_entry
        witnesses.append(
            {
                "evidence_declaration": evidence,
                "spec_declaration": spec,
                "evidence_mode": evidence_mode,
                "evidence_manifest": evidence_manifest,
                "spec_manifest": spec_manifest,
            }
        )
    payload: dict[str, Any] = {
        "schema": SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_SCHEMA,
        "artifact_kind": SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_POLICY_VERSION,
        "paper": paper,
        "source_record_audit_file_sha256": _bytes_sha256(raw_bytes),
        "source_record_audit_sha256": raw_payload.get("source_record_audit_sha256"),
        "source_record_audit_integrity_sha256": raw_payload.get(
            "source_record_audit_integrity_sha256"
        ),
        "paper_statement_map_file_sha256": _bytes_sha256(statement_map_bytes),
        "paper_statement_map_sha256": raw_payload.get("paper_statement_map_sha256"),
        "transparent_spec_pair_witnesses": witnesses,
        "source_declared_open_nonresult_witnesses": sorted(
            open_witnesses, key=lambda witness: witness["source_item"]
        ),
    }
    payload[SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD] = (
        _canonical_json_sha256(payload)
    )
    authority_payload: Mapping[str, Any] | None = None
    authority_bytes: bytes | None = None
    if candidate_pairs:
        authority_path = paper_dir / "audit" / "lean_signature_manifest_cache_authority.json"
        loaded_authority, loaded_authority_bytes, authority_error = _read_json_bytes(
            authority_path
        )
        if (
            authority_error
            or loaded_authority_bytes is None
            or not isinstance(loaded_authority, Mapping)
        ):
            return None, authority_error or "manifest authority is unavailable"
        authority_payload = loaded_authority
        authority_bytes = loaded_authority_bytes
    _projection, validation_error = semantic_contract_revalidation_projection(
        paper_dir=paper_dir,
        paper=paper,
        raw_audit=raw_payload,
        raw_audit_raw_bytes=raw_bytes,
        statement_map_payload=statement_map,
        statement_map_raw_bytes=statement_map_bytes,
        artifact_payload=payload,
        artifact_raw_bytes=json.dumps(payload, ensure_ascii=True).encode("utf-8"),
        authority_payload=authority_payload,
        authority_raw_bytes=authority_bytes,
    )
    if validation_error:
        return None, "issued artifact failed self-validation: " + validation_error
    path = semantic_contract_revalidation_artifact_path(paper_dir)
    _atomic_write_json(path, payload)
    return path, ""


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Issue a compact immutable source-record semantic-contract witness."
    )
    parser.add_argument("--paper", required=True, help="paper directory name")
    args = parser.parse_args()
    paper = str(args.paper).strip()
    paper_dir = ROOT / "papers" / paper
    path, error = issue_semantic_contract_revalidation_artifact(
        paper_dir=paper_dir, paper=paper
    )
    if error:
        print(f"source-record semantic-contract revalidation: ERROR: {error}")
        return 2
    assert path is not None
    print(f"source-record semantic-contract revalidation: wrote {path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry point.
    raise SystemExit(main())
