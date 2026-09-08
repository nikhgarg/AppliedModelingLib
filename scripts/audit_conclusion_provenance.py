#!/usr/bin/env python3
"""Fail when reviewed theorems consume conclusions without real constructors.

This workflow reruns or reuses a fingerprint-current *full* source-record
analysis from current Lean source instead of trusting checked-in JSON sidecars.
The full surface is necessary for the name-independent elaborated signatures
that make item-level source-record reuse sound. The helper reuses its
paper-local full-audit cache when that cache is current; otherwise it performs
the isolated paper scan, including the narrow source-premise consistency query
needed to detect a reviewed model input that entails ``False``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from dataclasses import asdict, dataclass
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable, Mapping, Sequence, cast

# The CI workflow executes this file directly. Resolve its transitive imports
# through the same repository package used by module-style execution.
if __package__ in {None, ""}:
    repository_root = str(Path(__file__).resolve().parents[1])
    if repository_root not in sys.path:
        sys.path.insert(0, repository_root)

try:
    from scripts.source_record_projection_contract import (
        CheckedProjectionResult,
        checked_projection_result,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_projection_contract import (
        CheckedProjectionResult,
        checked_projection_result,
    )

try:
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA

try:
    from scripts.source_record_integrity import (
        source_record_item_reuse_eligible,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_integrity import (
        source_record_item_reuse_eligible,
    )

try:
    from scripts.formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from formalization_protocol import CURRENT_SOURCE_RECORD_PROMPT_VERSION

try:
    from scripts.source_record_obligation_groups import (
        raw_source_record_obligation_groups,
    )
except ModuleNotFoundError:  # pragma: no cover - supports direct-script imports.
    from source_record_obligation_groups import (
        raw_source_record_obligation_groups,
    )

try:
    from scripts.source_record_archived_transports import (
        archived_source_record_transport_artifacts,
        archived_source_record_transport_item_field,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_archived_transports import (
        archived_source_record_transport_artifacts,
        archived_source_record_transport_item_field,
    )

try:
    from scripts.source_record_overlay_protocol import (
        serialized_source_record_overlay_labels,
        source_record_overlay_labels_with_artifacts,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_overlay_protocol import (
        serialized_source_record_overlay_labels,
        source_record_overlay_labels_with_artifacts,
    )

try:
    from scripts.source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        SEMANTIC_ASSOCIATION_SCHEMA,
        SEMANTIC_ASSOCIATION_SHA256_FIELD,
        SOURCE_TARGET_DISPOSITION_FIELD,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        approved_source_convention_antecedent_errors,
        approved_source_convention_metadata_errors,
        current_source_correction_identity_by_key,
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
        source_input_target_disposition_errors,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        SEMANTIC_ASSOCIATION_SCHEMA,
        SEMANTIC_ASSOCIATION_SHA256_FIELD,
        SOURCE_TARGET_DISPOSITION_FIELD,
        SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD,
        SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        approved_source_convention_antecedent_errors,
        approved_source_convention_metadata_errors,
        current_source_correction_identity_by_key,
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
        source_input_target_disposition_errors,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )

try:
    from scripts.source_claim_semantic_contract import (
        SourceClaimAtomReceipt,
        SourceDomainCorrespondenceReceipt,
        RecursiveFieldExplicitParentComponentReceipt,
        SemanticContractExecutableTerminalComponentReceipt,
        StrictSourceSpecCorrespondenceReceipt,
        TransparentSpecFullSurfaceCorrespondenceReceipt,
        source_claim_component_sha256,
        theorem_facing_semantic_restriction_status,
        theorem_realization_component_contract_errors,
        theorem_realization_components,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_claim_semantic_contract import (
        SourceClaimAtomReceipt,
        SourceDomainCorrespondenceReceipt,
        RecursiveFieldExplicitParentComponentReceipt,
        SemanticContractExecutableTerminalComponentReceipt,
        StrictSourceSpecCorrespondenceReceipt,
        TransparentSpecFullSurfaceCorrespondenceReceipt,
        source_claim_component_sha256,
        theorem_facing_semantic_restriction_status,
        theorem_realization_component_contract_errors,
        theorem_realization_components,
    )

try:
    from scripts.source_claim_atom_schema import (
        graph_native_source_spec_realization_identity_sha256,
        source_claim_atoms_semantic_sha256,
    )
except ModuleNotFoundError:  # pragma: no cover - supports direct-script imports.
    from source_claim_atom_schema import (
        graph_native_source_spec_realization_identity_sha256,
        source_claim_atoms_semantic_sha256,
    )

try:
    from scripts.source_record_assumption_association import (
        SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
        SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN,
        SOURCE_ASSUMPTION_ASSOCIATION_ROLE,
        source_assumption_effective_semantic_pin,
    )
except ModuleNotFoundError:  # pragma: no cover - supports direct-script imports.
    from source_record_assumption_association import (
        SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
        SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN,
        SOURCE_ASSUMPTION_ASSOCIATION_ROLE,
        source_assumption_effective_semantic_pin,
    )

try:
    from scripts.source_record_record_closure_completion import (
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
        RecordFieldClosureCompletionCandidate,
        closure_attestation_for_candidate,
        closure_attestation_sha256,
        closure_completion_receipt_error,
        current_record_field_closure_completion_candidates,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_record_closure_completion import (
        RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD,
        RecordFieldClosureCompletionCandidate,
        closure_attestation_for_candidate,
        closure_attestation_sha256,
        closure_completion_receipt_error,
        current_record_field_closure_completion_candidates,
    )

try:
    from scripts.source_coverage_scope import (
        SOURCE_DOMAIN_PRESENTATION_KINDS,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_coverage_scope import (
        SOURCE_DOMAIN_PRESENTATION_KINDS,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )

try:
    from scripts.configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        FORMALIZATION_REGULARITY_CLASSIFICATION,
        load_configured_assumption_formalization_regularity_context,
        response_claims_configured_assumption_formalization_regularity,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from configured_assumption_formalization_regularities import (
        ConfiguredAssumptionFormalizationRegularityContext,
        FORMALIZATION_REGULARITY_CLASSIFICATION,
        load_configured_assumption_formalization_regularity_context,
        response_claims_configured_assumption_formalization_regularity,
    )

try:
    from scripts.audit_repository import (
        semantic_model_review_findings,
        source_record_expected_item_digests,
        source_record_expected_item_digest_pins,
        source_record_target_disposition_rebind_context,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from audit_repository import (
        semantic_model_review_findings,
        source_record_expected_item_digests,
        source_record_expected_item_digest_pins,
        source_record_target_disposition_rebind_context,
    )

try:
    from scripts.audit_evidence_integrity import (
        author_approved_corrected_scope,
        author_approved_corrected_scope_contract_is_current,
        canonical_source_record_match_sidecar_path,
        canonical_source_record_sidecar_effective_coverage_error,
        corrected_model_mapping_freshness_error,
        corrected_model_scope_model_bindings,
        corrected_model_transitively_reachable_field_items,
        current_paper_statement_map_sha256,
        semantic_contract_closeout_bridge_inventory,
        source_claim_atom_semantic_sha256,
        source_spec_correspondence_item_identity_sha256,
        source_spec_correspondence_validation_errors,
        source_spec_correspondence_requested,
        source_record_audit_identity_error,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from audit_evidence_integrity import (
        author_approved_corrected_scope,
        author_approved_corrected_scope_contract_is_current,
        canonical_source_record_match_sidecar_path,
        canonical_source_record_sidecar_effective_coverage_error,
        corrected_model_mapping_freshness_error,
        corrected_model_scope_model_bindings,
        corrected_model_transitively_reachable_field_items,
        current_paper_statement_map_sha256,
        semantic_contract_closeout_bridge_inventory,
        source_claim_atom_semantic_sha256,
        source_spec_correspondence_item_identity_sha256,
        source_spec_correspondence_validation_errors,
        source_spec_correspondence_requested,
        source_record_audit_identity_error,
    )

try:
    from scripts.source_record_auxiliary_routing_supplement import (
        ValidatedAuxiliaryRoutingContext,
        current_auxiliary_routing_context,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_auxiliary_routing_supplement import (
        ValidatedAuxiliaryRoutingContext,
        current_auxiliary_routing_context,
    )


ROOT = Path(__file__).resolve().parents[1]
PAPERS = ROOT / "papers"
HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
FULLY_FORMALIZED_STATUSES = {"formalized", "formalized with caveat"}
SOURCE_RECORD_PROMPT_VERSION = CURRENT_SOURCE_RECORD_PROMPT_VERSION
_CONTEXT_OVERRIDE_UNSET = object()
RESTRICTED_SUBTYPE_DOMAIN_CONTEXT_KIND = "restricted_subtype_domain"
TRANSPARENT_SUBTYPE_DOMAIN_CONTEXT_SCHEMA = 1
SOURCE_CLAIM_ATOM_ASSOCIATION_SCHEMA = 1
SOURCE_CLAIM_ATOM_SEMANTIC_ASSOCIATION_FIELD = (
    "source_claim_atom_semantic_association_sha256"
)
SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS = (
    "boundary_input_items",
    "theorem_facing_input_items",
    "conclusion_dependency_items",
    "recursive_field_items",
    "semantic_model_items",
    "type_valued_certificate_result_items",
    "source_premise_consistency_items",
)
EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.I,
)


@dataclass(frozen=True)
class Finding:
    paper: str
    row: str
    binder: str
    fields: tuple[str, ...]
    message: str

    def format(self) -> str:
        target = f"{self.row}.{self.binder}"
        field_text = f" fields={','.join(self.fields)}" if self.fields else ""
        return f"[ERROR] {self.paper} {target}:{field_text} {self.message}"


class _SourceRecordSnapshotBinding:
    """Bind one issued capability to one exact snapshot object."""

    __slots__ = ("snapshot",)

    def __init__(self) -> None:
        self.snapshot: SourceRecordAuditSnapshot | None = None


@dataclass(frozen=True)
class SourceRecordAuditSnapshot:
    """One run-scoped raw audit parsed from exact bytes.

    ``source_file_sha256`` binds ``payload`` to the bytes parsed by
    :func:`load_source_record_audit_snapshot`.  A canonical snapshot retains
    its source path so the conclusion gate can reject a concurrent replacement
    before returning a result.  ``identity_validated`` is issued only by this
    module after the ordinary current-source identity replay succeeds.
    ``structural_v11_validated`` is a separate capability that exposes the
    payload only as recursive inventory after current v11 semantics and
    theorem realization pass; it never authenticates historical judgments.
    Neither capability is persisted or inferred from serialized fields.
    """

    paper: str
    payload: dict[str, Any]
    source_file_sha256: str
    source_path: Path | None
    paper_statement_map_sha256: str = ""
    source_record_match_path: Path | None = None
    source_record_match_sha256: str = ""
    current_judgments_override: Mapping[str, dict[str, Any]] | None = None
    status_payload_override: Mapping[str, Any] | None = None
    paper_statement_map_override: Mapping[str, Any] | None = None
    corrected_scope_current_override: bool | None = None
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET
    configured_assumption_regularity_context_override: object = (
        _CONTEXT_OVERRIDE_UNSET
    )
    configured_assumption_regularity_context_error_override: str | None = None
    auxiliary_routing_context_override: object = _CONTEXT_OVERRIDE_UNSET
    auxiliary_routing_context_error_override: str | None = None
    input_raw_bytes_override: Mapping[Path, bytes | None] | None = None
    _content_binding_token: object | None = None
    _identity_validation_token: object | None = None
    _structural_v11_validation_token: object | None = None

    @property
    def identity_validated(self) -> bool:
        """Whether this process issued currentness validation for the snapshot."""

        binding = self._identity_validation_token
        return (
            isinstance(binding, _SourceRecordSnapshotBinding)
            and binding.snapshot is self
        )

    @property
    def content_bound(self) -> bool:
        """Whether the payload was parsed by the exact-byte snapshot loader."""

        binding = self._content_binding_token
        return (
            isinstance(binding, _SourceRecordSnapshotBinding)
            and binding.snapshot is self
        )

    @property
    def structural_v11_validated(self) -> bool:
        """Whether v11 issued this raw payload as structural inventory only."""

        binding = self._structural_v11_validation_token
        return (
            isinstance(binding, _SourceRecordSnapshotBinding)
            and binding.snapshot is self
        )


def _issued_source_record_audit_snapshot(
    *,
    paper: str,
    payload: dict[str, Any],
    source_file_sha256: str,
    source_path: Path | None,
    paper_statement_map_sha256: str = "",
    source_record_match_path: Path | None = None,
    source_record_match_sha256: str = "",
    current_judgments_override: Mapping[str, dict[str, Any]] | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    corrected_scope_current_override: bool | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
    configured_assumption_regularity_context_override: object = (
        _CONTEXT_OVERRIDE_UNSET
    ),
    configured_assumption_regularity_context_error_override: str | None = None,
    auxiliary_routing_context_override: object = _CONTEXT_OVERRIDE_UNSET,
    auxiliary_routing_context_error_override: str | None = None,
    input_raw_bytes_override: Mapping[Path, bytes | None] | None = None,
    identity_validated: bool = False,
    structural_v11_validated: bool = False,
    payload_is_immutable: bool = False,
) -> SourceRecordAuditSnapshot:
    """Issue an exact-object-bound snapshot capability."""

    if not payload_is_immutable:
        evidence_module = sys.modules.get(
            "scripts.audit_evidence_integrity"
        ) or sys.modules.get("audit_evidence_integrity")
        if evidence_module is None:
            if __package__:
                from . import audit_evidence_integrity as evidence_module
            else:  # pragma: no cover - direct script invocation.
                import audit_evidence_integrity as evidence_module
        payload = evidence_module._freeze_json(payload)
        assert isinstance(payload, dict)
    content_binding = _SourceRecordSnapshotBinding()
    identity_binding = (
        _SourceRecordSnapshotBinding() if identity_validated else None
    )
    structural_v11_binding = (
        _SourceRecordSnapshotBinding() if structural_v11_validated else None
    )
    frozen_input_raw_bytes = (
        MappingProxyType(
            {
                path.resolve(): (bytes(raw) if isinstance(raw, bytes) else None)
                for path, raw in input_raw_bytes_override.items()
            }
        )
        if input_raw_bytes_override is not None
        else None
    )
    snapshot = SourceRecordAuditSnapshot(
        paper=paper,
        payload=payload,
        source_file_sha256=source_file_sha256,
        source_path=source_path,
        paper_statement_map_sha256=paper_statement_map_sha256,
        source_record_match_path=source_record_match_path,
        source_record_match_sha256=source_record_match_sha256,
        current_judgments_override=current_judgments_override,
        status_payload_override=status_payload_override,
        paper_statement_map_override=paper_statement_map_override,
        corrected_scope_current_override=corrected_scope_current_override,
        administrative_projection_rebind_override=(
            administrative_projection_rebind_override
        ),
        configured_assumption_regularity_context_override=(
            configured_assumption_regularity_context_override
        ),
        configured_assumption_regularity_context_error_override=(
            configured_assumption_regularity_context_error_override
        ),
        auxiliary_routing_context_override=auxiliary_routing_context_override,
        auxiliary_routing_context_error_override=(
            auxiliary_routing_context_error_override
        ),
        input_raw_bytes_override=frozen_input_raw_bytes,
        _content_binding_token=content_binding,
        _identity_validation_token=identity_binding,
        _structural_v11_validation_token=structural_v11_binding,
    )
    content_binding.snapshot = snapshot
    if identity_binding is not None:
        identity_binding.snapshot = snapshot
    if structural_v11_binding is not None:
        structural_v11_binding.snapshot = snapshot
    return snapshot


@dataclass(frozen=True)
class TransparentSpecSemanticParentReceipt:
    """Authenticated direct-evidence/transparent-Spec semantic pair.

    The generator owns every identity in this receipt.  The canonical JSON
    fields retain the exact alpha-normalized proposition surface and source
    identities without making a declaration, row, or binder name semantic
    evidence.
    """

    semantic_model_judgment_key: str
    evidence_declaration_identity: tuple[str, str]
    evidence_elaborated_signature_identity: tuple[str, str]
    spec_declaration_identity: tuple[str, str]
    alpha_normalized_surface_json: str
    source_item_identities_json: str


@dataclass(frozen=True)
class StrictTransparentSpecSemanticParent:
    """A current strict source-to-Spec parent for one generated semantic row.

    This is deliberately a runtime-only projection.  It joins a checked
    source-to-Spec receipt to the generator-owned direct-evidence/transparent-
    Spec pair and the complete atom route.  It is therefore an alternate
    source-semantic disposition for a strict named claim, not an exemption
    inferred from an LLM judgment key, declaration name, or source kind.
    """

    semantic_model_judgment_key: str
    parent_receipt: TransparentSpecSemanticParentReceipt
    parent_semantic_association_sha256: str
    parent_source_claim_atom_association_sha256: str
    parent_source_claim_atom_semantic_association_sha256: str
    source_item_keys: tuple[str, ...]
    source_root_receipts: tuple[StrictSourceSpecCorrespondenceReceipt, ...]


@dataclass(frozen=True)
class CorrectedModelConclusionRow:
    """One exact generated declaration covered by a corrected-model contract."""

    semantic_model_judgment_key: str
    qualified_declaration: str
    declaration_sha256: str
    elaborated_signature_identities: frozenset[tuple[str, str]]
    governing_model_spec_declaration: str
    governing_model_field_keys: frozenset[str]
    requires_explicit_rooted_field_paths: bool
    transparent_spec_parent_receipt: TransparentSpecSemanticParentReceipt | None = None


@dataclass(frozen=True)
class CorrectedModelConclusionBridge:
    """Narrow provenance bridge for a fully current corrected-model scope.

    This is not a generic waiver for a paper folder.  Its rows come from the
    current generated semantic-model surface and have already been tied to the
    contract's exact item/target/assumption mappings.  The field sets preserve
    the distinction between the approved governing model and unrelated record
    inputs encountered by the conclusion-dependency scan.
    """

    rows: tuple[CorrectedModelConclusionRow, ...]


def _sha256_value(value: object) -> str | None:
    """Return one normalized SHA-256 value without coercing malformed input."""

    if not isinstance(value, str):
        return None
    normalized = value.strip().lower()
    return normalized if re.fullmatch(r"[0-9a-f]{64}", normalized) else None


def _reviewed_declaration_identity(
    item: dict[str, Any],
) -> tuple[str, str] | None:
    """Read the generator-owned declaration identity for a reviewed item.

    The source-record row label is presentation metadata, not an identity.  A
    corrected-model exemption must instead be tied to the exact declaration
    whose source text was scanned and hashed.
    """

    raw_identity = item.get("reviewed_declaration_identity")
    if not isinstance(raw_identity, dict):
        return None
    declaration = raw_identity.get("qualified_declaration")
    digest = _sha256_value(raw_identity.get("declaration_sha256"))
    if not isinstance(declaration, str) or not declaration.strip() or digest is None:
        return None
    return declaration.strip(), digest


def _all_elaborated_signature_identities(
    item: Mapping[str, Any],
) -> frozenset[tuple[str, str]] | None:
    """Read the complete generated elaborated-signature identity set."""

    raw_signatures = item.get("reviewed_elaborated_signature_identities")
    if raw_signatures is None:
        return frozenset()
    if not isinstance(raw_signatures, list) or not raw_signatures:
        return None
    signatures: set[tuple[str, str]] = set()
    for raw_signature in raw_signatures:
        if not isinstance(raw_signature, Mapping):
            return None
        declaration = str(
            raw_signature.get("qualified_declaration") or ""
        ).strip()
        signature_digest = _sha256_value(
            raw_signature.get("elaborated_signature_sha256")
        )
        if not declaration or signature_digest is None:
            return None
        identity = (declaration, signature_digest)
        if identity in signatures:
            return None
        signatures.add(identity)
    return frozenset(signatures)


def _unique_elaborated_signature_identity(
    item: Mapping[str, Any], *, declaration: str, allow_aggregate: bool = False
) -> tuple[str, str] | None:
    """Select one exact declaration signature, rejecting unowned aggregates."""

    signatures = _all_elaborated_signature_identities(item)
    if signatures is None:
        return None
    if len(signatures) != 1 and not allow_aggregate:
        return None
    matches = [identity for identity in signatures if identity[0] == declaration]
    return matches[0] if len(matches) == 1 else None


def _elaborated_signature_identities(
    item: dict[str, Any],
    *,
    declaration: str,
) -> frozenset[tuple[str, str]] | None:
    """Read exact generator-owned elaborated signatures for one declaration.

    Aggregate-only semantic items may not have an elaborated-signature receipt;
    their declaration identity is still required.  When signatures are present,
    both sides of an exemption must contain the same complete set.  Do not
    infer an association from a row, binder, type, or declaration suffix.
    """

    signatures = _all_elaborated_signature_identities(item)
    if signatures is None or any(
        signature_declaration != declaration
        for signature_declaration, _digest in signatures
    ):
        return None
    return signatures


def _source_item_identity_pairs(
    raw_identities: object,
) -> frozenset[tuple[str, str]] | None:
    """Read exact source-item and keyless semantic SHA pairs fail-closed."""

    if not isinstance(raw_identities, list) or not raw_identities:
        return None
    pairs: set[tuple[str, str]] = set()
    for raw_identity in raw_identities:
        if not isinstance(raw_identity, dict):
            return None
        source_sha = _sha256_value(raw_identity.get("source_map_item_sha256"))
        semantic_sha = _sha256_value(raw_identity.get("source_semantic_sha256"))
        if source_sha is None or semantic_sha is None:
            return None
        pair = (source_sha, semantic_sha)
        if pair in pairs:
            return None
        pairs.add(pair)
    return frozenset(pairs)


def _association_signature_identity(
    raw_signature: object,
    *,
    declaration: str,
) -> tuple[str, str] | None:
    """Read the one association-level elaborated signature exactly."""

    if not isinstance(raw_signature, dict):
        return None
    signature_declaration = raw_signature.get("qualified_declaration")
    signature_sha = _sha256_value(
        raw_signature.get("elaborated_signature_sha256")
    )
    if (
        not isinstance(signature_declaration, str)
        or signature_declaration.strip() != declaration
        or signature_sha is None
    ):
        return None
    return declaration, signature_sha


def transparent_subtype_domain_input_is_accepted_source_data(
    item: dict[str, Any],
    data_antecedent_keys: set[str],
) -> bool:
    """Accept a subtype-domain value only with exact source-domain context.

    The predicate stored by a Lean `Subtype` can be an implicit restriction of
    the paper's source claim.  It is nonpropositional witness data only after
    the generator has structurally shown that it cannot feed the result and
    has attached one exact, byte-pinned `restricted_subtype_domain` context to
    the same reviewed declaration/source/signature association.
    """

    if item.get("kind") != "transparent_subtype_domain_input":
        return False
    if (
        item.get("domain_data_only") is not True
        or item.get("subtype_domain_semantic_data_only") is not True
        or item.get("subtype_expansion_complete") is not True
        or item.get("subtype_carrier_is_definitely_data") is not True
        or str(item.get("subtype_predicate_result_relation") or "").strip()
        or item.get("subtype_predicate_record_dependencies")
        or item.get("subtype_carrier_record_dependencies")
        or item.get("subtype_predicate_record_binder_dependencies")
        or not isinstance(item.get("subtype_predicate_result_bridges"), list)
        or item.get("subtype_predicate_result_bridges")
    ):
        return False
    predicate_expansion = item.get("subtype_predicate_proposition_alias_expansion")
    if not isinstance(predicate_expansion, dict) or predicate_expansion.get(
        "blocked_routes"
    ):
        return False
    if not source_record_item_reuse_eligible(
        item,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    ):
        return False

    reviewed_identity = _reviewed_declaration_identity(item)
    if reviewed_identity is None:
        return False
    declaration, _declaration_sha = reviewed_identity
    signatures = _elaborated_signature_identities(item, declaration=declaration)
    if not signatures:
        return False

    source_association = item.get("source_contract_association")
    if not isinstance(source_association, dict):
        return False
    association_identity = _reviewed_declaration_identity(source_association)
    association_source_pairs = _source_item_identity_pairs(
        source_association.get("source_item_identities")
    )
    association_signature = _association_signature_identity(
        source_association.get("reviewed_elaborated_signature_identity"),
        declaration=declaration,
    )
    if (
        association_identity != reviewed_identity
        or association_source_pairs is None
        or association_signature is None
        or signatures != frozenset({association_signature})
    ):
        return False

    context = item.get("subtype_domain_source_context")
    if not isinstance(context, dict):
        return False
    if (
        context.get("schema") != TRANSPARENT_SUBTYPE_DOMAIN_CONTEXT_SCHEMA
        or context.get("required_kind") != RESTRICTED_SUBTYPE_DOMAIN_CONTEXT_KIND
        or context.get("status") != "satisfied"
    ):
        return False
    context_association = context.get("association")
    if not isinstance(context_association, dict):
        return False
    context_identity = _reviewed_declaration_identity(context_association)
    context_source_pairs = _source_item_identity_pairs(
        context_association.get("source_item_identities")
    )
    context_signature = _association_signature_identity(
        context_association.get("reviewed_elaborated_signature_identity"),
        declaration=declaration,
    )
    if (
        context_identity != reviewed_identity
        or context_source_pairs != association_source_pairs
        or context_signature != association_signature
    ):
        return False

    selected_contexts = context.get("selected_contexts")
    if not isinstance(selected_contexts, list) or not selected_contexts:
        return False
    selected_source_semantic_shas: set[str] = set()
    seen_contexts: set[tuple[str, str]] = set()
    source_semantic_shas = {
        semantic_sha for _source_sha, semantic_sha in association_source_pairs
    }
    for selected in selected_contexts:
        if not isinstance(selected, dict):
            return False
        source_semantic_sha = _sha256_value(selected.get("source_semantic_sha256"))
        context_sha = _sha256_value(selected.get("context_sha256"))
        semantic_context_sha = _sha256_value(
            selected.get("semantic_context_sha256")
        )
        anchors = selected.get("source_anchor_evidence")
        if (
            selected.get("kind") != RESTRICTED_SUBTYPE_DOMAIN_CONTEXT_KIND
            or source_semantic_sha is None
            or context_sha is None
            or semantic_context_sha is None
            or not isinstance(anchors, list)
            or not anchors
        ):
            return False
        context_key = (source_semantic_sha, context_sha)
        if context_key in seen_contexts:
            return False
        seen_contexts.add(context_key)
        selected_source_semantic_shas.add(source_semantic_sha)
    if selected_source_semantic_shas != source_semantic_shas:
        return False

    key = str(item.get("judgment_key") or "").strip()
    return bool(key and key in data_antecedent_keys)


def paper_ids(
    paper_filter: str | None,
    *,
    public_complete: bool = False,
) -> list[str]:
    ids = sorted(
        path.parent.name
        for path in PAPERS.glob("*/status.json")
        if path.parent.name != "TEMPLATE"
    )
    if not public_complete:
        return [paper for paper in ids if not paper_filter or paper == paper_filter]

    selected: list[str] = []
    for paper in ids:
        status_payload = load_payload(PAPERS / paper / "status.json") or {}
        if "repository_visibility" not in status_payload:
            raise ValueError(
                f"papers/{paper}/status.json: public release requires explicit "
                "repository_visibility (`public` or `private_only`)"
            )
        visibility = status_payload.get("repository_visibility")
        if visibility not in {"public", "private_only"}:
            raise ValueError(
                f"papers/{paper}/status.json: repository_visibility must be "
                f"`public` or `private_only`, got {visibility!r}"
            )
        status = str(status_payload.get("status") or "").strip().lower()
        if visibility == "public" and status in FULLY_FORMALIZED_STATUSES:
            selected.append(paper)
    return [paper for paper in selected if not paper_filter or paper == paper_filter]


def load_payload(path: Path) -> dict[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _file_sha256(path: Path) -> str:
    """Hash one file without retaining another large in-memory copy."""

    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError:
        return ""
    return digest.hexdigest()


def load_source_record_audit_snapshot(
    paper: str,
    path: Path,
) -> SourceRecordAuditSnapshot | None:
    """Parse a raw audit once and bind it to the exact input file bytes."""

    try:
        raw = path.read_bytes()
    except OSError:
        return None
    return source_record_audit_snapshot_from_bytes(
        paper,
        raw,
        source_path=path,
    )


def source_record_audit_snapshot_from_bytes(
    paper: str,
    raw: bytes,
    *,
    source_path: Path | None = None,
) -> SourceRecordAuditSnapshot | None:
    """Create the transferable snapshot API from one exact byte string."""

    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(payload, dict):
        return None
    return _issued_source_record_audit_snapshot(
        paper=paper,
        payload=payload,
        source_file_sha256=hashlib.sha256(raw).hexdigest(),
        source_path=source_path,
    )


def _loaded_evidence_integrity_callable(name: str) -> object | None:
    """Return one already loaded policy gate, independent of context ownership."""

    for module_name in (
        "scripts.audit_evidence_integrity",
        "audit_evidence_integrity",
    ):
        candidate = getattr(sys.modules.get(module_name), name, None)
        if callable(candidate):
            return candidate
    return None


def source_record_audit_snapshot_from_evidence_context(
    paper: str,
    context: object,
    *,
    structural_v11_prevalidated: bool = False,
) -> tuple[SourceRecordAuditSnapshot | None, str]:
    """Transfer one already validated exact evidence snapshot without reparsing.

    Only the concrete ``EvidenceRunContext`` issuer is accepted. Its raw audit
    payload is recursively immutable, its byte digest/path came from the same
    read that produced that payload, and its identity replay already bound the
    current statement map and producer/source inputs. The orchestrator retains
    the context and performs its broader final mutation check after conclusion
    provenance finishes.
    """

    evidence_context_types = tuple(
        context_type
        for module_name in (
            "scripts.audit_evidence_integrity",
            "audit_evidence_integrity",
        )
        for module in (sys.modules.get(module_name),)
        for context_type in (getattr(module, "EvidenceRunContext", None),)
        if isinstance(context_type, type)
    )
    if not evidence_context_types:
        if __package__:
            from .audit_evidence_integrity import EvidenceRunContext
        else:  # pragma: no cover - direct script invocation.
            from audit_evidence_integrity import EvidenceRunContext
        evidence_context_types = (EvidenceRunContext,)
    if not isinstance(context, evidence_context_types):
        return None, "caller did not supply an EvidenceRunContext"
    if getattr(context, "issued_by_builder", False) is not True:
        return None, "evidence context was not issued by the exact snapshot builder"
    if context.folder != (PAPERS / paper).resolve():
        return None, "evidence context belongs to a different paper"
    legacy_state = getattr(context, "legacy_source_record_state", None)
    if legacy_state is None:
        return None, "evidence context did not select the legacy source-record lane"
    legacy_inputs = getattr(legacy_state, "inputs", None)
    audit_snapshot = getattr(legacy_inputs, "audit_snapshot", None)
    match_snapshot = getattr(legacy_inputs, "match_snapshot", None)
    configured_path_errors = (
        ("source-record audit", getattr(legacy_inputs, "audit_path_error", "")),
        ("source-record judgment", getattr(legacy_inputs, "match_path_error", "")),
        ("source-proof fidelity ledger", context.source_proof_fidelity_path_error),
    )
    for label, path_error in configured_path_errors:
        if path_error:
            return None, (
                f"evidence context has an invalid configured {label} path: "
                + path_error
            )
    if legacy_state.administrative_projection_rebind_error:
        return None, (
            "evidence context has an invalid administrative projection rebind: "
            + legacy_state.administrative_projection_rebind_error
        )
    structural_v11_current = False
    if legacy_state.source_record_identity_error and structural_v11_prevalidated:
        v11_state = _loaded_evidence_integrity_callable(
            "v11_direct_semantic_review_state"
        )
        if callable(v11_state):
            structural_v11_current, _v11_error = v11_state(
                context.folder,
                context.status,
                context=context,
            )
    if legacy_state.source_record_identity_error and not structural_v11_current:
        return None, (
            "evidence context has no current source-record identity: "
            + legacy_state.source_record_identity_error
        )
    payload = getattr(audit_snapshot, "payload", None)
    digest = getattr(audit_snapshot, "sha256", None) or ""
    if not isinstance(payload, dict) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        return None, "evidence context has no exact source-record payload"
    if str(payload.get("paper") or "").strip() != paper:
        return None, "evidence source-record payload belongs to a different paper"
    administrative_rebind = _normalized_administrative_projection_rebind(
        legacy_state.administrative_projection_rebind
    )
    if (
        legacy_state.administrative_projection_rebind is not None
        and administrative_rebind is None
    ):
        return None, "evidence context has a malformed administrative projection rebind"
    regularity_context = _normalized_configured_assumption_regularity_context(
        legacy_state.configured_assumption_regularity_context
    )
    if (
        legacy_state.configured_assumption_regularity_context is not None
        and regularity_context is None
    ):
        return None, "evidence context has a malformed configured-assumption regularity context"
    return (
        _issued_source_record_audit_snapshot(
            paper=paper,
            payload=payload,
            source_file_sha256=digest,
            source_path=getattr(audit_snapshot, "path", None),
            paper_statement_map_sha256=context.paper_statement_map_sha256,
            source_record_match_path=getattr(match_snapshot, "path", None),
            source_record_match_sha256=(
                getattr(match_snapshot, "sha256", None) or ""
            ),
            current_judgments_override=(
                {}
                if structural_v11_current
                else legacy_state.current_source_record_judgments
            ),
            status_payload_override=context.status_payload,
            paper_statement_map_override=context.statement_map,
            corrected_scope_current_override=legacy_state.corrected_scope_current,
            administrative_projection_rebind_override=(
                administrative_rebind
            ),
            configured_assumption_regularity_context_override=(
                regularity_context
            ),
            configured_assumption_regularity_context_error_override=(
                legacy_state.configured_assumption_regularity_context_error
            ),
            auxiliary_routing_context_override=(
                legacy_state.auxiliary_routing_context
            ),
            auxiliary_routing_context_error_override=(
                legacy_state.auxiliary_routing_context_error
            ),
            input_raw_bytes_override={
                input_snapshot.path.resolve(): input_snapshot.raw_bytes
                for input_snapshot in context.input_snapshots
            },
            identity_validated=not structural_v11_current,
            structural_v11_validated=structural_v11_current,
            payload_is_immutable=True,
        ),
        "",
    )


def source_record_audit_snapshot_mutation_error(
    snapshot: SourceRecordAuditSnapshot,
) -> str:
    """Reject a run-scoped snapshot when its exact watched bytes changed."""

    if not snapshot.content_bound:
        return "source-record audit snapshot has no exact content binding"
    if snapshot.source_path is not None:
        current_digest = _file_sha256(snapshot.source_path)
        if not current_digest:
            return "source-record audit snapshot file is missing or unreadable"
        if current_digest != snapshot.source_file_sha256:
            return "source-record audit snapshot bytes changed during the audit"
    if snapshot.paper_statement_map_sha256:
        current_map_digest = current_paper_statement_map_sha256(
            PAPERS / snapshot.paper
        )
        if current_map_digest != snapshot.paper_statement_map_sha256:
            return "paper statement-map bytes changed during the audit"
    if snapshot.source_record_match_sha256:
        if snapshot.source_record_match_path is None:
            return "source-record judgment snapshot has no bound source path"
        current_match_digest = _file_sha256(snapshot.source_record_match_path)
        if current_match_digest != snapshot.source_record_match_sha256:
            return "source-record judgment bytes changed during the audit"
    return ""


def circular_candidates(item: dict[str, Any]) -> str:
    parts: list[str] = []
    for raw_candidate in item.get("rejected_constructors") or []:
        if not isinstance(raw_candidate, dict):
            continue
        name = str(raw_candidate.get("declaration") or "unnamed constructor")
        reasons = [
            str(reason)
            for reason in (
                raw_candidate.get("circular_inputs")
                or raw_candidate.get("conditional_inputs")
                or []
            )
            if str(reason)
        ]
        parts.append(name + (" <- " + "; ".join(reasons[:3]) if reasons else ""))
    return " | ".join(parts)


def bool_certificate_finding_message(item: dict[str, Any]) -> str:
    """Describe proof-bearing Boolean debt without relying on checker names."""

    checker = str(item.get("checker") or "local Boolean checker")
    if item.get("input_origin") == "dependent_if_guard":
        return (
            f"{checker} unfolds to a proof-bearing proposition encoded by `decide`, "
            "a truth-valued `if`, or a finite Boolean wrapper inside a dependent result-level "
            "`if` guard; moving the obligation under `if` does not construct it"
        )
    return (
        f"{checker} unfolds to a proof-bearing proposition encoded by `decide`, "
        "a truth-valued `if`, or a finite Boolean wrapper over one; "
        "do not hide a theorem/model obligation behind `checker = true`"
    )


def selector_certificate_finding_message(item: dict[str, Any]) -> str:
    """Describe proof-bearing Option-success debt without selector-name heuristics."""

    selector = str(item.get("selector") or "local Option selector")
    return (
        f"{selector} returns `some` only under a proof-bearing proposition; "
        "do not hide that theorem/model obligation behind `selector = some value`"
    )


def _authenticated_overlay_union_module() -> Any:
    """Load the shared transport authority only when current evidence needs it."""

    try:
        from scripts import source_record_authenticated_overlay_union as overlay_union
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_authenticated_overlay_union as overlay_union
    return overlay_union


def _copy_loaded_source_record_overlay_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    return _authenticated_overlay_union_module().copy_loader_authenticated_or_plain_current_item(
        value, updates
    )


def _project_current_source_record_response_association_pins(
    audit_payload: Mapping[str, Any],
    current: Mapping[str, Mapping[str, Any]],
    *,
    statement_map: Mapping[str, Any] | None = None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> dict[str, dict[str, Any]]:
    """Apply the same raw-derived association projection as the evidence gate.

    Conclusion provenance has a separate authenticated loader because it
    performs a different downstream analysis.  It must nevertheless consume
    the same response surface, so this final composition repeats no matching
    logic and delegates pin construction to the shared raw-group projector.
    """

    groups, group_errors = raw_source_record_obligation_groups(audit_payload)
    if group_errors:
        return {}
    projected_current: dict[str, dict[str, Any]] = {}
    for raw_key, value in current.items():
        key = str(raw_key).strip()
        if not key or not isinstance(value, Mapping):
            continue
        group = groups.get(key)
        raw_members = group.get("raw_members") if isinstance(group, Mapping) else None
        if not isinstance(raw_members, list):
            continue
        association_members = [
            item
            for member in raw_members
            if isinstance(member, tuple)
            and len(member) == 2
            and isinstance(member[1], Mapping)
            and isinstance(member[1].get("source_contract_association"), Mapping)
            for item in (member[1],)
        ]
        if (
            not association_members
            and not response_claims_configured_assumption_formalization_regularity(
                value
            )
        ):
            # Some semantic-model rows are current, independently reviewed
            # model records rather than source-routed judgments. There is no
            # association pin to project for them; retaining their already
            # validated item receipt preserves the longstanding v10 path. A
            # configured regularity is also non-source-credit, but it does
            # require its separate raw-derived structural context pin below.
            projected_current[key] = _copy_loaded_source_record_overlay_item(value)
            continue
        projected, error = project_source_record_response_association_pins(
            raw_members,
            value,
            judgment_key=key,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=(
                configured_assumption_formalization_regularity_context
            ),
        )
        if error or projected is None:
            continue
        projected_current[key] = _copy_loaded_source_record_overlay_item(
            value, projected
        )
    return projected_current


def _current_judgments_from_payload(
    paper: str,
    audit_payload: dict[str, Any],
    payload: dict[str, Any],
    *,
    paper_dir: Path | None = None,
    authenticated_overlay_lane: object | None = None,
) -> dict[str, dict[str, Any]]:
    if payload.get("schema") != 1 or payload.get("paper") not in {None, paper}:
        return {}
    raw_items = payload.get("items") or payload.get("field_judgments") or {}
    if not isinstance(raw_items, dict):
        return {}
    overlay_union = None
    if authenticated_overlay_lane is not None:
        overlay_union = _authenticated_overlay_union_module()
        if (
            not isinstance(
                authenticated_overlay_lane,
                overlay_union.AuthenticatedCurrentOverlayLane,
            )
            or raw_items is not authenticated_overlay_lane.items
        ):
            return {}
    required_prompt_version = str(audit_payload.get("prompt_version") or "").strip()
    required_audit_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    required_item_digests = current_item_digests(audit_payload)
    required_item_digest_pins = current_item_digest_pins(audit_payload)
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_audit_digest = str(payload.get("source_record_audit_sha256") or "").strip()
    payload_validator = payload.get("validator") or payload.get("model") or payload.get("judge")
    payload_timestamp = payload.get("validated_at") or payload.get("timestamp") or payload.get(
        "generated_at"
    )
    out: dict[str, dict[str, Any]] = {}
    for key, value in raw_items.items():
        if not isinstance(value, dict):
            continue
        if archived_source_record_transport_item_field(value):
            continue
        raw_key = str(key)
        loaded_overlay_entry = bool(
            authenticated_overlay_lane is not None
            and overlay_union is not None
            and overlay_union.authenticated_current_overlay_item(
                authenticated_overlay_lane, value
            )
        )
        if authenticated_overlay_lane is not None and not loaded_overlay_entry:
            continue
        if (
            authenticated_overlay_lane is None
            and serialized_source_record_overlay_labels(value)
        ):
            continue
        item_prompt_version = str(
            value.get("prompt_version") or payload_prompt_version
        ).strip()
        item_audit_digest = str(
            value.get("source_record_audit_sha256") or payload_audit_digest
        ).strip()
        item_digest = str(value.get("source_record_item_sha256") or "").strip()
        item_digest_schema = value.get("source_record_item_digest_schema")
        required_item_digest = required_item_digests.get(raw_key)
        item_digest_pins = judgment_item_digest_pins(value)
        required_item_pins = required_item_digest_pins.get(raw_key)
        audit_digest_current = bool(
            required_audit_digest and item_audit_digest == required_audit_digest
        )
        if loaded_overlay_entry:
            # Authenticated overlays recompare the complete generated semantic
            # descriptor. Do not misread historical aggregate provenance as
            # ordinary freshness or permit a name/key remap.
            item_digest_current = True
            item_digest_pins_current = True
            audit_digest_current = False
        else:
            item_digest_current = bool(
                item_digest
                and required_item_digest
                and isinstance(item_digest_schema, int)
                and (item_digest_schema, item_digest) == required_item_digest
            )
            item_digest_pins_current = bool(
                item_digest_pins
                and required_item_pins
                and item_digest_pins == required_item_pins
                and (
                    not item_digest
                    or (
                        isinstance(item_digest_schema, int)
                        and any(
                            schema == item_digest_schema and digest == item_digest
                            for _kind, schema, digest in item_digest_pins
                        )
                    )
                )
            )
        if item_prompt_version != required_prompt_version or not (
            audit_digest_current or item_digest_current or item_digest_pins_current
        ):
            continue
        validator = (
            value.get("validator") or value.get("model") or value.get("judge") or payload_validator
        )
        timestamp = (
            value.get("validated_at")
            or value.get("timestamp")
            or value.get("generated_at")
            or payload_timestamp
        )
        if validator and timestamp:
            out[raw_key] = _copy_loaded_source_record_overlay_item(
                value,
                {
                    "prompt_version": item_prompt_version,
                    "source_record_audit_sha256": item_audit_digest,
                    "source_record_item_sha256": item_digest,
                    "source_record_item_digest_schema": item_digest_schema,
                },
            )
    return out


def current_judgments(paper: str, audit_payload: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Load ordinary judgments plus authenticated narrow-reuse overlays."""

    folder = PAPERS / paper
    if archived_source_record_transport_artifacts(folder):
        return {}
    path = folder / "audit" / "source_record_match_llm.json"
    if not path.exists():
        path = folder / "source_record_match_llm.json"
    sidecar_payload = load_payload(path) or {}
    ordinary = _current_judgments_from_payload(
        paper, audit_payload, sidecar_payload, paper_dir=folder
    )
    consumed_overlay_labels = (
        "differential",
        "semantic_rebind",
    )
    present_overlay_labels = source_record_overlay_labels_with_artifacts(
        folder, lane_labels=consumed_overlay_labels
    )
    overlay_current: dict[str, dict[str, dict[str, Any]]] = {}
    if present_overlay_labels:
        overlay_union = _authenticated_overlay_union_module()
        try:
            lanes = overlay_union.load_authenticated_current_overlay_lanes(
                folder,
                paper,
                audit_payload,
                lane_labels=present_overlay_labels,
            )
        except overlay_union.SourceRecordAuthenticatedOverlayUnionError:
            return {}
        for lane in lanes:
            overlay_current[lane.label] = _current_judgments_from_payload(
                paper,
                audit_payload,
                {"schema": 1, "paper": paper, "items": lane.items},
                authenticated_overlay_lane=lane,
            )
    # An overlay remains authoritative over stale ordinary evidence, but an
    # ordinary response carrying the exact current aggregate receipt is newer
    # evidence and wins over every overlay lane.
    current_raw_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    ordinary_with_current_receipt = {
        key: value
        for key, value in ordinary.items()
        if current_raw_digest
        and str(value.get("source_record_audit_sha256") or "").strip()
        == current_raw_digest
    }
    composed = {
        **overlay_current.get("semantic_rebind", {}),
        **ordinary,
        **overlay_current.get("differential", {}),
        **ordinary_with_current_receipt,
    }
    if canonical_source_record_match_sidecar_path(path, folder):
        coverage_error = canonical_source_record_sidecar_effective_coverage_error(
            audit_payload,
            sidecar_payload,
            effective_items=composed,
            paper_dir=folder,
            sidecar_path=path,
        )
        if coverage_error:
            # Conclusion provenance may not be the side door through which a
            # canonical partial response ledger gains credit.  The shared
            # gate verifies selected-current descriptor/overlay provenance
            # without using row, source-key, or declaration-name matching.
            return {}
    statement_map_payload = load_payload(
        folder / "audit" / "paper_statement_map.json"
    )
    statement_map = (
        statement_map_payload if isinstance(statement_map_payload, Mapping) else None
    )
    status_payload = load_payload(folder / "status.json")
    regularity_context, _regularity_context_error = (
        load_configured_assumption_formalization_regularity_context(
            folder,
            audit_payload,
            status_payload=(
                status_payload if isinstance(status_payload, Mapping) else None
            ),
        )
    )
    return _project_current_source_record_response_association_pins(
        audit_payload,
        composed,
        statement_map=statement_map,
        configured_assumption_formalization_regularity_context=regularity_context,
    )


def current_item_digests(audit_payload: dict[str, Any]) -> dict[str, tuple[int, str]]:
    """Return unambiguous current per-item semantic digests by judgment key.

    A conclusion dependency is richer than the duplicate boundary-input view.
    If the two differ, no *scalar* item digest proves that the sidecar reviewed
    both. A separately validated exact pin set can do so; see
    ``current_item_digest_pins``.
    """

    candidate_digests: dict[str, set[tuple[int, str]]] = {}
    for section in SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS:
        raw_items = audit_payload.get(section) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not source_record_item_reuse_eligible(
                item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            schema = item.get("source_record_item_digest_schema")
            digest = str(item.get("source_record_item_sha256") or "").strip()
            if key and isinstance(schema, int) and digest:
                candidate_digests.setdefault(key, set()).add((schema, digest))
    return {
        key: next(iter(digests))
        for key, digests in candidate_digests.items()
        if len(digests) == 1
    }


def current_item_digest_pins(
    audit_payload: dict[str, Any],
) -> dict[str, frozenset[tuple[str, int, str]]]:
    """Return every current semantic item pin for each generated judgment key.

    A sidecar may reuse a source-record judgment after the aggregate receipt
    changes only when it pins the *complete* generated semantic surface for
    that judgment.  Each pin includes the generated type-shape kind, digest
    schema, and semantic digest; matching the exact set cannot be satisfied by
    retaining only the weaker boundary view of a richer conclusion dependency.
    """

    candidate_pins: dict[str, set[tuple[str, int, str]]] = {}
    for section in SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS:
        raw_items = audit_payload.get(section) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not source_record_item_reuse_eligible(
                item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            kind = str(item.get("kind") or "").strip()
            schema = item.get("source_record_item_digest_schema")
            digest = str(item.get("source_record_item_sha256") or "").strip()
            if key and kind and isinstance(schema, int) and digest:
                candidate_pins.setdefault(key, set()).add((kind, schema, digest))
    return {
        key: frozenset(pins)
        for key, pins in candidate_pins.items()
        if pins
    }


def judgment_item_digest_pins(
    judgment: dict[str, Any],
) -> frozenset[tuple[str, int, str]] | None:
    """Parse a sidecar's complete generated-item pin set fail-closed."""

    raw_pins = judgment.get("source_record_item_sha256s")
    if not isinstance(raw_pins, list) or not raw_pins:
        return None
    pins: set[tuple[str, int, str]] = set()
    for raw_pin in raw_pins:
        if not isinstance(raw_pin, dict):
            return None
        kind = str(raw_pin.get("kind") or "").strip()
        schema = raw_pin.get("source_record_item_digest_schema")
        digest = str(raw_pin.get("source_record_item_sha256") or "").strip()
        if not kind or not isinstance(schema, int) or not digest:
            return None
        pins.add((kind, schema, digest))
    if len(pins) != len(raw_pins):
        return None
    return frozenset(pins)


def source_antecedents_with_classifications(
    judgments: dict[str, dict[str, Any]], classifications: set[str]
) -> set[str]:
    out: set[str] = set()
    for key, item in judgments.items():
        classification = str(
            item.get("classification")
            or item.get("judgment")
            or item.get("verdict")
            or item.get("status")
            or ""
        ).strip()
        location = str(
            item.get("source_location")
            or item.get("source_evidence")
            or ""
        ).strip()
        if classification in classifications and EXACT_SOURCE_LOCATOR_RE.search(location):
            out.add(key)
    return out


def exact_source_antecedents(judgments: dict[str, dict[str, Any]]) -> set[str]:
    return source_antecedents_with_classifications(
        judgments, {"validated_source_assumption"}
    )


def theorem_realization_contract_requested(
    status_payload: Mapping[str, Any],
    statement_map: Mapping[str, Any] | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Whether this paper must use the v11 realization lane.

    The generated occurrence ledger is diagnostic infrastructure and is
    intentionally emitted for ordinary v10 papers as well. Its mere presence
    is not activation. Explicit switches activate the lane, and the shared
    transition gate additionally activates it for a new paper; a material
    repair of a trusted legacy-v10 paper remains on the current item-level v10
    lane unless it explicitly upgrades.
    """

    return source_spec_correspondence_requested(
        dict(status_payload),
        dict(statement_map) if isinstance(statement_map, Mapping) else None,
        folder=folder,
    )


def theorem_realization_contract_active(
    audit_payload: Mapping[str, Any],
    status_payload: Mapping[str, Any],
    statement_map: Mapping[str, Any] | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Whether a required v11 lane has its current ledger.

    Callers that need strict acceptance semantics use this rather than the raw
    schema field.  If the paper requested the lane but the ledger is absent,
    the dedicated contract gate reports that failure while compatibility code
    remains in its legacy interpretation instead of manufacturing unrelated
    provenance errors.
    """

    return bool(
        theorem_realization_contract_requested(
            status_payload, statement_map, folder=folder
        )
        and audit_payload.get("theorem_realization_contract_schema") == 1
    )


def nonpropositional_source_data_antecedents(
    judgments: dict[str, dict[str, Any]], *, strict_realization: bool = False
) -> set[str]:
    """Return legacy data receipts, never schema-1 automatic credit.

    A non-``Prop`` sort is not provenance in the v11 theorem-realization
    lane. Historical v10 consumers still use their explicit source-record
    receipts for dashboard interpretation, so retain that read-only adapter
    unless the caller explicitly requests strict realization handling.
    """

    if strict_realization:
        return set()
    return source_antecedents_with_classifications(
        judgments, {"nonpropositional_witness_data"}
    )


def _context_transport_copy(value: object) -> object:
    """Project authority containers to JSON-shaped mutable base containers."""

    if isinstance(value, Mapping):
        return {str(key): _context_transport_copy(item) for key, item in value.items()}
    if isinstance(value, (list, tuple)):
        return [_context_transport_copy(item) for item in value]
    return value


def _deep_freeze_context_value(value: object) -> object:
    """Freeze authority data while preserving ``dict``/``list`` interfaces."""

    evidence_module = sys.modules.get(
        "scripts.audit_evidence_integrity"
    ) or sys.modules.get("audit_evidence_integrity")
    if evidence_module is None:
        if __package__:
            from . import audit_evidence_integrity as evidence_module
        else:  # pragma: no cover - direct script invocation.
            import audit_evidence_integrity as evidence_module
    return evidence_module._freeze_json(_context_transport_copy(value))


def _normalized_administrative_projection_rebind(
    context: object,
) -> ValidatedAdministrativeProjectionRebind | None:
    """Normalize one validated cross-module authority into immutable maps."""

    if context is None:
        return None
    association_rebinds = getattr(context, "association_rebinds", None)
    association_bindings = getattr(context, "association_bindings", None)
    rebound_association_bindings = getattr(
        context, "rebound_association_bindings", None
    )
    rebind_maps = (
        association_rebinds,
        association_bindings,
        rebound_association_bindings,
    )
    if not all(
        isinstance(entries, Mapping)
        and all(isinstance(key, str) and isinstance(value, Mapping) for key, value in entries.items())
        for entries in rebind_maps
    ):
        return None
    try:
        try:
            from scripts.source_record_target_disposition import (
                ValidatedAdministrativeProjectionRebind as active_rebind_type,
            )
        except ModuleNotFoundError:  # pragma: no cover - direct-script imports.
            from source_record_target_disposition import (
                ValidatedAdministrativeProjectionRebind as active_rebind_type,
            )
    except ModuleNotFoundError:  # pragma: no cover - no disposition authority.
        return None
    return active_rebind_type(
        association_rebinds=cast(
            Mapping[str, Mapping[str, object]],
            _deep_freeze_context_value(association_rebinds),
        ),
        association_bindings=cast(
            Mapping[str, Mapping[str, object]],
            _deep_freeze_context_value(association_bindings),
        ),
        rebound_association_bindings=cast(
            Mapping[str, Mapping[str, object]],
            _deep_freeze_context_value(rebound_association_bindings),
        ),
    )


def load_current_administrative_projection_rebind_context(
    paper: str,
    audit_payload: Mapping[str, Any],
    status_payload: Mapping[str, Any],
) -> tuple[ValidatedAdministrativeProjectionRebind | None, str]:
    """Load one optional rebind while preserving invalid-receipt errors."""

    folder = PAPERS / paper
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        review_surface = {}
    context, error = source_record_target_disposition_rebind_context(
        folder,
        dict(review_surface),
        dict(audit_payload),
    )
    if error:
        return None, error
    normalized = _normalized_administrative_projection_rebind(context)
    if context is not None and normalized is None:
        return None, "validated administrative projection rebind is malformed"
    return normalized, ""


def current_administrative_projection_rebind_context(
    paper: str,
    audit_payload: Mapping[str, Any],
    status_payload: Mapping[str, Any],
) -> ValidatedAdministrativeProjectionRebind | None:
    """Compatibility projection of the exact optional rebind context."""

    context, _error = load_current_administrative_projection_rebind_context(
        paper, audit_payload, status_payload
    )
    return context


def administrative_projection_rebind_context_or_override(
    paper: str,
    audit_payload: Mapping[str, Any],
    status_payload: Mapping[str, Any],
    override: object = _CONTEXT_OVERRIDE_UNSET,
) -> ValidatedAdministrativeProjectionRebind | None:
    """Use a transferred validation result, including a validated absence."""

    if override is _CONTEXT_OVERRIDE_UNSET:
        return current_administrative_projection_rebind_context(
            paper, audit_payload, status_payload
        )
    if isinstance(override, ValidatedAdministrativeProjectionRebind):
        return override
    return _normalized_administrative_projection_rebind(override)


def _normalized_configured_assumption_regularity_context(
    context: object,
) -> ConfiguredAssumptionFormalizationRegularityContext | None:
    """Normalize one configured-regularity authority into immutable maps."""

    if context is None:
        return None
    raw_audit_sha256 = getattr(context, "raw_audit_sha256", None)
    matches = getattr(context, "matches_by_structural_identity", None)
    if not isinstance(raw_audit_sha256, str) or not isinstance(matches, Mapping):
        return None
    return ConfiguredAssumptionFormalizationRegularityContext(
        raw_audit_sha256=raw_audit_sha256,
        matches_by_structural_identity=cast(
            Mapping[str, Any], _deep_freeze_context_value(matches)
        ),
    )


def configured_assumption_regularity_context_or_override(
    folder: Path,
    audit_payload: Mapping[str, Any],
    status_payload: Mapping[str, Any],
    override: object = _CONTEXT_OVERRIDE_UNSET,
    error_override: str | None = None,
) -> tuple[ConfiguredAssumptionFormalizationRegularityContext | None, str]:
    """Use the run snapshot's regularity result without reopening its ledger."""

    if override is _CONTEXT_OVERRIDE_UNSET:
        context, error = load_configured_assumption_formalization_regularity_context(
            folder,
            dict(audit_payload),
            status_payload=status_payload,
        )
        return _normalized_configured_assumption_regularity_context(context), error
    return (
        _normalized_configured_assumption_regularity_context(override),
        error_override or "",
    )


def source_input_has_current_target_disposition(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    statement_map: Mapping[str, Any] | None,
    source_proof_fidelity: Mapping[str, Any] | None,
    status: str,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> bool:
    """Return whether a judgment affirmatively claims valid source credit.

    ``source_input_target_disposition_errors`` is a conditional validator: a
    response that makes no source-credit claim correctly has no disposition
    errors. Receipt builders must therefore check the claim class first;
    interpreting ``no errors`` alone as evidence would grant source credit to
    semantic-review, data, or container labels.
    """

    if (
        str(judgment.get("classification") or "").strip()
        not in INPUT_SOURCE_CREDIT_CLASSIFICATIONS
    ):
        return False
    return not source_input_target_disposition_errors(
        item,
        judgment,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        status=status,
        administrative_projection_rebind=administrative_projection_rebind,
        configured_assumption_formalization_regularity_context=(
            configured_assumption_formalization_regularity_context
        ),
    )


def current_approved_source_convention_antecedent_keys(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> tuple[set[str], set[str]]:
    """Read historical convention receipts outside the active schema-1 lane.

    A convention can be used only through an occurrence-indexed, anchored
    correction/additional-assumption contract. It is not an independently
    accepted theorem input or record field merely because a sidecar labels it
    a convention.
    """

    folder = PAPERS / paper
    statement_map = (
        paper_statement_map_override
        if paper_statement_map_override is not None
        else load_payload(folder / "audit" / "paper_statement_map.json")
    )
    source_proof_fidelity = audit_payload.get("source_proof_fidelity")
    if not isinstance(statement_map, dict) or not isinstance(
        source_proof_fidelity, dict
    ):
        return set(), set()
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json") or {}
    )
    if theorem_realization_contract_active(
        audit_payload, status_payload, statement_map, folder=folder
    ):
        return set(), set()
    status = str(status_payload.get("status") or "")
    administrative_projection_rebind = (
        administrative_projection_rebind_context_or_override(
            paper,
            audit_payload,
            status_payload,
            administrative_projection_rebind_override,
        )
    )

    def accepted(item: Mapping[str, Any]) -> bool:
        key = str(item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        if not key or not isinstance(judgment, Mapping):
            return False
        if (
            str(judgment.get("classification") or "").strip()
            == FORMALIZATION_REGULARITY_CLASSIFICATION
        ):
            return False
        location = str(
            judgment.get("source_location") or judgment.get("source_evidence") or ""
        ).strip()
        if not EXACT_SOURCE_LOCATOR_RE.search(location):
            return False
        return not approved_source_convention_antecedent_errors(
            item,
            judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
        )

    input_keys = {
        str(item.get("judgment_key"))
        for item in audit_payload.get("conclusion_dependency_items") or []
        if isinstance(item, Mapping) and accepted(item)
    }
    field_keys = {
        str(item.get("judgment_key"))
        for item in audit_payload.get("recursive_field_items") or []
        if isinstance(item, Mapping) and accepted(item)
    }
    return input_keys, field_keys


def _current_source_item_semantic_sha256_by_key(
    statement_map: Mapping[str, Any] | None,
) -> dict[str, str]:
    """Return current semantic source identities without Lean-name routing."""

    if not isinstance(statement_map, Mapping):
        return {}
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return {}
    out: dict[str, str] = {}
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_item, Mapping):
            continue
        digest = source_record_source_item_semantic_sha256(dict(raw_item), "")
        if re.fullmatch(r"[0-9a-f]{64}", digest):
            out[key] = digest
    return out


def theorem_realization_component_occurrence_index(
    audit_payload: Mapping[str, Any],
) -> dict[str, frozenset[str]]:
    """Index every current component occurrence by its original judgment key.

    The synthetic ledger key is occurrence-specific, while source-record
    judgments deliberately remain reusable by their original key.  This index
    is therefore required before a scalar sidecar contract can be accepted:
    it proves whether that source judgment is associated with exactly one live
    material occurrence.
    """

    indexed: dict[str, set[str]] = {}
    for _section, raw_component in theorem_realization_components(audit_payload):
        if not isinstance(raw_component, Mapping):
            continue
        source_key = str(
            raw_component.get("source_judgment_key")
            or raw_component.get("judgment_key")
            or ""
        ).strip()
        component_sha = source_claim_component_sha256(raw_component)
        if not source_key or not re.fullmatch(r"[0-9a-f]{64}", component_sha):
            continue
        indexed.setdefault(source_key, set()).add(component_sha)
    return {
        key: frozenset(values)
        for key, values in indexed.items()
        if values
    }


def theorem_realization_components_by_source_key(
    audit_payload: Mapping[str, Any],
) -> dict[str, tuple[Mapping[str, Any], ...]]:
    """Return generated ledger occurrences grouped by their original key."""

    grouped: dict[str, list[Mapping[str, Any]]] = {}
    for _section, raw_component in theorem_realization_components(audit_payload):
        if not isinstance(raw_component, Mapping):
            continue
        source_key = str(
            raw_component.get("source_judgment_key")
            or raw_component.get("judgment_key")
            or ""
        ).strip()
        if source_key:
            grouped.setdefault(source_key, []).append(raw_component)
    return {
        key: tuple(value)
        for key, value in grouped.items()
    }


def current_source_claim_atom_receipts(
    audit_payload: Mapping[str, Any],
) -> tuple[SourceClaimAtomReceipt, ...]:
    """Read only generated current source-atom contexts as atom receipts.

    The source-record generator has already byte-checked the quoted source
    span when it attaches these contexts.  This adapter merely joins its atom
    route records to the current semantic digest; it never infers an atom from
    a name or a whole parent theorem item.
    """

    receipts: set[SourceClaimAtomReceipt] = set()
    for raw_item in audit_payload.get("semantic_model_items") or []:
        if not isinstance(raw_item, Mapping):
            continue
        association = raw_item.get("source_claim_atom_association")
        contexts = raw_item.get("source_claim_atom_contexts")
        if not isinstance(association, Mapping) or not isinstance(contexts, list):
            continue
        route_by_atom: dict[tuple[str, str], str] = {}
        for raw_route in association.get("source_claim_atom_routes") or []:
            if not isinstance(raw_route, Mapping):
                continue
            source_key = str(raw_route.get("source_key") or "").strip()
            atom_id = str(raw_route.get("atom_id") or "").strip()
            digest = str(
                raw_route.get("source_claim_atom_semantic_sha256") or ""
            ).strip().lower()
            if (
                source_key
                and atom_id
                and re.fullmatch(r"[0-9a-f]{64}", digest)
            ):
                route_by_atom[(atom_id, digest)] = source_key
        for raw_context in contexts:
            if not isinstance(raw_context, Mapping):
                continue
            atom_id = str(raw_context.get("id") or "").strip()
            digest = str(
                raw_context.get("source_claim_atom_semantic_sha256") or ""
            ).strip().lower()
            locator = str(raw_context.get("source_locator") or "").strip()
            source_key = route_by_atom.get((atom_id, digest), "")
            if (
                source_key
                and atom_id
                and re.fullmatch(r"[0-9a-f]{64}", digest)
                and EXACT_SOURCE_LOCATOR_RE.search(locator)
            ):
                receipts.add(
                    SourceClaimAtomReceipt(
                        source_item_key=source_key,
                        atom_id=atom_id,
                        atom_semantic_sha256=digest,
                        source_locator=locator,
                    )
                )
    return tuple(
        sorted(
            receipts,
            key=lambda receipt: (
                receipt.source_item_key,
                receipt.atom_id,
                receipt.atom_semantic_sha256,
            ),
        )
    )


def _generated_component_premise_or_result_role(
    component: Mapping[str, Any],
) -> str | None:
    """Read a premise/result role only from generated Lean occurrence data."""

    roles: set[str] = set()
    if str(component.get("result_occurrence_role") or "").strip() == "provided_result":
        roles.add("result")

    outer_route = str(component.get("lean_outer_binder_route") or "").strip()
    outer_indices = component.get("lean_outer_binder_indices")
    if (
        outer_route == "outer_telescope"
        and isinstance(outer_indices, list)
        and outer_indices
        and all(type(index) is int and index >= 0 for index in outer_indices)
    ):
        roles.add("premise")

    binder_atoms = _generated_binder_atom_identities(
        component.get("elaborated_outer_binder_atoms")
    )
    if binder_atoms:
        roles.add("premise")
    return next(iter(roles)) if len(roles) == 1 else None


def _generated_component_literal_type(component: Mapping[str, Any]) -> str:
    """Return one generated expanded component type without name inference."""

    for field in ("expanded_input_type", "expanded_binder_type", "type"):
        value = component.get(field)
        if isinstance(value, str) and value.strip():
            return value
    return ""


def _generated_component_type_witness_identity(
    component: Mapping[str, Any],
    *,
    structural_type_sha256: str,
) -> tuple[Mapping[str, Any], str] | None:
    """Return a complete Lean-emitted identity for a type-witness result."""

    receipt = component.get("elaborated_type_witness_payload_receipt")
    path = str(component.get("elaborated_witness_path") or "").strip()
    if not isinstance(receipt, Mapping) or not path:
        return None
    if (
        receipt.get("schema") != 1
        or str(receipt.get("status") or "").strip() != "ok"
        or str(receipt.get("occurrence_role") or "").strip()
        != str(component.get("result_occurrence_role") or "").strip()
        or str(receipt.get("path") or "").strip() != path
        or _sha256_value(receipt.get("normalized_type_sha256"))
        != structural_type_sha256
    ):
        return None
    return receipt, path


def _generated_result_certificate_allows_aggregate_signatures(
    component: Mapping[str, Any], *, section: str
) -> bool:
    """Whether the generator owns this component's aggregate signature set."""

    structural_sha = _sha256_value(component.get("structural_type_sha256"))
    return bool(
        section == "type_valued_certificate_result_items"
        and str(component.get("source_component_section") or "").strip()
        == section
        and str(component.get("source_claim_component_kind") or "").strip()
        == "result_type_certificate"
        and _generated_component_premise_or_result_role(component) == "result"
        and structural_sha is not None
        and _generated_component_type_witness_identity(
            component, structural_type_sha256=structural_sha
        )
        is not None
    )


def _substantive_correspondence_text(value: object, *, minimum_words: int) -> bool:
    text = str(value or "").strip()
    return bool(
        len(text) >= 24
        and len(re.findall(r"[A-Za-z0-9]+", text)) >= minimum_words
    )


def _current_direct_semantic_correspondence(
    component: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    semantic_key: str,
    effective_association: Mapping[str, Any],
    current_parent_association_sha256: str,
) -> bool:
    """Validate an occurrence-indexed substantive model correspondence.

    A definition/model source kind is not enough to justify a proposition or
    an otherwise unclassified component.  This stronger route requires the
    human-reviewed occurrence contract to reproduce every generated source,
    declaration, signature, and type identity and to explain the literal
    source/Lean semantic relation.  Nothing here selects a route from a row,
    declaration, binder, section, or reviewer-classification spelling.
    """

    component_key = str(component.get("judgment_key") or "").strip()
    source_key = str(
        component.get("source_judgment_key")
        or component.get("judgment_key")
        or ""
    ).strip()
    component_sha = source_claim_component_sha256(component)
    structural_sha = _sha256_value(
        component.get("source_claim_component_structural_type_sha256")
        or component.get("structural_type_sha256")
    )
    judgment = judgments.get(source_key)
    if (
        not component_key
        or not source_key
        or not component_sha
        or structural_sha is None
        or not isinstance(judgment, Mapping)
    ):
        return False

    raw_contracts = judgment.get("source_claim_semantic_contracts")
    if not isinstance(raw_contracts, Mapping):
        return False
    contract = raw_contracts.get(component_sha)
    if not isinstance(contract, Mapping):
        return False
    correspondence = contract.get("source_domain_correspondence")
    if (
        contract.get("schema") != 1
        or str(contract.get("route") or "").strip()
        != "source_domain_correspondence"
        or _sha256_value(contract.get("component_sha256")) != component_sha
        or _sha256_value(contract.get("structural_type_sha256"))
        != structural_sha
        or not isinstance(correspondence, Mapping)
        or _sha256_value(correspondence.get("component_sha256"))
        != component_sha
        or str(correspondence.get("source_model_judgment_key") or "").strip()
        != semantic_key
        or "source_model_judgment_keys" in correspondence
    ):
        return False

    substantive = correspondence.get("semantic_correspondence")
    if not isinstance(substantive, Mapping) or substantive.get("schema") != 1:
        return False
    literal_type = _generated_component_literal_type(component)
    type_witness_identity = _generated_component_type_witness_identity(
        component, structural_type_sha256=structural_sha
    )
    occurrence_role = _generated_component_premise_or_result_role(component)
    source_identities = effective_association.get("source_item_identities")
    if (
        (not literal_type and type_witness_identity is None)
        or occurrence_role is None
        or not isinstance(source_identities, list)
        or not source_identities
        or any(not isinstance(identity, Mapping) for identity in source_identities)
    ):
        return False
    source_locators = [
        str(identity.get("source_location") or "").strip()
        for identity in source_identities
    ]
    if any(
        not locator or not EXACT_SOURCE_LOCATOR_RE.search(locator)
        for locator in source_locators
    ):
        return False

    if len(source_identities) == 1:
        source_correspondence_matches = bool(
            str(substantive.get("source_locator") or "").strip()
            == source_locators[0]
            and "source_locators" not in substantive
            and "source_semantic_clauses" not in substantive
            and _substantive_correspondence_text(
                substantive.get("source_semantic_clause"), minimum_words=4
            )
        )
    else:
        raw_clauses = substantive.get("source_semantic_clauses")
        clauses = raw_clauses if isinstance(raw_clauses, list) else []
        source_correspondence_matches = bool(
            "source_locator" not in substantive
            and "source_semantic_clause" not in substantive
            and substantive.get("source_locators") == source_locators
            and len(clauses) == len(source_identities)
        )
        if source_correspondence_matches:
            for identity, locator, clause in zip(
                source_identities, source_locators, clauses, strict=True
            ):
                if (
                    not isinstance(clause, Mapping)
                    or _sha256_value(clause.get("source_semantic_sha256"))
                    != _sha256_value(identity.get("source_semantic_sha256"))
                    or str(clause.get("source_locator") or "").strip()
                    != locator
                    or not _substantive_correspondence_text(
                        clause.get("source_semantic_clause"), minimum_words=4
                    )
                ):
                    source_correspondence_matches = False
                    break

    current_component_association_sha = source_contract_association_record_digest(
        effective_association
    )
    if not _sha256_value(current_component_association_sha):
        return False
    lean_identity_matches = False
    if literal_type:
        lean_identity_matches = substantive.get("lean_component_type") == literal_type
    elif type_witness_identity is not None:
        witness_receipt, witness_path = type_witness_identity
        lean_identity_matches = bool(
            substantive.get("elaborated_type_witness_payload_receipt")
            == witness_receipt
            and str(substantive.get("elaborated_witness_path") or "").strip()
            == witness_path
            and _substantive_correspondence_text(
                substantive.get("lean_component_semantic_clause"),
                minimum_words=4,
            )
        )

    if (
        _sha256_value(substantive.get("component_sha256")) != component_sha
        or _sha256_value(substantive.get("structural_type_sha256"))
        != structural_sha
        or str(substantive.get("semantic_model_judgment_key") or "").strip()
        != semantic_key
        or _sha256_value(
            substantive.get("source_contract_association_sha256")
        )
        != current_component_association_sha
        or _sha256_value(substantive.get(SEMANTIC_ASSOCIATION_SHA256_FIELD))
        != current_parent_association_sha256
        or substantive.get("reviewed_declaration_identity")
        != effective_association.get("reviewed_declaration_identity")
        or substantive.get("reviewed_elaborated_signature_identity")
        != effective_association.get("reviewed_elaborated_signature_identity")
        or substantive.get("source_item_identities") != source_identities
        or not source_correspondence_matches
        or not lean_identity_matches
        or str(substantive.get("component_role") or "").strip()
        != occurrence_role
        or not _substantive_correspondence_text(
            substantive.get("semantic_match"), minimum_words=6
        )
    ):
        return False
    return True


def _current_source_domain_contract_receipt(
    component: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    semantic_key: str,
    component_occurrences: Mapping[str, Iterable[str]],
) -> SourceDomainCorrespondenceReceipt | None:
    """Validate one component contract against a candidate parent receipt.

    The candidate parent route is generated evidence, but it does not replace
    the human semantic disposition.  Reusing the authoritative component
    contract gate here requires the exact live occurrence SHA, structural type,
    and parent key before a receipt enters the closeout set.  This also keeps
    scalar legacy contracts confined to genuinely unique live occurrences.
    """

    source_key = str(
        component.get("source_judgment_key")
        or component.get("judgment_key")
        or ""
    ).strip()
    component_key = str(component.get("judgment_key") or "").strip()
    component_sha = source_claim_component_sha256(component)
    judgment = judgments.get(source_key)
    if (
        not source_key
        or not component_key
        or not component_sha
        or not semantic_key
        or not isinstance(judgment, Mapping)
    ):
        return None
    receipt = SourceDomainCorrespondenceReceipt(
        component_key=component_key,
        component_sha256=component_sha,
        source_model_judgment_key=semantic_key,
    )
    errors = theorem_realization_component_contract_errors(
        component,
        judgment,
        source_domain_correspondence_receipts=(receipt,),
        current_component_sha256s_by_source_judgment_key=(
            component_occurrences
        ),
    )
    return None if errors else receipt


def _current_direct_source_domain_correspondence_receipts(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    folder: Path,
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> set[SourceDomainCorrespondenceReceipt]:
    """Project exact definition/model routes into domain receipts.

    This is a positive semantic route, not a data-sort exemption.  The
    generated component and its unique semantic parent must either share the
    complete current schema-2 source/signature association or have the same
    exact generated declaration/signature as an authenticated component,
    explicit-direct, or whole-definition statement parent. Every associated source item must be definition/model
    vocabulary. A minimal occurrence-bound contract suffices only for a
    generated non-Prop source-domain occurrence. A proposition or an otherwise
    unknown occurrence additionally needs a fully pinned substantive component
    correspondence. Theorem-like or mixed source associations remain on the
    source-claim atom lane.
    """

    raw_source_items = statement_map.get("items")
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_source_items, Mapping) or not isinstance(
        raw_semantic_items, list
    ):
        return set()

    judgment_path = folder / "audit" / "source_record_match_llm.json"
    validated_parents: dict[
        str,
        list[
            tuple[
                Mapping[str, Any],
                Mapping[str, Any],
                str,
                TransparentSpecSemanticParentReceipt | None,
            ]
        ],
    ] = {}
    source_domain_parents_by_endpoint: dict[
        tuple[tuple[str, str], tuple[str, str]],
        list[tuple[str, Mapping[str, Any], str]],
    ] = {}
    for raw_semantic in raw_semantic_items:
        if not isinstance(raw_semantic, Mapping):
            continue
        semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
        semantic_judgment = judgments.get(semantic_key)
        if not semantic_key or not isinstance(semantic_judgment, Mapping):
            continue
        route = _current_direct_semantic_model_route(
            paper,
            folder,
            judgment_path,
            raw_semantic,
            semantic_judgment,
            audit_payload=audit_payload,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        if route is None:
            continue
        raw_parent_association, current_association_sha = route
        transparent_spec_parent_receipt = (
            _validated_transparent_spec_semantic_parent_receipt(raw_semantic)
        )
        validated_parents.setdefault(semantic_key, []).append(
            (
                raw_semantic,
                raw_parent_association,
                current_association_sha,
                transparent_spec_parent_receipt,
            )
        )
        effective_parent_association = administrative_projection_rebound_association(
            raw_parent_association, administrative_projection_rebind
        )
        parent_origin = str(
            effective_parent_association.get("association_origin") or ""
        ).strip()
        parent_role = str(
            effective_parent_association.get("role") or ""
        ).strip()
        if (parent_origin, parent_role) not in {
            (
                STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
                STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
            ),
            ("explicit_source_map_direct_route", "direct_source_route"),
            (
                STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
                STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
            ),
        }:
            continue
        parent_identity = _reviewed_declaration_identity(
            dict(effective_parent_association)
        )
        parent_signature = (
            _association_signature_identity(
                effective_parent_association.get(
                    "reviewed_elaborated_signature_identity"
                ),
                declaration=parent_identity[0],
            )
            if parent_identity is not None
            else None
        )
        if parent_identity is None or parent_signature is None:
            continue
        source_domain_parents_by_endpoint.setdefault(
            (parent_identity, parent_signature), []
        ).append(
            (semantic_key, raw_parent_association, current_association_sha)
        )

    receipts: set[SourceDomainCorrespondenceReceipt] = set()
    component_occurrences = theorem_realization_component_occurrence_index(
        audit_payload
    )
    for section, raw_component in theorem_realization_components(audit_payload):
        if not isinstance(raw_component, Mapping):
            continue
        component = raw_component
        if str(component.get("source_claim_component_role") or "").strip() != "material":
            continue
        proposition_sort = str(component.get("proposition_sort") or "").strip()
        restriction_status = theorem_facing_semantic_restriction_status(component)
        minimal_domain_occurrence = bool(
            proposition_sort == "false" and restriction_status == "source_domain"
        )
        substantive_domain_occurrence = bool(
            proposition_sort in {"true", "unknown"}
            or restriction_status == "unknown"
        )
        if not minimal_domain_occurrence and not substantive_domain_occurrence:
            continue

        component_identity = _reviewed_declaration_identity(dict(component))
        if component_identity is None:
            continue
        raw_association = component.get("source_contract_association")
        if raw_association is not None and not isinstance(raw_association, Mapping):
            continue
        if isinstance(raw_association, Mapping):
            association = dict(raw_association)
            component_signature = _unique_elaborated_signature_identity(
                component,
                declaration=component_identity[0],
                allow_aggregate=(
                    _generated_result_certificate_allows_aggregate_signatures(
                        component, section=section
                    )
                ),
            )
            association_signature = _association_signature_identity(
                association.get("reviewed_elaborated_signature_identity"),
                declaration=component_identity[0],
            )
            if (
                association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA
                or _sha256_value(association.get("association_sha256"))
                != source_contract_association_record_digest(association)
                or _reviewed_declaration_identity(association) != component_identity
                or component_signature is None
                or association_signature != component_signature
            ):
                continue
            semantic_key = str(
                association.get("semantic_model_judgment_key") or ""
            ).strip()
            parent_candidates = validated_parents.get(semantic_key, [])
            if len(parent_candidates) != 1:
                continue
            (
                _raw_parent,
                raw_parent_association,
                current_parent_sha,
                transparent_spec_parent_receipt,
            ) = parent_candidates[0]
            direct_component_route = bool(
                association.get("association_mode")
                == "explicit_source_map_direct_route"
                and association.get("semantic_contract_member_role")
                == "direct_source_route"
            )
            transparent_spec_route = bool(
                association.get("association_mode")
                == "semantic_contract_group_member"
                and association.get("semantic_contract_member_role")
                == "transparent_spec"
                and validated_transparent_spec_semantic_parent_route(
                    component, transparent_spec_parent_receipt
                )
                == TransparentSpecSemanticParentRoute(
                    semantic_model_judgment_key=semantic_key,
                    evidence_declaration=(
                        transparent_spec_parent_receipt.evidence_declaration_identity[0]
                        if transparent_spec_parent_receipt is not None
                        else ""
                    ),
                )
            )
            authenticated_assumption_route = bool(
                association.get("association_mode")
                == SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
                and association.get("semantic_contract_member_role")
                == SOURCE_ASSUMPTION_ASSOCIATION_ROLE
            )
            if not (
                direct_component_route
                or transparent_spec_route
                or authenticated_assumption_route
            ):
                continue
            effective_association = administrative_projection_rebound_association(
                association, administrative_projection_rebind
            )
        else:
            component_signatures = _elaborated_signature_identities(
                dict(component), declaration=component_identity[0]
            )
            if component_signatures is None or len(component_signatures) != 1:
                continue
            component_signature = next(iter(component_signatures))
            parent_candidates = source_domain_parents_by_endpoint.get(
                (component_identity, component_signature), []
            )
            if len(parent_candidates) != 1:
                continue
            semantic_key, raw_parent_association, current_parent_sha = (
                parent_candidates[0]
            )
            effective_association = administrative_projection_rebound_association(
                raw_parent_association, administrative_projection_rebind
            )
            direct_component_route = True
            transparent_spec_route = False
            authenticated_assumption_route = False

        effective_parent_association = administrative_projection_rebound_association(
            raw_parent_association, administrative_projection_rebind
        )
        parent_identity = _reviewed_declaration_identity(
            dict(effective_parent_association)
        )
        parent_signature = (
            _association_signature_identity(
                effective_parent_association.get(
                    "reviewed_elaborated_signature_identity"
                ),
                declaration=parent_identity[0],
            )
            if parent_identity is not None
            else None
        )
        expected_parent_identity = (
            transparent_spec_parent_receipt.evidence_declaration_identity
            if transparent_spec_route and transparent_spec_parent_receipt is not None
            else component_identity
        )
        expected_parent_signature = (
            transparent_spec_parent_receipt.evidence_elaborated_signature_identity
            if transparent_spec_route and transparent_spec_parent_receipt is not None
            else component_signature
        )
        if authenticated_assumption_route and (
            str(effective_parent_association.get("association_origin") or "").strip()
            != SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
            or str(effective_parent_association.get("role") or "").strip()
            != SOURCE_ASSUMPTION_ASSOCIATION_ROLE
        ):
            continue
        component_semantic_sha = _sha256_value(
            effective_association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
        )
        if (
            parent_identity != expected_parent_identity
            or parent_signature != expected_parent_signature
            or component_semantic_sha is None
            or (
                direct_component_route
                and component_semantic_sha != current_parent_sha
            )
            or _sha256_value(
                effective_parent_association.get(
                    SEMANTIC_ASSOCIATION_SHA256_FIELD
                )
            )
            != current_parent_sha
            or effective_association.get("source_item_identities")
            != effective_parent_association.get("source_item_identities")
        ):
            continue

        source_identities = effective_association.get("source_item_identities")
        if not isinstance(source_identities, list) or not source_identities:
            continue
        if authenticated_assumption_route and component_semantic_sha != (
            semantic_association_record_digest(
                [
                    str(identity.get("source_semantic_sha256") or "")
                    .strip()
                    .lower()
                    for identity in source_identities
                    if isinstance(identity, Mapping)
                ],
                effective_association.get(
                    "reviewed_elaborated_signature_identity"
                ),
            )
        ):
            continue
        source_kinds_are_domain = True
        for raw_identity in source_identities:
            if not isinstance(raw_identity, Mapping):
                source_kinds_are_domain = False
                break
            source_key = str(raw_identity.get("source_key") or "").strip()
            current_source_item = raw_source_items.get(source_key)
            current_kind = (
                str(current_source_item.get("source_kind") or "").strip().lower()
                if isinstance(current_source_item, Mapping)
                else ""
            )
            recorded_kind = str(
                raw_identity.get("source_kind") or ""
            ).strip().lower()
            if (
                current_kind not in SOURCE_DOMAIN_PRESENTATION_KINDS
                or recorded_kind != current_kind
            ):
                source_kinds_are_domain = False
                break
        if not source_kinds_are_domain:
            continue

        receipt = _current_source_domain_contract_receipt(
            component,
            judgments,
            semantic_key=semantic_key,
            component_occurrences=component_occurrences,
        )
        if receipt is None:
            continue

        if substantive_domain_occurrence and not _current_direct_semantic_correspondence(
            component,
            judgments,
            semantic_key=semantic_key,
            effective_association=effective_association,
            current_parent_association_sha256=current_parent_sha,
        ):
            continue
        receipts.add(receipt)
    return receipts


def current_source_domain_correspondence_receipts(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> tuple[SourceDomainCorrespondenceReceipt, ...]:
    """Project only complete semantic-model bindings into domain receipts.

    The binding reader has already checked the semantic-model source
    association, exact elaborated declaration/signature, and every transitive
    record field. This function merely binds that result to the generated
    component identity; neither a data classification nor a record name is an
    acceptance path.
    """

    folder = PAPERS / paper
    statement_map = (
        paper_statement_map_override
        if paper_statement_map_override is not None
        else load_payload(folder / "audit" / "paper_statement_map.json")
    )
    source_proof_fidelity = audit_payload.get("source_proof_fidelity")
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json") or {}
    )
    if not isinstance(statement_map, Mapping) or not isinstance(
        source_proof_fidelity, Mapping
    ):
        return ()
    administrative_projection_rebind = (
        administrative_projection_rebind_context_or_override(
            paper,
            audit_payload,
            status_payload,
            administrative_projection_rebind_override,
        )
    )
    bindings = current_complete_semantic_model_record_bindings(
        paper,
        audit_payload,
        judgments,
        status_payload_override=status_payload,
        paper_statement_map_override=statement_map,
        administrative_projection_rebind_override=(
            administrative_projection_rebind
        ),
    )
    components = [
        component
        for _section, component in theorem_realization_components(audit_payload)
        if isinstance(component, Mapping)
    ]
    receipts = _current_direct_source_domain_correspondence_receipts(
        paper,
        audit_payload,
        judgments,
        folder=folder,
        statement_map=statement_map,
        source_proof_fidelity=source_proof_fidelity,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    for binding in bindings:
        for component in components:
            source_key = str(
                component.get("source_judgment_key")
                or component.get("judgment_key")
                or ""
            ).strip()
            component_key = str(component.get("judgment_key") or "").strip()
            component_sha = source_claim_component_sha256(component)
            if not source_key or not component_key or not component_sha:
                continue
            section = str(component.get("source_component_section") or "").strip()
            is_bound_field = (
                section == "recursive_field_items"
                and source_key in binding.field_keys
            )
            is_bound_record_dependency = (
                section == "conclusion_dependency_items"
                and dependency_has_complete_semantic_model_record_binding(
                    component, (binding,)
                )
            )
            if is_bound_field or is_bound_record_dependency:
                receipts.add(
                    SourceDomainCorrespondenceReceipt(
                        component_key=component_key,
                        component_sha256=component_sha,
                        source_model_judgment_key=binding.source_model_judgment_key,
                    )
                )
    return tuple(sorted(receipts, key=lambda receipt: (
        receipt.component_key,
        receipt.component_sha256,
        receipt.source_model_judgment_key,
    )))


def _strict_source_spec_receipts_by_key(
    receipts: Iterable[StrictSourceSpecCorrespondenceReceipt],
) -> dict[str, StrictSourceSpecCorrespondenceReceipt]:
    """Index unambiguous runtime source-to-Spec receipts by source item.

    The source key is only the map coordinate of a receipt already minted by
    the strict source-map lane.  No Lean declaration, source label, or binder
    spelling is used to select a record here.
    """

    indexed: dict[str, StrictSourceSpecCorrespondenceReceipt] = {}
    ambiguous: set[str] = set()
    for receipt in receipts:
        if not isinstance(receipt, StrictSourceSpecCorrespondenceReceipt):
            continue
        key = receipt.source_item_key.strip()
        digests = (
            receipt.source_atoms_sha256,
            receipt.item_identity_sha256,
            receipt.spec_closure_sha256,
            receipt.spec_surface_sha256,
            receipt.closure_environment_sha256,
        )
        if (
            not key
            or not receipt.spec_declaration.strip()
            or not receipt.evidence_declaration.strip()
            or receipt.evidence_mode != "proves"
            or not receipt.semantic_shape.strip()
            or any(not re.fullmatch(r"[0-9a-f]{64}", digest) for digest in digests)
            or receipt.authority not in {
                "persisted_correspondence_v1",
                "v11_graph_native_v1",
            }
        ):
            continue
        existing = indexed.get(key)
        if existing is not None and existing != receipt:
            ambiguous.add(key)
            continue
        indexed[key] = receipt
    return {
        key: receipt
        for key, receipt in indexed.items()
        if key not in ambiguous
    }


def _strict_source_spec_runtime_matches_item(
    raw_item: Mapping[str, Any],
    receipt: StrictSourceSpecCorrespondenceReceipt,
) -> bool:
    """Verify one in-memory Lean receipt against its exact current map row."""

    raw_contract = raw_item.get("semantic_contract")
    if receipt.authority == "v11_graph_native_v1":
        raw_atoms = raw_item.get("source_claim_atoms")
        source_atoms_sha = source_claim_atoms_semantic_sha256(raw_atoms)
        if (
            raw_item.get("claim_bearing") is not True
            or not isinstance(raw_contract, Mapping)
            or not source_atoms_sha
            or source_atoms_sha != receipt.source_atoms_sha256
            or str(raw_contract.get("spec_declaration") or "").strip()
            != receipt.spec_declaration
            or str(raw_contract.get("evidence_declaration") or "").strip()
            != receipt.evidence_declaration
            or str(raw_contract.get("evidence_mode") or "").strip()
            != receipt.evidence_mode
            or str(raw_contract.get("semantic_shape") or "").strip()
            != receipt.semantic_shape
        ):
            return False
        expected_identity = graph_native_source_spec_realization_identity_sha256(
            raw_contract,
            source_atoms_sha256=source_atoms_sha,
            spec_closure_sha256=receipt.spec_closure_sha256,
            spec_surface_sha256=receipt.spec_surface_sha256,
            closure_environment_sha256=receipt.closure_environment_sha256,
        )
        return bool(
            expected_identity
            and expected_identity == receipt.item_identity_sha256
        )
    correspondence = raw_item.get("source_spec_correspondence")
    if (
        raw_item.get("claim_bearing") is not True
        or not isinstance(raw_contract, Mapping)
        or not isinstance(correspondence, Mapping)
        or source_spec_correspondence_validation_errors(
            correspondence,
            raw_atoms=raw_item.get("source_claim_atoms"),
            raw_contract=raw_contract,
        )
    ):
        return False
    if (
        str(raw_contract.get("spec_declaration") or "").strip()
        != receipt.spec_declaration
        or str(raw_contract.get("evidence_declaration") or "").strip()
        != receipt.evidence_declaration
        or str(raw_contract.get("evidence_mode") or "").strip()
        != receipt.evidence_mode
        or str(raw_contract.get("semantic_shape") or "").strip()
        != receipt.semantic_shape
        or source_spec_correspondence_item_identity_sha256(
            raw_contract, correspondence
        )
        != receipt.item_identity_sha256
    ):
        return False
    recorded = {
        "source_atoms_sha256": receipt.source_atoms_sha256,
        "item_identity_sha256": receipt.item_identity_sha256,
        "spec_closure_sha256": receipt.spec_closure_sha256,
        "spec_surface_sha256": receipt.spec_surface_sha256,
        "closure_environment_sha256": receipt.closure_environment_sha256,
    }
    if any(
        str(correspondence.get(field) or "").strip().lower() != value
        for field, value in recorded.items()
    ):
        return False

    # This route grants full-surface coverage only when every source atom was
    # explicitly tied to the canonical root.  Component subhashes, names, and
    # nearby closure nodes cannot silently turn a partial correspondence into
    # a whole-Spec authorization.
    bindings = correspondence.get("source_atom_bindings")
    if not isinstance(bindings, list) or not bindings:
        return False
    return all(
        isinstance(binding, Mapping)
        and [
            str(component).strip().lower()
            for component in binding.get("spec_component_sha256s") or []
        ]
        == [receipt.spec_surface_sha256]
        for binding in bindings
    )


def _strict_source_identity_matches_current_item(
    raw_identity: object,
    *,
    source_key: str,
    raw_item: Mapping[str, Any],
    receipt: StrictSourceSpecCorrespondenceReceipt,
) -> bool:
    """Bind a generated parent identity to the exact current source-map row."""

    if not isinstance(raw_identity, Mapping):
        return False
    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, Mapping):
        return False
    source_semantic_sha = source_record_source_item_semantic_sha256(
        dict(raw_item), ""
    )
    if (
        str(raw_identity.get("source_key") or "").strip() != source_key
        or _sha256_value(raw_identity.get("source_map_item_sha256"))
        != source_record_source_item_record_sha256(raw_item)
        or _sha256_value(raw_identity.get("source_semantic_sha256"))
        != source_semantic_sha
    ):
        return False
    identity_contract = raw_identity.get("semantic_contract")
    return bool(
        isinstance(identity_contract, Mapping)
        and str(identity_contract.get("spec_declaration") or "").strip()
        == receipt.spec_declaration
        and str(identity_contract.get("evidence_declaration") or "").strip()
        == receipt.evidence_declaration
        and str(identity_contract.get("evidence_mode") or "").strip()
        == receipt.evidence_mode
        and str(identity_contract.get("semantic_shape") or "").strip()
        == receipt.semantic_shape
        and str(raw_contract.get("spec_declaration") or "").strip()
        == receipt.spec_declaration
        and str(raw_contract.get("evidence_declaration") or "").strip()
        == receipt.evidence_declaration
        and str(raw_contract.get("evidence_mode") or "").strip()
        == receipt.evidence_mode
        and str(raw_contract.get("semantic_shape") or "").strip()
        == receipt.semantic_shape
    )


def _source_claim_atom_semantic_association_pin(
    contexts: Iterable[Mapping[str, Any]],
    signature: object,
) -> str | None:
    """Recompute the source-record generator's name-free atom association pin."""

    signature_digest = (
        str(signature.get("elaborated_signature_sha256") or "").strip().lower()
        if isinstance(signature, Mapping)
        else ""
    )
    atom_digests = [
        str(context.get("source_claim_atom_semantic_sha256") or "")
        .strip()
        .lower()
        for context in contexts
    ]
    if (
        not re.fullmatch(r"[0-9a-f]{64}", signature_digest)
        or not atom_digests
        or any(not re.fullmatch(r"[0-9a-f]{64}", value) for value in atom_digests)
        or len(set(atom_digests)) != len(atom_digests)
    ):
        return None
    return hashlib.sha256(
        json.dumps(
            {
                "schema": SOURCE_CLAIM_ATOM_ASSOCIATION_SCHEMA,
                "source_claim_atom_semantic_sha256": sorted(atom_digests),
                "elaborated_signature_sha256": signature_digest,
            },
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _transparent_spec_parent_atom_receipt(
    raw_semantic: Mapping[str, Any],
    parent_receipt: TransparentSpecSemanticParentReceipt,
    *,
    expected_source_atoms: frozenset[tuple[str, str]],
    current_atom_receipts: frozenset[SourceClaimAtomReceipt],
) -> tuple[str, str] | None:
    """Validate the direct parent's exact source-atom bridge.

    Source-atom identifiers and Lean routes are only generated navigation
    coordinates.  The equality below is over source-facing atom content
    hashes, current source roots, and the direct evidence signature.
    """

    association = raw_semantic.get(SOURCE_CLAIM_ATOM_ASSOCIATION_FIELD)
    contexts = raw_semantic.get("source_claim_atom_contexts")
    if not isinstance(association, Mapping) or not isinstance(contexts, list):
        return None
    association_sha = _sha256_value(association.get("association_sha256"))
    if (
        association.get("schema") != SOURCE_CLAIM_ATOM_ASSOCIATION_SCHEMA
        or str(association.get("association_origin") or "").strip()
        != SOURCE_CLAIM_ATOM_ROUTE_ORIGIN
        or str(association.get("role") or "").strip()
        != SOURCE_CLAIM_ATOM_ROUTE_ROLE
        or association_sha != source_contract_association_record_digest(association)
        or _reviewed_declaration_identity(dict(association))
        != parent_receipt.evidence_declaration_identity
        or _association_signature_identity(
            association.get("reviewed_elaborated_signature_identity"),
            declaration=parent_receipt.evidence_declaration_identity[0],
        )
        != parent_receipt.evidence_elaborated_signature_identity
        or _canonical_semantic_receipt_json(
            association.get("source_item_identities")
        )
        != parent_receipt.source_item_identities_json
    ):
        return None
    context_mappings: list[Mapping[str, Any]] = []
    context_coordinates: set[tuple[str, str]] = set()
    for raw_context in contexts:
        if not isinstance(raw_context, Mapping):
            return None
        atom_id = str(raw_context.get("id") or "").strip()
        generated_digest = str(
            raw_context.get("source_claim_atom_semantic_sha256") or ""
        ).strip().lower()
        if (
            not atom_id
            or not re.fullmatch(r"[0-9a-f]{64}", generated_digest)
            or (atom_id, generated_digest) in context_coordinates
        ):
            return None
        context_coordinates.add((atom_id, generated_digest))
        context_mappings.append(raw_context)
    expected_semantic_pin = _source_claim_atom_semantic_association_pin(
        context_mappings,
        association.get("reviewed_elaborated_signature_identity"),
    )
    semantic_pin = _sha256_value(
        association.get(SOURCE_CLAIM_ATOM_SEMANTIC_ASSOCIATION_FIELD)
    )
    if expected_semantic_pin is None or semantic_pin != expected_semantic_pin:
        return None

    routes = association.get("source_claim_atom_routes")
    if not isinstance(routes, list) or not routes:
        return None
    source_key_by_context: dict[tuple[str, str], str] = {}
    for raw_route in routes:
        if not isinstance(raw_route, Mapping):
            return None
        source_key = str(raw_route.get("source_key") or "").strip()
        atom_id = str(raw_route.get("atom_id") or "").strip()
        generated_digest = str(
            raw_route.get("source_claim_atom_semantic_sha256") or ""
        ).strip().lower()
        coordinate = (atom_id, generated_digest)
        if (
            not source_key
            or not atom_id
            or not re.fullmatch(r"[0-9a-f]{64}", generated_digest)
            or coordinate in source_key_by_context
        ):
            return None
        source_key_by_context[coordinate] = source_key
    if set(source_key_by_context) != context_coordinates:
        return None

    observed_source_atoms: set[tuple[str, str]] = set()
    for context in context_mappings:
        atom_id = str(context.get("id") or "").strip()
        generated_digest = str(
            context.get("source_claim_atom_semantic_sha256") or ""
        ).strip().lower()
        source_key = source_key_by_context.get((atom_id, generated_digest))
        content_digest = source_claim_atom_semantic_sha256(dict(context))
        locator = str(context.get("source_locator") or "").strip()
        if not source_key or not content_digest or not locator:
            return None
        atom_receipt = SourceClaimAtomReceipt(
            source_item_key=source_key,
            atom_id=atom_id,
            atom_semantic_sha256=generated_digest,
            source_locator=locator,
        )
        if atom_receipt not in current_atom_receipts:
            return None
        observed_source_atoms.add((source_key, content_digest))
    if observed_source_atoms != set(expected_source_atoms):
        return None
    return association_sha, semantic_pin


def _current_strict_transparent_spec_semantic_parents(
    paper: str,
    audit_payload: Mapping[str, Any],
    *,
    current_source_spec_correspondence_receipts: Iterable[
        StrictSourceSpecCorrespondenceReceipt
    ] = (),
    strict_source_scope_item_keys: Iterable[str] | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> tuple[StrictTransparentSpecSemanticParent, ...]:
    """Return strict source-to-Spec parents that are complete at the root.

    A semantic-model sidecar is intentionally absent from this selector.  A
    qualifying parent instead needs all of the following current runtime
    evidence: a strict root in the configured source scope, an exact Lean
    source-to-Spec receipt, a generator-owned direct-evidence/transparent-Spec
    pair, and an atom association whose complete source-facing content matches
    the root inventory.  Thus the selector cannot be widened by a source kind,
    declaration/binder spelling, or an optional journal entry.
    """

    folder = PAPERS / paper
    statement_map = (
        paper_statement_map_override
        if paper_statement_map_override is not None
        else load_payload(folder / "audit" / "paper_statement_map.json")
    )
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json") or {}
    )
    if not isinstance(statement_map, Mapping) or not isinstance(status_payload, Mapping):
        return ()
    raw_source_items = statement_map.get("items")
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_source_items, Mapping) or not isinstance(raw_semantic_items, list):
        return ()

    if strict_source_scope_item_keys is None:
        try:
            inventory, inventory_findings = semantic_contract_closeout_bridge_inventory(
                folder, str(status_payload.get("status") or "")
            )
        except Exception:
            return ()
        if inventory is None or inventory_findings:
            return ()
        strict_scope = frozenset(inventory.contract_item_keys)
    else:
        strict_scope = frozenset(
            str(value).strip()
            for value in strict_source_scope_item_keys
            if isinstance(value, str) and value.strip()
        )
    if not strict_scope:
        return ()

    runtime_by_key = _strict_source_spec_receipts_by_key(
        current_source_spec_correspondence_receipts
    )
    current_roots: dict[
        str, tuple[Mapping[str, Any], StrictSourceSpecCorrespondenceReceipt]
    ] = {}
    for source_key in strict_scope:
        raw_item = raw_source_items.get(source_key)
        receipt = runtime_by_key.get(source_key)
        if (
            isinstance(raw_item, Mapping)
            and receipt is not None
            and _strict_source_spec_runtime_matches_item(raw_item, receipt)
        ):
            current_roots[source_key] = (raw_item, receipt)
    if not current_roots:
        return ()

    administrative_projection_rebind = (
        administrative_projection_rebind_context_or_override(
            paper,
            audit_payload,
            status_payload,
            administrative_projection_rebind_override,
        )
    )
    current_atom_receipts = frozenset(current_source_claim_atom_receipts(audit_payload))
    candidates: dict[str, list[StrictTransparentSpecSemanticParent]] = {}
    for raw_semantic in raw_semantic_items:
        if not isinstance(raw_semantic, Mapping):
            continue
        semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
        if not semantic_key:
            continue
        direct_route = _current_direct_semantic_model_association_route(
            raw_semantic,
            administrative_projection_rebind=administrative_projection_rebind,
        )
        parent_receipt = _validated_transparent_spec_semantic_parent_receipt(
            raw_semantic
        )
        if direct_route is None or parent_receipt is None:
            continue
        raw_parent_association, parent_semantic_association_sha = direct_route
        if not re.fullmatch(r"[0-9a-f]{64}", parent_semantic_association_sha):
            continue
        raw_source_identities = raw_parent_association.get("source_item_identities")
        if (
            not isinstance(raw_source_identities, list)
            or not raw_source_identities
            or _canonical_semantic_receipt_json(raw_source_identities)
            != parent_receipt.source_item_identities_json
        ):
            continue
        source_keys: set[str] = set()
        identity_is_current = True
        for raw_identity in raw_source_identities:
            if not isinstance(raw_identity, Mapping):
                identity_is_current = False
                break
            source_key = str(raw_identity.get("source_key") or "").strip()
            root = current_roots.get(source_key)
            if (
                not source_key
                or source_key in source_keys
                or root is None
                or not _strict_source_identity_matches_current_item(
                    raw_identity,
                    source_key=source_key,
                    raw_item=root[0],
                    receipt=root[1],
                )
            ):
                identity_is_current = False
                break
            source_keys.add(source_key)
        if not identity_is_current or not source_keys:
            continue

        expected_source_atoms: set[tuple[str, str]] = set()
        for source_key in source_keys:
            root_item, _root_receipt = current_roots[source_key]
            raw_atoms = root_item.get("source_claim_atoms")
            if not isinstance(raw_atoms, list) or not raw_atoms:
                identity_is_current = False
                break
            for raw_atom in raw_atoms:
                content_digest = source_claim_atom_semantic_sha256(raw_atom)
                if not content_digest or (source_key, content_digest) in expected_source_atoms:
                    identity_is_current = False
                    break
                expected_source_atoms.add((source_key, content_digest))
            if not identity_is_current:
                break
        if not identity_is_current or not expected_source_atoms:
            continue
        parent_atom_receipt = _transparent_spec_parent_atom_receipt(
            raw_semantic,
            parent_receipt,
            expected_source_atoms=frozenset(expected_source_atoms),
            current_atom_receipts=current_atom_receipts,
        )
        if parent_atom_receipt is None:
            continue
        parent_atom_association_sha, parent_atom_semantic_sha = parent_atom_receipt
        ordered_source_keys = tuple(sorted(source_keys))
        candidates.setdefault(semantic_key, []).append(
            StrictTransparentSpecSemanticParent(
                semantic_model_judgment_key=semantic_key,
                parent_receipt=parent_receipt,
                parent_semantic_association_sha256=parent_semantic_association_sha,
                parent_source_claim_atom_association_sha256=(
                    parent_atom_association_sha
                ),
                parent_source_claim_atom_semantic_association_sha256=(
                    parent_atom_semantic_sha
                ),
                source_item_keys=ordered_source_keys,
                source_root_receipts=tuple(
                    current_roots[source_key][1]
                    for source_key in ordered_source_keys
                ),
            )
        )
    return tuple(
        parent
        for semantic_key in sorted(candidates)
        for parent in candidates[semantic_key]
        if len(candidates[semantic_key]) == 1
    )


def current_strict_transparent_spec_semantic_parent_judgment_keys(
    paper: str,
    audit_payload: Mapping[str, Any],
    *,
    current_source_spec_correspondence_receipts: Iterable[
        StrictSourceSpecCorrespondenceReceipt
    ] = (),
    strict_source_scope_item_keys: Iterable[str] | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> frozenset[str]:
    """Return only semantic rows discharged by the strict runtime parent lane.

    This projection is used to decide whether a source-record semantic-model
    journal is required.  The returned keys are an output of the exact strict
    parent selector above, never a caller-supplied exemption list.
    """

    return frozenset(
        parent.semantic_model_judgment_key
        for parent in _current_strict_transparent_spec_semantic_parents(
            paper,
            audit_payload,
            current_source_spec_correspondence_receipts=(
                current_source_spec_correspondence_receipts
            ),
            strict_source_scope_item_keys=strict_source_scope_item_keys,
            status_payload_override=status_payload_override,
            paper_statement_map_override=paper_statement_map_override,
            administrative_projection_rebind_override=(
                administrative_projection_rebind_override
            ),
        )
    )


def current_transparent_spec_full_surface_correspondence_receipts(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    current_source_spec_correspondence_receipts: Iterable[
        StrictSourceSpecCorrespondenceReceipt
    ] = (),
    strict_source_scope_item_keys: Iterable[str] | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> tuple[TransparentSpecFullSurfaceCorrespondenceReceipt, ...]:
    """Project strict source-to-Spec evidence onto every exact occurrence.

    This is the one generic bridge for a full canonical transparent Spec.  It
    does not select a route from any declaration, binder, field, section, or
    source-kind spelling.  The source-map closeout inventory supplies the
    root scope; Lean supplied the current closure receipt; generated schema-2
    associations supply the parent and occurrence coordinates.
    """

    # ``judgments`` remains an argument for call-site compatibility with the
    # wider theorem-realization gate.  Strict source-to-Spec parents are
    # authenticated from current runtime receipts, not from an optional LLM
    # sidecar entry.
    del judgments
    parents_by_semantic_key: dict[str, list[StrictTransparentSpecSemanticParent]] = {}
    for parent in _current_strict_transparent_spec_semantic_parents(
        paper,
        audit_payload,
        current_source_spec_correspondence_receipts=(
            current_source_spec_correspondence_receipts
        ),
        strict_source_scope_item_keys=strict_source_scope_item_keys,
        status_payload_override=status_payload_override,
        paper_statement_map_override=paper_statement_map_override,
        administrative_projection_rebind_override=(
            administrative_projection_rebind_override
        ),
    ):
        parents_by_semantic_key.setdefault(
            parent.semantic_model_judgment_key, []
        ).append(parent)

    receipts: set[TransparentSpecFullSurfaceCorrespondenceReceipt] = set()
    for _section, raw_component in theorem_realization_components(audit_payload):
        if not isinstance(raw_component, Mapping):
            continue
        if str(raw_component.get("source_claim_component_role") or "").strip() != "material":
            continue
        association = raw_component.get("source_contract_association")
        if not isinstance(association, Mapping):
            continue
        semantic_key = str(
            association.get("semantic_model_judgment_key") or ""
        ).strip()
        parents = parents_by_semantic_key.get(semantic_key, [])
        if len(parents) != 1:
            continue
        parent = parents[0]
        parent_receipt = parent.parent_receipt
        if (
            validated_transparent_spec_semantic_parent_route(
                raw_component, parent_receipt
            )
            != TransparentSpecSemanticParentRoute(
                semantic_model_judgment_key=semantic_key,
                evidence_declaration=parent_receipt.evidence_declaration_identity[0],
            )
        ):
            continue
        component_key = str(raw_component.get("judgment_key") or "").strip()
        source_judgment_key = str(
            raw_component.get("source_judgment_key")
            or raw_component.get("judgment_key")
            or ""
        ).strip()
        component_sha = source_claim_component_sha256(raw_component)
        structural_sha = str(
            raw_component.get("source_claim_component_structural_type_sha256")
            or ""
        ).strip().lower()
        component_association_sha = _sha256_value(association.get("association_sha256"))
        if (
            not component_key
            or not source_judgment_key
            or not re.fullmatch(r"[0-9a-f]{64}", component_sha)
            or not re.fullmatch(r"[0-9a-f]{64}", structural_sha)
            or component_association_sha
            != source_contract_association_record_digest(association)
        ):
            continue
        source_root_receipts = parent.source_root_receipts
        receipts.add(
            TransparentSpecFullSurfaceCorrespondenceReceipt(
                component_key=component_key,
                source_judgment_key=source_judgment_key,
                component_sha256=component_sha,
                structural_type_sha256=structural_sha,
                semantic_model_judgment_key=semantic_key,
                source_item_keys=parent.source_item_keys,
                source_spec_correspondence_item_identity_sha256s=tuple(
                    (receipt.source_item_key, receipt.item_identity_sha256)
                    for receipt in source_root_receipts
                ),
                source_spec_correspondence_closure_sha256s=tuple(
                    (receipt.source_item_key, receipt.spec_closure_sha256)
                    for receipt in source_root_receipts
                ),
                source_spec_correspondence_surface_sha256s=tuple(
                    (receipt.source_item_key, receipt.spec_surface_sha256)
                    for receipt in source_root_receipts
                ),
                source_spec_correspondence_environment_sha256s=tuple(
                    (receipt.source_item_key, receipt.closure_environment_sha256)
                    for receipt in source_root_receipts
                ),
                parent_semantic_association_sha256=(
                    parent.parent_semantic_association_sha256
                ),
                parent_source_claim_atom_association_sha256=(
                    parent.parent_source_claim_atom_association_sha256
                ),
                parent_source_claim_atom_semantic_association_sha256=(
                    parent.parent_source_claim_atom_semantic_association_sha256
                ),
                component_source_contract_association_sha256=(
                    component_association_sha
                ),
            )
        )
    return tuple(
        sorted(
            receipts,
            key=lambda receipt: (
                receipt.component_key,
                receipt.component_sha256,
                receipt.source_judgment_key,
            ),
        )
    )


def current_strict_transparent_spec_full_surface_source_record_judgment_keys(
    paper: str,
    audit_payload: Mapping[str, Any],
    *,
    current_source_spec_correspondence_receipts: Iterable[
        StrictSourceSpecCorrespondenceReceipt
    ] = (),
    strict_source_scope_item_keys: Iterable[str] | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> frozenset[str]:
    """Return source-record keys fully discharged by strict full-Spec receipts.

    This is deliberately stricter than projecting receipt keys directly.  A
    source-record judgment key is reusable metadata, while the strict route
    authorizes individual generated component occurrences.  Consequently a
    key is returned only when its complete current *material* occurrence set
    is in a one-to-one exact correspondence with current strict receipts.

    The projection does not accept a caller-provided key list, source label,
    declaration name, or function name.  It reads the schema-1 generated
    component ledger, checks the generator-owned source-contract association
    of every material occurrence, and asks the strict runtime selector above
    to mint the receipts.  A nonmaterial, malformed, duplicated, or uncovered
    component therefore leaves its source-record judgment in the ordinary
    review lane.
    """

    # Strict V11 correspondence is defined over the explicit occurrence
    # ledger.  The legacy fallback reader deliberately deduplicates entries,
    # which would make a duplicate raw component invisible here.
    raw_components = audit_payload.get("theorem_realization_component_items")
    if not isinstance(raw_components, list):
        return frozenset()

    # Only current generated source-record requirements can be discharged.
    # This prevents a component from manufacturing a source-record key merely
    # by placing arbitrary text in ``source_judgment_key``.
    expected_source_record_keys = {
        str(key).strip()
        for field in (
            "expected_input_judgment_keys",
            "expected_field_judgment_keys",
        )
        for key in audit_payload.get(field) or []
        if isinstance(key, str) and key.strip()
    }
    if not expected_source_record_keys:
        return frozenset()

    generated_source_record_keys: set[str] = set()
    for section in SOURCE_RECORD_JUDGMENT_ITEM_SECTIONS:
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            if key:
                generated_source_record_keys.add(key)
    candidate_keys = expected_source_record_keys & generated_source_record_keys
    if not candidate_keys:
        return frozenset()

    # The tuple includes every generator-owned coordinate carried by both the
    # raw occurrence and the runtime receipt.  Keep a list, rather than a set,
    # until after duplicate checks so an accidental duplicate cannot disappear
    # through normal Python set semantics.
    raw_occurrences: dict[str, list[tuple[str, str, str, str, str, str]]] = {}
    invalid_keys: set[str] = set()
    seen_component_keys: dict[str, set[str]] = {}
    seen_occurrences: dict[str, set[tuple[str, str, str, str, str, str]]] = {}
    for raw_component in raw_components:
        if not isinstance(raw_component, Mapping):
            continue
        source_key = str(raw_component.get("source_judgment_key") or "").strip()
        if source_key not in candidate_keys:
            continue
        if (
            str(raw_component.get("source_claim_component_role") or "").strip()
            != "material"
        ):
            invalid_keys.add(source_key)
            continue
        component_key = str(raw_component.get("judgment_key") or "").strip()
        component_sha = source_claim_component_sha256(raw_component)
        structural_sha = str(
            raw_component.get("source_claim_component_structural_type_sha256")
            or ""
        ).strip().lower()
        association = raw_component.get("source_contract_association")
        association_sha = (
            _sha256_value(association.get("association_sha256"))
            if isinstance(association, Mapping)
            else None
        )
        semantic_key = (
            str(association.get("semantic_model_judgment_key") or "").strip()
            if isinstance(association, Mapping)
            else ""
        )
        if (
            not component_key
            or not re.fullmatch(r"[0-9a-f]{64}", component_sha)
            or not re.fullmatch(r"[0-9a-f]{64}", structural_sha)
            or not semantic_key
            or association_sha is None
            or not isinstance(association, Mapping)
            or association_sha != source_contract_association_record_digest(association)
        ):
            invalid_keys.add(source_key)
            continue
        identity = (
            source_key,
            component_key,
            component_sha,
            structural_sha,
            semantic_key,
            association_sha,
        )
        component_keys = seen_component_keys.setdefault(source_key, set())
        identities = seen_occurrences.setdefault(source_key, set())
        if component_key in component_keys or identity in identities:
            invalid_keys.add(source_key)
            continue
        component_keys.add(component_key)
        identities.add(identity)
        raw_occurrences.setdefault(source_key, []).append(identity)

    if not raw_occurrences:
        return frozenset()

    receipts = current_transparent_spec_full_surface_correspondence_receipts(
        paper,
        audit_payload,
        {},
        current_source_spec_correspondence_receipts=(
            current_source_spec_correspondence_receipts
        ),
        strict_source_scope_item_keys=strict_source_scope_item_keys,
        status_payload_override=status_payload_override,
        paper_statement_map_override=paper_statement_map_override,
        administrative_projection_rebind_override=(
            administrative_projection_rebind_override
        ),
    )
    receipt_occurrences: dict[str, list[tuple[str, str, str, str, str, str]]] = {}
    receipt_component_keys: dict[str, set[str]] = {}
    receipt_identities: dict[str, set[tuple[str, str, str, str, str, str]]] = {}
    for receipt in receipts:
        source_key = receipt.source_judgment_key.strip()
        if source_key not in raw_occurrences:
            continue
        identity = (
            source_key,
            receipt.component_key.strip(),
            receipt.component_sha256.strip().lower(),
            receipt.structural_type_sha256.strip().lower(),
            receipt.semantic_model_judgment_key.strip(),
            receipt.component_source_contract_association_sha256.strip().lower(),
        )
        if (
            not all(identity)
            or any(
                not re.fullmatch(r"[0-9a-f]{64}", value)
                for value in identity[2:4] + identity[5:]
            )
        ):
            invalid_keys.add(source_key)
            continue
        component_keys = receipt_component_keys.setdefault(source_key, set())
        identities = receipt_identities.setdefault(source_key, set())
        if identity[1] in component_keys or identity in identities:
            invalid_keys.add(source_key)
            continue
        component_keys.add(identity[1])
        identities.add(identity)
        receipt_occurrences.setdefault(source_key, []).append(identity)

    covered: set[str] = set()
    for source_key, expected in raw_occurrences.items():
        actual = receipt_occurrences.get(source_key, [])
        if (
            source_key not in invalid_keys
            and len(expected) == len(actual)
            and set(expected) == set(actual)
        ):
            covered.add(source_key)
    return frozenset(covered)


def theorem_realization_component_contract_findings(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
    current_source_spec_correspondence_receipts: Iterable[
        StrictSourceSpecCorrespondenceReceipt
    ] = (),
    semantic_contract_executable_terminal_component_receipts: Iterable[
        SemanticContractExecutableTerminalComponentReceipt
    ] = (),
    recursive_field_explicit_parent_component_receipts: Iterable[
        RecursiveFieldExplicitParentComponentReceipt
    ] = (),
    strict_source_scope_item_keys: Iterable[str] | None = None,
    configured_assumption_regularity_context_override: object = (
        _CONTEXT_OVERRIDE_UNSET
    ),
    configured_assumption_regularity_context_error_override: str | None = None,
) -> list[Finding]:
    """Require provenance for every generated theorem-realization component.

    The direct theorem ``Spec`` route remains the authoritative conclusion
    fidelity check. This complementary gate checks the complete realization
    graph: inputs, record/model fields, result certificates, and dependent
    nodes. Transitive proof/local dependencies are checked by Lean's recursive
    Spec graph rather than a duplicate Python traversal. Structural discovery
    only adds components; it never grants a data/model exemption.
    """

    folder = PAPERS / paper
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json") or {}
    )
    statement_map = (
        paper_statement_map_override
        if paper_statement_map_override is not None
        else load_payload(folder / "audit" / "paper_statement_map.json")
    )
    requires_occurrence_contract = theorem_realization_contract_requested(
        status_payload,
        statement_map if isinstance(statement_map, Mapping) else None,
        folder=folder,
    )
    if not requires_occurrence_contract:
        # The source-record generator emits the occurrence ledger for every
        # paper so later audits can activate v11 without regenerating its
        # structural discovery. Availability is not itself activation, and an
        # unchanged baseline-v10 paper retains its established interpretation.
        return []
    if audit_payload.get("theorem_realization_contract_schema") != 1:
        return [
            Finding(
                paper,
                "<theorem-realization ledger>",
                "<generated component schema>",
                (),
                "theorem-realization component contract ledger is missing schema 1; "
                "this is a legacy/pending audit and cannot receive occurrence-level source-claim closeout credit",
            )
        ]

    source_proof_fidelity = audit_payload.get("source_proof_fidelity")
    status = str(status_payload.get("status") or "")
    administrative_projection_rebind = (
        administrative_projection_rebind_context_or_override(
            paper,
            audit_payload,
            status_payload,
            administrative_projection_rebind_override,
        )
    )
    regularity_context, regularity_context_error = (
        configured_assumption_regularity_context_or_override(
            folder,
            audit_payload,
            status_payload,
            configured_assumption_regularity_context_override,
            configured_assumption_regularity_context_error_override,
        )
    )
    source_item_semantic_sha256_by_key = _current_source_item_semantic_sha256_by_key(
        statement_map if isinstance(statement_map, Mapping) else None
    )
    source_correction_identities = current_source_correction_identity_by_key(
        statement_map if isinstance(statement_map, Mapping) else None,
        source_proof_fidelity if isinstance(source_proof_fidelity, Mapping) else None,
    )

    # This is deliberately a generic currentness receipt. A route's exact
    # source anchor, atom binding, and correction record decide what it
    # realizes, while the affirmative classification check below distinguishes
    # a valid source disposition from a response that simply claims no credit.
    current_source_disposition_keys: set[str] = set()
    all_raw_items: list[tuple[str, Mapping[str, Any]]] = []
    for section in (
        "theorem_facing_input_items",
        "boundary_input_items",
        "conclusion_dependency_items",
        "type_valued_certificate_result_items",
        "recursive_field_items",
    ):
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if isinstance(item, Mapping):
                all_raw_items.append((section, item))
    for _section, item in all_raw_items:
        key = str(item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        if not key or not isinstance(judgment, Mapping):
            continue
        if regularity_context_error and (
            str(judgment.get("classification") or "").strip()
            == FORMALIZATION_REGULARITY_CLASSIFICATION
        ):
            return [
                Finding(
                    paper,
                    str(item.get("row") or "<theorem-realization ledger>"),
                    str(item.get("binder") or key),
                    (key,),
                    "configured-assumption formalization regularity is invalid: "
                    + regularity_context_error,
                )
            ]
        if source_input_has_current_target_disposition(
            item,
            judgment,
            statement_map=(dict(statement_map) if isinstance(statement_map, Mapping) else None),
            source_proof_fidelity=(
                dict(source_proof_fidelity)
                if isinstance(source_proof_fidelity, Mapping)
                else None
            ),
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
            configured_assumption_formalization_regularity_context=regularity_context,
        ):
            current_source_disposition_keys.add(key)

    findings: list[Finding] = []
    component_occurrences = theorem_realization_component_occurrence_index(
        audit_payload
    )
    atom_receipts = current_source_claim_atom_receipts(audit_payload)
    require_source_claim_atoms = bool(
        isinstance(statement_map, Mapping)
        and statement_map.get("source_claim_atoms_schema") == 1
    )
    domain_receipts = current_source_domain_correspondence_receipts(
        paper,
        audit_payload,
        judgments,
        status_payload_override=status_payload,
        paper_statement_map_override=(
            statement_map if isinstance(statement_map, Mapping) else None
        ),
        administrative_projection_rebind_override=(
            administrative_projection_rebind
        ),
    )
    full_surface_receipts = (
        current_transparent_spec_full_surface_correspondence_receipts(
            paper,
            audit_payload,
            judgments,
            current_source_spec_correspondence_receipts=(
                current_source_spec_correspondence_receipts
            ),
            strict_source_scope_item_keys=strict_source_scope_item_keys,
            status_payload_override=status_payload,
            paper_statement_map_override=(
                statement_map if isinstance(statement_map, Mapping) else None
            ),
            administrative_projection_rebind_override=(
                administrative_projection_rebind
            ),
        )
    )
    for section, raw_item in theorem_realization_components(audit_payload):
        if not isinstance(raw_item, Mapping):
            continue
        item = raw_item
        key = str(item.get("source_judgment_key") or item.get("judgment_key") or "").strip()
        judgment = judgments.get(key)
        errors = theorem_realization_component_contract_errors(
            item,
            judgment if isinstance(judgment, Mapping) else {},
            source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
            current_exact_source_antecedent_keys=current_source_disposition_keys,
            # A sidecar string cannot manufacture a derivation. The resolver
            # remains empty until its Lean Meta declaration/type/dependency
            # receipt is available.
            checked_lean_bridge_receipts=(),
            source_domain_correspondence_receipts=domain_receipts,
            transparent_spec_full_surface_correspondence_receipts=(
                full_surface_receipts
            ),
            semantic_contract_executable_terminal_component_receipts=(
                semantic_contract_executable_terminal_component_receipts
            ),
            recursive_field_explicit_parent_component_receipts=(
                recursive_field_explicit_parent_component_receipts
            ),
            current_component_sha256s_by_source_judgment_key=component_occurrences,
            current_source_claim_atom_receipts=atom_receipts,
            require_source_claim_atom=require_source_claim_atoms,
            current_source_disposition_keys=current_source_disposition_keys,
            current_source_correction_identity_by_key=source_correction_identities,
        )
        if not errors:
            continue
        raw_input = item.get("input")
        binder = str(item.get("binder") or "").strip()
        if not binder and isinstance(raw_input, Mapping):
            binder = str(raw_input.get("names") or "").strip()
        findings.append(
            Finding(
                paper,
                str(item.get("row") or section).strip() or section,
                binder or key or "<theorem-facing premise>",
                (key,) if key else (),
                "theorem-realization component lacks a complete source-claim semantic contract: "
                + "; ".join(errors),
            )
        )
    return findings


# Compatibility for callers during the terminology migration. The generic
# policy is semantic restrictions, not an operational-proposition name class.
theorem_facing_semantic_restriction_findings = theorem_realization_component_contract_findings
theorem_facing_operational_obligation_findings = theorem_realization_component_contract_findings


@dataclass(frozen=True)
class SemanticModelRecordBinding:
    """A complete, source-bound semantic model record binding.

    This is intentionally keyed by generator-owned declaration/signature and
    record-input identities.  A shared recursive field key alone cannot carry
    convention credit to another reviewed theorem.
    """

    declaration_identity: tuple[str, str]
    elaborated_signatures: frozenset[tuple[str, str]]
    record_root: str
    binder_names: frozenset[str]
    binder_atom_identities: tuple[tuple[str, str, str], ...]
    fully_qualified_expanded_record_type: str
    resolved_structure_alias_identity: tuple[str, str, str] | None
    field_keys: frozenset[str]
    source_model_judgment_key: str
    legacy_compatibility: bool = False
    transparent_spec_parent_receipt: TransparentSpecSemanticParentReceipt | None = None


@dataclass(frozen=True)
class TransparentSpecSemanticParentRoute:
    """Exact schema-2 route from a transparent Spec to its evidence model."""

    semantic_model_judgment_key: str
    evidence_declaration: str


def _generated_dependency_binder_names(item: Mapping[str, Any]) -> frozenset[str]:
    """Read one generated binder group without using its spelling as evidence."""

    raw_names = item.get("binder_names")
    if raw_names is not None:
        if not isinstance(raw_names, list):
            return frozenset()
        names = [str(name).strip() for name in raw_names if str(name).strip()]
        return frozenset(names) if names and len(names) == len(set(names)) else frozenset()
    names = [
        name.strip()
        for name in re.split(r"\s+", str(item.get("binder") or "").strip())
        if name.strip() and name.strip() not in {"_", "inst"}
        and not name.strip().startswith("[")
        and not name.strip().endswith("]")
    ]
    return frozenset(names) if names and len(names) == len(set(names)) else frozenset()


def _generated_binder_atom_identities(
    raw_atoms: object,
) -> tuple[tuple[str, str, str], ...] | None:
    """Read an ordered Lean-owned outer-binder atom receipt fail-closed."""

    if not isinstance(raw_atoms, list) or not raw_atoms:
        return None
    identities: list[tuple[str, str, str]] = []
    prior_index = -1
    for raw_atom in raw_atoms:
        if not isinstance(raw_atom, Mapping):
            return None
        ref = str(raw_atom.get("ref") or "").strip()
        role = str(raw_atom.get("role") or "").strip()
        digest = str(raw_atom.get("signature_atom_sha256") or "").strip().lower()
        ref_match = re.fullmatch(r"b/([0-9]+)", ref)
        if (
            ref_match is None
            or role not in {"parameter", "assumption"}
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
        ):
            return None
        binder_index = int(ref_match.group(1))
        if binder_index <= prior_index:
            return None
        prior_index = binder_index
        identities.append((ref, role, digest))
    return tuple(identities)


def _fully_qualified_expanded_record_type_has_root(
    type_text: object, record_root: str
) -> bool:
    """Check the generated fully-qualified outer record constructor.

    The ordered Lean atom hash owns the alpha-invariant elaborated binder
    identity.  This independent generated surface proves that the separately
    generated record root is the direct head, rather than a nested mention
    inside another carrier.  Strict parent/dependency joins additionally
    compare this complete surface byte-for-byte; this helper alone is not a
    parent-binding predicate.
    """

    normalized = str(type_text or "").strip()
    match = re.match(
        r"^@?([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
        normalized,
    )
    return bool(match is not None and match.group(1) == record_root)


def _generated_review_dependency_roots(
    raw_semantic: Mapping[str, Any], semantic_declaration: str
) -> frozenset[str]:
    """Read exact reviewed roots for one generated Lean dependency graph.

    A semantic item normally owns its graph directly.  A transparent ``Spec``
    may own the graph instead, but only when the generator records a complete
    linear structural route from that exact Spec to the reviewed evidence
    declaration.  Names are identities here, never lexical classifications.
    """

    roots = {semantic_declaration}
    expanded = raw_semantic.get("expanded_lean_surface")
    if not isinstance(expanded, Mapping):
        return frozenset(roots)
    expansion = expanded.get("review_alias_expansion")
    if not isinstance(expansion, Mapping):
        return frozenset(roots)
    reviewed = str(expansion.get("reviewed_declaration") or "").strip()
    effective = str(expansion.get("effective_declaration") or "").strip()
    if (
        not reviewed
        or expansion.get("complete") is not True
        or effective != semantic_declaration
    ):
        return frozenset(roots)
    if reviewed == semantic_declaration:
        roots.add(reviewed)
        return frozenset(roots)
    if expansion.get("structural_alpha_normalized_equal") is not True:
        return frozenset(roots)
    raw_steps = expansion.get("steps")
    if not isinstance(raw_steps, list) or not raw_steps:
        return frozenset(roots)
    current = reviewed
    seen = {current}
    for raw_step in raw_steps:
        if not isinstance(raw_step, Mapping):
            return frozenset(roots)
        source = str(raw_step.get("from") or "").strip()
        target = str(raw_step.get("to") or "").strip()
        kind = str(raw_step.get("kind") or "").strip()
        if source != current or not target or not kind or target in seen:
            return frozenset(roots)
        current = target
        seen.add(current)
    if current == semantic_declaration:
        roots.add(reviewed)
    return frozenset(roots)


def _generated_resolved_structure_alias_identity(
    audit_payload: Mapping[str, Any],
    raw_semantic: Mapping[str, Any],
    raw_binding: Mapping[str, Any],
    *,
    semantic_declaration: str,
    record_root: str,
) -> tuple[str, str, str] | None:
    """Validate one exact generated alias route to a record root.

    The type spelling only selects candidates.  Acceptance requires a unique
    fully-qualified alias in the generator-owned resolved-alias ledger and an
    exact declaration/body identity on the scan-complete Lean dependency
    graph for this reviewed semantic item.  Missing, stale, cyclic, ambiguous,
    or merely same-named aliases therefore fail closed.
    """

    source_type = str(raw_binding.get("source_type_canonical") or "").strip()
    head_match = re.match(
        r"^\(*\s*@?([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)",
        source_type,
    )
    aliases = audit_payload.get("resolved_structure_aliases")
    if head_match is None or not isinstance(aliases, Mapping):
        return None
    source_head = head_match.group(1)
    alias_map: dict[str, str] = {}
    for raw_alias, raw_target in aliases.items():
        alias = str(raw_alias).strip()
        target = str(raw_target).strip()
        if not alias or "." not in alias or not target or "." not in target:
            return None
        alias_map[alias] = target

    expanded = raw_semantic.get("expanded_lean_surface")
    terminal_surface = (
        expanded.get("terminal_term_dependency_surface")
        if isinstance(expanded, Mapping)
        else None
    )
    if (
        not isinstance(terminal_surface, Mapping)
        or terminal_surface.get("scan_complete") is not True
        or terminal_surface.get("incomplete_reasons") != []
    ):
        return None
    raw_definitions = terminal_surface.get("transparent_definitions")
    if not isinstance(raw_definitions, list):
        return None
    dependency_roots = _generated_review_dependency_roots(
        raw_semantic, semantic_declaration
    )
    definitions_by_declaration: dict[str, list[Mapping[str, Any]]] = {}
    for raw_definition in raw_definitions:
        if not isinstance(raw_definition, Mapping):
            return None
        declaration = str(raw_definition.get("declaration") or "").strip()
        if declaration:
            definitions_by_declaration.setdefault(declaration, []).append(
                raw_definition
            )

    if "." in source_head:
        candidates = [source_head] if source_head in alias_map else []
    else:
        candidates = [
            alias
            for alias in alias_map
            if alias.rsplit(".", 1)[-1] == source_head
        ]
    graph_candidates = [
        alias
        for alias in candidates
        if alias in definitions_by_declaration
    ]
    if len(graph_candidates) != 1:
        return None
    alias = graph_candidates[0]

    seen: set[str] = set()
    current = alias
    first_identity: tuple[str, str, str] | None = None
    while current != record_root:
        if current in seen:
            return None
        seen.add(current)
        target = alias_map.get(current)
        definitions = definitions_by_declaration.get(current)
        if target is None or definitions is None or len(definitions) != 1:
            return None
        definition = definitions[0]
        declaration_sha = _sha256_value(definition.get("declaration_sha256"))
        body_sha = _sha256_value(definition.get("body_sha256"))
        dependency_chain = definition.get("dependency_chain")
        if (
            str(definition.get("declaration") or "").strip() != current
            or str(definition.get("kind") or "").strip() not in {"abbrev", "def"}
            or definition.get("body_surface_inspectable") is not True
            or declaration_sha is None
            or body_sha is None
            or not isinstance(dependency_chain, list)
            or len(dependency_chain) < 2
            or str(dependency_chain[0]).strip() not in dependency_roots
            or str(dependency_chain[-1]).strip() != current
        ):
            return None
        if first_identity is None:
            first_identity = (current, declaration_sha, body_sha)
        current = target
    return first_identity


def _component_has_exact_selected_record_route(
    component: Mapping[str, Any],
    *,
    record_root: str,
    semantic_declaration: str,
    semantic_signatures: frozenset[tuple[str, str]],
) -> bool:
    """Check one exact generator-owned field occurrence route."""

    expected_signatures = {
        digest
        for declaration, digest in semantic_signatures
        if declaration == semantic_declaration
    }
    raw_occurrences = component.get("selected_review_route_occurrences")
    if len(expected_signatures) != 1 or not isinstance(raw_occurrences, list):
        return False
    matches = 0
    for raw_occurrence in raw_occurrences:
        if not isinstance(raw_occurrence, Mapping):
            return False
        route_path = raw_occurrence.get("selected_route_path")
        field_path = str(raw_occurrence.get("recursive_field_path") or "").strip()
        if not isinstance(route_path, Mapping):
            continue
        declaration_path = route_path.get("declaration_path")
        route_roles = route_path.get("selected_route_roles")
        if (
            str(raw_occurrence.get("record_root") or "").strip() == record_root
            and field_path.startswith(record_root + " -> ")
            and str(route_path.get("selected_qualified_declaration") or "").strip()
            == semantic_declaration
            and str(
                route_path.get("selected_elaborated_signature_sha256") or ""
            ).strip().lower()
            in expected_signatures
            and isinstance(declaration_path, list)
            and bool(declaration_path)
            and str(declaration_path[0]).strip() == semantic_declaration
            and isinstance(route_roles, list)
            and "selected_source_route" in route_roles
        ):
            matches += 1
    return matches == 1


def _generated_record_binding_roots(
    item: Mapping[str, Any],
) -> tuple[
    str,
    frozenset[str],
    tuple[tuple[str, str, str], ...] | None,
    str,
] | None:
    """Read one exact semantic-model record input binding fail-closed."""

    roots = item.get("record_roots")
    names = item.get("binder_names")
    if not isinstance(roots, list):
        return None
    root_values = [str(value).strip() for value in roots if str(value).strip()]
    name_values = (
        [str(value).strip() for value in names if str(value).strip()]
        if isinstance(names, list)
        else []
    )
    if (
        len(root_values) != 1
        or "." not in root_values[0]
        or len(name_values) != len(set(name_values))
    ):
        return None
    return (
        root_values[0],
        frozenset(name_values),
        _generated_binder_atom_identities(
            item.get("elaborated_outer_binder_atoms")
        ),
        str(
            item.get("fully_qualified_expanded_type_canonical") or ""
        ).strip(),
    )


def _recursive_field_closure(
    field_items: Mapping[str, Mapping[str, Any]],
    judgments: Mapping[str, Mapping[str, Any]],
    root: str,
) -> frozenset[str] | None:
    """Follow generated nested-record links from one fully-qualified root."""

    by_structure: dict[str, set[str]] = {}
    for key, item in field_items.items():
        structure = str(item.get("structure") or "").strip()
        if not structure or not key:
            return None
        by_structure.setdefault(structure, set()).add(key)

    seen: set[str] = set()
    visiting: set[str] = set()
    closure: set[str] = set()

    def visit(structure: str) -> bool:
        if structure in visiting:
            return False
        if structure in seen:
            return True
        keys = by_structure.get(structure)
        if not keys:
            return False
        visiting.add(structure)
        for key in keys:
            item = field_items.get(key)
            if item is None:
                return False
            closure.add(key)
            nested = item.get("nested_structures")
            if not isinstance(nested, list):
                return False
            for raw_nested in nested:
                nested_structure = str(raw_nested or "").strip()
                if not nested_structure:
                    return False
                if nested_structure not in by_structure:
                    # A non-propositional fieldless carrier can have no
                    # generated subfields. It cannot conceal a proposition.
                    judgment = judgments.get(key)
                    if (
                        not isinstance(judgment, Mapping)
                        or str(judgment.get("classification") or "").strip()
                        != "nonpropositional_witness_data"
                    ):
                        return False
                    continue
                if not visit(nested_structure):
                    return False
        visiting.remove(structure)
        seen.add(structure)
        return True

    return frozenset(closure) if visit(root) else None


def _result_assumption_component_for_exact_atom(
    raw_items: object,
    component_groups: Mapping[str, Sequence[Mapping[str, Any]]],
    *,
    declaration_identity: tuple[str, str],
    elaborated_signatures: frozenset[tuple[str, str]],
    atom: Mapping[str, str],
) -> Mapping[str, Any] | None:
    """Find one result-premise component by its generated telescope atom.

    A state-transition receipt may transport source-domain credit only to the
    source-shaped initial and terminal predicates it actually checks.  This
    helper deliberately matches the fully qualified declaration identity,
    complete elaborated signature set, and one generated result-telescope atom.
    It does not inspect a binder, field, record, or declaration spelling.
    """

    if (
        not isinstance(raw_items, list)
        or len(elaborated_signatures) != 1
        or str(atom.get("role") or "").strip() != "assumption"
    ):
        return None
    expected_signature = next(iter(elaborated_signatures))[1]
    candidates: list[Mapping[str, Any]] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, Mapping):
            return None
        item = dict(raw_item)
        if (
            str(item.get("kind") or "").strip() != "theorem_facing_input"
            or _reviewed_declaration_identity(item) != declaration_identity
            or _elaborated_signature_identities(
                item, declaration=declaration_identity[0]
            )
            != elaborated_signatures
        ):
            continue
        path = item.get("elaborated_result_path")
        if (
            not isinstance(path, Mapping)
            or str(path.get("manifest_signature_sha256") or "").strip().lower()
            != expected_signature
            or str(path.get("input_section") or "").strip() != "result"
            # Lean represents proposition binders with the same semantic role
            # whether source syntax used `->` or `forall (h : P)`.  The exact
            # atom identity below, rather than that presentation choice,
            # selects the reviewed premise.
            or str(path.get("connective") or "").strip()
            not in {"arrow", "forall"}
            or path.get("binder_atoms") != [dict(atom)]
        ):
            continue
        key = str(item.get("judgment_key") or "").strip()
        components = component_groups.get(key)
        if not key or not isinstance(components, Sequence):
            return None
        matching = [
            component
            for component in components
            if isinstance(component, Mapping)
            and str(component.get("source_component_section") or "").strip()
            == "theorem_facing_input_items"
        ]
        if len(matching) != 1:
            return None
        candidates.append(matching[0])
    return candidates[0] if len(candidates) == 1 else None


def _semantic_model_source_association(
    item: Mapping[str, Any],
) -> tuple[Mapping[str, Any], str] | None:
    """Return one direct, schema-2 source association for a semantic model."""

    candidates = (
        (
            SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
            {SOURCE_ASSUMPTION_ASSOCIATION_ROLE},
        ),
        (
            STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD,
            {STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE},
        ),
        (
            "source_statement_association",
            {"direct_source_route", STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE},
        ),
        ("semantic_contract_source_association", {"direct_evidence", "transparent_spec"}),
    )
    for field, permitted_roles in candidates:
        association = item.get(field)
        if not isinstance(association, Mapping):
            continue
        if association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA:
            continue
        if str(association.get("role") or "").strip() not in permitted_roles:
            continue
        if field == SOURCE_ASSUMPTION_ASSOCIATION_FIELD:
            digest, error = source_assumption_effective_semantic_pin(association)
            if error:
                continue
        elif field == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_FIELD:
            digest, error = statement_source_component_effective_semantic_pin(
                association
            )
            if error:
                continue
        else:
            digest = _sha256_value(
                association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
            )
        if digest is not None:
            return association, digest
    return None


def _current_direct_semantic_model_association_route(
    raw_semantic: Mapping[str, Any],
    *,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> tuple[Mapping[str, Any], str] | None:
    """Reconstruct one current direct semantic association without a sidecar.

    This checks only generator-owned structural evidence: the schema-2
    association, its effective semantic pin, and exact declaration/signature
    identities.  It deliberately does *not* accept a source claim on that
    basis alone.  Ordinary model, definition, convention, and formula routes
    still call :func:`_current_direct_semantic_model_route`, which additionally
    requires the current semantic-model review judgment.  The sole alternate
    consumer is the strict source-to-transparent-Spec projector, where a
    separately checked atom-complete source-to-Spec runtime receipt supplies
    the source-semantic disposition.
    """

    semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
    semantic_identity = _reviewed_declaration_identity(dict(raw_semantic))
    if (
        not semantic_key
        or semantic_identity is None
    ):
        return None
    semantic_signatures = _elaborated_signature_identities(
        dict(raw_semantic), declaration=semantic_identity[0]
    )
    parent_route = _semantic_model_source_association(raw_semantic)
    if not semantic_signatures or parent_route is None:
        return None
    raw_association, _raw_association_sha256 = parent_route
    association = administrative_projection_rebound_association(
        raw_association, administrative_projection_rebind
    )
    if (
        str(association.get("association_origin") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
        and str(association.get("role") or "").strip()
        == SOURCE_ASSUMPTION_ASSOCIATION_ROLE
    ):
        assumption_pin, assumption_error = source_assumption_effective_semantic_pin(
            association
        )
        association_sha256 = assumption_pin if not assumption_error else None
    elif (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    ):
        statement_component_pin, statement_component_error = (
            statement_source_component_effective_semantic_pin(association)
        )
        association_sha256 = (
            statement_component_pin if not statement_component_error else None
        )
    elif (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        statement_review_pin, statement_review_error = (
            statement_source_review_effective_semantic_pin(association)
        )
        association_sha256 = (
            statement_review_pin if not statement_review_error else None
        )
    else:
        association_sha256 = _sha256_value(
            association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
        )
    association_identity = _reviewed_declaration_identity(dict(association))
    association_signature = _association_signature_identity(
        association.get("reviewed_elaborated_signature_identity"),
        declaration=semantic_identity[0],
    )
    if (
        association_sha256 is None
        or association_identity != semantic_identity
        or association_signature is None
        or semantic_signatures != frozenset({association_signature})
    ):
        return None
    return raw_association, association_sha256


def _current_direct_semantic_model_route(
    paper: str,
    folder: Path,
    judgment_path: Path,
    raw_semantic: Mapping[str, Any],
    semantic_judgment: Mapping[str, Any],
    *,
    audit_payload: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> tuple[Mapping[str, Any], str] | None:
    """Validate a direct route plus its required ordinary model-review judgment.

    The structural association is shared with the strict source-to-Spec
    projector, but the ordinary source-model lane must retain its
    dimension-by-dimension LLM review.  Keeping this check after the shared
    structural reconstruction prevents a bare source locator from becoming a
    route in either lane.
    """

    semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
    if not semantic_key or not isinstance(semantic_judgment, Mapping):
        return None
    direct_route = _current_direct_semantic_model_association_route(
        raw_semantic,
        administrative_projection_rebind=administrative_projection_rebind,
    )
    if direct_route is None:
        return None
    if semantic_model_review_findings(
        paper,
        folder,
        judgment_path,
        [dict(raw_semantic)],
        {semantic_key: dict(semantic_judgment)},
        digest=str(audit_payload.get("source_record_audit_sha256") or ""),
        expected_item_digests=source_record_expected_item_digests(dict(audit_payload)),
        expected_item_digest_pins=source_record_expected_item_digest_pins(
            dict(audit_payload)
        ),
        severity="ERROR",
        target_disposition_statement_map=dict(statement_map),
        target_disposition_source_proof_fidelity=dict(source_proof_fidelity),
        target_disposition_validated_vocabulary_binding_source_item_ids=(
            audit_payload.get(
                "source_coverage_validated_vocabulary_binding_source_items"
            )
        ),
        target_disposition_validated_vocabulary_direct_route_source_item_ids=(
            audit_payload.get(
                "source_coverage_validated_vocabulary_direct_route_source_items"
            )
        ),
        target_disposition_administrative_projection_rebind=(
            administrative_projection_rebind
        ),
        enforce_target_disposition=True,
    ):
        return None
    return direct_route


def _semantic_model_convention_ids(
    judgment: Mapping[str, Any], association_sha256: str
) -> frozenset[str] | None:
    """Return conventions explicitly approved by one validated semantic model."""

    dimensions = judgment.get("semantic_model_dimensions")
    if not isinstance(dimensions, Mapping):
        return None
    ids: set[str] = set()
    for response in dimensions.values():
        if not isinstance(response, Mapping):
            continue
        if (
            str(response.get("verdict") or "").strip()
            != "matches_approved_source_convention"
            or str(response.get(SOURCE_TARGET_DISPOSITION_FIELD) or "").strip()
            != "approved_source_convention"
            or _sha256_value(response.get(SEMANTIC_ASSOCIATION_SHA256_FIELD))
            != association_sha256
        ):
            continue
        raw_ids = response.get("model_convention_ids")
        if not isinstance(raw_ids, list):
            return None
        dimension_ids = [str(value).strip() for value in raw_ids if str(value).strip()]
        if not dimension_ids or len(dimension_ids) != len(set(dimension_ids)):
            return None
        ids.update(dimension_ids)
    return frozenset(ids) if ids else None


def _semantic_model_judgment_with_rebound_dimension_responses(
    judgment: Mapping[str, Any],
    raw_association: Mapping[str, Any],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> Mapping[str, Any]:
    """Transport only exact parent-bound dimension response pins.

    Semantic-model judgments keep their source-target assertions below
    ``semantic_model_dimensions`` rather than at the judgment root.  Each
    dimension can therefore be advanced only through the one exact raw parent
    association that the receipt reconstructed.  The repository semantic gate
    independently validates every resulting convention hash and target pin;
    this helper merely makes that already-validated current association visible
    to the record-binding consumer.
    """

    raw_dimensions = judgment.get("semantic_model_dimensions")
    if not isinstance(raw_dimensions, Mapping):
        return judgment
    rebound = dict(judgment)
    dimensions: dict[str, object] = {}
    for raw_key, raw_response in raw_dimensions.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_response, Mapping):
            dimensions[str(raw_key)] = raw_response
            continue
        dimensions[key] = administrative_projection_rebound_response(
            raw_response,
            raw_association,
            administrative_projection_rebind,
        )
    rebound["semantic_model_dimensions"] = dimensions
    return rebound


def _legacy_semantic_model_field_is_safe(
    field: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    raw_semantic_parent_association: Mapping[str, Any],
    semantic_association_sha256: str,
    semantic_convention_ids: frozenset[str],
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any],
    status: str,
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
) -> bool:
    """Read a pre-v11 record-field receipt without granting v11 credit.

    Historical source-record artifacts use a narrower convention/classification
    transport.  They remain readable so a new audit does not erase prior work,
    but this helper is called only when the generated occurrence ledger has
    *not* opted into schema 1.  New theorem-realization contracts never reach
    this category-driven adapter.
    """

    classification = str(judgment.get("classification") or "").strip()
    location = str(
        judgment.get("source_location") or judgment.get("source_evidence") or ""
    ).strip()
    if classification == "approved_source_convention":
        has_direct_route = isinstance(
            field.get("source_contract_association"), Mapping
        ) or isinstance(field.get("recursive_field_explicit_parent_route"), Mapping)
        if has_direct_route:
            return not approved_source_convention_antecedent_errors(
                field,
                judgment,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                status=status,
                administrative_projection_rebind=administrative_projection_rebind,
            ) and bool(EXACT_SOURCE_LOCATOR_RE.search(location))
        effective_judgment = administrative_projection_rebound_response(
            judgment,
            raw_semantic_parent_association,
            administrative_projection_rebind,
        )
        if approved_source_convention_metadata_errors(
            effective_judgment, source_proof_fidelity=source_proof_fidelity
        ):
            return False
        if _sha256_value(
            effective_judgment.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
        ) != semantic_association_sha256:
            return False
        raw_ids = effective_judgment.get("model_convention_ids")
        if not isinstance(raw_ids, list):
            return False
        field_ids = [str(value).strip() for value in raw_ids if str(value).strip()]
        return bool(
            field_ids
            and len(field_ids) == len(set(field_ids))
            and set(field_ids).issubset(semantic_convention_ids)
            and EXACT_SOURCE_LOCATOR_RE.search(location)
        )
    if classification == "validated_source_assumption":
        return bool(
            EXACT_SOURCE_LOCATOR_RE.search(location)
            and not source_input_target_disposition_errors(
                field,
                judgment,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                status=status,
                administrative_projection_rebind=administrative_projection_rebind,
            )
        )
    if classification == "nonpropositional_witness_data":
        return bool(EXACT_SOURCE_LOCATOR_RE.search(location))
    if classification == "container_recursively_audited":
        nested = field.get("nested_structures")
        return isinstance(nested, list) and any(
            str(value or "").strip() for value in nested
        )
    if classification == "proved_from_primitives":
        return bool(
            str(
                judgment.get("lean_derivation")
                or judgment.get("constructor")
                or judgment.get("derived_from")
                or ""
            ).strip()
        )
    return False


def _current_semantic_model_field_is_safe(
    field: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    raw_semantic_parent_association: Mapping[str, Any],
    semantic_association_sha256: str,
    semantic_convention_ids: frozenset[str],
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any],
    status: str,
    source_model_judgment_key: str = "",
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    source_item_semantic_sha256_by_key: Mapping[str, str] | None = None,
    current_source_disposition_keys: set[str] | None = None,
    current_source_correction_identities: (
        Mapping[str, Mapping[str, Any] | None] | None
    ) = None,
    current_component_sha256s_by_source_judgment_key: Mapping[str, Iterable[str]] | None = None,
    current_source_claim_atom_receipts: Iterable[SourceClaimAtomReceipt] = (),
    require_source_claim_atom: bool = False,
) -> bool:
    """Check one closure field under an already validated semantic parent.

    A field with its own direct generated source route must be judged against
    that route, not inherited from its parent.  A route-less field is
    different: its response may carry the exact prior semantic pin of the
    already-validated parent association.  In that one case, the receipt can
    transport the response before this binding compares it to the current
    parent.  The transport itself still requires byte-for-byte association
    identity and the exact old response pin; no root, field, or declaration
    spelling participates in the decision.
    """

    if not source_model_judgment_key:
        # Private callers that do not provide an occurrence-owned model key
        # are reading an archived v10 field route. Keep that compatibility
        # interpretation isolated from the schema-1 realization protocol.
        return _legacy_semantic_model_field_is_safe(
            field,
            judgment,
            raw_semantic_parent_association=raw_semantic_parent_association,
            semantic_association_sha256=semantic_association_sha256,
            semantic_convention_ids=semantic_convention_ids,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            status=status,
            administrative_projection_rebind=administrative_projection_rebind,
        )

    _ = (
        raw_semantic_parent_association,
        semantic_association_sha256,
        semantic_convention_ids,
    )
    component_key = str(field.get("judgment_key") or "").strip()
    component_sha = source_claim_component_sha256(field)
    generic_errors = theorem_realization_component_contract_errors(
        field,
        judgment,
        source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
        current_exact_source_antecedent_keys=(),
        # No bridge may be manufactured from a sidecar string. A future
        # Lean-owned resolver supplies exact receipts here.
        checked_lean_bridge_receipts=(),
        source_domain_correspondence_receipts=(
            SourceDomainCorrespondenceReceipt(
                component_key=component_key,
                component_sha256=component_sha,
                source_model_judgment_key=source_model_judgment_key,
            ),
        ),
        current_component_sha256s_by_source_judgment_key=(
            current_component_sha256s_by_source_judgment_key
        ),
        current_source_claim_atom_receipts=current_source_claim_atom_receipts,
        require_source_claim_atom=require_source_claim_atom,
        current_source_disposition_keys=current_source_disposition_keys or set(),
        current_source_correction_identity_by_key=(
            current_source_correction_identities
        ),
    )
    if generic_errors:
        return False
    # A successful occurrence-bound contract is the acceptance proof.  The
    # historic response classification may still guide legacy dashboard
    # presentation, but it cannot change an otherwise identical schema-1
    # realization outcome.
    return True


def _current_v10_record_field_closure_completion_is_safe(
    candidates: Sequence[RecordFieldClosureCompletionCandidate],
    *,
    semantic_key: str,
    semantic_identity: tuple[str, str],
    semantic_signatures: frozenset[tuple[str, str]],
    raw_association_sha256: str,
    root: str,
    binder_names: frozenset[str],
    closure: frozenset[str],
    semantic_judgment: Mapping[str, Any],
    judgments: Mapping[str, Mapping[str, Any]],
    recursive_field_components: Mapping[str, Mapping[str, Any]],
) -> bool:
    """Accept one v10 field closure only through its exact parent attestation.

    This is intentionally a v10 compatibility projection.  It does not create
    an occurrence-level source-claim semantic contract, so v11's generic
    theorem-realization gate continues to reject these children until a paper
    supplies the stronger v11 route.  Every matching fact here is generated
    identity data or a human attestation bound to that data; no name or source
    location selects a parent.
    """

    if len(semantic_signatures) != 1:
        return False
    matches = [
        candidate
        for candidate in candidates
        if candidate.semantic_model_judgment_key == semantic_key
        and candidate.declaration_identity == semantic_identity
        and candidate.elaborated_signature_identity in semantic_signatures
        and candidate.direct_source_association_sha256 == raw_association_sha256
        and candidate.record_root == root
        and candidate.binder_names == binder_names
        and candidate.field_keys == closure
    ]
    if len(matches) != 1:
        return False
    candidate = matches[0]
    attestation = closure_attestation_for_candidate(
        semantic_judgment, candidate=candidate
    )
    if attestation is None:
        return False
    attestation_digest = closure_attestation_sha256(attestation)
    for field_key, component_key, component_sha, structural_type_sha in (
        candidate.field_components
    ):
        component = recursive_field_components.get(field_key)
        judgment = judgments.get(field_key)
        if not isinstance(component, Mapping) or not isinstance(judgment, Mapping):
            return False
        if (
            str(component.get("judgment_key") or "").strip() != component_key
            or source_claim_component_sha256(component) != component_sha
            or _sha256_value(component.get("structural_type_sha256"))
            != structural_type_sha
        ):
            return False
        if closure_completion_receipt_error(
            judgment.get(RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD),
            candidate=candidate,
            field_key=field_key,
            component_key=component_key,
            component_sha256=component_sha,
            structural_type_sha256=structural_type_sha,
            attestation_sha256=attestation_digest,
        ):
            return False
    return True


def current_complete_semantic_model_record_bindings(
    paper: str,
    audit_payload: Mapping[str, Any],
    judgments: Mapping[str, dict[str, Any]],
    *,
    status_payload_override: Mapping[str, Any] | None = None,
    paper_statement_map_override: Mapping[str, Any] | None = None,
    administrative_projection_rebind_override: object = _CONTEXT_OVERRIDE_UNSET,
) -> tuple[SemanticModelRecordBinding, ...]:
    """Return only source-bound, fully audited record model bindings.

    This is a deliberately narrow compatibility bridge for v10 receipts that
    predate generated per-field parent-route receipts.  It never gives a leaf
    global credit.  Instead it validates the semantic parent, the exact
    record-input binding, and every generated field in that record's closure
    before exposing one binding for that one reviewed declaration.
    """

    folder = PAPERS / paper
    statement_map = (
        paper_statement_map_override
        if paper_statement_map_override is not None
        else load_payload(folder / "audit" / "paper_statement_map.json")
    )
    source_proof_fidelity = audit_payload.get("source_proof_fidelity")
    if not isinstance(statement_map, Mapping) or not isinstance(
        source_proof_fidelity, Mapping
    ):
        return ()
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json") or {}
    )
    status = str(status_payload.get("status") or "")
    strict_component_contract = theorem_realization_contract_active(
        audit_payload,
        status_payload,
        statement_map,
        folder=folder,
    )
    administrative_projection_rebind = (
        administrative_projection_rebind_context_or_override(
            paper,
            audit_payload,
            status_payload,
            administrative_projection_rebind_override,
        )
    )
    raw_fields = audit_payload.get("recursive_field_items")
    raw_semantic_items = audit_payload.get("semantic_model_items")
    expected_field_keys = audit_payload.get("expected_field_judgment_keys")
    if (
        not isinstance(raw_fields, list)
        or not isinstance(raw_semantic_items, list)
        or not isinstance(expected_field_keys, list)
    ):
        return ()
    field_items: dict[str, Mapping[str, Any]] = {}
    for raw_field in raw_fields:
        if not isinstance(raw_field, Mapping):
            return ()
        key = str(raw_field.get("judgment_key") or "").strip()
        if not key or key in field_items:
            return ()
        field_items[key] = raw_field
    expected = {str(key).strip() for key in expected_field_keys if str(key).strip()}
    if not expected or not set(field_items).issubset(expected):
        return ()

    judgment_path = folder / "audit" / "source_record_match_llm.json"
    expected_item_digests = source_record_expected_item_digests(dict(audit_payload))
    expected_item_digest_pins = source_record_expected_item_digest_pins(
        dict(audit_payload)
    )
    source_item_semantic_sha256_by_key = _current_source_item_semantic_sha256_by_key(
        statement_map
    )
    source_correction_identities = current_source_correction_identity_by_key(
        statement_map, source_proof_fidelity
    )
    component_occurrences = theorem_realization_component_occurrence_index(
        audit_payload
    )
    component_groups = theorem_realization_components_by_source_key(audit_payload)
    recursive_field_components: dict[str, Mapping[str, Any]] = {}
    for field_key, components in component_groups.items():
        matching = [
            component
            for component in components
            if str(component.get("source_component_section") or "").strip()
            == "recursive_field_items"
        ]
        if len(matching) == 1:
            recursive_field_components[field_key] = matching[0]
    closure_completion_candidates = (
        current_record_field_closure_completion_candidates(audit_payload)
    )
    atom_receipts = current_source_claim_atom_receipts(audit_payload)
    require_source_claim_atoms = bool(
        statement_map.get("source_claim_atoms_schema") == 1
    )
    current_source_disposition_keys: set[str] = set()
    for section in (
        "theorem_facing_input_items",
        "boundary_input_items",
        "conclusion_dependency_items",
        "type_valued_certificate_result_items",
        "recursive_field_items",
    ):
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            judgment = judgments.get(key)
            if not key or not isinstance(judgment, Mapping):
                continue
            if not source_input_has_current_target_disposition(
                raw_item,
                judgment,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                status=status,
                administrative_projection_rebind=administrative_projection_rebind,
            ):
                continue
            current_source_disposition_keys.add(key)
    candidate_bindings: list[SemanticModelRecordBinding] = []
    for raw_semantic in raw_semantic_items:
        if not isinstance(raw_semantic, Mapping):
            return ()
        semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
        semantic_judgment = judgments.get(semantic_key)
        semantic_identity = _reviewed_declaration_identity(dict(raw_semantic))
        if (
            not semantic_key
            or not isinstance(semantic_judgment, Mapping)
            or semantic_identity is None
        ):
            continue
        semantic_signatures = _elaborated_signature_identities(
            dict(raw_semantic), declaration=semantic_identity[0]
        )
        parent_route = _semantic_model_source_association(raw_semantic)
        if not semantic_signatures or parent_route is None:
            continue
        raw_association, raw_association_sha256 = parent_route
        association = administrative_projection_rebound_association(
            raw_association, administrative_projection_rebind
        )
        association_sha256 = _sha256_value(
            association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD)
        )
        if association_sha256 is None:
            continue
        association_identity = _reviewed_declaration_identity(dict(association))
        association_signature = _association_signature_identity(
            association.get("reviewed_elaborated_signature_identity"),
            declaration=semantic_identity[0],
        )
        if (
            association_identity != semantic_identity
            or association_signature is None
            or semantic_signatures != frozenset({association_signature})
        ):
            continue
        semantic_findings = semantic_model_review_findings(
            paper,
            folder,
            judgment_path,
            [dict(raw_semantic)],
            dict(judgments),
            digest=str(audit_payload.get("source_record_audit_sha256") or ""),
            expected_item_digests=expected_item_digests,
            expected_item_digest_pins=expected_item_digest_pins,
            severity="ERROR",
            target_disposition_statement_map=dict(statement_map),
            target_disposition_source_proof_fidelity=dict(source_proof_fidelity),
            target_disposition_validated_vocabulary_binding_source_item_ids=(
                audit_payload.get(
                    "source_coverage_validated_vocabulary_binding_source_items"
                )
            ),
            target_disposition_validated_vocabulary_direct_route_source_item_ids=(
                audit_payload.get(
                    "source_coverage_validated_vocabulary_direct_route_source_items"
                )
            ),
            target_disposition_administrative_projection_rebind=(
                administrative_projection_rebind
            ),
            enforce_target_disposition=True,
        )
        if semantic_findings:
            continue
        transparent_spec_parent_receipt = (
            _validated_transparent_spec_semantic_parent_receipt(raw_semantic)
        )
        effective_semantic_judgment = _semantic_model_judgment_with_rebound_dimension_responses(
            semantic_judgment,
            raw_association,
            administrative_projection_rebind,
        )
        if strict_component_contract:
            # Schema-1 field routes use the occurrence-bound generic gate.
            # Classifications remain diagnostic only.
            convention_ids = frozenset()
        else:
            convention_ids = _semantic_model_convention_ids(
                effective_semantic_judgment, association_sha256
            )
            if convention_ids is None:
                continue
        raw_bindings = raw_semantic.get("record_input_bindings")
        if not isinstance(raw_bindings, list):
            continue
        for raw_binding in raw_bindings:
            if not isinstance(raw_binding, Mapping):
                continue
            parsed_binding = _generated_record_binding_roots(raw_binding)
            if parsed_binding is None:
                continue
            (
                root,
                binder_names,
                binder_atom_identities,
                fully_qualified_expanded_record_type,
            ) = parsed_binding
            resolved_structure_alias_identity = None
            if strict_component_contract:
                if binder_atom_identities is None:
                    continue
                if not _fully_qualified_expanded_record_type_has_root(
                    fully_qualified_expanded_record_type, root
                ):
                    resolved_structure_alias_identity = (
                        _generated_resolved_structure_alias_identity(
                            audit_payload,
                            raw_semantic,
                            raw_binding,
                            semantic_declaration=semantic_identity[0],
                            record_root=root,
                        )
                    )
                    if resolved_structure_alias_identity is None:
                        continue
            elif not binder_names:
                continue
            closure = _recursive_field_closure(field_items, judgments, root)
            if not closure or not closure.issubset(expected):
                continue
            if strict_component_contract:
                if resolved_structure_alias_identity is not None and any(
                    field_key not in recursive_field_components
                    or not _component_has_exact_selected_record_route(
                        recursive_field_components[field_key],
                        record_root=root,
                        semantic_declaration=semantic_identity[0],
                        semantic_signatures=semantic_signatures,
                    )
                    for field_key in closure
                ):
                    continue
                unsafe_field = any(
                    not isinstance(judgments.get(field_key), Mapping)
                    or field_key not in recursive_field_components
                    or not _current_semantic_model_field_is_safe(
                        recursive_field_components[field_key],
                        judgments[field_key],
                        source_model_judgment_key=semantic_key,
                        raw_semantic_parent_association=raw_association,
                        semantic_association_sha256=association_sha256,
                        semantic_convention_ids=convention_ids,
                        statement_map=statement_map,
                        source_proof_fidelity=source_proof_fidelity,
                        status=status,
                        administrative_projection_rebind=administrative_projection_rebind,
                        source_item_semantic_sha256_by_key=(
                            source_item_semantic_sha256_by_key
                        ),
                        current_source_disposition_keys=current_source_disposition_keys,
                        current_source_correction_identities=(
                            source_correction_identities
                        ),
                        current_component_sha256s_by_source_judgment_key=(
                            component_occurrences
                        ),
                        current_source_claim_atom_receipts=atom_receipts,
                        require_source_claim_atom=require_source_claim_atoms,
                    )
                    for field_key in closure
                )
            else:
                closure_completion_is_safe = (
                    _current_v10_record_field_closure_completion_is_safe(
                        closure_completion_candidates,
                        semantic_key=semantic_key,
                        semantic_identity=semantic_identity,
                        semantic_signatures=semantic_signatures,
                        raw_association_sha256=raw_association_sha256,
                        root=root,
                        binder_names=binder_names,
                        closure=closure,
                        semantic_judgment=semantic_judgment,
                        judgments=judgments,
                        recursive_field_components=recursive_field_components,
                    )
                )
                unsafe_field = not closure_completion_is_safe and any(
                    not isinstance(judgments.get(field_key), Mapping)
                    or not _legacy_semantic_model_field_is_safe(
                        field_items[field_key],
                        judgments[field_key],
                        raw_semantic_parent_association=raw_association,
                        semantic_association_sha256=association_sha256,
                        semantic_convention_ids=convention_ids,
                        statement_map=statement_map,
                        source_proof_fidelity=source_proof_fidelity,
                        status=status,
                        administrative_projection_rebind=administrative_projection_rebind,
                    )
                    for field_key in closure
                )
            if unsafe_field:
                continue
            candidate_bindings.append(
                SemanticModelRecordBinding(
                    declaration_identity=semantic_identity,
                    elaborated_signatures=semantic_signatures,
                    record_root=root,
                    binder_names=binder_names,
                    binder_atom_identities=(
                        binder_atom_identities or ()
                    ),
                    fully_qualified_expanded_record_type=(
                        fully_qualified_expanded_record_type
                    ),
                    resolved_structure_alias_identity=(
                        resolved_structure_alias_identity
                    ),
                    field_keys=closure,
                    source_model_judgment_key=semantic_key,
                    legacy_compatibility=not strict_component_contract,
                    transparent_spec_parent_receipt=(
                        transparent_spec_parent_receipt
                    ),
                )
            )

    # A duplicate parent match is ambiguous. Retain only bindings that are
    # unique by the exact generated dependency identity, never by its label.
    def uniqueness_key(binding: SemanticModelRecordBinding) -> tuple[object, ...]:
        binder_identity: object = (
            binding.binder_names
            if binding.legacy_compatibility
            else (
                binding.binder_atom_identities,
                binding.fully_qualified_expanded_record_type,
                binding.resolved_structure_alias_identity,
            )
        )
        return (
            binding.declaration_identity,
            binding.elaborated_signatures,
            binding.record_root,
            binder_identity,
        )

    counts: dict[tuple[object, ...], int] = {}
    for binding in candidate_bindings:
        key = uniqueness_key(binding)
        counts[key] = counts.get(key, 0) + 1
    return tuple(
        binding
        for binding in candidate_bindings
        if counts[uniqueness_key(binding)] == 1
    )


def _canonical_semantic_receipt_json(value: object) -> str | None:
    """Canonicalize generated semantic evidence without interpreting names."""

    try:
        return json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    except (TypeError, ValueError):
        return None


def _validated_transparent_spec_semantic_parent_receipt(
    item: Mapping[str, Any],
) -> TransparentSpecSemanticParentReceipt | None:
    """Authenticate one current generated direct-evidence/Spec pair.

    The source-record generator already owns the structural pair validator.
    This consumer reuses it, then retains the exact identities and proposition
    surface needed to join a later transparent-Spec occurrence.  The extra
    digest checks make the receipt self-contained for conclusion projection.
    """

    identity = _reviewed_declaration_identity(dict(item))
    if identity is None:
        return None
    direct_declaration, direct_declaration_sha = identity
    qualified_declaration = str(item.get("qualified_declaration") or "").strip()
    signatures = _elaborated_signature_identities(
        dict(item), declaration=direct_declaration
    )
    if qualified_declaration != direct_declaration or not signatures or len(signatures) != 1:
        return None
    direct_signature = next(iter(signatures))

    # Import lazily: audit_repository invokes this module from two late audit
    # lanes, so a module-level import would create a circular initialization.
    try:
        from scripts.audit_repository import semantic_model_item_exact_receipt_identity
    except ModuleNotFoundError:  # pragma: no cover - direct-script imports.
        from audit_repository import semantic_model_item_exact_receipt_identity

    if semantic_model_item_exact_receipt_identity(
        item, qualified_declaration=direct_declaration
    ) != (direct_declaration_sha, direct_signature[1]):
        return None

    semantic_key = str(item.get("judgment_key") or "").strip()
    group = item.get("semantic_contract_group")
    association = item.get("semantic_contract_source_association")
    if (
        not semantic_key
        or not isinstance(group, Mapping)
        or not isinstance(association, Mapping)
    ):
        return None

    raw_members = group.get("member_rows")
    if not isinstance(raw_members, list) or len(raw_members) != 2:
        return None
    members: dict[str, tuple[str, str]] = {}
    for raw_member in raw_members:
        if not isinstance(raw_member, Mapping):
            return None
        role = str(raw_member.get("role") or "").strip()
        member_identity = _reviewed_declaration_identity(dict(raw_member))
        if role in members or member_identity is None:
            return None
        if str(raw_member.get("qualified_declaration") or "").strip() != member_identity[0]:
            return None
        members[role] = member_identity
    if set(members) != {"direct_evidence", "transparent_spec"}:
        return None
    if members["direct_evidence"] != identity:
        return None
    spec_identity = members["transparent_spec"]
    if spec_identity[0] == direct_declaration:
        return None

    direct_surface = group.get("direct_evidence_type")
    spec_surface = group.get("surface_root")
    if not isinstance(direct_surface, Mapping) or not isinstance(spec_surface, Mapping):
        return None
    alpha_surface = direct_surface.get("structural_alpha_normalized_surface")
    if (
        group.get("schema") != 1
        or group.get("structural_alpha_normalized_equal") is not True
        or str(direct_surface.get("qualified_declaration") or "").strip()
        != direct_declaration
        or str(spec_surface.get("kind") or "").strip()
        != "transparent_spec_body"
        or str(spec_surface.get("qualified_declaration") or "").strip()
        != spec_identity[0]
        or not isinstance(alpha_surface, Mapping)
        or spec_surface.get("structural_alpha_normalized_surface") != alpha_surface
    ):
        return None

    group_source_identities = group.get("source_item_identities")
    association_source_identities = association.get("source_item_identities")
    group_source_json = _canonical_semantic_receipt_json(group_source_identities)
    association_source_json = _canonical_semantic_receipt_json(
        association_source_identities
    )
    if (
        not isinstance(group_source_identities, list)
        or not group_source_identities
        or group_source_json is None
        or group_source_json != association_source_json
    ):
        return None

    source_keys: set[str] = set()
    source_semantic_sha256s: list[str] = []
    for raw_source_identity in group_source_identities:
        if not isinstance(raw_source_identity, Mapping):
            return None
        source_key = str(raw_source_identity.get("source_key") or "").strip()
        semantic_contract = raw_source_identity.get("semantic_contract")
        source_map_sha = _sha256_value(
            raw_source_identity.get("source_map_item_sha256")
        )
        source_semantic_sha = _sha256_value(
            raw_source_identity.get("source_semantic_sha256")
        )
        if (
            not source_key
            or source_key in source_keys
            or source_map_sha is None
            or source_semantic_sha is None
            or not isinstance(semantic_contract, Mapping)
            or str(semantic_contract.get("evidence_declaration") or "").strip()
            != direct_declaration
            or str(semantic_contract.get("spec_declaration") or "").strip()
            != spec_identity[0]
            or str(semantic_contract.get("evidence_mode") or "").strip()
            != "proves"
            or not str(semantic_contract.get("semantic_shape") or "").strip()
        ):
            return None
        source_keys.add(source_key)
        source_semantic_sha256s.append(source_semantic_sha)

    association_identity = _reviewed_declaration_identity(dict(association))
    association_signature = _association_signature_identity(
        association.get("reviewed_elaborated_signature_identity"),
        declaration=direct_declaration,
    )
    if (
        association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA
        or str(association.get("role") or "").strip() != "direct_evidence"
        or str(association.get("paired_qualified_declaration") or "").strip()
        != spec_identity[0]
        or association_identity != identity
        or association_signature != direct_signature
        or _sha256_value(association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD))
        != semantic_association_record_digest(
            source_semantic_sha256s,
            association.get("reviewed_elaborated_signature_identity"),
        )
    ):
        return None

    alpha_surface_json = _canonical_semantic_receipt_json(alpha_surface)
    if alpha_surface_json is None:
        return None
    return TransparentSpecSemanticParentReceipt(
        semantic_model_judgment_key=semantic_key,
        evidence_declaration_identity=identity,
        evidence_elaborated_signature_identity=direct_signature,
        spec_declaration_identity=spec_identity,
        alpha_normalized_surface_json=alpha_surface_json,
        source_item_identities_json=group_source_json,
    )


def validated_transparent_spec_semantic_parent_route(
    item: Mapping[str, Any],
    parent_receipt: TransparentSpecSemanticParentReceipt | None,
) -> TransparentSpecSemanticParentRoute | None:
    """Resolve one exact transparent-Spec/evidence semantic-model route.

    This consumes only the generator-owned schema-2 association, exact
    declaration/signature identities, source-item identities, and their
    recomputed digests. A Spec suffix, row label, or declaration-name pattern
    is never an acceptance condition.
    """

    identity = _reviewed_declaration_identity(dict(item))
    if identity is None or parent_receipt is None:
        return None
    spec_declaration, _spec_sha = identity
    if identity != parent_receipt.spec_declaration_identity:
        return None
    signature = _unique_elaborated_signature_identity(
        item,
        declaration=spec_declaration,
        allow_aggregate=(
            _generated_result_certificate_allows_aggregate_signatures(
                item,
                section=str(item.get("source_component_section") or "").strip(),
            )
        ),
    )
    association = item.get("source_contract_association")
    if not isinstance(association, Mapping):
        return None
    if (
        association.get("schema") != SEMANTIC_ASSOCIATION_SCHEMA
        or association.get("association_mode")
        != "semantic_contract_group_member"
        or association.get("semantic_contract_member_role")
        != "transparent_spec"
        or _sha256_value(association.get("association_sha256"))
        != source_contract_association_record_digest(association)
        or _reviewed_declaration_identity(dict(association)) != identity
    ):
        return None
    association_signature = _association_signature_identity(
        association.get("reviewed_elaborated_signature_identity"),
        declaration=spec_declaration,
    )
    if (
        association_signature is None
        or signature != association_signature
    ):
        return None

    raw_source_identities = association.get("source_item_identities")
    if not isinstance(raw_source_identities, list) or not raw_source_identities:
        return None
    if (
        _canonical_semantic_receipt_json(raw_source_identities)
        != parent_receipt.source_item_identities_json
    ):
        return None
    source_keys: set[str] = set()
    source_map_sha256_by_key: dict[str, str] = {}
    source_semantic_sha256s: list[str] = []
    evidence_declarations: set[str] = set()
    for raw_identity in raw_source_identities:
        if not isinstance(raw_identity, Mapping):
            return None
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_map_sha = _sha256_value(raw_identity.get("source_map_item_sha256"))
        source_semantic_sha = _sha256_value(
            raw_identity.get("source_semantic_sha256")
        )
        semantic_contract = raw_identity.get("semantic_contract")
        if (
            not source_key
            or source_key in source_keys
            or source_map_sha is None
            or source_semantic_sha is None
            or source_semantic_sha in source_semantic_sha256s
            or not isinstance(semantic_contract, Mapping)
            or str(semantic_contract.get("spec_declaration") or "").strip()
            != spec_declaration
            or str(semantic_contract.get("evidence_declaration") or "").strip()
            != parent_receipt.evidence_declaration_identity[0]
            or str(semantic_contract.get("evidence_mode") or "").strip()
            != "proves"
            or not str(semantic_contract.get("semantic_shape") or "").strip()
        ):
            return None
        evidence_declaration = str(
            semantic_contract.get("evidence_declaration") or ""
        ).strip()
        if not evidence_declaration:
            return None
        source_keys.add(source_key)
        source_map_sha256_by_key[source_key] = source_map_sha
        source_semantic_sha256s.append(source_semantic_sha)
        evidence_declarations.add(evidence_declaration)
    if len(evidence_declarations) != 1:
        return None
    raw_source_keys = association.get("source_map_item_keys")
    raw_source_map_sha256_by_key = association.get(
        "source_map_item_sha256_by_key"
    )
    if (
        not isinstance(raw_source_keys, list)
        or [str(value).strip() for value in raw_source_keys]
        != sorted(source_keys)
        or not isinstance(raw_source_map_sha256_by_key, Mapping)
        or {
            str(key).strip(): str(value).strip().lower()
            for key, value in raw_source_map_sha256_by_key.items()
        }
        != source_map_sha256_by_key
        or _sha256_value(association.get("source_map_item_keys_sha256"))
        != source_map_item_record_digest(sorted(source_keys))
        or _sha256_value(association.get(SEMANTIC_ASSOCIATION_SHA256_FIELD))
        != semantic_association_record_digest(
            source_semantic_sha256s,
            association.get("reviewed_elaborated_signature_identity"),
        )
    ):
        return None
    semantic_key = str(
        association.get("semantic_model_judgment_key") or ""
    ).strip()
    if semantic_key != parent_receipt.semantic_model_judgment_key:
        return None
    if evidence_declarations != {
        parent_receipt.evidence_declaration_identity[0]
    }:
        return None
    return TransparentSpecSemanticParentRoute(
        semantic_model_judgment_key=semantic_key,
        evidence_declaration=parent_receipt.evidence_declaration_identity[0],
    )


def dependency_has_complete_semantic_model_record_binding(
    item: Mapping[str, Any], bindings: tuple[SemanticModelRecordBinding, ...]
) -> bool:
    """Match a caller record to exactly one complete semantic-model binding.

    The binding is already built from the generic per-field source/Lean
    closure gate.  Do not reintroduce an acceptance condition based on whether
    a field happens to look unrelated to the row result: that relationship is
    useful diagnostic context, not evidence that a caller-supplied model was
    constructed from primitives.
    """

    identity = _reviewed_declaration_identity(dict(item))
    if identity is None:
        return False
    signatures = _elaborated_signature_identities(
        dict(item), declaration=identity[0]
    )
    record = str(item.get("record") or "").strip()
    binder_names = _generated_dependency_binder_names(item)
    binder_atom_identities = _generated_binder_atom_identities(
        item.get("elaborated_outer_binder_atoms")
    )
    fully_qualified_expanded_record_type = str(
        item.get("fully_qualified_expanded_binder_type_canonical") or ""
    ).strip()
    if not signatures or not record:
        return False
    matches = [
        binding
        for binding in bindings
        if (
            (
                binding.declaration_identity == identity
                and binding.elaborated_signatures == signatures
            )
            or (
                (
                    transparent_parent := (
                        validated_transparent_spec_semantic_parent_route(
                            item, binding.transparent_spec_parent_receipt
                        )
                    )
                )
                is not None
                and transparent_parent.semantic_model_judgment_key
                == binding.source_model_judgment_key
                and transparent_parent.evidence_declaration
                == binding.declaration_identity[0]
            )
        )
        and binding.record_root == record
        and (
            (
                binding.legacy_compatibility
                and bool(binder_names)
                and binding.binder_names == binder_names
            )
            or (
                not binding.legacy_compatibility
                and binder_atom_identities is not None
                and binding.binder_atom_identities == binder_atom_identities
                and (
                    (
                        binding.resolved_structure_alias_identity is None
                        and binding.fully_qualified_expanded_record_type
                        == fully_qualified_expanded_record_type
                        and _fully_qualified_expanded_record_type_has_root(
                            fully_qualified_expanded_record_type, record
                        )
                    )
                    or (
                        binding.resolved_structure_alias_identity is not None
                        and fully_qualified_expanded_record_type == ""
                        and isinstance(item.get("record_aliases"), list)
                        and {
                            str(value).strip()
                            for value in item.get("record_aliases") or []
                            if "." in str(value).strip()
                        }
                        == {binding.resolved_structure_alias_identity[0]}
                    )
                )
            )
        )
    ]
    if len(matches) != 1:
        return False
    binding = matches[0]
    if binding.legacy_compatibility:
        # Preserve the historical record-result boundary for v10 artifacts.
        # Schema-1 bindings never consult this shape classification.
        if not record_input_is_nonresult_source_model_or_data(dict(item)):
            return False
        if item.get("rejected_constructors") or item.get("conditional_constructors"):
            return False
    raw_fields = item.get("conclusion_fields")
    if not isinstance(raw_fields, list) or not raw_fields:
        return False
    for raw_field in raw_fields:
        if not isinstance(raw_field, Mapping):
            return False
        key = str(raw_field.get("judgment_key") or raw_field.get("path") or "").strip()
        if not key or key not in binding.field_keys:
            return False
        if binding.legacy_compatibility and (
            raw_field.get("source_antecedent_eligible") is not True
            or str(raw_field.get("relation_to_row_result") or "").strip()
        ):
            return False
    return True


def dependency_has_resolved_constructor(
    item: dict[str, Any],
    exact_antecedent_keys: set[str],
    judgments: dict[str, dict[str, Any]],
) -> bool:
    """Accept a non-record route only through a checked sidecar projection.

    A constructor that returns a fresh record of the same type cannot identify
    an arbitrary record supplied to the reviewed theorem by its caller.
    """

    if item.get("kind") == "record_conclusion_input":
        return False
    if item.get("valid_constructors"):
        return True
    key = str(item.get("judgment_key") or "").strip()
    return checked_projection_result(
        item,
        judgments.get(key),
        exact_antecedent_keys,
    ).accepted


def dependency_checked_projection_result(
    item: dict[str, Any],
    exact_antecedent_keys: set[str],
    judgments: dict[str, dict[str, Any]],
) -> CheckedProjectionResult:
    """Return the structural sidecar-contract verdict for one dependency."""

    key = str(item.get("judgment_key") or "").strip()
    return checked_projection_result(
        item,
        judgments.get(key),
        exact_antecedent_keys,
    )


def local_reducible_input_is_exact_source_antecedent(
    item: dict[str, Any], exact_antecedent_keys: set[str]
) -> bool:
    """Permit a fail-closed local wrapper only with current exact source evidence."""

    if item.get("kind") != "unexpanded_local_reducible_type_input":
        return False
    key = str(item.get("judgment_key") or "").strip()
    return bool(key and key in exact_antecedent_keys)


def conclusion_input_is_exact_source_antecedent(
    item: dict[str, Any],
    exact_antecedent_keys: set[str],
    *,
    judgments: Mapping[str, Mapping[str, Any]] | None = None,
) -> bool:
    """Permit exact source antecedents without relying on declaration names."""

    if item.get("conclusion_fields"):
        return False
    if item.get("kind") not in {
        "aliased_conclusion_bridge_input",
        "bool_certificate_input",
        "direct_conclusion_input",
        "selector_certificate_input",
        "unexpanded_local_reducible_type_input",
    }:
        return False
    key = str(item.get("judgment_key") or "").strip()
    return bool(key and key in exact_antecedent_keys)


def conclusion_input_is_accepted_source_antecedent(
    item: dict[str, Any],
    exact_antecedent_keys: set[str],
    data_antecedent_keys: set[str],
    approved_source_convention_keys: set[str] | None = None,
    *,
    strict_realization: bool = False,
    judgments: Mapping[str, Mapping[str, Any]] | None = None,
) -> bool:
    """Read legacy antecedent receipts or enforce the schema-1 rule.

    The category-bearing branch is retained only to render/check existing v10
    evidence. Schema-1 callers set ``strict_realization`` and accept no data,
    domain, or convention shortcut; those components must use the
    occurrence-bound contract gate.
    """

    if strict_realization:
        return conclusion_input_is_exact_source_antecedent(item, exact_antecedent_keys)
    if item.get("conclusion_fields"):
        return False
    if item.get("kind") == "transparent_subtype_domain_input":
        return transparent_subtype_domain_input_is_accepted_source_data(
            item, data_antecedent_keys
        )
    if item.get("kind") not in {
        "aliased_conclusion_bridge_input",
        "bool_certificate_input",
        "direct_conclusion_input",
        "selector_certificate_input",
        "unexpanded_local_reducible_type_input",
    }:
        return False
    key = str(item.get("judgment_key") or "").strip()
    return bool(
        key
        and (
            key in exact_antecedent_keys
            or key in data_antecedent_keys
            or key in (approved_source_convention_keys or set())
        )
    )


def record_input_is_nonresult_source_model_or_data(item: dict[str, Any]) -> bool:
    """Whether a record input is semantic model/data, not a result package.

    The source-record helper expands the record and computes each field's
    relation to the reviewed row result from type shape.  A record with only
    source-antecedent-eligible fields that have no relation to that result is
    an assumed model/data carrier. It is not evidence that the theorem smuggles
    in its own conclusion, but its fields still require current source-record
    provenance or a checked constructor before this standalone audit can pass.

    This deliberately consults neither declaration, binder, record, nor field
    spelling.  Any field related to the row result, or one that is not marked
    as a source antecedent, keeps the record in the conclusion-provenance
    failure path.
    """

    if item.get("kind") != "record_conclusion_input":
        return False
    if not str(item.get("record") or "").strip():
        return False
    raw_fields = item.get("conclusion_fields")
    if not isinstance(raw_fields, list) or not raw_fields:
        return False
    for raw_field in raw_fields:
        if not isinstance(raw_field, dict):
            return False
        if raw_field.get("source_antecedent_eligible") is not True:
            return False
        if str(raw_field.get("relation_to_row_result") or "").strip():
            return False
    return True


def unresolved_dependency_field_keys(
    item: dict[str, Any],
    exact_antecedent_keys: set[str],
    data_antecedent_keys: set[str] | None = None,
    approved_source_convention_field_keys: set[str] | None = None,
    *,
    strict_realization: bool = False,
) -> tuple[str, ...]:
    """Return legacy unresolved fields or strict occurrence-gate diagnostics.

    Domain/model correspondence is checked by the occurrence-level component
    ledger, rather than by silently omitting a non-proposition field here.
    """

    if not strict_realization:
        data_antecedent_keys = data_antecedent_keys or set()
        keys: list[str] = []
        for field in item.get("conclusion_fields") or []:
            if not isinstance(field, dict):
                continue
            key = str(field.get("judgment_key") or field.get("path") or "").strip()
            if not key:
                continue
            if field.get("source_antecedent_eligible") and key in exact_antecedent_keys:
                continue
            if (
                field.get("source_antecedent_eligible")
                and not str(field.get("relation_to_row_result") or "").strip()
                and key in (approved_source_convention_field_keys or set())
            ):
                continue
            semantic_kind = str(field.get("semantic_kind") or "").strip()
            if (
                field.get("source_antecedent_eligible")
                and semantic_kind != "proposition"
                and key in data_antecedent_keys
            ):
                continue
            keys.append(key)
        return tuple(keys)

    _ = data_antecedent_keys, approved_source_convention_field_keys
    keys: list[str] = []
    for field in item.get("conclusion_fields") or []:
        if not isinstance(field, dict):
            continue
        key = str(field.get("judgment_key") or field.get("path") or "").strip()
        if not key:
            continue
        if field.get("source_antecedent_eligible") and key in exact_antecedent_keys:
            continue
        keys.append(key)
    return tuple(keys)


def missing_configured_row_findings(
    paper: str, audit_payload: dict[str, Any]
) -> list[Finding]:
    """Fail closed when a configured review row is absent from parsed Lean source."""

    return [
        Finding(
            paper,
            str(row),
            "<configured row>",
            (),
            "configured review row was not found in the review or assumption "
            "Lean source; audit coverage is incomplete",
        )
        for row in audit_payload.get("missing_configured_review_rows") or []
        if isinstance(row, str) and row.strip()
    ]


def reachable_paper_interface_auxiliary_findings(
    paper: str,
    audit_payload: dict[str, Any],
    *,
    folder: Path | None = None,
    routing_context_override: object = _CONTEXT_OVERRIDE_UNSET,
    routing_context_error_override: str | None = None,
) -> list[Finding]:
    """Fail closed on hidden PaperInterface helpers reached by reviewed rows.

    The generator binds the reachability ledger to Lean-elaborated dependency
    evidence and exact fully-qualified source-map routes. This standalone gate
    must enforce the same rule as the repository closeout path; otherwise a
    helper placed in ``auxiliary_names`` could disappear from one audit entry
    point while still influencing a selected theorem or selected assumption.
    """

    # This guard is part of the current v10 generated surface. Legacy
    # diagnostic fixtures retain their historical behavior; a real v10 helper
    # run always emits the ledger below before this gate considers it current.
    prompt_version = str(audit_payload.get("prompt_version") or "").strip()
    if prompt_version and prompt_version != SOURCE_RECORD_PROMPT_VERSION:
        return []
    if folder is None or str(audit_payload.get("paper") or "").strip() != paper:
        # Standalone legacy fixtures and pre-v10 diagnostic payloads have no
        # canonical raw identity from which a supplement can be authenticated.
        # Production v10 evidence always names its paper and uses the shared
        # context below.
        ledger_keys = (
            "reachable_paper_interface_auxiliary_dependencies",
            "unresolved_reachable_paper_interface_auxiliaries",
            "ambiguous_reachable_paper_interface_auxiliary_references",
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors",
        )
        missing = [key for key in ledger_keys if key not in audit_payload]
        if missing:
            return [
                Finding(
                    paper,
                    "<reachable PaperInterface auxiliary>",
                    "<source-record routing ledger>",
                    (),
                    "current source-record audit lacks required reachable-auxiliary "
                    "routing field(s): "
                    + ", ".join(missing),
                )
            ]
        quarantine_configuration_errors = tuple(
            str(error).strip()
            for error in audit_payload.get(
                "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
            )
            or []
            if str(error).strip()
        )
        unresolved_auxiliaries = tuple(
            item
            for item in audit_payload.get(
                "unresolved_reachable_paper_interface_auxiliaries"
            )
            or []
            if isinstance(item, dict)
        )
        ambiguous_auxiliary_references = tuple(
            item
            for item in audit_payload.get(
                "ambiguous_reachable_paper_interface_auxiliary_references"
            )
            or []
            if isinstance(item, dict)
        )
    else:
        if routing_context_override is _CONTEXT_OVERRIDE_UNSET:
            routing_context, context_error = current_auxiliary_routing_context(
                root=ROOT,
                paper_dir=folder,
                paper=paper,
                audit_payload=audit_payload,
            )
        else:
            routing_context = (
                routing_context_override
                if isinstance(
                    routing_context_override,
                    ValidatedAuxiliaryRoutingContext,
                )
                else None
            )
            context_error = str(routing_context_error_override or "")
        if routing_context is None:
            return [
                Finding(
                    paper,
                    "<reachable PaperInterface auxiliary>",
                    "<source-record routing ledger>",
                    (),
                    "current source-record reachable-auxiliary routing evidence "
                    "is unavailable: "
                    + (context_error or "unknown validation error"),
                )
            ]
        # A routing supplement only authenticates the reachability ledger. It
        # cannot create source/proof credit or revive a lexical closure route.
        (
            augmented_payload,
            augmented_payload_error,
        ) = routing_context.audit_payload_with_authenticated_ledger(audit_payload)
        if augmented_payload is None:
            return [
                Finding(
                    paper,
                    "<reachable PaperInterface auxiliary>",
                    "<source-record routing ledger>",
                    (),
                    "current source-record reachable-auxiliary routing evidence "
                    "cannot be bound to the raw audit: "
                    + (augmented_payload_error or "unknown validation error"),
                )
            ]
        quarantine_configuration_errors = (
            routing_context.quarantine_configuration_errors()
        )
        unresolved_auxiliaries = routing_context.unresolved_auxiliaries()
        ambiguous_auxiliary_references = routing_context.ambiguous_references()

    findings: list[Finding] = []
    for error in quarantine_configuration_errors:
        if not str(error).strip():
            continue
        findings.append(
            Finding(
                paper,
                "<reachable PaperInterface auxiliary>",
                "<quarantine configuration>",
                (),
                "invalid source reason for a reachable quarantined auxiliary: "
                + str(error).strip(),
            )
        )
    for item in unresolved_auxiliaries:
        declaration = str(item.get("declaration") or "unknown declaration").strip()
        disposition = str(item.get("disposition") or "unresolved").strip()
        findings.append(
            Finding(
                paper,
                declaration,
                "<transitive auxiliary dependency>",
                (),
                "selected review roots reach this PaperInterface auxiliary without "
                "an exact fully-qualified source-map route/support or an explicit "
                f"quarantine source reason ({disposition}); Lean's elaborated dependency "
                "graph discovers reachability, while separate derivational or lexical "
                "receipts are diagnostic-only",
            )
        )
    for item in ambiguous_auxiliary_references:
        candidates = tuple(
            sorted(
                str(candidate).strip()
                for candidate in item.get("candidate_auxiliaries") or []
                if str(candidate).strip()
            )
        )
        findings.append(
            Finding(
                paper,
                "<ambiguous transitive auxiliary reference>",
                "<source-record routing ledger>",
                candidates,
                "a selected review root has an ambiguous local reference that may "
                "target a PaperInterface auxiliary; qualify it before assigning "
                "source-map support or a quarantine reason",
            )
        )
    return findings


def omitted_direct_dependency_findings(
    paper: str, audit_payload: dict[str, Any]
) -> list[Finding]:
    """Fail closed if the helper relates a premise to the result but omits it.

    This is deliberately redundant with the helper's dependency construction.
    The command-line gate must not silently pass merely because a future helper
    refactor records a semantic result relation only on the boundary surface.
    """

    dependency_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in audit_payload.get("conclusion_dependency_items") or []
        if isinstance(item, dict)
    }
    findings: list[Finding] = []
    canonical_items = audit_payload.get("theorem_facing_input_items")
    input_items = (
        canonical_items
        if isinstance(canonical_items, list)
        else audit_payload.get("boundary_input_items") or []
    )
    for item in input_items:
        if not isinstance(item, dict):
            continue
        relation = str(item.get("result_relation") or "").strip()
        key = str(item.get("judgment_key") or "").strip()
        if not relation or not key or key in dependency_keys:
            continue
        raw_input = item.get("input")
        visible_input = raw_input if isinstance(raw_input, dict) else {}
        findings.append(
            Finding(
                paper,
                str(item.get("row") or "unknown row"),
                str(visible_input.get("names") or "unknown binder"),
                (),
                "source-record helper omitted a premise with semantic result "
                f"relation `{relation}` from conclusion_dependency_items",
            )
        )
    return findings


def source_premise_false_eliminator_findings(
    paper: str,
    audit_payload: dict[str, Any],
    *,
    status_payload_override: Mapping[str, Any] | None = None,
) -> list[Finding]:
    """Reject full closeout when a reviewed source input directly entails False."""

    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(PAPERS / paper / "status.json") or {}
    )
    status = str(status_payload.get("status") or "").strip().lower()
    if status not in FULLY_FORMALIZED_STATUSES:
        return []
    if audit_payload.get("source_premise_consistency_schema") != 1:
        return []
    error = str(audit_payload.get("source_premise_consistency_error") or "").strip()
    if error:
        return [
            Finding(
                paper,
                "<source premise>",
                "<elaborated consistency scan>",
                (),
                "source-premise consistency scan did not complete: " + error,
            )
        ]
    raw_items = audit_payload.get("source_premise_consistency_items")
    if not isinstance(raw_items, list):
        return [
            Finding(
                paper,
                "<source premise>",
                "<elaborated consistency scan>",
                (),
                "source-premise consistency schema is present but its result list is "
                "missing or malformed",
            )
        ]
    findings: list[Finding] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, dict):
            findings.append(
                Finding(
                    paper,
                    "<source premise>",
                    "<elaborated consistency scan>",
                    (),
                    "source-premise consistency result contains a malformed item",
                )
            )
            continue
        reviewed = str(raw_item.get("reviewed_input_type") or "").strip()
        direct = raw_item.get("direct_eliminators")
        if not reviewed or not isinstance(direct, list):
            findings.append(
                Finding(
                    paper,
                    "<source premise>",
                    "<elaborated consistency scan>",
                    (),
                    "source-premise consistency item lacks a reviewed input or direct "
                    "eliminator list",
                )
            )
            continue
        names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in direct
                if isinstance(candidate, dict)
                and candidate.get("direct_eliminator") is True
                and str(candidate.get("candidate") or "").strip()
            }
        )
        if names:
            findings.append(
                Finding(
                    paper,
                    "<source premise>",
                    reviewed,
                    (),
                    "Lean elaboration found a direct route from this reviewed source "
                    "input to False via "
                    + ", ".join(names[:4])
                    + ("; ..." if len(names) > 4 else "")
                    + ". A full formalization claim cannot rely on an inconsistent "
                    "source-model premise.",
                )
            )
    return findings


def _unique_nonempty_strings(value: object) -> tuple[str, ...] | None:
    """Normalize a declared string list without accepting implicit duplicates."""

    if not isinstance(value, list):
        return None
    if any(not isinstance(entry, str) for entry in value):
        return None
    values = tuple(entry.strip() for entry in value)
    if not values or any(not entry for entry in values) or len(set(values)) != len(values):
        return None
    return tuple(sorted(values))


def _paper_local_contract_path(folder: Path, raw_path: object) -> Path | None:
    """Resolve a corrected-contract path without permitting a scope escape."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if candidate.is_absolute():
        return None
    try:
        resolved_folder = folder.resolve()
        resolved = (folder / candidate).resolve()
        resolved.relative_to(resolved_folder)
    except (OSError, RuntimeError, ValueError):
        return None
    return resolved


def _current_corrected_contract(
    folder: Path,
    status_payload: dict[str, Any],
    audit_payload: dict[str, Any],
    *,
    corrected_scope_current: bool | None = None,
    input_raw_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> tuple[dict[str, Any], dict[str, Any]] | None:
    """Return a contract only when it also pins this fresh helper payload.

    ``author_approved_corrected_scope_contract_is_current`` validates the
    canonical artifact used by the evidence gate.  The conclusion-provenance
    gate deliberately scans into a temporary file, so it must additionally
    bind that fresh payload to the same contract receipts and scope.  Otherwise
    a current checked-in contract could suppress a dependency discovered after
    the source scan changed.
    """

    if str(audit_payload.get("prompt_version") or "").strip() != (
        SOURCE_RECORD_PROMPT_VERSION
    ):
        return None
    if corrected_scope_current is False or (
        corrected_scope_current is None
        and not author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    ):
        return None
    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return None
    target_declarations = _unique_nonempty_strings(
        scope.get("target_result_declarations")
    )
    correction_ids = _unique_nonempty_strings(scope.get("correction_ids"))
    if target_declarations is None or correction_ids is None:
        return None
    scope_model_bindings, scope_model_binding_errors = (
        corrected_model_scope_model_bindings(
            scope,
            target_result_declarations=list(target_declarations),
        )
    )
    if scope_model_binding_errors or scope_model_bindings is None:
        return None
    contract_ref = scope.get("semantic_contract")
    if not isinstance(contract_ref, dict):
        return None
    contract_path = _paper_local_contract_path(folder, contract_ref.get("path"))
    expected_contract_digest = str(contract_ref.get("sha256") or "").strip().lower()
    if contract_path is None or not contract_path.is_file() or len(expected_contract_digest) != 64:
        return None
    if input_raw_bytes_override is not None:
        try:
            contract_raw = input_raw_bytes_override[contract_path.resolve()]
        except (KeyError, OSError, RuntimeError):
            return None
        if not isinstance(contract_raw, bytes):
            return None
    else:
        try:
            contract_raw = contract_path.read_bytes()
        except OSError:
            return None
    contract_digest = hashlib.sha256(contract_raw).hexdigest()
    if contract_digest != expected_contract_digest:
        return None
    try:
        contract = json.loads(contract_raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(contract, dict):
        return None

    audit_scope = audit_payload.get("formalization_scope")
    if not isinstance(audit_scope, dict):
        return None
    expected_scope_values = {
        "kind": scope.get("kind"),
        "scope_id": scope.get("scope_id"),
    }
    approval = scope.get("approval")
    base_archive = scope.get("base_archive")
    if not isinstance(approval, dict) or not isinstance(base_archive, dict):
        return None
    expected_scope_values.update(
        {
            "approval_artifact_sha256": approval.get("artifact_sha256"),
            "base_archive_sha256": base_archive.get("sha256"),
        }
    )
    for key, expected in expected_scope_values.items():
        if str(audit_scope.get(key) or "").strip() != str(expected or "").strip():
            return None
    if _unique_nonempty_strings(audit_scope.get("target_result_declarations")) != target_declarations:
        return None
    audit_model_bindings, audit_model_binding_errors = (
        corrected_model_scope_model_bindings(
            audit_scope,
            target_result_declarations=list(target_declarations),
        )
    )
    if (
        audit_model_binding_errors
        or audit_model_bindings is None
        or audit_model_bindings != scope_model_bindings
    ):
        return None
    if _unique_nonempty_strings(audit_scope.get("correction_ids")) != correction_ids:
        return None
    if audit_scope.get("archival_equivalence_claimed") is not False:
        return None

    required_receipts = {
        "source_record_audit_sha256": audit_payload.get("source_record_audit_sha256"),
        "source_record_audit_integrity_sha256": audit_payload.get(
            "source_record_audit_integrity_sha256"
        ),
        "source_record_scope_sha256": audit_scope.get("scope_sha256"),
    }
    if any(not isinstance(value, str) or len(value.strip()) != 64 for value in required_receipts.values()):
        return None
    for key, expected in required_receipts.items():
        if str(contract.get(key) or "").strip() != str(expected).strip():
            return None
    if str(contract.get("scope_id") or "").strip() != str(scope.get("scope_id") or "").strip():
        return None
    if _unique_nonempty_strings(contract.get("target_result_declarations")) != target_declarations:
        return None
    contract_model_bindings, contract_model_binding_errors = (
        corrected_model_scope_model_bindings(
            contract,
            target_result_declarations=list(target_declarations),
        )
    )
    if (
        contract_model_binding_errors
        or contract_model_bindings is None
        or contract_model_bindings != scope_model_bindings
    ):
        return None
    return contract, scope


def corrected_model_conclusion_bridge(
    paper: str,
    audit_payload: dict[str, Any],
    *,
    folder: Path | None = None,
    status_payload_override: Mapping[str, Any] | None = None,
    corrected_scope_current: bool | None = None,
    input_raw_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> CorrectedModelConclusionBridge | None:
    """Build exact current corrected-model provenance coverage for one paper.

    The bridge is intentionally derived from both the current contract and the
    temporary full source-record scan used by this audit.  It does not infer
    coverage from a binder, theorem, or record name.  Every covered row is a
    unique generated semantic item with a matching fully qualified declaration
    and fresh mapping.  Declared corrected targets and explicit assumptions
    must additionally have their dedicated exact mappings; governing-model
    fields must be exhaustively mapped as well.
    """

    folder = folder or PAPERS / paper
    if folder.name != paper:
        return None
    status_payload = (
        status_payload_override
        if status_payload_override is not None
        else load_payload(folder / "status.json")
    )
    if status_payload is None:
        return None
    current = _current_corrected_contract(
        folder,
        status_payload,
        audit_payload,
        corrected_scope_current=corrected_scope_current,
        input_raw_bytes_override=input_raw_bytes_override,
    )
    if current is None:
        return None
    contract, scope = current

    raw_semantic_items = audit_payload.get("semantic_model_items")
    expected_keys = _unique_nonempty_strings(
        audit_payload.get("expected_semantic_model_judgment_keys")
    )
    if not isinstance(raw_semantic_items, list) or expected_keys is None:
        return None
    semantic_by_key: dict[str, dict[str, Any]] = {}
    semantic_by_row: dict[str, dict[str, Any]] = {}
    semantic_by_qualified: dict[str, dict[str, Any]] = {}
    for item in raw_semantic_items:
        if not isinstance(item, dict):
            return None
        key = str(item.get("judgment_key") or "").strip()
        row = str(item.get("row") or "").strip()
        qualified = str(item.get("qualified_declaration") or "").strip()
        if (
            not key
            or not row
            or not qualified
            or key in semantic_by_key
            or row in semantic_by_row
            or qualified in semantic_by_qualified
        ):
            return None
        semantic_by_key[key] = item
        semantic_by_row[row] = item
        semantic_by_qualified[qualified] = item
    if set(semantic_by_key) != set(expected_keys):
        return None
    if _unique_nonempty_strings(contract.get("semantic_item_keys")) != expected_keys:
        return None

    raw_semantic_mappings = contract.get("semantic_item_mappings")
    if not isinstance(raw_semantic_mappings, list):
        return None
    semantic_mapping_by_key: dict[str, dict[str, Any]] = {}
    for mapping in raw_semantic_mappings:
        if not isinstance(mapping, dict):
            return None
        key = str(mapping.get("source_record_item_key") or "").strip()
        item = semantic_by_key.get(key)
        if item is None or key in semantic_mapping_by_key:
            return None
        if str(mapping.get("qualified_declaration") or "").strip() != str(
            item.get("qualified_declaration") or ""
        ).strip():
            return None
        if corrected_model_mapping_freshness_error(mapping, item):
            return None
        semantic_mapping_by_key[key] = mapping
    if set(semantic_mapping_by_key) != set(semantic_by_key):
        return None

    target_declarations = _unique_nonempty_strings(scope.get("target_result_declarations"))
    if target_declarations is None:
        return None
    scope_model_bindings, scope_model_binding_errors = (
        corrected_model_scope_model_bindings(
            scope,
            target_result_declarations=list(target_declarations),
        )
    )
    if scope_model_binding_errors or scope_model_bindings is None:
        return None
    target_model_specs = scope_model_bindings.target_model_spec_declarations
    if set(target_model_specs) != set(target_declarations):
        return None
    raw_target_mappings = contract.get("target_result_mappings")
    if not isinstance(raw_target_mappings, list):
        return None
    target_mapping_by_declaration: dict[str, dict[str, Any]] = {}
    for mapping in raw_target_mappings:
        if not isinstance(mapping, dict):
            return None
        declaration = str(mapping.get("target_declaration") or "").strip()
        item = semantic_by_qualified.get(declaration)
        mapped_model_spec = str(mapping.get("model_spec_declaration") or "").strip()
        if (
            declaration not in target_declarations
            or item is None
            or declaration in target_mapping_by_declaration
            or str(mapping.get("source_record_item_key") or "").strip()
            != str(item.get("judgment_key") or "").strip()
            or (
                mapped_model_spec
                and mapped_model_spec != target_model_specs.get(declaration)
            )
            or (
                not mapped_model_spec
                and not scope_model_bindings.uses_legacy_scalar
            )
            or corrected_model_mapping_freshness_error(mapping, item)
        ):
            return None
        target_mapping_by_declaration[declaration] = mapping
    if set(target_mapping_by_declaration) != set(target_declarations):
        return None

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return None
    raw_assumption_rows = review_surface.get("assumption_names", [])
    if not isinstance(raw_assumption_rows, list):
        return None
    assumption_rows = tuple(str(row).strip() for row in raw_assumption_rows)
    if any(not row for row in assumption_rows) or len(set(assumption_rows)) != len(assumption_rows):
        return None
    expected_assumption_declarations: set[str] = set()
    for row in assumption_rows:
        item = semantic_by_row.get(row)
        if item is None:
            return None
        expected_assumption_declarations.add(
            str(item.get("qualified_declaration") or "").strip()
        )
    raw_assumption_mappings = contract.get("assumption_mappings", [])
    if not isinstance(raw_assumption_mappings, list):
        return None
    assumption_mapping_by_declaration: dict[str, dict[str, Any]] = {}
    for mapping in raw_assumption_mappings:
        if not isinstance(mapping, dict):
            return None
        declaration = str(mapping.get("assumption_declaration") or "").strip()
        item = semantic_by_qualified.get(declaration)
        if (
            declaration not in expected_assumption_declarations
            or item is None
            or declaration in assumption_mapping_by_declaration
            or str(mapping.get("source_record_item_key") or "").strip()
            != str(item.get("judgment_key") or "").strip()
            or corrected_model_mapping_freshness_error(mapping, item)
        ):
            return None
        assumption_mapping_by_declaration[declaration] = mapping
    if set(assumption_mapping_by_declaration) != expected_assumption_declarations:
        return None

    governing_model_fields_by_target: dict[str, dict[str, dict[str, Any]]] = {}
    governing_model_fields: dict[str, dict[str, Any]] = {}
    for declaration in target_declarations:
        model_spec = target_model_specs.get(declaration)
        if not model_spec:
            return None
        fields, field_graph_errors = (
            corrected_model_transitively_reachable_field_items(
                audit_payload,
                model_spec_declaration=model_spec,
                target_result_declarations=[declaration],
            )
        )
        if field_graph_errors or not fields:
            return None
        governing_model_fields_by_target[declaration] = fields
        for key, field in fields.items():
            existing = governing_model_fields.get(key)
            if existing is not None and existing != field:
                return None
            governing_model_fields[key] = field

    raw_model_field_mappings = contract.get("model_field_mappings")
    if not isinstance(raw_model_field_mappings, list) or not raw_model_field_mappings:
        return None
    model_mapping_by_key: dict[str, dict[str, Any]] = {}
    for mapping in raw_model_field_mappings:
        if not isinstance(mapping, dict):
            return None
        key = str(mapping.get("source_record_item_key") or "").strip()
        field = governing_model_fields.get(key)
        if (
            field is None
            or key in model_mapping_by_key
            or corrected_model_mapping_freshness_error(mapping, field)
        ):
            return None
        model_mapping_by_key[key] = mapping
    if set(model_mapping_by_key) != set(governing_model_fields):
        return None

    rows: list[CorrectedModelConclusionRow] = []
    for _row, item in sorted(semantic_by_row.items()):
        declaration_identity = _reviewed_declaration_identity(item)
        if (
            declaration_identity is None
            or declaration_identity[0]
            != str(item.get("qualified_declaration") or "").strip()
        ):
            return None
        signature_identities = _elaborated_signature_identities(
            item,
            declaration=declaration_identity[0],
        )
        if signature_identities is None:
            return None
        declaration = declaration_identity[0]
        target_fields = governing_model_fields_by_target.get(declaration)
        target_model_spec = target_model_specs.get(declaration)
        if target_fields is None or target_model_spec is None:
            # Legacy scalar contracts historically covered their configured
            # semantic support rows as well as the named target. Preserve that
            # behavior only for the single-model form. A multi-model scope has
            # no safe root assignment for a non-target row, so it receives no
            # conclusion-input waiver through this bridge.
            if not scope_model_bindings.uses_legacy_scalar:
                continue
            target_model_spec = scope_model_bindings.model_spec_declarations[0]
            target_fields = governing_model_fields
        rows.append(
            CorrectedModelConclusionRow(
                semantic_model_judgment_key=str(item.get("judgment_key") or "").strip(),
                qualified_declaration=declaration,
                declaration_sha256=declaration_identity[1],
                elaborated_signature_identities=signature_identities,
                governing_model_spec_declaration=target_model_spec,
                governing_model_field_keys=frozenset(target_fields),
                requires_explicit_rooted_field_paths=(
                    not scope_model_bindings.uses_legacy_scalar
                ),
                transparent_spec_parent_receipt=(
                    _validated_transparent_spec_semantic_parent_receipt(item)
                ),
            )
        )
    # A contract cannot waive a declaration whose current semantic item lacks
    # the generator-owned identity. Returning no bridge is more conservative
    # than retaining name-based coverage for only a subset.
    return CorrectedModelConclusionBridge(rows=tuple(rows))


def _transparent_spec_corrected_model_row(
    bridge: CorrectedModelConclusionBridge,
    item: dict[str, Any],
    *,
    declaration_identity: tuple[str, str],
    signature_identities: frozenset[tuple[str, str]],
) -> CorrectedModelConclusionRow | None:
    """Resolve a transparent Spec only through its generated semantic contract.

    A configured evidence theorem can expose the telescope owned by a
    transparent companion ``def``.  In that case the dependency scanner
    correctly pins the Spec declaration while the corrected-model contract
    pins the evidence theorem.  The generated schema-2 association is the
    only bridge between those identities: it binds the exact Spec bytes and
    elaborated signature to one semantic-model item and to the source map's
    exact evidence theorem.  Row labels, suffixes, and declaration spelling
    are deliberately irrelevant.
    """

    if (
        _reviewed_declaration_identity(item) != declaration_identity
        or _elaborated_signature_identities(
            item, declaration=declaration_identity[0]
        )
        != signature_identities
    ):
        return None
    matches = [
        row
        for row in bridge.rows
        if (
            route := validated_transparent_spec_semantic_parent_route(
                item, row.transparent_spec_parent_receipt
            )
        )
        is not None
        and row.semantic_model_judgment_key == route.semantic_model_judgment_key
        and row.qualified_declaration == route.evidence_declaration
    ]
    return matches[0] if len(matches) == 1 else None


def corrected_model_dependency_is_covered(
    bridge: CorrectedModelConclusionBridge | None,
    item: dict[str, Any],
) -> bool:
    """Whether one ordinary model-input provenance finding has exact coverage.

    This purposefully does not waive result-bearing records, Boolean/selector
    proof wrappers, aliases, or any constructor cycle.  The corrected contract
    is a semantic model/target approval route, not a way to turn arbitrary
    conclusion packages into source data.
    """

    if bridge is None:
        return False
    if item.get("kind") != "record_conclusion_input":
        return False
    if item.get("rejected_constructors") or item.get("conditional_constructors"):
        return False
    declaration_identity = _reviewed_declaration_identity(item)
    if declaration_identity is None:
        return False
    declaration, declaration_sha256 = declaration_identity
    signature_identities = _elaborated_signature_identities(
        item,
        declaration=declaration,
    )
    if signature_identities is None:
        return False
    row_matches = [
        coverage
        for coverage in bridge.rows
        if coverage.qualified_declaration == declaration
        and coverage.declaration_sha256 == declaration_sha256
        and coverage.elaborated_signature_identities == signature_identities
    ]
    if len(row_matches) == 1:
        coverage = row_matches[0]
    elif row_matches:
        return False
    else:
        coverage = _transparent_spec_corrected_model_row(
            bridge,
            item,
            declaration_identity=declaration_identity,
            signature_identities=signature_identities,
        )
        if coverage is None:
            return False
    # The corrected target must consume the exact model root assigned to that
    # target.  Matching a covered nested field through a paired or otherwise
    # unrelated record is not a model-boundary waiver.
    if str(item.get("record") or "").strip() != coverage.governing_model_spec_declaration:
        return False
    raw_fields = item.get("conclusion_fields")
    if not isinstance(raw_fields, list):
        return False
    if not raw_fields:
        return False
    for field in raw_fields:
        if not isinstance(field, dict):
            return False
        key = str(field.get("judgment_key") or field.get("path") or "").strip()
        # A row-level semantic mapping reviews the complete target surface,
        # but it does not turn an arbitrary nested or unrelated record into
        # the approved governing model.  The contract validator requires an
        # exact mapping for every field reachable from that model; require the
        # dependency field to be one of those exact mapped fields here.
        if not key or key not in coverage.governing_model_field_keys:
            return False
        raw_path = field.get("path")
        if coverage.requires_explicit_rooted_field_paths:
            if not isinstance(raw_path, str):
                return False
            path_segments = tuple(segment.strip() for segment in raw_path.split(" -> "))
            if (
                len(path_segments) < 2
                or any(not segment for segment in path_segments)
                or path_segments[0] != coverage.governing_model_spec_declaration
                or path_segments[-1] != key
            ):
                return False
        if field.get("source_antecedent_eligible") is not True:
            return False
        if str(field.get("relation_to_row_result") or "").strip():
            return False
    return True


def current_saved_source_record_audit_snapshot(
    paper: str,
) -> SourceRecordAuditSnapshot | None:
    """Load one fingerprint-current canonical snapshot without rescanning Lean.

    The conclusion gate consumes the same generated surface as the source
    record audit.  Re-running that expensive helper after a change limited to
    downstream gates or sidecar metadata cannot add evidence.  Reuse is safe
    only after the canonical receipt independently verifies the current paper
    source/map identity; otherwise callers fall back to a fresh helper run.
    """

    folder = PAPERS / paper
    snapshot = load_source_record_audit_snapshot(
        paper, folder / "audit" / "source_record_audit.json"
    )
    if snapshot is None:
        return None
    payload = snapshot.payload
    if (
        not isinstance(payload, dict)
        or str(payload.get("paper") or "").strip() != paper
        or str(payload.get("prompt_version") or "").strip()
        != SOURCE_RECORD_PROMPT_VERSION
    ):
        return None
    statement_map_sha256 = current_paper_statement_map_sha256(folder)
    identity_error = source_record_audit_identity_error(
        payload,
        expected_paper_statement_map_sha256=statement_map_sha256,
        folder=folder,
    )
    if identity_error:
        return None
    validated = _issued_source_record_audit_snapshot(
        paper=snapshot.paper,
        payload=snapshot.payload,
        source_file_sha256=snapshot.source_file_sha256,
        source_path=snapshot.source_path,
        paper_statement_map_sha256=statement_map_sha256,
        status_payload_override=snapshot.status_payload_override,
        paper_statement_map_override=snapshot.paper_statement_map_override,
        administrative_projection_rebind_override=(
            snapshot.administrative_projection_rebind_override
        ),
        configured_assumption_regularity_context_override=(
            snapshot.configured_assumption_regularity_context_override
        ),
        configured_assumption_regularity_context_error_override=(
            snapshot.configured_assumption_regularity_context_error_override
        ),
        identity_validated=True,
        payload_is_immutable=True,
    )
    if source_record_audit_snapshot_mutation_error(validated):
        return None
    return validated


def current_saved_source_record_audit(paper: str) -> dict[str, Any] | None:
    """Compatibility projection of the exact canonical snapshot payload."""

    snapshot = current_saved_source_record_audit_snapshot(paper)
    return snapshot.payload if snapshot is not None else None


def acquire_source_record_audit_snapshot(
    paper: str,
) -> tuple[SourceRecordAuditSnapshot | None, subprocess.CompletedProcess[str]]:
    """Prefer an exact canonical snapshot; scan only when it is unavailable.

    The cached path intentionally has no temporary JSON transport.  A helper
    fallback still uses its CLI output file, but parses that file exactly once
    before deleting it.
    """

    cached = current_saved_source_record_audit_snapshot(paper)
    if cached is not None:
        return cached, subprocess.CompletedProcess(
            args=[],
            returncode=0,
            stdout="reused fingerprint-current canonical source-record audit",
        )

    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as handle:
        output_path = Path(handle.name)
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(HELPER),
                "--root",
                str(ROOT),
                "--paper",
                paper,
                "--out",
                str(output_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        snapshot = load_source_record_audit_snapshot(paper, output_path)
        if snapshot is not None:
            # The helper process has exited and the exact parsed bytes are now
            # owned by this run.  Do not retain a path that is deleted below.
            snapshot = _issued_source_record_audit_snapshot(
                paper=snapshot.paper,
                payload=snapshot.payload,
                source_file_sha256=snapshot.source_file_sha256,
                source_path=None,
                paper_statement_map_sha256=(
                    snapshot.paper_statement_map_sha256
                ),
                source_record_match_path=snapshot.source_record_match_path,
                source_record_match_sha256=snapshot.source_record_match_sha256,
                current_judgments_override=(
                    snapshot.current_judgments_override
                ),
                status_payload_override=snapshot.status_payload_override,
                paper_statement_map_override=(
                    snapshot.paper_statement_map_override
                ),
                corrected_scope_current_override=(
                    snapshot.corrected_scope_current_override
                ),
                administrative_projection_rebind_override=(
                    snapshot.administrative_projection_rebind_override
                ),
                configured_assumption_regularity_context_override=(
                    snapshot.configured_assumption_regularity_context_override
                ),
                configured_assumption_regularity_context_error_override=(
                    snapshot.configured_assumption_regularity_context_error_override
                ),
                auxiliary_routing_context_override=(
                    snapshot.auxiliary_routing_context_override
                ),
                auxiliary_routing_context_error_override=(
                    snapshot.auxiliary_routing_context_error_override
                ),
                identity_validated=snapshot.identity_validated,
                payload_is_immutable=True,
            )
        return snapshot, proc
    finally:
        try:
            output_path.unlink()
        except FileNotFoundError:
            pass


def _evidence_context_snapshot_for_paper(
    paper: str,
) -> tuple[SourceRecordAuditSnapshot | None, object | None, str]:
    """Acquire the same immutable transaction used by consolidated closeout."""

    try:
        evidence_module = sys.modules.get(
            "scripts.audit_evidence_integrity"
        ) or sys.modules.get("audit_evidence_integrity")
        if evidence_module is None:
            if __package__:
                from . import audit_evidence_integrity as evidence_module
            else:  # pragma: no cover - direct script invocation.
                import audit_evidence_integrity as evidence_module
        context = evidence_module.build_evidence_run_context(PAPERS / paper)
        snapshot, error = source_record_audit_snapshot_from_evidence_context(
            paper, context
        )
    except Exception as exc:  # noqa: BLE001 - audit acquisition fails closed.
        return None, None, str(exc)
    return snapshot, context, error


def _audit_paper(
    paper: str,
    *,
    theorem_realization_component_prevalidated: bool = False,
    source_record_snapshot: SourceRecordAuditSnapshot | None = None,
    finalize_snapshot: bool,
) -> list[Finding]:
    evidence_context: object | None = None
    if source_record_snapshot is None:
        snapshot, evidence_context, context_error = (
            _evidence_context_snapshot_for_paper(paper)
        )
        proc = subprocess.CompletedProcess(
            args=[],
            returncode=0 if snapshot is not None else 1,
            stdout=context_error,
        )
    else:
        snapshot = source_record_snapshot
        proc = subprocess.CompletedProcess(
            args=[], returncode=0, stdout="used caller-supplied run-scoped snapshot"
        )
    if proc.returncode != 0:
        detail = " ".join(proc.stdout.split())[-1000:]
        return [
            Finding(
                paper,
                "<audit>",
                "<helper>",
                (),
                "could not acquire a current immutable source-record evidence "
                "transaction"
                + (f": {detail}" if detail else ""),
            )
        ]
    if snapshot is None:
        detail = " ".join(proc.stdout.split())[-1000:]
        return [Finding(paper, "<audit>", "<helper>", (), f"helper failed: {detail}")]
    if snapshot.paper != paper:
        return [
            Finding(
                paper,
                "<audit>",
                "<source-record snapshot>",
                (),
                "source-record snapshot belongs to a different paper",
            )
        ]
    if (
        snapshot.structural_v11_validated
        and not theorem_realization_component_prevalidated
    ):
        return [
            Finding(
                paper,
                "<audit>",
                "<source-record snapshot>",
                (),
                "structural-v11 source-record inventory lacks the primary "
                "theorem-realization prevalidation capability",
            )
        ]
    mutation_error = (
        source_record_audit_snapshot_mutation_error(snapshot)
        if finalize_snapshot and evidence_context is None
        else ""
    )
    if mutation_error:
        return [
            Finding(
                paper,
                "<audit>",
                "<source-record snapshot>",
                (),
                mutation_error,
            )
        ]
    payload = snapshot.payload
    prompt_version = str(payload.get("prompt_version") or "").strip()
    if prompt_version != SOURCE_RECORD_PROMPT_VERSION:
        return [
            Finding(
                paper,
                "<audit>",
                "<source-record snapshot>",
                (),
                "source-record snapshot is not the current conclusion-provenance "
                f"schema/prompt ({prompt_version or 'missing'})",
            )
        ]
    paper_dir = PAPERS / paper
    payload_paper = str(payload.get("paper") or "").strip()
    if payload_paper != paper:
        return [
            Finding(
                paper,
                "<audit>",
                "<source-record snapshot>",
                (),
                "source-record snapshot payload belongs to a different paper",
            )
        ]
    if not snapshot.identity_validated and not snapshot.structural_v11_validated:
        statement_map_sha256 = current_paper_statement_map_sha256(paper_dir)
        identity_error = source_record_audit_identity_error(
            payload,
            expected_paper_statement_map_sha256=statement_map_sha256,
            folder=paper_dir,
        )
        if identity_error:
            return [
                Finding(
                    paper,
                    "<audit>",
                    "<current source-record scan>",
                    (),
                    "source-record helper returned an invalid or incomplete current "
                    "source-record audit: " + identity_error,
                )
            ]
        snapshot = _issued_source_record_audit_snapshot(
            paper=snapshot.paper,
            payload=snapshot.payload,
            source_file_sha256=snapshot.source_file_sha256,
            source_path=snapshot.source_path,
            paper_statement_map_sha256=statement_map_sha256,
            source_record_match_path=snapshot.source_record_match_path,
            source_record_match_sha256=snapshot.source_record_match_sha256,
            current_judgments_override=snapshot.current_judgments_override,
            status_payload_override=snapshot.status_payload_override,
            paper_statement_map_override=(
                snapshot.paper_statement_map_override
            ),
            corrected_scope_current_override=(
                snapshot.corrected_scope_current_override
            ),
            administrative_projection_rebind_override=(
                snapshot.administrative_projection_rebind_override
            ),
            configured_assumption_regularity_context_override=(
                snapshot.configured_assumption_regularity_context_override
            ),
            configured_assumption_regularity_context_error_override=(
                snapshot.configured_assumption_regularity_context_error_override
            ),
            identity_validated=True,
            payload_is_immutable=True,
        )
        mutation_error = (
            source_record_audit_snapshot_mutation_error(snapshot)
            if finalize_snapshot and evidence_context is None
            else ""
        )
        if mutation_error:
            return [
                Finding(
                    paper,
                    "<audit>",
                    "<source-record snapshot>",
                    (),
                    mutation_error,
                )
            ]

    try:
        judgments = (
            snapshot.current_judgments_override
            if snapshot.current_judgments_override is not None
            else current_judgments(paper, payload)
        )
        if not isinstance(judgments, Mapping):
            return [
                Finding(
                    paper,
                    "<audit>",
                    "<source-record judgments>",
                    (),
                    "current source-record judgment projection is unavailable",
                )
            ]
        status_payload = (
            snapshot.status_payload_override
            if snapshot.status_payload_override is not None
            else load_payload(PAPERS / paper / "status.json") or {}
        )
        statement_map = (
            snapshot.paper_statement_map_override
            if snapshot.paper_statement_map_override is not None
            else load_payload(
                PAPERS / paper / "audit" / "paper_statement_map.json"
            )
        )
        administrative_projection_rebind_override = (
            snapshot.administrative_projection_rebind_override
        )
        if administrative_projection_rebind_override is _CONTEXT_OVERRIDE_UNSET:
            (
                administrative_projection_rebind_override,
                administrative_projection_rebind_error,
            ) = load_current_administrative_projection_rebind_context(
                paper,
                payload,
                status_payload,
            )
            if administrative_projection_rebind_error:
                findings = [
                    Finding(
                        paper,
                        "<audit>",
                        "<administrative projection rebind>",
                        (),
                        "administrative projection rebind is invalid: "
                        + administrative_projection_rebind_error,
                    )
                ]
                return findings
        findings = missing_configured_row_findings(paper, payload)
        if not theorem_realization_component_prevalidated:
            # A consolidated v11 closeout has already checked the exact
            # expanded Specs, their paired proof endpoints, source atoms, and
            # complete transitive realization components.  Requiring another
            # source-map route merely because a reachable helper happens to
            # live in PaperInterface would make code location semantic.
            findings.extend(
                reachable_paper_interface_auxiliary_findings(
                    paper,
                    payload,
                    folder=PAPERS / paper,
                    routing_context_override=(
                        snapshot.auxiliary_routing_context_override
                    ),
                    routing_context_error_override=(
                        snapshot.auxiliary_routing_context_error_override
                    ),
                )
            )
        findings.extend(omitted_direct_dependency_findings(paper, payload))
        findings.extend(
            source_premise_false_eliminator_findings(
                paper,
                payload,
                status_payload_override=status_payload,
            )
        )
        if not theorem_realization_component_prevalidated:
            findings.extend(
                theorem_realization_component_contract_findings(
                    paper,
                    payload,
                    judgments,
                    status_payload_override=status_payload,
                    paper_statement_map_override=(
                        statement_map
                        if isinstance(statement_map, Mapping)
                        else None
                    ),
                    administrative_projection_rebind_override=(
                        administrative_projection_rebind_override
                    ),
                    configured_assumption_regularity_context_override=(
                        snapshot.configured_assumption_regularity_context_override
                    ),
                    configured_assumption_regularity_context_error_override=(
                        snapshot.configured_assumption_regularity_context_error_override
                    ),
                )
            )
        strict_component_contract = theorem_realization_contract_active(
            payload,
            status_payload,
            statement_map if isinstance(statement_map, Mapping) else None,
            folder=PAPERS / paper,
        )
        if snapshot.structural_v11_validated and not strict_component_contract:
            findings.append(
                Finding(
                    paper,
                    "<audit>",
                    "<source-record snapshot>",
                    (),
                    "structural-v11 inventory is unavailable because the exact "
                    "theorem-realization contract is not active",
                )
            )
            return findings
        antecedent_keys = exact_source_antecedents(judgments)
        data_antecedent_keys = nonpropositional_source_data_antecedents(
            judgments, strict_realization=strict_component_contract
        )
        (
            approved_source_convention_input_keys,
            approved_source_convention_field_keys,
        ) = current_approved_source_convention_antecedent_keys(
            paper,
            payload,
            judgments,
            status_payload_override=status_payload,
            paper_statement_map_override=(
                statement_map if isinstance(statement_map, Mapping) else None
            ),
            administrative_projection_rebind_override=(
                administrative_projection_rebind_override
            ),
        )
        semantic_model_record_bindings = (
            ()
            if strict_component_contract
            else current_complete_semantic_model_record_bindings(
                paper,
                payload,
                judgments,
                status_payload_override=status_payload,
                paper_statement_map_override=(
                    statement_map if isinstance(statement_map, Mapping) else None
                ),
                administrative_projection_rebind_override=(
                    administrative_projection_rebind_override
                ),
            )
        )
        corrected_model_bridge = corrected_model_conclusion_bridge(
            paper,
            payload,
            status_payload_override=status_payload,
            corrected_scope_current=snapshot.corrected_scope_current_override,
            input_raw_bytes_override=snapshot.input_raw_bytes_override,
        )
        for raw_failure in payload.get("recursion_failures") or []:
            if not isinstance(raw_failure, dict):
                continue
            findings.append(
                Finding(
                    paper,
                    "<record recursion>",
                    str(raw_failure.get("structure") or "unknown"),
                    (),
                    str(raw_failure.get("message") or raw_failure.get("kind") or "failed"),
                )
            )
        for item in payload.get("conclusion_dependency_items") or []:
            if not isinstance(item, dict):
                continue
            if strict_component_contract:
                # The schema-1 theorem-realization ledger already validates
                # every dependency occurrence and, for a direct record input,
                # requires its complete Lean/source field closure. Reapplying
                # the v10 constructor/record heuristic here is both redundant
                # and wrong for proof premises such as `Not (Nonempty R)`,
                # whose record type is nested rather than caller-supplied.
                continue
            if conclusion_input_is_accepted_source_antecedent(
                item,
                antecedent_keys,
                data_antecedent_keys,
                approved_source_convention_input_keys,
                strict_realization=strict_component_contract,
                judgments=judgments,
            ):
                continue
            if dependency_has_resolved_constructor(item, antecedent_keys, judgments):
                continue
            if dependency_has_complete_semantic_model_record_binding(
                item, semantic_model_record_bindings
            ):
                continue
            if (
                not strict_component_contract
                and corrected_model_dependency_is_covered(corrected_model_bridge, item)
            ):
                continue
            all_fields = tuple(
                str(field.get("judgment_key") or field.get("path") or "")
                for field in item.get("conclusion_fields") or []
                if isinstance(field, dict)
            )
            fields = unresolved_dependency_field_keys(
                item,
                antecedent_keys,
                data_antecedent_keys,
                approved_source_convention_field_keys,
                strict_realization=strict_component_contract,
            )
            if not strict_component_contract and record_input_is_nonresult_source_model_or_data(item):
                if not fields:
                    continue
                findings.append(
                    Finding(
                        paper,
                        str(item.get("row") or "unknown row"),
                        str(item.get("binder") or "unknown binder"),
                        fields,
                        "source-model record has no current exact source provenance "
                        "or checked constructor for its semantic field(s)",
                    )
                )
                continue
            if strict_component_contract and item.get("kind") == "record_conclusion_input":
                findings.append(
                    Finding(
                        paper,
                        str(item.get("row") or "unknown row"),
                        str(item.get("binder") or "unknown binder"),
                        fields or all_fields,
                        "caller-supplied record lacks a complete generic source/Lean "
                        "field-closure binding",
                    )
                )
                continue
            if all_fields and not fields:
                continue
            projection = dependency_checked_projection_result(
                item, antecedent_keys, judgments
            )
            rejected = circular_candidates(item)
            conditional = circular_candidates(
                {"rejected_constructors": item.get("conditional_constructors") or []}
            )
            if rejected:
                message = "only circular/repackaging constructor(s) found: " + rejected
            elif conditional:
                message = (
                    "constructor(s) remain conditional on an explicit checked_projection "
                    "contract tied to current exact source antecedents: "
                    + conditional
                )
                if projection.reason:
                    message += "; " + projection.reason
            elif item.get("kind") == "record_conclusion_input" and item.get(
                "valid_constructors"
            ):
                builders = ", ".join(
                    str(candidate.get("declaration") or "unnamed builder")
                    for candidate in item.get("valid_constructors") or []
                    if isinstance(candidate, dict)
                )
                message = (
                    "fresh-record builder(s) "
                    + (builders or "were found")
                    + " do not identify the caller-supplied record"
                )
            elif item.get("kind") == "bool_certificate_input":
                message = bool_certificate_finding_message(item)
            elif item.get("kind") == "selector_certificate_input":
                message = selector_certificate_finding_message(item)
            elif item.get("kind") == "aliased_conclusion_bridge_input":
                bridges = ", ".join(
                    str(bridge.get("declaration") or "unnamed local proof")
                    for bridge in item.get("result_bridges") or []
                    if isinstance(bridge, dict)
                )
                message = (
                    "delta-expanded proposition premise is converted into the "
                    "advertised result by referenced paper-local proof(s)"
                    + (f": {bridges}" if bridges else "")
                )
            else:
                message = (
                    "no paper-local constructor derives this conclusion-bearing input "
                    "from source primitives"
                )
            findings.append(
                Finding(
                    paper,
                    str(item.get("row") or "unknown row"),
                    str(item.get("binder") or "unknown binder"),
                    fields,
                    message,
                )
            )
        for item in payload.get("conclusion_dependency_items") or []:
            if not isinstance(item, dict):
                continue
            if strict_component_contract:
                # Strict occurrence contracts do not derive source credit
                # from the legacy `proved_from_primitives` prose field.
                continue
            rejected_names = {
                str(candidate.get("declaration") or "").strip()
                for candidate in item.get("rejected_constructors") or []
                if isinstance(candidate, dict) and str(candidate.get("declaration") or "").strip()
            }
            if not rejected_names:
                continue
            keys = {
                str(item.get("judgment_key") or "").strip(),
                *{
                    str(field.get("judgment_key") or "").strip()
                    for field in item.get("conclusion_fields") or []
                    if isinstance(field, dict)
                },
            } - {""}
            for key in sorted(keys & set(judgments)):
                judgment = judgments[key]
                classification = str(
                    judgment.get("classification")
                    or judgment.get("judgment")
                    or judgment.get("verdict")
                    or ""
                ).strip()
                if classification != "proved_from_primitives":
                    continue
                derivation = str(
                    judgment.get("lean_derivation")
                    or judgment.get("constructor")
                    or judgment.get("derived_from")
                    or ""
                )
                cited = sorted(
                    name for name in rejected_names if re.search(rf"\b{re.escape(name)}\b", derivation)
                )
                if cited:
                    findings.append(
                        Finding(
                            paper,
                            str(item.get("row") or "unknown row"),
                            str(item.get("binder") or "unknown binder"),
                            (key,),
                            "proved_from_primitives cites circular constructor(s): "
                            + ", ".join(cited),
                        )
                    )
        return findings
    finally:
        mutation_error = source_record_audit_snapshot_mutation_error(snapshot)
        if mutation_error and "findings" in locals():
            findings.append(
                Finding(
                    paper,
                    "<audit>",
                    "<source-record snapshot>",
                    (),
                    mutation_error,
                )
            )
        if (
            finalize_snapshot
            and evidence_context is not None
            and "findings" in locals()
        ):
            mutation_checker = _loaded_evidence_integrity_callable(
                "evidence_run_context_mutation_findings"
            )
            context_mutations = (
                mutation_checker(evidence_context)
                if callable(mutation_checker)
                else ()
            )
            for context_finding in context_mutations:
                findings.append(
                    Finding(
                        paper,
                        "<audit>",
                        "<evidence transaction>",
                        (),
                        context_finding.message,
                    )
                )


def audit_paper(
    paper: str,
    *,
    theorem_realization_component_prevalidated: bool = False,
    source_record_snapshot: SourceRecordAuditSnapshot | None = None,
    require_source_bytes: bool = True,
) -> list[Finding]:
    """Audit one paper and finalize every transaction acquired by this call."""

    if source_record_snapshot is None:
        from scripts.audit_evidence_integrity import (
            graph_native_closure_fast_path_findings,
        )

        # A canonical graph credential owns the complete conclusion/dependency
        # closure. Its validator rechecks the current Lean and source bindings;
        # neither a selected schema nor a stored success flag confers acceptance.
        # Only an unselected graph lane may continue to the legacy transaction.
        graph_findings = graph_native_closure_fast_path_findings(
            PAPERS / paper,
            release=False,
            require_source_bytes=require_source_bytes,
        )
        if graph_findings is not None:
            return [
                Finding(paper, "<audit>", "<accepted graph>", (), finding.message)
                for finding in graph_findings
                if finding.severity == "ERROR"
            ]

    return _audit_paper(
        paper,
        theorem_realization_component_prevalidated=(
            theorem_realization_component_prevalidated
        ),
        source_record_snapshot=source_record_snapshot,
        finalize_snapshot=True,
    )


def audit_paper_for_consolidated_closeout_transaction(
    paper: str,
    *,
    evidence_context: object,
    theorem_realization_component_prevalidated: bool = False,
) -> list[Finding]:
    """Audit against a context whose repository owner performs finalization.

    Requiring the issued evidence context, rather than exposing a Boolean on
    ``audit_paper``, keeps an ordinary caller from accidentally publishing an
    unfinalized result.
    """

    if theorem_realization_component_prevalidated:
        evidence_module = sys.modules.get(
            "scripts.audit_evidence_integrity"
        ) or sys.modules.get("audit_evidence_integrity")
        if evidence_module is None:
            if __package__:
                from . import audit_evidence_integrity as evidence_module
            else:  # pragma: no cover - direct script invocation.
                import audit_evidence_integrity as evidence_module
        receipt_validator = getattr(
            evidence_module,
            "has_current_v11_evidence_integrity_receipt",
            None,
        )
        if callable(receipt_validator) and receipt_validator(evidence_context):
            # The current v11 primary and evidence gates have already checked
            # the exact source atoms, expanded semantic targets, typed
            # result/proof contracts, direct definitions, complete Lean
            # dependency graph, material prerequisites, source inventory, and
            # axiom closure. The legacy conclusion pass is a projection of
            # those same obligations from the superseded raw carrier.
            return []

    snapshot, error = source_record_audit_snapshot_from_evidence_context(
        paper,
        evidence_context,
        structural_v11_prevalidated=(
            theorem_realization_component_prevalidated
        ),
    )
    if snapshot is None:
        return [
            Finding(
                paper,
                "<audit>",
                "<evidence transaction>",
                (),
                "could not reuse the exact closeout transaction"
                + (f": {error}" if error else ""),
            )
        ]
    return _audit_paper(
        paper,
        theorem_realization_component_prevalidated=(
            theorem_realization_component_prevalidated
        ),
        source_record_snapshot=snapshot,
        finalize_snapshot=False,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--paper", help="restrict the audit to one paper folder")
    selection.add_argument(
        "--public-complete",
        action="store_true",
        help=(
            "audit only papers explicitly marked repository_visibility=public "
            "whose mathematical status is formalized or formalized with caveat; "
            "fail if any paper omits repository visibility"
        ),
    )
    parser.add_argument("--json", action="store_true", help="emit findings as JSON")
    parser.add_argument(
        "--allow-missing-source-bytes",
        action="store_true",
        help="validate public graph credentials without requiring private source artifacts",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(4, os.cpu_count() or 1),
        help="number of independent paper scans to run concurrently (default: up to 4)",
    )
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be at least 1")

    try:
        papers = paper_ids(args.paper, public_complete=args.public_complete)
    except ValueError as exc:
        parser.error(str(exc))
    if args.paper and not papers:
        parser.error(f"paper folder/status.json not found: {args.paper}")
    if args.public_complete and not papers:
        parser.error("no explicitly public fully formalized papers found")
    def audit_selected_paper(paper: str) -> list[Finding]:
        return audit_paper(
            paper, require_source_bytes=not args.allow_missing_source_bytes
        )

    if args.jobs == 1 or len(papers) <= 1:
        paper_findings = [audit_selected_paper(paper) for paper in papers]
    else:
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            paper_findings = list(executor.map(audit_selected_paper, papers))
    findings = [finding for group in paper_findings for finding in group]
    findings.sort(key=lambda item: (item.paper, item.row, item.binder, item.fields))
    if args.json:
        print(json.dumps([asdict(finding) for finding in findings], indent=2, sort_keys=True))
    else:
        for finding in findings:
            print(finding.format())
        print(
            f"Conclusion-provenance audit: {len(findings)} error(s) across "
            f"{len(papers)} paper(s)"
        )
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
