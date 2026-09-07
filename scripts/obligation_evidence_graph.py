#!/usr/bin/env python3
"""Typed, portable obligation leaves and a pure evidence-graph diff.

This module is the semantic coordination core for incremental closeout.  It
does not read files, invoke Lean, call an LLM, or decide that a paper is
closed.  Existing strict producers mint the typed leaves after performing
their source, Lean, review, realization, or build checks.  A terminal verifier
must separately revalidate current source/Lean controls before granting
acceptance.

The important boundary is granularity: a leaf contains exactly one durable
obligation-family result.  Storage containers, declaration names, code
locations, engine versions, checkout paths, line numbers, timestamps, and Git
commits are intentionally absent.  Paper-local and reusable-library Lean code
therefore use the same declaration and source-to-Lean judgment schemas.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from enum import Enum
from types import MappingProxyType
from typing import Any, Iterable, Mapping

try:
    from scripts.portable_evidence_identity import portable_evidence_sha256
    from scripts.obligation_evidence_contracts import (
        LEAN_DECLARATION_MANIFEST_PAYLOAD_FIELDS,
        LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        LEAN_PROOF_ENDPOINT_PAYLOAD_FIELDS,
        LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
    )
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from portable_evidence_identity import portable_evidence_sha256
    from obligation_evidence_contracts import (
        LEAN_DECLARATION_MANIFEST_PAYLOAD_FIELDS,
        LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        LEAN_PROOF_ENDPOINT_PAYLOAD_FIELDS,
        LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
    )


OBLIGATION_EVIDENCE_LEAF_SCHEMA = 1
OBLIGATION_EVIDENCE_GRAPH_SCHEMA = 1
ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA = 2
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class ObligationEvidenceError(ValueError):
    """A leaf or graph is malformed, corrupt, cyclic, or incomplete."""


class ObligationKind(str, Enum):
    SOURCE_ATOM = "source_atom"
    LEAN_DECLARATION = "lean_declaration"
    SOURCE_LEAN_JUDGMENT = "source_lean_judgment"
    PROOF_REALIZATION = "proof_realization"
    BUILD = "build"
    PAPER_CLOSURE = "paper_closure"


class LeanSemanticTargetKind(str, Enum):
    SPEC_PROPOSITION = "spec_proposition"
    DEFINITION_DECLARATION = "definition_declaration"
    PROOF_ENDPOINT = "proof_endpoint"
    SOURCE_ASSUMPTION = "source_assumption"
    PROOF_SUPPORT = "proof_support"
    SEMANTIC_PREREQUISITE = "semantic_prerequisite"


class SourceLeanVerdict(str, Enum):
    MATCHES = "matches"
    MATCHES_APPROVED_CORRECTED_TARGET = "matches_approved_corrected_target"
    DOES_NOT_MATCH = "does_not_match"
    UNCERTAIN = "uncertain"


class ProofRealizationMode(str, Enum):
    PROVES = "proves"
    DEFINITIONALLY_REALIZES = "definitionally_realizes"
    REFUTES = "refutes"


def _sha256(value: object, field: str) -> str:
    text = str(value or "").strip().lower()
    if not SHA256_RE.fullmatch(text):
        raise ObligationEvidenceError(f"{field} is not a lowercase SHA-256 digest")
    return text


def _sha256s(
    values: Iterable[object], field: str, *, nonempty: bool
) -> tuple[str, ...]:
    result = tuple(sorted(_sha256(value, field) for value in values))
    if nonempty and not result:
        raise ObligationEvidenceError(f"{field} must not be empty")
    if len(set(result)) != len(result):
        raise ObligationEvidenceError(f"{field} contains a duplicate digest")
    return result


def _enum(value: object, enum_type: type[Enum], field: str) -> str:
    try:
        candidate = value.value if isinstance(value, enum_type) else str(value).strip()
        return str(enum_type(candidate).value)
    except ValueError as exc:
        raise ObligationEvidenceError(f"{field} is unsupported") from exc


def _leaf_material(
    *,
    kind: ObligationKind,
    contract_sha256: str,
    semantic_payload: Mapping[str, Any],
    depends_on: Iterable[object],
) -> tuple[dict[str, Any], tuple[str, ...], str]:
    dependencies = _sha256s(depends_on, "leaf dependency", nonempty=False)
    material = {
        "schema": OBLIGATION_EVIDENCE_LEAF_SCHEMA,
        "kind": kind.value,
        "contract_sha256": _sha256(contract_sha256, "leaf contract"),
        "semantic_payload": dict(semantic_payload),
        "depends_on": list(dependencies),
    }
    return material, dependencies, portable_evidence_sha256(material)


@dataclass(frozen=True)
class ObligationEvidenceLeaf:
    """One immutable content-addressed obligation-family result.

    ``leaf_sha256`` authenticates only the portable semantic material.  Human
    navigation and issuing-engine provenance belong in a separate index or
    receipt and cannot change this identity.
    """

    kind: ObligationKind
    contract_sha256: str
    semantic_payload: Mapping[str, Any]
    depends_on: tuple[str, ...]
    leaf_sha256: str

    def projection(self) -> dict[str, Any]:
        return {
            "schema": OBLIGATION_EVIDENCE_LEAF_SCHEMA,
            "kind": self.kind.value,
            "contract_sha256": self.contract_sha256,
            "semantic_payload": dict(self.semantic_payload),
            "depends_on": list(self.depends_on),
            "leaf_sha256": self.leaf_sha256,
        }


def _issue_leaf(
    *,
    kind: ObligationKind,
    contract_sha256: str,
    semantic_payload: Mapping[str, Any],
    depends_on: Iterable[object] = (),
) -> ObligationEvidenceLeaf:
    material, dependencies, digest = _leaf_material(
        kind=kind,
        contract_sha256=contract_sha256,
        semantic_payload=semantic_payload,
        depends_on=depends_on,
    )
    leaf = ObligationEvidenceLeaf(
        kind=kind,
        contract_sha256=material["contract_sha256"],
        semantic_payload=MappingProxyType(dict(material["semantic_payload"])),
        depends_on=dependencies,
        leaf_sha256=digest,
    )
    # Use the same strict parser used for persisted objects.  Constructors are
    # not a second, more permissive schema path.
    return validate_obligation_leaf(leaf.projection())


def source_atom_leaf(
    *,
    contract_sha256: str,
    source_artifact_sha256: str,
    source_quote_sha256: str,
    source_component_sha256: str,
    source_role_contract_sha256: str,
) -> ObligationEvidenceLeaf:
    """Mint a carrier-independent exact-source component leaf.

    The exact quote is the atom's source anchor. A possibly longer verbatim
    source bundle is bound separately by each source-to-Lean judgment. A
    paraphrase may help a human decompose coverage elsewhere, but it is
    deliberately not a substitute identity here.  The complete byte-pinned
    source corpus is validated and bound by the paper preflight/index and the
    terminal verifier; its container digest is checked here but is not repeated
    in every semantic atom.
    """

    _sha256(source_artifact_sha256, "source artifact")
    return _issue_leaf(
        kind=ObligationKind.SOURCE_ATOM,
        contract_sha256=contract_sha256,
        semantic_payload={
            "source_quote_sha256": _sha256(source_quote_sha256, "source quote"),
            "source_component_sha256": _sha256(
                source_component_sha256, "source component"
            ),
            "source_role_contract_sha256": _sha256(
                source_role_contract_sha256, "source role contract"
            ),
        },
    )


def source_atom_semantic_projection(
    leaf: ObligationEvidenceLeaf,
) -> Mapping[str, str]:
    """Return the stable exact-clause meaning shared by all atom carriers.

    Historical source-atom leaves repeated the complete source-artifact digest
    in every leaf. Current leaves bind that corpus once through the complete
    paper preflight/index. Both carriers identify one source clause by the same
    exact quote, source component, and source-role contract. This projection is
    therefore the version-independent comparison surface; it does not grant
    acceptance and it deliberately retains every clause-level semantic field.
    """

    if (
        not isinstance(leaf, ObligationEvidenceLeaf)
        or leaf.kind is not ObligationKind.SOURCE_ATOM
    ):
        raise ObligationEvidenceError(
            "source-atom semantic projection requires a source atom"
        )
    return MappingProxyType(
        {
            field: _sha256(leaf.semantic_payload.get(field), field.replace("_", " "))
            for field in (
                "source_quote_sha256",
                "source_component_sha256",
                "source_role_contract_sha256",
            )
        }
    )


def legacy_artifact_bound_source_atom_leaf(
    *,
    contract_sha256: str,
    source_artifact_sha256: str,
    source_quote_sha256: str,
    source_component_sha256: str,
    source_role_contract_sha256: str,
) -> ObligationEvidenceLeaf:
    """Reconstruct the historical source-atom schema for direct validation.

    This constructor exists only for fixtures and historical credential
    verification.  New producers must use :func:`source_atom_leaf`, which
    leaves the whole-corpus identity at the paper preflight/index boundary.
    """

    return _issue_leaf(
        kind=ObligationKind.SOURCE_ATOM,
        contract_sha256=contract_sha256,
        semantic_payload={
            "source_artifact_sha256": _sha256(
                source_artifact_sha256, "source artifact"
            ),
            "source_quote_sha256": _sha256(source_quote_sha256, "source quote"),
            "source_component_sha256": _sha256(
                source_component_sha256, "source component"
            ),
            "source_role_contract_sha256": _sha256(
                source_role_contract_sha256, "source role contract"
            ),
        },
    )


def lean_declaration_leaf(
    *,
    contract_sha256: str,
    semantic_target_kind: LeanSemanticTargetKind | str,
    elaborated_signature_sha256: str,
    elaborated_proposition_graph_sha256: str,
    semantic_dependency_sha256: str,
) -> ObligationEvidenceLeaf:
    """Mint one Lean-authored declaration-semantic leaf.

    Qualified declaration names and paper/library locations are navigation,
    not semantic identity.  The exact issuing receipt retains those names so a
    current verifier can ask Lean to reproduce these three semantic digests.
    """

    return _issue_leaf(
        kind=ObligationKind.LEAN_DECLARATION,
        contract_sha256=contract_sha256,
        semantic_payload={
            "semantic_target_kind": _enum(
                semantic_target_kind,
                LeanSemanticTargetKind,
                "Lean semantic target kind",
            ),
            "elaborated_signature_sha256": _sha256(
                elaborated_signature_sha256, "elaborated signature"
            ),
            "elaborated_proposition_graph_sha256": _sha256(
                elaborated_proposition_graph_sha256,
                "elaborated proposition graph",
            ),
            "semantic_dependency_sha256": _sha256(
                semantic_dependency_sha256, "semantic dependency"
            ),
        },
    )


def lean_proof_endpoint_leaf(
    *,
    contract_sha256: str,
    spec_declaration_sha256: str,
    relation: ProofRealizationMode | str,
) -> ObligationEvidenceLeaf:
    """Record a Lean-checked endpoint without duplicating its proof closure.

    The accepted transaction establishes the exact endpoint/Spec type relation.
    Conclusion provenance, the import closure, and the focused build remain
    separate graph leaves, so expanding the endpoint's entire proof body into
    another declaration manifest would add no semantic check.  The endpoint
    name stays in issuance/navigation provenance rather than semantic identity.
    """

    spec = _sha256(spec_declaration_sha256, "Spec declaration leaf")
    return _issue_leaf(
        kind=ObligationKind.LEAN_DECLARATION,
        contract_sha256=contract_sha256,
        semantic_payload={
            "semantic_target_kind": LeanSemanticTargetKind.PROOF_ENDPOINT.value,
            "spec_declaration_sha256": spec,
            "relation": _enum(
                relation, ProofRealizationMode, "proof endpoint relation"
            ),
        },
        depends_on=(spec,),
    )


def lean_reviewed_semantic_prerequisite_leaf(
    *,
    contract_sha256: str,
    reviewed_semantic_target_sha256: str,
    elaborated_signature_sha256: str | None = None,
) -> ObligationEvidenceLeaf:
    """Record the exact Lean meaning used in a prerequisite source review."""

    return lean_reviewed_semantic_target_leaf(
        contract_sha256=contract_sha256,
        semantic_target_kind=LeanSemanticTargetKind.SEMANTIC_PREREQUISITE,
        reviewed_semantic_target_sha256=reviewed_semantic_target_sha256,
        elaborated_signature_sha256=elaborated_signature_sha256,
    )


def lean_reviewed_semantic_target_leaf(
    *,
    contract_sha256: str,
    semantic_target_kind: LeanSemanticTargetKind | str,
    reviewed_semantic_target_sha256: str,
    elaborated_signature_sha256: str | None = None,
) -> ObligationEvidenceLeaf:
    """Record exact reviewed Lean meaning independent of source syntax/location."""

    target_kind = _enum(
        semantic_target_kind,
        LeanSemanticTargetKind,
        "Lean semantic target kind",
    )
    if target_kind == LeanSemanticTargetKind.PROOF_ENDPOINT.value:
        raise ObligationEvidenceError(
            "a proof endpoint requires the typed endpoint leaf contract"
        )
    payload = {
        "semantic_target_kind": target_kind,
        "reviewed_semantic_target_sha256": _sha256(
            reviewed_semantic_target_sha256,
            "reviewed semantic target",
        ),
    }
    if elaborated_signature_sha256 is not None:
        payload["elaborated_signature_sha256"] = _sha256(
            elaborated_signature_sha256,
            "Lean elaborated semantic identity",
        )
    return _issue_leaf(
        kind=ObligationKind.LEAN_DECLARATION,
        contract_sha256=contract_sha256,
        semantic_payload=payload,
    )


def legacy_content_bound_reviewed_semantic_target_leaf(
    *,
    contract_sha256: str,
    semantic_target_kind: LeanSemanticTargetKind | str,
    reviewed_semantic_target_sha256: str,
    declaration_content_sha256: str,
) -> ObligationEvidenceLeaf:
    """Reconstruct the historical syntax-bound reviewed-target leaf.

    New producers must use :func:`lean_reviewed_semantic_target_leaf`.  This
    constructor exists only for fixtures and direct verification of historical
    accepted graphs; declaration bytes are provenance, not semantic identity.
    """

    target_kind = _enum(
        semantic_target_kind,
        LeanSemanticTargetKind,
        "Lean semantic target kind",
    )
    if target_kind == LeanSemanticTargetKind.PROOF_ENDPOINT.value:
        raise ObligationEvidenceError(
            "a proof endpoint requires the typed endpoint leaf contract"
        )
    return _issue_leaf(
        kind=ObligationKind.LEAN_DECLARATION,
        contract_sha256=contract_sha256,
        semantic_payload={
            "semantic_target_kind": target_kind,
            "reviewed_semantic_target_sha256": _sha256(
                reviewed_semantic_target_sha256,
                "reviewed semantic target",
            ),
            "declaration_content_sha256": _sha256(
                declaration_content_sha256,
                "reviewed declaration content",
            ),
        },
    )


def source_lean_judgment_leaf(
    *,
    contract_sha256: str,
    source_atom_sha256s: Iterable[str],
    lean_declaration_sha256: str,
    verbatim_source_bundle_sha256: str,
    verdict: SourceLeanVerdict | str,
) -> ObligationEvidenceLeaf:
    """Mint one raw-source-to-expanded-Lean semantic judgment.

    The schema is identical for paper-local and library declarations.  Code
    location never changes the semantic review obligation.  Reviewer, prompt,
    reason, issuing-engine, and accepted-transaction details belong to an
    issuance attestation outside this semantic object.  They establish that
    the leaf was legitimately issued; changing their presentation cannot
    change the already-reviewed source/Lean proposition.
    """

    source_atoms = _sha256s(source_atom_sha256s, "source atom leaf", nonempty=True)
    lean_declaration = _sha256(lean_declaration_sha256, "Lean declaration leaf")
    return _issue_leaf(
        kind=ObligationKind.SOURCE_LEAN_JUDGMENT,
        contract_sha256=contract_sha256,
        semantic_payload={
            "source_atom_sha256s": list(source_atoms),
            "lean_declaration_sha256": lean_declaration,
            "verbatim_source_bundle_sha256": _sha256(
                verbatim_source_bundle_sha256, "verbatim source bundle"
            ),
            "verdict": _enum(verdict, SourceLeanVerdict, "source-Lean verdict"),
        },
        depends_on=(*source_atoms, lean_declaration),
    )


def proof_realization_leaf(
    *,
    contract_sha256: str,
    spec_declaration_sha256: str,
    proof_endpoint_sha256: str,
    relation: ProofRealizationMode | str,
    lean_relation_sha256: str,
) -> ObligationEvidenceLeaf:
    """Mint one Lean-established Spec/proof relationship."""

    spec = _sha256(spec_declaration_sha256, "Spec declaration leaf")
    endpoint = _sha256(proof_endpoint_sha256, "proof endpoint leaf")
    if spec == endpoint:
        raise ObligationEvidenceError(
            "proof realization requires distinct Spec and endpoint leaves"
        )
    return _issue_leaf(
        kind=ObligationKind.PROOF_REALIZATION,
        contract_sha256=contract_sha256,
        semantic_payload={
            "spec_declaration_sha256": spec,
            "proof_endpoint_sha256": endpoint,
            "relation": _enum(
                relation, ProofRealizationMode, "proof realization relation"
            ),
            "lean_relation_sha256": _sha256(
                lean_relation_sha256, "Lean realization relation"
            ),
        },
        depends_on=(spec, endpoint),
    )


def build_evidence_leaf(
    *,
    contract_sha256: str,
    target_declaration_sha256s: Iterable[str],
    build_command_sha256: str,
    toolchain_sha256: str,
    lean_import_closure_sha256: str,
) -> ObligationEvidenceLeaf:
    """Mint one passed build result without Git or machine coordinates."""

    targets = _sha256s(
        target_declaration_sha256s, "build target declaration", nonempty=True
    )
    return _issue_leaf(
        kind=ObligationKind.BUILD,
        contract_sha256=contract_sha256,
        semantic_payload={
            "target_declaration_sha256s": list(targets),
            "build_command_sha256": _sha256(build_command_sha256, "build command"),
            "toolchain_sha256": _sha256(toolchain_sha256, "build toolchain"),
            "lean_import_closure_sha256": _sha256(
                lean_import_closure_sha256, "Lean import closure"
            ),
            "result": "passed",
        },
        depends_on=targets,
    )


def paper_closure_leaf(
    *,
    contract_sha256: str,
    semantic_graph_sha256: str,
    paper_index_sha256: str,
    terminal_verification_sha256: str,
    terminal_authority_sha256: str,
    semantic_root_leaf_sha256s: Iterable[str],
    strict_closeout_authority: Mapping[str, Any] | None = None,
    final_holistic_audit_surface_sha256: str | None = None,
    source_assurance_sha256: str | None = None,
) -> ObligationEvidenceLeaf:
    """Mint the one terminal root that turns a semantic DAG into a credential.

    The semantic graph remains a separately content-addressed subgraph.  A
    verifier or tooling revision can therefore replace this terminal root
    without changing any source, Lean, judgment, realization, or build leaf.
    """

    roots = _sha256s(
        semantic_root_leaf_sha256s,
        "semantic graph root",
        nonempty=True,
    )
    payload: dict[str, Any] = {
        "semantic_graph_sha256": _sha256(semantic_graph_sha256, "semantic graph"),
        "paper_index_sha256": _sha256(paper_index_sha256, "paper index"),
        "terminal_verification_sha256": _sha256(
            terminal_verification_sha256, "terminal verification"
        ),
        "terminal_authority_sha256": _sha256(
            terminal_authority_sha256, "terminal authority"
        ),
        "semantic_root_leaf_sha256s": list(roots),
    }
    current_fields = (
        strict_closeout_authority,
        final_holistic_audit_surface_sha256,
        source_assurance_sha256,
    )
    if any(value is not None for value in current_fields):
        if any(value is None for value in current_fields):
            raise ObligationEvidenceError(
                "current paper closure requires authority and both semantic assurances"
            )
        if not isinstance(strict_closeout_authority, Mapping):
            raise ObligationEvidenceError(
                "current paper closure strict authority is malformed"
            )
        payload.update(
            {
                "strict_closeout_authority": dict(strict_closeout_authority),
                "final_holistic_audit_surface_sha256": _sha256(
                    final_holistic_audit_surface_sha256,
                    "final holistic audit surface",
                ),
                "source_assurance_sha256": _sha256(
                    source_assurance_sha256, "source assurance"
                ),
            }
        )
    return _issue_leaf(
        kind=ObligationKind.PAPER_CLOSURE,
        contract_sha256=contract_sha256,
        semantic_payload=payload,
        depends_on=roots,
    )


def _validated_semantic_payload(
    kind: ObligationKind,
    value: object,
) -> dict[str, Any]:
    if not isinstance(value, Mapping):
        raise ObligationEvidenceError("leaf semantic_payload is not an object")
    payload = dict(value)
    if kind is ObligationKind.SOURCE_ATOM:
        current_required = {
            "source_quote_sha256",
            "source_component_sha256",
            "source_role_contract_sha256",
        }
        legacy_required = {"source_artifact_sha256", *current_required}
        if set(payload) == current_required:
            required = current_required
        elif set(payload) == legacy_required:
            required = legacy_required
        else:
            raise ObligationEvidenceError("source-atom payload fields are malformed")
        return {field: _sha256(payload[field], field) for field in sorted(required)}
    if kind is ObligationKind.LEAN_DECLARATION:
        payload_fields = frozenset(payload)
        if payload_fields == LEAN_PROOF_ENDPOINT_PAYLOAD_FIELDS:
            target_kind = _enum(
                payload["semantic_target_kind"],
                LeanSemanticTargetKind,
                "Lean semantic target kind",
            )
            if target_kind != LeanSemanticTargetKind.PROOF_ENDPOINT.value:
                raise ObligationEvidenceError(
                    "proof-endpoint payload has the wrong semantic target kind"
                )
            return {
                "semantic_target_kind": target_kind,
                "spec_declaration_sha256": _sha256(
                    payload["spec_declaration_sha256"],
                    "Spec declaration leaf",
                ),
                "relation": _enum(
                    payload["relation"],
                    ProofRealizationMode,
                    "proof endpoint relation",
                ),
            }
        if payload_fields in {
            LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
            LEAN_IDENTITY_BOUND_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
            LEGACY_CONTENT_BOUND_LEAN_REVIEWED_SEMANTIC_TARGET_PAYLOAD_FIELDS,
        }:
            target_kind = _enum(
                payload["semantic_target_kind"],
                LeanSemanticTargetKind,
                "Lean semantic target kind",
            )
            if target_kind == LeanSemanticTargetKind.PROOF_ENDPOINT.value:
                raise ObligationEvidenceError(
                    "reviewed semantic-target payload has the wrong target kind"
                )
            result = {
                "semantic_target_kind": target_kind,
                "reviewed_semantic_target_sha256": _sha256(
                    payload["reviewed_semantic_target_sha256"],
                    "reviewed semantic target",
                ),
            }
            if "declaration_content_sha256" in payload:
                result["declaration_content_sha256"] = _sha256(
                    payload["declaration_content_sha256"],
                    "reviewed declaration content",
                )
            if "elaborated_signature_sha256" in payload:
                result["elaborated_signature_sha256"] = _sha256(
                    payload["elaborated_signature_sha256"],
                    "Lean elaborated semantic identity",
                )
            return result
        if payload_fields != LEAN_DECLARATION_MANIFEST_PAYLOAD_FIELDS:
            raise ObligationEvidenceError(
                "Lean-declaration payload fields are malformed"
            )
        return {
            "semantic_target_kind": _enum(
                payload["semantic_target_kind"],
                LeanSemanticTargetKind,
                "Lean semantic target kind",
            ),
            "elaborated_signature_sha256": _sha256(
                payload["elaborated_signature_sha256"], "elaborated signature"
            ),
            "elaborated_proposition_graph_sha256": _sha256(
                payload["elaborated_proposition_graph_sha256"],
                "elaborated proposition graph",
            ),
            "semantic_dependency_sha256": _sha256(
                payload["semantic_dependency_sha256"], "semantic dependency"
            ),
        }
    if kind is ObligationKind.SOURCE_LEAN_JUDGMENT:
        required = {
            "source_atom_sha256s",
            "lean_declaration_sha256",
            "verbatim_source_bundle_sha256",
            "verdict",
        }
        if set(payload) != required or not isinstance(
            payload.get("source_atom_sha256s"), list
        ):
            raise ObligationEvidenceError(
                "source-Lean judgment payload fields are malformed"
            )
        return {
            "source_atom_sha256s": list(
                _sha256s(
                    payload["source_atom_sha256s"],
                    "source atom leaf",
                    nonempty=True,
                )
            ),
            "lean_declaration_sha256": _sha256(
                payload["lean_declaration_sha256"], "Lean declaration leaf"
            ),
            "verbatim_source_bundle_sha256": _sha256(
                payload["verbatim_source_bundle_sha256"],
                "verbatim source bundle",
            ),
            "verdict": _enum(
                payload["verdict"], SourceLeanVerdict, "source-Lean verdict"
            ),
        }
    if kind is ObligationKind.PROOF_REALIZATION:
        required = {
            "spec_declaration_sha256",
            "proof_endpoint_sha256",
            "relation",
            "lean_relation_sha256",
        }
        if set(payload) != required:
            raise ObligationEvidenceError(
                "proof-realization payload fields are malformed"
            )
        spec = _sha256(payload["spec_declaration_sha256"], "Spec declaration leaf")
        endpoint = _sha256(payload["proof_endpoint_sha256"], "proof endpoint leaf")
        if spec == endpoint:
            raise ObligationEvidenceError(
                "proof realization requires distinct Spec and endpoint leaves"
            )
        return {
            "spec_declaration_sha256": spec,
            "proof_endpoint_sha256": endpoint,
            "relation": _enum(
                payload["relation"],
                ProofRealizationMode,
                "proof realization relation",
            ),
            "lean_relation_sha256": _sha256(
                payload["lean_relation_sha256"], "Lean realization relation"
            ),
        }
    if kind is ObligationKind.BUILD:
        required = {
            "target_declaration_sha256s",
            "build_command_sha256",
            "toolchain_sha256",
            "lean_import_closure_sha256",
            "result",
        }
        if set(payload) != required or not isinstance(
            payload.get("target_declaration_sha256s"), list
        ):
            raise ObligationEvidenceError("build payload fields are malformed")
        if payload.get("result") != "passed":
            raise ObligationEvidenceError("build evidence result is not passed")
        return {
            "target_declaration_sha256s": list(
                _sha256s(
                    payload["target_declaration_sha256s"],
                    "build target declaration",
                    nonempty=True,
                )
            ),
            "build_command_sha256": _sha256(
                payload["build_command_sha256"], "build command"
            ),
            "toolchain_sha256": _sha256(payload["toolchain_sha256"], "build toolchain"),
            "lean_import_closure_sha256": _sha256(
                payload["lean_import_closure_sha256"], "Lean import closure"
            ),
            "result": "passed",
        }
    if kind is ObligationKind.PAPER_CLOSURE:
        legacy_required = {
            "semantic_graph_sha256",
            "paper_index_sha256",
            "terminal_verification_sha256",
            "terminal_authority_sha256",
            "semantic_root_leaf_sha256s",
        }
        current_required = {
            *legacy_required,
            "strict_closeout_authority",
            "final_holistic_audit_surface_sha256",
            "source_assurance_sha256",
        }
        payload_fields = set(payload)
        if payload_fields not in (legacy_required, current_required) or not isinstance(
            payload.get("semantic_root_leaf_sha256s"), list
        ):
            raise ObligationEvidenceError("paper-closure payload fields are malformed")
        result: dict[str, Any] = {
            "semantic_graph_sha256": _sha256(
                payload["semantic_graph_sha256"], "semantic graph"
            ),
            "paper_index_sha256": _sha256(payload["paper_index_sha256"], "paper index"),
            "terminal_verification_sha256": _sha256(
                payload["terminal_verification_sha256"],
                "terminal verification",
            ),
            "terminal_authority_sha256": _sha256(
                payload["terminal_authority_sha256"], "terminal authority"
            ),
            "semantic_root_leaf_sha256s": list(
                _sha256s(
                    payload["semantic_root_leaf_sha256s"],
                    "semantic graph root",
                    nonempty=True,
                )
            ),
        }
        if payload_fields == current_required:
            authority = payload.get("strict_closeout_authority")
            if not isinstance(authority, Mapping):
                raise ObligationEvidenceError(
                    "paper-closure strict authority is malformed"
                )
            result.update(
                {
                    "strict_closeout_authority": dict(authority),
                    "final_holistic_audit_surface_sha256": _sha256(
                        payload["final_holistic_audit_surface_sha256"],
                        "final holistic audit surface",
                    ),
                    "source_assurance_sha256": _sha256(
                        payload["source_assurance_sha256"], "source assurance"
                    ),
                }
            )
        return result
    raise ObligationEvidenceError("unsupported obligation kind")


def validate_obligation_leaf(value: object) -> ObligationEvidenceLeaf:
    """Authenticate one persisted leaf's exact schema and content digest."""

    if not isinstance(value, Mapping):
        raise ObligationEvidenceError("obligation leaf is not an object")
    required = {
        "schema",
        "kind",
        "contract_sha256",
        "semantic_payload",
        "depends_on",
        "leaf_sha256",
    }
    if set(value) != required or value.get("schema") != OBLIGATION_EVIDENCE_LEAF_SCHEMA:
        raise ObligationEvidenceError("obligation leaf fields are malformed")
    try:
        kind = ObligationKind(str(value.get("kind") or ""))
    except ValueError as exc:
        raise ObligationEvidenceError("obligation leaf kind is unsupported") from exc
    if not isinstance(value.get("depends_on"), list):
        raise ObligationEvidenceError("leaf dependencies must be a list")
    contract = _sha256(value.get("contract_sha256"), "leaf contract")
    payload = _validated_semantic_payload(kind, value.get("semantic_payload"))
    dependencies = _sha256s(value["depends_on"], "leaf dependency", nonempty=False)

    if kind is ObligationKind.LEAN_DECLARATION and "spec_declaration_sha256" in payload:
        expected_dependencies = (payload["spec_declaration_sha256"],)
    elif kind in {ObligationKind.SOURCE_ATOM, ObligationKind.LEAN_DECLARATION}:
        expected_dependencies: tuple[str, ...] = ()
    elif kind is ObligationKind.SOURCE_LEAN_JUDGMENT:
        expected_dependencies = tuple(
            sorted(
                [
                    *payload["source_atom_sha256s"],
                    payload["lean_declaration_sha256"],
                ]
            )
        )
    elif kind is ObligationKind.PROOF_REALIZATION:
        expected_dependencies = tuple(
            sorted(
                [
                    payload["spec_declaration_sha256"],
                    payload["proof_endpoint_sha256"],
                ]
            )
        )
    elif kind is ObligationKind.BUILD:
        expected_dependencies = tuple(payload["target_declaration_sha256s"])
    else:
        expected_dependencies = tuple(payload["semantic_root_leaf_sha256s"])
    if dependencies != expected_dependencies:
        raise ObligationEvidenceError(
            f"{kind.value} dependencies disagree with its semantic payload"
        )

    material = {
        "schema": OBLIGATION_EVIDENCE_LEAF_SCHEMA,
        "kind": kind.value,
        "contract_sha256": contract,
        "semantic_payload": payload,
        "depends_on": list(dependencies),
    }
    digest = portable_evidence_sha256(material)
    if _sha256(value.get("leaf_sha256"), "leaf identity") != digest:
        raise ObligationEvidenceError("obligation leaf identity is corrupt")
    return ObligationEvidenceLeaf(
        kind=kind,
        contract_sha256=contract,
        semantic_payload=MappingProxyType(payload),
        depends_on=dependencies,
        leaf_sha256=digest,
    )


@dataclass(frozen=True)
class ObligationEvidenceGraph:
    """A complete, acyclic required leaf set for one paper snapshot."""

    leaves: Mapping[str, ObligationEvidenceLeaf]
    root_leaf_sha256s: tuple[str, ...]
    topological_leaf_sha256s: tuple[str, ...]
    graph_sha256: str

    @property
    def schema(self) -> int:
        if (
            len(self.root_leaf_sha256s) == 1
            and self.leaves[self.root_leaf_sha256s[0]].kind
            is ObligationKind.PAPER_CLOSURE
        ):
            return ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA
        return OBLIGATION_EVIDENCE_GRAPH_SCHEMA

    def projection(self) -> dict[str, Any]:
        accepting = self.schema == ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA
        return {
            "schema": self.schema,
            "acceptance_credential": accepting,
            "integrity_and_planning_only": not accepting,
            "leaf_sha256s": sorted(self.leaves),
            "root_leaf_sha256s": list(self.root_leaf_sha256s),
            "graph_sha256": self.graph_sha256,
        }


def build_obligation_graph(
    leaves: Iterable[ObligationEvidenceLeaf | Mapping[str, Any]],
    *,
    root_leaf_sha256s: Iterable[str],
) -> ObligationEvidenceGraph:
    """Build and authenticate a complete DAG without any producer fallback."""

    by_digest: dict[str, ObligationEvidenceLeaf] = {}
    for raw_leaf in leaves:
        leaf = (
            raw_leaf
            if isinstance(raw_leaf, ObligationEvidenceLeaf)
            else validate_obligation_leaf(raw_leaf)
        )
        # Reparse dataclass instances too; callers cannot bypass validation by
        # constructing one directly.
        leaf = validate_obligation_leaf(leaf.projection())
        previous = by_digest.get(leaf.leaf_sha256)
        if previous is not None and previous.projection() != leaf.projection():
            raise ObligationEvidenceError("one leaf identity has conflicting objects")
        by_digest[leaf.leaf_sha256] = leaf
    if not by_digest:
        raise ObligationEvidenceError("obligation graph has no leaves")
    roots = _sha256s(root_leaf_sha256s, "graph root", nonempty=True)
    missing_roots = sorted(set(roots) - set(by_digest))
    if missing_roots:
        raise ObligationEvidenceError(
            "obligation graph is missing root leaves: " + ", ".join(missing_roots)
        )
    for leaf in by_digest.values():
        missing = sorted(set(leaf.depends_on) - set(by_digest))
        if missing:
            raise ObligationEvidenceError(
                f"leaf {leaf.leaf_sha256} is missing dependencies: "
                + ", ".join(missing)
            )

    reachable: set[str] = set()
    frontier = list(roots)
    while frontier:
        digest = frontier.pop()
        if digest in reachable:
            continue
        reachable.add(digest)
        frontier.extend(by_digest[digest].depends_on)
    unreachable = sorted(set(by_digest) - reachable)
    if unreachable:
        raise ObligationEvidenceError(
            "obligation graph contains leaves unreachable from its roots: "
            + ", ".join(unreachable)
        )

    # Kahn's algorithm produces dependencies before dependents.  Sorting each
    # frontier makes the graph identity and planner order deterministic.
    remaining = {digest: set(leaf.depends_on) for digest, leaf in by_digest.items()}
    ordered: list[str] = []
    while remaining:
        ready = sorted(digest for digest, deps in remaining.items() if not deps)
        if not ready:
            raise ObligationEvidenceError("obligation graph contains a cycle")
        ordered.extend(ready)
        for digest in ready:
            del remaining[digest]
        ready_set = set(ready)
        for dependencies in remaining.values():
            dependencies.difference_update(ready_set)

    closure_leaves = [
        leaf for leaf in by_digest.values() if leaf.kind is ObligationKind.PAPER_CLOSURE
    ]
    accepting = (
        len(roots) == 1 and by_digest[roots[0]].kind is ObligationKind.PAPER_CLOSURE
    )
    if closure_leaves and (not accepting or closure_leaves != [by_digest[roots[0]]]):
        raise ObligationEvidenceError(
            "an accepted graph requires exactly one paper-closure leaf as its sole root"
        )
    schema = (
        ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA
        if accepting
        else OBLIGATION_EVIDENCE_GRAPH_SCHEMA
    )
    if accepting:
        closure = by_digest[roots[0]]
        semantic_leaves = {
            digest: leaf
            for digest, leaf in by_digest.items()
            if digest != closure.leaf_sha256
        }
        semantic_graph = build_obligation_graph(
            semantic_leaves.values(),
            root_leaf_sha256s=closure.depends_on,
        )
        if (
            semantic_graph.graph_sha256
            != closure.semantic_payload["semantic_graph_sha256"]
        ):
            raise ObligationEvidenceError(
                "paper-closure root names a different semantic obligation graph"
            )
    material = {
        "schema": schema,
        "leaf_sha256s": sorted(by_digest),
        "root_leaf_sha256s": list(roots),
    }
    return ObligationEvidenceGraph(
        leaves=MappingProxyType(by_digest),
        root_leaf_sha256s=roots,
        topological_leaf_sha256s=tuple(ordered),
        graph_sha256=portable_evidence_sha256(material),
    )


def validate_obligation_graph(
    value: object,
    *,
    leaves: Mapping[str, object],
) -> ObligationEvidenceGraph:
    """Authenticate a persisted graph index against its independently loaded leaves."""

    if not isinstance(value, Mapping):
        raise ObligationEvidenceError("obligation graph index is not an object")
    required = {
        "schema",
        "acceptance_credential",
        "integrity_and_planning_only",
        "leaf_sha256s",
        "root_leaf_sha256s",
        "graph_sha256",
    }
    if (
        set(value) != required
        or value.get("schema")
        not in {
            OBLIGATION_EVIDENCE_GRAPH_SCHEMA,
            ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA,
        }
        or not isinstance(value.get("leaf_sha256s"), list)
        or not isinstance(value.get("root_leaf_sha256s"), list)
    ):
        raise ObligationEvidenceError("obligation graph index fields are malformed")
    required_digests = _sha256s(value["leaf_sha256s"], "graph leaf", nonempty=True)
    if set(leaves) != set(required_digests):
        raise ObligationEvidenceError(
            "loaded obligation leaves disagree with the graph index"
        )
    parsed_leaves = []
    for digest in required_digests:
        leaf = validate_obligation_leaf(leaves[digest])
        if leaf.leaf_sha256 != digest:
            raise ObligationEvidenceError(
                "loaded obligation leaf is stored under the wrong identity"
            )
        parsed_leaves.append(leaf)
    graph = build_obligation_graph(
        parsed_leaves,
        root_leaf_sha256s=value["root_leaf_sha256s"],
    )
    accepting = graph.schema == ACCEPTED_OBLIGATION_EVIDENCE_GRAPH_SCHEMA
    if (
        value.get("schema") != graph.schema
        or value.get("acceptance_credential") is not accepting
        or value.get("integrity_and_planning_only") is accepting
    ):
        raise ObligationEvidenceError(
            "obligation graph acceptance fields are malformed"
        )
    if _sha256(value.get("graph_sha256"), "graph identity") != graph.graph_sha256:
        raise ObligationEvidenceError("obligation graph identity is corrupt")
    return graph


def merge_obligation_graphs(
    graphs: Iterable[ObligationEvidenceGraph],
) -> ObligationEvidenceGraph:
    """Union independently projected subgraphs under the same leaf schemas."""

    leaves: dict[str, ObligationEvidenceLeaf] = {}
    roots: set[str] = set()
    count = 0
    for raw_graph in graphs:
        count += 1
        graph = validate_obligation_graph(
            raw_graph.projection(),
            leaves={
                digest: leaf.projection() for digest, leaf in raw_graph.leaves.items()
            },
        )
        for digest, leaf in graph.leaves.items():
            previous = leaves.get(digest)
            if previous is not None and previous.projection() != leaf.projection():
                raise ObligationEvidenceError(
                    "obligation subgraphs disagree on one leaf object"
                )
            leaves[digest] = leaf
        roots.update(graph.root_leaf_sha256s)
    if count == 0:
        raise ObligationEvidenceError("no obligation subgraphs were supplied")
    return build_obligation_graph(leaves.values(), root_leaf_sha256s=roots)


@dataclass(frozen=True)
class ObligationGraphDiff:
    """Pure required-versus-available leaf comparison."""

    reusable_leaf_sha256s: tuple[str, ...]
    missing_leaf_sha256s: tuple[str, ...]
    corrupt_leaf_sha256s: tuple[str, ...]
    blocked_by_missing: Mapping[str, tuple[str, ...]]

    @property
    def complete(self) -> bool:
        return not self.missing_leaf_sha256s and not self.corrupt_leaf_sha256s


def diff_obligation_graph(
    required: ObligationEvidenceGraph,
    available: Mapping[str, object],
) -> ObligationGraphDiff:
    """Return exact reusable/missing leaves without reading or producing work."""

    required = validate_obligation_graph(
        required.projection(),
        leaves={digest: leaf.projection() for digest, leaf in required.leaves.items()},
    )
    reusable: set[str] = set()
    corrupt: set[str] = set()
    for digest in required.topological_leaf_sha256s:
        raw = available.get(digest)
        if raw is None:
            continue
        try:
            leaf = validate_obligation_leaf(raw)
        except ObligationEvidenceError:
            corrupt.add(digest)
            continue
        if (
            leaf.leaf_sha256 != digest
            or leaf.projection() != required.leaves[digest].projection()
        ):
            corrupt.add(digest)
            continue
        reusable.add(digest)
    missing = set(required.leaves) - reusable - corrupt
    unavailable = missing | corrupt
    blocked: dict[str, tuple[str, ...]] = {}
    for digest in required.topological_leaf_sha256s:
        dependencies = tuple(
            dependency
            for dependency in required.leaves[digest].depends_on
            if dependency in unavailable
        )
        if dependencies:
            blocked[digest] = dependencies
    order = {
        digest: index for index, digest in enumerate(required.topological_leaf_sha256s)
    }
    ordered = lambda values: tuple(sorted(values, key=order.__getitem__))
    return ObligationGraphDiff(
        reusable_leaf_sha256s=ordered(reusable),
        missing_leaf_sha256s=ordered(missing),
        corrupt_leaf_sha256s=ordered(corrupt),
        blocked_by_missing=MappingProxyType(blocked),
    )
