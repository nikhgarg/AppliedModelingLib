"""Complete source-claim semantic contracts for theorem realization.

The authoritative closeout question is not whether a node happens to look
like a proposition, a model field, or ordinary data.  For every material part
of a paper-facing theorem realization, the audit must hold a current semantic
provenance disposition: an exact source claim, an explicit source correction
or additional assumption, a source-domain correspondence, or a Lean-checked
derivation.  This includes carrier and function-valued inputs, record fields,
result certificates, and dependent guards. Transitive proof/local dependency
closure is checked by Lean's recursive Spec graph.

Structural extraction is deliberately only a *discovery* aid.  It can make an
unaccounted component visible, but it never grants an exemption based on a
field, declaration, binder, file, or objective name.  The legacy filename and
compatibility aliases remain so older source-record artifacts can be read;
new callers use the source-claim semantic-contract API below.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from typing import Any, Iterable, Mapping


SEMANTIC_RESTRICTION_OBLIGATION_FIELD = "semantic_restriction_obligation"
SEMANTIC_RESTRICTION_OBLIGATION_SCHEMA = 1
SOURCE_CLAIM_SEMANTIC_CONTRACT_FIELD = "source_claim_semantic_contract"
SOURCE_CLAIM_SEMANTIC_CONTRACTS_FIELD = "source_claim_semantic_contracts"
SOURCE_CLAIM_SEMANTIC_CONTRACT_SCHEMA = 1
SOURCE_CLAIM_COMPONENT_ROLE_FIELD = "source_claim_component_role"
SOURCE_CLAIM_COMPONENT_SHA256_FIELD = "source_claim_component_sha256"
SOURCE_CLAIM_COMPONENT_OCCURRENCE_FIELD = "source_claim_component_occurrence"
SOURCE_CLAIM_COMPONENT_STRUCTURAL_TYPE_SHA256_FIELD = (
    "source_claim_component_structural_type_sha256"
)
EXACT_SOURCE_CLAIM_ROUTE = "exact_source_claim"
APPROVED_SOURCE_CORRECTION_ROUTE = "approved_source_correction_or_additional_assumption"
SOURCE_DOMAIN_CORRESPONDENCE_ROUTE = "source_domain_correspondence"
# This route is deliberately receipt-only.  A current, source-scoped
# source-to-Spec correspondence can authorize every occurrence in the same
# canonical transparent Spec surface without manufacturing one sidecar JSON
# contract per binder.  The receipt is issued by the provenance projector only
# after the strict source-to-Spec lane and the generated parent association
# both validate.
TRANSPARENT_SPEC_FULL_SURFACE_CORRESPONDENCE_ROUTE = (
    "transparent_spec_full_surface_correspondence"
)
CHECKED_LEAN_DERIVATION_ROUTE = "checked_lean_derivation"
TRUSTED_EXTERNAL_SCAFFOLDING_ROUTE = "trusted_external_scaffolding"
# Compatibility for already-issued sidecars. New producer/user-facing policy
# uses the semantic-restriction spelling; the legacy field remains readable
# until its artifacts are deliberately migrated.
OPERATIONAL_PROP_OBLIGATION_FIELD = "operational_prop_obligation"
OPERATIONAL_PROP_OBLIGATION_SCHEMA = SEMANTIC_RESTRICTION_OBLIGATION_SCHEMA
EXPLICIT_SOURCE_ASSUMPTION_ROUTE = "explicit_semantically_matched_source_assumption"
CHECKED_LEAN_BRIDGE_ROUTE = "checked_lean_bridge"
FORMALIZATION_REGULARITY_CLASSIFICATION = "approved_formalization_regularity"

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_EXACT_LOCATOR_RE = re.compile(
    r"(?:\b[\w./-]+\.(?:tex|txt|md|pdf):\d+|"
    r"\b(?:Appendix|Theorem|Lemma|Proposition|Corollary|Definition|Equation|Section)\s+)",
    re.I,
)
_BARE_REFERENCE_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_IDENTIFIER_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'.]*$")

# These are carrier constructors, not paper-local aliases.  An unknown local
# head is deliberately not presumed to be data; an old artifact then needs a
# fresh Lean sort receipt before it can receive closeout credit.
_KNOWN_DATA_HEADS = frozenset(
    {
        "Any",
        "Bool",
        "ByteArray",
        "Char",
        "ENNReal",
        "Equiv.Perm",
        "Fin",
        "Finset",
        "Fintype",
        "Float",
        "Int",
        "Kernel",
        "List",
        "Measure",
        "MeasureTheory.Measure",
        "Multiset",
        "Nat",
        "Option",
        "PMF",
        "Perm",
        "Prod",
        "Rat",
        "Real",
        "Set",
        "Sort",
        "String",
        "Subtype",
        "Sum",
        "Type",
        "Unit",
        "\u2115",
        "\u2124",
        "\u211a",
        "\u211d",
        "\u211d\u22650",
        "\u211d\u22650\u221e",
    }
)
_LOGICAL_SURFACE_TOKENS = (
    "\u2200",
    "\u2203",
    "\u2192",
    "\u2194",
    "\u2227",
    "\u2228",
    "\u2260",
    "\u2264",
    "\u2265",
    "\u2208",
    "\u2209",
    "\u2286",
    "\u2282",
    "\u2287",
    "\u2283",
)


@dataclass(frozen=True)
class CheckedLeanBridgeReceipt:
    """A Lean-owned bridge result, never a sidecar assertion.

    A resolver constructs this only after Lean has checked the declaration's
    target type and dependency route.  The sidecar names the same route, but
    cannot manufacture this receipt by writing ``lean_checked: true``.
    """

    component_key: str
    declaration: str
    component_sha256: str
    field_type_sha256: str
    source_antecedent_keys: frozenset[str]


@dataclass(frozen=True)
class SourceDomainCorrespondenceReceipt:
    """A current source-domain/model correspondence for one material node.

    The receipt is produced only after the semantic-model review lane has
    checked its exact source association and elaborated review route.  It is
    intentionally separate from a label such as ``nonpropositional_witness``:
    a carrier, function, ``Fin n``, or record value is material whenever it is
    part of a theorem realization.
    """

    component_key: str
    component_sha256: str
    source_model_judgment_key: str


@dataclass(frozen=True)
class StrictSourceSpecCorrespondenceReceipt:
    """One current strict source-claim to canonical-Spec correspondence.

    The repository mints this only after Lean has checked the complete
    canonical Spec closure for a source-map item in the strict closeout scope.
    It is deliberately a runtime receipt: checked-in map data cannot claim
    that a stale closure is current by copying these fields.
    """

    source_item_key: str
    spec_declaration: str
    evidence_declaration: str
    evidence_mode: str
    semantic_shape: str
    source_atoms_sha256: str
    item_identity_sha256: str
    spec_closure_sha256: str
    spec_surface_sha256: str
    closure_environment_sha256: str
    authority: str = "persisted_correspondence_v1"


@dataclass(frozen=True)
class TransparentSpecFullSurfaceCorrespondenceReceipt:
    """A current full-surface source-to-transparent-Spec authorization.

    Unlike an item-level sidecar assertion, this is a deterministic runtime
    receipt.  It is issued only when a strict named source claim's current
    atom-level correspondence covers the canonical root Spec surface and a
    generated direct-evidence/transparent-Spec parent pair authenticates the
    occurrence.  Keeping the source correspondence, parent association, and
    generated occurrence identities together prevents a root-level source
    theorem from being reused for a nearby Spec, stale closure, or unrelated
    component.
    """

    component_key: str
    source_judgment_key: str
    component_sha256: str
    structural_type_sha256: str
    semantic_model_judgment_key: str
    source_item_keys: tuple[str, ...]
    source_spec_correspondence_item_identity_sha256s: tuple[tuple[str, str], ...]
    source_spec_correspondence_closure_sha256s: tuple[tuple[str, str], ...]
    source_spec_correspondence_surface_sha256s: tuple[tuple[str, str], ...]
    source_spec_correspondence_environment_sha256s: tuple[tuple[str, str], ...]
    parent_semantic_association_sha256: str
    parent_source_claim_atom_association_sha256: str
    parent_source_claim_atom_semantic_association_sha256: str
    component_source_contract_association_sha256: str


@dataclass(frozen=True)
class SemanticContractExecutableTerminalComponentReceipt:
    """One exact occurrence covered by an executable-terminal contract route.

    This is deliberately distinct from
    :class:`TransparentSpecFullSurfaceCorrespondenceReceipt`.  The latter
    certifies an atom-complete strict source-to-Spec closure.  This receipt
    instead records the narrower route for a direct source semantic contract
    whose transparent Spec reaches a structurally identified *executable*
    terminal.  Its issuer has checked the exact source identity, direct
    theorem/Spec match, current signature and dependency fingerprint,
    semantic-model review, and full terminal occurrence set inside one
    immutable closeout transaction.

    It is runtime-only.  A checked-in map, a terminal declaration spelling, or
    a reviewer label cannot manufacture occurrence credit.
    """

    component_key: str
    source_judgment_key: str
    component_sha256: str
    structural_type_sha256: str
    semantic_model_judgment_key: str
    component_source_contract_association_sha256: str
    source_item_key: str
    source_item_semantic_sha256: str
    source_map_item_sha256: str
    spec_declaration: str
    evidence_declaration: str
    evidence_elaborated_signature_sha256: str
    evidence_semantic_dependency_sha256: str
    terminal_receipt_sha256: str


@dataclass(frozen=True)
class RecursiveFieldExplicitParentComponentReceipt:
    """One exact source-model field occurrence closed inside a live run.

    A generated ``recursive_field_explicit_parent_route`` is deliberately not
    itself a component contract: it describes the narrow source scope that a
    reviewer may assess.  This receipt is minted only after the closeout
    transaction has checked that route against current map/ledger bytes, the
    exact direct parent signature and semantic-model review, and the current
    field judgment.  It then binds that result to one generated material
    occurrence.  Persisted JSON or a reviewer-supplied route label cannot
    create this capability.
    """

    component_key: str
    source_judgment_key: str
    component_sha256: str
    structural_type_sha256: str
    recursive_field_parent_route_sha256: str
    source_item_key: str
    source_item_semantic_sha256: str
    source_map_item_sha256: str
    root_record: str
    field_scope_sha256: str
    convention_id: str
    convention_sha256: str
    parent_semantic_model_judgment_key: str
    parent_qualified_declaration: str
    parent_declaration_sha256: str
    parent_elaborated_signature_sha256: str
    parent_source_association_sha256: str


def recursive_field_explicit_parent_component_receipt_matches(
    item: Mapping[str, Any],
    receipt: RecursiveFieldExplicitParentComponentReceipt,
) -> bool:
    """Match a runtime field receipt to one generated material component.

    This is intentionally a complete structural/provenance join.  It does
    not examine a binder, declaration suffix, source kind, or reviewer prose.
    The transaction issuer has checked the parent semantic review; this gate
    additionally requires every current route pin to be the one that issued
    the occurrence receipt.
    """

    if not isinstance(receipt, RecursiveFieldExplicitParentComponentReceipt):
        return False
    component_key = str(item.get("judgment_key") or "").strip()
    source_judgment_key = _field_key(item)
    component_sha = source_claim_component_sha256(item)
    structural_sha = field_type_sha256(item)
    route = item.get("recursive_field_explicit_parent_route")
    if (
        not component_key
        or not source_judgment_key
        or not isinstance(route, Mapping)
        or str(item.get("source_component_section") or "").strip()
        != "recursive_field_items"
        or str(item.get("source_claim_component_kind") or "").strip()
        != "recursive_record_field"
    ):
        return False
    route_sha = str(route.get("association_sha256") or "").strip().lower()
    source_item_key = str(route.get("source_item") or "").strip()
    root_record = str(route.get("root_record") or "").strip()
    field_scope_sha = str(route.get("field_scope_sha256") or "").strip().lower()
    convention_id = str(route.get("convention_id") or "").strip()
    convention_sha = str(route.get("convention_sha256") or "").strip().lower()
    parent_identity = route.get("parent_reviewed_declaration_identity")
    parent_signature = route.get("parent_elaborated_signature_identity")
    parent_semantic_model_judgment_key = str(
        route.get("parent_semantic_model_judgment_key") or ""
    ).strip()
    identities = route.get("source_item_identities")
    if (
        not all(
            _SHA256_RE.fullmatch(value)
            for value in (
                component_sha,
                structural_sha,
                route_sha,
                field_scope_sha,
                convention_sha,
            )
        )
        or not source_item_key
        or not root_record
        or not convention_id
        or not parent_semantic_model_judgment_key
        or not isinstance(parent_identity, Mapping)
        or not isinstance(parent_signature, Mapping)
        or not isinstance(identities, list)
        or len(identities) != 1
        or not isinstance(identities[0], Mapping)
    ):
        return False
    source_identity = identities[0]
    source_semantic_sha = str(
        source_identity.get("source_semantic_sha256") or ""
    ).strip().lower()
    source_map_sha = str(
        source_identity.get("source_map_item_sha256") or ""
    ).strip().lower()
    parent_qualified = str(
        parent_identity.get("qualified_declaration") or ""
    ).strip()
    parent_declaration_sha = str(
        parent_identity.get("declaration_sha256") or ""
    ).strip().lower()
    parent_signature_qualified = str(
        parent_signature.get("qualified_declaration") or ""
    ).strip()
    parent_signature_sha = str(
        parent_signature.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    parent_association_sha = str(
        route.get("parent_source_association_sha256") or ""
    ).strip().lower()
    if (
        str(source_identity.get("source_key") or "").strip() != source_item_key
        or parent_signature_qualified != parent_qualified
        or not parent_qualified
        or not all(
            _SHA256_RE.fullmatch(value)
            for value in (
                source_semantic_sha,
                source_map_sha,
                parent_declaration_sha,
                parent_signature_sha,
                parent_association_sha,
            )
        )
    ):
        return False
    return (
        receipt.component_key == component_key
        and receipt.source_judgment_key == source_judgment_key
        and receipt.component_sha256 == component_sha
        and receipt.structural_type_sha256 == structural_sha
        and receipt.recursive_field_parent_route_sha256 == route_sha
        and receipt.source_item_key == source_item_key
        and receipt.source_item_semantic_sha256 == source_semantic_sha
        and receipt.source_map_item_sha256 == source_map_sha
        and receipt.root_record == root_record
        and receipt.field_scope_sha256 == field_scope_sha
        and receipt.convention_id == convention_id
        and receipt.convention_sha256 == convention_sha
        and receipt.parent_semantic_model_judgment_key
        == parent_semantic_model_judgment_key
        and receipt.parent_qualified_declaration == parent_qualified
        and receipt.parent_declaration_sha256 == parent_declaration_sha
        and receipt.parent_elaborated_signature_sha256 == parent_signature_sha
        and receipt.parent_source_association_sha256 == parent_association_sha
    )


@dataclass(frozen=True)
class SourceClaimAtomReceipt:
    """Current identity of one source-theorem clause atom.

    A whole source-item digest is intentionally insufficient for a compound
    theorem: it cannot show which quantified/existence/uniqueness clause a
    material Lean component realizes.  New contracts bind this atom identity;
    parent-item routes remain compatibility-only for pre-atom artifacts.
    """

    source_item_key: str
    atom_id: str
    atom_semantic_sha256: str
    source_locator: str


def source_claim_component_sha256(item: Mapping[str, Any]) -> str:
    """Return the generated structural identity for one material component."""

    supplied = str(item.get(SOURCE_CLAIM_COMPONENT_SHA256_FIELD) or "").strip().lower()
    if _SHA256_RE.fullmatch(supplied):
        return supplied
    return field_type_sha256(item)


def canonical_field_type(item: Mapping[str, Any]) -> str:
    """Return a stable, spelling-preserving type surface for one field."""

    raw = (
        item.get("expanded_type")
        or item.get("type")
        or item.get("field_type")
        or ""
    )
    text = re.sub(r"\s+", " ", str(raw).strip())
    for source, target in (
        ("<->", "\u2194"),
        ("->", "\u2192"),
        ("/\\", "\u2227"),
        ("\\/", "\u2228"),
        ("<=", "\u2264"),
        (">=", "\u2265"),
        ("!=", "\u2260"),
    ):
        text = text.replace(source, target)
    text = re.sub(r"(?<![\w'])forall(?![\w'])", "\u2200", text)
    text = re.sub(r"(?<![\w'])exists(?![\w'])", "\u2203", text)
    text = re.sub(r"\s*([(){}\[\],:.])\s*", r"\1", text)
    text = re.sub(r"\s*(\u2192|\u2194|\u2227|\u2228|=|\u2260|\u2264|\u2265|<|>)\s*", r"\1", text)
    return text


def field_type_sha256(item: Mapping[str, Any]) -> str:
    """Return the generated structural type identity for one obligation route.

    Fresh source-record artifacts carry an alpha-normalized digest derived from
    the enclosing structural context.  Cached artifacts retain the conservative
    canonical-text fallback so ordinary legacy evidence can be inspected, but
    new route receipts never need to bind incidental binder spelling.
    """

    structural = str(item.get("structural_type_sha256") or "").strip().lower()
    if _SHA256_RE.fullmatch(structural):
        return structural

    text = canonical_field_type(item)
    if not text:
        return ""
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _top_level_terminal(text: str) -> str:
    """Return an outer arrow codomain without parsing names as semantics."""

    depth = 0
    last_arrow = -1
    for index, character in enumerate(text):
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth = max(depth - 1, 0)
        elif depth == 0 and character == "\u2192":
            last_arrow = index
    return text[last_arrow + 1 :].strip() if last_arrow >= 0 else text.strip()


def recursive_field_proposition_status(item: Mapping[str, Any]) -> str:
    """Classify a recursive leaf as proposition, data, or refresh-required.

    ``proposition`` is determined from a generated Lean sort receipt when one
    exists, otherwise from logical constructors in the type surface.  The
    latter covers old v10 fields such as universal/implicational calculus,
    probability, and optimization assertions without relying on local names.
    """

    for field in ("proposition_sort", "field_proposition_status"):
        explicit = item.get(field)
        if explicit in {"proposition", "true", True}:
            return "proposition"
        if explicit in {"data", "nonproposition", "false", False}:
            return "data_or_container"
        if explicit == "unknown":
            return "unknown"

    nested = item.get("nested_structures")
    if isinstance(nested, list) and any(str(value).strip() for value in nested):
        return "data_or_container"

    text = canonical_field_type(item)
    if not text:
        return "unknown"

    # A predicate-valued *data* argument has terminal type Prop.  It is not a
    # proof that the predicate holds, so it remains outside this leaf rule.
    terminal = _top_level_terminal(text)
    if terminal == "Prop" and "\u2200" not in text and "\u2203" not in text:
        return "data_or_container"

    masked = text.replace("\u211d\u22650\u221e", "Carrier").replace("\u211d\u22650", "Carrier")
    if any(token in masked for token in _LOGICAL_SURFACE_TOKENS) or "=" in masked:
        return "proposition"
    if re.search(r"\b(?:Prop|True|False|And|Or|Iff|Exists)\b", masked):
        return "proposition"

    head = re.match(r"^@?([A-Za-z_][A-Za-z0-9_'.]*|[\u2115\u2124\u211a\u211d])", text)
    if head is not None and head.group(1) in _KNOWN_DATA_HEADS:
        return "data_or_container"
    return "unknown"


def is_recursive_semantic_restriction(item: Mapping[str, Any]) -> bool:
    """Whether the cached/generated field visibly carries a restriction."""

    return recursive_field_proposition_status(item) == "proposition"


def is_recursive_operational_prop_field(item: Mapping[str, Any]) -> bool:
    """Compatibility alias for :func:`is_recursive_semantic_restriction`."""

    return is_recursive_semantic_restriction(item)


def theorem_facing_semantic_restriction_status(item: Mapping[str, Any]) -> str:
    """Return a compatibility status for one semantic-contract component.

    ``data_or_container`` is retained only for legacy, non-component callers.
    Every item emitted into ``theorem_realization_component_items`` or the
    canonical theorem-facing ledger is material by default. In particular,
    ``carrier_coherence_only`` means that a source-domain correspondence is
    required; it is not an exemption.
    """

    component_role = str(item.get(SOURCE_CLAIM_COMPONENT_ROLE_FIELD) or "").strip()
    restriction_role = str(item.get("semantic_restriction_role") or "").strip()
    role = str(item.get("theorem_facing_semantic_role") or "").strip()
    status = recursive_field_proposition_status(item)
    if component_role == "trusted_external_scaffolding":
        return "trusted_scaffolding"
    if component_role in {"opaque_or_unmapped", "unclassified"}:
        return "unknown"
    if component_role == "material":
        if restriction_role in {"requires_source_or_lean_closure", "restriction"}:
            return "proof_bearing"
        if restriction_role in {"unclassified", "unknown"}:
            return "unknown"
        if status == "proposition":
            return "proof_bearing"
        # A known carrier, function, selector, or record value still changes
        # the source theorem's domain. Its provenance is a correspondence,
        # not a free pass from a text/type classifier.
        return "source_domain"
    if restriction_role in {"requires_source_or_lean_closure", "restriction"}:
        return "proof_bearing"
    if restriction_role == "carrier_coherence_only":
        return "source_domain"
    if restriction_role in {"unclassified", "unknown"}:
        return "unknown"
    if role in {"proof_bearing", "semantic_restriction"}:
        return "proof_bearing"
    if role == "unclassified_theorem_input":
        return "unknown"
    if status == "proposition":
        return "proof_bearing"
    if status == "unknown":
        return "unknown"
    return "data_or_container"


def theorem_facing_proof_obligation_status(item: Mapping[str, Any]) -> str:
    """Compatibility alias for the semantic-restriction classifier."""

    return theorem_facing_semantic_restriction_status(item)


def _nonempty_text(value: object) -> bool:
    text = str(value or "").strip()
    return bool(text and not _BARE_REFERENCE_RE.fullmatch(text))


def _nonempty_unique_strings(value: object) -> tuple[list[str], str]:
    if not isinstance(value, list) or not value:
        return [], "must be a nonempty list"
    values = [str(item).strip() for item in value]
    if not all(values) or len(values) != len(set(values)):
        return [], "must contain unique nonempty strings"
    return values, ""


def _field_key(item: Mapping[str, Any]) -> str:
    return str(
        item.get("source_judgment_key") or item.get("judgment_key") or ""
    ).strip()


def _explicit_source_assumption_errors(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    obligation: Mapping[str, Any],
    *,
    source_item_semantic_sha256_by_key: Mapping[str, str] | None,
) -> list[str]:
    errors: list[str] = []
    if str(judgment.get("classification") or "").strip() not in {
        "validated_source_assumption",
        "approved_corrected_condition",
        "approved_source_convention",
    }:
        errors.append(
            "explicit source-assumption route requires `validated_source_assumption` or `approved_corrected_condition`"
        )
    disposition = str(judgment.get("source_target_disposition") or "").strip()
    expected_dispositions = {
        "validated_source_assumption": "literal_source_match",
        "approved_corrected_condition": "approved_corrected_target",
        "approved_source_convention": "approved_source_convention",
    }
    classification = str(judgment.get("classification") or "").strip()
    if classification in expected_dispositions and disposition != expected_dispositions[classification]:
        errors.append(
            "explicit source-assumption route has no matching source_target_disposition"
        )

    source = obligation.get("source_assumption")
    if not isinstance(source, Mapping):
        return errors + ["explicit source-assumption route needs a `source_assumption` object"]
    key = str(source.get("source_item_key") or "").strip()
    semantic_sha = str(source.get("source_item_semantic_sha256") or "").strip().lower()
    locator = str(source.get("source_locator") or "").strip()
    if not key:
        errors.append("source_assumption.source_item_key is required")
    if not _SHA256_RE.fullmatch(semantic_sha):
        errors.append("source_assumption.source_item_semantic_sha256 is missing or malformed")
    elif source_item_semantic_sha256_by_key is None:
        errors.append("explicit source-assumption route needs the current source-item semantic index")
    elif source_item_semantic_sha256_by_key.get(key) != semantic_sha:
        errors.append("source_assumption does not match the current source-item semantic identity")
    if not _EXACT_LOCATOR_RE.search(locator):
        errors.append("source_assumption.source_locator must be an exact source locator")
    for field in ("source_formula", "semantic_match"):
        if not _nonempty_text(source.get(field)):
            errors.append(
                "source_assumption."
                + field
                + " must state formula-level source/Lean evidence, not a name-only reference"
            )
    return errors


def _checked_lean_bridge_errors(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    obligation: Mapping[str, Any],
    *,
    current_exact_source_antecedent_keys: Iterable[str],
    checked_lean_bridge_receipts: Iterable[CheckedLeanBridgeReceipt],
) -> list[str]:
    errors: list[str] = []
    if str(judgment.get("classification") or "").strip() != "proved_from_primitives":
        errors.append("checked Lean bridge route requires `proved_from_primitives`")
    bridge = obligation.get("bridge")
    if not isinstance(bridge, Mapping):
        return errors + ["checked Lean bridge route needs a `bridge` object"]
    declaration = str(bridge.get("declaration") or "").strip()
    if not _IDENTIFIER_RE.fullmatch(declaration) or "." not in declaration:
        errors.append("bridge.declaration must be one fully qualified Lean declaration")
    supplied_type_sha = str(bridge.get("field_type_sha256") or "").strip().lower()
    expected_type_sha = field_type_sha256(item)
    if supplied_type_sha != expected_type_sha:
        errors.append("bridge.field_type_sha256 does not bind the current recursive field type")
    supplied_component_sha = str(
        bridge.get("component_sha256") or ""
    ).strip().lower()
    expected_component_sha = source_claim_component_sha256(item)
    if supplied_component_sha != expected_component_sha:
        errors.append(
            "bridge.component_sha256 does not bind the current generated component occurrence"
        )
    antecedents, antecedent_error = _nonempty_unique_strings(
        bridge.get("source_antecedent_keys")
    )
    if antecedent_error:
        errors.append("bridge.source_antecedent_keys " + antecedent_error)
        antecedents = []
    component_key = str(item.get("judgment_key") or "").strip()
    if component_key and component_key in antecedents:
        errors.append("bridge.source_antecedent_keys may not include the field being discharged")
    unvalidated = sorted(
        set(antecedents) - set(current_exact_source_antecedent_keys)
    )
    if unvalidated:
        errors.append(
            "bridge source antecedent(s) lack current explicit source-assumption evidence: "
            + ", ".join(unvalidated)
        )
    expected = CheckedLeanBridgeReceipt(
        component_key=component_key,
        declaration=declaration,
        component_sha256=expected_component_sha,
        field_type_sha256=expected_type_sha,
        source_antecedent_keys=frozenset(antecedents),
    )
    if expected not in set(checked_lean_bridge_receipts):
        errors.append(
            "bridge has no matching Lean-generated declaration/type/dependency receipt"
        )
    return errors


def _semantic_restriction_obligation(
    judgment: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Read the canonical restriction route, with a legacy artifact fallback."""

    canonical = judgment.get(SEMANTIC_RESTRICTION_OBLIGATION_FIELD)
    if canonical is not None:
        return canonical if isinstance(canonical, Mapping) else None
    legacy = judgment.get(OPERATIONAL_PROP_OBLIGATION_FIELD)
    return legacy if isinstance(legacy, Mapping) else None


def _current_component_sha256s(
    item: Mapping[str, Any],
    current_component_sha256s_by_source_judgment_key: Mapping[str, Iterable[str]] | None,
) -> tuple[set[str] | None, list[str]]:
    """Read the complete current occurrence set for an original judgment key."""

    key = _field_key(item)
    component_sha = source_claim_component_sha256(item)
    if not key or not component_sha:
        return None, ["component has no generated source key or occurrence identity"]
    if current_component_sha256s_by_source_judgment_key is None:
        return None, [
            "component contract gate needs the complete current occurrence ledger; "
            "a source judgment cannot self-certify that it is unique"
        ]
    raw_current = current_component_sha256s_by_source_judgment_key.get(key)
    if raw_current is None:
        return None, [
            "component occurrence is absent from the current theorem-realization ledger"
        ]
    current = {str(value).strip().lower() for value in raw_current}
    if not current or any(not _SHA256_RE.fullmatch(value) for value in current):
        return None, ["current theorem-realization occurrence ledger is malformed"]
    if component_sha not in current:
        return None, [
            "component occurrence identity does not match the current theorem-realization ledger"
        ]
    return current, []


def _source_claim_semantic_contract(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    current_component_sha256s_by_source_judgment_key: Mapping[str, Iterable[str]] | None,
) -> tuple[Mapping[str, Any] | None, list[str]]:
    """Select exactly one occurrence-indexed semantic contract fail-closed.

    A single source-record judgment can describe several material components.
    New sidecars therefore index contracts by the generator-owned occurrence
    hash.  The historical scalar field is accepted only when the live ledger
    proves that the original judgment owns exactly one occurrence.
    """

    component_sha = source_claim_component_sha256(item)
    current, ledger_errors = _current_component_sha256s(
        item, current_component_sha256s_by_source_judgment_key
    )
    if ledger_errors:
        return None, ledger_errors

    indexed = judgment.get(SOURCE_CLAIM_SEMANTIC_CONTRACTS_FIELD)
    scalar = judgment.get(SOURCE_CLAIM_SEMANTIC_CONTRACT_FIELD)
    if indexed is not None:
        if scalar is not None:
            return None, [
                "source judgment must use either component-indexed contracts or one unique scalar contract, not both"
            ]
        if isinstance(indexed, Mapping):
            selected = indexed.get(component_sha)
            if not isinstance(selected, Mapping):
                return None, [
                    "component-indexed source-claim contract has no exact entry for this occurrence"
                ]
            return selected, []
        if isinstance(indexed, list):
            selected = [
                value
                for value in indexed
                if isinstance(value, Mapping)
                and str(value.get("component_sha256") or "").strip().lower()
                == component_sha
            ]
            if len(selected) != 1:
                return None, [
                    "component-indexed source-claim contracts must contain exactly one entry for this occurrence"
                ]
            return selected[0], []
        return None, [
            "source_claim_semantic_contracts must be a component-SHA map or list"
        ]

    if scalar is None:
        return None, []
    if not isinstance(scalar, Mapping):
        return None, ["source_claim_semantic_contract must be an object"]
    if current != {component_sha}:
        return None, [
            "scalar source-claim contract is ambiguous because this source judgment has multiple current component occurrences; use source_claim_semantic_contracts indexed by component_sha256"
        ]
    return scalar, []


def _contract_component_binding_errors(
    item: Mapping[str, Any], contract: Mapping[str, Any]
) -> list[str]:
    errors: list[str] = []
    if contract.get("schema") != SOURCE_CLAIM_SEMANTIC_CONTRACT_SCHEMA:
        return ["source-claim semantic contract has an unsupported schema"]
    supplied = str(contract.get("component_sha256") or "").strip().lower()
    expected = source_claim_component_sha256(item)
    if not expected or supplied != expected:
        errors.append(
            "source-claim semantic contract is not bound to the current generated component occurrence"
        )
    supplied_structural = str(
        contract.get("structural_type_sha256") or ""
    ).strip().lower()
    expected_structural = field_type_sha256(item)
    if (
        not _SHA256_RE.fullmatch(supplied_structural)
        or not expected_structural
        or supplied_structural != expected_structural
    ):
        errors.append(
            "source-claim semantic contract is not bound to the current component structural type"
        )
    return errors


def _source_contract_anchor_errors(
    contract: Mapping[str, Any], *, correction: bool,
    source_item_semantic_sha256_by_key: Mapping[str, str] | None,
) -> list[str]:
    """Validate an occurrence-bound source/correction anchor.

    The route itself, its current source identity, and (when applicable) its
    explicit correction record determine whether this is admissible.  A
    source-record classification is descriptive legacy metadata, not evidence
    that a material theorem component has been accounted for.
    """
    anchor = contract.get("source_anchor")
    if not isinstance(anchor, Mapping):
        return ["source-claim contract needs a `source_anchor` object"]
    key = str(anchor.get("source_item_key") or "").strip()
    semantic_sha = str(anchor.get("source_item_semantic_sha256") or "").strip().lower()
    locator = str(anchor.get("source_locator") or "").strip()
    errors: list[str] = []
    if not key:
        errors.append("source_anchor.source_item_key is required")
    if not _SHA256_RE.fullmatch(semantic_sha):
        errors.append("source_anchor.source_item_semantic_sha256 is missing or malformed")
    elif source_item_semantic_sha256_by_key is None:
        errors.append("source-claim contract needs the current source-item semantic index")
    elif source_item_semantic_sha256_by_key.get(key) != semantic_sha:
        errors.append("source-claim contract does not match the current source-item semantic identity")
    if not _EXACT_LOCATOR_RE.search(locator):
        errors.append("source_anchor.source_locator must be an exact source locator")
    for field in ("source_formula", "semantic_match"):
        if not _nonempty_text(anchor.get(field)):
            errors.append(
                "source_anchor."
                + field
                + " must give formula/domain-level source evidence, not a name-only reference"
            )
    if correction:
        additional = contract.get("additional_assumption")
        if not isinstance(additional, Mapping):
            errors.append(
                "approved correction/additional-assumption route needs an `additional_assumption` object"
            )
        else:
            for field in ("statement", "justification", "report_locator"):
                if not _nonempty_text(additional.get(field)):
                    errors.append(
                        "additional_assumption."
                        + field
                        + " must be explicit and anchored"
                    )
            report_locator = str(additional.get("report_locator") or "").strip()
            if not _EXACT_LOCATOR_RE.search(report_locator):
                errors.append(
                    "additional_assumption.report_locator must be an exact report/source locator"
                )
    return errors


def _source_claim_atom_errors(
    contract: Mapping[str, Any],
    *,
    require_source_claim_atom: bool,
    current_source_claim_atom_receipts: Iterable[SourceClaimAtomReceipt],
) -> list[str]:
    """Validate a source-clause atom binding when the atom lane is active."""

    atom = contract.get("source_claim_atom")
    if atom is None and not require_source_claim_atom:
        return []
    if not isinstance(atom, Mapping):
        return [
            "exact source-claim contract needs a source_claim_atom object under the active source-atom policy"
        ]
    source_item_key = str(atom.get("source_item_key") or "").strip()
    atom_id = str(atom.get("id") or "").strip()
    semantic_sha = str(
        atom.get("source_claim_atom_semantic_sha256") or ""
    ).strip().lower()
    locator = str(atom.get("source_locator") or "").strip()
    if (
        not source_item_key
        or not atom_id
        or not _SHA256_RE.fullmatch(semantic_sha)
        or not _EXACT_LOCATOR_RE.search(locator)
    ):
        return [
            "source_claim_atom needs source_item_key, id, current semantic SHA-256, and an exact source locator"
        ]
    expected = SourceClaimAtomReceipt(
        source_item_key=source_item_key,
        atom_id=atom_id,
        atom_semantic_sha256=semantic_sha,
        source_locator=locator,
    )
    if expected not in set(current_source_claim_atom_receipts):
        return [
            "source_claim_atom has no matching current source-clause identity/quote receipt"
        ]
    anchor = contract.get("source_anchor")
    if isinstance(anchor, Mapping) and str(
        anchor.get("source_item_key") or ""
    ).strip() != source_item_key:
        return [
            "source_claim_atom must belong to the same source item as source_anchor"
        ]
    return []


def _correction_identity_pin_errors(
    raw_pin: object,
    current_identity: Mapping[str, Any],
    *,
    field: str,
    require_explanation: bool,
) -> list[str]:
    if not isinstance(raw_pin, Mapping):
        return [f"{field} must be an object pinned to the current source correction"]
    errors: list[str] = []
    target_sha = str(raw_pin.get("corrected_target_sha256") or "").strip().lower()
    current_target_sha = str(
        current_identity.get("corrected_target_sha256") or ""
    ).strip().lower()
    if (
        not _SHA256_RE.fullmatch(target_sha)
        or target_sha != current_target_sha
    ):
        errors.append(
            f"{field}.corrected_target_sha256 does not match the current corrected target"
        )
    governing_ids, governing_error = _nonempty_unique_strings(
        raw_pin.get("governing_defect_ids")
    )
    if governing_error:
        errors.append(f"{field}.governing_defect_ids {governing_error}")
    current_ids_raw = current_identity.get("governing_defect_ids")
    current_ids = (
        {
            value.strip()
            for value in current_ids_raw
            if isinstance(value, str) and value.strip()
        }
        if isinstance(current_ids_raw, (list, tuple, set, frozenset))
        else set()
    )
    if governing_ids and set(governing_ids) != current_ids:
        errors.append(
            f"{field}.governing_defect_ids do not match the current source correction"
        )
    if require_explanation:
        for explanatory_field in ("statement", "justification", "report_locator"):
            if not _nonempty_text(raw_pin.get(explanatory_field)):
                errors.append(
                    f"{field}.{explanatory_field} must be explicit and substantive"
                )
        report_locator = str(raw_pin.get("report_locator") or "").strip()
        if report_locator and not _EXACT_LOCATOR_RE.search(report_locator):
            errors.append(f"{field}.report_locator must be an exact report/source locator")
    return errors


def _strict_source_correction_contract_errors(
    contract: Mapping[str, Any],
    *,
    route: str,
    current_source_correction_identity_by_key: (
        Mapping[str, Mapping[str, Any] | None]
    ),
) -> list[str]:
    """Validate literal/corrected status at the occurrence contract itself."""

    anchor = contract.get("source_anchor")
    source_key = (
        str(anchor.get("source_item_key") or "").strip()
        if isinstance(anchor, Mapping)
        else ""
    )
    if not source_key or source_key not in current_source_correction_identity_by_key:
        return [
            "source-claim contract has no current source-item correction-status identity"
        ]
    current_identity = current_source_correction_identity_by_key[source_key]
    unaffected = contract.get("unaffected_by_source_correction")
    correction_pin = contract.get("source_correction")

    if route == EXACT_SOURCE_CLAIM_ROUTE:
        errors: list[str] = []
        if correction_pin is not None:
            errors.append("exact source-claim contract cannot carry `source_correction`")
        if current_identity is None:
            if unaffected is not None:
                errors.append(
                    "unaffected_by_source_correction is invalid because the current source item is not corrected"
                )
            return errors
        errors.extend(
            _correction_identity_pin_errors(
                unaffected,
                current_identity,
                field="unaffected_by_source_correction",
                require_explanation=True,
            )
        )
        return errors

    if route == APPROVED_SOURCE_CORRECTION_ROUTE:
        errors = []
        if unaffected is not None:
            errors.append(
                "correction/additional-assumption contract cannot carry `unaffected_by_source_correction`"
            )
        if current_identity is None:
            errors.append(
                "correction/additional-assumption contract is anchored to a source item without a current corrected target"
            )
            return errors
        errors.extend(
            _correction_identity_pin_errors(
                correction_pin,
                current_identity,
                field="source_correction",
                require_explanation=False,
            )
        )
        return errors
    return []


def _source_domain_parent_judgment_keys(
    correspondence: Mapping[str, Any],
) -> tuple[tuple[str, ...], list[str]]:
    """Read one or several semantic-parent identities fail-closed.

    The scalar field is retained for existing schema-1 contracts.  A shared
    component can instead list every semantic parent under which its generated
    occurrence is valid.  Parent spellings do not grant credit: a current
    generated correspondence receipt must still match one of these identities.
    """

    scalar_present = "source_model_judgment_key" in correspondence
    list_present = "source_model_judgment_keys" in correspondence
    if scalar_present and list_present:
        return (), [
            "source-domain correspondence must use either "
            "`source_model_judgment_key` or `source_model_judgment_keys`, not both"
        ]
    if scalar_present:
        raw_parent = correspondence.get("source_model_judgment_key")
        if not isinstance(raw_parent, str) or not raw_parent.strip():
            return (), [
                "source-domain correspondence `source_model_judgment_key` "
                "must be one nonempty string"
            ]
        return (raw_parent.strip(),), []
    if list_present:
        raw_parents = correspondence.get("source_model_judgment_keys")
        if not isinstance(raw_parents, list) or not raw_parents:
            return (), [
                "source-domain correspondence `source_model_judgment_keys` "
                "must be a nonempty list"
            ]
        if any(
            not isinstance(raw_parent, str) or not raw_parent.strip()
            for raw_parent in raw_parents
        ):
            return (), [
                "source-domain correspondence `source_model_judgment_keys` "
                "must contain only nonempty strings"
            ]
        parents = tuple(raw_parent.strip() for raw_parent in raw_parents)
        if len(parents) != len(set(parents)):
            return (), [
                "source-domain correspondence `source_model_judgment_keys` "
                "must contain unique parent identities"
            ]
        return parents, []
    return (), [
        "source-domain correspondence needs `source_model_judgment_key` or "
        "`source_model_judgment_keys`"
    ]


def complete_source_claim_semantic_contract_errors(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    source_item_semantic_sha256_by_key: Mapping[str, str] | None = None,
    current_exact_source_antecedent_keys: Iterable[str] = (),
    checked_lean_bridge_receipts: Iterable[CheckedLeanBridgeReceipt] = (),
    source_domain_correspondence_receipts: Iterable[SourceDomainCorrespondenceReceipt] = (),
    transparent_spec_full_surface_correspondence_receipts: Iterable[
        TransparentSpecFullSurfaceCorrespondenceReceipt
    ] = (),
    semantic_contract_executable_terminal_component_receipts: Iterable[
        SemanticContractExecutableTerminalComponentReceipt
    ] = (),
    recursive_field_explicit_parent_component_receipts: Iterable[
        RecursiveFieldExplicitParentComponentReceipt
    ] = (),
    current_component_sha256s_by_source_judgment_key: Mapping[str, Iterable[str]] | None = None,
    current_source_claim_atom_receipts: Iterable[SourceClaimAtomReceipt] = (),
    require_source_claim_atom: bool = False,
    allow_legacy_implicit_route: bool = False,
    current_source_disposition_keys: Iterable[str] | None = None,
    current_source_correction_identity_by_key: (
        Mapping[str, Mapping[str, Any] | None] | None
    ) = None,
    current_explicit_source_assumption_keys: Iterable[str] = (),
    current_formalization_regularity_keys: Iterable[str] = (),
    current_trusted_external_scaffolding_keys: Iterable[str] = (),
    current_trusted_external_scaffolding_component_sha256s: Iterable[str] = (),
) -> list[str]:
    """Validate one complete provenance disposition fail-closed.

    This is the authoritative generic gate.  The old restriction-specific
    function below delegates here for compatibility.  A raw classification,
    a source locator alone, a convention label, or prose in ``lean_derivation``
    is never a disposition.
    """

    key = _field_key(item) or "<unnamed theorem-realization component>"
    component_key = str(item.get("judgment_key") or "").strip()
    component_sha = source_claim_component_sha256(item)
    # Read only for the explicitly enabled legacy fallback below.  Schema-1
    # disposition selection never depends on this reviewer label.
    classification = str(judgment.get("classification") or "").strip()
    current_components, occurrence_errors = _current_component_sha256s(
        item, current_component_sha256s_by_source_judgment_key
    )
    if occurrence_errors:
        return occurrence_errors

    # A recursively traversed record container is not an additional source
    # primitive once the generator has explicitly classified that exact route
    # as a structural container.  Its recursively emitted children remain
    # material components and are checked independently below.  This narrow
    # case is intentionally tied to the generated section, kind, nested
    # structure, route, and current response classification; an arbitrary
    # opaque container still requires its own component contract.
    recursive_route = item.get("recursive_field_explicit_parent_route")
    nested_structures = item.get("nested_structures")
    if (
        str(item.get("source_component_section") or "").strip()
        == "recursive_field_items"
        and str(item.get("source_claim_component_kind") or "").strip()
        == "recursive_record_field"
        and isinstance(nested_structures, list)
        and bool(nested_structures)
        and all(isinstance(value, str) and value.strip() for value in nested_structures)
        and isinstance(recursive_route, Mapping)
        and recursive_route.get("permitted_classifications")
        == ["container_recursively_audited"]
        and classification == "container_recursively_audited"
    ):
        return []

    # A strict source-to-Spec record can cover the *whole* canonical
    # transparent Spec surface.  Its issuer has already checked the source
    # scope, atom coverage, current Lean closure receipt, direct evidence
    # parent, and exact component association.  This is intentionally an
    # in-memory capability rather than a reviewer-written component contract:
    # otherwise one theorem with many generated binders would require a large
    # duplicate sidecar whose text cannot add semantic evidence.
    expected_structural = field_type_sha256(item)
    current_full_surface_receipts = {
        receipt
        for receipt in transparent_spec_full_surface_correspondence_receipts
        if isinstance(receipt, TransparentSpecFullSurfaceCorrespondenceReceipt)
    }
    if any(
        receipt.component_key == component_key
        and receipt.source_judgment_key == key
        and receipt.component_sha256 == component_sha
        and receipt.structural_type_sha256 == expected_structural
        for receipt in current_full_surface_receipts
    ):
        return []
    # A direct source semantic contract may end in a structurally identified
    # executable terminal rather than a recursively transparent Prop closure.
    # This is not source-to-Spec correspondence credit: the runtime receipt is
    # minted only by the exact terminal-policy transaction after it verifies
    # the source contract, direct theorem/Spec pair, semantic-model review,
    # dependency fingerprint, and all terminal occurrences.  Match the
    # generated component and its parent association exactly so a receipt for
    # one Spec surface cannot discharge a nearby binder or model route.
    raw_component_association = item.get("source_contract_association")
    component_association_sha = (
        str(raw_component_association.get("association_sha256") or "")
        .strip()
        .lower()
        if isinstance(raw_component_association, Mapping)
        else ""
    )
    semantic_model_key = (
        str(raw_component_association.get("semantic_model_judgment_key") or "").strip()
        if isinstance(raw_component_association, Mapping)
        else ""
    )
    current_terminal_receipts = {
        receipt
        for receipt in semantic_contract_executable_terminal_component_receipts
        if isinstance(receipt, SemanticContractExecutableTerminalComponentReceipt)
    }
    if any(
        receipt.component_key == component_key
        and receipt.source_judgment_key == key
        and receipt.component_sha256 == component_sha
        and receipt.structural_type_sha256 == expected_structural
        and receipt.semantic_model_judgment_key == semantic_model_key
        and receipt.component_source_contract_association_sha256
        == component_association_sha
        for receipt in current_terminal_receipts
    ):
        return []
    # A recursively expanded source-model field may be an exact primitive of
    # the reviewed source model rather than a theorem/Spec component with its
    # own semantic-contract association.  It receives no name- or
    # classification-based exemption: only a live receipt can close it, and
    # that receipt must bind the generated field route, source identity,
    # convention, direct semantic parent, and the exact material occurrence.
    current_recursive_field_receipts = {
        receipt
        for receipt in recursive_field_explicit_parent_component_receipts
        if isinstance(receipt, RecursiveFieldExplicitParentComponentReceipt)
    }
    if any(
        recursive_field_explicit_parent_component_receipt_matches(item, receipt)
        for receipt in current_recursive_field_receipts
    ):
        return []
    # A sort/type classifier is discovery metadata, never an exemption.  In
    # particular, ``Fin n``, a custom carrier, a function/predicate value, or
    # a record container can change the theorem's source domain even when it
    # is not a proposition.  The sole special case is an occurrence explicitly
    # registered by its generated identity as an external primitive.  This
    # keeps trusted scaffolding name-free and prevents a role/classification
    # label from granting itself credit.
    _ = current_trusted_external_scaffolding_keys
    registered_external_component_sha256s = {
        str(value).strip().lower()
        for value in current_trusted_external_scaffolding_component_sha256s
        if _SHA256_RE.fullmatch(str(value).strip().lower())
    }
    if component_sha in registered_external_component_sha256s:
        contract, contract_errors = _source_claim_semantic_contract(
            item,
            judgment,
            current_component_sha256s_by_source_judgment_key=(
                current_component_sha256s_by_source_judgment_key
            ),
        )
        if contract_errors:
            return contract_errors
        if (
            isinstance(contract, Mapping)
            and not _contract_component_binding_errors(item, contract)
            and str(contract.get("route") or "").strip()
            == TRUSTED_EXTERNAL_SCAFFOLDING_ROUTE
        ):
            return []
        return [
            key
            + " is an explicitly registered external primitive but lacks a current component-bound trusted-scaffolding contract"
        ]

    # Historical callers supplied judgment-key dispositions before contracts
    # were occurrence-indexed. Strict v11 callers instead provide the current
    # source-correction index below: the component-bound contract is itself
    # the human semantic disposition, independent of reviewer classification.
    source_disposition_keys = set(
        current_explicit_source_assumption_keys
        if current_source_disposition_keys is None
        else current_source_disposition_keys
    )
    _ = current_formalization_regularity_keys

    contract, contract_selection_errors = _source_claim_semantic_contract(
        item,
        judgment,
        current_component_sha256s_by_source_judgment_key=(
            current_component_sha256s_by_source_judgment_key
        ),
    )
    if contract_selection_errors:
        return contract_selection_errors
    if isinstance(contract, Mapping):
        errors = _contract_component_binding_errors(item, contract)
        route = str(contract.get("route") or "").strip()
        if route == EXACT_SOURCE_CLAIM_ROUTE:
            errors += _source_contract_anchor_errors(
                contract,
                correction=False,
                source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
            )
            errors += _source_claim_atom_errors(
                contract,
                require_source_claim_atom=require_source_claim_atom,
                current_source_claim_atom_receipts=current_source_claim_atom_receipts,
            )
            if current_source_correction_identity_by_key is not None:
                errors += _strict_source_correction_contract_errors(
                    contract,
                    route=route,
                    current_source_correction_identity_by_key=(
                        current_source_correction_identity_by_key
                    ),
                )
            elif key not in source_disposition_keys:
                errors.append(
                    "exact source-claim contract has no current target-disposition receipt"
                )
            return errors
        if route == APPROVED_SOURCE_CORRECTION_ROUTE:
            errors += _source_contract_anchor_errors(
                contract,
                correction=True,
                source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
            )
            errors += _source_claim_atom_errors(
                contract,
                require_source_claim_atom=require_source_claim_atom,
                current_source_claim_atom_receipts=current_source_claim_atom_receipts,
            )
            if current_source_correction_identity_by_key is not None:
                errors += _strict_source_correction_contract_errors(
                    contract,
                    route=route,
                    current_source_correction_identity_by_key=(
                        current_source_correction_identity_by_key
                    ),
                )
            elif key not in source_disposition_keys:
                errors.append(
                    "correction/additional-assumption contract has no current target-disposition receipt for this occurrence"
                )
            return errors
        if route == SOURCE_DOMAIN_CORRESPONDENCE_ROUTE:
            correspondence = contract.get("source_domain_correspondence")
            if not isinstance(correspondence, Mapping):
                return errors + [
                    "source-domain correspondence route needs a `source_domain_correspondence` object"
                ]
            source_model_keys, parent_errors = (
                _source_domain_parent_judgment_keys(correspondence)
            )
            errors += parent_errors
            supplied_component_sha = str(
                correspondence.get("component_sha256") or ""
            ).strip().lower()
            if supplied_component_sha != component_sha:
                errors.append(
                    "source-domain correspondence does not bind the current generated component occurrence"
                )
            current_receipts = set(source_domain_correspondence_receipts)
            if source_model_keys and not any(
                SourceDomainCorrespondenceReceipt(
                    component_key=component_key,
                    component_sha256=component_sha,
                    source_model_judgment_key=source_model_key,
                )
                in current_receipts
                for source_model_key in source_model_keys
            ):
                errors.append(
                    "source-domain correspondence has no matching current "
                    "semantic-model/elaborated-route receipt for a listed parent"
                )
            return errors
        if route == CHECKED_LEAN_DERIVATION_ROUTE:
            bridge_contract = {
                "schema": SEMANTIC_RESTRICTION_OBLIGATION_SCHEMA,
                "field_type_sha256": source_claim_component_sha256(item),
                "bridge": contract.get("bridge"),
            }
            return errors + _checked_lean_bridge_errors(
                item,
                judgment,
                bridge_contract,
                current_exact_source_antecedent_keys=current_exact_source_antecedent_keys,
                checked_lean_bridge_receipts=checked_lean_bridge_receipts,
            )
        return errors + [
            "source-claim semantic contract route must be an exact source claim, explicit correction/additional assumption, source-domain correspondence, or checked Lean derivation"
        ]

    # Existing direct target-disposition validation can close literal/corrected
    # source components only in explicitly enabled compatibility mode. If an
    # old sidecar supplies a route object, validate that object rather than
    # bypassing its source identity checks.
    legacy = _semantic_restriction_obligation(judgment)
    if (
        allow_legacy_implicit_route
        and
        not isinstance(legacy, Mapping)
        and
        classification in {"validated_source_assumption", "approved_corrected_condition"}
        and key in set(current_explicit_source_assumption_keys)
        and current_components == {component_sha}
    ):
        return []

    # Preserve old explicitly generated bridge sidecars while requiring their
    # Lean receipt. A `lean_checked: true` field is ignored by the bridge
    # checker.
    if allow_legacy_implicit_route and isinstance(legacy, Mapping):
        if current_components != {component_sha}:
            return [
                "legacy source/Lean route is ambiguous across multiple current component occurrences; issue component-indexed contracts"
            ]
        legacy_route = str(legacy.get("route") or "").strip()
        if legacy_route == EXPLICIT_SOURCE_ASSUMPTION_ROUTE:
            errors = _explicit_source_assumption_errors(
                item,
                judgment,
                legacy,
                source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
            )
            if key not in set(current_explicit_source_assumption_keys):
                errors.append(
                    "legacy explicit source-assumption route has no current target-disposition receipt"
                )
            return errors
        if legacy_route == CHECKED_LEAN_BRIDGE_ROUTE:
            return _checked_lean_bridge_errors(
                item,
                judgment,
                legacy,
                current_exact_source_antecedent_keys=current_exact_source_antecedent_keys,
                checked_lean_bridge_receipts=checked_lean_bridge_receipts,
            )

    return [
        key
        + " is a material theorem-realization component with no source-claim semantic contract"
    ]


def semantic_restriction_obligation_errors(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    *,
    source_item_semantic_sha256_by_key: Mapping[str, str] | None = None,
    current_exact_source_antecedent_keys: Iterable[str] = (),
    checked_lean_bridge_receipts: Iterable[CheckedLeanBridgeReceipt] = (),
    source_domain_correspondence_receipts: Iterable[SourceDomainCorrespondenceReceipt] = (),
    recursive_field_explicit_parent_component_receipts: Iterable[
        RecursiveFieldExplicitParentComponentReceipt
    ] = (),
    current_component_sha256s_by_source_judgment_key: Mapping[str, Iterable[str]] | None = None,
    current_source_claim_atom_receipts: Iterable[SourceClaimAtomReceipt] = (),
    require_source_claim_atom: bool = False,
    allow_legacy_implicit_route: bool = False,
    current_source_disposition_keys: Iterable[str] | None = None,
    current_source_correction_identity_by_key: (
        Mapping[str, Mapping[str, Any] | None] | None
    ) = None,
    current_explicit_source_assumption_keys: Iterable[str] = (),
    current_formalization_regularity_keys: Iterable[str] = (),
    current_trusted_external_scaffolding_keys: Iterable[str] = (),
    current_trusted_external_scaffolding_component_sha256s: Iterable[str] = (),
) -> list[str]:
    """Compatibility facade for the complete source-claim contract gate."""

    return complete_source_claim_semantic_contract_errors(
        item,
        judgment,
        source_item_semantic_sha256_by_key=source_item_semantic_sha256_by_key,
        current_exact_source_antecedent_keys=current_exact_source_antecedent_keys,
        checked_lean_bridge_receipts=checked_lean_bridge_receipts,
        source_domain_correspondence_receipts=source_domain_correspondence_receipts,
        recursive_field_explicit_parent_component_receipts=(
            recursive_field_explicit_parent_component_receipts
        ),
        current_component_sha256s_by_source_judgment_key=(
            current_component_sha256s_by_source_judgment_key
        ),
        current_source_claim_atom_receipts=current_source_claim_atom_receipts,
        require_source_claim_atom=require_source_claim_atom,
        allow_legacy_implicit_route=allow_legacy_implicit_route,
        current_source_disposition_keys=current_source_disposition_keys,
        current_source_correction_identity_by_key=(
            current_source_correction_identity_by_key
        ),
        current_explicit_source_assumption_keys=current_explicit_source_assumption_keys,
        current_formalization_regularity_keys=current_formalization_regularity_keys,
        current_trusted_external_scaffolding_keys=(
            current_trusted_external_scaffolding_keys
        ),
        current_trusted_external_scaffolding_component_sha256s=(
            current_trusted_external_scaffolding_component_sha256s
        ),
    )


def semantic_restriction_is_closed(
    item: Mapping[str, Any],
    judgment: Mapping[str, Any],
    **kwargs: Any,
) -> bool:
    """Return whether the generic restriction policy has no open route."""

    return not semantic_restriction_obligation_errors(item, judgment, **kwargs)


def operational_prop_field_obligation_errors(
    item: Mapping[str, Any], judgment: Mapping[str, Any], **kwargs: Any
) -> list[str]:
    """Compatibility alias for :func:`semantic_restriction_obligation_errors`."""

    return semantic_restriction_obligation_errors(item, judgment, **kwargs)


def operational_prop_field_is_closed(
    item: Mapping[str, Any], judgment: Mapping[str, Any], **kwargs: Any
) -> bool:
    """Compatibility alias for :func:`semantic_restriction_is_closed`."""

    return semantic_restriction_is_closed(item, judgment, **kwargs)


def theorem_facing_obligation_items(
    audit_payload: Mapping[str, Any],
) -> tuple[tuple[str, Mapping[str, Any]], ...]:
    """Return every material theorem-realization component exactly once.

    New generator payloads provide an exhaustive component ledger. Legacy
    payloads fall back to the canonical inputs, recursive fields, dependencies,
    and result certificates, but canonical data/domain inputs are deliberately
    included rather than silently exempted.
    """

    explicit_components = audit_payload.get("theorem_realization_component_items")
    if isinstance(explicit_components, list):
        collected: list[tuple[str, Mapping[str, Any]]] = []
        seen: set[tuple[str, str, str]] = set()
        for item in explicit_components:
            if not isinstance(item, Mapping):
                continue
            key = _field_key(item)
            section = str(item.get("source_component_section") or "component").strip()
            if not key or not section:
                continue
            # Source judgments are reusable metadata, not component identity.
            # Preserve every occurrence the generator emitted, including two
            # same-source record fields or dependencies in one section.
            identity = (
                section,
                source_claim_component_sha256(item),
                str(item.get("judgment_key") or "").strip(),
            )
            if identity not in seen:
                seen.add(identity)
                collected.append((section, item))
        return tuple(collected)

    canonical_input_keys = {
        _field_key(item)
        for item in audit_payload.get("theorem_facing_input_items") or []
        if isinstance(item, Mapping) and _field_key(item)
    }
    conclusion_keys = {
        _field_key(item)
        for item in audit_payload.get("conclusion_dependency_items") or []
        if isinstance(item, Mapping) and _field_key(item)
    }
    collected: list[tuple[str, Mapping[str, Any]]] = []
    seen: set[tuple[str, str]] = set()
    for section in (
        "theorem_facing_input_items",
        "recursive_field_items",
        "boundary_input_items",
        "conclusion_dependency_items",
        "type_valued_certificate_result_items",
    ):
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, Mapping):
                continue
            key = _field_key(item)
            if not key:
                continue
            if (
                section in {"boundary_input_items", "conclusion_dependency_items"}
                and key in canonical_input_keys
            ):
                continue
            if section == "boundary_input_items" and key in conclusion_keys:
                continue
            if section == "conclusion_dependency_items" and item.get(
                "conclusion_fields"
            ):
                continue
            # The fallback reader must not infer an exemption from a data
            # sort. New schema-1 payloads supply the explicit ledger above;
            # older payloads remain pending/non-credit, but their material
            # surfaces are still visible to diagnostics.
            identity = (section, key)
            if identity in seen:
                continue
            seen.add(identity)
            collected.append((section, item))
    return tuple(collected)
