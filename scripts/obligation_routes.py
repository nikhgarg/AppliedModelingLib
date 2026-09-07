#!/usr/bin/env python3
"""Pure typed interpretation of the paper source-route ledger.

This is the single structural boundary shared by preflight, evidence producers,
presentation generators, planners, and terminal verification. It validates
exact source anchors and explicit semantic contracts without reading files,
running Lean, or inferring meaning from declaration locations.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from enum import Enum
from typing import Any, Mapping


SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
DECLARATION_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_'?]*(?:\.[A-Za-z_][A-Za-z0-9_'?]*)*$"
)
RESULT_SOURCE_KINDS = frozenset(
    {
        "lemma",
        "theorem",
        "proposition",
        "corollary",
        "claim",
        "runtime_claim",
        "example",
    }
)
# Historical route vocabulary, also read when authenticating accepted graphs.
# Fresh role-typed admission is owned by structural_obligation_preflight:
# definitions and algorithms expose actual semantic declarations; assertions
# attached to them are separate result items. Keeping this reader vocabulary
# does not authorize a fresh definition-as-reflexive-Spec route.
PROOF_CONTRACT_SOURCE_KINDS = RESULT_SOURCE_KINDS | frozenset(
    {
        "definition",
        "formula",
        "equation",
        "algorithm",
        "algorithmic_formula",
    }
)
SOURCE_SEMANTIC_DECLARATION_KINDS = frozenset(
    {
        "definition",
        "predicate_vocabulary",
        "formula",
        "equation",
        "algorithm",
        "algorithmic_formula",
        "assumption",
        "condition",
        "model",
    }
)
# A direct semantic definition has no truth value to prove.  These source
# presentations may therefore use a Lean-checked definition-to-Spec
# equivalence, while named results must keep an ordinary proof/refutation
# endpoint.  The source map still opts into this lane explicitly.
DEFINITIONAL_CONTRACT_SOURCE_KINDS = frozenset(
    {
        "definition",
        "formula",
        "equation",
        "algorithm",
        "algorithmic_formula",
    }
)


class ObligationRouteError(ValueError):
    """A source item or semantic route is structurally malformed."""


class RouteKind(str, Enum):
    RESULT_SEMANTIC = "result_semantic"
    SOURCE_SEMANTIC_DECLARATION = "source_semantic_declaration"
    SOURCE_ASSUMPTION = "source_assumption"
    PROOF_SUPPORT = "proof_support"
    SOURCE_CONVENTION = "source_convention"
    SOURCE_PRESENTATION_ALIAS = "source_presentation_alias"
    SOURCE_SCOPE_DISPOSITION = "source_scope_disposition"
    PENDING_SOURCE_ROUTE = "pending_source_route"
    SOURCE_CONTEXT = "source_context"


class SemanticReviewTargetKind(str, Enum):
    """The one Lean-owned semantic object shown to the source reviewer."""

    SPEC_PROPOSITION = "spec_proposition"
    DEFINITION_DECLARATION = "definition_declaration"


def _digest(value: object) -> str:
    """Preserve the historical typed-route digest during module extraction."""

    payload = (
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _declaration(value: object, field: str) -> str:
    text = str(value or "").strip()
    if not DECLARATION_RE.fullmatch(text):
        raise ObligationRouteError(f"{field} is not a qualified Lean declaration")
    return text


def _strings(value: object, field: str) -> tuple[str, ...]:
    if value is None:
        return ()
    if not isinstance(value, list):
        raise ObligationRouteError(f"{field} must be a list")
    result = tuple(str(item).strip() for item in value)
    if any(not item for item in result) or len(set(result)) != len(result):
        raise ObligationRouteError(f"{field} contains an empty or duplicate item")
    return result


def _anchor_digests(value: object) -> tuple[str, ...]:
    """Authenticate every embedded byte-pinned quote without inferring scope."""

    found: list[str] = []

    def visit(node: object) -> None:
        if isinstance(node, Mapping):
            if "quoted_text" in node or "quoted_text_sha256" in node:
                quoted = node.get("quoted_text")
                recorded = str(node.get("quoted_text_sha256") or "").strip().lower()
                if not isinstance(quoted, str) or not SHA256_RE.fullmatch(recorded):
                    raise ObligationRouteError(
                        "source anchor quote/hash pair is malformed"
                    )
                actual = hashlib.sha256(quoted.encode("utf-8")).hexdigest()
                if actual != recorded:
                    raise ObligationRouteError("source anchor quote digest is incorrect")
                found.append(recorded)
            for child in node.values():
                visit(child)
        elif isinstance(node, list):
            for child in node:
                visit(child)

    visit(value)
    return tuple(found)


def source_item_primary_anchor_sha256s(value: object) -> tuple[str, ...]:
    """Return only the item's claim-bearing top-level source anchors.

    ``EvidenceRoute.anchor_sha256s`` intentionally authenticates every quote
    embedded anywhere in a route, including model/context bundles.  Source
    atom leaves have a narrower role: absent explicit claim atoms, they are
    formed from ``source_anchor_evidence`` only.  Keeping that projection here
    gives structural preflight and final credential issuance one implementation
    of the distinction.
    """

    if not isinstance(value, Mapping):
        raise ObligationRouteError("source item is not an object")
    anchors = value.get("source_anchor_evidence")
    if not isinstance(anchors, list) or not anchors:
        raise ObligationRouteError("source item has no anchor evidence")
    return tuple(sorted(set(_anchor_digests(anchors))))


def semantic_review_target(
    raw: Mapping[str, object],
    *,
    spec_declaration: str,
    evidence_mode: str,
) -> tuple[SemanticReviewTargetKind, str]:
    """Return the explicit Lean object used for source-semantic review."""

    kind = SemanticReviewTargetKind.SPEC_PROPOSITION
    declaration = spec_declaration
    raw_review_target = raw.get("semantic_review_target")
    if raw_review_target is None:
        return kind, declaration
    if (
        not isinstance(raw_review_target, Mapping)
        or set(raw_review_target) != {"schema", "kind", "declaration"}
        or raw_review_target.get("schema") != 1
    ):
        raise ObligationRouteError("malformed semantic_review_target")
    try:
        kind = SemanticReviewTargetKind(
            str(raw_review_target.get("kind") or "").strip()
        )
    except ValueError as exc:
        raise ObligationRouteError("unsupported semantic review target kind") from exc
    if kind is not SemanticReviewTargetKind.DEFINITION_DECLARATION:
        raise ObligationRouteError(
            "only a definition declaration may override the Spec review target"
        )
    declaration = _declaration(
        raw_review_target.get("declaration"),
        "semantic_review_target.declaration",
    )
    if not spec_declaration or evidence_mode not in {
        "proves",
        "definitionally_realizes",
    }:
        raise ObligationRouteError(
            "definition review target requires a proposition-shaped semantic contract"
        )
    return kind, declaration


@dataclass(frozen=True)
class EvidenceRoute:
    """One source-ledger item normalized without storage-location inference."""

    source_item_id: str
    source_kind: str
    route_kind: RouteKind
    claim_bearing: bool
    inventory_role: str
    spec_declaration: str
    evidence_declaration: str
    evidence_mode: str
    semantic_review_target_kind: SemanticReviewTargetKind
    semantic_review_declaration: str
    semantic_declarations: tuple[str, ...]
    support_declarations: tuple[str, ...]
    convention_ids: tuple[str, ...]
    source_component_of: str
    anchor_sha256s: tuple[str, ...]

    @classmethod
    def from_source_item(
        cls,
        source_item_id: str,
        raw: object,
    ) -> "EvidenceRoute":
        if not isinstance(raw, Mapping):
            raise ObligationRouteError(
                f"source item {source_item_id!r} is not an object"
            )
        source_item_id = str(source_item_id).strip()
        if not source_item_id:
            raise ObligationRouteError("source item id is empty")
        claim_bearing_raw = raw.get("claim_bearing")
        claim_bearing = claim_bearing_raw is not False
        if claim_bearing_raw not in {None, True, False}:
            raise ObligationRouteError(
                f"source item {source_item_id!r} has non-boolean claim_bearing"
            )
        inventory_role = str(raw.get("inventory_role") or "").strip()
        source_kind = str(raw.get("source_kind") or "").strip().lower()
        contract = raw.get("semantic_contract")
        spec = ""
        evidence = ""
        evidence_mode = ""
        semantic_review_target_kind = SemanticReviewTargetKind.SPEC_PROPOSITION
        semantic_review_declaration = ""
        if contract is not None:
            if not isinstance(contract, Mapping) or set(contract) != {
                "spec_declaration",
                "evidence_declaration",
                "evidence_mode",
                "semantic_shape",
            }:
                raise ObligationRouteError(
                    f"source item {source_item_id!r} has malformed semantic_contract"
                )
            spec = _declaration(contract.get("spec_declaration"), "spec_declaration")
            evidence = _declaration(
                contract.get("evidence_declaration"), "evidence_declaration"
            )
            evidence_mode = str(contract.get("evidence_mode") or "").strip()
            if evidence_mode not in {
                "proves",
                "refutes",
                "definitionally_realizes",
            }:
                raise ObligationRouteError(
                    f"source item {source_item_id!r} has unsupported evidence_mode"
                )
            if contract.get("semantic_shape") != "plain":
                raise ObligationRouteError(
                    f"source item {source_item_id!r} has unsupported semantic_shape"
                )

        try:
            (
                semantic_review_target_kind,
                semantic_review_declaration,
            ) = semantic_review_target(
                raw,
                spec_declaration=spec,
                evidence_mode=evidence_mode,
            )
        except ObligationRouteError as exc:
            raise ObligationRouteError(
                f"source item {source_item_id!r} {exc}"
            ) from exc

        support = []
        for field in (
            "support_lean_declarations",
            "support_declarations",
            "proof_lean_declarations",
        ):
            support.extend(_strings(raw.get(field), field))
        support_tuple = tuple(dict.fromkeys(support))
        for declaration in support_tuple:
            if not LEAN_NAME_RE.fullmatch(declaration):
                raise ObligationRouteError("support declaration is not a Lean name")
        conventions = _strings(raw.get("model_convention_ids"), "model_convention_ids")
        source_component_of = str(raw.get("source_component_of") or "").strip()
        semantic_declarations = (
            _strings(raw.get("lean_declarations"), "lean_declarations")
            if inventory_role == "source_semantic_declaration"
            else ()
        )
        for declaration in semantic_declarations:
            if not LEAN_NAME_RE.fullmatch(declaration):
                raise ObligationRouteError(
                    "source semantic declaration is not a Lean name"
                )

        if spec:
            # A source result has the same semantic obligation wherever its
            # Lean declaration happens to live. Lean's elaborated graph owns
            # module/source provenance; a namespace prefix is not evidence.
            route_kind = RouteKind.RESULT_SEMANTIC
        elif inventory_role == "source_semantic_declaration":
            route_kind = RouteKind.SOURCE_SEMANTIC_DECLARATION
        elif inventory_role in {
            "source_premise_declaration",
            "premise_declaration",
        }:
            route_kind = RouteKind.SOURCE_ASSUMPTION
        elif inventory_role == "proof_support":
            route_kind = RouteKind.PROOF_SUPPORT
        elif inventory_role in {
            "source_presentation_alias",
            "repeated_source_presentation",
        }:
            route_kind = RouteKind.SOURCE_PRESENTATION_ALIAS
        elif inventory_role in {
            "source_scope_exclusion",
            "quarantined_source_defect",
            "deep_audit_material",
            "source_context_observation",
        } or raw.get("scope_disposition"):
            route_kind = RouteKind.SOURCE_SCOPE_DISPOSITION
        elif conventions:
            route_kind = RouteKind.SOURCE_CONVENTION
        elif claim_bearing:
            route_kind = RouteKind.PENDING_SOURCE_ROUTE
        else:
            route_kind = RouteKind.SOURCE_CONTEXT
        return cls(
            source_item_id=source_item_id,
            source_kind=source_kind,
            route_kind=route_kind,
            claim_bearing=claim_bearing,
            inventory_role=inventory_role,
            spec_declaration=spec,
            evidence_declaration=evidence,
            evidence_mode=evidence_mode,
            semantic_review_target_kind=semantic_review_target_kind,
            semantic_review_declaration=semantic_review_declaration,
            semantic_declarations=semantic_declarations,
            support_declarations=support_tuple,
            convention_ids=conventions,
            source_component_of=source_component_of,
            anchor_sha256s=_anchor_digests(raw),
        )

    def projection(self) -> dict[str, Any]:
        result = {
            "source_item_id": self.source_item_id,
            "source_kind": self.source_kind,
            "route_kind": self.route_kind.value,
            "claim_bearing": self.claim_bearing,
            "inventory_role": self.inventory_role,
            "spec_declaration": self.spec_declaration,
            "evidence_declaration": self.evidence_declaration,
            "evidence_mode": self.evidence_mode,
            "semantic_review_target_kind": self.semantic_review_target_kind.value,
            "semantic_review_declaration": self.semantic_review_declaration,
            "support_declarations": list(self.support_declarations),
            "convention_ids": list(self.convention_ids),
            "source_component_of": self.source_component_of,
            "anchor_sha256s": list(self.anchor_sha256s),
        }
        # Preserve historical route identities exactly. Only the opt-in
        # source-role schema owns this field, so an empty value is omitted.
        if self.semantic_declarations:
            result["semantic_declarations"] = list(self.semantic_declarations)
        return result


@dataclass(frozen=True)
class EvidenceRouteSet:
    routes: tuple[EvidenceRoute, ...]
    sha256: str

    @classmethod
    def from_source_map(cls, source_map: object) -> "EvidenceRouteSet":
        if not isinstance(source_map, Mapping):
            raise ObligationRouteError("paper statement map is not an object")
        raw_items = source_map.get("items")
        if not isinstance(raw_items, Mapping):
            raise ObligationRouteError("paper statement map has no item ledger")
        routes = tuple(
            EvidenceRoute.from_source_item(
                str(source_item_id),
                raw_items[source_item_id],
            )
            for source_item_id in sorted(raw_items, key=str)
        )
        projection = [route.projection() for route in routes]
        return cls(routes=routes, sha256=_digest(projection))

    def projection(self) -> list[dict[str, Any]]:
        return [route.projection() for route in self.routes]

    def by_source_item(self) -> dict[str, EvidenceRoute]:
        """Return the uniquely keyed typed route ledger."""

        return {route.source_item_id: route for route in self.routes}

    def human_review_source_items(
        self,
        review_declarations: tuple[str, ...],
        source_condition_items: tuple[str, ...] = (),
    ) -> tuple[str, ...]:
        """Resolve one configured human surface to exact source-item IDs.

        Declaration names are routing coordinates only.  The typed source
        ledger owns the reviewed source items, and an explicit source-condition
        selection names source items directly.  This keeps display counts from
        becoming a second source-coverage authority.
        """

        if any(not name.strip() for name in review_declarations) or len(
            set(review_declarations)
        ) != len(review_declarations):
            raise ObligationRouteError(
                "human-review declarations contain an empty or duplicate name"
            )
        if any(not item.strip() for item in source_condition_items) or len(
            set(source_condition_items)
        ) != len(source_condition_items):
            raise ObligationRouteError(
                "human-review source conditions contain an empty or duplicate item"
            )

        def declaration_coordinates(route: EvidenceRoute) -> tuple[str, ...]:
            coordinates = list(route.semantic_declarations)
            if route.semantic_review_declaration:
                coordinates.append(route.semantic_review_declaration)
            return tuple(coordinates)

        selected: list[str] = []
        for configured in review_declarations:
            configured = configured.strip()
            candidates = {
                route.source_item_id
                for route in self.routes
                if route.claim_bearing
                and any(
                    declaration == configured
                    or declaration.rsplit(".", 1)[-1] == configured
                    for declaration in declaration_coordinates(route)
                )
            }
            if len(candidates) != 1:
                raise ObligationRouteError(
                    f"human-review declaration {configured!r} does not resolve "
                    "to exactly one claim-bearing source item"
                )
            selected.append(next(iter(candidates)))

        by_source_item = self.by_source_item()
        for source_item in source_condition_items:
            source_item = source_item.strip()
            route = by_source_item.get(source_item)
            if route is None or not route.claim_bearing:
                raise ObligationRouteError(
                    f"human-review source condition {source_item!r} is not a "
                    "claim-bearing source item"
                )
            selected.append(source_item)

        if len(selected) != len(set(selected)):
            raise ObligationRouteError(
                "human-review declarations and source conditions overlap"
            )
        return tuple(selected)

    def result_routes(self) -> tuple[EvidenceRoute, ...]:
        """Return the one typed route for every asserted source result."""

        return tuple(
            route
            for route in self.routes
            if route.route_kind is RouteKind.RESULT_SEMANTIC
        )

    def result_specifications(self) -> tuple[str, ...]:
        """Return the deterministic selected result-Spec surface."""

        return tuple(sorted(route.spec_declaration for route in self.result_routes()))

    def result_route_by_specification(self) -> dict[str, EvidenceRoute]:
        """Return the exact source route keyed by its semantic Spec."""

        result: dict[str, EvidenceRoute] = {}
        for route in self.result_routes():
            if route.spec_declaration in result:
                raise ObligationRouteError(
                    "one semantic Spec is routed by multiple source items"
                )
            result[route.spec_declaration] = route
        return result

    def source_semantic_declarations(self) -> tuple[str, ...]:
        """Return every explicitly role-routed source-semantic declaration.

        This route layer does not classify declarations from namespace or file
        spelling.  The loaded Lean environment owns the later paper/reusable-
        library partition through exact module ownership.
        """

        return tuple(
            sorted(
                {
                    declaration
                    for route in self.routes
                    if route.route_kind is RouteKind.SOURCE_SEMANTIC_DECLARATION
                    for declaration in route.semantic_declarations
                }
            )
        )

    def legacy_source_semantic_declarations_by_namespace(
        self, *, library: bool
    ) -> tuple[str, ...]:
        """Partition old presentation-only callers by historical spelling.

        Current audit, graph construction, and acceptance must use
        ``source_semantic_declarations`` and let Lean classify ownership.  This
        helper exists only while the staged legacy packet path remains
        readable; it grants no evidence credit.
        """

        return tuple(
            declaration
            for declaration in self.source_semantic_declarations()
            if declaration.startswith("AppliedModelingLib.") == library
        )


def typed_route_validation_required(source_map: object) -> bool:
    """Whether a map has opted into the shared semantic-route contract."""

    if not isinstance(source_map, Mapping):
        return False
    if source_map.get("semantic_contract_schema") is not None:
        return True
    items = source_map.get("items")
    return isinstance(items, Mapping) and any(
        isinstance(item, Mapping) and "semantic_contract" in item
        for item in items.values()
    )
