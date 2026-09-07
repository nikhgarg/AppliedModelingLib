#!/usr/bin/env python3
"""Authoritative semantic-obligation ledger and scope validators."""

from __future__ import annotations

import hashlib
import json
import re
import sys
from collections.abc import Callable
from pathlib import Path
from typing import Any

if __package__ in {None, ""}:  # Canonical imports under direct-file execution.
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scripts.lean_signature_manifest import signature_manifest_digest

EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.IGNORECASE,
)
NAME_ONLY_SOURCE_COVERAGE_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.IGNORECASE,
)
NAME_ONLY_SEMANTIC_EVIDENCE_RE = re.compile(
    r"\b(?:names? match|matched by name|same (?:theorem|lemma|definition|function|"
    r"field|predicate|wrapper) name|same identifier|identifiers? (?:match|coincide)|"
    r"same symbol|matching labels?|same label|phrase overlap|same wording)\b",
    re.IGNORECASE,
)
PROFILE_QUANTIFICATION_SCOPES = {
    "not_profile_based",
    "fixed_profile",
    "all_profiles",
    "existential_profile",
    "mixed_profile_scope",
}
QUANTIFICATION_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
}
SOURCE_ALGORITHM_CLAIM_LEVELS = {
    "not_algorithmic",
    "existence",
    "executable",
    "polynomial_time",
}
LEAN_ALGORITHM_CLAIM_LEVELS = SOURCE_ALGORITHM_CLAIM_LEVELS | {
    "noncomputable_existence"
}
RUNNER_PROVENANCE_KINDS = {
    "not_applicable",
    "same_formalized_runner",
    "proved_refinement",
    "independent_characterization",
    "missing",
}
RESULT_PROVENANCE_KINDS = {
    "not_applicable",
    "runner_derived",
    "preservation_bridge",
    "independent_characterization",
    "missing",
}
LEGACY_FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v2-shape-action-witness-count-execution"
)
FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v3-shape-action-witness-count-generic-execution"
)
SUPPORTED_FIDELITY_RISK_REVIEW_VERSIONS = {
    LEGACY_FIDELITY_RISK_REVIEW_VERSION,
    FIDELITY_RISK_REVIEW_VERSION,
}
LEGACY_FIDELITY_EXECUTION_SCOPE_FIELDS = (
    ("source_quota_turnout_scope", "source quota/turnout scope"),
    ("lean_quota_turnout_scope", "Lean quota/turnout scope"),
    ("source_seat_termination_scope", "source seat-count/stopping scope"),
    ("lean_seat_termination_scope", "Lean seat-count/stopping scope"),
    ("source_round_scope", "source round/executor scope"),
    ("lean_round_scope", "Lean round/executor scope"),
    ("source_arithmetic_domain", "source arithmetic domain"),
    ("lean_arithmetic_domain", "Lean arithmetic domain"),
    ("source_cost_claim_scope", "source cost/complexity scope"),
    ("lean_cost_claim_scope", "Lean cost/complexity scope"),
    ("global_claim_bridge_basis", "global-claim bridge basis"),
)
FIDELITY_EXECUTION_SCOPE_FIELDS = (
    ("source_input_scope", "source input scope"),
    ("lean_input_scope", "Lean input scope"),
    ("source_state_transition_scope", "source state-transition scope"),
    ("lean_state_transition_scope", "Lean state-transition scope"),
    ("source_termination_scope", "source termination scope"),
    ("lean_termination_scope", "Lean termination scope"),
    ("source_numeric_representation", "source numeric representation"),
    ("lean_numeric_representation", "Lean numeric representation"),
    ("source_cost_scope", "source cost/complexity scope"),
    ("lean_cost_scope", "Lean cost/complexity scope"),
    ("global_claim_bridge_basis", "global-claim bridge basis"),
)
FIDELITY_RISK_DIMENSIONS = {
    "output_shape",
    "adversarial_action_space",
    "coherent_extrema_witness",
    "cardinality_fibers",
    "execution_claim_scope",
}
FIDELITY_RISK_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
    "uncertain",
}
COHERENT_EXTREMA_WITNESS_STATUSES = {
    "not_required",
    "same_coherent_witness",
    "proved_jointly_realizable",
    "separate_witnesses_only",
    "missing",
}
COUNTING_SEMANTICS = {
    "syntactic_family_cardinality",
    "nonempty_realized_fibers",
    "other",
}
SURJECTIVITY_STATUSES = {
    "not_required",
    "definitionally_surjective",
    "proved_surjective",
    "missing",
}
SEMANTIC_WORLD_ROLES = {"source", "lean", "shared"}
SEMANTIC_WORLD_BRIDGE_RELATIONS = {
    "definitionally_equal",
    "equivalent",
    "refines",
    "simulates",
    "preserves_result",
}
OPERATIONAL_COMPLEXITY_REVIEW_VERSION = (
    "operational-complexity-review-v1-transitive-work-accounting"
)
OPERATIONAL_WORK_CATEGORIES = {
    "traversal_enumeration_length",
    "duplicate_multiplicity",
    "materialization_rebuilding",
    "representation_container_primitives",
    "exact_rational_bit_growth",
}
OPERATIONAL_WORK_STATUSES = {
    "charged",
    "proved_absent",
    "not_applicable",
    "missing",
    "excluded_by_claim",
}
FULL_RUNTIME_MATCH_WORK_STATUSES = {
    "charged",
    "proved_absent",
    "not_applicable",
}
CLOSURE_ELIMINATION_EVIDENCE_KINDS = {
    "generated_ir_call_graph",
    "cost_threaded_executor",
}
NAMED_DEFINITION_CLASSIFICATIONS = {
    "substantive",
    "self_characterizing",
    "routing_only",
}
NUMERIC_SEMANTIC_RELATIONS = {
    "definitionally_equal",
    "proved_equivalent",
    "witness_specific_equivalent",
    "different",
    "uncertain",
}
DISCRETE_SEMANTIC_RELATIONS = NUMERIC_SEMANTIC_RELATIONS
NUMERIC_SEMANTIC_CONSTANTS = {
    "Add.add",
    "Div.div",
    "HAdd.hAdd",
    "HDiv.hDiv",
    "HMul.hMul",
    "HSub.hSub",
    "LE.le",
    "LT.lt",
    "Mul.mul",
    "Nat.div",
    "OfNat.ofNat",
    "Sub.sub",
}
DISCRETE_SEMANTIC_CONSTANT_PREFIXES = (
    "List.contains",
    "List.drop",
    "List.erase",
    "List.filter",
    "List.find",
    "List.get",
    "List.head",
    "List.idxOf",
    "List.lookup",
    "List.mem",
    "List.tail",
)


# `conditional_boundary` is the historical sidecar token. The user-facing
# term is deliberately narrower: the source conclusion is exact and every
# additional Lean input is explicit and audited.
VISIBLE_PREMISE_BOUNDARY_LABEL = "visible-premise boundary"
CONDITIONAL_BOUNDARY_RESOLUTION = "conditional_boundary"
CONDITIONAL_BOUNDARY_RESOLUTION_ALIASES = {
    "conditional_boundary",
    "visible_premise_boundary",
    "visible-premise-boundary",
    "visible premise boundary",
    "accepted_boundary",
    "known_boundary",
    "external_library_boundary",
    "known_dependence_on_external_library",
    "known_external_library_dependence",
    "intentional_mismatch",
}


def _normalize_llm_match_judgment(raw: Any) -> str:
    """Normalize LLM match verdicts for dashboard display."""

    if isinstance(raw, bool):
        return "matches" if raw else "mismatch"
    value = str(raw or "").strip().lower()
    if value in {"match", "matches", "yes", "true", "equivalent", "same"}:
        return "matches"
    if value in {"mismatch", "does_not_match", "does not match", "no", "false", "different"}:
        return "mismatch"
    if value in {"uncertain", "unknown", "unsure", "partial", "needs_review"}:
        return "uncertain"
    return value


def _normalize_llm_match_resolution(raw: Any) -> str:
    """Normalize optional LLM statement-match resolution categories."""

    value = re.sub(r"[\s-]+", "_", str(raw or "").strip().lower())
    if not value or value in {"none", "unresolved", "open"}:
        return ""
    if value in CONDITIONAL_BOUNDARY_RESOLUTION_ALIASES:
        return CONDITIONAL_BOUNDARY_RESOLUTION
    return value


def signature_manifest_atom_digest(atom: Any) -> str:
    """Hash one name-free manifest atom for v10 Lean-obligation routing."""

    if not isinstance(atom, dict):
        return ""
    payload = {
        "ref": str(atom.get("ref") or "").strip(),
        "role": str(atom.get("role") or "").strip(),
        "canonical": atom.get("canonical"),
    }
    if payload["role"] != "conclusion":
        payload["binder_info"] = str(atom.get("binder_info") or "").strip()
    if not payload["ref"] or not payload["role"] or payload["canonical"] is None:
        return ""
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def operational_complexity_review_error(
    raw: Any, expected_complexity_conclusion_id: str
) -> str:
    """Validate operational evidence required for a full polynomial-time match.

    Identifiers in this review route graph edges and conclusion references only.
    Runtime credit comes from expanded operation semantics, complete reachable-
    branch coverage, a worst-case recurrence, and explicit work accounting.
    """

    if not isinstance(raw, dict):
        return "polynomial-time match is missing operational_complexity_review"

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    if required_string(raw.get("schema_version")) != OPERATIONAL_COMPLEXITY_REVIEW_VERSION:
        return "operational complexity review has an invalid schema_version"

    for field, label in (
        ("executor_semantics", "executor semantics"),
        ("input_domain", "input domain"),
        ("input_size_measure", "input-size measure"),
    ):
        if not substantive(raw.get(field)):
            return f"operational complexity review lacks substantive {label}"

    graph = raw.get("dependency_graph")
    if not isinstance(graph, dict):
        return "operational complexity review has no dependency_graph object"
    nodes = graph.get("nodes")
    edges = graph.get("edges")
    roots = graph.get("root_node_ids")
    if not isinstance(nodes, list) or not nodes:
        return "operational dependency graph has no nodes"
    if not isinstance(edges, list):
        return "operational dependency graph has no edges list"
    if not isinstance(roots, list) or not roots:
        return "operational dependency graph has no root_node_ids"

    node_ids: set[str] = set()
    adjacency: dict[str, set[str]] = {}
    node_work_categories: set[str] = set()
    for node in nodes:
        if not isinstance(node, dict):
            return "operational dependency graph node is not an object"
        node_id = required_string(node.get("id"))
        if not node_id or node_id in node_ids:
            return "operational dependency graph node has a missing or duplicate id"
        if not substantive(node.get("operation_semantics")):
            return "operational dependency graph node lacks substantive operation semantics"
        if not substantive(node.get("reachable_branch_domain")):
            return "operational dependency graph node lacks a reachable branch domain"
        categories = node.get("work_accounting_categories")
        if not isinstance(categories, list) or not categories:
            return "operational dependency graph node has no work-accounting categories"
        normalized_categories = [required_string(item) for item in categories]
        if any(not item for item in normalized_categories):
            return "operational dependency graph node has an empty work category"
        if len(normalized_categories) != len(set(normalized_categories)):
            return "operational dependency graph node has duplicate work categories"
        if set(normalized_categories) - OPERATIONAL_WORK_CATEGORIES:
            return "operational dependency graph node has an unknown work category"
        node_work_categories.update(normalized_categories)
        node_ids.add(node_id)
        adjacency[node_id] = set()

    normalized_roots = [required_string(item) for item in roots]
    if any(not item for item in normalized_roots):
        return "operational dependency graph has an empty root node id"
    if len(normalized_roots) != len(set(normalized_roots)):
        return "operational dependency graph has duplicate root node ids"
    if set(normalized_roots) - node_ids:
        return "operational dependency graph references an unknown root node"

    for edge in edges:
        if not isinstance(edge, dict):
            return "operational dependency graph edge is not an object"
        from_node = required_string(edge.get("from_node_id"))
        to_node = required_string(edge.get("to_node_id"))
        if from_node not in node_ids or to_node not in node_ids:
            return "operational dependency graph edge has an unknown endpoint"
        if not substantive(edge.get("invocation_semantics")):
            return "operational dependency graph edge lacks invocation semantics"
        if not substantive(edge.get("branch_condition")):
            return "operational dependency graph edge lacks a branch condition"
        adjacency[from_node].add(to_node)

    reachable = set(normalized_roots)
    frontier = list(normalized_roots)
    while frontier:
        current = frontier.pop()
        for dependency in adjacency[current]:
            if dependency not in reachable:
                reachable.add(dependency)
                frontier.append(dependency)
    if reachable != node_ids:
        return "operational dependency graph contains a node unreachable from its roots"
    if graph.get("transitive_closure_complete") is not True:
        return "operational dependency graph does not certify complete transitive closure"
    if graph.get("all_reachable_branches_complete") is not True:
        return "operational dependency graph does not cover every reachable branch"
    if not substantive(graph.get("coverage_basis")):
        return "operational dependency graph lacks a substantive coverage basis"

    if not substantive(raw.get("worst_case_recurrence")):
        return "operational complexity review lacks a worst-case recurrence"
    if not substantive(raw.get("worst_case_bound")):
        return "operational complexity review lacks a worst-case bound"
    conclusion_id = required_string(raw.get("complexity_lean_conclusion_id"))
    if not conclusion_id or conclusion_id != expected_complexity_conclusion_id:
        return "operational complexity review is not bound to the complexity conclusion"
    if not substantive(raw.get("complexity_statement_binding")):
        return "operational complexity review lacks a semantic complexity-statement binding"

    work_items = raw.get("work_accounting")
    if not isinstance(work_items, list):
        return "operational complexity review has no work_accounting list"
    recorded_categories: set[str] = set()
    for item in work_items:
        if not isinstance(item, dict):
            return "operational work-accounting item is not an object"
        category = required_string(item.get("category")).lower()
        if category not in OPERATIONAL_WORK_CATEGORIES:
            return "operational work-accounting item has an invalid category"
        if category in recorded_categories:
            return "operational work-accounting has a duplicate category"
        recorded_categories.add(category)
        status = required_string(item.get("status")).lower()
        if status not in OPERATIONAL_WORK_STATUSES:
            return "operational work-accounting item has an invalid status"
        if status not in FULL_RUNTIME_MATCH_WORK_STATUSES:
            return (
                "polynomial-time match has missing or excluded_by_claim "
                "operational work"
            )
        if status == "charged" and category not in node_work_categories:
            return (
                "charged operational work category is not linked to a dependency "
                "graph node"
            )
        for field, label in (
            ("operation_semantics", "operation semantics"),
            (
                "worst_case_charge_or_absence_basis",
                "worst-case charge or absence basis",
            ),
            ("evidence_basis", "evidence basis"),
        ):
            if not substantive(item.get(field)):
                return f"operational work-accounting item lacks substantive {label}"
    if recorded_categories != OPERATIONAL_WORK_CATEGORIES:
        return "operational work-accounting does not cover every required category"

    closure = raw.get("closure_elimination")
    if not isinstance(closure, dict):
        return "operational complexity review has no closure_elimination object"
    material = closure.get("material")
    if not isinstance(material, bool):
        return "closure_elimination has no Boolean material field"
    if not material:
        if not substantive(closure.get("non_material_basis")):
            return "non-material closure elimination lacks a substantive basis"
        return ""

    evidence_kind = required_string(closure.get("evidence_kind")).lower()
    if evidence_kind not in CLOSURE_ELIMINATION_EVIDENCE_KINDS:
        return "material closure elimination has an invalid evidence_kind"
    for field, label in (
        ("evidence_artifact_sha256", "evidence artifact"),
        ("audited_source_sha256", "audited source"),
    ):
        digest = required_string(closure.get(field))
        if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            return f"material closure elimination lacks a valid {label} SHA-256 pin"
    if not required_string(closure.get("evidence_locator")):
        return "material closure elimination has no evidence locator"
    for field, label in (
        ("old_dependency_semantics", "old dependency semantics"),
        ("semantic_binding", "semantic artifact/source binding"),
        ("elimination_basis", "dependency-elimination basis"),
    ):
        if not substantive(closure.get(field)):
            return f"material closure elimination lacks substantive {label}"
    if closure.get("symbol_names_used_as_evidence") is not False:
        return "material closure elimination may not use symbol names as evidence"
    return ""


def fidelity_risk_review_error(
    raw: Any,
    source_obligations: dict[str, str],
    lean_obligations: dict[str, str],
    verdict: str,
    source_algorithm_level: str,
) -> str:
    """Validate source/Lean fidelity hazards without using declaration names.

    The statement manifest and obligation ledger identify where a fact occurs,
    but identifiers do not establish its semantics.  This review forces an
    independent comparison of five recurring failure modes and binds every
    positive match to a visible Lean conclusion.
    """

    if not isinstance(raw, dict):
        return "semantic scope review has no fidelity_risk_review object"
    schema_version = raw.get("schema_version")
    if (
        not isinstance(schema_version, str)
        or schema_version not in SUPPORTED_FIDELITY_RISK_REVIEW_VERSIONS
    ):
        return "fidelity risk review has an invalid schema_version"

    dimensions = raw.get("dimensions")
    if not isinstance(dimensions, dict):
        return "fidelity risk review has no dimensions object"
    dimension_names = set(dimensions)
    if dimension_names != FIDELITY_RISK_DIMENSIONS:
        missing = sorted(FIDELITY_RISK_DIMENSIONS - dimension_names)
        extra = sorted(dimension_names - FIDELITY_RISK_DIMENSIONS)
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unknown " + ", ".join(extra))
        return "fidelity risk review dimensions are incomplete: " + "; ".join(details)

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    def obligation_ids(
        value: Any, known: dict[str, str], label: str
    ) -> tuple[set[str], str]:
        if not isinstance(value, list) or not value:
            return set(), f"{label} must be a nonempty list"
        normalized = [required_string(item) for item in value]
        if any(not item for item in normalized):
            return set(), f"{label} contains an empty obligation id"
        if len(normalized) != len(set(normalized)):
            return set(), f"{label} contains duplicate obligation ids"
        if set(normalized) - set(known):
            return set(), f"{label} references unknown obligation ids"
        return set(normalized), ""

    conclusion_ids = {
        key for key, kind in lean_obligations.items() if kind == "conclusion"
    }
    normalized: dict[str, dict[str, Any]] = {}
    for name in sorted(FIDELITY_RISK_DIMENSIONS):
        item = dimensions.get(name)
        if not isinstance(item, dict):
            return f"fidelity risk dimension `{name}` is not an object"
        applicable = item.get("applicable")
        if not isinstance(applicable, bool):
            return f"fidelity risk dimension `{name}` has no Boolean applicable field"
        normalized[name] = item
        if not applicable:
            if not substantive(item.get("absence_basis")):
                return f"fidelity risk dimension `{name}` lacks a substantive absence_basis"
            continue

        _, error = obligation_ids(
            item.get("source_obligation_ids"),
            source_obligations,
            f"fidelity risk dimension `{name}` source_obligation_ids",
        )
        if error:
            return error
        lean_ids, error = obligation_ids(
            item.get("lean_obligation_ids"),
            lean_obligations,
            f"fidelity risk dimension `{name}` lean_obligation_ids",
        )
        if error:
            return error
        for field, label in (
            ("source_semantics", "source semantics"),
            ("lean_semantics", "Lean semantics"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"fidelity risk dimension `{name}` lacks substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in FIDELITY_RISK_RELATIONS:
            return f"fidelity risk dimension `{name}` has an invalid relation"
        if verdict == "matches":
            if relation != "equivalent":
                return (
                    f"matches judgment records non-equivalent `{name}` semantics"
                )
            if not substantive(item.get("lean_evidence_statement")):
                return (
                    f"matching fidelity risk dimension `{name}` lacks a substantive "
                    "Lean evidence statement"
                )
            evidence_id = required_string(item.get("lean_evidence_conclusion_id"))
            if evidence_id not in conclusion_ids:
                return (
                    f"matching fidelity risk dimension `{name}` is not bound to a "
                    "Lean conclusion obligation"
                )
            if evidence_id not in lean_ids:
                return (
                    f"matching fidelity risk dimension `{name}` evidence conclusion "
                    "is not among its reviewed Lean obligations"
                )

    output_shape = normalized["output_shape"]
    if output_shape.get("applicable"):
        for field, label in (
            ("source_output_shape", "source output arity/shape"),
            ("lean_output_shape", "Lean output arity/shape"),
            ("projection_terminal_policy", "projection and terminal-component policy"),
            ("arity_basis", "arity comparison basis"),
        ):
            if not substantive(output_shape.get(field)):
                return f"output-shape review lacks substantive {label}"

    action_space = normalized["adversarial_action_space"]
    if action_space.get("applicable"):
        for field, label in (
            ("source_action_space", "source action-space semantics"),
            ("lean_action_space", "Lean action-space semantics"),
            ("carrier_capacity_basis", "carrier/capacity basis"),
            ("duplicate_interaction_basis", "duplicate-interaction basis"),
            ("nonvacuity_basis", "nonvacuity basis"),
        ):
            if not substantive(action_space.get(field)):
                return f"adversarial action-space review lacks substantive {label}"
        source_nonvacuous = action_space.get("source_nonvacuous")
        lean_nonvacuous = action_space.get("lean_nonvacuous")
        if not isinstance(source_nonvacuous, bool) or not isinstance(
            lean_nonvacuous, bool
        ):
            return "adversarial action-space review lacks Boolean nonvacuity judgments"
        if verdict == "matches" and not (source_nonvacuous and lean_nonvacuous):
            return (
                "matching universal adversarial transformation has a vacuous or "
                "ill-formed legal action space"
            )

    extrema = normalized["coherent_extrema_witness"]
    if extrema.get("applicable"):
        for field, label in (
            ("source_extrema_semantics", "source extrema semantics"),
            ("lean_extrema_semantics", "Lean extrema semantics"),
            ("coherent_witness_basis", "coherent-witness basis"),
            ("runner_refinement_basis", "actual-runner/refinement basis"),
        ):
            if not substantive(extrema.get(field)):
                return f"coherent-extrema review lacks substantive {label}"
        source_combines = extrema.get("source_combines_candidatewise_extrema")
        lean_combines = extrema.get("lean_combines_candidatewise_extrema")
        if not isinstance(source_combines, bool) or not isinstance(
            lean_combines, bool
        ):
            return "coherent-extrema review lacks Boolean candidatewise-combination judgments"
        witness_status = required_string(extrema.get("coherent_witness_status")).lower()
        if witness_status not in COHERENT_EXTREMA_WITNESS_STATUSES:
            return "coherent-extrema review has an invalid coherent_witness_status"
        if (source_combines or lean_combines) and witness_status == "not_required":
            return "candidatewise extrema are combined without a coherent-witness audit"
        if verdict == "matches" and witness_status not in {
            "not_required",
            "same_coherent_witness",
            "proved_jointly_realizable",
        }:
            return (
                "matching extrema claim combines bounds that are not realized by one "
                "coherent witness"
            )

    counting = normalized["cardinality_fibers"]
    if counting.get("applicable"):
        for field, label in (
            ("source_counted_object", "source counted object"),
            ("lean_counted_object", "Lean counted object"),
            ("realized_fiber_semantics", "realized-fiber semantics"),
            ("surjectivity_basis", "surjectivity basis"),
        ):
            if not substantive(counting.get(field)):
                return f"cardinality/fiber review lacks substantive {label}"
        source_counting = required_string(counting.get("source_counting_semantics")).lower()
        lean_counting = required_string(counting.get("lean_counting_semantics")).lower()
        if source_counting not in COUNTING_SEMANTICS or lean_counting not in COUNTING_SEMANTICS:
            return "cardinality/fiber review has invalid counting semantics"
        source_exact = counting.get("source_claims_exact_cardinality")
        lean_exact = counting.get("lean_claims_exact_cardinality")
        if not isinstance(source_exact, bool) or not isinstance(lean_exact, bool):
            return "cardinality/fiber review lacks Boolean exact-cardinality judgments"
        if verdict == "matches" and source_exact != lean_exact:
            return "matches judgment confuses exact cardinality with a bound"
        status = required_string(counting.get("surjectivity_status")).lower()
        if status not in SURJECTIVITY_STATUSES:
            return "cardinality/fiber review has an invalid surjectivity_status"
        crosses_family_fibers = {
            source_counting,
            lean_counting,
        } == {"syntactic_family_cardinality", "nonempty_realized_fibers"}
        claims_family_fiber_equality = counting.get(
            "claims_syntactic_family_equals_realized_fibers"
        )
        if not isinstance(claims_family_fiber_equality, bool):
            return (
                "cardinality/fiber review lacks a Boolean "
                "claims_syntactic_family_equals_realized_fibers field"
            )
        surjectivity_required = (
            claims_family_fiber_equality
            or (verdict == "matches" and source_exact and crosses_family_fibers)
        )
        if surjectivity_required and status not in {
            "definitionally_surjective",
            "proved_surjective",
        }:
            return (
                "exact syntactic-family/realized-fiber equality lacks surjectivity evidence"
            )
        if status in {"definitionally_surjective", "proved_surjective"}:
            if not substantive(counting.get("surjectivity_statement")):
                return "surjectivity evidence lacks a substantive mathematical statement"
            surjectivity_id = required_string(
                counting.get("surjectivity_lean_conclusion_id")
            )
            if surjectivity_id not in conclusion_ids:
                return "surjectivity evidence is not bound to a Lean conclusion obligation"
            counting_lean_ids = {
                required_string(item)
                for item in counting.get("lean_obligation_ids", [])
            }
            if surjectivity_id not in counting_lean_ids:
                return (
                    "surjectivity evidence conclusion is not among the cardinality "
                    "dimension's reviewed Lean obligations"
                )

    execution_scope = normalized["execution_claim_scope"]
    if source_algorithm_level != "not_algorithmic" and not execution_scope.get(
        "applicable"
    ):
        return "algorithmic row lacks an applicable execution-claim scope review"
    if execution_scope.get("applicable"):
        execution_fields = (
            LEGACY_FIDELITY_EXECUTION_SCOPE_FIELDS
            if schema_version == LEGACY_FIDELITY_RISK_REVIEW_VERSION
            else FIDELITY_EXECUTION_SCOPE_FIELDS
        )
        for field, label in execution_fields:
            if not substantive(execution_scope.get(field)):
                return f"execution-claim scope review lacks substantive {label}"
    return ""


def semantic_scope_review_error(
    raw: Any,
    source_obligations: dict[str, str],
    lean_obligations: dict[str, str],
    lean_manifest_atoms: dict[str, dict[str, Any]],
    verdict: str,
    *,
    require_source_definition_semantics_review: bool = False,
) -> str:
    """Validate the name-independent semantic-world review for one row.

    The declaration manifest freezes the Lean type, but one final proposition
    atom may contain several logically unrelated conjuncts.  In particular,
    runner success and a self-characterizing predicate about an independently
    supplied output do not establish that the runner produced or preserves that
    output. V10 therefore requires the reviewer to record profile scope,
    definition expansion, algorithmic strength, runner/result provenance,
    fidelity-risk dimensions, and every bridge between distinct semantic
    worlds. The enumerated relations are checked structurally; the mathematical
    truth of the prose remains an independent source-review obligation.  A
    source-definition route has one extra structural review because a
    total Lean definition can otherwise conceal a source-domain extension or
    an omitted operational guarantee.
    """

    if not isinstance(raw, dict):
        return "missing `semantic_scope_review` object"

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    def canonical_contains_constant(value: Any, predicate: Callable[[str], bool]) -> bool:
        if isinstance(value, list):
            return any(canonical_contains_constant(item, predicate) for item in value)
        if not isinstance(value, dict):
            return False
        if value.get("tag") == "const" and predicate(str(value.get("name") or "")):
            return True
        return any(canonical_contains_constant(item, predicate) for item in value.values())

    def lean_atom_has_numeric_semantics(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"), lambda name: name in NUMERIC_SEMANTIC_CONSTANTS
        )

    def lean_atom_has_discrete_semantics(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"),
            lambda name: name.startswith(DISCRETE_SEMANTIC_CONSTANT_PREFIXES),
        )

    def lean_atom_has_expanded_definition(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}

        def contains_expansion(value: Any) -> bool:
            if isinstance(value, list):
                return any(contains_expansion(item) for item in value)
            if not isinstance(value, dict):
                return False
            if value.get("tag") in {
                "definition",
                "inductive",
                "inlined_definition",
                "local_constructor",
                "local_inductive",
                "local_recursor",
                "local_theorem",
            }:
                return True
            return any(contains_expansion(item) for item in value.values())

        return contains_expansion(atom.get("canonical"))

    def lean_conclusion_exposes_equivalence(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"), lambda name: name in {"Eq", "Iff"}
        )

    def obligation_id_list(
        value: Any, field: str, known: dict[str, str], *, nonempty: bool
    ) -> tuple[set[str], str]:
        if not isinstance(value, list):
            return set(), f"{field} is not a list"
        normalized = [required_string(item) for item in value]
        if any(not item for item in normalized):
            return set(), f"{field} contains an empty obligation id"
        if len(normalized) != len(set(normalized)):
            return set(), f"{field} contains duplicate obligation ids"
        if nonempty and not normalized:
            return set(), f"{field} must not be empty"
        unknown = set(normalized) - set(known)
        if unknown:
            return set(), f"{field} references unknown obligation ids"
        return set(normalized), ""

    def operator_review_coverage_error(
        review: dict[str, Any],
        items: list[Any],
        *,
        source_item_field: str,
        lean_item_field: str,
        non_source_field: str,
        non_lean_field: str,
        label: str,
        lean_absence_conflict: Callable[[str], bool],
    ) -> str:
        covered_source: set[str] = set()
        covered_lean: set[str] = set()
        for item in items:
            if not isinstance(item, dict):
                return f"{label} review item is not an object"
            source_ids, error = obligation_id_list(
                item.get(source_item_field),
                f"{label} review item {source_item_field}",
                source_obligations,
                nonempty=True,
            )
            if error:
                return error
            lean_ids, error = obligation_id_list(
                item.get(lean_item_field),
                f"{label} review item {lean_item_field}",
                lean_obligations,
                nonempty=True,
            )
            if error:
                return error
            covered_source.update(source_ids)
            covered_lean.update(lean_ids)
        non_source, error = obligation_id_list(
            review.get(non_source_field),
            non_source_field,
            source_obligations,
            nonempty=False,
        )
        if error:
            return error
        non_lean, error = obligation_id_list(
            review.get(non_lean_field),
            non_lean_field,
            lean_obligations,
            nonempty=False,
        )
        if error:
            return error
        if covered_source & non_source:
            return f"{label} source obligations are both reviewed and classified absent"
        if covered_lean & non_lean:
            return f"{label} Lean obligations are both reviewed and classified absent"
        if covered_source | non_source != set(source_obligations):
            return f"{label} review does not cover every source obligation"
        if covered_lean | non_lean != set(lean_obligations):
            return f"{label} review does not cover every Lean obligation"
        conflicts = sorted(item for item in non_lean if lean_absence_conflict(item))
        if conflicts:
            return (
                f"{label} review classifies manifest-visible operator semantics as absent: "
                + ", ".join(conflicts)
            )
        return ""

    source_scope = required_string(raw.get("source_quantification")).lower()
    lean_scope = required_string(raw.get("lean_quantification")).lower()
    scope_relation = required_string(raw.get("quantification_relation")).lower()
    if source_scope not in PROFILE_QUANTIFICATION_SCOPES:
        return "semantic scope review has an invalid source_quantification"
    if lean_scope not in PROFILE_QUANTIFICATION_SCOPES:
        return "semantic scope review has an invalid lean_quantification"
    if scope_relation not in QUANTIFICATION_RELATIONS:
        return "semantic scope review has an invalid quantification_relation"
    if not substantive(raw.get("source_quantification_basis")):
        return "semantic scope review lacks a substantive source quantification basis"
    if not substantive(raw.get("lean_quantification_basis")):
        return "semantic scope review lacks a substantive Lean quantification basis"
    if verdict == "matches":
        if scope_relation != "equivalent":
            return "matches judgment records non-equivalent source/Lean quantification"
        fixed_or_global = {
            "fixed_profile",
            "all_profiles",
            "existential_profile",
        }
        if source_scope in fixed_or_global and lean_scope in fixed_or_global:
            if source_scope != lean_scope:
                return "matches judgment confuses fixed-, existential-, and all-profile scope"
        elif source_scope != lean_scope:
            return "matches judgment records different source/Lean profile scope"

    definition_review = raw.get("named_definition_review")
    if not isinstance(definition_review, dict):
        return "semantic scope review has no named_definition_review object"
    definitions_present = definition_review.get("definitions_present")
    if not isinstance(definitions_present, bool):
        return "named_definition_review has no Boolean definitions_present"
    definition_items = definition_review.get("items")
    if not isinstance(definition_items, list):
        return "named_definition_review has no items list"
    if definitions_present != bool(definition_items):
        return "named_definition_review presence flag does not match its items"
    if not definitions_present and not substantive(
        definition_review.get("absence_basis")
    ):
        return "named_definition_review lacks a substantive absence_basis"
    covered_definition_obligations: set[str] = set()
    for item in definition_items:
        if not isinstance(item, dict):
            return "named definition review item is not an object"
        obligation_ids, error = obligation_id_list(
            item.get("lean_obligation_ids"),
            "named definition review item lean_obligation_ids",
            lean_obligations,
            nonempty=True,
        )
        if error:
            return error
        covered_definition_obligations.update(obligation_ids)
    non_definition_obligations, error = obligation_id_list(
        definition_review.get("non_definition_lean_obligation_ids"),
        "non_definition_lean_obligation_ids",
        lean_obligations,
        nonempty=False,
    )
    if error:
        return error
    if covered_definition_obligations & non_definition_obligations:
        return "Lean obligations are both definition-reviewed and classified definition-free"
    if covered_definition_obligations | non_definition_obligations != set(
        lean_obligations
    ):
        return "named definition review does not cover every Lean obligation"
    hidden_expansions = sorted(
        item
        for item in non_definition_obligations
        if lean_atom_has_expanded_definition(item)
    )
    if hidden_expansions:
        return (
            "named definition review classifies manifest-expanded definitions as absent: "
            + ", ".join(hidden_expansions)
        )
    for item in definition_items:
        if not isinstance(item, dict):
            return "named definition review item is not an object"
        if not required_string(item.get("surface_expression")):
            return "named definition review item has no surface_expression"
        if not substantive(item.get("unfolded_semantics")):
            return "named definition review item lacks substantive unfolded semantics"
        if not substantive(item.get("expansion_basis")):
            return "named definition review item lacks a substantive expansion basis"
        recursive_dependencies = item.get("recursive_result_dependencies")
        if not isinstance(recursive_dependencies, list):
            return "named definition review item has no recursive_result_dependencies list"
        recursive_complete = item.get("recursive_expansion_complete")
        if not isinstance(recursive_complete, bool):
            return "named definition review item has no Boolean recursive_expansion_complete"
        seen_dependencies: set[str] = set()
        for dependency in recursive_dependencies:
            if not isinstance(dependency, dict):
                return "recursive named-definition dependency is not an object"
            dependency_expression = required_string(
                dependency.get("surface_expression")
            )
            if not dependency_expression or dependency_expression in seen_dependencies:
                return "recursive named-definition dependency is missing or duplicated"
            seen_dependencies.add(dependency_expression)
            if not substantive(dependency.get("unfolded_semantics")):
                return (
                    "recursive named-definition dependency lacks substantive "
                    "unfolded semantics"
                )
            if not substantive(dependency.get("expansion_basis")):
                return (
                    "recursive named-definition dependency lacks a substantive "
                    "expansion basis"
                )
        if verdict == "matches" and not recursive_complete:
            return (
                "matches judgment has an incomplete recursive named-definition expansion"
            )
        classification = required_string(item.get("classification")).lower()
        if classification not in NAMED_DEFINITION_CLASSIFICATIONS:
            return "named definition review item has an invalid classification"
        used_as_evidence = item.get("used_as_source_conclusion_evidence")
        if not isinstance(used_as_evidence, bool):
            return (
                "named definition review item has no Boolean "
                "used_as_source_conclusion_evidence"
            )
        if classification == "self_characterizing" and used_as_evidence:
            return (
                "self-characterizing definition cannot justify a source conclusion; "
                "require runner-derived provenance or a preservation/refinement bridge"
            )

    # This is deliberately keyed by the pinned source item's semantic kind
    # (see the caller), not by a declaration name.  It is separate from the
    # recursive named-definition expansion above: that expansion asks what a
    # Lean wrapper means, while this review asks whether the source *defined
    # object* has been extended, totalized, or stripped of an advertised
    # operational property.
    source_definition_review = raw.get("source_definition_semantics_review")
    if require_source_definition_semantics_review and not isinstance(
        source_definition_review, dict
    ):
        return (
            "source-expression route lacks "
            "source_definition_semantics_review"
        )
    if source_definition_review is not None:
        if not isinstance(source_definition_review, dict):
            return "source_definition_semantics_review is not an object"
        source_ids, error = obligation_id_list(
            source_definition_review.get("source_obligation_ids"),
            "source_definition_semantics_review source_obligation_ids",
            source_obligations,
            nonempty=True,
        )
        if error:
            return error
        lean_ids, error = obligation_id_list(
            source_definition_review.get("lean_obligation_ids"),
            "source_definition_semantics_review lean_obligation_ids",
            lean_obligations,
            nonempty=True,
        )
        if error:
            return error
        # A source-facing definition review must cover the full visible
        # interface.  Reviewing just its result lets a hidden domain premise
        # or an instance-carried domain restriction escape the comparison.
        if source_ids != set(source_obligations):
            return (
                "source_definition_semantics_review does not cover every "
                "source obligation"
            )
        if lean_ids != set(lean_obligations):
            return (
                "source_definition_semantics_review does not cover every "
                "Lean obligation"
            )

        for source_field, lean_field, relation_field, label in (
            (
                "source_legal_domain",
                "lean_legal_domain",
                "domain_relation",
                "legal domain",
            ),
            (
                "source_outside_domain_behavior",
                "lean_outside_domain_behavior",
                "outside_domain_relation",
                "outside-domain/totalization behavior",
            ),
            (
                "source_operational_semantics",
                "lean_operational_semantics",
                "operational_relation",
                "operational meaning",
            ),
        ):
            if not substantive(source_definition_review.get(source_field)):
                return (
                    "source_definition_semantics_review lacks substantive source "
                    f"{label}"
                )
            if not substantive(source_definition_review.get(lean_field)):
                return (
                    "source_definition_semantics_review lacks substantive Lean "
                    f"{label}"
                )
            relation = required_string(
                source_definition_review.get(relation_field)
            ).lower()
            if relation not in SOURCE_DEFINITION_SEMANTIC_RELATIONS:
                return (
                    "source_definition_semantics_review has invalid "
                    f"{relation_field}"
                )
            if verdict == "matches" and relation != "equivalent":
                return (
                    "matches judgment records non-equivalent source-definition "
                    f"{label}"
                )

        property_status = required_string(
            source_definition_review.get("advertised_property_status")
        ).lower()
        if property_status not in SOURCE_DEFINITION_PROPERTY_STATUSES:
            return (
                "source_definition_semantics_review has invalid "
                "advertised_property_status"
            )
        properties = source_definition_review.get("advertised_properties")
        if not isinstance(properties, list):
            return "source_definition_semantics_review has no advertised_properties list"
        if property_status == "no_advertised_properties":
            if properties:
                return (
                    "no_advertised_properties status cannot carry advertised "
                    "property entries"
                )
            if not substantive(
                source_definition_review.get("no_advertised_properties_basis")
            ):
                return (
                    "source_definition_semantics_review lacks substantive "
                    "no_advertised_properties_basis"
                )
        elif not properties:
            return (
                "properties_reviewed source-definition status requires at least "
                "one advertised property"
            )

        seen_property_ids: set[str] = set()
        conclusion_ids = {
            key for key, kind in lean_obligations.items() if kind == "conclusion"
        }
        source_conclusion_ids = {
            key for key, kind in source_obligations.items() if kind == "conclusion"
        }
        for property_item in properties:
            if not isinstance(property_item, dict):
                return "source-definition advertised property is not an object"
            property_id = required_string(property_item.get("id"))
            if not property_id or property_id in seen_property_ids:
                return "source-definition advertised property has a missing or duplicate id"
            seen_property_ids.add(property_id)
            for field, label in (
                ("source_property", "source property"),
                ("lean_realization", "Lean realization"),
                ("evidence_basis", "evidence basis"),
            ):
                if not substantive(property_item.get(field)):
                    return (
                        "source-definition advertised property lacks substantive "
                        f"{label}"
                    )
            property_source_ids, error = obligation_id_list(
                property_item.get("source_obligation_ids"),
                "source-definition advertised property source_obligation_ids",
                source_obligations,
                nonempty=True,
            )
            if error:
                return error
            property_lean_ids, error = obligation_id_list(
                property_item.get("lean_obligation_ids"),
                "source-definition advertised property lean_obligation_ids",
                lean_obligations,
                nonempty=True,
            )
            if error:
                return error
            if not (property_source_ids & source_conclusion_ids):
                return (
                    "source-definition advertised property is not bound to a "
                    "source conclusion obligation"
                )
            if not (property_lean_ids & conclusion_ids):
                return (
                    "source-definition advertised property is not bound to a "
                    "Lean conclusion obligation"
                )
            relation = required_string(property_item.get("relation")).lower()
            if relation not in SOURCE_DEFINITION_SEMANTIC_RELATIONS:
                return "source-definition advertised property has an invalid relation"
            if verdict == "matches" and relation != "equivalent":
                return (
                    "matches judgment records a non-equivalent source-definition "
                    "advertised property"
                )
            evidence_kind = required_string(
                property_item.get("lean_evidence_kind")
            ).lower()
            if evidence_kind not in SOURCE_DEFINITION_PROPERTY_EVIDENCE_KINDS:
                return (
                    "source-definition advertised property has an invalid "
                    "lean_evidence_kind"
                )
            if verdict == "matches" and evidence_kind == "missing":
                return (
                    "matches judgment has an advertised source-definition property "
                    "without Lean evidence"
                )
            if evidence_kind in {
                "paper_interface_equivalence",
                "paper_interface_conclusion",
            }:
                evidence_conclusion_id = required_string(
                    property_item.get("lean_evidence_conclusion_id")
                )
                if evidence_conclusion_id not in conclusion_ids:
                    return (
                        "source-definition advertised property paper-interface evidence "
                        "is not a Lean conclusion obligation"
                    )
                if evidence_conclusion_id not in property_lean_ids:
                    return (
                        "source-definition advertised property paper-interface evidence "
                        "is not bound to its Lean obligations"
                    )
                if (
                    evidence_kind == "paper_interface_equivalence"
                    and not lean_conclusion_exposes_equivalence(evidence_conclusion_id)
                ):
                    return (
                        "source-definition advertised property equivalence evidence "
                        "does not explicitly contain equality or iff"
                    )
            elif evidence_kind == "expanded_definition_body":
                if not any(
                    (lean_manifest_atoms.get(obligation_id) or {})
                    .get("canonical", {})
                    .get("tag")
                    == "definition"
                    for obligation_id in property_lean_ids & conclusion_ids
                ):
                    return (
                        "source-definition advertised property claims expanded "
                        "definition-body evidence without a definition-valued Lean conclusion"
                    )

    numeric_review = raw.get("numeric_semantics_review")
    if not isinstance(numeric_review, dict):
        return "semantic scope review has no numeric_semantics_review object"
    formulas_present = numeric_review.get("formulas_present")
    if not isinstance(formulas_present, bool):
        return "numeric_semantics_review has no Boolean formulas_present"
    numeric_items = numeric_review.get("items")
    if not isinstance(numeric_items, list):
        return "numeric_semantics_review has no items list"
    if formulas_present != bool(numeric_items):
        return "numeric_semantics_review presence flag does not match its items"
    if not formulas_present and not substantive(numeric_review.get("absence_basis")):
        return "numeric_semantics_review lacks a substantive absence_basis"
    coverage_error = operator_review_coverage_error(
        numeric_review,
        numeric_items,
        source_item_field="source_obligation_ids",
        lean_item_field="lean_obligation_ids",
        non_source_field="non_numeric_source_obligation_ids",
        non_lean_field="non_numeric_lean_obligation_ids",
        label="numeric semantics",
        lean_absence_conflict=lean_atom_has_numeric_semantics,
    )
    if coverage_error:
        return coverage_error
    conclusion_ids = {
        key for key, kind in lean_obligations.items() if kind == "conclusion"
    }
    seen_numeric_item_ids: set[str] = set()
    for item in numeric_items:
        if not isinstance(item, dict):
            return "numeric semantics review item is not an object"
        item_id = required_string(item.get("id"))
        if not item_id or item_id in seen_numeric_item_ids:
            return "numeric semantics review item has a missing or duplicate id"
        seen_numeric_item_ids.add(item_id)
        if not required_string(item.get("source_expression")):
            return "numeric semantics review item has no source_expression"
        if not required_string(item.get("lean_expression")):
            return "numeric semantics review item has no lean_expression"
        for field, label in (
            ("source_domain", "source domain"),
            ("lean_domain", "Lean domain"),
            ("source_operations", "source operations"),
            ("lean_operations", "Lean operations"),
            ("source_coercions", "source coercion review"),
            ("lean_coercions", "Lean coercion review"),
            ("source_division", "source division convention"),
            ("lean_division", "Lean division convention"),
            ("source_rounding", "source rounding behavior"),
            ("lean_rounding", "Lean rounding behavior"),
            ("source_normalization", "source normalization"),
            ("lean_normalization", "Lean normalization"),
            ("source_strictness", "source strictness"),
            ("lean_strictness", "Lean strictness"),
            ("source_zero_denominator", "source zero-denominator behavior"),
            ("lean_zero_denominator", "Lean zero-denominator behavior"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"numeric semantics review item lacks a substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in NUMERIC_SEMANTIC_RELATIONS:
            return "numeric semantics review item has an invalid relation"
        if relation in {"proved_equivalent", "witness_specific_equivalent"}:
            conclusion_id = required_string(
                item.get("lean_equivalence_conclusion_id")
            )
            if conclusion_id not in conclusion_ids:
                return (
                    "numeric semantics equivalence is not exposed by a Lean "
                    "conclusion obligation"
                )
            if conclusion_id not in set(item.get("lean_obligation_ids") or []):
                return (
                    "numeric semantics equivalence conclusion is not bound to the "
                    "reviewed Lean obligations"
                )
            if not lean_conclusion_exposes_equivalence(conclusion_id):
                return (
                    "numeric semantics equivalence conclusion does not explicitly "
                    "contain equality or iff"
                )
            if not substantive(item.get("lean_equivalence_statement")):
                return "numeric semantics equivalence lacks its explicit Lean statement"
        if verdict == "matches" and relation not in {
            "definitionally_equal",
            "proved_equivalent",
        }:
            return (
                "matches judgment records non-equivalent or witness-only numeric semantics"
            )

    discrete_review = raw.get("discrete_semantics_review")
    if not isinstance(discrete_review, dict):
        return "semantic scope review has no discrete_semantics_review object"
    operations_present = discrete_review.get("operations_present")
    if not isinstance(operations_present, bool):
        return "discrete_semantics_review has no Boolean operations_present"
    discrete_items = discrete_review.get("items")
    if not isinstance(discrete_items, list):
        return "discrete_semantics_review has no items list"
    if operations_present != bool(discrete_items):
        return "discrete_semantics_review presence flag does not match its items"
    if not operations_present and not substantive(discrete_review.get("absence_basis")):
        return "discrete_semantics_review lacks a substantive absence_basis"
    coverage_error = operator_review_coverage_error(
        discrete_review,
        discrete_items,
        source_item_field="source_obligation_ids",
        lean_item_field="lean_obligation_ids",
        non_source_field="non_discrete_source_obligation_ids",
        non_lean_field="non_discrete_lean_obligation_ids",
        label="discrete semantics",
        lean_absence_conflict=lean_atom_has_discrete_semantics,
    )
    if coverage_error:
        return coverage_error
    seen_discrete_item_ids: set[str] = set()
    for item in discrete_items:
        if not isinstance(item, dict):
            return "discrete semantics review item is not an object"
        item_id = required_string(item.get("id"))
        if not item_id or item_id in seen_discrete_item_ids:
            return "discrete semantics review item has a missing or duplicate id"
        seen_discrete_item_ids.add(item_id)
        if not required_string(item.get("source_expression")):
            return "discrete semantics review item has no source_expression"
        if not required_string(item.get("lean_expression")):
            return "discrete semantics review item has no lean_expression"
        for field, label in (
            ("source_domain", "source domain"),
            ("lean_domain", "Lean domain"),
            ("source_operation", "source operation"),
            ("lean_operation", "Lean operation"),
            ("source_order_sensitivity", "source order sensitivity"),
            ("lean_order_sensitivity", "Lean order sensitivity"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"discrete semantics review item lacks a substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in DISCRETE_SEMANTIC_RELATIONS:
            return "discrete semantics review item has an invalid relation"
        if relation in {"proved_equivalent", "witness_specific_equivalent"}:
            conclusion_id = required_string(
                item.get("lean_equivalence_conclusion_id")
            )
            if conclusion_id not in conclusion_ids:
                return (
                    "discrete semantics equivalence is not exposed by a Lean "
                    "conclusion obligation"
                )
            if conclusion_id not in set(item.get("lean_obligation_ids") or []):
                return (
                    "discrete semantics equivalence conclusion is not bound to the "
                    "reviewed Lean obligations"
                )
            if not lean_conclusion_exposes_equivalence(conclusion_id):
                return (
                    "discrete semantics equivalence conclusion does not explicitly "
                    "contain equality or iff"
                )
            if not substantive(item.get("lean_equivalence_statement")):
                return "discrete semantics equivalence lacks its explicit Lean statement"
        if verdict == "matches" and relation not in {
            "definitionally_equal",
            "proved_equivalent",
        }:
            return (
                "matches judgment records non-equivalent or witness-only discrete semantics"
            )

    algorithm_review = raw.get("algorithm_review")
    if not isinstance(algorithm_review, dict):
        return "semantic scope review has no algorithm_review object"
    source_level = required_string(algorithm_review.get("source_claim_level")).lower()
    lean_level = required_string(algorithm_review.get("lean_claim_level")).lower()
    runner_provenance = required_string(
        algorithm_review.get("runner_provenance")
    ).lower()
    result_provenance = required_string(
        algorithm_review.get("result_provenance")
    ).lower()
    if source_level not in SOURCE_ALGORITHM_CLAIM_LEVELS:
        return "algorithm review has an invalid source_claim_level"
    if lean_level not in LEAN_ALGORITHM_CLAIM_LEVELS:
        return "algorithm review has an invalid lean_claim_level"
    if runner_provenance not in RUNNER_PROVENANCE_KINDS:
        return "algorithm review has an invalid runner_provenance"
    if result_provenance not in RESULT_PROVENANCE_KINDS:
        return "algorithm review has an invalid result_provenance"
    if not substantive(algorithm_review.get("source_claim_basis")):
        return "algorithm review lacks a substantive source_claim_basis"
    if not substantive(algorithm_review.get("lean_claim_basis")):
        return "algorithm review lacks a substantive lean_claim_basis"

    fidelity_error = fidelity_risk_review_error(
        raw.get("fidelity_risk_review"),
        source_obligations,
        lean_obligations,
        verdict,
        source_level,
    )
    if fidelity_error:
        return fidelity_error

    worlds = raw.get("semantic_worlds")
    if not isinstance(worlds, list) or not worlds:
        return "semantic scope review has no semantic_worlds"
    world_roles: dict[str, str] = {}
    for world in worlds:
        if not isinstance(world, dict):
            return "semantic world is not an object"
        world_id = required_string(world.get("id"))
        role = required_string(world.get("role")).lower()
        if not world_id or world_id in world_roles:
            return "semantic world has a missing or duplicate id"
        if role not in SEMANTIC_WORLD_ROLES:
            return f"semantic world `{world_id}` has an invalid role"
        if not substantive(world.get("semantics")):
            return f"semantic world `{world_id}` lacks substantive semantics"
        world_roles[world_id] = role
    if "shared" not in set(world_roles.values()) and not {
        "source",
        "lean",
    }.issubset(set(world_roles.values())):
        return "semantic worlds do not identify shared semantics or both source and Lean worlds"

    bridges = raw.get("world_bridges")
    if not isinstance(bridges, list):
        return "semantic scope review has no world_bridges list"
    normalized_bridges: list[dict[str, str]] = []
    for bridge in bridges:
        if not isinstance(bridge, dict):
            return "semantic world bridge is not an object"
        from_world = required_string(bridge.get("from_world"))
        to_world = required_string(bridge.get("to_world"))
        relation = required_string(bridge.get("relation")).lower()
        statement = required_string(bridge.get("statement"))
        conclusion_id = required_string(bridge.get("lean_conclusion_id"))
        if (
            from_world not in world_roles
            or to_world not in world_roles
            or from_world == to_world
        ):
            return "semantic world bridge has invalid endpoints"
        if relation not in SEMANTIC_WORLD_BRIDGE_RELATIONS:
            return "semantic world bridge has an invalid relation"
        if not substantive(statement):
            return "semantic world bridge lacks a substantive mathematical statement"
        if conclusion_id not in conclusion_ids:
            return "semantic world bridge is not exposed by a Lean conclusion obligation"
        normalized_bridges.append(
            {
                "from": from_world,
                "to": to_world,
                "relation": relation,
                "statement": statement,
            }
        )

    if verdict != "matches":
        return ""

    source_worlds = {
        key for key, role in world_roles.items() if role in {"source", "shared"}
    }
    lean_worlds = {
        key for key, role in world_roles.items() if role in {"lean", "shared"}
    }

    def has_bridge(relations: set[str], expected_statement: str = "") -> bool:
        return any(
            bridge["from"] in source_worlds
            and bridge["to"] in lean_worlds
            and bridge["from"] != bridge["to"]
            and bridge["relation"] in relations
            and (not expected_statement or bridge["statement"] == expected_statement)
            for bridge in normalized_bridges
        )

    separate_worlds = "shared" not in set(world_roles.values())

    def separate_worlds_bridge_error() -> str:
        if not separate_worlds:
            return ""
        if not has_bridge(
            {"definitionally_equal", "equivalent", "refines", "simulates"}
        ):
            return (
                "separate source and Lean semantic worlds have no exposed equality, "
                "equivalence, refinement, or simulation bridge"
            )
        if not has_bridge(
            {"definitionally_equal", "equivalent", "preserves_result"}
        ):
            return (
                "separate source and Lean semantic worlds have no exposed "
                "result-preservation bridge"
            )
        return ""

    compatible_lean_levels = {
        "not_algorithmic": {"not_algorithmic"},
        "existence": {"existence", "noncomputable_existence"},
        "executable": {"executable"},
        "polynomial_time": {"polynomial_time"},
    }
    if lean_level not in compatible_lean_levels[source_level]:
        return (
            "matches judgment conflates noncomputable existence, executable output, "
            "and polynomial-time claims"
        )

    if source_level == "not_algorithmic":
        if runner_provenance != "not_applicable" or result_provenance != "not_applicable":
            return "non-algorithmic row records algorithm runner/result provenance"
        world_error = separate_worlds_bridge_error()
        if world_error:
            return world_error
        return ""

    if source_level == "existence":
        if runner_provenance not in {
            "not_applicable",
            "same_formalized_runner",
            "proved_refinement",
        }:
            return "existence-only match records unsupported runner refinement"
        if result_provenance not in {
            "not_applicable",
            "runner_derived",
            "preservation_bridge",
        }:
            return "existence-only match records unsupported result provenance"
        world_error = separate_worlds_bridge_error()
        if world_error:
            return world_error
        if runner_provenance == "same_formalized_runner" and separate_worlds:
            return "same runner provenance has no shared semantic world"
        if runner_provenance == "proved_refinement":
            if result_provenance != "preservation_bridge":
                return (
                    "a cross-world existence refinement needs an exposed "
                    "result-preservation bridge"
                )
        else:
            return ""

    if runner_provenance in {"independent_characterization", "missing", "not_applicable"}:
        return (
            "algorithmic match lacks source-runner provenance; an independent "
            "characterization is not a refinement"
        )
    if result_provenance in {"independent_characterization", "missing", "not_applicable"}:
        return (
            "algorithmic match lacks runner-derived result provenance or an exposed "
            "preservation bridge"
        )

    if result_provenance == "runner_derived":
        if not substantive(algorithm_review.get("runner_result_statement")):
            return "runner-derived result provenance lacks a substantive result statement"
        runner_result_id = required_string(
            algorithm_review.get("runner_result_lean_conclusion_id")
        )
        if runner_result_id not in conclusion_ids:
            return "runner-derived result is not exposed by a Lean conclusion obligation"

    if runner_provenance == "proved_refinement":
        if result_provenance != "preservation_bridge":
            return (
                "a refined source runner needs an exposed result-preservation bridge; "
                "success of the Lean runner alone is insufficient"
            )
        statement = required_string(algorithm_review.get("refinement_statement"))
        if not substantive(statement):
            return "proved runner refinement lacks a substantive refinement statement"
        if not has_bridge(
            {"definitionally_equal", "refines", "simulates", "equivalent"},
            statement,
        ):
            return "proved runner refinement has no exposed source-to-Lean world bridge"
    elif runner_provenance == "same_formalized_runner":
        if "shared" not in set(world_roles.values()):
            return "same runner provenance has no shared semantic world"

    if result_provenance == "preservation_bridge":
        statement = required_string(
            algorithm_review.get("result_preservation_statement")
        )
        if not substantive(statement):
            return "result preservation provenance lacks a substantive bridge statement"
        if not has_bridge(
            {"definitionally_equal", "preserves_result", "equivalent"}, statement
        ):
            return "result preservation is not exposed as a source-to-Lean world bridge"

    if source_level == "polynomial_time":
        if not substantive(algorithm_review.get("complexity_statement")):
            return "polynomial-time match has no substantive complexity statement"
        if not substantive(algorithm_review.get("arithmetic_model")):
            return "polynomial-time match has no explicit arithmetic/representation model"
        complexity_id = required_string(
            algorithm_review.get("complexity_lean_conclusion_id")
        )
        if complexity_id not in conclusion_ids:
            return "polynomial-time claim is not exposed by a Lean conclusion obligation"
    return ""


def semantic_obligation_ledger_error(
    raw: Any,
    signature_manifest: dict[str, Any] | None = None,
    *,
    require_source_definition_semantics_review: bool = False,
) -> str:
    """Validate the atom-by-atom source/Lean comparison behind a judgment.

    Declaration names and prose similarity are not evidence that a theorem's
    assumptions and conclusions agree. A v10 statement judgment therefore
    carries explicit semantic obligations and relations between them. It also
    requires an exact partition of the binder-name-independent atoms extracted
    from the elaborated Lean type. This is a structural fail-closed check; an
    independent reviewer still has to judge whether the recorded formulas and
    implications are mathematically right.
    """

    if not isinstance(raw, dict):
        return "judgment is not an object"
    source = raw.get("source_obligations")
    lean = raw.get("lean_obligations")
    alignment = raw.get("obligation_alignment")
    if not isinstance(source, list) or not isinstance(lean, list):
        return "missing source_obligations/lean_obligations lists"
    if not isinstance(alignment, list):
        return "missing obligation_alignment list"

    if not isinstance(signature_manifest, dict):
        return "Lean declaration manifest is unavailable"
    manifest_digest = str(signature_manifest.get("sha256") or "").strip()
    recorded_manifest_digest = str(raw.get("lean_signature_sha256") or "").strip()
    if not manifest_digest:
        return "Lean declaration manifest has no canonical digest"
    if signature_manifest_digest(signature_manifest) != manifest_digest:
        return "Lean declaration manifest canonical digest is invalid"
    if not recorded_manifest_digest:
        return "judgment has no `lean_signature_sha256`"
    if recorded_manifest_digest != manifest_digest:
        return "judgment Lean declaration manifest digest is stale"
    manifest_atoms = signature_manifest.get("atoms")
    if not isinstance(manifest_atoms, list) or not manifest_atoms:
        return "Lean declaration manifest has no atoms"
    manifest_roles: dict[str, str] = {}
    manifest_atom_digests: dict[str, str] = {}
    manifest_atoms_by_ref: dict[str, dict[str, Any]] = {}
    for atom in manifest_atoms:
        if not isinstance(atom, dict):
            return "Lean declaration manifest atom is not an object"
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip().lower()
        if not ref or ref in manifest_roles:
            return "Lean declaration manifest has a missing/duplicate atom ref"
        if role not in {"parameter", "assumption", "conclusion"}:
            return f"Lean declaration manifest atom `{ref}` has invalid role"
        manifest_roles[ref] = role
        manifest_atoms_by_ref[ref] = atom
        atom_digest = signature_manifest_atom_digest(atom)
        if not atom_digest:
            return f"Lean declaration manifest atom `{ref}` has no canonical digest"
        manifest_atom_digests[ref] = atom_digest

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def obligation_index(values: list[Any], side: str) -> tuple[dict[str, str], str]:
        out: dict[str, str] = {}
        for value in values:
            if not isinstance(value, dict):
                return {}, f"{side} obligation is not an object"
            key = required_string(value.get("id"))
            kind = required_string(value.get("kind")).lower()
            if not key or key in out:
                return {}, f"{side} obligation has a missing/duplicate id"
            if kind not in {"parameter", "assumption", "conclusion"}:
                return {}, f"{side} obligation `{key}` has invalid kind"
            if side == "source":
                statement = required_string(value.get("statement"))
                if not statement:
                    return {}, f"source obligation `{key}` has no semantic statement"
                source_location = required_string(value.get("source_location"))
                if not source_location:
                    return {}, f"source obligation `{key}` has no source location"
                if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
                    return {}, f"source obligation `{key}` has no exact source locator"
            elif "statement" in value:
                return {}, (
                    f"Lean obligation `{key}` supplies unaudited prose in `statement`; "
                    "v7 binds it only through signature_ref/signature_atom_sha256"
                )
            out[key] = kind
        if not any(kind == "conclusion" for kind in out.values()):
            return {}, f"{side} ledger has no conclusion"
        return out, ""

    source_index, error = obligation_index(source, "source")
    if error:
        return error
    lean_index, error = obligation_index(lean, "Lean")
    if error:
        return error

    covered_manifest_refs: dict[str, str] = {}
    lean_manifest_atoms: dict[str, dict[str, Any]] = {}
    for value in lean:
        key = required_string(value.get("id"))
        ref = required_string(value.get("signature_ref"))
        if not ref:
            return f"Lean obligation `{key}` has no `signature_ref`"
        if ref not in manifest_roles:
            return f"Lean obligation `{key}` references unknown signature atom `{ref}`"
        if ref in covered_manifest_refs:
            return f"Lean signature atom `{ref}` is referenced by multiple obligations"
        if lean_index[key] != manifest_roles[ref]:
            return f"Lean obligation `{key}` kind does not match signature atom `{ref}` role"
        recorded_atom_digest = required_string(value.get("signature_atom_sha256"))
        if not recorded_atom_digest:
            return f"Lean obligation `{key}` has no `signature_atom_sha256`"
        if recorded_atom_digest != manifest_atom_digests[ref]:
            return f"Lean obligation `{key}` signature atom digest is stale"
        covered_manifest_refs[ref] = key
        lean_manifest_atoms[key] = manifest_atoms_by_ref[ref]
    missing_manifest_refs = set(manifest_roles) - set(covered_manifest_refs)
    if missing_manifest_refs:
        return "Lean obligations omit signature atom(s): " + ", ".join(
            sorted(missing_manifest_refs)
        )

    aligned_source: set[str] = set()
    aligned_lean: set[str] = set()
    has_directional_alignment = False
    for value in alignment:
        if not isinstance(value, dict):
            return "obligation alignment entry is not an object"
        source_id = required_string(value.get("source_id"))
        lean_id = required_string(value.get("lean_id"))
        relation = required_string(value.get("relation")).lower()
        basis = required_string(value.get("semantic_basis"))
        bridge = required_string(value.get("bridge_statement"))
        if source_id not in source_index or lean_id not in lean_index:
            return "obligation alignment references an unknown id"
        if source_index[source_id] != lean_index[lean_id]:
            return "obligation alignment mixes assumption and conclusion kinds"
        if relation not in {"equivalent", "source_implies_lean", "lean_implies_source"}:
            return "obligation alignment has an invalid semantic relation"
        if not basis:
            return "obligation alignment lacks a semantic basis"
        if NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis):
            return "obligation alignment semantic_basis relies on names instead of semantics"
        if not bridge:
            return "obligation alignment lacks an explicit semantic bridge statement"
        if NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(bridge):
            return "obligation alignment bridge_statement relies on names instead of semantics"
        aligned_source.add(source_id)
        aligned_lean.add(lean_id)
        has_directional_alignment = has_directional_alignment or relation != "equivalent"

    source_conclusions = {
        key for key, kind in source_index.items() if kind == "conclusion"
    }
    source_inputs = {
        key for key, kind in source_index.items() if kind in {"parameter", "assumption"}
    }
    lean_inputs = {
        key for key, kind in lean_index.items() if kind in {"parameter", "assumption"}
    }
    lean_conclusions = {
        key for key, kind in lean_index.items() if kind == "conclusion"
    }
    missing_conclusions = source_conclusions - aligned_source
    missing_source_inputs = source_inputs - aligned_source
    unjustified_inputs = lean_inputs - aligned_lean
    missing_lean_conclusions = lean_conclusions - aligned_lean

    def recorded_gap_ids(field: str) -> tuple[set[str], str]:
        values = raw.get(field)
        if not isinstance(values, list):
            return set(), f"missing explicit `{field}` list"
        if any(not isinstance(value, str) or not value.strip() for value in values):
            return set(), f"`{field}` must contain nonempty obligation ids"
        normalized = [value.strip() for value in values]
        if len(normalized) != len(set(normalized)):
            return set(), f"`{field}` contains duplicate obligation ids"
        return set(normalized), ""

    unmatched, error = recorded_gap_ids("unmatched_source_conclusions")
    if error:
        return error
    unjustified, error = recorded_gap_ids("unjustified_lean_inputs")
    if error:
        return error
    if unmatched != missing_conclusions:
        return "`unmatched_source_conclusions` does not equal the unmatched source conclusion ids"
    unmatched_inputs, error = recorded_gap_ids("unmatched_source_inputs")
    if error:
        return error
    unmatched_lean_conclusions, error = recorded_gap_ids("unmatched_lean_conclusions")
    if error:
        return error
    if unmatched_inputs != missing_source_inputs:
        return "`unmatched_source_inputs` does not equal the unmatched source input ids"
    if unjustified != unjustified_inputs:
        return "`unjustified_lean_inputs` does not equal the unjustified Lean input ids"
    if unmatched_lean_conclusions != missing_lean_conclusions:
        return "`unmatched_lean_conclusions` does not equal the unmatched Lean conclusion ids"

    verdict = _normalize_llm_match_judgment(
        raw.get("judgment")
        or raw.get("verdict")
        or raw.get("status")
        or raw.get("matches")
    )
    resolution = _normalize_llm_match_resolution(
        raw.get("resolution")
        or raw.get("accepted_resolution")
        or raw.get("review_resolution")
    )
    # A visible-premise boundary may differ from the source only by its
    # explicitly recorded extra Lean inputs.  It must not use the mismatch
    # verdict to bypass checks for weakened quantification, computational
    # capability, runner provenance, or cross-world result preservation.
    scope_verdict = (
        "matches"
        if verdict == "matches"
        or (
            verdict == "mismatch"
            and resolution == CONDITIONAL_BOUNDARY_RESOLUTION
        )
        else verdict
    )
    scope_error = semantic_scope_review_error(
        raw.get("semantic_scope_review"),
        source_index,
        lean_index,
        lean_manifest_atoms,
        scope_verdict,
        require_source_definition_semantics_review=(
            require_source_definition_semantics_review
        ),
    )
    if scope_error:
        return scope_error
    semantic_scope = raw.get("semantic_scope_review")
    algorithm_review = (
        semantic_scope.get("algorithm_review")
        if isinstance(semantic_scope, dict)
        and isinstance(semantic_scope.get("algorithm_review"), dict)
        else {}
    )
    source_claim_level = str(
        algorithm_review.get("source_claim_level") or ""
    ).strip().lower()
    lean_claim_level = str(
        algorithm_review.get("lean_claim_level") or ""
    ).strip().lower()
    if (
        verdict == "matches"
        and source_claim_level == "polynomial_time"
        and lean_claim_level == "polynomial_time"
    ):
        complexity_error = operational_complexity_review_error(
            raw.get("operational_complexity_review"),
            str(
                algorithm_review.get("complexity_lean_conclusion_id") or ""
            ).strip(),
        )
        if complexity_error:
            return complexity_error
    all_gaps = unmatched | unmatched_inputs | unjustified | unmatched_lean_conclusions
    if verdict == "matches" and (all_gaps or has_directional_alignment):
        return "matches judgment records a semantic obligation gap"
    if verdict in {"mismatch", "uncertain"} and not (all_gaps or has_directional_alignment):
        return f"{verdict} judgment records no semantic obligation gap"
    return ""


# Source definitions need a distinct semantic review from theorem proof
# evidence.  A definition can compile while quietly extending a partial source
# operation, replacing a probability law by an unnormalised formula, or naming
# a selector without the advertised attainment property.  This classification
# comes from the source inventory, never from a Lean declaration or map key.
SOURCE_DEFINITION_SEMANTIC_KINDS = {"definition", "predicate_vocabulary"}
# This deliberately extends only the direct-route semantic-review gate below.
# Formula/equation kinds remain outside definition partition and coverage rules:
# they need a domain/totalization review, but are not thereby source definitions.
SOURCE_DIRECT_EXPRESSION_SEMANTIC_KINDS = (
    SOURCE_DEFINITION_SEMANTIC_KINDS
    | {"formula", "equation", "algorithmic_formula"}
)
SOURCE_DEFINITION_SEMANTIC_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
    "uncertain",
}
SOURCE_DEFINITION_PROPERTY_STATUSES = {
    "properties_reviewed",
    "no_advertised_properties",
}
SOURCE_DEFINITION_PROPERTY_EVIDENCE_KINDS = {
    "expanded_definition_body",
    "paper_interface_equivalence",
    "paper_interface_conclusion",
    "missing",
}
