#!/usr/bin/env python3
"""Render the strict source-record human and LLM semantic-review prompt.

This module is pure policy presentation. It consumes only the already-frozen
source-record payload selected by the semantic producer; it cannot read source
files, select claims, invoke Lean, admit cached evidence, or issue receipts.
"""

from __future__ import annotations

import json
from typing import Any, Mapping


def judge_prompt(
    paper_id: str,
    items: list[dict[str, Any]],
    source_proof_fidelity: dict[str, Any] | None = None,
    semantic_context_requirements: list[dict[str, Any]] | None = None,
) -> str:
    semantic_context_instruction = ""
    if semantic_context_requirements:
        semantic_context_instruction = (
            "\n\nThe source-map semantic-context requirements below are byte-pinned "
            "source-text review context only. They are not theorem statements, proof "
            "routes, source-coverage credit, or evidence that any Lean declaration or "
            "function has the intended semantics. For each relevant expanded Lean "
            "surface, compare the literal source quote, declared semantic kind, and "
            "explanation with the actual quantifiers, domains, laws, conventions, and "
            "totalizations. A context requirement can expose a missing assumption or a "
            "mismatch; it cannot discharge that obligation. Do not infer anything from "
            "the source-map key or from a Lean declaration/function name.\n\n"
            + json.dumps(semantic_context_requirements, indent=2, sort_keys=True)
        )
    proof_fidelity_instruction = ""
    if source_proof_fidelity is not None:
        proof_fidelity_instruction = (
            "\n\nThe optional source-proof fidelity ledger below records source-proof text by "
            "source locator and mathematical claim, not by Lean declaration name. A recorded "
            "proof defect is never by itself a validated paper/source assumption. Its "
            "model_conventions and checked_proof_steps are also source-located semantic "
            "context: compare their literal formal meaning and stated scope with the expanded "
            "Lean surface. A convention is not a literal source theorem unless a source-side "
            "semantic bridge is supplied, and a checked proof step proves only its stated "
            "scope rather than a broader null-fiber, arbitrary-partition, or arbitrary-space "
            "claim. Do not classify a boundary input or field as validated_source_assumption "
            "merely because it restates a repaired proof line, convention, or checked-step "
            "summary: require a Lean derivation, an explicit approved partial boundary, or an "
            "explicit corrected source-statement path.\n\n"
            + json.dumps(source_proof_fidelity, indent=2, sort_keys=True)
        )
    item_block = json.dumps(items, indent=2, sort_keys=True)
    context_blocks = [
        instruction
        for instruction in (semantic_context_instruction, proof_fidelity_instruction)
        if instruction
    ]
    if context_blocks:
        item_block = "\n\n".join(context_blocks) + "\n\nSource-record items:\n" + item_block
    return (
        "You are auditing Lean formalization provenance, not just theorem text.\n"
        f"Paper: {paper_id}\n\n"
        "For each item below, compare the original paper source statement/proof text "
        "with the Lean-checked statement and the dependency path. Scrutinize every "
        "visible theorem input semantically: names and source-looking type suffixes "
        "are only routing hints, not evidence. Do not approve by theorem label, "
        "phrase overlap, or source-looking Lean name. Each input must correspond "
        "to a specific paper primitive/source assumption, be derived by a "
        "Lean-checked constructor from paper primitives, be an approved external "
        "boundary, or remain an unresolved conditional/partial boundary. In "
        "particular, any Certificate, Replay, Process, or Bridge input needs a "
        "specific source statement or an instantiation path from the paper's "
        "primitive model; do not accept it merely because the final theorem name "
        "resembles the paper claim.\n\n"
        "When recording a judgment, copy the generated `source_record_item_digest_schema`, "
        "`source_record_item_semantic_id`, and `source_record_item_sha256` exactly when "
        "the item marks `source_record_item_reuse_eligibility.eligible` true. Never invent "
        "or reconstruct these values from a row, binder, source-map key, or declaration "
        "name. An ineligible item has aggregate-audit freshness only and must not receive a "
        "synthetic item digest.\n\n"
        "The judgment sidecar must also record a top-level "
        "`formalization_review_protocol_sha256` computed by the current "
        "`scripts.formalization_protocol.formalization_review_protocol_digest`; this is "
        "review authority, not a generated Lean-obligation identity. Never copy a stale "
        "digest from a cached raw audit.\n\n"
        "For an optimization, finite-search, or algorithmic result, also audit the "
        "semantics end to end. Identify the literal legal action space (including "
        "whether rankings may be partial, blank, repeated, or only full); determine "
        "whether a profile is an ordered tuple, a multiset, or a bounded stock and "
        "whether multiplicities are unrestricted; inspect the actual source executor "
        "used to evaluate the objective/target; and check both successful and "
        "no-result branches over the stated capacity. A generic finite selector is "
        "not an implementation, a source-faithful optimizer, or a runtime proof until "
        "those semantic bridges are derived. Distinguish a noncomputable existence "
        "selector from an executable enumeration, and separately verify any claimed "
        "complexity, arithmetic representation, and refinement relation to external "
        "code. Apply this checklist from expanded definitions and proof dependencies, "
        "not declaration names or function-name patterns.\n\n"
        "Explicitly test the recurring fidelity hazards. Compare the source output's "
        "arity and projection policy with the actual runner output, including any "
        "terminal component. For universal adversarial transformations, establish an "
        "inhabited legal action space with the stated carrier/capacity and check whether "
        "prefixing or concatenation creates duplicate-invalid ballots. Never combine "
        "candidatewise extrema unless one coherent admissible witness realizes the "
        "combined values, and require an actual-runner or checked refinement bridge. "
        "Separate syntax-family cardinality from the number of nonempty realized fibers; "
        "an exact equality needs surjectivity. Finally, compare source and Lean input "
        "domains, state transitions, termination conditions, numeric representations, "
        "and cost scopes. Keep a local transition, restricted input class, partial "
        "execution, or local cost count separate from an advertised end-to-end or "
        "polynomial claim until a checked global bridge is present.\n\n"
        "For every `semantic_model_comparison` item, do not reuse the ordinary field "
        "classification as a substitute for the requested source-model comparison. Set its "
        "top-level `classification` to `semantic_model_review` and provide a "
        "`semantic_model_dimensions` object keyed by every listed dimension. Each dimension "
        "must give `verdict` (`matches_source_model`, `not_applicable`, "
        "`mismatch_or_open`, or `documented_partial_boundary`), an exact `source_locator`, "
        "a concrete `semantic_comparison`, and `lean_evidence` tied to the expanded surface. "
        "A detected dimension marked `requires_checked_bridge_when_detected`, including "
        "endpoint support, joint law/state evolution, extended rates, and opaque carrier "
        "surfaces, also needs `lean_bridge`: a checked theorem, constructor, equality, "
        "simulation, or refinement route. `not_applicable` is invalid for a detected shape. "
        "When the expanded surface lists `terminal_term_dependency_surface`, audit the "
        "transparent definition chain by its displayed Lean constructors, source files, and "
        "digests, not by its local names. Any listed opaque, ambiguous, tactic-body, or "
        "bounded path remains bridge-required; it cannot be waved away because its terminal "
        "type is `Real` or `Prop`. "
        "When a `carrier_and_domain` dimension has "
        "`requires_cardinality_boundary_analysis_when_detected`, include a "
        "`cardinality_boundary_analysis` object with a verdict "
        "(`threshold_checked`, `no_strictness_or_interior_requirement`, "
        "`mismatch_or_open`, or `documented_partial_boundary`), "
        "`source_cardinality_domain`, `lean_cardinality_domain`, "
        "`boundary_cases_checked`, `strictness_witness_or_reason`, and "
        "`lean_boundary_evidence`. When a `joint_law_and_state_evolution` dimension "
        "has `requires_transformed_law_analysis_when_detected`, include a "
        "`transformed_law_analysis` object with a verdict "
        "(`no_transform_or_canonicalization`, `transformed_law_checked`, "
        "`canonicalization_checked`, `mismatch_or_open`, or "
        "`documented_partial_boundary`), `source_operation`, `lean_operation`, "
        "`parameter_domain_and_endpoints`, "
        "`law_normalization_or_pushforward_evidence`, "
        "`outcome_equivariance_or_no_relabeling_evidence`, and "
        "`lean_semantic_bridge`. An explicit no-transform finding still needs those "
        "semantic fields; do not substitute declaration names. "
        "When a `joint_law_and_state_evolution` dimension has "
        "`requires_distribution_parameterization_analysis_when_detected`, include a "
        "`distribution_parameterization_analysis` object with a verdict "
        "(`no_parameterized_law_or_scale`, `definitionally_same_parameterization`, "
        "`proved_exact_law_equivalence`, "
        "`proved_outcome_equivalence_after_translation`, `mismatch_or_open`, or "
        "`documented_partial_boundary`), `source_parameterization`, "
        "`source_scale_or_variance`, `lean_parameterization`, "
        "`lean_scale_or_variance`, `parameter_translation`, "
        "`family_coupling_scope`, `family_coupling_evidence`, "
        "`law_equivalence_evidence`, `outcome_preservation_evidence`, and "
        "`lean_semantic_bridge`. State the literal source and Lean scale/rate/"
        "precision/standard-deviation/variance conventions and the parameter mapping "
        "formula. A positive reparameterization by itself is not source-to-Lean law "
        "equivalence: the review needs a checked equality, equivalence, or pushforward "
        "of laws plus the outcome-preservation scope. When the source compares two "
        "accuracies, scales, or parameters, state whether both arise from one "
        "parameter-independent base law or latent source; separate source-looking "
        "laws at each parameter are not a source family until a checked coupling "
        "bridge proves that relation. "
        "When a `joint_law_and_state_evolution` dimension has "
        "`requires_source_carrier_coherence_analysis_when_detected`, include a "
        "`source_carrier_coherence_analysis` object with verdict "
        "(`source_carrier_pushforward_checked`, "
        "`source_conditioned_or_restricted_pushforward_checked`, "
        "`source_defined_joint_kernel_law_checked`, "
        "`generated_product_or_kernel_not_source_pushforward`, "
        "`weighted_or_tilted_not_source_pushforward`, `mismatch_or_open`, or "
        "`documented_partial_boundary`), `source_random_variable_carrier`, "
        "`lean_random_variable_carrier`, "
        "`stage_identity_or_resampling_evidence`, `joint_law_bridge_evidence`, "
        "`measure_construction`, `measure_transport_evidence`, "
        "`source_rate_scope`, `lean_rate_scope`, and `rate_family_evidence`. "
        "State whether all stages use the same source random variable or one "
        "source-defined joint kernel law. A generated product, weighted, or tilted "
        "likelihood measure is not a source pushforward until an explicit source-carrier "
        "transport proves it. When the source claim is rate-free or rate-indexed, a "
        "fixed-rate Lean witness is insufficient: give a checked all-rate indexed family "
        "bridge with the shared source policy/carrier. "
        "In particular, compare strict tail statements with terminal cutoff/top-support facts; "
        "compare an iid/product law with the source state evolution; and compare finite Real "
        "rates with all WithTop/infinite cases after unfolding wrappers. For a detected "
        "conditioning/calibration or null-cell/partition shape, separately state whether "
        "conditioning is pointwise, almost-everywhere, positive-fiber, or measurable-event "
        "based, expose the joint-event formula, and distinguish finite, countable, and "
        "arbitrary partition scope; state cell measurability/cover/disjointness and the "
        "zero-mass-cell totalization. Do not treat an exact-fiber equation as meaningful on "
        "null or atomless fibers without a checked bridge. A finite positive-mass calculation "
        "cannot silently cover an arbitrary partition. For a detected expectation definedness "
        "shape, state what makes each expectation a defined value "
        "(integrability/measurability or extended-value convention), including "
        "indicator/strategy correctness functions. These are expanded mathematical semantics, not "
        "field-name checks.\n\n"
        "When a semantic-model dimension has "
        "`requires_source_equality_partition_analysis`, include a "
        "`source_equality_partition_analysis` object whose "
        "`semantic_association_sha256` exactly matches the generated association and "
        "whose relation is `feature_equality_iff_class_equality`. Give separate "
        "verdicts and expanded Lean evidence for "
        "`feature_equality_implies_class_equality` and "
        "`class_equality_implies_feature_equality`, plus a combined "
        "`lean_bridge_evidence`. A same-class-implies-same-feature field alone is "
        "a weaker one-way condition, not a source-defined equality partition; mark "
        "the enclosing dimension mismatch/open or partial if either direction is "
        "absent. Do not infer either direction from a type, field, binder, or "
        "declaration name.\n\n"
        "When a semantic-model dimension has "
        "`requires_strategic_observation_totality_analysis`, include a "
        "`strategic_observation_totality_analysis` object whose "
        "`semantic_association_sha256` exactly matches the generated association. "
        "State the literal source equilibrium action domain and the Lean feasible "
        "action domain; enumerate the observation branches induced by feasible "
        "actions; classify zero-probability branches; and state how each conditional "
        "expectation/posterior/payoff is total there. A full match needs a checked "
        "source-backed totalization, proof that every action-relevant branch has "
        "positive probability, proof that the action is infeasible, or an explicit "
        "source equilibrium-domain restriction. A finite off-path belief/payoff "
        "inserted only by Lean is `lean_only_offpath_completion`, not a source match; "
        "mark the enclosing dimension mismatch/open or partial. Do not infer any of "
        "this from a theorem, equilibrium predicate, strategy, posterior, binder, "
        "or function name.\n\n"
        "When a semantic-model dimension has "
        "`requires_conditioning_information_analysis`, include a "
        "`conditioning_information_analysis` object whose "
        "`semantic_association_sha256` exactly matches the generated association. "
        "For every generated source contract, reproduce its source conditional-value "
        "kind, observed-component IDs, ordered action-selection-stage IDs, "
        "raw-vs-selected law population, and conditionalization scope; then state the "
        "Lean conditional-value kind and enumerate the corresponding Lean observed "
        "components and stages with expanded descriptions. Use the direct-match verdict "
        "only when the value kind, component set, ordered stages, law population, and "
        "a.e./pointwise scope all agree. A raw posterior or raw conditional law is not "
        "evidence for a source-selected population, and a chosen RCD version does not "
        "establish a pointwise belief. Record a mismatch/open or partial boundary "
        "otherwise. This comparison is semantic and source/signature pinned; do not "
        "infer it from a "
        "posterior, belief, conditional, kernel, theorem, binder, or function name.\n\n"
        "Unfold every result-bearing predicate, iff, and transparent wrapper before "
        "assigning source credit. If a winner, feasibility, or optimality predicate "
        "unfolds to the same advertised fact about an independently supplied object, "
        "that is a self-characterization, not evidence that the source algorithm "
        "produced the object. Keep the source runner, Lean runner, runner output, "
        "fixed input profile, universally quantified profile family, and any "
        "independently characterized object in distinct semantic worlds until a "
        "Lean-checked equality, simulation, refinement, or result-preservation "
        "proposition connects them. Merely conjoining a runner-success fact with an "
        "independent definitional characterization is not such a bridge. A theorem "
        "about one fixed profile is not an all-profile theorem. A noncomputable "
        "witness is not an executable algorithm, and executability is not a "
        "polynomial-time bound; require the runtime conclusion and arithmetic/input "
        "representation model separately.\n\n"
        "When a boundary input has a nonempty result_relation, compare its proposition "
        "to the advertised result structurally. An input that is equivalent to, provides, "
        "or is a logical component of the advertised feasibility/cost/runtime/optimality "
        "result is conclusion-bearing proof debt, not independent source evidence for the "
        "same source theorem. Do not classify that caller-supplied result component as a "
        "validated_source_assumption solely from a source locator; source-facing coverage "
        "must use a row that derives the component from paper primitives.\n\n"
        "For an input carrying a generated `source_contract_association`, source credit is "
        "content-pinned rather than name-pinned. For schema 1, copy its exact "
        "`association_sha256` into `source_contract_association_sha256`, its exact "
        "`source_map_item_keys`, and its exact `source_map_item_sha256_by_key`. For schema "
        "2, copy the generated `semantic_association_sha256` exactly: it binds the current "
        "source semantic identities and exact elaborated review signature. Schema-2 legacy "
        "key/full-map pins are aggregate-route diagnostics and may be stale after a uniquely "
        "validated semantic-safe map-key or route rename; never reconstruct a semantic pin. "
        "Do not substitute "
        "a source-map key, row, binder, or function name. A literal archival source condition uses "
        "`validated_source_assumption` plus `source_target_disposition` "
        "`literal_source_match`. A necessary explicit source-model convention uses "
        "`approved_source_convention`, `source_target_disposition` "
        "`approved_source_convention`, and exact `model_convention_ids` with their current "
        "`model_convention_sha256_by_id` values. A corrected source condition uses "
        "`approved_corrected_condition`, `source_target_disposition` "
        "`approved_corrected_target`, and the exact corrected-target defect union plus "
        "`corrected_target_sha256_by_source_item` for schema 1 or "
        "`corrected_target_sha256_by_source_semantic_sha256` for schema 2. Never call an archival statement literal "
        "when its associated source-map target is corrected. `approved_external_boundary` "
        "is partial-only and cannot close a formalized paper.\n\n"
        "A recursive field carrying generated `recursive_field_explicit_parent_route` has "
        "only the narrow source route recorded in that receipt. Its classification must be "
        "one of the receipt's exact `permitted_classifications`; never extend a container "
        "route to a leaf below it. A receipt on a nested record permits only "
        "`container_recursively_audited`, and a non-container leaf can never use that "
        "classification. When the receipt permits `approved_source_convention`, use "
        "`source_target_disposition: approved_source_convention`, cite exactly its one "
        "`convention_id`, and copy its exact convention digest and source locator. Do not "
        "replace that receipt with a field name, parent declaration, or a different "
        "source-model convention.\n\n"
        "For a `semantic_model_review` item carrying a generated "
        "`source_statement_association`, the source map explicitly selected one "
        "source presentation and one current fully-qualified review route. It is "
        "not a direct/Spec structural contract and it is not evidence by name. "
        "For every successful dimension response, copy its generated schema-2 "
        "`semantic_association_sha256` exactly and state the matching "
        "`source_target_disposition`. Use `approved_corrected_target` with the "
        "exact corrected-target defect union and "
        "`corrected_target_sha256_by_source_semantic_sha256` when that selected "
        "source item has an approved corrected target; never silently label that "
        "archival statement literal. A map-key or source-locator rename can only "
        "reuse the response through this generated source-semantic plus current "
        "elaborated-signature pin.\n\n"
        "Classify the item as "
        "one of: proved_from_primitives, validated_source_assumption, approved_source_convention, "
        "approved_corrected_condition, approved_external_boundary, "
        "visible_boundary_component, derived_from_visible_boundary, "
        "container_recursively_audited, derived_consequence_record, "
        "nonpropositional_witness_data, or unresolved_assumed_math. Use "
        "visible_boundary_component only for a recursive/internal source-record field that is "
        "exactly exposed as a component of a visible theorem-boundary premise; do not use it "
        "for the theorem-boundary input itself. Use derived_from_visible_boundary only when "
        "Lean derives the recursive/internal field from visible theorem-boundary premises and "
        "the boundary premises remain explicit proof debt in the reviewed statement. "
        "container_recursively_audited only for a field whose type is another audited "
        "record/source/certificate and whose nested fields are separately judged; do not use "
        "it for a field whose type is a mathematical proposition or formula. Use "
        "derived_consequence_record only for fields of a theorem-output/consequence record "
        "whose constructor proof is separately checked and whose premise records are separately "
        "audited. Use nonpropositional_witness_data only for bare data witnesses "
        "(for example a chosen stream, cost function, gradient/noise/bias function, or "
        "projection function) whose type is not proposition-valued and does not itself state "
        "an equality, recurrence, optimality, measurability, convergence, continuity, or "
        "response/trajectory semantics. The proposition-valued fields that constrain that "
        "witness must still be classified separately. When a conclusion field reports a "
        "hidden_subtype_predicate, only the subtype's value projection is witness data; its "
        "property projection is proposition-bearing and must be proved or matched to an exact "
        "source assumption. A nonpropositional_witness_data judgment cannot discharge it. Mark "
        "unresolved_assumed_math if the Lean row merely "
        "takes a record/certificate/replay/process/bridge/source-model field that "
        "states convexity, response semantics, trace/replay validity, transfer "
        "preservation, trajectory generation, continuity, convergence, equilibrium, "
        "or a displayed formula that should be derived. Do not mark a field as "
        "proved just because Lean typechecks a projection from a structure premise. "
        "For conclusion_dependency_items, only a valid_constructors entry carrying a "
        "passing result_type_compatibility Lean-Meta definitional-equality check is "
        "authoritative for an unconditional derivation. An incompatible_constructors "
        "entry is not a route even when its record head has the same spelling: fixed "
        "parameters and universe levels must match the exact reviewed binder. A rejected constructor is "
        "circular because an alpha-equivalent/provider proposition or axiom/opaque "
        "dependency supplies the target. A conditional constructor is acceptable "
        "only through a `proved_from_primitives` judgment on that conclusion-bearing "
        "premise with a checked_projection object containing exactly: "
        "constructor_declaration, conditional_constructor_result_type, and "
        "source_antecedent_keys. The declaration and result type must exactly match "
        "one static conditional_constructors entry; source_antecedent_keys must "
        "exactly equal that entry's required_source_antecedent_fields and each key "
        "must have a current validated_source_assumption judgment with an exact "
        "source locator. Do not cite a function name or free-form lean_derivation "
        "as a substitute for this contract. A rejected/circular or unlisted "
        "constructor is invalid. Names and container suffixes do not change either "
        "verdict.\n\n"
        + item_block
    )


def source_record_llm_judge_prompt(
    paper: str, payload: Mapping[str, Any]
) -> str:
    """Render the human/LLM review prompt from immutable semantic evidence."""

    def dict_items(key: str) -> list[dict[str, Any]]:
        value = payload.get(key)
        if not isinstance(value, list):
            return []
        return [item for item in value if isinstance(item, dict)]

    conclusion_dependencies = dict_items("conclusion_dependency_items")
    dependency_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in conclusion_dependencies
    }
    covered_boundary_keys = {
        str(key).strip()
        for key in payload.get("statement_ledger_covered_boundary_input_keys", [])
        if isinstance(key, str) and key.strip()
    }
    uncovered_boundary_items = [
        item
        for item in dict_items("boundary_input_items")
        if str(item.get("judgment_key") or "").strip()
        not in covered_boundary_keys | dependency_keys
    ]
    source_proof_fidelity = payload.get("source_proof_fidelity")
    semantic_context_items = payload.get("semantic_context_requirements")
    return judge_prompt(
        paper,
        conclusion_dependencies
        + uncovered_boundary_items
        + dict_items("type_valued_certificate_result_items")
        + dict_items("rows_with_semantic_inputs")
        + dict_items("recursive_field_items")
        + dict_items("semantic_model_items"),
        source_proof_fidelity if isinstance(source_proof_fidelity, dict) else None,
        (
            [item for item in semantic_context_items if isinstance(item, dict)]
            if isinstance(semantic_context_items, list)
            else []
        ),
    )
