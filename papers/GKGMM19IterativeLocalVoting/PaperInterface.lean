import GKGMM19IterativeLocalVoting.AppendixLemmaBounds
import GKGMM19IterativeLocalVoting.PopulationTheorem3

open MeasureTheory
open AppliedModelingLib
open scoped BigOperators ENNReal

/-!
# Audited Review Surface: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This file contains the full row-level review surface used by the dashboard
and LLM-as-judge checks. `AuditInterface.lean` is only a compatibility import
for older module paths.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- If implementation endpoints become broad or helper-heavy, move them to
  `ProofInterface.lean`; keep this filename as the single review surface.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `ConditionsC123`: source assumptions C1, C2, C3.
- `IsLpNormedUtilities`: Definition 1's utility family.
- `IsWeightedEuclideanUtilitiesWith`: Definition 2's utility family.
- `IsDecomposableUtilitiesWith`: Definition 3's utility family.
- `Algorithm1ILVFormulaData`: Algorithm 1's sampling, initialization, update,
  stopping, and return semantics.
- `ModelBFiniteResponseAt`: Model B's finite-coordinate normalized movement.
- `c1_convex_solution_space_source_formula`: source interpretation of C1 as
  the direct `Convex` fact used by projection arguments.
- `theorem1_norm_pair_l2_l2`, `theorem1_norm_pair_l1_linf`, and
  `theorem1_norm_pair_linf_l1`: the three source norm pairs for Theorem 1.
- `theorem1_visible_hypotheses_case_certificate_formula`: the visible Theorem 1
  hypotheses form the structured SSGM case certificate.
- `algorithm1_radius_formula`: the ILV radius rule `r_t = r_0 / t`.
- `algorithm1_radius_tendsto_zero`: the ILV radius rule tends to zero.
- `algorithm1_radius_sq_summable`: the shifted squared radii are summable.
- `algorithm1_radius_sum_tendsto_atTop`: for `r_0 > 0`, shifted radius
  partial sums diverge.
- `algorithm1_radius_not_summable`: for `r_0 > 0`, shifted radii are not
  summable.
- `algorithm1_radius_ssgm_step_size_conditions`: the deterministic radius
  schedule satisfies the step-size conditions required by the SSGM layer.
- `algorithm1_local_neighborhood_formula`: local `Lq` ball query set.
- `algorithm1_norm_projection_formula`: the projected point is a closest
  feasible point in the selected source norm.
- `algorithm1_projected_update_formula`: the raw local response is projected
  back to the feasible set.
- `algorithm1_projected_trajectory_feasible_of_normProjection`: projected
  Algorithm 1 trajectories remain feasible.
- `algorithm1_window_stable_formula` and `algorithm1_stop_condition_formula`:
  the stopping-window and terminal-time stopping conditions.
- `modelA_raw_response_formula`: source Model A maximization over the raw
  query ball before projection.
- `modelA_raw_response_isMaxOn_formula`: mathlib extrema formulation of that
  source raw response.
- `modelA_raw_response_lp_normed_cost_minimizer_formula`: source raw utility
  maximization as distance minimization for Definition 1 utilities.
- `modelA_response_formula`, `_isMaxOn_formula`, and
  `_lp_normed_cost_minimizer_formula`: retained feasible-query variants used
  by earlier downstream interfaces.
- `modelB_finite_response_formula`: a derived characterization of
  `ModelBFiniteResponseAt` for a supplied subgradient vector.
- `modelB_finite_response_neg_lp_cost_gradient_formula`: sign-correct finite
  Model B movement for the Theorem 2 `Lp` cost-gradient candidate.
- `modelB_finite_algorithm1_trace_source_formula`: primitive raw Model B
  Algorithm 1 trace source with selected voters, sampled ideals, coordinate
  noncollision, coordinate raw-update formula, and projected updates.
- `modelB_finite_trace_source_formula`: proof-facing Model B trace source after
  the Holder-dual sign bridge derives the normalized response predicate.
- `modelB_finite_trace_selected_voter_cost_formula`: proof-facing Model B
  finite `Lp` sample costs remain tied to selected voters' ideal points after
  the raw trace source is converted.
- `theorem2_finite_ssgm_bridge_selected_voter_cost_formula`: Theorem 2's
  deterministic SSGM bridge preserves that selected-voter cost formula.
- `theorem2_source_semantics_selected_voter_cost_formula`: the same selected
  voter cost preservation directly from primitive `Theorem2` source semantics.
- `theorem2_source_semantics_step_size_conditions`: Theorem 2 source semantics
  turns the positive Algorithm 1 radius into the SSGM step-size package.
- `theorem2_source_semantics_trajectory_feasible`: Theorem 2 source semantics
  yields feasible projected Model B iterates for the selected Holder-dual case.
- `theorem2_source_semantics_finite_bridge_formula`: Theorem 2 source semantics
  builds the structured finite SSGM bridge consumed by the convergence theorem.
- `definition1_lp_normed_utilities_formula`: Lp-normed utilities.
- `finite_coordinate_norm_distance_source_formula`: finite-coordinate
  interpretation of the abstract source norm-distance field.
- `definition1_finite_coordinate_l1_formula`, `_l2_formula`,
  `_linf_formula`, and `_lp_formula`: concrete finite-coordinate source
  formulas.
- `lemma3_finite_holder_dual_gradient_candidate_norm_formula`: the algebraic
  core of Appendix C.4 Lemma 3 for the displayed finite Holder-dual gradient
  candidate.
- `lemma3_gradient_candidate_source_formula`: the displayed coordinate formula
  for that candidate gradient.
- `lemma3_gradient_candidate_hasFDerivAt_formula`: the candidate gradient is
  the Frechet derivative of the finite-coordinate `Lp` cost away from coordinate
  equalities.
- `lemma3_coordinate_equality_bad_event_null_from_boundedDensity`: the finite
  coordinate-equality bad event is null under bounded density once each base
  coordinate hyperplane is null.
- `lemma3_coordinate_equality_bad_event_null_from_productMeasure`: a concrete
  product-measure instance using atomless one-dimensional marginals.
- `lemma3_coordinate_noncollision_ae_from_productMeasure`: the corresponding
  almost-everywhere coordinate noncollision condition.
- `c3_bounded_density_coordinate_noncollision_ae`: a structured finite-coordinate
  C3 density carrier implies that noncollision condition.
- `finite_coordinate_ideal_distribution_data_formula` and
  `finite_coordinate_c3_carrier_formula`: full-space bounded-density C3 data and its
  source-facing carrier.
- `definition2_weighted_euclidean_utilities_formula`: weighted-Euclidean
  utilities.
- `weighted_euclidean_l2_ssgm_trace_source_formula`: Proposition 1 weighted
  `L2` projected update equation and sample-subgradient source trace.
- `weighted_euclidean_l2_concrete_component_trace_source_formula`: Proposition
  1 concrete component-distance trace source whose finite `L2` component
  formulas derive the sample-subgradient trace.
- `weighted_euclidean_l2_ssgm_source_formula`: proof-facing Proposition 1
  weighted `L2` projected sample-subgradient source recurrence.
- `weighted_euclidean_l2_ssgm_source_trajectory_feasible`: feasibility derived
  from that projected source recurrence.
- `proposition1_source_semantics_trajectory_feasible`: feasibility derived from
  Proposition 1 source semantics and the finite SSGM bridge for the selected
  Model A/B branch.
- `proposition1_source_semantics_step_size_conditions`: the positive source
  radius in Proposition 1 source semantics yields the SSGM step-size package.
- `weighted_euclidean_social_objective_formula_source_formula`: Proposition 1
  social optima as feasible maximizers of societal utility.
- `weighted_euclidean_social_objective_source_formula`: derived minimization
  objective `-societalUtility` used by the SSGM bridge.
- `proposition1_source_semantics_social_objective_minimizer_formula`: full
  Proposition 1 source semantics yields the same social-optimal/minimizer
  bridge.
- `proposition1_concrete_component_source_semantics_formula`: Proposition 1
  concrete component-distance source semantics used by the full primitive
  source closeout route.
- `proposition1_source_semantics_finite_bridge_formula`: Proposition 1 source
  semantics builds the structured weighted finite SSGM bridge.
- `definition3_decomposable_utilities_formula`: decomposable utilities.
- `decomposable_median_set_source_formula` and
  `decomposable_median_carrier_formula`: Proposition 2 median-set source
  formula and derived proof-facing carrier.
- `decomposable_linf_coordinate_replacement_formula` and
  `decomposable_linf_local_response_bridge_formula`: Proposition 2
  coordinate-replacement source semantics and derived local `L∞` response
  bridge.
- `finite_coordinate_product_box_solution_space_source_formula` and
  `finite_coordinate_linf_coordinate_replacement_source_formula`: explicit
  product-box and finite-coordinate `L∞` replacement source formulas used by
  Proposition 2.
- `proposition2_finite_coordinate_source_semantics_formula`: paper-faithful
  finite-coordinate Proposition 2 source semantics derived from finite norm
  semantics, product-box closure, and coordinatewise median-set source formulas.
- `proposition2_source_semantics_case_certificate_formula`: Proposition 2 source
  semantics builds the structured SSGM case certificate.
- `theorem3_finite_directional_field_model_formula`: concrete finite
  normalized-gradient field data used by the Theorem 3 closeout route.
- `theorem3_expected_finiteDot_modelB_response_increment_formula` and
  `theorem3_expected_finiteDot_modelB_response_increment_sum_formula`:
  one-step and accumulated weighted-expectation identities for finite-dot
  Model B increments.
- `theorem3_feasible_direction_at_formula`: the positive-step feasibility
  predicate used by the Theorem 3 projection residual argument.
- `theorem3_l2_projection_normal_cone_formula`,
  `theorem3_projection_residual_nonpos_formula`, and
  `theorem3_projection_step_progress_formula`: deterministic projection
  residual geometry used by the Theorem 3 drift argument.
- `theorem3_iid_weighted_voter_global_concentration_formula`: iid
  selected-voter finite-dot concentration for the corrected global-radius
  projected-trace route.
- `theorem3_global_projected_trace_ae_skeleton_formula`: explicit almost-sure
  global-tail projected Algorithm 1 trace data used by the Theorem 3 route.
- `theorem3_field_coordinate_continuity_source_formula`: source interpretation
  of directional-field uniform continuity as coordinate continuity of the
  concrete finite normalized-gradient field.
- `theorem3_global_projected_trace_deterministic_trace_core_formula`: raw
  pointwise global-tail trace source, separated from field continuity.
- `theorem3_global_projected_algorithm1_trace_source_formula`: primitive
  global projected Algorithm 1 trace generator that derives the old
  deterministic trace core.
- `theorem3_global_projected_algorithm1_update_source_formula`: split
  Algorithm 1 update source for the Theorem 3 global-tail route.
- `theorem3_aggregate_feasible_direction_formula`: record-free statement of
  the aggregate feasible-direction property used to expose the constrained
  Theorem 3 alternative without hiding it in a source record.
- `theorem3_global_projected_trace_deterministic_trace_source_formula`: raw
  pointwise global-tail trace source after recombining field continuity.
- `theorem3_global_projected_trace_deterministic_skeleton_formula`:
  proof-facing pointwise trace skeleton after adding the separate C1 convexity
  interpretation.
- `finite_coordinate_convergence_source_formula`: source reading of abstract
  point convergence as finite coordinatewise convergence.
- `finite_coordinate_full_sampled_projected_source_semantics_formula`: sampled
  projected source semantics deriving Theorem 2 and Proposition 1 deterministic
  trace records while keeping Theorem 3 update, convergence, field, continuity,
  and C1 convexity source fields visible without an aggregate feasibility
  source premise.

## Named Results

- `theorem1_lp_normed_dual_cases`, `theorem2_modelB_holder_dual_norms`,
  `proposition1_weighted_euclidean_l2`, and
  `proposition2_decomposable_linf_medians`: named convergence endpoints
  projected from theorem-specific source semantics and the approved SSGM
  convergence bundle. Proposition 2 uses the finite-coordinate/product-box
  reading exposed by `Proposition2FiniteCoordinateSourceSemantics`.
- `theorem1_modelB_linf_l1_finite_c3_convergence`: the fully concrete
  finite-coordinate `(∞,1)` Model B branch, with a bounded-density C3 ideal
  process, compact C1 projection geometry, and an explicit social-objective
  identity, converges almost surely to the social-optimum set.
- `theorem1_modelA_linf_l1_finite_c3_convergence`: the fully concrete
  finite-coordinate `(∞,1)` Model A branch, using the Borel exact water-filled
  local minimizer and the corrected crossing-or-near-tie perturbation budget,
  converges almost surely to the social-optimum set.
- `theorem1_modelA_l2_l2_finite_c3_convergence`,
  `theorem1_modelB_l2_l2_finite_c3_convergence`,
  `theorem1_modelA_l1_linf_finite_c3_convergence`, and
  `theorem1_modelB_l1_linf_finite_c3_convergence`: the other four concrete
  finite-coordinate branches of Theorem 1, with their displayed Algorithm 1
  trajectories and the corresponding expected-cost/social-objective identity.
- `theorem2_modelB_finite_holder_dual_c3_convergence`: the concrete
  finite-exponent Hölder-dual Model B execution used by Theorem 2.
- `proposition1_weighted_euclidean_l2_finite_execution_convergence`: the
  checked finite-coordinate weighted-Euclidean `L2` outcome-indexed execution
  reaches the source social-optimum set.  Its exact sampled-process
  construction remains a visible source-model obligation.
- `proposition1_weighted_euclidean_l2_modelA_joint_execution_convergence`:
  the concrete joint-law Model A execution, with a measurable exact source
  response and its C3 rare-event correction, reaches the identified
  social-optimal set.
- `proposition2_coordinatewise_boundary_finite_c3_median`: Proposition 2 under
  the coordinatewise-boundary Model B reading used in its proof.  The visible
  `Spec` retains the decomposable-utility scope, checks the concrete response
  trace, and proves Model A and Model B convergence to the transparent
  feasible expected-absolute-deviation median target.
- `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_projected_trace`:
  paper-faithful projected-trace endpoint using the original global Algorithm 1
  radius schedule along each tail.
- `theorem3_convergent_l2_modelB_is_directional_equilibrium_global_ae_trace`:
  same corrected global route from the almost-sure trace skeleton; the
  selected-voter concentration theorem is proved in `ProofInterface.lean`.
- `theorem3_zero_or_no_aggregate_feasible_direction_formula`: constrained
  projected Theorem 3 alternative proved from the sampled projected source
  package without assuming the missing aggregate feasible-direction property.
- `theorem3_statement_of_full_sampled_projected_source_semantics_univ`: exact
  `theorem3Statement` recovery from the sampled projected source package under
  the explicit full-space condition `E.solutionSpace = Set.univ`.
- `theorem3_full_space_and_restricted_space`: the full-space recovery of the
  printed conclusion together with the approved restricted-space alternative.
- `finite_coordinate_source_semantics_ssgm_consequences`: the four
  SSGM-backed endpoint statements from separate theorem source semantics plus
  an explicit SSGM theorem bundle.
- `finite_coordinate_full_sampled_projected_paper_consequences_with_ssgm` and
  `finite_coordinate_full_sampled_projected_paper_consequences`: projected
  finite-coordinate closeout from sampled source semantics and an explicit
  SSGM theorem bundle, recording the constrained Theorem 3 alternative plus
  the full-space exact recovery theorem.
-/

namespace GKGMM19IterativeLocalVoting

/--
Data-only carrier for review-surface formulas that use only the feasible set
and norm-distance notation from an ILV instance.
-/
structure ILVGeometryFormulaData (Point : Type*) where
  solutionSpace : Set Point
  normDistance : SourceNorm → Point → Point → ℝ

/-- Data-only feasible local-neighborhood variant retained for prior review rows. -/
def localNeighborhoodFormulaData {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (center : Point) (r : ℝ) : Set Point :=
  {candidate | candidate ∈ G.solutionSpace ∧
    G.normDistance q candidate center ≤ r}

/-- The source Model A raw query ball before Algorithm 1 performs its projection. -/
def rawLocalNeighborhoodFormulaData {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (center : Point) (r : ℝ) : Set Point :=
  {candidate | G.normDistance q candidate center ≤ r}

/-- Data-only projection formula for the source notation `[y]_X`. -/
def isNormProjectionOntoFormulaData {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (project : Point → Point) : Prop :=
  ∀ y, project y ∈ G.solutionSpace ∧
    IsMinOn (fun x => G.normDistance q x y) G.solutionSpace (project y)

/-- Data-only stopping-window formula for Algorithm 1. -/
def algorithm1WindowStableFormulaData {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) : Prop :=
  ∀ l m,
    l ∈ Finset.Icc (t - N) t →
      m ∈ Finset.Icc (t - N) t →
        G.normDistance q (trajectory l) (trajectory m) ≤ epsilon

/-- Data-only stopping condition formula for Algorithm 1. -/
def algorithm1StopConditionFormulaData {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) : Prop :=
  t = T ∨ algorithm1WindowStableFormulaData G q trajectory t N epsilon

/--
Data-only carrier for review-surface formulas that use only utility, the
feasible set, and the source norm-distance notation.
-/
structure ILVUtilityFormulaData (Voter Point : Type*) where
  solutionSpace : Set Point
  utility : Voter → Point → ℝ
  normDistance : SourceNorm → Point → Point → ℝ
  /-- The governing model says each voter's utility is bounded on the feasible set. -/
  utility_bounded_on_solutionSpace : ∀ voter, ∃ bound : ℝ, ∀ x,
    x ∈ solutionSpace → |utility voter x| ≤ bound

def ILVUtilityFormulaData.geometry {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) :
    ILVGeometryFormulaData Point where
  solutionSpace := U.solutionSpace
  normDistance := U.normDistance

/-- Transparent governing-model clause that every voter utility is bounded on `X`. -/
def utilityBoundedOnSolutionSpaceFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) : Prop :=
  ∀ voter, ∃ bound : ℝ, ∀ x, x ∈ U.solutionSpace → |U.utility voter x| ≤ bound

def modelAResponseFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
    ∀ candidate, candidate ∈ localNeighborhoodFormulaData U.geometry q center r →
      U.utility voter candidate ≤ U.utility voter response

/-- Source-faithful Model A response over the raw query ball. -/
def modelARawResponseFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
    ∀ candidate, candidate ∈ rawLocalNeighborhoodFormulaData U.geometry q center r →
      U.utility voter candidate ≤ U.utility voter response

/--
Complete finite-coordinate source formula for a Model B response.  Unlike the
implementation carrier, this review target exposes both the printed
subgradient inequality and the normalized full-radius update in one place.  It
also records the approved source-definedness convention for the otherwise
unstated zero-gradient case: the voter stays at the current point.
-/
/- The source's admissible norm parameters: `L1`, `L2`, `L∞`, or `Lp` with `p > 0`. -/
def sourceNormFormulaData : SourceNorm → Prop
  | SourceNorm.l1 => True
  | SourceNorm.l2 => True
  | SourceNorm.linfty => True
  | SourceNorm.lp p => 0 < p

def modelBFiniteResponseFormulaData
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : (Coord → ℝ) → ℝ) (q : SourceNorm)
    (center : Coord → ℝ) (r : ℝ) (response : Coord → ℝ) : Prop :=
  sourceNormFormulaData q ∧
    ∃ gradient : Coord → ℝ,
      (∀ y,
        utility y - utility center ≥
          AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
            gradient (fun i => y i - center i)) ∧
        ((gradient = 0 ∧ response = center) ∨
          (gradient ≠ 0 ∧ response = fun i =>
            center i + r * (gradient i / finiteCoordinateNorm q gradient)))

def isLpNormedUtilitiesFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (ideal : Voter → Point)
    (p : SourceNorm) : Prop :=
  ∀ v x, U.utility v x = -U.normDistance p x (ideal v)

/--
The printed Definition 1 formula on the feasible solution space.  Algorithm 1
queries raw local candidates before projection; the separately reviewed
raw-query-domain convention supplies `isLpNormedUtilitiesFormulaData` at those
points.
-/
def isLpNormedUtilitiesOnSolutionSpaceFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (ideal : Voter → Point)
    (p : SourceNorm) : Prop :=
  ∀ v x, x ∈ U.solutionSpace → U.utility v x = -U.normDistance p x (ideal v)

/--
Exact finite-coordinate Definition 1 formula on the paper's feasible solution
space.  This is the source-facing review target; the generic utility carrier
above remains proof support only.
-/
def finiteCoordinateLpNormedUtilitiesOnSolutionSpaceFormulaData
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p : SourceNorm) : Prop :=
  sourceNormFormulaData p ∧
    ∀ voter x, x ∈ E.solutionSpace →
      E.utility voter x = -finiteCoordinateDistance p x (E.ideal voter)

/--
Approved raw-query-domain extension of Definition 1.  Algorithm 1 maximizes
the displayed utility before projection, so the same finite-coordinate formula
is available at every raw candidate in that query.
-/
def finiteCoordinateLpNormedUtilitiesRawQueryFormulaData
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p : SourceNorm) : Prop :=
  sourceNormFormulaData p ∧
    ∀ voter x,
      E.utility voter x = -finiteCoordinateDistance p x (E.ideal voter)

/--
Exact finite-coordinate Model A response: an arbitrary utility maximizer in
the raw `Lq` ball, before the algorithm's later projection onto `X`.
-/
def finiteCoordinateModelARawResponseFormulaData
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (q : SourceNorm)
    (center : Coord → ℝ) (radius : ℝ) (voter : Voter)
    (response : Coord → ℝ) : Prop :=
  sourceNormFormulaData q ∧
    finiteCoordinateDistance q response center ≤ radius ∧
      ∀ candidate,
        finiteCoordinateDistance q candidate center ≤ radius →
          E.utility voter candidate ≤ E.utility voter response

/--
Exact finite-coordinate Algorithm 1 source surface.  The paper's unqualified
projection and stopping-vector magnitude are represented by the standard
Euclidean interpretation on its ambient `R^M` decision space.
-/
def finiteCoordinateAlgorithm1ILVFormulaData
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (population : Measure Voter) (executionLaw : Measure (ℕ → Voter))
    (E : ILVEnvironment Voter (Coord → ℝ)) (q : SourceNorm)
    (initial : Coord → ℝ) (epsilon : ℝ) (N : ℕ) (r0 : ℝ) (T : ℕ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (rawResponse trajectory : (ℕ → Voter) → ℕ → Coord → ℝ)
    (stopTime : (ℕ → Voter) → ℕ) (output : (ℕ → Voter) → Coord → ℝ) : Prop :=
  sourceNormFormulaData q ∧
    IsProbabilityMeasure population ∧
      executionLaw = (Measure.infinitePi fun _ : ℕ => population) ∧
        initial ∈ E.solutionSpace ∧
          0 < epsilon ∧ 0 < r0 ∧ 0 < T ∧
            AppliedModelingLib.Optimization.EuclideanProjectionOnto
              E.solutionSpace project ∧
              ((∀ (omega : ℕ → Voter) (t : ℕ),
                  finiteCoordinateModelARawResponseFormulaData E q
                    (trajectory omega t) (ilvRadius r0 (t + 1))
                    (omega (t + 1)) (rawResponse omega (t + 1))) ∨
                (∀ (omega : ℕ → Voter) (t : ℕ),
                  modelBFiniteResponseFormulaData
                    (E.utility (omega (t + 1))) q
                    (trajectory omega t) (ilvRadius r0 (t + 1))
                    (rawResponse omega (t + 1)))) ∧
              ∀ omega : ℕ → Voter,
                trajectory omega 0 = initial ∧
                  (∀ t : ℕ,
                    trajectory omega (t + 1) = project (rawResponse omega (t + 1))) ∧
                  0 < stopTime omega ∧ stopTime omega ≤ T ∧
                  (stopTime omega = T ∨
                    ∀ l m,
                      l ∈ Finset.Icc (stopTime omega - N) (stopTime omega) →
                        m ∈ Finset.Icc (stopTime omega - N) (stopTime omega) →
                          finiteCoordinateDistance SourceNorm.l2
                            (trajectory omega l) (trajectory omega m) ≤ epsilon) ∧
                  (∀ t : ℕ, 0 < t → t < stopTime omega →
                    ¬ ∀ l m,
                      l ∈ Finset.Icc (t - N) t →
                        m ∈ Finset.Icc (t - N) t →
                          finiteCoordinateDistance SourceNorm.l2
                            (trajectory omega l) (trajectory omega m) ≤ epsilon) ∧
                  output omega = trajectory omega (stopTime omega)

/--
Exact finite-coordinate Definition 3 formula.  The sum ranges over all `M`
ambient coordinates and evaluates each component utility at that coordinate.
-/
def finiteCoordinateDecomposableUtilityFamilyFormulaData
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (componentUtility : Coord → Voter → ℝ → ℝ) : Prop :=
  (∀ coordinate voter, ConcaveOn ℝ Set.univ (componentUtility coordinate voter)) ∧
    ∀ voter x,
      E.utility voter x =
        Finset.univ.sum (fun coordinate => componentUtility coordinate voter (x coordinate))

/-- The independent population-sampling law used by Algorithm 1. -/
noncomputable def algorithm1SampleLaw {Voter : Type*} [MeasurableSpace Voter]
    (population : Measure Voter) : Measure (ℕ → Voter) :=
  Measure.infinitePi fun _ : ℕ => population

/--
Complete source semantics of Algorithm 1.

The outcome `omega` supplies the independently sampled voter at source time
`t + 1`. The relation records every displayed input, the raw favorite-point
query, projection, first stopping time, and returned solution.
-/
def Algorithm1ILVFormulaData {Voter Point : Type*} [MeasurableSpace Voter]
    (population : Measure Voter) (executionLaw : Measure (ℕ → Voter))
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (initial : Point) (epsilon : ℝ) (N : ℕ) (r0 : ℝ) (T : ℕ)
    (project : Point → Point)
    (rawResponse trajectory : (ℕ → Voter) → ℕ → Point)
    (stopTime : (ℕ → Voter) → ℕ) (output : (ℕ → Voter) → Point) : Prop :=
  IsProbabilityMeasure population ∧
    executionLaw = algorithm1SampleLaw population ∧
      initial ∈ U.solutionSpace ∧
        0 < epsilon ∧ 0 < r0 ∧ 0 < T ∧
          isNormProjectionOntoFormulaData U.geometry SourceNorm.l2 project ∧
          ∀ omega : ℕ → Voter,
            trajectory omega 0 = initial ∧
              (∀ t : ℕ,
                modelARawResponseFormulaData U q (trajectory omega t)
                  (ilvRadius r0 (t + 1)) (omega (t + 1))
                  (rawResponse omega (t + 1)) ∧
                trajectory omega (t + 1) =
                  project (rawResponse omega (t + 1))) ∧
              0 < stopTime omega ∧ stopTime omega ≤ T ∧
              (stopTime omega = T ∨
                algorithm1WindowStableFormulaData U.geometry SourceNorm.l2
                  (trajectory omega) (stopTime omega) N epsilon) ∧
              (∀ t : ℕ, 0 < t → t < stopTime omega →
                ¬ algorithm1WindowStableFormulaData U.geometry SourceNorm.l2
                    (trajectory omega) t N epsilon) ∧
              output omega = trajectory omega (stopTime omega)

def normDistanceMinimizerFormulaData {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (p : SourceNorm)
    (target : Point) (feasible : Set Point) (response : Point) : Prop :=
  response ∈ feasible ∧
    ∀ candidate, candidate ∈ feasible →
      U.normDistance p response target ≤ U.normDistance p candidate target

/--
C1 convexity source interpretation: the abstract paper C1 clause gives the
`Convex` fact used by the finite-dimensional projection residual proof.
-/
theorem c1_convex_solution_space_source_formula {Voter Point : Type*}
    [AddCommMonoid Point] [Module ℝ Point]
    (E : ILVEnvironment Voter Point) :
    Nonempty (C1ConvexSolutionSpaceSource E) ↔
      Convex ℝ E.solutionSpace := by
  constructor
  · rintro ⟨S⟩
    exact S.convex_solutionSpace
  · intro h
    exact ⟨{ convex_solutionSpace := h }⟩

/-- Theorem 1 source norm pair `(2,2)`. -/
theorem theorem1_norm_pair_l2_l2 :
    Theorem1NormPair SourceNorm.l2 SourceNorm.l2 := by
  exact theorem1NormPair_l2_l2

/-- Theorem 1 source norm pair `(1,∞)`. -/
theorem theorem1_norm_pair_l1_linf :
    Theorem1NormPair SourceNorm.l1 SourceNorm.linfty := by
  exact theorem1NormPair_l1_linf

/-- Theorem 1 source norm pair `(∞,1)`. -/
theorem theorem1_norm_pair_linf_l1 :
    Theorem1NormPair SourceNorm.linfty SourceNorm.l1 := by
  exact theorem1NormPair_linf_l1

/--
Theorem 1 deterministic handoff: C1-C3, the selected `Lp` utility condition,
the Model A/B branch, the response predicate, and one of the three norm-pair
cases are exactly the source certificate consumed by the SSGM convergence
theorem.
-/
theorem theorem1_visible_hypotheses_case_certificate_formula
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    {p q : SourceNorm} {model : VoterResponseModel}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E p)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model)
    (hpq : Theorem1NormPair p q) :
    Theorem1SSGMCaseCertificate E p q model := by
  exact
    proof_theorem1_caseCertificate_of_visible_hypotheses
      hC hUtil hmodel hResponse hpq

/--
Algorithm 1 step-size schedule `r_t = r_0 / t`.

Source status: exact displayed Algorithm 1 formula.
-/
theorem algorithm1_radius_formula (r0 : ℝ) (t : ℕ) :
    ilvRadius r0 t = r0 / (t : ℝ) := by
  rfl

/-- Algorithm 1 radius schedule tends to zero. -/
theorem algorithm1_radius_tendsto_zero (r0 : ℝ) :
    Filter.Tendsto (ilvRadius r0) Filter.atTop (nhds 0) := by
  exact ilvRadius_tendsto_zero r0

/--
Algorithm 1 shifted squared radii are summable, matching the square-step
condition used by stochastic approximation arguments.
-/
theorem algorithm1_radius_sq_summable (r0 : ℝ) :
    Summable (fun t : ℕ => (ilvRadius r0 (t + 1)) ^ 2) := by
  exact ilvRadius_sq_summable r0

/--
Algorithm 1 shifted radius partial sums diverge for positive initial radius,
matching the non-summable step-size condition used by stochastic approximation
arguments.
-/
theorem algorithm1_radius_sum_tendsto_atTop {r0 : ℝ} (hr0 : 0 < r0) :
    Filter.Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
      Filter.atTop Filter.atTop := by
  exact ilvRadius_sum_tendsto_atTop hr0

/--
Algorithm 1 shifted radii are not summable for positive initial radius.
-/
theorem algorithm1_radius_not_summable {r0 : ℝ} (hr0 : 0 < r0) :
    ¬ Summable (fun t : ℕ => ilvRadius r0 (t + 1)) := by
  exact ilvRadius_not_summable hr0

/--
Algorithm 1 radius schedule satisfies the step-size package used by the
stochastic subgradient layer.
-/
theorem algorithm1_radius_ssgm_step_size_conditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact algorithm1_radius_ssgmStepSizeConditions hr0

/--
Algorithm 1 local-neighborhood query set.
Source status: direct source formula
Source note: This is the local `Lq`-ball query intersected with the feasible
solution space `X`.
-/
theorem algorithm1_local_neighborhood_formula {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (center candidate : Point) (r : ℝ) :
    candidate ∈ localNeighborhoodFormulaData G q center r ↔
      candidate ∈ G.solutionSpace ∧
        G.normDistance q candidate center ≤ r := by
  rfl

/--
Algorithm 1 projection operator `[y]_X`: a selected feasible point minimizing
distance to the raw point in the source norm used for projection.

Source status: direct source formula
-/
theorem algorithm1_norm_projection_formula {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (project : Point → Point) :
    isNormProjectionOntoFormulaData G q project ↔
      ∀ y, project y ∈ G.solutionSpace ∧
        IsMinOn (fun x => G.normDistance q x y) G.solutionSpace (project y) := by
  rfl

/--
Algorithm 1 projected update: the next iterate is the projection of the raw
local response.

Source status: direct source formula
-/
theorem algorithm1_projected_update_formula
    {Point : Type*} (project : Point → Point) (raw next : Point) :
    Algorithm1ProjectedUpdate project raw next ↔ next = project raw := by
  exact algorithm1ProjectedUpdate_formula project raw next

/--
Projected Algorithm 1 trajectories stay in the feasible solution space once
initialized there.

Source status: derived invariant from the projection formula
-/
theorem algorithm1_projected_trajectory_feasible_of_normProjection
    {Point : Type*} {G : ILVGeometryFormulaData Point} {q : SourceNorm}
    {project : Point → Point} {raw trajectory : ℕ → Point}
    (hproject : isNormProjectionOntoFormulaData G q project)
    (h0 : trajectory 0 ∈ G.solutionSpace)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ G.solutionSpace := by
  exact algorithm1ProjectedUpdates_mem_of_projectionOnto
    (fun y => (hproject y).1) h0 hupdate

/--
Algorithm 1 stopping-window condition: all recent iterates in the window are
within `epsilon` of one another.

Source status: direct source formula
-/
theorem algorithm1_window_stable_formula {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) :
    algorithm1WindowStableFormulaData G q trajectory t N epsilon ↔
      ∀ l m,
        l ∈ Finset.Icc (t - N) t →
          m ∈ Finset.Icc (t - N) t →
            G.normDistance q (trajectory l) (trajectory m) ≤ epsilon := by
  rfl

/--
Algorithm 1 stopping condition: stop at terminal time `T` or when the recent
window is stable.

Source status: direct source formula
-/
theorem algorithm1_stop_condition_formula {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) :
    algorithm1StopConditionFormulaData G q trajectory T N t epsilon ↔
      t = T ∨ algorithm1WindowStableFormulaData G q trajectory t N epsilon := by
  rfl

/--
Feasible-query Model A variant retained for downstream interfaces that require
the raw response itself to lie in the solution space.  The paper's direct
Model A query is instead exposed by `modelA_raw_response_formula`.
-/
theorem modelA_response_formula {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    modelAResponseFormulaData U q center r voter response ↔
      response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
        ∀ candidate, candidate ∈ localNeighborhoodFormulaData U.geometry q center r →
          U.utility voter candidate ≤ U.utility voter response := by
  rfl

/-- Feasible-query Model A variant as mathlib `IsMaxOn`. -/
theorem modelA_response_isMaxOn_formula {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    modelAResponseFormulaData U q center r voter response ↔
      response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
        IsMaxOn (U.utility voter)
          (localNeighborhoodFormulaData U.geometry q center r) response := by
  rfl

/--
Model A source formula: the voter returns a favorite point in the raw queried
norm ball, and Algorithm 1 projects that response onto the feasible set later.
Source status: direct source formula
-/
theorem modelA_raw_response_formula {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    modelARawResponseFormulaData U q center r voter response ↔
      response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
        ∀ candidate, candidate ∈ rawLocalNeighborhoodFormulaData U.geometry q center r →
          U.utility voter candidate ≤ U.utility voter response := by
  rfl

/-- Model A source formula as mathlib `IsMaxOn` over the raw query ball. -/
theorem modelA_raw_response_isMaxOn_formula {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    modelARawResponseFormulaData U q center r voter response ↔
      response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
        IsMaxOn (U.utility voter)
          (rawLocalNeighborhoodFormulaData U.geometry q center r) response := by
  rfl

/--
Finite-coordinate Theorem 2 Model B response formula after Lemma 3 removes the
normalization from the sign-correct utility-gradient direction.

Source status: derived finite-coordinate sign bridge from Lemma 3
-/
theorem modelB_finite_response_neg_lp_cost_gradient_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response ↔
      response =
        fun i => center i - r *
          lpCostGradientCandidate p (fun j => center j - ideal j) i := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_formula
    hdual hcoord r response

/--
Raw finite Model B Algorithm 1 trace source: selected voters determine the
sampled ideal points used in the finite `Lp` costs, raw responses follow the
paper's sign-correct coordinate update, and projected updates generate the
environment trajectory.
-/
theorem modelB_finite_algorithm1_trace_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) :
    Nonempty (FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ voter : ℕ → Voter,
          ∃ raw : ℕ → Coord → ℝ,
            IsNormProjectionOnto E (SourceNorm.lp q) project ∧
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈
                E.solutionSpace ∧
              (∀ t : ℕ,
                ∀ i : Coord,
                  E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t i ≠
                    E.ideal (voter t) i) ∧
              (∀ t : ℕ,
                raw t =
                  fun i =>
                    E.trajectory (SourceNorm.lp q)
                        VoterResponseModel.modelB t i -
                      ilvRadius r0 (t + 1) *
                        lpCostGradientCandidate p
                          (fun j =>
                            E.trajectory (SourceNorm.lp q)
                                VoterResponseModel.modelB t j -
                              E.ideal (voter t) j) i) ∧
              (∀ t : ℕ,
                Algorithm1ProjectedUpdate project (raw t)
                  (E.trajectory (SourceNorm.lp q)
                    VoterResponseModel.modelB (t + 1))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.voter, S.raw, S.project_norm, S.initial_feasible,
      S.coordinate_noncollision, S.raw_update_formula, S.projected_update⟩
  · rintro ⟨project, voter, raw, hProject, hInitial, hAvoids, hRawUpdate,
      hUpdate⟩
    exact
      ⟨{ project := project
         voter := voter
         raw := raw
         project_norm := hProject
         initial_feasible := hInitial
         coordinate_noncollision := hAvoids
         raw_update_formula := hRawUpdate
         projected_update := hUpdate }⟩

/--
Proof-facing finite Model B Algorithm 1 trace source: the raw coordinate update
has been converted to the normalized Model B response predicate by Holder
duality and coordinate noncollision.
-/
theorem modelB_finite_trace_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) :
    Nonempty (FiniteModelBILVTraceSource E p q r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ voter : ℕ → Voter,
          ∃ raw : ℕ → Coord → ℝ,
            IsNormProjectionOnto E (SourceNorm.lp q) project ∧
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈
                E.solutionSpace ∧
              (∀ t : ℕ,
                E.ideal (voter t) ∉
                  coordinateEqualityBadEvent
                    (E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t)) ∧
              (∀ t : ℕ,
                ModelBFiniteResponseAt (SourceNorm.lp q)
                  (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
                  (ilvRadius r0 (t + 1))
                  (fun i => -lpCostGradientCandidate p
                    (fun j =>
                      E.trajectory (SourceNorm.lp q)
                          VoterResponseModel.modelB t j -
                        E.ideal (voter t) j) i)
                  (raw t)) ∧
              (∀ t : ℕ,
                Algorithm1ProjectedUpdate project (raw t)
                  (E.trajectory (SourceNorm.lp q)
                    VoterResponseModel.modelB (t + 1))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.voter, S.raw, S.project_norm, S.initial_feasible,
      S.avoids_badEvent, S.modelB_response, S.projected_update⟩
  · rintro ⟨project, voter, raw, hProject, hInitial, hAvoids, hResponse,
      hUpdate⟩
    exact
      ⟨{ project := project
         voter := voter
         raw := raw
         project_norm := hProject
         initial_feasible := hInitial
         avoids_badEvent := hAvoids
         modelB_response := hResponse
         projected_update := hUpdate }⟩

/--
Proof-facing Theorem 2 trace sample-cost formula: after the Holder-dual sign
bridge converts the raw selected-voter trace to the normalized Model B response
predicate, the finite `Lp` sample costs still use the ideal point of the same
selected voter.
-/
theorem modelB_finite_trace_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0) :
    (∀ t : ℕ, T.ideal t = E.ideal (T.voter t)) ∧
      (∀ t : ℕ, ∀ y : Coord → ℝ,
        AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - T.ideal t i) =
          AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - E.ideal (T.voter t) i)) := by
  exact ⟨T.ideal_eq_selectedVoter, T.lpCost_eq_selectedVoter_lpCost⟩

/--
Theorem 2 deterministic SSGM bridge sample-cost formula: the finite `Lp` cost
seen by the SSGM boundary is the cost to the ideal of the selected voter in the
underlying Algorithm 1 trace.
-/
theorem theorem2_finite_ssgm_bridge_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q) :
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) :=
  B.lpCost_eq_selectedVoter_lpCost

/--
Theorem 2 source-semantics selected-voter cost formula: the finite SSGM bridge
constructed from primitive `Theorem2` source semantics preserves the fact that
every sample cost is measured against the selected voter's ideal point.
-/
theorem theorem2_source_semantics_selected_voter_cost_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    let B : Theorem2FiniteSSGMBridge E p q :=
      proof_theorem2SourceSemantics_finite_bridge
        (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) := by
  exact
    proof_theorem2SourceSemantics_finite_bridge_selected_voter_cost_formula
      (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/--
Theorem 2 source-semantics radius consequence: the positive Algorithm 1 radius
in the deterministic source semantics supplies the SSGM step-size hypotheses.
-/
theorem theorem2_source_semantics_step_size_conditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E) :
    SSGMStepSizeConditions (ilvRadius S.r0) := by
  exact
    proof_theorem2SourceSemantics_stepSizeConditions
      (theorem2SourceSemantics_of_primitive S)

/--
Theorem 2 source-semantics trajectory feasibility: after the raw selected-voter
Model B trace is converted through the Holder-dual finite bridge, every
projected Model B iterate remains in the feasible solution space.
-/
theorem theorem2_source_semantics_trajectory_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    ∀ t : ℕ,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
        E.solutionSpace := by
  exact
    proof_theorem2SourceSemantics_trajectory_mem_solutionSpace
      (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/--
Theorem 2 source-semantics finite bridge: the deterministic source semantics
build the structured finite SSGM input bridge for the selected Holder-dual
case.
-/
def theorem2_source_semantics_finite_bridge_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    Theorem2FiniteSSGMBridge E p q :=
  proof_theorem2SourceSemantics_finite_bridge
    (theorem2SourceSemantics_of_primitive S) hC hUtil hResponse hdual

/--
Finite-coordinate source norm-distance formula: the abstract environment
distance field is interpreted as the concrete finite-coordinate source norm.
-/
theorem finite_coordinate_norm_distance_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    UsesFiniteCoordinateNormDistance E ↔
      ∀ p x y, E.normDistance p x y = finiteCoordinateDistance p x y := by
  rfl

/--
Model A under Definition 1 is the appendix cost-minimization problem over the
local neighborhood.
Source status: derived sign bridge from Definition 1
-/
theorem modelA_response_lp_normed_cost_minimizer_formula
    {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (p q : SourceNorm)
    (ideal : Voter → Point)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : isLpNormedUtilitiesFormulaData U ideal p) :
    modelAResponseFormulaData U q center r voter response ↔
      response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
        IsMinOn (fun candidate => U.normDistance p candidate (ideal voter))
          (localNeighborhoodFormulaData U.geometry q center r) response := by
  constructor
  · intro h
    rcases h with ⟨hmem, hmax⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmax candidate hcandidate
    rw [hUtil voter candidate, hUtil voter response] at hle
    exact neg_le_neg_iff.mp hle
  · intro h
    rcases h with ⟨hmem, hmin⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmin hcandidate
    rw [hUtil voter candidate, hUtil voter response]
    exact neg_le_neg hle

/--
Under Definition 1, the source Model A raw response minimizes distance to the
voter's ideal point over the raw query ball.
Source status: derived sign bridge from Definition 1
-/
theorem modelA_raw_response_lp_normed_cost_minimizer_formula
    {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (p q : SourceNorm)
    (ideal : Voter → Point)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : isLpNormedUtilitiesFormulaData U ideal p) :
    modelARawResponseFormulaData U q center r voter response ↔
      response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
        IsMinOn (fun candidate => U.normDistance p candidate (ideal voter))
          (rawLocalNeighborhoodFormulaData U.geometry q center r) response := by
  constructor
  · intro h
    rcases h with ⟨hmem, hmax⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmax candidate hcandidate
    rw [hUtil voter candidate, hUtil voter response] at hle
    exact neg_le_neg_iff.mp hle
  · intro h
    rcases h with ⟨hmem, hmin⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmin hcandidate
    rw [hUtil voter candidate, hUtil voter response]
    exact neg_le_neg hle

/-- Definition 1 specialized to concrete finite-coordinate `L1`. -/
theorem definition1_finite_coordinate_l1_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) :
    (∀ v x, utility v x =
        -finiteCoordinateDistance SourceNorm.l1 x (ideal v)) ↔
      ∀ v x, utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.l1
          (fun m => x m - ideal v m) := by
  rfl

/-- Definition 1 specialized to concrete finite-coordinate `L2`. -/
theorem definition1_finite_coordinate_l2_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) :
    (∀ v x, utility v x =
        -finiteCoordinateDistance SourceNorm.l2 x (ideal v)) ↔
      ∀ v x, utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun m => x m - ideal v m) := by
  rfl

/-- Definition 1 specialized to concrete finite-coordinate `L∞`. -/
theorem definition1_finite_coordinate_linf_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) :
    (∀ v x, utility v x =
        -finiteCoordinateDistance SourceNorm.linfty x (ideal v)) ↔
      ∀ v x, utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.linf
          (fun m => x m - ideal v m) := by
  rfl

/-- Definition 1 specialized to concrete finite-coordinate finite `Lp`. -/
theorem definition1_finite_coordinate_lp_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ)
    (p : ℝ) :
    (∀ v x, utility v x =
        -finiteCoordinateDistance (SourceNorm.lp p) x (ideal v)) ↔
      ∀ v x, utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun m => x m - ideal v m) := by
  rfl

/--
Appendix C.4 Lemma 3 displayed candidate-gradient coordinate formula.

Source status: direct finite-coordinate formula bridge. The denominator is shown
in the paper's `||x - ideal||_p^(p-1)` form.
-/
theorem lemma3_gradient_candidate_source_formula
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 0 < p) (d : Coord → ℝ) :
    lpCostGradientCandidate p d =
      fun i => (|d i| ^ (p - 1) * (d i / |d i|)) /
        (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
  exact lpCostGradientCandidate_eq_source_formula hp d

/--
Appendix C.4 Lemma 3, algebraic core: the displayed finite Holder-dual
gradient candidate for the `Lp` cost has `Lq` norm equal to `1` away from
coordinate equalities.

Source status: formalized candidate-gradient algebra. The matching
finite-coordinate derivative attachment is exposed in the next row.
-/
theorem lemma3_finite_holder_dual_gradient_candidate_norm_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    finiteCoordinateNorm (SourceNorm.lp q)
      (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1 := by
  exact lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl hdual hcoord

/--
Appendix C.4 Lemma 3 derivative attachment: away from coordinate equalities,
the displayed candidate-gradient vector represents the Frechet derivative of
the finite-coordinate `Lp` cost.

Source status: formalized finite-coordinate differentiability bridge.
-/
theorem lemma3_gradient_candidate_hasFDerivAt_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    HasFDerivAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p (fun i => x i - ideal i))) x := by
  have hd : ∀ i, (fun j => x j - ideal j) i ≠ 0 := by
    intro i
    exact sub_ne_zero.mpr (hcoord i)
  have hbase :
      HasFDerivAt
        (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (fun i => x i - ideal i) :=
    hasFDerivAt_lpCostGradientCandidate hp hd
  simpa [Function.comp_def] using
    (hasFDerivAt_comp_sub (𝕜 := ℝ)
      (f := fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
      (f' := AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p (fun i => x i - ideal i)))
      (x := x) ideal).mpr hbase

/--
Appendix C.4 Lemma 3 bad-event bridge: the finite union of coordinate-equality
hyperplanes is null under a bounded-density ideal distribution, provided each
coordinate hyperplane is null for the base measure.

Source status: formalized finite-union and absolute-continuity reduction.
-/
theorem lemma3_coordinate_equality_bad_event_null_from_boundedDensity
    {Coord : Type*} [Fintype Coord] [MeasurableSpace (Coord → ℝ)]
    {ν μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : AppliedModelingLib.Probability.HasBoundedDensity ν μ C)
    (x : Coord → ℝ)
    (hcoord : ∀ i, ν (coordinateEqualityHyperplane x i) = 0) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact boundedDensity_coordinateEqualityBadEvent_null hbd x hcoord

/--
Appendix C.4 Lemma 3 bad-event bridge, product-measure instance: if the ideal
distribution has bounded density with respect to a finite product of atomless
one-dimensional marginals, then the coordinate-equality bad event is null.

Source status: formalized finite-dimensional product-measure nullness plus
absolute-continuity transfer.
-/
theorem lemma3_coordinate_equality_bad_event_null_from_productMeasure
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact productMeasure_boundedDensity_coordinateEqualityBadEvent_null ρ hbd x

/--
Appendix C.4 Lemma 3 bad-event bridge, a.e. form: under the same
product-measure bounded-density assumption, almost every ideal point avoids all
coordinate equalities with the current point.

Source status: formalized null-event-to-a.e. bridge for the Lemma 3 hypotheses.
-/
theorem lemma3_coordinate_noncollision_ae_from_productMeasure
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i := by
  exact ae_forall_coordinate_ne_of_productMeasure_boundedDensity ρ hbd x

/--
Structured finite-coordinate C3 bridge: a bounded density with respect to the
full finite-dimensional Lebesgue measure supplies the almost-everywhere
coordinate noncollision condition used by Appendix C.4 Lemma 3.  This is the
C3 condition stated in the paper; it imposes no coordinate-independence
assumption.

Source status: formalized proof-seam target for replacing the abstract C3 field.
-/
theorem c3_bounded_density_coordinate_noncollision_ae
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure, ∀ i, x i ≠ ideal i := by
  exact D.coordinate_noncollision_ae x

/--
Exact source-facing finite-dimensional C3 data: a probability law on ideal
points with a bounded **measurable** density relative to Lebesgue measure.
The measurable witness is displayed here rather than inferred from the
implementation-level bounded-density helper.
-/
def finiteCoordinateIdealDistributionFormulaData
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) : Prop :=
  IsProbabilityMeasure D.idealMeasure ∧
    D.densityBound ≠ ⊤ ∧
      ∃ density : (Coord → ℝ) → ℝ≥0∞,
        Measurable density ∧
          D.idealMeasure = (volume : Measure (Coord → ℝ)).withDensity density ∧
            ∀ᵐ ideal ∂(volume : Measure (Coord → ℝ)), density ideal ≤ D.densityBound

/--
Concrete finite-coordinate C3 density data formula: the sampled ideal
distribution is a probability measure with bounded density with respect to
full finite-dimensional Lebesgue measure.
-/
theorem finite_coordinate_ideal_distribution_data_formula
    {Coord : Type*} [Fintype Coord] :
    Nonempty (FiniteCoordinateIdealDistributionData Coord) ↔
      ∃ idealMeasure : Measure (Coord → ℝ),
        ∃ densityBound : ℝ≥0∞,
          densityBound ≠ ⊤ ∧
            IsProbabilityMeasure idealMeasure ∧
              AppliedModelingLib.Probability.HasBoundedDensity
                (volume : Measure (Coord → ℝ)) idealMeasure densityBound ∧
                ∃ density : (Coord → ℝ) → ℝ≥0∞,
                  Measurable density ∧
                    idealMeasure = (volume : Measure (Coord → ℝ)).withDensity density ∧
                      ∀ᵐ ideal ∂(volume : Measure (Coord → ℝ)), density ideal ≤ densityBound := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.idealMeasure, D.densityBound, D.densityBound_ne_top,
      D.probability, D.hasBoundedDensity, D.density_measurable⟩
  · rintro ⟨idealMeasure, densityBound, hFinite, hProbability, hBoundedDensity,
      hMeasurableDensity⟩
    exact
      ⟨{ idealMeasure := idealMeasure
         probability := hProbability
         densityBound := densityBound
         densityBound_ne_top := hFinite
         hasBoundedDensity := hBoundedDensity
         density_measurable := hMeasurableDensity }⟩

/--
Source-facing finite C3 carrier formula: concrete full-space bounded-density
data are exactly the data used by the finite-coordinate noncollision bridge.
-/
theorem finite_coordinate_c3_carrier_formula
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateC3Carrier E) ↔
      Nonempty (FiniteCoordinateIdealDistributionData Coord) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.data⟩
  · rintro ⟨data⟩
    exact ⟨{ data := data }⟩

/--
Weighted-Euclidean `L2` raw source trace used by Proposition 1 before invoking
the SSGM theorem.  The source supplies the sampled voter stream, the sampled
cost formula, the projected update equation, and sample-subgradient
certificates separately; Lean derives the proof-facing sample-subgradient
recurrence.
-/
theorem weighted_euclidean_l2_ssgm_trace_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2SSGMTraceSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ sampleCost : ℕ → (Coord → ℝ) → ℝ,
            ∃ subgradient : ℕ → Coord → ℝ,
              ∃ noise : ℕ → Coord → ℝ,
                ∃ bias : ℕ → Coord → ℝ,
                  0 < r0 ∧
                    IsNormProjectionOnto E SourceNorm.l2 project ∧
                    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                    (∀ t : ℕ, ∀ x : Coord → ℝ,
                      sampleCost t x = -E.utility (selectedVoter t) x) ∧
                    (∀ t : ℕ,
                      E.trajectory SourceNorm.l2 model (t + 1) =
                        project
                          (fun i =>
                            E.trajectory SourceNorm.l2 model t i -
                              ilvRadius r0 (t + 1) *
                                (subgradient t i + noise t i + bias t i))) ∧
                    (∀ t : ℕ,
                      FiniteSubgradientAt (sampleCost t)
                        (E.trajectory SourceNorm.l2 model t) (subgradient t)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.selectedVoter, S.sampleCost, S.subgradient, S.noise,
      S.bias, S.r0_pos, S.project_norm, S.initial_feasible,
      S.sampleCost_eq_neg_utility, S.projected_update,
      S.sample_subgradient⟩
  · rintro ⟨project, selectedVoter, sampleCost, subgradient, noise, bias, hr0,
      hProject, hInitial, hSampleCost, hUpdate, hSubgradient⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         sampleCost := sampleCost
         subgradient := subgradient
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         sampleCost_eq_neg_utility := hSampleCost
         projected_update := hUpdate
         sample_subgradient := hSubgradient }⟩

/--
Concrete component-distance Proposition 1 trace source.  This is the stricter
source layer used by the full closeout path: each component distance is
identified with a finite `L2` distance to an explicit component ideal, and Lean
derives the weighted sample-subgradient certificate from those component
formulas and nonnegative coefficients.
-/
theorem weighted_euclidean_l2_concrete_component_trace_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2ConcreteComponentTraceSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ componentIdeal : Component → Voter → Coord → ℝ,
            ∃ noise : ℕ → Coord → ℝ,
              ∃ bias : ℕ → Coord → ℝ,
                0 < r0 ∧
                  IsNormProjectionOnto E SourceNorm.l2 project ∧
                  E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components →
                    0 ≤
                      W.weight (selectedVoter t) k /
                        W.weightNorm2 (selectedVoter t)) ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components → ∀ x : Coord → ℝ,
                    W.componentDistance k x (selectedVoter t) =
                      finiteCoordinateDistance SourceNorm.l2 x
                        (componentIdeal k (selectedVoter t))) ∧
                  (∀ t : ℕ, ∀ k, k ∈ W.components → ∀ i : Coord,
                    E.trajectory SourceNorm.l2 model t i ≠
                      componentIdeal k (selectedVoter t) i) ∧
                  (∀ t : ℕ,
                    E.trajectory SourceNorm.l2 model (t + 1) =
                      project
                        (fun i =>
                          E.trajectory SourceNorm.l2 model t i -
                            ilvRadius r0 (t + 1) *
                              (W.components.sum
                                  (fun k =>
                                    (W.weight (selectedVoter t) k /
                                        W.weightNorm2 (selectedVoter t)) *
                                      lpCostGradientCandidate 2
                                        (fun j =>
                                          E.trajectory SourceNorm.l2 model t j -
                                            componentIdeal k
                                              (selectedVoter t) j) i) +
                                noise t i + bias t i))) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.project, S.selectedVoter, S.componentIdeal, S.noise, S.bias,
        S.r0_pos, S.project_norm, S.initial_feasible,
        S.coefficient_nonneg, S.component_distance_eq_l2,
        S.component_noncollision, S.projected_update⟩
  · rintro
      ⟨project, selectedVoter, componentIdeal, noise, bias, hr0,
        hProject, hInitial, hCoefficient, hDistance, hNoncollision,
        hUpdate⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         componentIdeal := componentIdeal
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         coefficient_nonneg := hCoefficient
         component_distance_eq_l2 := hDistance
         component_noncollision := hNoncollision
         projected_update := hUpdate }⟩

/--
Weighted-Euclidean `L2` source recurrence used by Proposition 1 before invoking
the SSGM theorem.  The source keeps the sampled voter stream and sampled cost
formula visible while supplying the projected sample-subgradient recurrence and
positive paper radius; Lean derives the SSGM step-size package and trajectory
feasibility from these fields.
-/
theorem weighted_euclidean_l2_ssgm_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) :
    Nonempty (WeightedEuclideanL2SSGMSource E W model r0) ↔
      ∃ project : (Coord → ℝ) → Coord → ℝ,
        ∃ selectedVoter : ℕ → Voter,
          ∃ sampleCost : ℕ → (Coord → ℝ) → ℝ,
            ∃ subgradient : ℕ → Coord → ℝ,
              ∃ noise : ℕ → Coord → ℝ,
                ∃ bias : ℕ → Coord → ℝ,
                  0 < r0 ∧
                    IsNormProjectionOnto E SourceNorm.l2 project ∧
                    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace ∧
                    (∀ t : ℕ, ∀ x : Coord → ℝ,
                      sampleCost t x = -E.utility (selectedVoter t) x) ∧
                    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
                      (E.trajectory SourceNorm.l2 model) (ilvRadius r0)
                      subgradient noise bias := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.project, S.selectedVoter, S.sampleCost, S.subgradient, S.noise,
      S.bias, S.r0_pos, S.project_norm, S.initial_feasible,
      S.sampleCost_eq_neg_utility, S.follows⟩
  · rintro ⟨project, selectedVoter, sampleCost, subgradient, noise, bias, hr0,
      hProject, hInitial, hSampleCost, hFollows⟩
    exact
      ⟨{ project := project
         selectedVoter := selectedVoter
         sampleCost := sampleCost
         subgradient := subgradient
         noise := noise
         bias := bias
         r0_pos := hr0
         project_norm := hProject
         initial_feasible := hInitial
         sampleCost_eq_neg_utility := hSampleCost
         follows := hFollows }⟩

/--
Weighted-Euclidean Proposition 1 source recurrence keeps all projected iterates
inside the feasible solution space.
-/
theorem weighted_euclidean_l2_ssgm_source_trajectory_feasible
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMSource E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  S.trajectory_mem_solutionSpace

theorem weighted_euclidean_l2_ssgm_trace_source_trajectory_feasible
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMTraceSource E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  (weightedEuclideanL2SSGMSource_of_traceSource S).trajectory_mem_solutionSpace

/--
Proposition 1 source-semantics trajectory feasibility: the finite bridge
constructed from `Proposition1SourceSemantics` keeps the projected `L2`
trajectory inside the solution space for the selected Model A/B branch.
-/
theorem proposition1_source_semantics_trajectory_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace := by
  exact
    proof_proposition1SourceSemantics_trajectory_mem_solutionSpace
      S hC hWeighted model hmodel hResponse

/--
Proposition 1 source-semantics radius consequence: the positive radius bundled
with the weighted `L2` trace source gives the SSGM step-size hypotheses for the
selected Model A/B branch.
-/
theorem proposition1_source_semantics_step_size_conditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {model : VoterResponseModel}
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ∃ r0 : ℝ, SSGMStepSizeConditions (ilvRadius r0) := by
  exact
    proof_proposition1SourceSemantics_stepSizeConditions
      S hC hW hmodel hResponse

/--
Proposition 1 social-optimum source formula: social optima are exactly the
feasible maximizers of societal utility.
-/
theorem weighted_euclidean_social_objective_formula_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) :
    Nonempty (WeightedEuclideanSocialObjectiveFormulaSource E W) ↔
      ∀ x : Coord → ℝ,
        x ∈ E.socialOptimal ↔
          x ∈ E.solutionSpace ∧
            IsMaxOn E.societalUtility E.solutionSpace x := by
  constructor
  · rintro ⟨S⟩
    exact S.mem_socialOptimal_iff_societalUtility_isMaxOn
  · intro h
    exact
      ⟨{ mem_socialOptimal_iff_societalUtility_isMaxOn := h }⟩

/--
Derived Proposition 1 minimization objective: minimizing `-societalUtility` on
the feasible set is equivalent to maximizing societal utility, so the raw
social-optimality formula yields the proof-facing SSGM objective source.
-/
theorem weighted_euclidean_social_objective_source_formula
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (S : WeightedEuclideanSocialObjectiveFormulaSource E W) :
    ∀ x : Coord → ℝ,
      x ∈ E.socialOptimal ↔
        x ∈ E.solutionSpace ∧
          IsMinOn (socialCostObjective E) E.solutionSpace x :=
  (weightedEuclideanSocialObjectiveSource_of_formulaSource S).mem_socialOptimal_iff

/--
Proposition 1 source-semantics objective consequence: the full source semantics
derive the proof-facing minimization target `-societalUtility` whose feasible
minimizers are exactly the paper's social optima.
-/
theorem proposition1_source_semantics_social_objective_minimizer_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] {Component : Type}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hC : ConditionsC123 E)
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    {x : Coord → ℝ} :
    x ∈ E.socialOptimal ↔
      x ∈ E.solutionSpace ∧
        IsMinOn (socialCostObjective E) E.solutionSpace x := by
  exact
    proof_proposition1SourceSemantics_socialObjective_mem_socialOptimal_iff
      S hC hW

/--
Proposition 1 source-semantics finite bridge: the deterministic source
semantics build the weighted finite SSGM bridge for the selected Model A/B
branch.
-/
noncomputable def proposition1_source_semantics_finite_bridge_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    {Component : Type}
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
      Σ' _hWeightedW : IsWeightedEuclideanUtilitiesWith E W,
        Proposition1FiniteSSGMBridge E W model :=
  proof_proposition1SourceSemantics_finite_bridge
    S hC hWeighted model hmodel hResponse

/--
Definition 4: DLCD finite-budget utility formula.

Source status: direct paper-facing Definition 4 finite-budget utility formula row.
-/
noncomputable def dlcdBudgetUtility
    {Dim : Type*} [Fintype Dim]
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) (x : Dim → ℝ) : ℝ :=
  (∑ m : Dim, componentUtility m (x m)) -
    deficitWeight *
      ((∑ m : Dim, if isExpense m then x m else 0) -
        (∑ m : Dim, if isExpense m then 0 else x m))

/--
Source Definition 4 / DLCD: decomposable utility with a linear cost for the
budget deficit.

Source status: direct paper-facing Definition 4 DLCD formula row.
-/
def paper_definition4_dlcd_formula
    {Dim : Type*} [Fintype Dim]
    (utility : (Dim → ℝ) → ℝ)
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) : Prop :=
  0 ≤ deficitWeight ∧
    (∀ m : Dim, ConcaveOn ℝ Set.univ (componentUtility m)) ∧
      ∀ x : Dim → ℝ,
        utility x =
          (∑ m : Dim, componentUtility m (x m)) -
            deficitWeight *
              ((∑ m : Dim, if isExpense m then x m else 0) -
                (∑ m : Dim, if isExpense m then 0 else x m))

/--
Transparent source-facing target for Appendix Theorem 4.  The neighborhood
premise records the source's local finite-valued continuity condition directly;
the conclusion is written as the finite-coordinate subgradient inequality
rather than through a statement alias.
-/
def appendix_theorem4_expected_subgradient_boundarySpec
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta) [IsProbabilityMeasure mu]
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ)
    (hX_nonempty : solutionSpace.Nonempty)
    (hX_bounded : Bornology.IsBounded solutionSpace)
    (hX_closed : IsClosed solutionSpace)
    (hX_convex : Convex ℝ solutionSpace)
    (hx : x ∈ solutionSpace)
    (hcost_integrable :
      ∀ y, y ∈ solutionSpace →
        Integrable (fun theta => sampleCost theta y) mu)
    (hgradient_integrable :
      ∀ i, Integrable (fun theta => sampleGradient theta i) mu)
    (hsample_convex :
      ∀ theta, ConvexOn ℝ solutionSpace (sampleCost theta))
    (hfinite_continuous_neighborhood :
      ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ y,
        dist y x < epsilon →
          Integrable (fun theta => sampleCost theta y) mu ∧
            ContinuousAt (fun z => ∫ theta, sampleCost theta z ∂mu) y)
    (hsample :
      ∀ theta,
        FiniteSubgradientWithinAt
          (sampleCost theta) solutionSpace x (sampleGradient theta)) : Prop :=
  ∀ y, y ∈ solutionSpace →
    (∫ theta, sampleCost theta x ∂mu) +
        AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => ∫ theta, sampleGradient theta i ∂mu)
          (fun i => y i - x i) ≤
      ∫ theta, sampleCost theta y ∂mu

/-- Appendix Theorem 4: expected selected subgradients are subgradients of
the expected objective. -/
theorem appendix_theorem4_expected_subgradient_boundary
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta) [IsProbabilityMeasure mu]
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ)
    (hX_nonempty : solutionSpace.Nonempty)
    (hX_bounded : Bornology.IsBounded solutionSpace)
    (hX_closed : IsClosed solutionSpace)
    (hX_convex : Convex ℝ solutionSpace)
    (hx : x ∈ solutionSpace)
    (hcost_integrable :
      ∀ y, y ∈ solutionSpace →
        Integrable (fun theta => sampleCost theta y) mu)
    (hgradient_integrable :
      ∀ i, Integrable (fun theta => sampleGradient theta i) mu)
    (hsample_convex :
      ∀ theta, ConvexOn ℝ solutionSpace (sampleCost theta))
    (hfinite_continuous_neighborhood :
      ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ y,
        dist y x < epsilon →
          Integrable (fun theta => sampleCost theta y) mu ∧
            ContinuousAt (fun z => ∫ theta, sampleCost theta z ∂mu) y)
    (hsample :
      ∀ theta,
        FiniteSubgradientWithinAt
          (sampleCost theta) solutionSpace x (sampleGradient theta)) :
    appendix_theorem4_expected_subgradient_boundarySpec
      mu solutionSpace sampleCost x sampleGradient hX_nonempty hX_bounded
      hX_closed hX_convex hx hcost_integrable hgradient_integrable
      hsample_convex hfinite_continuous_neighborhood hsample := by
  rcases hfinite_continuous_neighborhood with ⟨epsilon, hepsilon, hlocal⟩
  have hexpected_continuous :
      ContinuousAt (fun y => ∫ theta, sampleCost theta y ∂mu) x :=
    (hlocal x (by simpa using hepsilon)).2
  exact assumption_expected_subgradient_theorem
    mu solutionSpace sampleCost x sampleGradient hX_nonempty hX_bounded
      hX_closed hX_convex hx hcost_integrable hgradient_integrable
      hsample_convex hexpected_continuous hsample

/--
Transparent source-facing target for Appendix Theorem 5.  The source-shaped
hypothesis bundle is paired with the explicit measurability and integrability
data needed to interpret the paper's conditional expectations, and concludes
with the displayed almost-sure convergence proposition.
-/
def appendix_theorem5_ssgm_convergence_boundarySpec
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) : Prop :=
  solutionSpace.Nonempty →
    Bornology.IsBounded solutionSpace →
      IsClosed solutionSpace →
        Convex ℝ solutionSpace →
          ConvexOn ℝ solutionSpace objective →
            xstar ∈ solutionSpace →
              IsMinOn objective solutionSpace xstar →
                (∀ y, y ∈ solutionSpace → objective y = objective xstar → y = xstar) →
                  (∀ t : ℕ, 0 < t → 0 < radius t) →
                    Summable (fun t : ℕ => (radius (t + 1)) ^ 2) →
                      Filter.Tendsto
                        (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1))
                        Filter.atTop Filter.atTop →
                        (∀ y,
                          project y ∈ solutionSpace ∧
                            IsMinOn
                              (fun z => finiteCoordinateDistance SourceNorm.l2 z y)
                              solutionSpace (project y)) →
                          (∀ t, ∀ᵐ omega ∂mu,
                            trajectory (t + 1) omega =
                              project (fun i =>
                                trajectory t omega i -
                                  radius (t + 1) *
                                    (meanSubgradient t omega i + noise t omega i + bias t i))) →
                            (∀ i,
                              StronglyAdapted filtration (fun t omega => trajectory t omega i)) →
                              (∀ i,
                                StronglyAdapted filtration (fun t omega => meanSubgradient t omega i)) →
                                (∀ t, ∀ᵐ omega ∂mu,
                                  trajectory t omega ∈ solutionSpace ∧
                                    FiniteSubgradientWithinAt objective solutionSpace
                                      (trajectory t omega) (meanSubgradient t omega)) →
                                  (∃ C1 : ℝ, 0 ≤ C1 ∧
                                    ∀ y, y ∈ solutionSpace → ∀ g,
                                      FiniteSubgradientWithinAt objective solutionSpace y g →
                                        finiteCoordinateNorm SourceNorm.l2 g ≤ C1) →
                                    (∀ t i, Integrable (fun omega => noise t omega i) mu) →
                                      (∀ t i,
                                        mu[fun omega => noise t omega i | filtration t] =ᵐ[mu] 0) →
                                        (∀ t, Integrable (fun omega =>
                                          finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2) mu) →
                                          (∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ t,
                                            mu[fun omega =>
                                              finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2
                                              | filtration t] ≤ᵐ[mu] fun _ => C2) →
                                            (∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ t,
                                              finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ C3) →
                                              Summable (fun t =>
                                                radius (t + 1) *
                                                  finiteCoordinateNorm SourceNorm.l2 (bias t)) →
                                                StronglyAdapted filtration
                                                  (fun t omega =>
                                                    objective (trajectory t omega) - objective xstar) →
                                                  (∀ t, Integrable
                                                    (fun omega =>
                                                      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
                                                        (fun i => trajectory t omega i - xstar i)) mu) →
                                                    (∀ t, Integrable
                                                      (fun omega =>
                                                        objective (trajectory t omega) - objective xstar) mu) →
                                                      (∀ t i, Integrable
                                                        (fun omega =>
                                                          (trajectory t omega i - xstar i) * noise t omega i) mu) →
                                                        (∃ distanceBound : ℝ, 0 ≤ distanceBound ∧ ∀ t,
                                                          ∀ᵐ omega ∂mu,
                                                            AppliedModelingLib.FiniteDimensionalNorms.l2
                                                              (fun i => trajectory t omega i - xstar i) ≤
                                                                distanceBound) →
                                                          (∀ y, y ∈ solutionSpace → ∃ g,
                                                            FiniteSubgradientWithinAt objective solutionSpace y g) →
                                                            ∀ᵐ omega ∂mu,
                                                              Filter.Tendsto
                                                                (fun t => trajectory t omega)
                                                                Filter.atTop (nhds xstar)

/-- Appendix Theorem 5: source-shaped stochastic-subgradient assumptions,
plus explicit probability-space regularity, imply almost-sure convergence. -/
theorem appendix_theorem5_ssgm_convergence_boundary
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) :
    appendix_theorem5_ssgm_convergence_boundarySpec
      mu filtration solutionSpace objective project trajectory meanSubgradient
      noise bias radius xstar := by
  intro hnonempty hbounded hclosed hconvex hobjective_convex htarget
    htarget_minimizes htarget_unique hstep_pos hstep_sq hstep_diverges
    hclosest_projection hupdate htrajectory_adapted hmean_subgradient_adapted
    htrajectory_subgradient hbounded_subgradients hnoise_coordinate_integrable
    hnoise_mean_zero hnoise_energy_integrable hbounded_noise_energy hbounded_bias
    hstep_bias_summable hobjective_gap_adapted hpotential_integrable
    hobjective_gap_integrable hnoise_product_integrable hdistance hsubgradient_exists
  rcases hdistance with ⟨distanceBound, hdistance_nonneg, hdistance_bound⟩
  let hsource :
      AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
        trajectory meanSubgradient noise bias radius xstar :=
    { solutionSpace_nonempty := hnonempty
      solutionSpace_bounded := hbounded
      solutionSpace_closed := hclosed
      solutionSpace_convex := hconvex
      objective_convex := hobjective_convex
      target_mem_solutionSpace := htarget
      target_minimizes := htarget_minimizes
      target_unique := htarget_unique
      step_sizes := ⟨hstep_pos, hstep_sq, hstep_diverges⟩
      closest_point_projection := hclosest_projection
      update := hupdate
      trajectory_adapted := htrajectory_adapted
      mean_subgradient_adapted := hmean_subgradient_adapted
      trajectory_subgradient := htrajectory_subgradient
      bounded_subgradients := hbounded_subgradients
      noise_coordinate_integrable := hnoise_coordinate_integrable
      noise_mean_zero := hnoise_mean_zero
      noise_energy_integrable := hnoise_energy_integrable
      bounded_noise_energy := hbounded_noise_energy
      bounded_bias := hbounded_bias
      step_bias_summable := hstep_bias_summable }
  let hregular :
      AppendixTheorem5ExecutionRegularity mu filtration solutionSpace objective project
        trajectory meanSubgradient noise bias radius xstar :=
    { objective_gap_adapted := hobjective_gap_adapted
      potential_integrable := hpotential_integrable
      objective_gap_integrable := hobjective_gap_integrable
      noise_product_integrable := hnoise_product_integrable
      distanceBound := distanceBound
      distanceBound_nonneg := hdistance_nonneg
      distance_bound := hdistance_bound
      subgradient_exists := hsubgradient_exists }
  exact hregular.ae_tendsto mu filtration solutionSpace objective project
    trajectory meanSubgradient noise bias radius xstar hsource

/--
Source-faithful adapted-bias reading of Appendix Theorem 5.  The bias and
noise terms remain sample-path processes; regularity only supplies the
measurability needed for their stated conditional expectations and martingale
partial sum.
-/
def appendix_theorem5_adapted_biasSpec
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) : Prop :=
  ∀ (h : AppendixTheorem5AdaptedBiasHypotheses mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5AdaptedBiasRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar),
    ∀ᵐ omega ∂mu, Filter.Tendsto (fun t => trajectory t omega) Filter.atTop (nhds xstar)

/-- The adapted-bias Appendix Theorem 5 endpoint is realized in Lean. -/
theorem appendix_theorem5_adapted_bias
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) :
    appendix_theorem5_adapted_biasSpec mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar := by
  intro h R
  exact R.ae_tendsto mu filtration solutionSpace objective project trajectory
    meanSubgradient noise bias radius xstar h

/--
Corrected set-valued replacement for Appendix Theorem 5.  This is the route
for the main-text branches whose social optimum can be nonunique under C1--C3;
it proves convergence to the minimizer set rather than adding a uniqueness
premise absent from those branches.
-/
theorem appendix_theorem5_minimizer_set_replacement
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ) :
    AppendixTheorem5MinimizerSetStatement mu filtration solutionSpace targetSet
      objective project trajectory meanSubgradient noise bias radius reference := by
  intro hsource hregular
  exact hregular.outcomeIndexed_convergesToSet mu filtration solutionSpace targetSet
    objective project trajectory meanSubgradient noise bias radius reference hsource

/--
Proposition 2 median-set source formula: the paper's median target is the set
of points whose decomposed coordinates lie in the corresponding one-dimensional
median sets.
-/
theorem decomposable_median_set_source_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableMedianSetSource E D) ↔
      ∃ coordinateMedianSet : Coord → Set ℝ,
        ∀ x : Point,
          x ∈ E.medianSet ↔
            ∀ m, m ∈ D.coords →
              D.coordinate m x ∈ coordinateMedianSet m := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.coordinateMedianSet, S.mem_medianSet_iff⟩
  · rintro ⟨coordinateMedianSet, hMedian⟩
    exact
      ⟨{ coordinateMedianSet := coordinateMedianSet
         mem_medianSet_iff := hMedian }⟩

/--
Proof-facing Proposition 2 median carrier formula derived from the median-set
source and decomposable-utility instance.
-/
theorem decomposable_median_carrier_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableMedianCarrier E D) ↔
      IsDecomposableUtilitiesWith E D ∧
        ∃ coordinateMedianSet : Coord → Set ℝ,
          E.medianSet =
            {x | ∀ m, m ∈ D.coords →
              D.coordinate m x ∈ coordinateMedianSet m} := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.decomposable, C.coordinateMedianSet, C.medianSet_formula⟩
  · rintro ⟨hD, coordinateMedianSet, hFormula⟩
    exact
      ⟨{ decomposable := hD
         coordinateMedianSet := coordinateMedianSet
         medianSet_formula := hFormula }⟩

/--
Proposition 2 coordinate-replacement source formula: inside an `L∞` local
query, a feasible one-coordinate value can replace that coordinate of a
response while preserving local feasibility and all other decomposed
coordinates.
-/
theorem decomposable_linf_coordinate_replacement_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableLinfCoordinateReplacement E D) ↔
      ∃ replace : Point → Coord → ℝ → Point,
        (∀ {center response : Point} {r : ℝ} {voter : Voter}
          (_hresponse :
            ModelAResponseAt E SourceNorm.linfty center r voter response)
          {m : Coord} {z : ℝ},
          m ∈ D.coords →
            z ∈ {z | ∃ candidate,
              candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                D.coordinate m candidate = z} →
              replace response m z ∈
                LocalNeighborhood E SourceNorm.linfty center r) ∧
        (∀ (response : Point) {m : Coord} {z : ℝ},
          m ∈ D.coords →
            D.coordinate m (replace response m z) = z) ∧
        (∀ (response : Point) {m : Coord} {z : ℝ} {l : Coord},
          l ∈ D.coords →
            l ≠ m →
              D.coordinate l (replace response m z) =
                D.coordinate l response) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.replace, S.replace_mem_local, S.replace_coordinate_self,
      S.replace_coordinate_other⟩
  · rintro ⟨replace, hMem, hSelf, hOther⟩
    exact
      ⟨{ replace := replace
         replace_mem_local := hMem
         replace_coordinate_self := hSelf
         replace_coordinate_other := hOther }⟩

/--
Proof-facing Proposition 2 local `L∞` response bridge formula: a Model A
maximizer for decomposable utilities is coordinatewise optimal over the
one-dimensional values available in the local query.
-/
theorem decomposable_linf_local_response_bridge_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    Nonempty (DecomposableLinfLocalResponseBridge E D) ↔
      IsDecomposableUtilitiesWith E D ∧
        ∀ {center response : Point} {r : ℝ} {voter : Voter},
          ModelAResponseAt E SourceNorm.linfty center r voter response →
            ∀ m, m ∈ D.coords →
              IsMaxOn
                (fun z : ℝ => D.coordinateUtility m voter z)
                {z | ∃ candidate,
                  candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                    D.coordinate m candidate = z}
                (D.coordinate m response) := by
  constructor
  · rintro ⟨B⟩
    exact ⟨B.decomposable, B.coordinate_response_optimal⟩
  · rintro ⟨hD, hOptimal⟩
    exact
      ⟨{ decomposable := hD
         coordinate_response_optimal := hOptimal }⟩

/--
Finite-coordinate product-box solution-space source formula: replacing one
coordinate of a feasible point by the same coordinate from another feasible
point remains feasible.
-/
theorem finite_coordinate_product_box_solution_space_source_formula
    {Voter Coord : Type*} [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateProductBoxSolutionSpaceSource E) ↔
      ∀ {x y : Coord → ℝ},
        x ∈ E.solutionSpace →
          y ∈ E.solutionSpace →
            ∀ m : Coord, Function.update x m (y m) ∈ E.solutionSpace := by
  constructor
  · rintro ⟨S⟩
    exact S.coordinate_update_mem_solutionSpace
  · intro h
    exact ⟨{ coordinate_update_mem_solutionSpace := h }⟩

/--
Finite-coordinate `L∞` replacement source formula: finite norm semantics,
product-box solution-space closure, and ambient-coordinate projection formulas
are exactly the data used to derive `DecomposableLinfCoordinateReplacement`.
-/
theorem finite_coordinate_linf_coordinate_replacement_source_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (D : DecomposableStructure Voter (Coord → ℝ) Coord) :
    Nonempty (FiniteCoordinateLinfCoordinateReplacementSource E D) ↔
      ∃ hNorm : UsesFiniteCoordinateNormDistance E,
        ∃ productBox : FiniteCoordinateProductBoxSolutionSpaceSource E,
          ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.normDistance, S.productBox, S.coordinate_eq⟩
  · rintro ⟨hNorm, productBox, hCoordinate⟩
    exact
      ⟨{ normDistance := hNorm
         productBox := productBox
         coordinate_eq := hCoordinate }⟩

/--
Finite-coordinate Proposition 2 source semantics: this is the paper-faithful
ambient-coordinate route.  It supplies finite norm semantics, product-box
solution-space closure, and coordinatewise median-set source formulas; Lean
derives the `L∞` coordinate-replacement bridge from those fields for any
decomposition whose coordinates are the ambient coordinate projections.
-/
theorem proposition2_finite_coordinate_source_semantics_formula
    {Voter Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition2FiniteCoordinateSourceSemantics E) ↔
      ∃ hNorm : UsesFiniteCoordinateNormDistance E,
        ∃ productBox : FiniteCoordinateProductBoxSolutionSpaceSource E,
          ∃ hMedian :
            (∀ {D : DecomposableStructure Voter (Coord → ℝ) Coord},
              ConditionsC123 E →
                IsDecomposableUtilitiesWith E D →
                  DecomposableMedianSetSource E D),
            True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.normDistance, S.productBox, S.medianSetSource, trivial⟩
  · rintro ⟨hNorm, productBox, hMedian, _⟩
    exact
      ⟨{ normDistance := hNorm
         productBox := productBox
         medianSetSource := hMedian }⟩

/--
Proposition 2 source-semantics case certificate: the deterministic source
semantics build the structured decomposable/median `L∞` case certificate for
the selected decomposition and Model A/B branch.
-/
noncomputable def proposition2_source_semantics_case_certificate_formula
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    {Coord : Type}
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    Σ D : DecomposableStructure Voter Point Coord,
      Proposition2SSGMCaseCertificate E D model :=
  proof_proposition2SourceSemantics_case_certificate
    S hC hDecomposable model hmodel hResponse

/--
Concrete finite-coordinate normalized-gradient field model used by Theorem 3.
This expands the source-semantics record so the field formula is not hidden
behind the record name.
-/
theorem theorem3_finite_directional_field_model_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteTheorem3DirectionalFieldModel E) ↔
      ∃ weight : Voter → ℝ,
        (∀ voter, 0 ≤ weight voter) ∧
          (∑ voter : Voter, weight voter) = 1 ∧
            ∃ utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ,
              E.utilityGradient = utilityGradient ∧
                E.scalarDirection = finiteScalarDirection ∧
                  E.voterExpectation = finiteVoterExpectation weight ∧
                    E.directionalField =
                      finiteTheorem3DirectionalField weight utilityGradient ∧
                      E.zeroDirection = (fun _ : Coord => (0 : ℝ)) ∧
                        (∀ g : Coord → ℝ,
                          E.normDistance SourceNorm.l2 g E.zeroDirection =
                            finiteCoordinateNorm SourceNorm.l2 g) := by
  constructor
  · rintro ⟨M⟩
    exact
      ⟨M.weight, M.weight_nonneg, M.weight_sum, M.utilityGradient,
        M.utilityGradient_eq, M.scalarDirection_eq, M.voterExpectation_eq,
        M.directionalField_eq, M.zeroDirection_eq, M.normDistance_l2_zero_eq⟩
  · rintro
      ⟨weight, hweight_nonneg, hweight_sum, utilityGradient,
        hUtilityGradient, hScalarDirection, hVoterExpectation,
        hDirectionalField, hZeroDirection, hNormDistance⟩
    exact
      ⟨{ weight := weight
         weight_nonneg := hweight_nonneg
         weight_sum := hweight_sum
         utilityGradient := utilityGradient
         utilityGradient_eq := hUtilityGradient
         scalarDirection_eq := hScalarDirection
         voterExpectation_eq := hVoterExpectation
         directionalField_eq := hDirectionalField
         zeroDirection_eq := hZeroDirection
         normDistance_l2_zero_eq := hNormDistance }⟩

/--
Theorem 3's source-facing population field.  Unlike the legacy finite-support
helper above, this is the literal measure/population reading of the paper's
expectation `E_v`.  Every coordinate integral is required to be integrable,
and the zero-gradient contribution is explicitly zero.
-/
theorem theorem3_population_directional_field_model_formula
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (PopulationTheorem3DirectionalFieldModel E) ↔
      ∃ population : Measure Voter,
        IsProbabilityMeasure population ∧
          ∃ utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ,
            E.utilityGradient = utilityGradient ∧
              (∀ voter x,
                FiniteSourceSubgradientAt (E.utility voter) x
                  (utilityGradient voter x)) ∧
                E.scalarDirection = finiteScalarDirection ∧
                  E.zeroDirection = (fun _ : Coord => (0 : ℝ)) ∧
                    (∀ g : Coord → ℝ,
                      E.normDistance SourceNorm.l2 g E.zeroDirection =
                        finiteCoordinateNorm SourceNorm.l2 g) ∧
                      (∀ x i,
                        Integrable
                          (fun voter =>
                            modelBFiniteNormalizedDirection SourceNorm.l2
                              (utilityGradient voter x) i)
                          population) ∧
                        E.directionalField =
                          populationTheorem3DirectionalField
                            population utilityGradient ∧
                          (∀ x,
                            E.voterExpectation
                                (fun voter =>
                                  theorem3NormalizedGradientDirection E voter x) =
                              populationTheorem3DirectionalField
                                population utilityGradient x) := by
  constructor
  · rintro ⟨M⟩
    exact
      ⟨M.population, M.population_probability, M.utilityGradient,
        M.utilityGradient_eq, M.utilityGradient_source_subgradient,
        M.scalarDirection_eq, M.zeroDirection_eq,
        M.normDistance_l2_zero_eq, M.normalized_gradient_integrable,
        M.directionalField_eq, M.voterExpectation_normalized_eq⟩
  · rintro
      ⟨population, hprobability, utilityGradient, hUtilityGradient, hSubgradient,
        hScalarDirection, hZeroDirection, hNormDistance, hIntegrable,
        hDirectionalField, hExpectation⟩
    exact
      ⟨{ population := population
         population_probability := hprobability
         utilityGradient := utilityGradient
         utilityGradient_eq := hUtilityGradient
         utilityGradient_source_subgradient := hSubgradient
         scalarDirection_eq := hScalarDirection
         zeroDirection_eq := hZeroDirection
         normDistance_l2_zero_eq := hNormDistance
         normalized_gradient_integrable := hIntegrable
         directionalField_eq := hDirectionalField
         voterExpectation_normalized_eq := hExpectation }⟩

/--
Transparent source view of the general-population iid trace used for Theorem
3.  At time `n`, the state is a function of the finite history through `n`;
the update then uses the independent `(n+1)`st population draw.  The remaining
analytic clauses make explicit the standard probability well-definedness
implicit in that iid, probability-one source formulation: the displayed
recursion is measurable, adapted, and integrable enough for its conditional
expectations.  In particular, no martingale conclusion is listed as a source
premise.
-/
theorem theorem3_population_iid_trace_source_formula
    {Voter Coord : Type*} [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) :
    Nonempty (PopulationTheorem3IidTraceSource M) ↔
      ∃ initial : Coord → ℝ,
        ∃ trajectory : ℕ → (ℕ → Voter) → Coord → ℝ,
          ∃ state : ∀ n, (Fin (n + 1) → Voter) → Coord → ℝ,
            ∃ r0 : ℝ,
              0 < r0 ∧
                E.solutionSpace = Set.univ ∧
                  PopulationTheorem3DirectionalFieldUniformContinuity M ∧
                    (∀ omega, trajectory 0 omega = initial) ∧
                    (∀ n omega,
                        trajectory n omega = state n (iidSequencePastPrefix n omega)) ∧
                        (∀ n omega,
                          trajectory (n + 1) omega =
                            fun i => trajectory n omega i +
                              ilvRadius r0 (n + 1) *
                                modelBFiniteNormalizedDirection SourceNorm.l2
                                  (M.utilityGradient (iidSequenceSample n omega)
                                    (trajectory n omega)) i) ∧
                        (∀ (a : Coord → ℝ) n,
                          Integrable (fun z : (Fin (n + 1) → Voter) × Voter =>
                            populationTheorem3PastCenteredTest M
                              (ilvRadius r0 (n + 1)) a (state n z.1) z.2)
                            (Measure.map (fun omega =>
                              (iidSequencePastPrefix n omega, iidSequenceSample n omega))
                              (iidSequenceMeasure M.population))) ∧
                          (∀ a : Coord → ℝ,
                            StronglyAdapted (iidSequenceNaturalFiltration (α := Voter))
                              (fun n omega => ∑ i ∈ Finset.range n,
                                populationTheorem3CenteredIncrement M r0 trajectory
                                  iidSequenceSample a i omega)) ∧
                            (∀ (a : Coord → ℝ) (n : ℕ),
                              AEStronglyMeasurable
                                (populationTheorem3CenteredIncrement M r0 trajectory
                                  iidSequenceSample a n)
                                (iidSequenceMeasure M.population)) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.initial, S.trajectory, S.state, S.r0, S.r0_pos,
      S.solutionSpace_univ, S.field_continuity, S.initial_eq, S.trajectory_from_past,
      S.raw_update,
      S.centered_test_integrable, S.centered_partial_sum_adapted,
      S.centered_aestronglyMeasurable⟩
  · rintro ⟨initial, trajectory, state, r0, hr0, hfullspace, hcontinuity,
      hinitial, hpast, hupdate, hintegrable, hadapted, hmeasurable⟩
    exact
      ⟨{ initial := initial
         trajectory := trajectory
         state := state
         r0 := r0
         r0_pos := hr0
         solutionSpace_univ := hfullspace
         field_continuity := hcontinuity
         initial_eq := hinitial
         trajectory_from_past := hpast
         raw_update := hupdate
         centered_test_integrable := hintegrable
         centered_partial_sum_adapted := hadapted
         centered_aestronglyMeasurable := hmeasurable }⟩

/--
Theorem 3 finite-dot expectation identity: averaging raw Model B increments
against finite voter weights gives the radius times the finite-dot product with
the concrete normalized-gradient field.
-/
theorem theorem3_expected_finiteDot_modelB_response_increment_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    {x : Coord → ℝ} {response : Voter → Coord → ℝ}
    (a : Coord → ℝ) (r : ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 x r
          (utilityGradient voter x) (response voter)) :
    (∑ voter : Voter,
      weight voter * finiteDot a (fun i => response voter i - x i)) =
      r * finiteDot a
        (finiteTheorem3DirectionalField weight utilityGradient x) :=
  finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment
    weight utilityGradient a r hresponse

/--
Theorem 3 accumulated finite-dot expectation identity over a finite prefix of
the projected-trace tail.
-/
theorem theorem3_expected_finiteDot_modelB_response_increment_sum_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (a : Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter)) :
    ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response t voter i - center t i)) =
        ∑ t ∈ Finset.range n,
          radius t *
            finiteDot a
              (finiteTheorem3DirectionalField weight utilityGradient
                (center t)) :=
  finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
    weight utilityGradient center radius response a hresponse

/--
Projection residual feasibility used by the corrected Theorem 3 route: some
positive step in the fixed direction remains feasible from the projected point.
-/
theorem theorem3_feasible_direction_at_formula
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (point direction : Coord → ℝ) :
    FiniteFeasibleDirectionAt X point direction ↔
      ∃ η : ℝ, 0 < η ∧ (fun i => point i + η * direction i) ∈ X := by
  rfl

/--
Theorem 3 projection geometry: an `L2` nearest-point projection onto a convex
solution set satisfies the finite normal-cone inequality used by the projection
residual argument.
-/
theorem theorem3_l2_projection_normal_cone_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectionNormalConeAt E.solutionSpace raw next :=
  finiteProjectionNormalConeAt_of_l2_normProjection
    hNorm hconv hproject hupdate

/--
Theorem 3 projection residual geometry: if a direction is feasible from the
projected point, then its finite-dot product with the projection residual is
nonpositive.
-/
theorem theorem3_projection_residual_nonpos_formula
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : FiniteFeasibleDirectionAt X next direction) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 :=
  finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
    hnormal hfeasible

/--
Theorem 3 projection progress inequality: for a raw step
`previous + r * direction`, the squared projected movement divided by `r` is
bounded by the finite-dot progress in that direction.
-/
theorem theorem3_projection_step_progress_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ}
    {previous raw next direction : Coord → ℝ} {r : ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hr : 0 < r)
    (hraw : raw = fun i => previous i + r * direction i)
    (hprevious : previous ∈ E.solutionSpace) :
    (1 / r) *
        finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
      finiteDot direction (fun i => next i - previous i) :=
  finiteDot_step_progress_of_l2_normProjection
    hNorm hconv hproject hupdate hr hraw hprevious

/--
Theorem 3 selected-voter concentration: for iid voters drawn from the finite
weighted voter law, the realized finite-dot raw Model B increments are
eventually within a finite concentration bound of their weighted expectation,
using the corrected global-tail Algorithm 1 radii.
-/
theorem theorem3_iid_weighted_voter_global_concentration_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (G : FiniteTheorem3DirectionalFieldModel E)
    (hweight_nonneg : ∀ voter, 0 ≤ G.weight voter)
    (hweight_sum : (∑ voter : Voter, G.weight voter) = 1)
    {r0 : ℝ} (hr0 : 0 < r0)
    (xstar : Coord → ℝ) (N : ℕ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
          (ilvTailRadius r0 N t)
          (G.utilityGradient voter
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
          (response t voter)) :
    ∀ᵐ sampledVoter
        ∂theorem3FiniteWeightedVoterSequenceMeasure
          G.weight hweight_nonneg hweight_sum,
      ∃ concentrationBound : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n,
            ∑ voter : Voter,
              G.weight voter *
                finiteDot
                  (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                  (fun i =>
                    response t voter i -
                      E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                        (t + N) i)) -
            concentrationBound ≤
          theorem3ConcreteFiniteFieldProjection G xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField G.weight G.utilityGradient xstar)
                (fun i =>
                  response t (sampledVoter t) i -
                    E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                      (t + N) i) :=
  proof_theorem3_finiteDot_projectedTrace_global_concentration_ae_of_iid_weightedVoter
    G hweight_nonneg hweight_sum hr0 xstar N response hresponse

/--
Almost-sure global projected Algorithm 1 trace skeleton used by the corrected
Theorem 3 route.  This spells out the remaining source-semantics data: global
tail radii, concrete Model B responses for all voters, almost-sure selected raw
responses for the sampled voter stream, finite `L2` projection, projected
updates into the environment trajectory, and positive-step feasibility of the
fixed `G(x*)` direction after each projected point.
-/
theorem theorem3_global_projected_trace_ae_skeleton_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              ModelBFiniteResponseAt SourceNorm.l2
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N))
                                (ilvTailRadius r0 N t)
                                (M.utilityGradient voter
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))
                                (response t voter)) ∧
                            ∀ᵐ sampledVoter
                                ∂theorem3FiniteWeightedVoterSequenceMeasure
                                  M.weight M.weight_nonneg M.weight_sum,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                Convex ℝ E.solutionSpace ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity, S.ae_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hAETrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         ae_projected_trace := hAETrace }⟩

/--
Theorem 3 concrete field continuity source: the abstract paper continuity
assumption gives coordinatewise continuity of the concrete finite normalized
gradient field.
-/
theorem theorem3_field_coordinate_continuity_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3ConcreteFieldContinuitySource M) ↔
      (E.directionalFieldUniformlyContinuous →
        ∀ xstar i ε, 0 < ε →
          ∃ δ, 0 < δ ∧
            ∀ x : Coord → ℝ,
              finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                  finiteTheorem3DirectionalField M.weight
                    M.utilityGradient xstar i| < ε) := by
  constructor
  · rintro ⟨S⟩
    exact S.coordinate_continuity
  · intro h
    exact ⟨{ coordinate_continuity := h }⟩

/--
Primitive global projected Algorithm 1 trace generator for the corrected
Theorem 3 route.  This is the granular source record used by the full closeout
path: it exposes finite `L2` norm semantics, a sampled-stream-dependent
projection operator, projected global-tail Algorithm 1 updates, and the
positive-step feasibility of the fixed `G(x*)` direction from each projected
tail iterate.
-/
theorem theorem3_global_projected_algorithm1_trace_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          ∃ hNorm : UsesFiniteCoordinateNormDistance E,
            ∃ project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ,
              (∀ sampledVoter : ℕ → Voter,
                IsNormProjectionOnto E SourceNorm.l2
                  (project sampledVoter)) ∧
              (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
                ConditionsC123 E →
                  E.directionalFieldUniformlyContinuous →
                    E.respondsAccordingTo VoterResponseModel.modelB →
                      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                        VoterResponseModel.modelB xstar →
                        (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                          0 < c →
                            (∀ n : ℕ,
                              c ≤
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (n + N)))) →
                              ∀ sampledVoter : ℕ → Voter,
                                ∀ t : ℕ,
                                  Algorithm1ProjectedUpdate
                                    (project sampledVoter)
                                    (fun i =>
                                      E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB
                                          (t + N) i +
                                        ilvTailRadius r0 N t *
                                          (modelBFiniteNormalizedDirection SourceNorm.l2
                                            (M.utilityGradient (sampledVoter t)
                                              (E.trajectory SourceNorm.l2
                                                VoterResponseModel.modelB
                                                (t + N))) i))
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
              (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
                ConditionsC123 E →
                  E.directionalFieldUniformlyContinuous →
                    E.respondsAccordingTo VoterResponseModel.modelB →
                      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                        VoterResponseModel.modelB xstar →
                        (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                          0 < c →
                            (∀ n : ℕ,
                              c ≤
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (n + N)))) →
                              ∀ sampledVoter : ℕ → Voter,
                                ∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.r0_pos, S.normDistance, S.project, S.project_norm,
        S.projected_update, S.feasible_direction⟩
  · rintro
      ⟨r0, hr0, hNorm, project, hProjectNorm, hProjectedUpdate,
        hFeasibleDirection⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         normDistance := hNorm
         project := project
         project_norm := hProjectNorm
         projected_update := hProjectedUpdate
         feasible_direction := hFeasibleDirection }⟩

/--
Stricter primitive global projected Algorithm 1 trace generator for Theorem 3:
the aggregate `G(x*)` feasibility field is no longer primitive.  It is derived
from a common positive step that keeps every per-voter normalized-gradient move
inside the solution space, plus convexity of `X`.
-/
theorem theorem3_global_projected_algorithm1_update_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty (FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          ∃ hNorm : UsesFiniteCoordinateNormDistance E,
            ∃ project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ,
              (∀ sampledVoter : ℕ → Voter,
                IsNormProjectionOnto E SourceNorm.l2
                  (project sampledVoter)) ∧
              (∀ {N : ℕ},
                ∀ sampledVoter : ℕ → Voter,
                  ∀ t : ℕ,
                    Algorithm1ProjectedUpdate
                      (project sampledVoter)
                      (fun i =>
                        E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB
                            (t + N) i +
                          ilvTailRadius r0 N t *
                            (modelBFiniteNormalizedDirection SourceNorm.l2
                              (M.utilityGradient (sampledVoter t)
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB
                                  (t + N))) i))
                      (E.trajectory SourceNorm.l2
                        VoterResponseModel.modelB
                        (t + 1 + N))) := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.r0_pos, S.normDistance, S.project, S.project_norm,
        S.projected_update⟩
  · rintro ⟨r0, hr0, hNorm, project, hProjectNorm, hProjectedUpdate⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         normDistance := hNorm
         project := project
         project_norm := hProjectNorm
         projected_update := hProjectedUpdate }⟩

/--
Record-free aggregate feasible-direction formula for the projected Theorem 3
residual argument.  The final no-hidden-premise closeout states that, in the
general constrained case, this formula may fail; it is not taken as a source
record premise.
-/
theorem theorem3_aggregate_feasible_direction_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    FiniteTheorem3AggregateFeasibleDirectionFormula M ↔
      ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
        ConditionsC123 E →
          E.directionalFieldUniformlyContinuous →
            E.respondsAccordingTo VoterResponseModel.modelB →
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                (finiteTheorem3DirectionalField M.weight
                    M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                  0 < c →
                    (∀ n : ℕ,
                      c ≤
                        finiteDot
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar)
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N)))) →
                      ∀ t : ℕ,
                        FiniteFeasibleDirectionAt E.solutionSpace
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar) := by
  rfl

/--
Trace-only deterministic global projected Algorithm 1 source for the corrected
Theorem 3 route.  Field continuity is deliberately not part of this source; it
is supplied by `FiniteTheorem3ConcreteFieldContinuitySource`.
-/
theorem theorem3_global_projected_trace_deterministic_trace_core_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              response t voter =
                                fun i =>
                                  E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + N) i +
                                    ilvTailRadius r0 N t *
                                      (modelBFiniteNormalizedDirection SourceNorm.l2
                                        (M.utilityGradient voter
                                          (E.trajectory SourceNorm.l2
                                            VoterResponseModel.modelB
                                            (t + N))) i)) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         deterministic_projected_trace := hTrace }⟩

/--
Raw deterministic global projected Algorithm 1 trace source for the corrected
Theorem 3 route.  This contains the pointwise sampled-voter trace alignment;
the C1 convexity interpretation is supplied separately by the full source model
and then combined into the proof-facing deterministic skeleton.
-/
theorem theorem3_global_projected_trace_deterministic_trace_source_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              response t voter =
                                fun i =>
                                  E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + N) i +
                                    ilvTailRadius r0 N t *
                                      (modelBFiniteNormalizedDirection SourceNorm.l2
                                        (M.utilityGradient voter
                                          (E.trajectory SourceNorm.l2
                                            VoterResponseModel.modelB
                                            (t + N))) i)) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity,
      S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         deterministic_projected_trace := hTrace }⟩

/--
Proof-facing deterministic global projected Algorithm 1 trace skeleton for the
corrected Theorem 3 route.  It combines the raw pointwise trace source with the
C1 convexity interpretation needed by the projection residual argument.
-/
theorem theorem3_global_projected_trace_deterministic_skeleton_formula
    {Voter Coord : Type*} [Fintype Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Nonempty
        (FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
          M) ↔
      ∃ r0 : ℝ,
        0 < r0 ∧
          (E.directionalFieldUniformlyContinuous →
            ∀ xstar i ε, 0 < ε →
              ∃ δ, 0 < δ ∧
                ∀ x : Coord → ℝ,
                  finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
                    |finiteTheorem3DirectionalField M.weight
                        M.utilityGradient x i -
                      finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar i| < ε) ∧
          (ConditionsC123 E → Convex ℝ E.solutionSpace) ∧
          (∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
            ConditionsC123 E →
              E.directionalFieldUniformlyContinuous →
                E.respondsAccordingTo VoterResponseModel.modelB →
                  FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar ≠ fun _ => (0 : ℝ)) →
                      0 < c →
                        (∀ n : ℕ,
                          c ≤
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (n + N)))) →
                          ∃ response : ℕ → Voter → Coord → ℝ,
                            (∀ t voter,
                              ModelBFiniteResponseAt SourceNorm.l2
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N))
                                (ilvTailRadius r0 N t)
                                (M.utilityGradient voter
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))
                                (response t voter)) ∧
                            ∀ sampledVoter : ℕ → Voter,
                              ∃ raw : ℕ → Coord → ℝ,
                              ∃ project : (Coord → ℝ) → Coord → ℝ,
                                UsesFiniteCoordinateNormDistance E ∧
                                IsNormProjectionOnto E SourceNorm.l2 project ∧
                                (∀ t : ℕ,
                                  raw t = response t (sampledVoter t)) ∧
                                (∀ t : ℕ,
                                  Algorithm1ProjectedUpdate project (raw t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))) ∧
                                (∀ t : ℕ,
                                  FiniteFeasibleDirectionAt E.solutionSpace
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB
                                      (t + 1 + N))
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar))) := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.r0, S.r0_pos, S.coordinate_continuity,
      S.convex_solutionSpace, S.deterministic_projected_trace⟩
  · rintro ⟨r0, hr0, hCoordinateContinuity, hConvex, hTrace⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         coordinate_continuity := hCoordinateContinuity
         convex_solutionSpace := hConvex
         deterministic_projected_trace := hTrace }⟩

/--
Finite-coordinate reading of the abstract trajectory-convergence predicate used
by the exact Theorem 3 statement adapter.
-/
theorem finite_coordinate_convergence_source_formula
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateConvergenceSource E) ↔
      ∀ {q : SourceNorm} {model : VoterResponseModel} {xstar : Coord → ℝ},
        ILVTrajectoryConvergesTo E q model xstar →
          FiniteCoordinateILVTrajectoryConvergesTo E q model xstar := by
  constructor
  · rintro ⟨S⟩
    exact S.finite_coordinate_of_ilv_converges
  · intro h
    exact ⟨{ finite_coordinate_of_ilv_converges := h }⟩

/--
Sampled projected full finite-coordinate source semantics used by the
no-hidden-premise closeout route.  Theorem 2 and Proposition 1 enter through
sampled-process records whose marginal-law/bad-event fields derive deterministic
noncollision internally.  Theorem 3 includes projected Algorithm 1 update
semantics but deliberately does not assume aggregate feasibility.
-/
theorem finite_coordinate_full_sampled_projected_source_semantics_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateILVFullSampledProjectedSourceSemantics E) ↔
      ∃ theorem2 : Theorem2SampledSourceSemantics E,
        ∃ proposition1 : Proposition1ConcreteComponentSampledSourceSemantics E,
          ∃ proposition2 : Proposition2SourceSemantics E,
            ∃ field : FiniteTheorem3DirectionalFieldModel E,
              ∃ hConvex : C1ConvexSolutionSpaceSource E,
                ∃ hConvergence : FiniteCoordinateConvergenceSource E,
                  ∃ hContinuity :
                    FiniteTheorem3ConcreteFieldContinuitySource field,
                    Nonempty
                      (FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource
                        field) := by
  constructor
  · rintro ⟨M⟩
    exact
      ⟨M.theorem2_source, M.proposition1_source,
        M.proposition2_source, M.theorem3_field,
        M.theorem3_convex_solutionSpace, M.theorem3_convergence,
        M.theorem3_continuity, ⟨M.theorem3_algorithm1_update⟩⟩
  · rintro
      ⟨theorem2, proposition1, proposition2, field, hConvex,
        hConvergence, hContinuity, ⟨algorithm1Update⟩⟩
    exact
      ⟨{ theorem2_source := theorem2
         proposition1_source := proposition1
         proposition2_source := proposition2
         theorem3_field := field
         theorem3_convex_solutionSpace := hConvex
         theorem3_convergence := hConvergence
         theorem3_continuity := hContinuity
         theorem3_algorithm1_update := algorithm1Update }⟩

/-- The C1 convexity premise used by the finite-coordinate Theorem 3 route. -/
def c1ConvexSolutionSpaceSourceFormula
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : C1ConvexSolutionSpaceSource E) : Prop :=
  Convex ℝ E.solutionSpace

/--
The finite directional-field data used by Theorem 3, written as one bounded
semantic prerequisite rather than a record name.
-/
def finiteTheorem3DirectionalFieldModelFormula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) : Prop :=
  (∀ voter, 0 ≤ M.weight voter) ∧
    (∑ voter : Voter, M.weight voter) = 1 ∧
      E.utilityGradient = M.utilityGradient ∧
        E.scalarDirection = finiteScalarDirection ∧
          E.voterExpectation = finiteVoterExpectation M.weight ∧
            E.directionalField =
              finiteTheorem3DirectionalField M.weight M.utilityGradient ∧
              (E.zeroDirection = fun _ => (0 : ℝ)) ∧
                ∀ gradient : Coord → ℝ,
                  E.normDistance SourceNorm.l2 gradient E.zeroDirection =
                    finiteCoordinateNorm SourceNorm.l2 gradient

/-- The concrete coordinatewise convergence reading used by Theorem 3. -/
def finiteCoordinateConvergenceSourceFormula
    {Voter Coord : Type*}
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C : FiniteCoordinateConvergenceSource E) : Prop :=
  ∀ {q : SourceNorm} {model : VoterResponseModel} {xstar : Coord → ℝ},
    ILVTrajectoryConvergesTo E q model xstar →
      ∀ coordinate : Coord,
        Filter.Tendsto
          (fun n : ℕ => E.trajectory q model n coordinate)
          Filter.atTop (nhds (xstar coordinate))

/-- The displayed uniform-continuity reading for the finite Theorem 3 field. -/
def finiteTheorem3ConcreteFieldContinuitySourceFormula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (C : FiniteTheorem3ConcreteFieldContinuitySource M) : Prop :=
  E.directionalFieldUniformlyContinuous →
    ∀ xstar coordinate epsilon, 0 < epsilon →
      ∃ delta, 0 < delta ∧
        ∀ x : Coord → ℝ,
          finiteCoordinateDistance SourceNorm.l2 x xstar < delta →
            |finiteTheorem3DirectionalField M.weight M.utilityGradient x coordinate -
              finiteTheorem3DirectionalField M.weight M.utilityGradient
                xstar coordinate| < epsilon

/--
The projected Algorithm 1 update source used by the finite Theorem 3 route.
It exposes the full normalized selected-voter update and its projection.
-/
def finiteTheorem3GlobalProjectedAlgorithm1UpdateSourceFormula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (A : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M) : Prop :=
  0 < A.r0 ∧
    UsesFiniteCoordinateNormDistance E ∧
      (∀ sampledVoter : ℕ → Voter,
        IsNormProjectionOnto E SourceNorm.l2 (A.project sampledVoter)) ∧
        ∀ {N : ℕ} (sampledVoter : ℕ → Voter) (t : ℕ),
          Algorithm1ProjectedUpdate (A.project sampledVoter)
            (fun coordinate =>
              E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N) coordinate +
                ilvTailRadius A.r0 N t *
                  modelBFiniteNormalizedDirection SourceNorm.l2
                    (M.utilityGradient (sampledVoter t)
                      (E.trajectory SourceNorm.l2
                        VoterResponseModel.modelB (t + N))) coordinate)
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))

/--
Theorem 3's narrow sampled/projected source package, displayed without the
unrelated Theorem 2 and Proposition 1 records.  It contains exactly the
finite directional-field realization, C1 convexity, the source convergence
reading, field-continuity reading, and the projected Algorithm 1 update used
by the two-part Theorem 3 endpoint.
-/
theorem finite_coordinate_theorem3_sampled_projected_source_semantics_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (FiniteCoordinateTheorem3SampledProjectedSourceSemantics E) ↔
      ∃ field : FiniteTheorem3DirectionalFieldModel E,
        ∃ hConvex : C1ConvexSolutionSpaceSource E,
          ∃ hConvergence : FiniteCoordinateConvergenceSource E,
            ∃ hContinuity : FiniteTheorem3ConcreteFieldContinuitySource field,
              Nonempty (FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource field) := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.theorem3_field, M.theorem3_convex_solutionSpace,
      M.theorem3_convergence, M.theorem3_continuity, ⟨M.theorem3_algorithm1_update⟩⟩
  · rintro ⟨field, hConvex, hConvergence, hContinuity, ⟨algorithm1Update⟩⟩
    exact
      ⟨{ theorem3_field := field
         theorem3_convex_solutionSpace := hConvex
         theorem3_convergence := hConvergence
         theorem3_continuity := hContinuity
         theorem3_algorithm1_update := algorithm1Update }⟩

/--
Theorem 2 source-semantics interface: exact expansion of the deterministic
non-SSGM data still needed before invoking the SSGM convergence theorem.  The
trace source includes a selected-voter stream, so the sampled ideal used in the
finite `Lp` cost is `E.ideal (voter t)`.
-/
theorem theorem2_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Theorem2PrimitiveSourceSemantics E) ↔
      ∃ r0 : ℝ,
        ∃ hNorm : UsesFiniteCoordinateNormDistance E,
          ∃ c3Data : FiniteCoordinateIdealDistributionData Coord,
            ∃ hTrace :
              (∀ {p q : ℝ},
                IsLpNormedUtilities E (SourceNorm.lp p) →
                  E.respondsAccordingTo VoterResponseModel.modelB →
                    HolderDualFinite p q →
                      FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0),
              0 < r0 := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.r0, S.hNorm, S.c3Data, S.modelB_primitive_trace, S.r0_pos⟩
  · rintro ⟨r0, hNorm, c3Data, hTrace, hr0⟩
    exact
      ⟨{ r0 := r0
         r0_pos := hr0
         hNorm := hNorm
         c3Data := c3Data
         modelB_primitive_trace := hTrace }⟩

/--
Proposition 1 concrete component source-semantics interface: exact expansion of
the deterministic weighted-Euclidean component-distance trace data and
social-objective source data.  The older `Proposition1SourceSemantics`
weighted-`L2` input is derived from this row by first deriving component
subgradients and then summing them with the nonnegative source coefficients.
-/
theorem proposition1_concrete_component_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition1ConcreteComponentSourceSemantics E) ↔
      ∃ hWeightedInputs :
        (∀ {Component : Type}
          {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
          {model : VoterResponseModel},
          ConditionsC123 E →
            IsWeightedEuclideanUtilitiesWith E W →
              (model = VoterResponseModel.modelA ∨
                  model = VoterResponseModel.modelB) →
                  E.respondsAccordingTo model →
                    Σ r0 : ℝ,
                      WeightedEuclideanL2ConcreteComponentTraceSource
                        E W model r0),
        ∃ hWeightedObjective :
          (∀ {Component : Type}
            {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
            ConditionsC123 E →
              IsWeightedEuclideanUtilitiesWith E W →
                WeightedEuclideanSocialObjectiveFormulaSource E W),
          True := by
  constructor
  · rintro ⟨S⟩
    exact
      ⟨S.weighted_l2_concrete_component_inputs, S.weighted_objective,
        trivial⟩
  · rintro ⟨hWeightedInputs, hWeightedObjective, _⟩
    exact
      ⟨{ weighted_l2_concrete_component_inputs := hWeightedInputs
         weighted_objective := hWeightedObjective }⟩

/--
Proposition 1 source-semantics interface: exact expansion of the deterministic
weighted-Euclidean SSGM-input and social-objective source data.
-/
theorem proposition1_source_semantics_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) :
    Nonempty (Proposition1SourceSemantics E) ↔
      ∃ hWeightedInputs :
        (∀ {Component : Type}
          {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
          {model : VoterResponseModel},
          ConditionsC123 E →
            IsWeightedEuclideanUtilitiesWith E W →
              (model = VoterResponseModel.modelA ∨
                  model = VoterResponseModel.modelB) →
                  E.respondsAccordingTo model →
                    Σ r0 : ℝ, WeightedEuclideanL2SSGMTraceSource E W model r0),
        ∃ hWeightedObjective :
          (∀ {Component : Type}
            {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
            ConditionsC123 E →
              IsWeightedEuclideanUtilitiesWith E W →
                WeightedEuclideanSocialObjectiveFormulaSource E W),
          True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.weighted_l2_inputs, S.weighted_objective, trivial⟩
  · rintro ⟨hWeightedInputs, hWeightedObjective, _⟩
    exact
      ⟨{ weighted_l2_inputs := hWeightedInputs
         weighted_objective := hWeightedObjective }⟩

/--
Proposition 2 source-semantics interface: exact expansion of the deterministic
median-set and local `L∞` response data.
-/
theorem proposition2_source_semantics_formula
    {Voter Point : Type*} (E : ILVEnvironment Voter Point) :
    Nonempty (Proposition2SourceSemantics E) ↔
      ∃ hMedian :
        (∀ {Axis : Type}
          {D : DecomposableStructure Voter Point Axis},
          ConditionsC123 E →
            IsDecomposableUtilitiesWith E D →
              DecomposableMedianCarrier E D),
        ∃ hLinfResponse :
          (∀ {Axis : Type}
            {D : DecomposableStructure Voter Point Axis},
            ConditionsC123 E →
              IsDecomposableUtilitiesWith E D →
                DecomposableLinfLocalResponseBridge E D),
          True := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.medianCarrier, S.linfResponse, trivial⟩
  · rintro ⟨hMedian, hLinfResponse, _⟩
    exact
      ⟨{ medianCarrier := hMedian
         linfResponse := hLinfResponse }⟩

/--
Separate theorem source semantics plus an explicit SSGM theorem bundle imply
the four SSGM-backed endpoint consequences.  This row exposes the exact
non-SSGM source obligations before the single reusable SSGM boundary is used.
-/
theorem finite_coordinate_source_semantics_ssgm_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (T2 : Theorem2PrimitiveSourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact
    proof_ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
      (theorem2SourceSemantics_of_primitive T2) P1 P2 S

/--
Unproved source specification for Theorem 1.  This is deliberately a `Prop`
definition, not a theorem: `ILVEnvironment.convergesWithProbabilityOne` is an
abstract field, so no convergence conclusion may be asserted until a concrete
stochastic semantics and the SSGM theorem are supplied.
-/
def theorem1_lp_normed_dual_cases
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  theorem1Statement E

/--
Concrete Theorem 1 Model B `(∞,1)` endpoint: the symmetric active-coordinate
subgradient gives a Borel, conditionally centered finite C3 recursion.  Under
the visible C1/C2/C3 finite-coordinate data and the stated social-objective
identity, it converges almost surely to the paper's social-optimum set.
-/
theorem theorem1_modelB_linf_l1_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLinfSocialObjectiveSource E C3.data) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelBLinfOutcomeTrajectory C3.data r0 project initial) := by
  exact finiteModelBLinfCanonicalMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hr0 initial hinitial T

/--
Concrete Theorem 1 Model A `(∞,1)` endpoint: the Borel water-filled exact
local response is a projected symmetric-subgradient update outside the
corrected crossing-or-near-tie envelope, whose C3 moment budget is summable.
It therefore converges almost surely to the stated social-optimum set.
-/
theorem theorem1_modelA_linf_l1_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLinfSocialObjectiveSource E C3.data) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelALinfL1OutcomeTrajectory C3.data r0 project initial) := by
  exact finiteModelALinfL1CanonicalPerturbedMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hr0 initial hinitial T

/-- Concrete Theorem 1 Model B `(2,2)` endpoint. -/
theorem theorem1_modelB_l2_l2_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data 2) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelBOutcomeTrajectory C3.data 2 r0 project initial) := by
  exact finiteModelBCanonicalMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S HolderDualFinite.two_two hr0 initial hinitial T

/-- Concrete Theorem 1 Model A `(2,2)` endpoint. -/
theorem theorem1_modelA_l2_l2_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data 2) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelAL2OutcomeTrajectory C3.data r0 project initial) := by
  exact finiteModelAL2CanonicalPerturbedMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hr0 initial hinitial T

/-- Concrete Theorem 1 Model B `(1,∞)` endpoint. -/
theorem theorem1_modelB_l1_linf_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data 1) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial) := by
  exact finiteModelBCanonicalLpOneMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hr0 initial hinitial T

/-- Concrete Theorem 1 Model A `(1,∞)` endpoint. -/
theorem theorem1_modelA_l1_linf_finite_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data 1) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial) := by
  exact finiteModelAL1LinfCanonicalPerturbedMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hr0 initial hinitial T

/--
Concrete Theorem 2 Model B endpoint for finite Hölder-dual exponents.  The
displayed iid Algorithm 1 recursion is a direct instance of the reusable
projected stochastic-subgradient minimizer-set convergence theorem.
-/
theorem theorem2_modelB_finite_holder_dual_c3_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {p q r0 : ℝ} (hdual : HolderDualFinite p q) (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data p) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelBOutcomeTrajectory C3.data p r0 project initial) := by
  exact finiteModelBCanonicalMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    C3 S hdual hr0 initial hinitial T

/--
Reusable Proposition 2 convergence lemma for the concrete coordinate-sign
process. Model A and the `p = 1` Model B `L∞` executions converge to the median
set whenever the source median target contains the corresponding
social-optimum set.
-/
theorem proposition2_l1_linf_finite_c3_median_convergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : FiniteModelBLpSocialObjectiveSource E C3.data 1)
    (hmedian : E.socialOptimal ⊆ E.medianSet) :
    @OutcomeIndexedILVConvergesToMedianSet
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial) ∧
    @OutcomeIndexedILVConvergesToMedianSet
      Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
      (finiteModelBIdealSequenceMeasure C3.data)
      (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial) := by
  constructor
  · exact AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet.mono
      (theorem1_modelA_l1_linf_finite_c3_convergence C3 S hr0 initial hinitial T)
      hmedian
  · exact AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet.mono
      (theorem1_modelB_l1_linf_finite_c3_convergence C3 S hr0 initial hinitial T)
      hmedian

/--
Unproved source specification for Theorem 2.  The deterministic
`Theorem2PrimitiveSourceSemantics` and an explicit
`Theorem2SSGMConvergenceTheorem` remain available as the checked route to this
proposition; this declaration itself does not assert an arbitrary environment's
unconstrained convergence field.
-/
def theorem2_modelB_holder_dual_norms
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  theorem2Statement E

/--
Unproved source specification for Proposition 1.  It remains proposition data
until concrete stochastic semantics discharge the separate
`Proposition1SSGMConvergenceTheorem` interface.
-/
def proposition1_weighted_euclidean_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  proposition1Statement E

/--
Proposition 1's finite-coordinate outcome-indexed route.  This is a proved
stochastic convergence result once the displayed weighted-Euclidean Algorithm
1 execution (including its sample law, moments, target identification, and
response update) has been constructed.  Those source-process fields are kept
in `WeightedEuclideanL2OutcomeIndexedMinimizerSetSource`; no convergence field
is assumed there.
-/
theorem proposition1_weighted_euclidean_l2_finite_execution_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2OutcomeIndexedMinimizerSetSource E W model r0) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter S.Ω (Coord → ℝ) S.measurableSpace inferInstance E S.μ S.trajectory := by
  exact S.outcomeIndexed_convergesToSocialOptimal

/--
Concrete joint-law Model A route for Proposition 1.  The selected raw response
is required only to be a measurable exact source response; the proof controls
its rare block-crossing deviations directly under C1--C3.
-/
theorem proposition1_weighted_euclidean_l2_modelA_joint_execution_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : WeightedEuclideanJointSampleData Coord Component)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D.idealDistribution project)
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : WeightedEuclideanJointSampleSocialObjectiveSource E D) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
      inferInstance inferInstance E (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
      (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0 project initial) := by
  exact weightedEuclideanJointSampleModelACanonicalPerturbedMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
    D S A hr0 initial hinitial T

/--
Definition 2's direct social-objective formulation of Proposition 1.  The
target set here maximizes the expected sampled weighted-Euclidean utility,
defined from the joint voter law itself; equivalently, it is the exact
population-cost minimizer set used by the stochastic proof.  This avoids an
additional equality witness for an ambient environment's opaque social-utility
field, while retaining the same concrete C1/C2 and measurable Model A inputs.
-/
theorem proposition1_weighted_euclidean_l2_modelA_joint_execution_population_social_optimal_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : WeightedEuclideanJointSampleData Coord Component)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D.idealDistribution project)
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace) :
    @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
      (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
      inferInstance inferInstance (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
      (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0 project initial)
      (weightedEuclideanJointSamplePopulationSocialOptimalSet D E.solutionSpace) := by
  simpa only [weightedEuclideanJointSamplePopulationSocialOptimalSet_eq_minimizerSet] using
    weightedEuclideanJointSampleModelACanonicalPerturbedMinimizerSetExecution_outcomeIndexedConverges
      D S A hr0 initial hinitial

/--
Concrete-C1 specialization of the joint-law Model A route.  The projection is
the canonical Euclidean closest-point map generated by the closed, bounded,
convex, nonempty feasible set, so no separate projection-existence or Borel
measurability witness is needed.  The remaining arguments state the concrete
C1/C2 facts and the exact measurable Model A response process.
-/
theorem proposition1_weighted_euclidean_l2_modelA_joint_execution_canonical_projection_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : WeightedEuclideanJointSampleData Coord Component)
    (hnonempty : E.solutionSpace.Nonempty)
    (hclosed : IsClosed E.solutionSpace)
    (hbounded : Bornology.IsBounded E.solutionSpace)
    (hconvex : Convex ℝ E.solutionSpace)
    (hunique : HasUniqueIdealSolution E)
    (hideal : ∀ᵐ ideal ∂D.idealDistribution.idealMeasure, ideal ∈ E.solutionSpace)
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace)
    (T : WeightedEuclideanJointSampleSocialObjectiveSource E D) :
    @OutcomeIndexedILVConvergesToSocietalOptimal
      Voter (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
      inferInstance inferInstance E (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
      (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0
        (finiteModelBC1C2CanonicalProjection hclosed hbounded hnonempty) initial) := by
  exact proposition1_weighted_euclidean_l2_modelA_joint_execution_convergence D
    (FiniteModelBC1C2Source.canonical D.idealDistribution hnonempty hclosed hbounded hconvex
      hunique hideal)
    A hr0 initial hinitial T

/--
Concrete-C1, direct-social-objective specialization of Proposition 1's Model A
route.  Both the Euclidean projection and the Definition 2 social objective
are constructed from their mathematical formulas.  The remaining Model A
input is the paper's unspecified measurable tie-breaking between raw local
maximizers.
-/
theorem proposition1_weighted_euclidean_l2_modelA_joint_execution_canonical_projection_population_social_optimal_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : WeightedEuclideanJointSampleData Coord Component)
    (hnonempty : E.solutionSpace.Nonempty)
    (hclosed : IsClosed E.solutionSpace)
    (hbounded : Bornology.IsBounded E.solutionSpace)
    (hconvex : Convex ℝ E.solutionSpace)
    (hunique : HasUniqueIdealSolution E)
    (hideal : ∀ᵐ ideal ∂D.idealDistribution.idealMeasure, ideal ∈ E.solutionSpace)
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace) :
    @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
      (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
      inferInstance inferInstance (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
      (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0
        (finiteModelBC1C2CanonicalProjection hclosed hbounded hnonempty) initial)
      (weightedEuclideanJointSamplePopulationSocialOptimalSet D E.solutionSpace) := by
  exact proposition1_weighted_euclidean_l2_modelA_joint_execution_population_social_optimal_convergence
    D
    (FiniteModelBC1C2Source.canonical D.idealDistribution hnonempty hclosed hbounded hconvex
      hunique hideal)
    A hr0 initial hinitial

/--
Fully concrete Definition 2 / Model A Proposition 1 route.  The source's
previously unspecified measurable tie-breaking is instantiated by the Borel
finite weighted block water-filling response, which has been proved to be an
exact raw local maximizer for every valid joint sample.
-/
theorem proposition1_weighted_euclidean_l2_modelA_joint_execution_canonical_waterfill_population_social_optimal_convergence
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : WeightedEuclideanJointSampleData Coord Component)
    (hnonempty : E.solutionSpace.Nonempty)
    (hclosed : IsClosed E.solutionSpace)
    (hbounded : Bornology.IsBounded E.solutionSpace)
    (hconvex : Convex ℝ E.solutionSpace)
    (hunique : HasUniqueIdealSolution E)
    (hideal : ∀ᵐ ideal ∂D.idealDistribution.idealMeasure, ideal ∈ E.solutionSpace)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (hinitial : initial ∈ E.solutionSpace) :
    @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
      (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
      inferInstance inferInstance (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
      (weightedEuclideanJointSampleModelAOutcomeTrajectory
        (weightedEuclideanJointSampleWaterfillModelAResponseSource D) r0
        (finiteModelBC1C2CanonicalProjection hclosed hbounded hnonempty) initial)
      (weightedEuclideanJointSamplePopulationSocialOptimalSet D E.solutionSpace) := by
  exact proposition1_weighted_euclidean_l2_modelA_joint_execution_canonical_projection_population_social_optimal_convergence
    D hnonempty hclosed hbounded hconvex hunique hideal
    (weightedEuclideanJointSampleWaterfillModelAResponseSource D) hr0 initial hinitial

/--
Exact printed Proposition 2 statement, kept as a source specification. For
this proposition, the paper's proof reads Model B coordinatewise: every active
coordinate moves the full `L∞` radius toward the sampled ideal. The checked
paper-facing endpoint makes that convention explicit. The general normalized
gradient-ray formula is a distinct process when derivative magnitudes differ;
see `docs/PROPOSITION2_MODEL_B_SOURCE_NOTE.md`.
-/
def proposition2_decomposable_linf_medians
    {Voter : Type} {Coord : Type} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  proposition2Statement E

/--
Proposition 2, finite-coordinate/product-box route: under C1-C3 and
decomposable utilities whose coordinates are the ambient finite coordinates,
ILV with `L∞` neighborhoods converges w.p. 1 to the coordinatewise median set
for Model A or B response.  The `L∞` replacement property is derived from the
finite source semantics; the SSGM theorem bundle is an explicit input.
-/
theorem proposition2_finite_coordinate_decomposable_linf_medians
    {Voter : Type} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2FiniteCoordinateStatement E := by
  exact
    proof_proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
      S hSSGM

/--
Theorem 3 corrected projected-trace route: this is the paper-faithful version
of the sharper finite trace endpoint.  If the tail beginning at global time `N`
is represented by a pathwise projected Algorithm 1 trace using the original
radius `r0 / (N + t + 1)`, then every coordinatewise-convergent Model B `L2`
trajectory converges to a directional equilibrium.
-/
theorem theorem3_convergent_l2_modelB_is_directional_equilibrium_global_projected_trace
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (G : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics G) :
    ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                IsDirectionalEquilibrium E xstar := by
  intro hC hContinuous hResponse xstar hConverges
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTraceGlobalPathwise
    G D hC hContinuous hResponse hConverges

/--
Theorem 3 corrected almost-sure trace route: the explicit source trace skeleton
is almost-sure with respect to the iid weighted-voter product law.  The
finite-dot concentration theorem and the extraction of a good pathwise stream
are proved in `ProofInterface.lean`.
-/
theorem theorem3_convergent_l2_modelB_is_directional_equilibrium_global_ae_trace
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (G : FiniteTheorem3DirectionalFieldModel E)
    (S : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton G) :
    ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                IsDirectionalEquilibrium E xstar := by
  intro hC hContinuous hResponse xstar hConverges
  exact
    proof_theorem3_finite_projectedTraceGlobalAETraceSkeleton_directionalEquilibrium
      G S hC hContinuous hResponse hConverges

/--
Theorem 3 projected/constrained alternative from sampled projected source
semantics.  Without assuming aggregate feasibility, Lean proves that either the
paper's zero-field conclusion holds or the aggregate feasible-direction formula
fails.
-/
theorem theorem3_zero_or_no_aggregate_feasible_direction_formula
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E) :
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.theorem3_field.weight
                  M.theorem3_field.utilityGradient xstar =
                  fun _ => (0 : ℝ)) ∨
                ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                  M.theorem3_field := by
  intro hC hContinuous hResponse xstar hConverges
  exact
    proof_theorem3_finite_fullSampledProjectedSourceSemantics_zero_or_no_aggregateFeasibleDirectionFormula
      M hC hContinuous hResponse hConverges

/--
Exact original Theorem 3 statement from sampled projected source semantics in
the full finite-coordinate space.  Here aggregate feasibility is derived from
`E.solutionSpace = Set.univ`, so no aggregate-feasibility source record is
assumed.

Source status: conditional boundary; this is the exact paper statement only in
the explicit full-space case `E.solutionSpace = Set.univ`.
-/
theorem theorem3_statement_of_full_sampled_projected_source_semantics_univ
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ))) :
    theorem3Statement E := by
  exact
    proof_theorem3Statement_of_fullSampledProjectedSourceSemantics_univ_solutionSpace
      M hUniv

/--
Theorem 3 under its approved two-part reading: first the paper's zero-direction
result in full space, then the exact alternative for a restricted projected
space.  In the latter, feasibility can block a nonzero aggregate direction.
-/
theorem theorem3_full_space_and_restricted_space
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateTheorem3SampledProjectedSourceSemantics E) :
    (ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.theorem3_field.weight
                  M.theorem3_field.utilityGradient xstar =
                  fun _ => (0 : ℝ)) ∨
                ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                  M.theorem3_field) ∧
      (E.solutionSpace = (Set.univ : Set (Coord → ℝ)) →
        Theorem3DirectionalFieldFormula E →
          ConditionsC123 E →
            E.directionalFieldUniformlyContinuous →
              E.respondsAccordingTo VoterResponseModel.modelB →
                ∀ xstar,
                  ILVTrajectoryConvergesTo E SourceNorm.l2
                    VoterResponseModel.modelB xstar →
                    IsDirectionalEquilibrium E xstar) := by
  constructor
  · intro hC hContinuous hResponse xstar hConverges
    exact
      proof_theorem3_finite_zero_or_no_aggregateFeasibleDirectionFormula_of_convergent_projectedUpdate
        M.theorem3_field M.theorem3_continuity M.theorem3_algorithm1_update
        (fun _ => M.theorem3_convex_solutionSpace.convex_solutionSpace)
        hC hContinuous hResponse hConverges
  · intro hUniv
    simpa only [theorem3Statement] using
      proof_theorem3Statement_of_theorem3SampledProjectedSourceSemantics_univ_solutionSpace
        M hUniv

universe u v

/--
The literal general-population, full-space reading of Theorem 3.  The source
states an expectation over voters and a convergent iid Model B execution; this
contract keeps both at the paper boundary rather than replacing them with a
fixed finite trajectory.
-/
def theorem3_population_fullspaceSpec : Prop :=
  ∀ {Voter : Type u} {Coord : Type v}
    [MetricSpace Voter] [SecondCountableTopology Voter]
    [MeasurableSpace Voter] [BorelSpace Voter] [StandardBorelSpace Voter]
    [Nonempty Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E)
    (S : PopulationTheorem3IidTraceSource M)
    (xstar : Coord → ℝ),
    (∀ᵐ omega ∂iidSequenceMeasure M.population,
      PopulationTheorem3OutcomeConvergesTo S.trajectory omega xstar) →
      ∀ᵐ omega ∂iidSequenceMeasure M.population,
        IsDirectionalEquilibrium E xstar

/-- Proof endpoint for the literal population/full-space Theorem 3 contract. -/
theorem theorem3_population_fullspace : theorem3_population_fullspaceSpec := by
  intro Voter Coord _ _ _ _ _ _ _ _ E M S xstar hconverges
  exact populationTheorem3_iid_fullspace_directional_equilibrium M S xstar hconverges

/--
An explicitly supplementary finite projected-space alternative.  A boundary
can block a nonzero aggregate direction, so this theorem is not presented as a
literal restatement of the paper's full-space Theorem 3.
-/
def theorem3_restricted_space_alternativeSpec : Prop :=
  ∀ {Voter : Type u} {Coord : Type v} [Fintype Voter]
      [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
      [Fintype Coord] [Nonempty Coord]
      (E : ILVEnvironment Voter (Coord → ℝ))
      (M : FiniteCoordinateTheorem3SampledProjectedSourceSemantics E),
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                (finiteTheorem3DirectionalField M.theorem3_field.weight
                    M.theorem3_field.utilityGradient xstar =
                    fun _ => (0 : ℝ)) ∨
                  ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                    M.theorem3_field

/-- Proof endpoint for the supplementary restricted-space alternative. -/
theorem theorem3_restricted_space_alternative :
    theorem3_restricted_space_alternativeSpec := by
  intro Voter Coord _ _ _ _ _ E M hC hContinuous hResponse xstar hconverges
  exact (theorem3_full_space_and_restricted_space E M).1
    hC hContinuous hResponse xstar hconverges

/--
Compatibility bundle retaining the formerly published two-part presentation.
The first conjunct is the source-facing Theorem 3 contract; the second is the
separately labelled finite projected-space alternative.
-/
def theorem3_population_full_space_and_restricted_spaceSpec : Prop :=
  theorem3_population_fullspaceSpec.{u, v} ∧
    (∀ {Voter : Type u} {Coord : Type v} [Fintype Voter]
      [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
      [Fintype Coord] [Nonempty Coord]
      (E : ILVEnvironment Voter (Coord → ℝ))
      (M : FiniteCoordinateTheorem3SampledProjectedSourceSemantics E),
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ∀ xstar,
              FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
                VoterResponseModel.modelB xstar →
                (finiteTheorem3DirectionalField M.theorem3_field.weight
                    M.theorem3_field.utilityGradient xstar =
                    fun _ => (0 : ℝ)) ∨
                  ¬ FiniteTheorem3AggregateFeasibleDirectionFormula
                    M.theorem3_field)

/-- Proof endpoint for the general-population full-space conclusion and the
explicit restricted-space alternative. -/
theorem theorem3_population_full_space_and_restricted_space :
    theorem3_population_full_space_and_restricted_spaceSpec := by
  constructor
  · exact theorem3_population_fullspace
  · exact theorem3_restricted_space_alternative

/--
No-hidden-premise sampled projected finite-coordinate paper closeout with an
explicit SSGM theorem bundle.
-/
theorem finite_coordinate_full_sampled_projected_paper_consequences_with_ssgm
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  exact
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics_ssgmConvergence
      M S

/--
No-hidden-premise sampled projected finite-coordinate paper closeout using an
explicit SSGM theorem bundle.
-/
theorem finite_coordinate_full_sampled_projected_paper_consequences
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (M : FiniteCoordinateILVFullSampledProjectedSourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    FiniteCoordinateILVFullProjectedPaperConsequences M := by
  exact
    proof_finiteCoordinateILVFullProjectedPaperConsequences_of_fullSampledProjectedSourceSemantics_ssgmConvergence
      M S

/-- Transparent v11 semantic target for `theorem1_norm_pair_l2_l2`. -/
def theorem1_norm_pair_l2_l2Spec : Prop :=
  Theorem1NormPair SourceNorm.l2 SourceNorm.l2

/-- Transparent v11 semantic target for `theorem1_norm_pair_l1_linf`. -/
def theorem1_norm_pair_l1_linfSpec : Prop :=
  Theorem1NormPair SourceNorm.l1 SourceNorm.linfty

/-- Transparent v11 semantic target for `theorem1_norm_pair_linf_l1`. -/
def theorem1_norm_pair_linf_l1Spec : Prop :=
  Theorem1NormPair SourceNorm.linfty SourceNorm.l1

/-- Transparent v11 semantic target for `algorithm1_radius_formula`. -/
def algorithm1_radius_formulaSpec (r0 : ℝ) (t : ℕ) : Prop :=
  ilvRadius r0 t = r0 / (t : ℝ)

/-- Transparent v11 semantic target for `algorithm1_radius_tendsto_zero`. -/
def algorithm1_radius_tendsto_zeroSpec (r0 : ℝ) : Prop :=
  Filter.Tendsto (ilvRadius r0) Filter.atTop (nhds 0)

/-- Transparent v11 semantic target for `algorithm1_radius_sq_summable`. -/
def algorithm1_radius_sq_summableSpec (r0 : ℝ) : Prop :=
  Summable (fun t : ℕ => (ilvRadius r0 (t + 1)) ^ 2)

/-- Transparent v11 semantic target for `algorithm1_radius_sum_tendsto_atTop`. -/
def algorithm1_radius_sum_tendsto_atTopSpec {r0 : ℝ} (hr0 : 0 < r0) : Prop :=
  Filter.Tendsto
    (fun n : ℕ => ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
    Filter.atTop Filter.atTop

/-- Transparent v11 semantic target for `algorithm1_radius_not_summable`. -/
def algorithm1_radius_not_summableSpec {r0 : ℝ} (hr0 : 0 < r0) : Prop :=
  ¬ Summable (fun t : ℕ => ilvRadius r0 (t + 1))

/-- Transparent v11 semantic target for `algorithm1_radius_ssgm_step_size_conditions`. -/
def algorithm1_radius_ssgm_step_size_conditionsSpec {r0 : ℝ} (hr0 : 0 < r0) : Prop :=
  SSGMStepSizeConditions (ilvRadius r0)

/-- Transparent v11 semantic target for `algorithm1_local_neighborhood_formula`. -/
def algorithm1_local_neighborhood_formulaSpec {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (center candidate : Point) (r : ℝ) : Prop :=
  candidate ∈ localNeighborhoodFormulaData G q center r ↔
    candidate ∈ G.solutionSpace ∧
      G.normDistance q candidate center ≤ r

/-- Transparent v11 semantic target for `algorithm1_norm_projection_formula`. -/
def algorithm1_norm_projection_formulaSpec {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (project : Point → Point) : Prop :=
  isNormProjectionOntoFormulaData G q project ↔
    ∀ y, project y ∈ G.solutionSpace ∧
      IsMinOn (fun x => G.normDistance q x y) G.solutionSpace (project y)

/-- Transparent v11 semantic target for `algorithm1_projected_update_formula`. -/
def algorithm1_projected_update_formulaSpec
    {Point : Type*} (project : Point → Point) (raw next : Point) : Prop :=
  Algorithm1ProjectedUpdate project raw next ↔ next = project raw

/-- Transparent v11 semantic target for `algorithm1_projected_trajectory_feasible_of_normProjection`. -/
def algorithm1_projected_trajectory_feasible_of_normProjectionSpec
    {Point : Type*} {G : ILVGeometryFormulaData Point} {q : SourceNorm}
    {project : Point → Point} {raw trajectory : ℕ → Point}
    (hproject : isNormProjectionOntoFormulaData G q project)
    (h0 : trajectory 0 ∈ G.solutionSpace)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) : Prop :=
  ∀ t : ℕ, trajectory t ∈ G.solutionSpace

/-- Transparent v11 semantic target for `algorithm1_window_stable_formula`. -/
def algorithm1_window_stable_formulaSpec {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) : Prop :=
  algorithm1WindowStableFormulaData G q trajectory t N epsilon ↔
    ∀ l m,
      l ∈ Finset.Icc (t - N) t →
        m ∈ Finset.Icc (t - N) t →
          G.normDistance q (trajectory l) (trajectory m) ≤ epsilon

/-- Transparent v11 semantic target for `algorithm1_stop_condition_formula`. -/
def algorithm1_stop_condition_formulaSpec {Point : Type*}
    (G : ILVGeometryFormulaData Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) : Prop :=
  algorithm1StopConditionFormulaData G q trajectory T N t epsilon ↔
    t = T ∨ algorithm1WindowStableFormulaData G q trajectory t N epsilon

/-- Transparent v11 semantic target for `modelA_response_formula`. -/
def modelA_response_formulaSpec {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  modelAResponseFormulaData U q center r voter response ↔
    response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
      ∀ candidate, candidate ∈ localNeighborhoodFormulaData U.geometry q center r →
        U.utility voter candidate ≤ U.utility voter response

/-- Transparent v11 semantic target for `modelA_response_isMaxOn_formula`. -/
def modelA_response_isMaxOn_formulaSpec {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  modelAResponseFormulaData U q center r voter response ↔
    response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
      IsMaxOn (U.utility voter)
        (localNeighborhoodFormulaData U.geometry q center r) response

/-- Transparent v11 semantic target for `modelA_raw_response_formula`. -/
def modelA_raw_response_formulaSpec {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  modelARawResponseFormulaData U q center r voter response ↔
    response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
      ∀ candidate, candidate ∈ rawLocalNeighborhoodFormulaData U.geometry q center r →
        U.utility voter candidate ≤ U.utility voter response

/-- Transparent v11 semantic target for `modelA_raw_response_isMaxOn_formula`. -/
def modelA_raw_response_isMaxOn_formulaSpec {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  modelARawResponseFormulaData U q center r voter response ↔
    response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
      IsMaxOn (U.utility voter)
        (rawLocalNeighborhoodFormulaData U.geometry q center r) response

/-- Transparent v11 semantic target for `modelB_finite_response_neg_lp_cost_gradient_formula`. -/
def modelB_finite_response_neg_lp_cost_gradient_formulaSpec
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) : Prop :=
  ModelBFiniteResponseAt (SourceNorm.lp q) center r
      (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
      response ↔
    response =
      fun i => center i - r *
        lpCostGradientCandidate p (fun j => center j - ideal j) i

/-- Transparent v11 semantic target for `modelA_response_lp_normed_cost_minimizer_formula`. -/
def modelA_response_lp_normed_cost_minimizer_formulaSpec
    {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (p q : SourceNorm)
    (ideal : Voter → Point)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : isLpNormedUtilitiesFormulaData U ideal p) : Prop :=
  modelAResponseFormulaData U q center r voter response ↔
      response ∈ localNeighborhoodFormulaData U.geometry q center r ∧
        IsMinOn (fun candidate => U.normDistance p candidate (ideal voter))
          (localNeighborhoodFormulaData U.geometry q center r) response

/-- Transparent v11 semantic target for `modelA_raw_response_lp_normed_cost_minimizer_formula`. -/
def modelA_raw_response_lp_normed_cost_minimizer_formulaSpec
    {Voter Point : Type*}
    (U : ILVUtilityFormulaData Voter Point) (p q : SourceNorm)
    (ideal : Voter → Point)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : isLpNormedUtilitiesFormulaData U ideal p) : Prop :=
  modelARawResponseFormulaData U q center r voter response ↔
    response ∈ rawLocalNeighborhoodFormulaData U.geometry q center r ∧
      IsMinOn (fun candidate => U.normDistance p candidate (ideal voter))
        (rawLocalNeighborhoodFormulaData U.geometry q center r) response

/-- Transparent v11 semantic target for `definition1_finite_coordinate_l1_formula`. -/
def definition1_finite_coordinate_l1_formulaSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) : Prop :=
  (∀ v x, utility v x =
      -finiteCoordinateDistance SourceNorm.l1 x (ideal v)) ↔
    ∀ v x, utility v x =
      -AppliedModelingLib.FiniteDimensionalNorms.l1
        (fun m => x m - ideal v m)

/-- Transparent v11 semantic target for `definition1_finite_coordinate_l2_formula`. -/
def definition1_finite_coordinate_l2_formulaSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) : Prop :=
  (∀ v x, utility v x =
      -finiteCoordinateDistance SourceNorm.l2 x (ideal v)) ↔
    ∀ v x, utility v x =
      -AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun m => x m - ideal v m)

/-- Transparent v11 semantic target for `definition1_finite_coordinate_linf_formula`. -/
def definition1_finite_coordinate_linf_formulaSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ) : Prop :=
  (∀ v x, utility v x =
      -finiteCoordinateDistance SourceNorm.linfty x (ideal v)) ↔
    ∀ v x, utility v x =
      -AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun m => x m - ideal v m)

/-- Transparent v11 semantic target for `definition1_finite_coordinate_lp_formula`. -/
def definition1_finite_coordinate_lp_formulaSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : Voter → (Coord → ℝ) → ℝ) (ideal : Voter → Coord → ℝ)
    (p : ℝ) : Prop :=
  (∀ v x, utility v x =
      -finiteCoordinateDistance (SourceNorm.lp p) x (ideal v)) ↔
    ∀ v x, utility v x =
      -AppliedModelingLib.FiniteDimensionalNorms.lp p
        (fun m => x m - ideal v m)

/-- Transparent v11 semantic target for `lemma3_gradient_candidate_source_formula`. -/
def lemma3_gradient_candidate_source_formulaSpec
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 0 < p) (d : Coord → ℝ) : Prop :=
  lpCostGradientCandidate p d =
    fun i => (|d i| ^ (p - 1) * (d i / |d i|)) /
      (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1)

/-- Transparent v11 semantic target for `lemma3_finite_holder_dual_gradient_candidate_norm_formula`. -/
def lemma3_finite_holder_dual_gradient_candidate_norm_formulaSpec
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) : Prop :=
  finiteCoordinateNorm (SourceNorm.lp q)
    (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1

/-- Transparent v11 semantic target for `lemma3_gradient_candidate_hasFDerivAt_formula`. -/
def lemma3_gradient_candidate_hasFDerivAt_formulaSpec
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) : Prop :=
  HasFDerivAt
    (fun y : Coord → ℝ =>
      AppliedModelingLib.FiniteDimensionalNorms.lp p
        (fun i => y i - ideal i))
    (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
      (lpCostGradientCandidate p (fun i => x i - ideal i))) x

/-- Transparent v11 semantic target for `lemma3_coordinate_equality_bad_event_null_from_boundedDensity`. -/
def lemma3_coordinate_equality_bad_event_null_from_boundedDensitySpec
    {Coord : Type*} [Fintype Coord] [MeasurableSpace (Coord → ℝ)]
    {ν μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : AppliedModelingLib.Probability.HasBoundedDensity ν μ C)
    (x : Coord → ℝ)
    (hcoord : ∀ i, ν (coordinateEqualityHyperplane x i) = 0) : Prop :=
  μ (coordinateEqualityBadEvent x) = 0

/-- Transparent v11 semantic target for `lemma3_coordinate_equality_bad_event_null_from_productMeasure`. -/
def lemma3_coordinate_equality_bad_event_null_from_productMeasureSpec
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) : Prop :=
  μ (coordinateEqualityBadEvent x) = 0

/-- Transparent v11 semantic target for `lemma3_coordinate_noncollision_ae_from_productMeasure`. -/
def lemma3_coordinate_noncollision_ae_from_productMeasureSpec
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) : Prop :=
  ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i

/-- Transparent v11 semantic target for `c3_bounded_density_coordinate_noncollision_ae`. -/
def c3_bounded_density_coordinate_noncollision_aeSpec
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) (x : Coord → ℝ) : Prop :=
  ∀ᵐ ideal ∂D.idealMeasure, ∀ i, x i ≠ ideal i

/-- Transparent v11 semantic target for the source definition `dlcdBudgetUtility`. -/
def dlcdBudgetUtilitySpec
    {Dim : Type*} [Fintype Dim]
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) (x : Dim → ℝ) : Prop :=
  dlcdBudgetUtility isExpense componentUtility deficitWeight x = ((∑ m : Dim, componentUtility m (x m)) -
    deficitWeight *
      ((∑ m : Dim, if isExpense m then x m else 0) -
        (∑ m : Dim, if isExpense m then 0 else x m)))

/-- Transparent v11 semantic target for the source definition `paper_definition4_dlcd_formula`. -/
def paper_definition4_dlcd_formulaSpec
    {Dim : Type*} [Fintype Dim]
    (utility : (Dim → ℝ) → ℝ)
    (isExpense : Dim → Bool) (componentUtility : Dim → ℝ → ℝ)
    (deficitWeight : ℝ) : Prop :=
  paper_definition4_dlcd_formula utility isExpense componentUtility deficitWeight = (0 ≤ deficitWeight ∧
    (∀ m : Dim, ConcaveOn ℝ Set.univ (componentUtility m)) ∧
      ∀ x : Dim → ℝ,
        utility x =
          dlcdBudgetUtility isExpense componentUtility deficitWeight x)

/-- Transparent v11 semantic target for the source definition `theorem1_lp_normed_dual_cases`. -/
def theorem1_lp_normed_dual_casesSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  theorem1_lp_normed_dual_cases E = (theorem1Statement E)

/-- Transparent v11 semantic target for the source definition `theorem2_modelB_holder_dual_norms`. -/
def theorem2_modelB_holder_dual_normsSpec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  theorem2_modelB_holder_dual_norms E = (theorem2Statement E)

/-- Transparent v11 semantic target for the source definition `proposition1_weighted_euclidean_l2`. -/
def proposition1_weighted_euclidean_l2Spec
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  proposition1_weighted_euclidean_l2 E = (proposition1Statement E)

/-- Transparent v11 semantic target for the source definition `proposition2_decomposable_linf_medians`. -/
def proposition2_decomposable_linf_mediansSpec
    {Voter : Type} {Coord : Type} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  proposition2_decomposable_linf_medians E = (proposition2Statement E)

/-- Semantic target for the corrected minimizer-set replacement of Appendix Theorem 5. -/
def appendix_theorem5_minimizer_set_replacementSpec
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ) : Prop :=
  AppendixTheorem5MinimizerSetStatement mu filtration solutionSpace targetSet
    objective project trajectory meanSubgradient noise bias radius reference

/--
Transparent semantic target for Appendix Lemma 1.  It retains the source's
universal quantifier over every sampled-cost subgradient, rather than fixing a
convenient candidate.  The explicit finite constant is `2 * card Coord`.
-/
def appendix_lemma1_uniform_direction_errorSpec : Prop := by
  classical
  exact
  (∀ {Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {center ideal : Coord → ℝ} {r : ℝ} (g : Coord → ℝ),
      0 < r →
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i)) center g →
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => l2BallDirection center ideal r i - g i) ≤ 2 * Fintype.card Coord) ∧
  (∀ {Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {center ideal : Coord → ℝ} {r : ℝ} (g : Coord → ℝ),
      0 < r →
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i)) center g →
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => l1LinfBallDirection center ideal r i - g i) ≤ 2 * Fintype.card Coord) ∧
  (∀ {Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {center ideal raw : Coord → ℝ} {r : ℝ} (g : Coord → ℝ),
      0 < r →
      finiteCoordinateDistance SourceNorm.l1 raw center ≤ r →
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)) center g →
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => linfL1RawDirection center raw r i - g i) ≤ 2 * Fintype.card Coord)

/-- Appendix Lemma 1's finite uniform error bound for all three norm pairs. -/
theorem appendix_lemma1_uniform_direction_error :
    appendix_lemma1_uniform_direction_errorSpec := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Coord _ _ center ideal r g hr hsub
    exact appendixLemma1_l2BallDirection_uniform_norm_gap_all_subgradients hr g hsub
  · intro Coord _ _ center ideal r g hr hsub
    exact appendixLemma1_l1LinfBallDirection_uniform_norm_gap_all_subgradients hr g hsub
  · intro Coord _ _ center ideal raw r g hr hraw hsub
    exact appendixLemma1_linfL1RawDirection_uniform_norm_gap_all_subgradients hr hraw g hsub

/--
Proof-support envelope statement for Appendix Lemma 2.  The source-facing
`Spec` below instead names the paper's actual subgradient-failure event.
-/
private def appendixLemma2BadEventEnvelopeLinearRate : Prop := by
  classical
  exact
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      {D : FiniteCoordinateIdealDistributionData Coord}
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E D project)
      {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ) (n : ℕ),
      (∀ omega,
        ¬ FiniteSubgradientAt
            (fun y : Coord → ℝ =>
              AppliedModelingLib.FiniteDimensionalNorms.l2
                (fun i => y i - finiteModelBIdealSample n omega i))
            (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
            (l2BallDirection
              (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
              (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1))) →
          finiteModelBIdealSample n omega ∈
            l2BallBadEvent
              (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1))) ∧
        (finiteModelBIdealSequenceMeasure D)[
          fun omega =>
            (l2BallBadEvent
              (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1))).indicator (fun _ => (1 : ℝ))
              (finiteModelBIdealSample n omega) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
            finiteModelBIdealSequenceMeasure D]
          fun _ => ilvRadius r0 (n + 1) *
            finiteModelBC1C2CoordinateSlabRealConstant S) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      {D : FiniteCoordinateIdealDistributionData Coord}
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E D project)
      {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ) (n : ℕ),
      (∀ omega,
        ¬ FiniteSubgradientAt
            (fun y : Coord → ℝ =>
              AppliedModelingLib.FiniteDimensionalNorms.l1
                (fun i => y i - finiteModelBIdealSample n omega i))
            (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
            (l1LinfBallDirection
              (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
              (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1))) →
          finiteModelBIdealSample n omega ∈
            l1LinfSlabBadEvent
              (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1))) ∧
        (finiteModelBIdealSequenceMeasure D)[
          fun omega =>
            (l1LinfSlabBadEvent
              (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1))).indicator (fun _ => (1 : ℝ))
              (finiteModelBIdealSample n omega) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
            finiteModelBIdealSequenceMeasure D]
          fun _ => ilvRadius r0 (n + 1) *
            finiteModelBC1C2CoordinateSlabRealConstant S) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      {D : FiniteCoordinateIdealDistributionData Coord}
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E D project)
      {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ) (n : ℕ),
      (∀ omega,
        ¬ FiniteSubgradientAt
            (fun y : Coord → ℝ =>
              AppliedModelingLib.FiniteDimensionalNorms.linf
                (fun i => y i - finiteModelBIdealSample n omega i))
            (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
            (linfL1RawDirection
              (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
              (finiteModelALinfL1OutcomeRawResponse r0
                (finiteModelALinfL1OutcomeTrajectory D r0 project initial)
                finiteModelBIdealSample n omega)
              (ilvRadius r0 (n + 1))) →
          finiteModelBIdealSample n omega ∈
            l1LinfSlabBadEvent
              (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1)) ∪
            linfL1NearTieBadEvent
              (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1))) ∧
        (finiteModelBIdealSequenceMeasure D)[
          fun omega =>
            (l1LinfSlabBadEvent
              (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
              (ilvRadius r0 (n + 1)) ∪
              linfL1NearTieBadEvent
                (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
                (ilvRadius r0 (n + 1))).indicator (fun _ => (1 : ℝ))
              (finiteModelBIdealSample n omega) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
            finiteModelBIdealSequenceMeasure D]
          fun _ => ilvRadius r0 (n + 1) *
            (finiteModelBC1C2CoordinateSlabRealConstant S +
              finiteModelBC1C2LinearTieSlabRealConstant S))

/-- Envelope proof route for Appendix Lemma 2's direct source statement. -/
private theorem appendixLemma2_badEventEnvelopeLinearRate :
    appendixLemma2BadEventEnvelopeLinearRate := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Voter Coord _ _ E D project S r0 hr0 initial n
    refine ⟨?_, finiteModelAL2Outcome_l2BallBadEvent_condExp_le S hr0 initial n⟩
    intro omega hfailure
    by_contra hbad
    exact hfailure (l2BallDirection_subgradient_of_notMem_badEvent
      (ilvRadius_succ_pos hr0 n) hbad)
  · intro Voter Coord _ _ E D project S r0 hr0 initial n
    refine ⟨?_, finiteModelAL1LinfOutcome_slabBadEvent_condExp_le S hr0 initial n⟩
    intro omega hfailure
    by_contra hbad
    exact hfailure (l1LinfBallDirection_subgradient_of_notMem_slabBadEvent
      (ilvRadius_succ_pos hr0 n) hbad)
  · intro Voter Coord _ _ E D project S r0 hr0 initial n
    refine ⟨?_, finiteModelALinfL1Outcome_correctedEnvelope_condExp_le S hr0 initial n⟩
    intro omega hfailure
    by_contra hbad
    exact hfailure (by
      simpa only [finiteModelALinfL1OutcomeRawResponse] using
        linfL1WaterfillRawDirection_subgradient_of_notMem_correctedEnvelope
          (ilvRadius_succ_pos hr0 n) hbad)

/--
The actual source failure event in Appendix Lemma 2 at `(2,2)` inherits the
conditional envelope bound.  Measurability is explicit because the source
conditions its indicator on the realized history.
-/
private theorem appendixLemma2_l2_sourceFailureEvent_condExp_le
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (n : ℕ) (A : Set (ℕ → Coord → ℝ))
    (hAmeas : MeasurableSet A)
    (hAfailure : ∀ omega, omega ∈ A ↔
      ¬ FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l2
            (fun i => y i - finiteModelBIdealSample n omega i))
        (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
        (l2BallDirection
          (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
          (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1)))) :
    (finiteModelBIdealSequenceMeasure D)[
      A.indicator (fun _ => (1 : ℝ)) |
      finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
        finiteModelBIdealSequenceMeasure D]
      fun _ => ilvRadius r0 (n + 1) *
        finiteModelBC1C2CoordinateSlabRealConstant S := by
  classical
  letI : IsProbabilityMeasure (finiteModelBIdealSequenceMeasure D) :=
    finiteModelBIdealSequenceMeasure_isProbabilityMeasure D
  let radius : ℝ := ilvRadius r0 (n + 1)
  let B : Set (ℕ → Coord → ℝ) := {omega |
    finiteModelBIdealSample n omega ∈ l2BallBadEvent
      (finiteModelAL2OutcomeTrajectory D r0 project initial n omega) radius}
  have htrajectory : Measurable (finiteModelAL2OutcomeTrajectory D r0 project initial n) :=
    (stronglyMeasurable_finiteModelAL2OutcomeTrajectory_natural D r0 project initial
      S.project_measurable n).measurable.mono
      ((finiteModelBIdealNaturalFiltration (Coord := Coord)).le n) le_rfl
  have hpair : Measurable (fun omega : ℕ → Coord → ℝ =>
      (finiteModelAL2OutcomeTrajectory D r0 project initial n omega,
        finiteModelBIdealSample n omega)) :=
    htrajectory.prodMk (measurable_finiteModelBIdealSample n)
  have hBmeas : MeasurableSet B := by
    let event : Set ((Coord → ℝ) × (Coord → ℝ)) :=
      {z | z.2 ∈ l2BallBadEvent z.1 radius}
    have hevent : MeasurableSet event :=
      measurableSet_l2BallBadEvent_state_ideal radius
    simpa only [B, event] using hevent.preimage hpair
  have hsubset : ∀ᵐ omega ∂finiteModelBIdealSequenceMeasure D, omega ∈ A → omega ∈ B := by
    filter_upwards [] with omega hAomega
    by_contra hBomega
    exact (hAfailure omega).mp hAomega
      (l2BallDirection_subgradient_of_notMem_badEvent
        (ilvRadius_succ_pos hr0 n) hBomega)
  calc
    (finiteModelBIdealSequenceMeasure D)[A.indicator (fun _ => (1 : ℝ)) |
        finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
          finiteModelBIdealSequenceMeasure D]
        (finiteModelBIdealSequenceMeasure D)[B.indicator (fun _ => (1 : ℝ)) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] :=
      condExp_indicator_le_of_ae_subset (finiteModelBIdealSequenceMeasure D)
        (finiteModelBIdealNaturalFiltration (Coord := Coord) n) hAmeas hBmeas hsubset
    _ ≤ᵐ[finiteModelBIdealSequenceMeasure D] fun _ =>
        ilvRadius r0 (n + 1) * finiteModelBC1C2CoordinateSlabRealConstant S := by
      simpa only [B, radius] using
        finiteModelAL2Outcome_l2BallBadEvent_condExp_le S hr0 initial n

/-- Proof bridge from the source `(1,∞)` failure event to its envelope. -/
private theorem appendixLemma2_l1Linf_sourceFailureEvent_condExp_le
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (n : ℕ) (A : Set (ℕ → Coord → ℝ))
    (hAmeas : MeasurableSet A)
    (hAfailure : ∀ omega, omega ∈ A ↔
      ¬ FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l1
            (fun i => y i - finiteModelBIdealSample n omega i))
        (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
        (l1LinfBallDirection
          (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
          (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1)))) :
    (finiteModelBIdealSequenceMeasure D)[
      A.indicator (fun _ => (1 : ℝ)) |
      finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
        finiteModelBIdealSequenceMeasure D]
      fun _ => ilvRadius r0 (n + 1) *
        finiteModelBC1C2CoordinateSlabRealConstant S := by
  classical
  letI : IsProbabilityMeasure (finiteModelBIdealSequenceMeasure D) :=
    finiteModelBIdealSequenceMeasure_isProbabilityMeasure D
  let radius : ℝ := ilvRadius r0 (n + 1)
  let B : Set (ℕ → Coord → ℝ) := {omega |
    finiteModelBIdealSample n omega ∈ l1LinfSlabBadEvent
      (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega) radius}
  have htrajectory : Measurable (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n) :=
    (stronglyMeasurable_finiteModelAL1LinfOutcomeTrajectory_natural D r0 project initial
      S.project_measurable n).measurable.mono
      ((finiteModelBIdealNaturalFiltration (Coord := Coord)).le n) le_rfl
  have hpair : Measurable (fun omega : ℕ → Coord → ℝ =>
      (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega,
        finiteModelBIdealSample n omega)) :=
    htrajectory.prodMk (measurable_finiteModelBIdealSample n)
  have hBmeas : MeasurableSet B := by
    let event : Set ((Coord → ℝ) × (Coord → ℝ)) :=
      {z | z.2 ∈ l1LinfSlabBadEvent z.1 radius}
    have hevent : MeasurableSet event :=
      measurableSet_l1LinfSlabBadEvent_state_ideal radius
    simpa only [B, event] using hevent.preimage hpair
  have hsubset : ∀ᵐ omega ∂finiteModelBIdealSequenceMeasure D, omega ∈ A → omega ∈ B := by
    filter_upwards [] with omega hAomega
    by_contra hBomega
    exact (hAfailure omega).mp hAomega
      (l1LinfBallDirection_subgradient_of_notMem_slabBadEvent
        (ilvRadius_succ_pos hr0 n) hBomega)
  calc
    (finiteModelBIdealSequenceMeasure D)[A.indicator (fun _ => (1 : ℝ)) |
        finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
          finiteModelBIdealSequenceMeasure D]
        (finiteModelBIdealSequenceMeasure D)[B.indicator (fun _ => (1 : ℝ)) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] :=
      condExp_indicator_le_of_ae_subset (finiteModelBIdealSequenceMeasure D)
        (finiteModelBIdealNaturalFiltration (Coord := Coord) n) hAmeas hBmeas hsubset
    _ ≤ᵐ[finiteModelBIdealSequenceMeasure D] fun _ =>
        ilvRadius r0 (n + 1) * finiteModelBC1C2CoordinateSlabRealConstant S := by
      simpa only [B, radius] using
        finiteModelAL1LinfOutcome_slabBadEvent_condExp_le S hr0 initial n

/-- Proof bridge from the source `(∞,1)` failure event to its envelope. -/
private theorem appendixLemma2_linfL1_sourceFailureEvent_condExp_le
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D project)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (n : ℕ) (A : Set (ℕ → Coord → ℝ))
    (hAmeas : MeasurableSet A)
    (hAfailure : ∀ omega, omega ∈ A ↔
      ¬ FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.linf
            (fun i => y i - finiteModelBIdealSample n omega i))
        (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
        (linfL1RawDirection
          (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
          (finiteModelALinfL1OutcomeRawResponse r0
            (finiteModelALinfL1OutcomeTrajectory D r0 project initial)
            finiteModelBIdealSample n omega)
          (ilvRadius r0 (n + 1)))) :
    (finiteModelBIdealSequenceMeasure D)[
      A.indicator (fun _ => (1 : ℝ)) |
      finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
        finiteModelBIdealSequenceMeasure D]
      fun _ => ilvRadius r0 (n + 1) *
        (finiteModelBC1C2CoordinateSlabRealConstant S +
          finiteModelBC1C2LinearTieSlabRealConstant S) := by
  classical
  letI : IsProbabilityMeasure (finiteModelBIdealSequenceMeasure D) :=
    finiteModelBIdealSequenceMeasure_isProbabilityMeasure D
  let radius : ℝ := ilvRadius r0 (n + 1)
  let B : Set (ℕ → Coord → ℝ) := {omega |
    finiteModelBIdealSample n omega ∈ l1LinfSlabBadEvent
      (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega) radius ∪
      linfL1NearTieBadEvent
        (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega) radius}
  have htrajectory : Measurable (finiteModelALinfL1OutcomeTrajectory D r0 project initial n) :=
    (stronglyMeasurable_finiteModelALinfL1OutcomeTrajectory_natural D r0 project initial
      S.project_measurable n).measurable.mono
      ((finiteModelBIdealNaturalFiltration (Coord := Coord)).le n) le_rfl
  have hpair : Measurable (fun omega : ℕ → Coord → ℝ =>
      (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega,
        finiteModelBIdealSample n omega)) :=
    htrajectory.prodMk (measurable_finiteModelBIdealSample n)
  have hBmeas : MeasurableSet B := by
    let event : Set ((Coord → ℝ) × (Coord → ℝ)) :=
      {z | z.2 ∈ l1LinfSlabBadEvent z.1 radius ∪ linfL1NearTieBadEvent z.1 radius}
    have hevent : MeasurableSet event :=
      (measurableSet_l1LinfSlabBadEvent_state_ideal radius).union
        (measurableSet_linfL1NearTieBadEvent_state_ideal radius)
    simpa only [B, event] using hevent.preimage hpair
  have hsubset : ∀ᵐ omega ∂finiteModelBIdealSequenceMeasure D, omega ∈ A → omega ∈ B := by
    filter_upwards [] with omega hAomega
    by_contra hBomega
    exact (hAfailure omega).mp hAomega (by
      simpa only [finiteModelALinfL1OutcomeRawResponse] using
        linfL1WaterfillRawDirection_subgradient_of_notMem_correctedEnvelope
          (ilvRadius_succ_pos hr0 n) hBomega)
  calc
    (finiteModelBIdealSequenceMeasure D)[A.indicator (fun _ => (1 : ℝ)) |
        finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
          finiteModelBIdealSequenceMeasure D]
        (finiteModelBIdealSequenceMeasure D)[B.indicator (fun _ => (1 : ℝ)) |
          finiteModelBIdealNaturalFiltration (Coord := Coord) n] :=
      condExp_indicator_le_of_ae_subset (finiteModelBIdealSequenceMeasure D)
        (finiteModelBIdealNaturalFiltration (Coord := Coord) n) hAmeas hBmeas hsubset
    _ ≤ᵐ[finiteModelBIdealSequenceMeasure D] fun _ =>
        ilvRadius r0 (n + 1) *
          (finiteModelBC1C2CoordinateSlabRealConstant S +
            finiteModelBC1C2LinearTieSlabRealConstant S) := by
      simpa only [B, radius] using
        finiteModelALinfL1Outcome_correctedEnvelope_condExp_le S hr0 initial n

/--
Transparent semantic target for Appendix Lemma 2.  For each source norm pair,
`A n` is the paper's actual subgradient-failure event at step `n`; the
conclusion is the printed conditional `O(r_t)` indicator bound, not the
larger measurable envelope used in the proof.
-/
def appendix_lemma2_bad_event_linear_rateSpec : Prop := by
  classical
  exact
    (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
        {E : ILVEnvironment Voter (Coord → ℝ)}
        {D : FiniteCoordinateIdealDistributionData Coord}
        {project : (Coord → ℝ) → Coord → ℝ}
        (S : FiniteModelBC1C2Source E D project)
        {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ)
        (A : ℕ → Set (ℕ → Coord → ℝ)),
        (∀ n, MeasurableSet (A n)) →
        (∀ n omega, omega ∈ A n ↔
          ¬ FiniteSubgradientAt
              (fun y : Coord → ℝ =>
                AppliedModelingLib.FiniteDimensionalNorms.l2
                  (fun i => y i - finiteModelBIdealSample n omega i))
              (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
              (l2BallDirection
                (finiteModelAL2OutcomeTrajectory D r0 project initial n omega)
                (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1)))) →
        ∃ C : ℝ, ∀ n,
          (finiteModelBIdealSequenceMeasure D)[
            (A n).indicator (fun _ => (1 : ℝ)) |
            finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
              finiteModelBIdealSequenceMeasure D]
            fun _ => C * ilvRadius r0 (n + 1)) ∧
    (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
        {E : ILVEnvironment Voter (Coord → ℝ)}
        {D : FiniteCoordinateIdealDistributionData Coord}
        {project : (Coord → ℝ) → Coord → ℝ}
        (S : FiniteModelBC1C2Source E D project)
        {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ)
        (A : ℕ → Set (ℕ → Coord → ℝ)),
        (∀ n, MeasurableSet (A n)) →
        (∀ n omega, omega ∈ A n ↔
          ¬ FiniteSubgradientAt
              (fun y : Coord → ℝ =>
                AppliedModelingLib.FiniteDimensionalNorms.l1
                  (fun i => y i - finiteModelBIdealSample n omega i))
              (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
              (l1LinfBallDirection
                (finiteModelAL1LinfOutcomeTrajectory D r0 project initial n omega)
                (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1)))) →
        ∃ C : ℝ, ∀ n,
          (finiteModelBIdealSequenceMeasure D)[
            (A n).indicator (fun _ => (1 : ℝ)) |
            finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
              finiteModelBIdealSequenceMeasure D]
            fun _ => C * ilvRadius r0 (n + 1)) ∧
    (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
        {E : ILVEnvironment Voter (Coord → ℝ)}
        {D : FiniteCoordinateIdealDistributionData Coord}
        {project : (Coord → ℝ) → Coord → ℝ}
        (S : FiniteModelBC1C2Source E D project)
        {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ)
        (A : ℕ → Set (ℕ → Coord → ℝ)),
        (∀ n, MeasurableSet (A n)) →
        (∀ n omega, omega ∈ A n ↔
          ¬ FiniteSubgradientAt
              (fun y : Coord → ℝ =>
                AppliedModelingLib.FiniteDimensionalNorms.linf
                  (fun i => y i - finiteModelBIdealSample n omega i))
              (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
              (linfL1RawDirection
                (finiteModelALinfL1OutcomeTrajectory D r0 project initial n omega)
                (finiteModelALinfL1OutcomeRawResponse r0
                  (finiteModelALinfL1OutcomeTrajectory D r0 project initial)
                  finiteModelBIdealSample n omega)
                (ilvRadius r0 (n + 1)))) →
        ∃ C : ℝ, ∀ n,
          (finiteModelBIdealSequenceMeasure D)[
            (A n).indicator (fun _ => (1 : ℝ)) |
            finiteModelBIdealNaturalFiltration (Coord := Coord) n] ≤ᵐ[
              finiteModelBIdealSequenceMeasure D]
            fun _ => C * ilvRadius r0 (n + 1))

/-- Appendix Lemma 2's direct conditional linear-in-radius source bound. -/
theorem appendix_lemma2_bad_event_linear_rate :
    appendix_lemma2_bad_event_linear_rateSpec := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro Voter Coord _ _ E D project S r0 hr0 initial A hAmeas hAfailure
    refine ⟨finiteModelBC1C2CoordinateSlabRealConstant S, ?_⟩
    intro n
    simpa only [mul_comm] using
      appendixLemma2_l2_sourceFailureEvent_condExp_le S hr0 initial n (A n)
        (hAmeas n) (hAfailure n)
  · intro Voter Coord _ _ E D project S r0 hr0 initial A hAmeas hAfailure
    refine ⟨finiteModelBC1C2CoordinateSlabRealConstant S, ?_⟩
    intro n
    simpa only [mul_comm] using
      appendixLemma2_l1Linf_sourceFailureEvent_condExp_le S hr0 initial n (A n)
        (hAmeas n) (hAfailure n)
  · intro Voter Coord _ _ E D project S r0 hr0 initial A hAmeas hAfailure
    refine ⟨finiteModelBC1C2CoordinateSlabRealConstant S +
      finiteModelBC1C2LinearTieSlabRealConstant S, ?_⟩
    intro n
    simpa only [mul_comm] using
      appendixLemma2_linfL1_sourceFailureEvent_condExp_le S hr0 initial n (A n)
        (hAmeas n) (hAfailure n)

/--
Proof-support envelope statement for Appendix Lemma 4.  The source-facing
`Spec` below names its actual weighted subgradient-failure event.
-/
private def appendixLemma4WeightedBadEventEnvelopeLinearRate : Prop :=
  ∀ {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : WeightedEuclideanJointSampleData Coord Component}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D.idealDistribution project)
    (A : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ) (n : ℕ),
    (∀ omega,
      (∀ k, 0 ≤ D.sampleWeight (AppliedModelingLib.iidSequenceSample n omega) k) →
        0 < D.sampleWeightNorm2 (AppliedModelingLib.iidSequenceSample n omega) →
          ¬ FiniteSubgradientAt
              (weightedEuclideanJointSampleCost D
                (AppliedModelingLib.iidSequenceSample n omega))
              (weightedEuclideanJointSampleModelAOutcomeTrajectory
                A r0 project initial n omega)
              (weightedEuclideanJointSampleModelARawDirection A
                (weightedEuclideanJointSampleModelAOutcomeTrajectory
                  A r0 project initial n omega)
                (ilvRadius r0 (n + 1))
                (AppliedModelingLib.iidSequenceSample n omega)) →
            AppliedModelingLib.iidSequenceSample n omega ∈
              weightedEuclideanJointSampleBlockBadEvent D
                (weightedEuclideanJointSampleModelAOutcomeTrajectory
                  A r0 project initial n omega)
                (ilvRadius r0 (n + 1))) ∧
      (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)[
        fun omega =>
          (weightedEuclideanJointSampleBlockBadEvent D
            (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0 project initial n omega)
            (ilvRadius r0 (n + 1))).indicator (fun _ => (1 : ℝ))
            (AppliedModelingLib.iidSequenceSample n omega) |
        AppliedModelingLib.iidSequenceNaturalFiltration
          (α := (Component → ℝ) × (Coord → ℝ)) n] ≤ᵐ[
            AppliedModelingLib.iidSequenceMeasure D.jointMeasure]
        fun _ => ilvRadius r0 (n + 1) *
          finiteModelBC1C2CoordinateSlabRealConstant S

/-- Envelope proof route for Appendix Lemma 4's direct source statement. -/
private theorem appendixLemma4_weightedBadEventEnvelopeLinearRate :
    appendixLemma4WeightedBadEventEnvelopeLinearRate := by
  intro Voter Coord Component _ _ _ E D project S A r0 hr0 initial n
  refine ⟨?_, weightedEuclideanJointSampleModelAOutcome_blockBadEvent_condExp_le
    S A hr0 initial n⟩
  intro omega hweight hweightNorm hfailure
  by_contra hbad
  exact hfailure
    (weightedEuclideanJointSampleModelARawDirection_subgradient_of_valid_of_notMem_blockBadEvent
      A (ilvRadius_succ_pos hr0 n) (AppliedModelingLib.iidSequenceSample n omega)
      hweight hweightNorm hbad)

/-- Proof bridge from Appendix Lemma 4's actual failure event to its envelope. -/
private theorem appendixLemma4_sourceFailureEvent_condExp_le
    {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : WeightedEuclideanJointSampleData Coord Component}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D.idealDistribution project)
    (Aresponse : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0)
    (initial : Coord → ℝ) (n : ℕ)
    (A : Set (ℕ → (Component → ℝ) × (Coord → ℝ)))
    (hAmeas : MeasurableSet A)
    (hAfailure : ∀ omega, omega ∈ A ↔
      ¬ FiniteSubgradientAt
          (weightedEuclideanJointSampleCost D
            (AppliedModelingLib.iidSequenceSample n omega))
          (weightedEuclideanJointSampleModelAOutcomeTrajectory
            Aresponse r0 project initial n omega)
          (weightedEuclideanJointSampleModelARawDirection Aresponse
            (weightedEuclideanJointSampleModelAOutcomeTrajectory
              Aresponse r0 project initial n omega)
            (ilvRadius r0 (n + 1))
            (AppliedModelingLib.iidSequenceSample n omega))) :
    (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)[
      A.indicator (fun _ => (1 : ℝ)) |
      AppliedModelingLib.iidSequenceNaturalFiltration
        (α := (Component → ℝ) × (Coord → ℝ)) n] ≤ᵐ[
        AppliedModelingLib.iidSequenceMeasure D.jointMeasure]
      fun _ => ilvRadius r0 (n + 1) *
        finiteModelBC1C2CoordinateSlabRealConstant S := by
  classical
  letI : IsProbabilityMeasure D.jointMeasure := D.probability
  letI : IsProbabilityMeasure (AppliedModelingLib.iidSequenceMeasure D.jointMeasure) :=
    AppliedModelingLib.iidSequenceMeasure_isProbabilityMeasure D.jointMeasure
  let radius : ℝ := ilvRadius r0 (n + 1)
  let B : Set (ℕ → (Component → ℝ) × (Coord → ℝ)) := {omega |
    AppliedModelingLib.iidSequenceSample n omega ∈
      weightedEuclideanJointSampleBlockBadEvent D
        (weightedEuclideanJointSampleModelAOutcomeTrajectory
          Aresponse r0 project initial n omega) radius}
  have htrajectory : Measurable
      (weightedEuclideanJointSampleModelAOutcomeTrajectory Aresponse r0 project initial n) :=
    (stronglyMeasurable_weightedEuclideanJointSampleModelAOutcomeTrajectory_natural
      Aresponse r0 project initial S.project_measurable n).measurable.mono
      ((AppliedModelingLib.iidSequenceNaturalFiltration
        (α := (Component → ℝ) × (Coord → ℝ))).le n) le_rfl
  have hpair : Measurable (fun omega : ℕ → (Component → ℝ) × (Coord → ℝ) =>
      (weightedEuclideanJointSampleModelAOutcomeTrajectory
        Aresponse r0 project initial n omega,
        AppliedModelingLib.iidSequenceSample n omega)) :=
    htrajectory.prodMk (AppliedModelingLib.measurable_iidSequenceSample n)
  have hBmeas : MeasurableSet B := by
    let event : Set ((Coord → ℝ) × ((Component → ℝ) × (Coord → ℝ))) :=
      {z | z.2 ∈ weightedEuclideanJointSampleBlockBadEvent D z.1 radius}
    have hevent : MeasurableSet event :=
      measurableSet_weightedEuclideanJointSampleBlockBadEvent_state_sample D radius
    simpa only [B, event] using hevent.preimage hpair
  have hweight : ∀ᵐ omega ∂AppliedModelingLib.iidSequenceMeasure D.jointMeasure,
      ∀ k, 0 ≤ D.sampleWeight (AppliedModelingLib.iidSequenceSample n omega) k := by
    have hmap : ∀ᵐ sample ∂Measure.map (AppliedModelingLib.iidSequenceSample n)
        (AppliedModelingLib.iidSequenceMeasure D.jointMeasure),
        ∀ k, 0 ≤ D.sampleWeight sample k := by
      rw [AppliedModelingLib.iidSequenceSample_law D.jointMeasure n]
      exact D.sampleWeight_nonnegative_ae
    exact MeasureTheory.ae_of_ae_map
      (AppliedModelingLib.measurable_iidSequenceSample n).aemeasurable hmap
  have hweightNorm : ∀ᵐ omega ∂AppliedModelingLib.iidSequenceMeasure D.jointMeasure,
      0 < D.sampleWeightNorm2 (AppliedModelingLib.iidSequenceSample n omega) := by
    have hmap : ∀ᵐ sample ∂Measure.map (AppliedModelingLib.iidSequenceSample n)
        (AppliedModelingLib.iidSequenceMeasure D.jointMeasure),
        0 < D.sampleWeightNorm2 sample := by
      rw [AppliedModelingLib.iidSequenceSample_law D.jointMeasure n]
      exact D.sampleWeightNorm2_pos_ae
    exact MeasureTheory.ae_of_ae_map
      (AppliedModelingLib.measurable_iidSequenceSample n).aemeasurable hmap
  have hsubset : ∀ᵐ omega ∂AppliedModelingLib.iidSequenceMeasure D.jointMeasure,
      omega ∈ A → omega ∈ B := by
    filter_upwards [hweight, hweightNorm] with omega hweightomega hnormomega hAomega
    by_contra hBomega
    exact (hAfailure omega).mp hAomega
      (weightedEuclideanJointSampleModelARawDirection_subgradient_of_valid_of_notMem_blockBadEvent
        Aresponse (ilvRadius_succ_pos hr0 n)
        (AppliedModelingLib.iidSequenceSample n omega) hweightomega hnormomega hBomega)
  calc
    (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)[
        A.indicator (fun _ => (1 : ℝ)) |
        AppliedModelingLib.iidSequenceNaturalFiltration
          (α := (Component → ℝ) × (Coord → ℝ)) n] ≤ᵐ[
          AppliedModelingLib.iidSequenceMeasure D.jointMeasure]
        (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)[
          B.indicator (fun _ => (1 : ℝ)) |
          AppliedModelingLib.iidSequenceNaturalFiltration
            (α := (Component → ℝ) × (Coord → ℝ)) n] :=
      condExp_indicator_le_of_ae_subset
        (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
        (AppliedModelingLib.iidSequenceNaturalFiltration
          (α := (Component → ℝ) × (Coord → ℝ)) n) hAmeas hBmeas hsubset
    _ ≤ᵐ[AppliedModelingLib.iidSequenceMeasure D.jointMeasure] fun _ =>
        ilvRadius r0 (n + 1) * finiteModelBC1C2CoordinateSlabRealConstant S := by
      simpa only [B, radius] using
        weightedEuclideanJointSampleModelAOutcome_blockBadEvent_condExp_le
          S Aresponse hr0 initial n

/--
Transparent semantic target for Appendix Lemma 4: its actual Definition-2
subgradient-failure event has a conditional probability of order `r_t`.
-/
def appendix_lemma4_weighted_bad_event_linear_rateSpec : Prop :=
  ∀ {Voter Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : WeightedEuclideanJointSampleData Coord Component}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D.idealDistribution project)
    (Aresponse : WeightedEuclideanJointSampleModelAResponseSource D)
    {r0 : ℝ} (hr0 : 0 < r0) (initial : Coord → ℝ)
    (A : ℕ → Set (ℕ → (Component → ℝ) × (Coord → ℝ))),
    (∀ n, MeasurableSet (A n)) →
    (∀ n omega, omega ∈ A n ↔
      ¬ FiniteSubgradientAt
          (weightedEuclideanJointSampleCost D
            (AppliedModelingLib.iidSequenceSample n omega))
          (weightedEuclideanJointSampleModelAOutcomeTrajectory
            Aresponse r0 project initial n omega)
          (weightedEuclideanJointSampleModelARawDirection Aresponse
            (weightedEuclideanJointSampleModelAOutcomeTrajectory
              Aresponse r0 project initial n omega)
            (ilvRadius r0 (n + 1))
            (AppliedModelingLib.iidSequenceSample n omega))) →
    ∃ C : ℝ, ∀ n,
      (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)[
        (A n).indicator (fun _ => (1 : ℝ)) |
        AppliedModelingLib.iidSequenceNaturalFiltration
          (α := (Component → ℝ) × (Coord → ℝ)) n] ≤ᵐ[
            AppliedModelingLib.iidSequenceMeasure D.jointMeasure]
        fun _ => C * ilvRadius r0 (n + 1)

/-- Appendix Lemma 4's direct conditional linear-in-radius source bound. -/
theorem appendix_lemma4_weighted_bad_event_linear_rate :
    appendix_lemma4_weighted_bad_event_linear_rateSpec := by
  intro Voter Coord Component _ _ _ E D project S Aresponse r0 hr0 initial A hAmeas hAfailure
  refine ⟨finiteModelBC1C2CoordinateSlabRealConstant S, ?_⟩
  intro n
  simpa only [mul_comm] using
    appendixLemma4_sourceFailureEvent_condExp_le S Aresponse hr0 initial n (A n)
      (hAmeas n) (hAfailure n)

/-- Source-facing finite-coordinate C3 formula for a concrete ideal-point law. -/
def finiteCoordinateC3CarrierFormula
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E) : Prop :=
  finiteCoordinateIdealDistributionFormulaData C3.data

/--
Exact source-facing C1--C2 surface for a concrete finite-coordinate run.
Euclidean projection and measurability are retained in the proof carrier, but
not presented here as if they were additional printed C1/C2 clauses.
-/
def finiteCoordinateC1C2SourceFormula
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D project) : Prop :=
  E.solutionSpace.Nonempty ∧
    IsClosed E.solutionSpace ∧
      Bornology.IsBounded E.solutionSpace ∧
        Convex ℝ E.solutionSpace ∧
          ∀ voter,
            E.ideal voter ∈ E.solutionSpace ∧
              (∀ x, x ∈ E.solutionSpace →
                E.utility voter x ≤ E.utility voter (E.ideal voter)) ∧
              ∀ x, x ∈ E.solutionSpace →
                E.utility voter x = E.utility voter (E.ideal voter) →
                  x = E.ideal voter

/-- The proof carrier supplies the exact C1--C2 source-facing surface. -/
theorem finiteCoordinateC1C2SourceFormula_of_source
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E D project) :
    finiteCoordinateC1C2SourceFormula S :=
  ⟨S.solutionSpace_nonempty, S.geometry.closed_solutionSpace,
    S.geometry.bounded_solutionSpace, S.geometry.convex_solutionSpace,
    S.ideal_is_unique_utility_maximizer⟩

/--
Complete source-facing Definition 2 data: the joint voter law, block
decomposition, and the displayed normalized weighted-Euclidean utility.
`weightedEuclideanJointSampleUtility` is the concrete one-voter formula used
by the Proposition 1 execution, rather than the older generic helper route.
-/
def weightedEuclideanJointSampleFormulaData
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) : Prop :=
  IsProbabilityMeasure D.jointMeasure ∧
    D.densityBound ≠ ⊤ ∧
      (∃ density : ((Component → ℝ) × (Coord → ℝ)) → ℝ≥0∞,
        Measurable density ∧
          D.jointMeasure =
            ((volume : Measure (Component → ℝ)).prod (volume : Measure (Coord → ℝ))).withDensity
              density ∧
            ∀ᵐ sample ∂((volume : Measure (Component → ℝ)).prod
              (volume : Measure (Coord → ℝ))), density sample ≤ D.densityBound) ∧
        Measure.map Prod.snd D.jointMeasure = D.idealDistribution.idealMeasure ∧
          D.weightSet.Nonempty ∧
            Bornology.IsBounded D.weightSet ∧
              IsClosed D.weightSet ∧
                Convex ℝ D.weightSet ∧
                  (∀ weight, weight ∈ D.weightSet → ∀ k, 0 ≤ weight k) ∧
                    (∀ᵐ sample ∂D.jointMeasure, sample.1 ∈ D.weightSet) ∧
                      (∀ᵐ sample ∂D.jointMeasure, sample.1 ≠ 0) ∧
                        (∀ k, (D.componentBlock k).Nonempty) ∧
                          (∀ k l, k ≠ l → Disjoint (D.componentBlock k) (D.componentBlock l)) ∧
                            (∀ i, ∃ k, i ∈ D.componentBlock k) ∧
                              ∀ sample state,
                                weightedEuclideanJointSampleUtility D sample state =
                                  -Finset.univ.sum (fun k =>
                                    (D.sampleWeight sample k / D.sampleWeightNorm2 sample) *
                                      finiteCoordinateBlockL2Distance
                                        (D.componentBlock k) state (D.sampleIdeal sample k))

/--
Complete source-facing Definition 3 formula for one utility family: every
coordinate utility is concave and their sum is the voter's utility.
-/
def decomposableUtilityFamilyFormulaData
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) : Prop :=
  (∀ coordinate voter, ConcaveOn ℝ Set.univ (D.coordinateUtility coordinate voter)) ∧
    ∀ voter x,
      E.utility voter x =
        D.coords.sum (fun coordinate =>
          D.coordinateUtility coordinate voter (D.coordinate coordinate x))

/-- Source-facing identification of the finite `Lp` population objective. -/
def finiteModelBLpSocialObjectiveSourceFormula
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord} {p : ℝ}
    (T : FiniteModelBLpSocialObjectiveSource E D p) : Prop :=
  (∀ x, E.societalUtility x = -finiteModelBExpectedLpCost D p x) ∧
    ∀ x, x ∈ E.socialOptimal ↔ x ∈ E.solutionSpace ∧
      IsMaxOn E.societalUtility E.solutionSpace x

/-- Source-facing identification of the finite `L∞` population objective. -/
def finiteModelBLinfSocialObjectiveSourceFormula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : FiniteCoordinateIdealDistributionData Coord}
    (T : FiniteModelBLinfSocialObjectiveSource E D) : Prop :=
  (∀ x, E.societalUtility x = -finiteModelBExpectedLinfCost D x) ∧
    ∀ x, x ∈ E.socialOptimal ↔ x ∈ E.solutionSpace ∧
      IsMaxOn E.societalUtility E.solutionSpace x

/-- The direct C1--C3 and social-objective source premises for a finite `Lp` run. -/
def finiteModelBLpSourceInputsFormula
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project) {p : ℝ}
    (T : FiniteModelBLpSocialObjectiveSource E C3.data p) : Prop :=
  finiteCoordinateC3CarrierFormula C3 ∧
    finiteModelBC1C2SourceFormula S ∧
      finiteModelBLpSocialObjectiveSourceFormula T

/-- The direct C1--C3 and social-objective source premises for a finite `L∞` run. -/
def finiteModelBLinfSourceInputsFormula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    (T : FiniteModelBLinfSocialObjectiveSource E C3.data) : Prop :=
  finiteCoordinateC3CarrierFormula C3 ∧
    finiteModelBC1C2SourceFormula S ∧
      finiteModelBLinfSocialObjectiveSourceFormula T

theorem finiteModelBLpSourceInputsFormula_of_sources
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project) {p : ℝ}
    (T : FiniteModelBLpSocialObjectiveSource E C3.data p) :
    finiteModelBLpSourceInputsFormula C3 S T :=
  ⟨⟨C3.data.probability, C3.data.densityBound_ne_top, C3.data.density_measurable⟩,
    S.finiteModelBC1C2SourceFormula,
    ⟨T.societalUtility_eq_neg_expectedLpCost,
      T.mem_socialOptimal_iff_societalUtility_isMaxOn⟩⟩

theorem finiteModelBLinfSourceInputsFormula_of_sources
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    (T : FiniteModelBLinfSocialObjectiveSource E C3.data) :
    finiteModelBLinfSourceInputsFormula C3 S T :=
  ⟨⟨C3.data.probability, C3.data.densityBound_ne_top, C3.data.density_measurable⟩,
    S.finiteModelBC1C2SourceFormula,
    ⟨T.societalUtility_eq_neg_expectedLinfCost,
      T.mem_socialOptimal_iff_societalUtility_isMaxOn⟩⟩

/-- The six finite-coordinate C1--C3 branches stated by Theorem 1. -/
def theorem1_finite_c3_six_casesSpec : Prop := by
  classical
  exact
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLpSocialObjectiveSource E C3.data 2,
        finiteModelBLpSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelAL2OutcomeTrajectory C3.data r0 project initial)) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLpSocialObjectiveSource E C3.data 2,
        finiteModelBLpSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelBOutcomeTrajectory C3.data 2 r0 project initial)) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLpSocialObjectiveSource E C3.data 1,
        finiteModelBLpSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLpSocialObjectiveSource E C3.data 1,
        finiteModelBLpSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLinfSocialObjectiveSource E C3.data,
        finiteModelBLinfSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelALinfL1OutcomeTrajectory C3.data r0 project initial)) ∧
  (∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (C3 : FiniteCoordinateC3Carrier E)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E C3.data project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : FiniteModelBLinfSocialObjectiveSource E C3.data,
        finiteModelBLinfSourceInputsFormula C3 S T ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelBLinfOutcomeTrajectory C3.data r0 project initial))

/-- Proof endpoint for the six concrete Theorem 1 branches. -/
theorem theorem1_finite_c3_six_cases : theorem1_finite_c3_six_casesSpec := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLpSourceInputsFormula_of_sources C3 S T,
      theorem1_modelA_l2_l2_finite_c3_convergence C3 S hr0 initial hinitial T⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLpSourceInputsFormula_of_sources C3 S T,
      theorem1_modelB_l2_l2_finite_c3_convergence C3 S hr0 initial hinitial T⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLpSourceInputsFormula_of_sources C3 S T,
      theorem1_modelA_l1_linf_finite_c3_convergence C3 S hr0 initial hinitial T⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLpSourceInputsFormula_of_sources C3 S T,
      theorem1_modelB_l1_linf_finite_c3_convergence C3 S hr0 initial hinitial T⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLinfSourceInputsFormula_of_sources C3 S T,
      theorem1_modelA_linf_l1_finite_c3_convergence C3 S hr0 initial hinitial T⟩
  · intro Voter Coord _ _ E C3 project S r0 hr0 initial hinitial T
    exact ⟨finiteModelBLinfSourceInputsFormula_of_sources C3 S T,
      theorem1_modelB_linf_l1_finite_c3_convergence C3 S hr0 initial hinitial T⟩

/-- The finite-exponent Holder-dual Model B endpoint stated by Theorem 2. -/
def theorem2_modelB_finite_holder_dual_c3Spec : Prop :=
  ∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {p q r0 : ℝ}, HolderDualFinite p q → 0 < r0 →
    ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
    ∀ T : FiniteModelBLpSocialObjectiveSource E C3.data p,
      finiteModelBLpSourceInputsFormula C3 S T ∧
        (∀ᵐ omega ∂finiteModelBIdealSequenceMeasure C3.data, ∀ n,
          ModelBFiniteResponseAt (SourceNorm.lp q)
            (finiteModelBOutcomeTrajectory C3.data p r0 project initial n omega)
            (ilvRadius r0 (n + 1))
            (fun i => -lpCostGradientCandidate p
              (fun j => finiteModelBOutcomeTrajectory C3.data p r0 project initial n omega j -
                finiteModelBIdealSample n omega j) i)
            (finiteModelBOutcomeRawResponse p r0
              (finiteModelBOutcomeTrajectory C3.data p r0 project initial)
              finiteModelBIdealSample n omega)) ∧
          @OutcomeIndexedILVConvergesToSocietalOptimal
            Voter (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance E
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelBOutcomeTrajectory C3.data p r0 project initial)

/-- Proof endpoint for the finite Holder-dual Theorem 2 contract. -/
theorem theorem2_modelB_finite_holder_dual_c3 :
    theorem2_modelB_finite_holder_dual_c3Spec := by
  intro Voter Coord _ _ E C3 project S p q r0 hdual hr0 initial hinitial T
  refine ⟨finiteModelBLpSourceInputsFormula_of_sources C3 S T, ?_,
    theorem2_modelB_finite_holder_dual_c3_convergence C3 S hdual hr0 initial hinitial T⟩
  exact finiteModelBOutcomeRawResponse_is_modelBResponse_ae_all
    C3.data hdual project initial S.project_measurable

/--
The source-facing behavior of a selected Model A response for one weighted
Euclidean sample.  The raw response is measurable and, for every valid
nonnegative nonzero weight vector, is a favorite point in the displayed raw
Euclidean query ball.  This keeps the selected tie-breaking rule visible in
Proposition 1 rather than treating its record name as a semantic premise.
-/
def weightedEuclideanJointSampleModelAResponseSourceFormula
    {Coord Component : Type*} [Fintype Coord] [Fintype Component] [Nonempty Coord]
    (D : WeightedEuclideanJointSampleData Coord Component)
    (A : WeightedEuclideanJointSampleModelAResponseSource D) : Prop :=
  (∀ radius, Measurable (fun z :
      (Coord → ℝ) × ((Component → ℝ) × (Coord → ℝ)) =>
      A.rawResponse z.1 z.2 radius)) ∧
    ∀ state radius sample, 0 < radius →
      (∀ k, 0 ≤ D.sampleWeight sample k) →
        0 < D.sampleWeightNorm2 sample →
          WeightedEuclideanJointSampleModelARawResponseAt D state radius sample
            (A.rawResponse state sample radius)

/-- The concrete Definition 2 joint-law Model A and Model B Proposition 1 endpoints. -/
def proposition1_weighted_euclidean_joint_c3Spec : Prop :=
  (∀ {Voter Coord Component : Type*}
      [Fintype Coord] [Fintype Component] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (D : WeightedEuclideanJointSampleData Coord Component)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E D.idealDistribution project)
      (A : WeightedEuclideanJointSampleModelAResponseSource D)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : WeightedEuclideanJointSampleSocialObjectiveSource E D,
        finiteModelBC1C2SourceFormula S ∧
          weightedEuclideanJointSampleModelAResponseSourceFormula D A ∧
            weightedEuclideanJointSamplePopulationMinimizerSet D E.solutionSpace =
              E.socialOptimal ∧
              @OutcomeIndexedILVConvergesToSocietalOptimal
                Voter (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
                inferInstance inferInstance E (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
                (weightedEuclideanJointSampleModelAOutcomeTrajectory A r0 project initial)) ∧
  (∀ {Voter Coord Component : Type*}
      [Fintype Coord] [Fintype Component] [Nonempty Coord]
      {E : ILVEnvironment Voter (Coord → ℝ)}
      (D : WeightedEuclideanJointSampleData Coord Component)
      {project : (Coord → ℝ) → Coord → ℝ}
      (S : FiniteModelBC1C2Source E D.idealDistribution project)
      {r0 : ℝ}, 0 < r0 →
      ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      ∀ T : WeightedEuclideanJointSampleSocialObjectiveSource E D,
        finiteModelBC1C2SourceFormula S ∧
          weightedEuclideanJointSamplePopulationMinimizerSet D E.solutionSpace =
            E.socialOptimal ∧
            @OutcomeIndexedILVConvergesToSocietalOptimal
              Voter (ℕ → (Component → ℝ) × (Coord → ℝ)) (Coord → ℝ)
              inferInstance inferInstance E (AppliedModelingLib.iidSequenceMeasure D.jointMeasure)
              (weightedEuclideanJointSampleOutcomeTrajectory D r0 project initial))

/-- Proof endpoint for both concrete Proposition 1 response models. -/
theorem proposition1_weighted_euclidean_joint_c3 :
    proposition1_weighted_euclidean_joint_c3Spec := by
  constructor
  · intro Voter Coord Component _ _ _ E D project S A r0 hr0 initial hinitial T
    refine ⟨S.finiteModelBC1C2SourceFormula,
      ⟨A.rawResponse_measurable, A.rawResponse_exact_of_valid⟩,
      T.minimizerSet_eq_socialOptimal, ?_⟩
    exact proposition1_weighted_euclidean_l2_modelA_joint_execution_convergence
      D S A hr0 initial hinitial T
  · intro Voter Coord Component _ _ _ E D project S r0 hr0 initial hinitial T
    refine ⟨S.finiteModelBC1C2SourceFormula, T.minimizerSet_eq_socialOptimal, ?_⟩
    exact weightedEuclideanJointSampleCanonicalMinimizerSetExecution_outcomeIndexedConvergesToSocialOptimal
      D S hr0 initial hinitial T

/--
Proposition 2 under the coordinatewise-boundary Model B clarification used by
its proof.  The displayed Model B trace moves every active coordinate by the
full `L∞` radius toward that coordinate of the sampled voter's ideal.  The
expected-`L1` minimizer set is the transparent feasible coordinatewise-median
target for this sign process, not a restriction that the paper's decomposable
utilities be spatial `L1`.  The proof's coordinatewise comparison is justified
by an explicit product-coordinate feasible-set condition; arbitrary convex
feasible sets do not suffice.  The canonical iid traces are also explicitly
identified as raw Model A responses for the sampled voters; this prevents the
convergence proof for the ideal-sampled sign process from floating separately
from the decomposable-utility execution stated in the proposition.
-/
def proposition2_coordinatewise_boundary_finite_c3_medianSpec : Prop :=
  ∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    (D : DecomposableStructure Voter (Coord → ℝ) Coord)
    (hdecomposable : IsDecomposableUtilitiesWith E D)
    (hcoords : D.coords = Finset.univ)
    (hcoordinate : ∀ m x, D.coordinate m x = x m)
    (hnorm : UsesFiniteCoordinateNormDistance E)
    (hproductBox : ∀ {x y : Coord → ℝ},
      x ∈ E.solutionSpace → y ∈ E.solutionSpace →
        ∀ m : Coord, ∃ replacement : Coord → ℝ,
          replacement ∈ E.solutionSpace ∧ replacement m = y m ∧
            ∀ l : Coord, l ≠ m → replacement l = x l)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ}, 0 < r0 →
    ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      (∃ sampledVoter : (Coord → ℝ) → Voter,
        (∀ᵐ ideal ∂C3.data.idealMeasure,
          E.ideal (sampledVoter ideal) = ideal) ∧
          (∀ᵐ omega ∂finiteModelBIdealSequenceMeasure C3.data, ∀ n,
            ModelARawResponseAt E SourceNorm.linfty
              (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial n omega)
              (ilvRadius r0 (n + 1))
              (sampledVoter (finiteModelBIdealSample n omega))
              (finiteModelAL1LinfOutcomeRawResponse r0
                (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
                finiteModelBIdealSample n omega))) →
      finiteCoordinateC3CarrierFormula C3 ∧
        finiteModelBC1C2SourceFormula S ∧
          (∃ sampledVoter : (Coord → ℝ) → Voter,
            (∀ᵐ ideal ∂C3.data.idealMeasure,
              E.ideal (sampledVoter ideal) = ideal) ∧
              (∀ᵐ omega ∂finiteModelBIdealSequenceMeasure C3.data, ∀ n,
                ModelARawResponseAt E SourceNorm.linfty
                  (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial n omega)
                  (ilvRadius r0 (n + 1))
                  (sampledVoter (finiteModelBIdealSample n omega))
                  (finiteModelAL1LinfOutcomeRawResponse r0
                    (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
                    finiteModelBIdealSample n omega))) ∧
          (∀ {center response : Coord → ℝ} {r : ℝ} {voter : Voter},
            ModelAResponseAt E SourceNorm.linfty center r voter response →
              ∀ m : Coord,
                IsMaxOn (fun z : ℝ => D.coordinateUtility m voter z)
                  {z | ∃ candidate,
                    candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                      D.coordinate m candidate = z}
                  (D.coordinate m response)) ∧
          (∀ n omega,
            ModelBCoordinatewiseBoundaryResponseAt
              (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial n omega)
              (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1))
              (finiteModelBOutcomeRawResponse 1 r0
                (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
                finiteModelBIdealSample n omega)) ∧
            @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
              (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance
              (finiteModelBIdealSequenceMeasure C3.data)
              (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
              (finiteModelBExpectedLpMinimizerSet C3.data 1 E.solutionSpace) ∧
            @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
              (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance
              (finiteModelBIdealSequenceMeasure C3.data)
              (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
              (finiteModelBExpectedLpMinimizerSet C3.data 1 E.solutionSpace)

/-- Proof endpoint for Proposition 2 under its coordinatewise Model B reading. -/
theorem proposition2_coordinatewise_boundary_finite_c3_median :
    proposition2_coordinatewise_boundary_finite_c3_medianSpec := by
  intro Voter Coord _ _ E C3 D hdecomposable hcoords hcoordinate hnorm hproductBox
    project S r0 hr0 initial hinitial hexecution
  refine ⟨⟨C3.data.probability, C3.data.densityBound_ne_top,
    C3.data.density_measurable⟩, S.finiteModelBC1C2SourceFormula, hexecution, ?_, ?_, ?_, ?_⟩
  · classical
    let R : FiniteCoordinateLinfCoordinateReplacementSource E D :=
      { normDistance := hnorm
        productBox :=
          { coordinate_update_mem_solutionSpace := by
              intro x y hx hy m
              obtain ⟨replacement, hmem, hm, hother⟩ := hproductBox hx hy m
              have hupdate : Function.update x m (y m) = replacement := by
                funext l
                by_cases hl : l = m
                · subst l
                  simp [hm]
                · simp [Function.update, hl, hother l hl]
              simpa [hupdate] using hmem }
        coordinate_eq := by
          intro m _ x
          exact hcoordinate m x }
    let B : DecomposableLinfLocalResponseBridge E D :=
      decomposableLinfLocalResponseBridge_of_coordinateReplacement hdecomposable
        (decomposableLinfCoordinateReplacement_of_finiteCoordinate R)
    intro center response r voter hresponse m
    exact B.coordinate_response_isMaxOn hresponse m (by simp [hcoords])
  · intro n omega
    exact finiteModelBOutcomeRawResponse_one_is_coordinatewiseBoundary
      r0 (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
      finiteModelBIdealSample n omega
  · exact finiteModelAL1LinfCanonicalPerturbedMinimizerSetExecution_outcomeIndexedConverges
      C3 S hr0 initial hinitial
  · exact finiteModelBCanonicalLpOneMinimizerSetExecution_outcomeIndexedConverges
      C3 S hr0 initial hinitial

/--
Convex-domain repair for Proposition 2.  C1 permits coupled feasible sets, so
the source's ambient coordinatewise median need not be feasible.  Retaining
the paper's exact sampled Model A execution premise and its proof's
coordinatewise-boundary Model B reading, the checked recursions converge on
every C1 domain to the minimizer set of expected `L1` distance restricted to
that feasible domain.  On a product domain this constrained target is the
ordinary coordinatewise median set used in the printed proposition.
-/
def proposition2_convex_domain_constrained_l1Spec : Prop :=
  ∀ {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C3 : FiniteCoordinateC3Carrier E)
    (D : DecomposableStructure Voter (Coord → ℝ) Coord)
    (hdecomposable : IsDecomposableUtilitiesWith E D)
    (hcoords : D.coords = Finset.univ)
    (hcoordinate : ∀ m x, D.coordinate m x = x m)
    (hnorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ}
    (S : FiniteModelBC1C2Source E C3.data project)
    {r0 : ℝ}, 0 < r0 →
    ∀ initial : Coord → ℝ, initial ∈ E.solutionSpace →
      (∃ sampledVoter : (Coord → ℝ) → Voter,
        (∀ᵐ ideal ∂C3.data.idealMeasure,
          E.ideal (sampledVoter ideal) = ideal) ∧
          (∀ᵐ omega ∂finiteModelBIdealSequenceMeasure C3.data, ∀ n,
            ModelARawResponseAt E SourceNorm.linfty
              (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial n omega)
              (ilvRadius r0 (n + 1))
              (sampledVoter (finiteModelBIdealSample n omega))
              (finiteModelAL1LinfOutcomeRawResponse r0
                (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
                finiteModelBIdealSample n omega))) →
      finiteCoordinateC3CarrierFormula C3 ∧
        finiteModelBC1C2SourceFormula S ∧
          (∃ sampledVoter : (Coord → ℝ) → Voter,
            (∀ᵐ ideal ∂C3.data.idealMeasure,
              E.ideal (sampledVoter ideal) = ideal) ∧
              (∀ᵐ omega ∂finiteModelBIdealSequenceMeasure C3.data, ∀ n,
                ModelARawResponseAt E SourceNorm.linfty
                  (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial n omega)
                  (ilvRadius r0 (n + 1))
                  (sampledVoter (finiteModelBIdealSample n omega))
                  (finiteModelAL1LinfOutcomeRawResponse r0
                    (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
                    finiteModelBIdealSample n omega))) ∧
          (∀ n omega,
            ModelBCoordinatewiseBoundaryResponseAt
              (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial n omega)
              (finiteModelBIdealSample n omega) (ilvRadius r0 (n + 1))
              (finiteModelBOutcomeRawResponse 1 r0
                (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
                finiteModelBIdealSample n omega)) ∧
          @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
            (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelAL1LinfOutcomeTrajectory C3.data r0 project initial)
            (finiteModelBExpectedLpMinimizerSet C3.data 1 E.solutionSpace) ∧
          @AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
            (ℕ → Coord → ℝ) (Coord → ℝ) inferInstance inferInstance
            (finiteModelBIdealSequenceMeasure C3.data)
            (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
            (finiteModelBExpectedLpMinimizerSet C3.data 1 E.solutionSpace)

/--
The C1-only recovery of Proposition 2's convergence argument.  It removes the
coordinate-replacement condition from the convergence proof and changes only
the infeasible ambient-median target to the constrained expected-`L1`
minimizer set.
-/
theorem proposition2_convex_domain_constrained_l1 :
    proposition2_convex_domain_constrained_l1Spec := by
  intro Voter Coord _ _ E C3 D hdecomposable hcoords hcoordinate hnorm project S r0 hr0 initial
    hinitial hexecution
  refine ⟨⟨C3.data.probability, C3.data.densityBound_ne_top,
    C3.data.density_measurable⟩, S.finiteModelBC1C2SourceFormula, hexecution, ?_, ?_, ?_⟩
  · intro n omega
    exact finiteModelBOutcomeRawResponse_one_is_coordinatewiseBoundary
      r0 (finiteModelBOutcomeTrajectory C3.data 1 r0 project initial)
      finiteModelBIdealSample n omega
  · exact finiteModelAL1LinfCanonicalPerturbedMinimizerSetExecution_outcomeIndexedConverges
      C3 S hr0 initial hinitial
  · exact finiteModelBCanonicalLpOneMinimizerSetExecution_outcomeIndexedConverges
      C3 S hr0 initial hinitial

end GKGMM19IterativeLocalVoting
