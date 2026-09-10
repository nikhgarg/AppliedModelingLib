import GKGMM19IterativeLocalVoting.MainTheorems
import AppliedModelingLib.Foundations.Optimization.ProjectedStochasticConvergence
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib
open scoped BigOperators MeasureTheory

/-!
# Paper Assumptions: Iterative Local Voting for Collective Decision-making in Continuous Spaces

This file is the only paper-local place for assumptions that are not derived in
Lean. Keep it small. Each declaration must be explicitly stated by the paper,
listed in `status.json` `review_surface.assumption_names`, and judged in
`assumption_match_llm.json` as a true source/model assumption rather than a
proof convenience.

Use `-- audit-premise: <exact Lean binder>` comments to route hidden theorem
premises to an approved assumption declaration when the audit reports an exact
binder string.

## Paper Assumptions

- `assumption_conditions_c123`: source assumptions C1, C2, and C3.
- `assumption_expected_subgradient_theorem`: a proved finite-coordinate,
  general-probability-space form of Appendix Theorem 4 with every
  integrability obligation explicit.

## Appendix 5 Bridge

`AppendixTheorem5Hypotheses` records the source's displayed stochastic
subgradient conditions. `AppendixTheorem5ExecutionRegularity` makes the
measurability and integrability needed by its conditional expectations
explicit, and builds the reusable projected stochastic-subgradient execution
whose convergence theorem proves the Appendix 5 conclusion.
-/

namespace GKGMM19IterativeLocalVoting

/-!
Conditional-error component for the adapted-bias reading of Appendix
Theorem 5.  This is deliberately separate from convergence: an a.s. norm
envelope must first be converted into the conditional descent-error bound
consumed by the reusable perturbation API.
-/
theorem condExp_randomBiasError_le_of_ae_norm_le
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord]
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (m : MeasurableSpace Omega) (hm : m ≤ mOmega)
    (bias : Omega → Coord → ℝ) (radius distanceBound bound : ℝ)
    (hradius : 0 ≤ radius) (hdistance : 0 ≤ distanceBound)
    (hbound : 0 ≤ bound)
    (h_integrable : Integrable
      (fun omega =>
        2 * radius * distanceBound * FiniteDimensionalNorms.l2 (bias omega) +
          3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (bias omega)) mu)
    (hae : ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (bias omega) ≤ bound) :
    mu[fun omega =>
      2 * radius * distanceBound * FiniteDimensionalNorms.l2 (bias omega) +
        3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (bias omega) | m] ≤ᵐ[mu]
      fun _ => 2 * radius * distanceBound * bound + 3 * radius ^ 2 * bound ^ 2 := by
  have hpoint : (fun omega =>
      2 * radius * distanceBound * FiniteDimensionalNorms.l2 (bias omega) +
        3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (bias omega)) ≤ᵐ[mu]
      fun _ => 2 * radius * distanceBound * bound + 3 * radius ^ 2 * bound ^ 2 := by
    filter_upwards [hae] with omega homega
    have hsq : FiniteDimensionalNorms.l2Sq (bias omega) ≤ bound ^ 2 := by
      rw [← FiniteDimensionalNorms.normL2_sq_eq_normL2Sq]
      exact (sq_le_sq₀ (FiniteDimensionalNorms.normL2_nonneg _) hbound).mpr homega
    have hcoef1 : 0 ≤ 2 * radius * distanceBound := by positivity
    have hcoef2 : 0 ≤ 3 * radius ^ 2 := by positivity
    nlinarith [FiniteDimensionalNorms.normL2_nonneg (bias omega),
      FiniteDimensionalNorms.normL2Sq_nonneg (bias omega)]
  calc
    mu[fun omega =>
        2 * radius * distanceBound * FiniteDimensionalNorms.l2 (bias omega) +
          3 * radius ^ 2 * FiniteDimensionalNorms.l2Sq (bias omega) | m] ≤ᵐ[mu]
        mu[fun _ : Omega =>
          2 * radius * distanceBound * bound + 3 * radius ^ 2 * bound ^ 2 | m] :=
      condExp_mono h_integrable (integrable_const _) hpoint
    _ =ᵐ[mu] fun _ =>
        2 * radius * distanceBound * bound + 3 * radius ^ 2 * bound ^ 2 := by
      exact Filter.Eventually.of_forall fun omega =>
        congrFun (condExp_const (μ := mu) (m₀ := mOmega) hm
          (2 * radius * distanceBound * bound + 3 * radius ^ 2 * bound ^ 2)) omega

/--
The pathwise scalar-series bridge for an adapted random bias.  It combines
almost-sure summability of the linear step--bias term with square-summability
of the step sizes and an a.s. uniform bias envelope.  No convergence claim is
made here; this is the error-budget input for the perturbation endpoint.
-/
theorem ae_summable_randomBiasError_of_ae_summable_step
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} [Fintype Coord]
    (mu : @Measure Omega mOmega) (radius : ℕ → ℝ) (bias : Omega → ℕ → Coord → ℝ)
    (distanceBound bound : ℝ)
    (hradius_sq : Summable (fun n => radius (n + 1) ^ 2))
    (hbound : 0 ≤ bound)
    (hstep_bias : ∀ᵐ omega ∂mu,
      Summable (fun n => radius (n + 1) *
        FiniteDimensionalNorms.l2 (bias omega n)))
    (hae_bound : ∀ᵐ omega ∂mu, ∀ n,
      FiniteDimensionalNorms.l2 (bias omega n) ≤ bound) :
    ∀ᵐ omega ∂mu,
      Summable (fun n =>
        2 * radius (n + 1) * distanceBound *
            FiniteDimensionalNorms.l2 (bias omega n) +
          3 * radius (n + 1) ^ 2 *
            FiniteDimensionalNorms.l2Sq (bias omega n)) := by
  filter_upwards [hstep_bias, hae_bound] with omega hstep hboundω
  have hlinear : Summable (fun n =>
      2 * radius (n + 1) * distanceBound *
        FiniteDimensionalNorms.l2 (bias omega n)) := by
    convert hstep.mul_left (2 * distanceBound) using 1
    ext n
    ring
  have hquadBound : Summable (fun n =>
      3 * bound ^ 2 * radius (n + 1) ^ 2) :=
    hradius_sq.mul_left (3 * bound ^ 2)
  have hquad : Summable (fun n =>
      3 * radius (n + 1) ^ 2 *
        FiniteDimensionalNorms.l2Sq (bias omega n)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (radius (n + 1))))
        (FiniteDimensionalNorms.normL2Sq_nonneg _)
    · intro n
      have hsq : FiniteDimensionalNorms.l2Sq (bias omega n) ≤ bound ^ 2 := by
        rw [← FiniteDimensionalNorms.normL2_sq_eq_normL2Sq]
        exact (sq_le_sq₀ (FiniteDimensionalNorms.normL2_nonneg _) hbound).mpr
          (hboundω n)
      calc
        3 * radius (n + 1) ^ 2 *
              FiniteDimensionalNorms.l2Sq (bias omega n) ≤
            3 * radius (n + 1) ^ 2 * bound ^ 2 :=
          mul_le_mul_of_nonneg_left hsq
            (mul_nonneg (by norm_num) (sq_nonneg (radius (n + 1))))
        _ = 3 * bound ^ 2 * radius (n + 1) ^ 2 := by ring
    · exact hquadBound
  convert hlinear.add hquad using 1

/--
Source assumptions C1, C2, and C3 from Section 3:
nonempty bounded closed convex solution space, unique ideal points, and a
bounded measurable density for independently drawn ideal points.
-/
-- audit-premise: hC : assumption_conditions_c123 E
abbrev assumption_conditions_c123 {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  E.solutionSpace_nonempty_bounded_closed_convex ∧
    E.uniqueIdealSolutions ∧
      E.idealDistribution_bounded_measurable_density

/--
Finite-coordinate subgradient inequality restricted to a feasible set.

This is the shared projected-subgradient API; the paper-local name is retained
only to keep the Appendix 4 and 5 source interfaces readable.
-/
abbrev FiniteSubgradientWithinAt
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (solutionSpace : Set (Coord → ℝ))
    (x g : Coord → ℝ) : Prop :=
  AppliedModelingLib.Optimization.FiniteSubgradientOn cost solutionSpace x g

/-- Appendix Theorem 4's expected objective and expected selected gradient. -/
def ExpectedSubgradientTheoremStatement
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta)
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ) : Prop :=
  FiniteSubgradientWithinAt
    (fun y => ∫ theta, sampleCost theta y ∂mu)
    solutionSpace
    x
    (fun i => ∫ theta, sampleGradient theta i ∂mu)

/--
Finite-coordinate, measure-theoretic form of Appendix Theorem 4.  The two
integrability hypotheses are the formal content of the paper's requirement
that the displayed expectations be well-defined.  The proof integrates the
sample subgradient inequality and commutes a finite coordinate sum with the
integral.
-/
theorem assumption_expected_subgradient_theorem
    {Theta Coord : Type*} [MeasurableSpace Theta] [Fintype Coord]
    (mu : Measure Theta) [IsProbabilityMeasure mu]
    (solutionSpace : Set (Coord → ℝ))
    (sampleCost : Theta → (Coord → ℝ) → ℝ)
    (x : Coord → ℝ) (sampleGradient : Theta → Coord → ℝ)
    (_hX_nonempty : solutionSpace.Nonempty)
    (_hX_bounded : Bornology.IsBounded solutionSpace)
    (_hX_closed : IsClosed solutionSpace)
    (_hX_convex : Convex ℝ solutionSpace)
    (_hx : x ∈ solutionSpace)
    (hcost_integrable :
      ∀ y, y ∈ solutionSpace →
        Integrable (fun theta => sampleCost theta y) mu)
    (hgradient_integrable :
      ∀ i, Integrable (fun theta => sampleGradient theta i) mu)
    (_hsample_convex :
      ∀ theta, ConvexOn ℝ solutionSpace (sampleCost theta))
    (_hexpected_continuous :
      ContinuousAt (fun y => ∫ theta, sampleCost theta y ∂mu) x)
    (hsample :
      ∀ theta,
        FiniteSubgradientWithinAt
          (sampleCost theta) solutionSpace x (sampleGradient theta)) :
    ExpectedSubgradientTheoremStatement
      mu solutionSpace sampleCost x sampleGradient := by
  intro y hy
  let d : Coord → ℝ := fun i => y i - x i
  have hlinear_integrable :
      Integrable
        (fun theta =>
          AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient theta) d) mu := by
    simp_rw [coordinateLinearFunctional_apply]
    exact MeasureTheory.integrable_finset_sum Finset.univ (by
      intro i _hi
      exact (hgradient_integrable i).mul_const (d i))
  have hlinear_integral :
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => ∫ theta, sampleGradient theta i ∂mu) d =
        ∫ theta,
          AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
            (sampleGradient theta) d ∂mu := by
    simp_rw [coordinateLinearFunctional_apply]
    rw [MeasureTheory.integral_finset_sum]
    · simp_rw [MeasureTheory.integral_mul_const]
    · intro i _hi
      exact (hgradient_integrable i).mul_const (d i)
  rw [hlinear_integral]
  rw [← MeasureTheory.integral_add
    (hcost_integrable x _hx) hlinear_integrable]
  apply MeasureTheory.integral_mono_ae
  · exact (hcost_integrable x _hx).add hlinear_integrable
  · exact hcost_integrable y hy
  · exact Filter.Eventually.of_forall (fun theta => hsample theta y hy)

/--
Concrete source-shaped statement of Appendix Theorem 5. It exposes the
probability space, filtration, bounded closed convex feasible set, convex
objective with a unique minimizer, projected update, step sizes, subgradients,
conditional mean-zero noise, conditional bounded second moments, bounded bias,
and almost-sure summability before concluding almost-sure convergence.
-/
structure AppendixTheorem5Hypotheses
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) : Prop where
  solutionSpace_nonempty : solutionSpace.Nonempty
  solutionSpace_bounded : Bornology.IsBounded solutionSpace
  solutionSpace_closed : IsClosed solutionSpace
  solutionSpace_convex : Convex ℝ solutionSpace
  objective_convex : ConvexOn ℝ solutionSpace objective
  target_mem_solutionSpace : xstar ∈ solutionSpace
  target_minimizes : IsMinOn objective solutionSpace xstar
  target_unique : ∀ y, y ∈ solutionSpace → objective y = objective xstar → y = xstar
  step_sizes : SSGMStepSizeConditions radius
  closest_point_projection : ∀ y,
    project y ∈ solutionSpace ∧
      IsMinOn
        (fun x => finiteCoordinateDistance SourceNorm.l2 x y)
        solutionSpace (project y)
  update : ∀ t, ∀ᵐ omega ∂mu,
    trajectory (t + 1) omega =
      project (fun i =>
        trajectory t omega i -
          radius (t + 1) *
            (meanSubgradient t omega i + noise t omega i + bias t i))
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun t omega => trajectory t omega i)
  mean_subgradient_adapted : ∀ i,
    StronglyAdapted filtration (fun t omega => meanSubgradient t omega i)
  trajectory_subgradient : ∀ t, ∀ᵐ omega ∂mu,
    trajectory t omega ∈ solutionSpace ∧
      FiniteSubgradientWithinAt objective solutionSpace (trajectory t omega)
        (meanSubgradient t omega)
  bounded_subgradients : ∃ C1 : ℝ, 0 ≤ C1 ∧
    ∀ x, x ∈ solutionSpace → ∀ g,
      FiniteSubgradientWithinAt objective solutionSpace x g →
        finiteCoordinateNorm SourceNorm.l2 g ≤ C1
  noise_coordinate_integrable : ∀ t i,
    Integrable (fun omega => noise t omega i) mu
  noise_mean_zero : ∀ t i,
    mu[fun omega => noise t omega i | filtration t] =ᵐ[mu] 0
  noise_energy_integrable : ∀ t,
    Integrable (fun omega =>
      finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2) mu
  bounded_noise_energy : ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ t,
    mu[fun omega =>
      finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2 | filtration t]
        ≤ᵐ[mu] fun _ => C2
  bounded_bias : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ t,
    finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ C3
  step_bias_summable : Summable (fun t =>
    radius (t + 1) * finiteCoordinateNorm SourceNorm.l2 (bias t))

/-- The exact source-shaped implication recorded as Appendix Theorem 5. -/
def AppendixTheorem5Statement
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
  AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
    trajectory meanSubgradient noise bias radius xstar →
    ∀ᵐ omega ∂mu,
      Tendsto (fun t => trajectory t omega) atTop (nhds xstar)

/--
The minimizer-set replacement for Appendix Theorem 5.  The printed theorem
assumes a unique minimizer, but the main-text `L1`/median applications need
only convergence to the (possibly non-singleton) set of minimizers.  This
record states the same projected stochastic-subgradient hypotheses with the
target identification made set-valued; it contains no convergence conclusion.
-/
structure AppendixTheorem5MinimizerSetHypotheses
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ) : Prop where
  solutionSpace_nonempty : solutionSpace.Nonempty
  solutionSpace_bounded : Bornology.IsBounded solutionSpace
  solutionSpace_closed : IsClosed solutionSpace
  solutionSpace_convex : Convex ℝ solutionSpace
  objective_convex : ConvexOn ℝ solutionSpace objective
  reference_mem_targetSet : reference ∈ targetSet
  targetSet_subset_solutionSpace : targetSet ⊆ solutionSpace
  targetSet_minimizes : ∀ target, target ∈ targetSet →
    IsMinOn objective solutionSpace target
  minimizer_mem_targetSet : ∀ x, x ∈ solutionSpace →
    IsMinOn objective solutionSpace x → x ∈ targetSet
  step_sizes : SSGMStepSizeConditions radius
  closest_point_projection : ∀ y,
    project y ∈ solutionSpace ∧
      IsMinOn
        (fun x => finiteCoordinateDistance SourceNorm.l2 x y)
        solutionSpace (project y)
  update : ∀ t, ∀ᵐ omega ∂mu,
    trajectory (t + 1) omega =
      project (fun i =>
        trajectory t omega i -
          radius (t + 1) *
            (meanSubgradient t omega i + noise t omega i + bias t i))
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun t omega => trajectory t omega i)
  trajectory_subgradient : ∀ t, ∀ᵐ omega ∂mu,
    trajectory t omega ∈ solutionSpace ∧
      FiniteSubgradientWithinAt objective solutionSpace (trajectory t omega)
        (meanSubgradient t omega)
  bounded_subgradients : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x, x ∈ solutionSpace → ∀ g,
      FiniteSubgradientWithinAt objective solutionSpace x g →
        finiteCoordinateNorm SourceNorm.l2 g ≤ C
  noise_coordinate_integrable : ∀ t i,
    Integrable (fun omega => noise t omega i) mu
  noise_mean_zero : ∀ t i,
    mu[fun omega => noise t omega i | filtration t] =ᵐ[mu] 0
  noise_energy_integrable : ∀ t,
    Integrable (fun omega =>
      finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2) mu
  bounded_noise_energy : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
    mu[fun omega =>
      finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2 | filtration t]
        ≤ᵐ[mu] fun _ => C
  bounded_bias : ∃ C : ℝ, 0 ≤ C ∧ ∀ t,
    finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ C
  step_bias_summable : Summable (fun t =>
    radius (t + 1) * finiteCoordinateNorm SourceNorm.l2 (bias t))

/--
Regularity hypotheses for the minimizer-set replacement.  Conditional
expectation, potential, and integrability facts are target-dependent because
the corrected conclusion ranges over all social optima, not a preselected one.
-/
structure AppendixTheorem5MinimizerSetRegularity
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ) where
  target_objective_gap_adapted : ∀ target, target ∈ targetSet →
    StronglyAdapted filtration
      (fun t omega => objective (trajectory t omega) - objective target)
  target_potential_integrable : ∀ target, target ∈ targetSet → ∀ t, Integrable
    (fun omega => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => trajectory t omega i - target i)) mu
  target_objective_gap_integrable : ∀ target, target ∈ targetSet → ∀ t, Integrable
    (fun omega => objective (trajectory t omega) - objective target) mu
  target_noise_product_integrable : ∀ target, target ∈ targetSet → ∀ t i, Integrable
    (fun omega => (trajectory t omega i - target i) * noise t omega i) mu
  target_distanceBound : (Coord → ℝ) → ℝ
  target_distanceBound_nonneg : ∀ target, target ∈ targetSet →
    0 ≤ target_distanceBound target
  target_distance_bound : ∀ target, target ∈ targetSet → ∀ t, ∀ᵐ omega ∂mu,
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => trajectory t omega i - target i) ≤ target_distanceBound target
  subgradient_exists : ∀ x, x ∈ solutionSpace → ∃ g,
    FiniteSubgradientWithinAt objective solutionSpace x g

/--
The corrected Appendix Theorem 5 conclusion: each sample path converges to
some objective minimizer.  This is the conclusion needed by the set-valued
main-text results, including the median branch.
-/
def AppendixTheorem5MinimizerSetStatement
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
  AppendixTheorem5MinimizerSetHypotheses mu filtration solutionSpace targetSet
    objective project trajectory meanSubgradient noise bias radius reference →
  AppendixTheorem5MinimizerSetRegularity mu filtration solutionSpace targetSet
    objective project trajectory meanSubgradient noise bias radius reference →
  AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet mu trajectory targetSet

/--
Build the reusable minimizer-set execution from the corrected Appendix 5
source conditions.  In particular, this construction has no uniqueness field
and no stored convergence result.
-/
noncomputable def AppendixTheorem5MinimizerSetRegularity.toProjectedSSGMExecution
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ)
    (h : AppendixTheorem5MinimizerSetHypotheses mu filtration solutionSpace targetSet
      objective project trajectory meanSubgradient noise bias radius reference)
    (R : AppendixTheorem5MinimizerSetRegularity mu filtration solutionSpace targetSet
      objective project trajectory meanSubgradient noise bias radius reference) :
    AppliedModelingLib.Optimization.ProjectedStochasticSubgradientMinimizerSetExecution Coord := by
  letI := mOmega
  have hproject :
      AppliedModelingLib.Optimization.SquaredDistanceNonexpansiveOn solutionSpace project := by
    apply AppliedModelingLib.Optimization.euclideanProjection_squaredDistanceNonexpansive
      h.solutionSpace_convex
    intro y
    simpa [AppliedModelingLib.Optimization.EuclideanProjectionOnto,
      finiteCoordinateDistance, finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.l2] using h.closest_point_projection y
  have hcompact : IsCompact solutionSpace :=
    AppliedModelingLib.FiniteDimensionalNorms.isCompact_of_isClosed_of_bounded
      h.solutionSpace_closed h.solutionSpace_bounded
  let C : ℝ := Classical.choose h.bounded_subgradients
  have hC : 0 ≤ C ∧ ∀ x, x ∈ solutionSpace → ∀ g,
      FiniteSubgradientWithinAt objective solutionSpace x g →
        finiteCoordinateNorm SourceNorm.l2 g ≤ C :=
    Classical.choose_spec h.bounded_subgradients
  let noiseBound : ℝ := Classical.choose h.bounded_noise_energy
  have hnoiseBound : 0 ≤ noiseBound ∧ ∀ t,
      mu[fun omega => finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2
        | filtration t] ≤ᵐ[mu] fun _ => noiseBound :=
    Classical.choose_spec h.bounded_noise_energy
  let biasBound : ℝ := Classical.choose h.bounded_bias
  have hbiasBound : 0 ≤ biasBound ∧ ∀ t,
      finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ biasBound :=
    Classical.choose_spec h.bounded_bias
  refine
    { Ω := Omega
      measurableSpace := mOmega
      μ := mu
      probability := inferInstance
      filtration := filtration
      trajectory := trajectory
      meanSubgradient := meanSubgradient
      noise := noise
      bias := bias
      radius := radius
      solutionSpace := solutionSpace
      objective := objective
      project := project
      targetSet := targetSet
      reference := reference
      reference_mem_targetSet := h.reference_mem_targetSet
      targetSet_subset_solutionSpace := h.targetSet_subset_solutionSpace
      targetSet_minimizes := h.targetSet_minimizes
      minimizer_mem_targetSet := h.minimizer_mem_targetSet
      project_nonexpansive := hproject
      trajectory_adapted := h.trajectory_adapted
      target_objective_gap_adapted := R.target_objective_gap_adapted
      target_potential_integrable := R.target_potential_integrable
      target_objective_gap_integrable := R.target_objective_gap_integrable
      target_noise_product_integrable := R.target_noise_product_integrable
      noise_coordinate_integrable := h.noise_coordinate_integrable
      noise_mean_zero := h.noise_mean_zero
      noise_energy_integrable := ?_
      C := C
      noiseBound := noiseBound
      target_distanceBound := R.target_distanceBound
      C_nonneg := hC.1
      noiseBound_nonneg := hnoiseBound.1
      target_distanceBound_nonneg := R.target_distanceBound_nonneg
      noise_energy_bound := ?_
      update := h.update
      subgradient := ?_
      gradient_bound := ?_
      target_distance_bound := R.target_distance_bound
      radius_nonneg := ?_
      biasBound := biasBound
      biasBound_nonneg := hbiasBound.1
      bias_bound := hbiasBound.2
      step_bias_summable := ?_
      radius_sq_summable := h.step_sizes.2.1
      radius_diverges := h.step_sizes.2.2
      trajectory_mem_solutionSpace := ?_
      compact_solutionSpace := hcompact
      objective_continuous := ?_ }
  · intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using
      h.noise_energy_integrable t
  · intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using hnoiseBound.2 t
  · intro t
    filter_upwards [h.trajectory_subgradient t] with omega htrajectory
    exact htrajectory.2
  · intro t
    filter_upwards [h.trajectory_subgradient t] with omega htrajectory
    exact hC.2 (trajectory t omega) htrajectory.1
      (meanSubgradient t omega) htrajectory.2
  · intro t
    exact le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t))
  · simpa [finiteCoordinateNorm, SourceNorm.l2] using h.step_bias_summable
  · exact ae_all_iff.2 fun t =>
      (h.trajectory_subgradient t).mono fun _ htrajectory => htrajectory.1
  · apply AppliedModelingLib.Optimization.continuousOn_of_exists_bounded_subgradientOn hC.1
    intro x hx
    rcases R.subgradient_exists x hx with ⟨g, hg⟩
    exact ⟨g, hg, hC.2 x hx g hg⟩

/-- The corrected Appendix 5 assumptions imply convergence to the full minimizer set. -/
theorem AppendixTheorem5MinimizerSetRegularity.outcomeIndexed_convergesToSet
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace targetSet : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (reference : Coord → ℝ)
    (h : AppendixTheorem5MinimizerSetHypotheses mu filtration solutionSpace targetSet
      objective project trajectory meanSubgradient noise bias radius reference)
    (R : AppendixTheorem5MinimizerSetRegularity mu filtration solutionSpace targetSet
      objective project trajectory meanSubgradient noise bias radius reference) :
    AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  let S := R.toProjectedSSGMExecution mu filtration solutionSpace targetSet objective project
    trajectory meanSubgradient noise bias radius reference h
  convert S.outcomeIndexedConvergesToSet using 1

/--
The closed/bounded/convex feasible-set and closest-point-projection portion of
Appendix Theorem 5 is exactly the reusable Euclidean projection geometry.
-/
theorem AppendixTheorem5Hypotheses.euclideanProjectionSourceGeometry
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar) :
    AppliedModelingLib.Optimization.EuclideanProjectionSourceGeometry
      Coord solutionSpace project := by
  refine
    { closed_solutionSpace := h.solutionSpace_closed
      bounded_solutionSpace := h.solutionSpace_bounded
      convex_solutionSpace := h.solutionSpace_convex
      closest_point_projection := ?_ }
  intro y
  simpa [finiteCoordinateDistance, finiteCoordinateNorm, SourceNorm.l2,
    AppliedModelingLib.FiniteDimensionalNorms.l2] using h.closest_point_projection y

/-- Appendix Theorem 5's closest-point projection is nonexpansive in the
squared Euclidean distance used by the reusable stochastic descent theorem. -/
theorem AppendixTheorem5Hypotheses.project_nonexpansive
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar) :
    AppliedModelingLib.Optimization.SquaredDistanceNonexpansiveOn solutionSpace project :=
  h.euclideanProjectionSourceGeometry mu filtration solutionSpace objective project
    trajectory meanSubgradient noise bias radius xstar |>.squaredDistance_nonexpansive

/-- A finite-coordinate Appendix Theorem 5 feasible set is compact. -/
theorem AppendixTheorem5Hypotheses.compact_solutionSpace
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar) :
    IsCompact solutionSpace :=
  h.euclideanProjectionSourceGeometry mu filtration solutionSpace objective project
    trajectory meanSubgradient noise bias radius xstar |>.compact_solutionSpace

/--
Measurability and integrability data needed to interpret Appendix Theorem 5 on
an actual probability space.  The printed theorem uses conditional
expectations and almost-sure statements, so these are its standard
well-definedness conditions made explicit for Lean.  They are separate from
the displayed analytic bounds in `AppendixTheorem5Hypotheses` and contain no
convergence conclusion.
-/
structure AppendixTheorem5ExecutionRegularity
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) where
  objective_gap_adapted : StronglyAdapted filtration
    (fun t omega => objective (trajectory t omega) - objective xstar)
  potential_integrable : ∀ t, Integrable
    (fun omega => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => trajectory t omega i - xstar i)) mu
  objective_gap_integrable : ∀ t, Integrable
    (fun omega => objective (trajectory t omega) - objective xstar) mu
  noise_product_integrable : ∀ t i, Integrable
    (fun omega => (trajectory t omega i - xstar i) * noise t omega i) mu
  distanceBound : ℝ
  distanceBound_nonneg : 0 ≤ distanceBound
  distance_bound : ∀ t, ∀ᵐ omega ∂mu,
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => trajectory t omega i - xstar i) ≤ distanceBound
  subgradient_exists : ∀ x, x ∈ solutionSpace → ∃ g,
    FiniteSubgradientWithinAt objective solutionSpace x g

/--
The source-facing Appendix Theorem 5 conditions and their explicit
well-definedness data instantiate the reusable projected stochastic
subgradient execution.  This is a source-to-library bridge only: the
almost-sure convergence result itself is supplied by the generic library
theorem for the resulting execution.
-/
noncomputable def AppendixTheorem5ExecutionRegularity.toProjectedSSGMExecution
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5ExecutionRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar) :
    AppliedModelingLib.Optimization.ProjectedStochasticSubgradientExecution Coord := by
  letI := mOmega
  have hproject_nonexpansive :=
    h.project_nonexpansive mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar
  have hcompact :=
    h.compact_solutionSpace mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar
  let C1 : ℝ := Classical.choose h.bounded_subgradients
  have hC1 : 0 ≤ C1 ∧ ∀ x, x ∈ solutionSpace → ∀ g,
      FiniteSubgradientWithinAt objective solutionSpace x g →
        finiteCoordinateNorm SourceNorm.l2 g ≤ C1 :=
    Classical.choose_spec h.bounded_subgradients
  let C2 : ℝ := Classical.choose h.bounded_noise_energy
  have hC2 : 0 ≤ C2 ∧ ∀ t,
      mu[fun omega => finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2
        | filtration t] ≤ᵐ[mu] fun _ => C2 :=
    Classical.choose_spec h.bounded_noise_energy
  let biasBound : ℝ := Classical.choose h.bounded_bias
  have hbias : 0 ≤ biasBound ∧ ∀ t,
      finiteCoordinateNorm SourceNorm.l2 (bias t) ≤ biasBound :=
    Classical.choose_spec h.bounded_bias
  refine
    { Ω := Omega
      measurableSpace := mOmega
      μ := mu
      probability := inferInstance
      filtration := filtration
      trajectory := trajectory
      meanSubgradient := meanSubgradient
      noise := noise
      bias := bias
      radius := radius
      solutionSpace := solutionSpace
      objective := objective
      project := project
      target := xstar
      target_mem_solutionSpace := h.target_mem_solutionSpace
      project_nonexpansive := hproject_nonexpansive
      trajectory_adapted := h.trajectory_adapted
      objective_gap_adapted := R.objective_gap_adapted
      potential_integrable := R.potential_integrable
      objective_gap_integrable := R.objective_gap_integrable
      noise_product_integrable := R.noise_product_integrable
      noise_coordinate_integrable := h.noise_coordinate_integrable
      noise_mean_zero := h.noise_mean_zero
      noise_energy_integrable := ?_
      C1 := C1
      C2 := C2
      distanceBound := R.distanceBound
      C1_nonneg := hC1.1
      C2_nonneg := hC2.1
      distanceBound_nonneg := R.distanceBound_nonneg
      noise_energy_bound := ?_
      update := h.update
      subgradient := ?_
      gradient_bound := ?_
      distance_bound := R.distance_bound
      radius_nonneg := ?_
      biasBound := biasBound
      biasBound_nonneg := hbias.1
      bias_bound := hbias.2
      step_bias_summable := ?_
      radius_sq_summable := h.step_sizes.2.1
      radius_diverges := h.step_sizes.2.2
      trajectory_mem_solutionSpace := ?_
      compact_solutionSpace := hcompact
      subgradient_exists_bounded := ?_
      target_minimizes := h.target_minimizes
      target_unique := h.target_unique }
  · intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using
      h.noise_energy_integrable t
  · intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using hC2.2 t
  · intro t
    filter_upwards [h.trajectory_subgradient t] with omega homega
    exact homega.2
  · intro t
    filter_upwards [h.trajectory_subgradient t] with omega homega
    exact hC1.2 (trajectory t omega) homega.1 (meanSubgradient t omega) homega.2
  · intro t
    exact le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t))
  · simpa [finiteCoordinateNorm, SourceNorm.l2] using h.step_bias_summable
  · exact ae_all_iff.2 fun t =>
      (h.trajectory_subgradient t).mono fun _ homega => homega.1
  · intro x hx
    rcases R.subgradient_exists x hx with ⟨g, hg⟩
    exact ⟨g, hg, hC1.2 x hx g hg⟩

/--
The source-facing Appendix Theorem 5 hypotheses, together with the explicit
well-definedness data for their stochastic process, imply almost-sure
convergence by the reusable projected stochastic-subgradient theorem.
-/
theorem AppendixTheorem5ExecutionRegularity.ae_tendsto
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ)
    (bias : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5Hypotheses mu filtration solutionSpace objective project
      trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5ExecutionRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar) :
    ∀ᵐ omega ∂mu, Tendsto (fun t => trajectory t omega) atTop (nhds xstar) := by
  let S := R.toProjectedSSGMExecution mu filtration solutionSpace objective project
    trajectory meanSubgradient noise bias radius xstar h
  convert S.ae_tendsto using 1

/--
Appendix Theorem 5 with the source's adapted random bias process.  The
displayed analytic hypotheses are unchanged from the printed theorem; unlike
the deterministic specialization above, the update and both bias bounds are
stated on sample paths.
-/
structure AppendixTheorem5AdaptedBiasHypotheses
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) : Prop where
  solutionSpace_nonempty : solutionSpace.Nonempty
  solutionSpace_bounded : Bornology.IsBounded solutionSpace
  solutionSpace_closed : IsClosed solutionSpace
  solutionSpace_convex : Convex ℝ solutionSpace
  objective_convex : ConvexOn ℝ solutionSpace objective
  target_mem_solutionSpace : xstar ∈ solutionSpace
  target_minimizes : IsMinOn objective solutionSpace xstar
  target_unique : ∀ y, y ∈ solutionSpace → objective y = objective xstar → y = xstar
  step_sizes : SSGMStepSizeConditions radius
  closest_point_projection : ∀ y,
    project y ∈ solutionSpace ∧
      IsMinOn (fun x => finiteCoordinateDistance SourceNorm.l2 x y)
        solutionSpace (project y)
  update : ∀ t, ∀ᵐ omega ∂mu,
    trajectory (t + 1) omega =
      project (fun i => trajectory t omega i - radius (t + 1) *
        (meanSubgradient t omega i + noise t omega i + bias t omega i))
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun t omega => trajectory t omega i)
  bias_adapted : ∀ i,
    StronglyAdapted filtration (fun t omega => bias t omega i)
  trajectory_subgradient : ∀ t, ∀ᵐ omega ∂mu,
    trajectory t omega ∈ solutionSpace ∧
      FiniteSubgradientWithinAt objective solutionSpace (trajectory t omega)
        (meanSubgradient t omega)
  bounded_subgradients : ∃ C1 : ℝ, 0 ≤ C1 ∧
    ∀ x, x ∈ solutionSpace → ∀ g,
      FiniteSubgradientWithinAt objective solutionSpace x g →
        finiteCoordinateNorm SourceNorm.l2 g ≤ C1
  noise_coordinate_integrable : ∀ t i,
    Integrable (fun omega => noise t omega i) mu
  noise_mean_zero : ∀ t i,
    mu[fun omega => noise t omega i | filtration t] =ᵐ[mu] 0
  noise_energy_integrable : ∀ t,
    Integrable (fun omega => finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2) mu
  bounded_noise_energy : ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ t,
    mu[fun omega => finiteCoordinateNorm SourceNorm.l2 (noise t omega) ^ 2
      | filtration t] ≤ᵐ[mu] fun _ => C2
  bounded_bias : ∃ C3 : ℝ, 0 ≤ C3 ∧ ∀ t, ∀ᵐ omega ∂mu,
    finiteCoordinateNorm SourceNorm.l2 (bias t omega) ≤ C3
  step_bias_summable : ∀ᵐ omega ∂mu,
    Summable (fun t => radius (t + 1) *
      finiteCoordinateNorm SourceNorm.l2 (bias t omega))

/--
Minimal regularity for the adapted-bias reading.  The final field gives the
natural adaptedness of the weighted-noise partial sum; its integrability and
square-integrable martingale bound are derived from C2 below, rather than
entered as convergence premises.
-/
structure AppendixTheorem5AdaptedBiasRegularity
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ) where
  noise_product_integrable : ∀ t i, Integrable
    (fun omega => (trajectory t omega i - xstar i) * noise t omega i) mu
  distanceBound : ℝ
  distanceBound_nonneg : 0 ≤ distanceBound
  distance_bound : ∀ t, ∀ᵐ omega ∂mu,
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => trajectory t omega i - xstar i) ≤ distanceBound
  subgradient_exists : ∀ x, x ∈ solutionSpace → ∃ g,
    FiniteSubgradientWithinAt objective solutionSpace x g
  noise_dot_partialSum_adapted : StronglyAdapted filtration
    (fun k omega => ∑ t ∈ Finset.range k,
      -(2 * radius (t + 1)) * AppliedModelingLib.FiniteDimensionalNorms.dot
        (noise t omega) (fun i => trajectory t omega i - xstar i))

/--
The pointwise descent estimate behind the adapted-bias version of Appendix
Theorem 5.  Crucially, the linear bias term remains a realized sample-path
increment; replacing it by the uniform envelope would give a non-summable
multiple of `radius`.
-/
theorem AppendixTheorem5AdaptedBiasHypotheses.raw_descent
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5AdaptedBiasHypotheses mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5AdaptedBiasRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ t, ∀ᵐ omega ∂mu,
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (t + 1) omega i - xstar i) ≤
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => trajectory t omega i - xstar i) -
          2 * radius (t + 1) *
            (objective (trajectory t omega) - objective xstar) -
          2 * radius (t + 1) * AppliedModelingLib.FiniteDimensionalNorms.dot
            (noise t omega) (fun i => trajectory t omega i - xstar i) +
          2 * radius (t + 1) * R.distanceBound *
            AppliedModelingLib.FiniteDimensionalNorms.l2 (bias t omega) +
          3 * radius (t + 1) ^ 2 *
            (C1 ^ 2 + AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) +
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq (bias t omega)) := by
  letI := mOmega
  obtain ⟨C1, hC1_nonneg, hC1⟩ := h.bounded_subgradients
  refine ⟨C1, hC1_nonneg, ?_⟩
  have hproject : AppliedModelingLib.Optimization.SquaredDistanceNonexpansiveOn
      solutionSpace project := by
    apply AppliedModelingLib.Optimization.euclideanProjection_squaredDistanceNonexpansive
      h.solutionSpace_convex
    intro y
    simpa [finiteCoordinateDistance, finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.l2] using h.closest_point_projection y
  intro t
  filter_upwards [h.update t, h.trajectory_subgradient t, R.distance_bound t] with
      omega hupdate hsub hdistance
  have hgradient_bound :
      AppliedModelingLib.FiniteDimensionalNorms.l2 (meanSubgradient t omega) ≤ C1 := by
    simpa [finiteCoordinateNorm, SourceNorm.l2] using
      hC1 (trajectory t omega) hsub.1 (meanSubgradient t omega) hsub.2
  have hradius : 0 ≤ radius (t + 1) :=
    le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t))
  have hstep :=
    AppliedModelingLib.Optimization.l2Sq_projected_subgradient_noise_bias_step_le_bounded
      (noise := noise t omega) (bias := bias t omega) hproject hsub.2
      h.target_mem_solutionSpace hradius hgradient_bound hdistance
  simpa [hupdate] using hstep

/--
The weighted centered-noise term in Appendix Theorem 5 has an almost-surely
convergent partial sum.  This is the explicit finite-dimensional martingale
orthogonality calculation supplied by the source's conditional C2 bound and
the feasible-distance envelope.
-/
theorem AppendixTheorem5AdaptedBiasHypotheses.noise_dot_ae_tendsto
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5AdaptedBiasHypotheses mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5AdaptedBiasRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar) :
    ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun k => ∑ t ∈ Finset.range k,
        -(2 * radius (t + 1)) * AppliedModelingLib.FiniteDimensionalNorms.dot
          (noise t omega) (fun i => trajectory t omega i - xstar i))
        atTop (nhds limit) := by
  letI := mOmega
  let Y : ℕ → Omega → ℝ := fun t omega =>
    -(2 * radius (t + 1)) * AppliedModelingLib.FiniteDimensionalNorms.dot
      (noise t omega) (fun i => trajectory t omega i - xstar i)
  have hY_centered : ∀ t, mu[Y t | filtration t] =ᵐ[mu] 0 := by
    intro t
    have hdot :
        mu[fun omega => AppliedModelingLib.FiniteDimensionalNorms.dot
          (noise t omega) (fun i => trajectory t omega i - xstar i)
          | filtration t] =ᵐ[mu] 0 := by
      apply AppliedModelingLib.Optimization.condExp_finiteDot_eq_zero_of_coordinatewise
      · intro i
        exact (h.trajectory_adapted i t).sub stronglyMeasurable_const
      · intro i
        simpa [mul_comm] using R.noise_product_integrable t i
      · exact h.noise_coordinate_integrable t
      · exact h.noise_mean_zero t
    calc
      mu[Y t | filtration t] =ᵐ[mu]
          (-(2 * radius (t + 1))) •
            mu[fun omega => AppliedModelingLib.FiniteDimensionalNorms.dot
              (noise t omega) (fun i => trajectory t omega i - xstar i)
              | filtration t] := by
            simpa [Y, Pi.smul_apply, smul_eq_mul] using
              (condExp_smul (μ := mu) (-(2 * radius (t + 1)))
                (fun omega => AppliedModelingLib.FiniteDimensionalNorms.dot
                  (noise t omega) (fun i => trajectory t omega i - xstar i))
                (filtration t))
      _ =ᵐ[mu] 0 := by
        filter_upwards [hdot] with omega hzero
        simp [hzero]
  rcases h.bounded_noise_energy with ⟨C2, hC2_nonneg, hC2⟩
  have hnoise_energy_integrable : ∀ t,
      Integrable (fun omega =>
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega)) mu := by
    intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using
      h.noise_energy_integrable t
  have hnoise_energy_bound : ∀ t,
      mu[fun omega => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (noise t omega) | filtration t] ≤ᵐ[mu] fun _ => C2 := by
    intro t
    simpa [finiteCoordinateNorm, SourceNorm.l2,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using hC2 t
  have hnoise_integral_le : ∀ t,
      (∫ omega, AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) ∂mu) ≤ C2 := by
    intro t
    calc
      (∫ omega, AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) ∂mu) =
          ∫ omega, mu[fun omega =>
            AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega)
            | filtration t] omega ∂mu := by
              exact (integral_condExp (μ := mu)
                (f := fun omega => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
                  (noise t omega)) (m := filtration t) (m₀ := mOmega)
                (filtration.le t)).symm
      _ ≤ ∫ _omega : Omega, C2 ∂mu := by
            exact integral_mono_ae integrable_condExp (integrable_const C2)
              (hnoise_energy_bound t)
      _ = C2 := by simp
  let secondBound : ℕ → ℝ := fun t =>
    4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2 * C2
  have hY_sq_point : ∀ t, ∀ᵐ omega ∂mu,
      (Y t omega) ^ 2 ≤
        (4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2) *
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) := by
    intro t
    filter_upwards [R.distance_bound t] with omega hdistance
    have hdot_sq := AppliedModelingLib.FiniteDimensionalNorms.dot_sq_le_l2Sq_mul_l2Sq
      (noise t omega) (fun i => trajectory t omega i - xstar i)
    have hdistance_sq :
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun i => trajectory t omega i - xstar i) ^ 2 ≤ R.distanceBound ^ 2 :=
      (sq_le_sq₀ (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _)
        R.distanceBound_nonneg).mpr hdistance
    have hscaled :
        4 * radius (t + 1) ^ 2 *
            AppliedModelingLib.FiniteDimensionalNorms.dot (noise t omega)
              (fun i => trajectory t omega i - xstar i) ^ 2 ≤
          4 * radius (t + 1) ^ 2 *
            (AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) *
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq
                (fun i => trajectory t omega i - xstar i)) := by
      exact mul_le_mul_of_nonneg_left hdot_sq (by positivity)
    calc
      (Y t omega) ^ 2 =
          4 * radius (t + 1) ^ 2 *
            AppliedModelingLib.FiniteDimensionalNorms.dot (noise t omega)
              (fun i => trajectory t omega i - xstar i) ^ 2 := by
                dsimp [Y]
                ring
      _ ≤ 4 * radius (t + 1) ^ 2 *
            (AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) *
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq
                (fun i => trajectory t omega i - xstar i)) := hscaled
      _ ≤ 4 * radius (t + 1) ^ 2 *
            (AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) *
              R.distanceBound ^ 2) := by
                apply mul_le_mul_of_nonneg_left
                · exact mul_le_mul_of_nonneg_left
                    (by simpa [← AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq]
                      using hdistance_sq)
                    (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg _)
                · positivity
      _ = (4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2) *
            AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) := by ring
  have hY_sq_integrable : ∀ t, Integrable (fun omega => (Y t omega) ^ 2) mu := by
    intro t
    have hdot_integrable : Integrable (fun omega =>
        AppliedModelingLib.FiniteDimensionalNorms.dot (noise t omega)
          (fun i => trajectory t omega i - xstar i)) mu := by
      simpa [AppliedModelingLib.FiniteDimensionalNorms.dot, mul_comm] using
        integrable_finset_sum (Finset.univ : Finset Coord)
          (fun i _hi => R.noise_product_integrable t i)
    refine Integrable.mono'
      ((hnoise_energy_integrable t).const_mul
        (4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2)) ?_ ?_
    · convert
        ((hdot_integrable.const_mul (-(2 * radius (t + 1)))).aestronglyMeasurable.pow 2)
        using 1
    · filter_upwards [hY_sq_point t] with omega hpoint
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hpoint
  have hY_memLp : ∀ t, MemLp (Y t) 2 mu := by
    intro t
    apply (memLp_two_iff_integrable_sq ?_).2 (hY_sq_integrable t)
    have hdot_integrable : Integrable (fun omega =>
        AppliedModelingLib.FiniteDimensionalNorms.dot (noise t omega)
          (fun i => trajectory t omega i - xstar i)) mu := by
      simpa [AppliedModelingLib.FiniteDimensionalNorms.dot, mul_comm] using
        integrable_finset_sum (Finset.univ : Finset Coord)
          (fun i _hi => R.noise_product_integrable t i)
    simpa [Y] using
      (hdot_integrable.const_mul (-(2 * radius (t + 1)))).aestronglyMeasurable
  have hY_second : ∀ t, (∫ omega, (Y t omega) ^ 2 ∂mu) ≤ secondBound t := by
    intro t
    calc
      (∫ omega, (Y t omega) ^ 2 ∂mu) ≤
          ∫ omega, (4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2) *
            AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) ∂mu := by
              exact integral_mono_ae (hY_sq_integrable t)
                ((hnoise_energy_integrable t).const_mul _) (hY_sq_point t)
      _ = (4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2) *
          ∫ omega, AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega) ∂mu := by
            rw [integral_const_mul]
      _ ≤ 4 * radius (t + 1) ^ 2 * R.distanceBound ^ 2 * C2 := by
            exact mul_le_mul_of_nonneg_left (hnoise_integral_le t) (by positivity)
      _ = secondBound t := rfl
  have hsecond_nonneg : ∀ t, 0 ≤ secondBound t := by
    intro t
    dsimp [secondBound]
    positivity
  have hsecond_summable : Summable secondBound := by
    have hsquare := h.step_sizes.2.1.mul_left (4 * R.distanceBound ^ 2 * C2)
    convert hsquare using 1
    ext t
    dsimp [secondBound]
    ring
  simpa [Y] using
    (AppliedModelingLib.ae_tendsto_partial_sum_of_condExp_zero_of_summable_secondMoments
      R.noise_dot_partialSum_adapted hY_memLp hY_centered hY_second
      hsecond_summable hsecond_nonneg)

/--
The repaired Appendix Theorem 5 endpoint for an adapted bias process.  Its
linear bias error is controlled by the source's almost-sure weighted series;
the centered noise pairing is a convergent martingale increment, not a
deterministic error budget.
-/
theorem AppendixTheorem5AdaptedBiasRegularity.ae_tendsto
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega}
    [Fintype Coord] [Nonempty Coord]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (filtration : Filtration (Ω := Omega) ℕ mOmega)
    (solutionSpace : Set (Coord → ℝ))
    (objective : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory meanSubgradient noise bias : ℕ → Omega → Coord → ℝ)
    (radius : ℕ → ℝ) (xstar : Coord → ℝ)
    (h : AppendixTheorem5AdaptedBiasHypotheses mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar)
    (R : AppendixTheorem5AdaptedBiasRegularity mu filtration solutionSpace objective
      project trajectory meanSubgradient noise bias radius xstar) :
    ∀ᵐ omega ∂mu, Tendsto (fun t => trajectory t omega) atTop (nhds xstar) := by
  letI := mOmega
  rcases h.raw_descent mu filtration solutionSpace objective project trajectory
    meanSubgradient noise bias radius xstar R with ⟨C, hC_nonneg, hdescent⟩
  let potential : ℕ → Omega → ℝ := fun t omega =>
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => trajectory t omega i - xstar i)
  let loss : ℕ → Omega → ℝ := fun t omega =>
    2 * radius (t + 1) * (objective (trajectory t omega) - objective xstar)
  let error : ℕ → ℝ := fun t => 3 * radius (t + 1) ^ 2 * C ^ 2
  let noiseIncrement : ℕ → Omega → ℝ := fun t omega =>
    -(2 * radius (t + 1)) * AppliedModelingLib.FiniteDimensionalNorms.dot
      (noise t omega) (fun i => trajectory t omega i - xstar i)
  let noiseEnergyIncrement : ℕ → Omega → ℝ := fun t omega =>
    3 * radius (t + 1) ^ 2 *
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega)
  let biasIncrement : ℕ → Omega → ℝ := fun t omega =>
    2 * radius (t + 1) * R.distanceBound *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (bias t omega) +
      3 * radius (t + 1) ^ 2 *
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (bias t omega)
  let increment : ℕ → Omega → ℝ := fun t omega =>
    noiseIncrement t omega + noiseEnergyIncrement t omega + biasIncrement t omega
  have hpotential_nonneg : ∀ t, ∀ᵐ omega ∂mu, 0 ≤ potential t omega := by
    intro t
    filter_upwards [] with omega
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg _
  have hloss_nonneg : ∀ t, ∀ᵐ omega ∂mu, 0 ≤ loss t omega := by
    intro t
    filter_upwards [h.trajectory_subgradient t] with omega htrajectory
    dsimp [loss]
    exact mul_nonneg
      (mul_nonneg (by norm_num)
        (le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t))))
      (sub_nonneg.mpr (h.target_minimizes htrajectory.1))
  have hstep : ∀ t, ∀ᵐ omega ∂mu,
      potential (t + 1) omega ≤ potential t omega + error t - loss t omega +
        increment t omega := by
    intro t
    filter_upwards [hdescent t] with omega hdescent
    dsimp [potential, error, loss, increment, noiseIncrement,
      noiseEnergyIncrement, biasIncrement]
    nlinarith [hdescent]
  have herror : Summable error := by
    have hsquare := h.step_sizes.2.1.mul_left (3 * C ^ 2)
    convert hsquare using 1
    ext t
    dsimp [error]
    ring
  have herror_nonneg : ∀ t, 0 ≤ error t := by
    intro t
    dsimp [error]
    positivity
  have hnoise_tendsto : ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun k => ∑ t ∈ Finset.range k, noiseIncrement t omega)
        atTop (nhds limit) := by
    simpa [noiseIncrement] using
      (h.noise_dot_ae_tendsto mu filtration solutionSpace objective project trajectory
        meanSubgradient noise bias radius xstar R)
  rcases h.bounded_noise_energy with ⟨C2, hC2_nonneg, hC2⟩
  have hnoise_energy_base : ∀ᵐ omega ∂mu,
      Summable (fun t => radius (t + 1) ^ 2 *
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (noise t omega)) := by
    apply AppliedModelingLib.Optimization.ae_summable_radius_sq_l2Sq_noise_of_condExp_le
      filtration radius noise C2
    · intro t
      simpa [finiteCoordinateNorm, SourceNorm.l2,
        AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using
        h.noise_energy_integrable t
    · intro t
      simpa [finiteCoordinateNorm, SourceNorm.l2,
        AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq] using hC2 t
    · exact h.step_sizes.2.1
  have hnoise_energy_summable : ∀ᵐ omega ∂mu,
      Summable (fun t => noiseEnergyIncrement t omega) := by
    filter_upwards [hnoise_energy_base] with omega hsum
    convert hsum.mul_left 3 using 1
    ext t
    dsimp [noiseEnergyIncrement]
    ring
  rcases h.bounded_bias with ⟨C3, hC3_nonneg, hC3⟩
  have hbias_bound : ∀ᵐ omega ∂mu, ∀ t,
      AppliedModelingLib.FiniteDimensionalNorms.l2 (bias t omega) ≤ C3 :=
    ae_all_iff.2 hC3
  have hbias_summable : ∀ᵐ omega ∂mu,
      Summable (fun t => biasIncrement t omega) := by
    simpa [biasIncrement] using
      (ae_summable_randomBiasError_of_ae_summable_step mu radius
        (fun omega t => bias t omega) R.distanceBound C3 h.step_sizes.2.1 hC3_nonneg
        (by simpa using h.step_bias_summable) hbias_bound)
  have hincrement_tendsto : ∀ᵐ omega ∂mu, ∃ limit : ℝ,
      Tendsto (fun k => ∑ t ∈ Finset.range k, increment t omega)
        atTop (nhds limit) := by
    filter_upwards [hnoise_tendsto, hnoise_energy_summable, hbias_summable]
      with omega hnoise henergy hbias
    rcases hnoise with ⟨noiseLimit, hnoise⟩
    refine ⟨(noiseLimit + ∑' t, noiseEnergyIncrement t omega) +
      ∑' t, biasIncrement t omega, ?_⟩
    convert (hnoise.add henergy.hasSum.tendsto_sum_nat).add
      hbias.hasSum.tendsto_sum_nat using 1
    ext k
    simp only [increment, Finset.sum_add_distrib]
  have hpotential_tendsto :=
    AppliedModelingLib.Optimization.ae_exists_tendsto_potential_of_nonnegative_descent_add_increment
      hpotential_nonneg hloss_nonneg hstep herror herror_nonneg hincrement_tendsto
  have hincrement_eventual_upper : ∀ᵐ omega ∂mu,
      ∃ upper : ℝ, ∃ T : ℕ, ∀ n : ℕ, T ≤ n →
        (∑ t ∈ Finset.range n, increment t omega) ≤ upper := by
    filter_upwards [hincrement_tendsto] with omega hlimit
    rcases hlimit with ⟨limit, hlimit⟩
    rcases hlimit.bddAbove_range with ⟨upper, hupper⟩
    exact ⟨upper, 0, fun n _ => hupper ⟨n, rfl⟩⟩
  have hloss_summable :=
    AppliedModelingLib.Optimization.ae_summable_loss_of_nonnegative_descent_add_increment
      hpotential_nonneg hloss_nonneg hstep herror herror_nonneg hincrement_eventual_upper
  have htrajectory_mem : ∀ᵐ omega ∂mu, ∀ t, trajectory t omega ∈ solutionSpace :=
    ae_all_iff.2 fun t => (h.trajectory_subgradient t).mono fun _ htrajectory => htrajectory.1
  rcases h.bounded_subgradients with ⟨sourceC, hsourceC_nonneg, hsourceC⟩
  have hcompact : IsCompact solutionSpace :=
    AppliedModelingLib.FiniteDimensionalNorms.isCompact_of_isClosed_of_bounded
      h.solutionSpace_closed h.solutionSpace_bounded
  have hcontinuous : ContinuousOn objective solutionSpace := by
    apply AppliedModelingLib.Optimization.continuousOn_of_exists_bounded_subgradientOn
      hsourceC_nonneg
    intro x hx
    rcases R.subgradient_exists x hx with ⟨g, hg⟩
    refine ⟨g, hg, ?_⟩
    simpa [finiteCoordinateNorm, SourceNorm.l2] using hsourceC x hx g hg
  have hloss_separation : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta : ℝ, 0 < delta ∧ ∀ t omega,
        trajectory t omega ∈ solutionSpace → epsilon ≤ potential t omega →
          delta * radius (t + 1) ≤ loss t omega := by
    intro epsilon hepsilon
    rcases AppliedModelingLib.FiniteDimensionalNorms.exists_pos_le_objective_gap_of_isCompact_of_continuousOn_of_unique_min
      hcompact hcontinuous h.target_minimizes h.target_unique epsilon hepsilon with
        ⟨delta, hdelta_pos, hgap⟩
    refine ⟨2 * delta, mul_pos (by norm_num) hdelta_pos, ?_⟩
    intro t omega hmem hpotential
    have hgap_value := hgap (trajectory t omega) hmem hpotential
    dsimp [loss]
    have hfactor_nonneg : 0 ≤ 2 * radius (t + 1) :=
      mul_nonneg (by norm_num) (le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t)))
    have hscale := mul_le_mul_of_nonneg_left hgap_value hfactor_nonneg
    nlinarith
  have hpotential_zero :=
    AppliedModelingLib.Optimization.ae_tendsto_potential_zero_of_tendsto_and_summable_of_ae_valid_loss_separation
      hpotential_nonneg hpotential_tendsto hloss_summable
      (fun t => le_of_lt (h.step_sizes.1 (t + 1) (Nat.succ_pos t)))
      h.step_sizes.2.2 htrajectory_mem hloss_separation
  filter_upwards [hpotential_zero] with omega hzero
  exact AppliedModelingLib.FiniteDimensionalNorms.tendsto_pi_of_tendsto_l2Sq_sub_zero hzero

/--
Apply an explicit SSGM convergence bundle to a concrete finite-coordinate
source model to obtain the named four-endpoint consequence bundle.
-/
theorem ssgm_convergence_theorem_consequences
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E :=
  ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    M S

end GKGMM19IterativeLocalVoting
