import GKGMM19IterativeLocalVoting.MainTheorems
import AppliedModelingLib.Foundations.Optimization.ProjectedStochasticConvergence
import Mathlib.Probability.Martingale.Convergence

open MeasureTheory ProbabilityTheory Filter
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
