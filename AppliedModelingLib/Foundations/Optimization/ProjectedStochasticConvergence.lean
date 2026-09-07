import AppliedModelingLib.Foundations.Optimization.StochasticSubgradient
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators MeasureTheory NNReal ENNReal

namespace AppliedModelingLib.Optimization

/--
An outcome-indexed convergence conclusion for a stochastic trajectory.  Each
almost-sure sample path may converge to its own target in the designated set;
this is the correct set-valued conclusion when the minimizer need not be
unique.  A deterministic target is a stronger special case supplied by the
constructor below.
-/
def OutcomeIndexedConvergesToSet
    {Omega Point : Type*} [MeasurableSpace Omega] [TopologicalSpace Point]
    (mu : Measure Omega) (trajectory : ℕ → Omega → Point) (targetSet : Set Point) : Prop :=
  ∀ᵐ omega ∂mu, ∃ target ∈ targetSet,
    Tendsto (fun n => trajectory n omega) atTop (nhds target)

/-- Package an almost-sure limit and its target-set membership as an
`OutcomeIndexedConvergesToSet` conclusion. -/
theorem outcomeIndexedConvergesToSet_of_ae_tendsto
    {Omega Point : Type*} [MeasurableSpace Omega] [TopologicalSpace Point]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Point} {target : Point}
    {targetSet : Set Point} (htarget : target ∈ targetSet)
    (hconverges : ∀ᵐ omega ∂mu,
      Tendsto (fun n => trajectory n omega) atTop (nhds target)) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet :=
  hconverges.mono fun _ hlimit => ⟨target, htarget, hlimit⟩

/-- Enlarge the designated set in an outcome-indexed convergence conclusion. -/
theorem OutcomeIndexedConvergesToSet.mono
    {Omega Point : Type*} [MeasurableSpace Omega] [TopologicalSpace Point]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Point}
    {targetSet targetSet' : Set Point}
    (h : OutcomeIndexedConvergesToSet mu trajectory targetSet)
    (hsubset : targetSet ⊆ targetSet') :
    OutcomeIndexedConvergesToSet mu trajectory targetSet' := by
  filter_upwards [h] with omega homega
  rcases homega with ⟨target, htarget, hconverges⟩
  exact ⟨target, hsubset htarget, hconverges⟩

/--
Turn the two deterministic ingredients of a minimizer-set convergence proof
into the correct almost-sure, path-dependent conclusion.  On almost every
path, quasi-Fejér analysis must give a squared-distance limit for every target
in the set, and compactness/objective descent must give one subsequence
converging to a target in that set.  The finite-dimensional terminal lemma
then upgrades the subsequence to convergence of the full path.

The universal potential premise is deliberately pathwise.  Separate
almost-everywhere statements for uncountably many targets cannot be
intersected without an additional separability argument.
-/
theorem outcomeIndexedConvergesToSet_of_ae_all_l2Sq_potential_limits_and_ae_subsequence
    {Omega Coord : Type*} [MeasurableSpace Omega] [Fintype Coord]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Coord → ℝ}
    {targetSet : Set (Coord → ℝ)}
    (hpotential : ∀ᵐ omega ∂mu, ∀ target, target ∈ targetSet →
      ∃ limit : ℝ, Tendsto
        (fun n => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i)) atTop (nhds limit))
    (hsubsequence : ∀ᵐ omega ∂mu, ∃ target ∈ targetSet,
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto (fun n => trajectory (subseq n) omega) atTop (nhds target)) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  filter_upwards [hpotential, hsubsequence] with omega hall hsubsequence
  rcases hsubsequence with ⟨target, htarget, subseq, hsubseq_strict, hsubseq⟩
  rcases hall target htarget with ⟨limit, hpotential⟩
  exact ⟨target, htarget,
    AppliedModelingLib.FiniteDimensionalNorms.tendsto_pi_of_tendsto_l2Sq_sub_of_tendsto_subseq
      hpotential hsubseq_strict hsubseq⟩

/--
Finite affine anchors are enough for minimizer-set convergence.  If every
target in the set is an affine combination of a fixed finite anchor family,
the common almost-sure event need only contain the potential limits for those
anchors.  The affine squared-distance identity supplies the potential limit
for the path-dependent subsequential target.
-/
theorem outcomeIndexedConvergesToSet_of_ae_anchor_l2Sq_potential_limits_and_ae_subsequence
    {Omega Coord Anchor : Type*} [MeasurableSpace Omega] [Fintype Coord] [Fintype Anchor]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Coord → ℝ}
    {targetSet : Set (Coord → ℝ)} (anchor : Anchor → Coord → ℝ)
    (haffine : ∀ target, target ∈ targetSet → ∃ weights : Anchor → ℝ,
      (∑ a, weights a = 1) ∧ ∀ i, target i = ∑ a, weights a * anchor a i)
    (hpotential : ∀ᵐ omega ∂mu, ∀ a, ∃ limit : ℝ, Tendsto
      (fun n => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - anchor a i)) atTop (nhds limit))
    (hsubsequence : ∀ᵐ omega ∂mu, ∃ target ∈ targetSet,
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto (fun n => trajectory (subseq n) omega) atTop (nhds target)) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  filter_upwards [hpotential, hsubsequence] with omega hanchor hsubsequence
  rcases hsubsequence with ⟨target, htarget, subseq, hsubseq_strict, hsubseq⟩
  rcases haffine target htarget with ⟨weights, hweights, htarget_weights⟩
  rcases AppliedModelingLib.FiniteDimensionalNorms.exists_tendsto_l2Sq_sub_of_affine_combination
    (f := fun n => trajectory n omega) target weights anchor hweights htarget_weights hanchor with
      ⟨limit, htarget_potential⟩
  exact ⟨target, htarget,
    AppliedModelingLib.FiniteDimensionalNorms.tendsto_pi_of_tendsto_l2Sq_sub_of_tendsto_subseq
      htarget_potential hsubseq_strict hsubseq⟩

/--
Pointwise almost-sure potential convergence for every target in a
finite-dimensional set is enough for the minimizer-set argument.  The proof
first chooses finitely many anchors from the target set, and only then
intersects their almost-sure events; it never takes an invalid uncountable
intersection.
-/
theorem outcomeIndexedConvergesToSet_of_ae_target_l2Sq_potential_limits_and_ae_subsequence
    {Omega Coord : Type*} [MeasurableSpace Omega] [Fintype Coord]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Coord → ℝ}
    {targetSet : Set (Coord → ℝ)}
    (hpotential : ∀ target, target ∈ targetSet → ∀ᵐ omega ∂mu, ∃ limit : ℝ, Tendsto
      (fun n => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) atTop (nhds limit))
    (hsubsequence : ∀ᵐ omega ∂mu, ∃ target ∈ targetSet,
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto (fun n => trajectory (subseq n) omega) atTop (nhds target)) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  classical
  rcases AppliedModelingLib.FiniteDimensionalNorms.exists_finset_affine_combination_representation
    targetSet with ⟨anchor, hanchor, haffine⟩
  apply outcomeIndexedConvergesToSet_of_ae_anchor_l2Sq_potential_limits_and_ae_subsequence
    (fun a : (↑anchor) => (a : Coord → ℝ)) haffine
  · rw [ae_all_iff]
    intro a
    exact hpotential a (hanchor a.property)
  · exact hsubsequence

/--
A compact finite-dimensional trajectory with summable nonnegative objective
gaps along a divergent step-size sequence has a subsequence converging to a
minimizer.  This is the compactness/objective half of the standard
minimizer-set stochastic-subgradient argument.
-/
theorem exists_minimizer_subsequence_of_compact_continuousOn_of_summable_weighted_gap
    {Coord : Type*} [Fintype Coord]
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {trajectory : ℕ → Coord → ℝ} {target : Coord → ℝ} {radius : ℕ → ℝ}
    (htrajectory_mem : ∀ n, trajectory n ∈ solutionSpace)
    (hcompact : IsCompact solutionSpace)
    (hcontinuous : ContinuousOn objective solutionSpace)
    (hmin : IsMinOn objective solutionSpace target)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hsummable : Summable (fun n =>
      radius (n + 1) * (objective (trajectory n) - objective target))) :
    ∃ minimizer ∈ solutionSpace, IsMinOn objective solutionSpace minimizer ∧
      ∃ subseq : ℕ → ℕ, StrictMono subseq ∧
        Tendsto (fun n => trajectory (subseq n)) atTop (nhds minimizer) := by
  let gap : ℕ → ℝ := fun n => objective (trajectory n) - objective target
  have hgap_nonneg : ∀ n, 0 ≤ gap n := by
    intro n
    exact sub_nonneg.mpr (hmin (htrajectory_mem n))
  have hfrequent : ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in atTop, gap n < epsilon :=
    frequently_lt_of_summable_mul_of_tendsto_sum_atTop hradius_nonneg (by
      simpa [gap] using hsummable) hradius_diverges
  rcases exists_strictMono_tendsto_zero_of_frequently_lt hgap_nonneg hfrequent with
    ⟨smallSubseq, hsmall_strict, hgap_small⟩
  rcases hcompact.tendsto_subseq (x := fun n => trajectory (smallSubseq n))
    (fun n => htrajectory_mem (smallSubseq n)) with
      ⟨minimizer, hminimizer_mem, clusterSubseq, hcluster_strict, hcluster⟩
  have htrajectory_cluster : Tendsto
      (fun n => trajectory (smallSubseq (clusterSubseq n))) atTop (nhds minimizer) := by
    simpa [Function.comp_def] using hcluster
  have hgap_cluster : Tendsto
      (fun n => objective (trajectory (smallSubseq (clusterSubseq n))) - objective target)
        atTop (nhds 0) := by
    simpa [Function.comp_def, gap] using hgap_small.comp hcluster_strict.tendsto_atTop
  have htrajectory_cluster_within : Tendsto
      (fun n => trajectory (smallSubseq (clusterSubseq n))) atTop
        (nhdsWithin minimizer solutionSpace) :=
    tendsto_nhdsWithin_iff.mpr ⟨htrajectory_cluster,
      Filter.Eventually.of_forall fun n =>
        htrajectory_mem (smallSubseq (clusterSubseq n))⟩
  have hobjective_cluster : Tendsto
      (fun n => objective (trajectory (smallSubseq (clusterSubseq n)))) atTop
        (nhds (objective minimizer)) :=
    (hcontinuous minimizer hminimizer_mem).tendsto.comp htrajectory_cluster_within
  have hgap_limit : Tendsto
      (fun n => objective (trajectory (smallSubseq (clusterSubseq n))) - objective target)
        atTop (nhds (objective minimizer - objective target)) :=
    hobjective_cluster.sub tendsto_const_nhds
  have hobjective_eq : objective minimizer = objective target :=
    sub_eq_zero.mp (tendsto_nhds_unique hgap_cluster hgap_limit).symm
  have hminimizer : IsMinOn objective solutionSpace minimizer := by
    intro y hy
    rw [hobjective_eq]
    exact hmin hy
  exact ⟨minimizer, hminimizer_mem, hminimizer,
    smallSubseq ∘ clusterSubseq, hsmall_strict.comp hcluster_strict,
    by simpa [Function.comp_def] using htrajectory_cluster⟩

/--
Finite-anchor potential limits and almost-sure summable weighted objective
gaps imply convergence to a minimizer set.  This packages the complete
non-unique-minimizer terminal argument while keeping the stochastic descent
calculation, affine representation, and objective/minimizer identification as
separate mathematical inputs.
-/
theorem outcomeIndexedConvergesToSet_of_ae_anchor_potential_limits_and_ae_summable_gaps
    {Omega Coord Anchor : Type*} [MeasurableSpace Omega] [Fintype Coord] [Fintype Anchor]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Coord → ℝ}
    {solutionSpace targetSet : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {target : Coord → ℝ} {radius : ℕ → ℝ} (anchor : Anchor → Coord → ℝ)
    (haffine : ∀ x, x ∈ targetSet → ∃ weights : Anchor → ℝ,
      (∑ a, weights a = 1) ∧ ∀ i, x i = ∑ a, weights a * anchor a i)
    (hpotential : ∀ᵐ omega ∂mu, ∀ a, ∃ limit : ℝ, Tendsto
      (fun n => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - anchor a i)) atTop (nhds limit))
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hcompact : IsCompact solutionSpace)
    (hcontinuous : ContinuousOn objective solutionSpace)
    (hmin : IsMinOn objective solutionSpace target)
    (hminimizer_targetSet : ∀ x, x ∈ solutionSpace →
      IsMinOn objective solutionSpace x → x ∈ targetSet)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hsummable : ∀ᵐ omega ∂mu, Summable (fun n =>
      radius (n + 1) * (objective (trajectory n omega) - objective target))) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  apply outcomeIndexedConvergesToSet_of_ae_anchor_l2Sq_potential_limits_and_ae_subsequence
    anchor haffine hpotential
  filter_upwards [htrajectory_mem, hsummable] with omega htrajectory hsum
  rcases exists_minimizer_subsequence_of_compact_continuousOn_of_summable_weighted_gap
    htrajectory hcompact hcontinuous hmin hradius_nonneg hradius_diverges hsum with
      ⟨minimizer, hminimizer_mem, hminimizer, subseq, hsubseq_strict, hsubseq⟩
  exact ⟨minimizer, hminimizer_targetSet minimizer hminimizer_mem hminimizer,
    subseq, hsubseq_strict, hsubseq⟩

/--
The finite-dimensional minimizer-set convergence theorem with pointwise
almost-sure potential limits.  It automatically reduces those pointwise
statements to finite affine anchors before forming the common event.
-/
theorem outcomeIndexedConvergesToSet_of_ae_target_potential_limits_and_ae_summable_gaps
    {Omega Coord : Type*} [MeasurableSpace Omega] [Fintype Coord]
    {mu : Measure Omega} {trajectory : ℕ → Omega → Coord → ℝ}
    {solutionSpace targetSet : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {target : Coord → ℝ} {radius : ℕ → ℝ}
    (hpotential : ∀ x, x ∈ targetSet → ∀ᵐ omega ∂mu, ∃ limit : ℝ, Tendsto
      (fun n => AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - x i)) atTop (nhds limit))
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hcompact : IsCompact solutionSpace)
    (hcontinuous : ContinuousOn objective solutionSpace)
    (hmin : IsMinOn objective solutionSpace target)
    (hminimizer_targetSet : ∀ x, x ∈ solutionSpace →
      IsMinOn objective solutionSpace x → x ∈ targetSet)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (hsummable : ∀ᵐ omega ∂mu, Summable (fun n =>
      radius (n + 1) * (objective (trajectory n omega) - objective target))) :
    OutcomeIndexedConvergesToSet mu trajectory targetSet := by
  apply outcomeIndexedConvergesToSet_of_ae_target_l2Sq_potential_limits_and_ae_subsequence
    hpotential
  filter_upwards [htrajectory_mem, hsummable] with omega htrajectory hsum
  rcases exists_minimizer_subsequence_of_compact_continuousOn_of_summable_weighted_gap
    htrajectory hcompact hcontinuous hmin hradius_nonneg hradius_diverges hsum with
      ⟨minimizer, hminimizer_mem, hminimizer, subseq, hsubseq_strict, hsubseq⟩
  exact ⟨minimizer, hminimizer_targetSet minimizer hminimizer_mem hminimizer,
    subseq, hsubseq_strict, hsubseq⟩

/--
The finite-dimensional Euclidean feasible-set data shared by projected
optimization algorithms.  A closest-point projection onto a closed bounded
convex set is both compactly supported and nonexpansive in squared distance;
the lemmas below expose those consequences once for all applications.
-/
structure EuclideanProjectionSourceGeometry
    (Coord : Type*) [Fintype Coord]
    (solutionSpace : Set (Coord → ℝ))
    (project : (Coord → ℝ) → Coord → ℝ) : Prop where
  closed_solutionSpace : IsClosed solutionSpace
  bounded_solutionSpace : Bornology.IsBounded solutionSpace
  convex_solutionSpace : Convex ℝ solutionSpace
  closest_point_projection : EuclideanProjectionOnto solutionSpace project

/--
A closed, bounded, convex, nonempty finite-dimensional feasible set has a
canonical pointwise Euclidean nearest-point projection.  This constructor
keeps existence of the projection in the reusable optimization API rather
than requiring an application to postulate it pointwise.
-/
noncomputable def canonicalEuclideanProjectionSourceGeometry
    {Coord : Type*} [Fintype Coord]
    (solutionSpace : Set (Coord → ℝ))
    (hclosed : IsClosed solutionSpace)
    (hbounded : Bornology.IsBounded solutionSpace)
    (hconvex : Convex ℝ solutionSpace)
    (hnonempty : solutionSpace.Nonempty) :
    EuclideanProjectionSourceGeometry Coord solutionSpace
      (euclideanProjection solutionSpace
        (FiniteDimensionalNorms.isCompact_of_isClosed_of_bounded hclosed hbounded)
        hnonempty) where
  closed_solutionSpace := hclosed
  bounded_solutionSpace := hbounded
  convex_solutionSpace := hconvex
  closest_point_projection := euclideanProjection_onto solutionSpace
    (FiniteDimensionalNorms.isCompact_of_isClosed_of_bounded hclosed hbounded)
    hnonempty

/-- A source-geometry package supplies the compactness required by the
finite-dimensional stochastic convergence theorem. -/
theorem EuclideanProjectionSourceGeometry.compact_solutionSpace
    {Coord : Type*} [Fintype Coord]
    {solutionSpace : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (G : EuclideanProjectionSourceGeometry Coord solutionSpace project) :
    IsCompact solutionSpace :=
  FiniteDimensionalNorms.isCompact_of_isClosed_of_bounded
    G.closed_solutionSpace G.bounded_solutionSpace

/-- A source-geometry package supplies the squared-distance projection
inequality used in one-step projected stochastic descent. -/
theorem EuclideanProjectionSourceGeometry.squaredDistance_nonexpansive
    {Coord : Type*} [Fintype Coord]
    {solutionSpace : Set (Coord → ℝ)} {project : (Coord → ℝ) → Coord → ℝ}
    (G : EuclideanProjectionSourceGeometry Coord solutionSpace project) :
    SquaredDistanceNonexpansiveOn solutionSpace project :=
  euclideanProjection_squaredDistanceNonexpansive
    G.convex_solutionSpace G.closest_point_projection

/--
Data for one finite-dimensional projected stochastic-subgradient execution.

The record contains the ordinary process, moment, feasibility, and optimization
hypotheses used by the convergence theorem below.  It deliberately contains no
convergence conclusion, so applications must construct the actual sampled
process rather than supply a result-shaped certificate.
-/
structure ProjectedStochasticSubgradientExecution
    (Coord : Type*) [Fintype Coord] where
  Ω : Type*
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  filtration : Filtration (Ω := Ω) ℕ measurableSpace
  trajectory : ℕ → Ω → Coord → ℝ
  meanSubgradient : ℕ → Ω → Coord → ℝ
  noise : ℕ → Ω → Coord → ℝ
  bias : ℕ → Coord → ℝ
  radius : ℕ → ℝ
  solutionSpace : Set (Coord → ℝ)
  objective : (Coord → ℝ) → ℝ
  project : (Coord → ℝ) → Coord → ℝ
  target : Coord → ℝ
  target_mem_solutionSpace : target ∈ solutionSpace
  project_nonexpansive : SquaredDistanceNonexpansiveOn solutionSpace project
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun n omega => trajectory n omega i)
  objective_gap_adapted : StronglyAdapted filtration
    (fun n omega => objective (trajectory n omega) - objective target)
  potential_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory n omega i - target i)) μ
  objective_gap_integrable : ∀ n, Integrable
    (fun omega => objective (trajectory n omega) - objective target) μ
  noise_product_integrable : ∀ n i, Integrable
    (fun omega => (trajectory n omega i - target i) * noise n omega i) μ
  noise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) μ
  noise_mean_zero : ∀ n i,
    μ[fun omega => noise n omega i | filtration n] =ᵐ[μ] 0
  noise_energy_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) μ
  C1 : ℝ
  C2 : ℝ
  distanceBound : ℝ
  C1_nonneg : 0 ≤ C1
  C2_nonneg : 0 ≤ C2
  distanceBound_nonneg : 0 ≤ distanceBound
  noise_energy_bound : ∀ n,
    μ[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)
      | filtration n] ≤ᵐ[μ] fun _ => C2
  update : ∀ n, ∀ᵐ omega ∂μ,
    trajectory (n + 1) omega = project (fun i => trajectory n omega i -
      radius (n + 1) *
        (meanSubgradient n omega i + noise n omega i + bias n i))
  subgradient : ∀ n, ∀ᵐ omega ∂μ,
    FiniteSubgradientOn objective solutionSpace (trajectory n omega)
      (meanSubgradient n omega)
  gradient_bound : ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C1
  distance_bound : ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2
      (fun i => trajectory n omega i - target i) ≤ distanceBound
  radius_nonneg : ∀ n, 0 ≤ radius (n + 1)
  biasBound : ℝ
  biasBound_nonneg : 0 ≤ biasBound
  bias_bound : ∀ n, FiniteDimensionalNorms.l2 (bias n) ≤ biasBound
  step_bias_summable : Summable (fun n =>
    radius (n + 1) * FiniteDimensionalNorms.l2 (bias n))
  radius_sq_summable : Summable (fun n => radius (n + 1) ^ 2)
  radius_diverges : Tendsto
    (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop
  trajectory_mem_solutionSpace : ∀ᵐ omega ∂μ, ∀ n,
    trajectory n omega ∈ solutionSpace
  compact_solutionSpace : IsCompact solutionSpace
  subgradient_exists_bounded : ∀ x, x ∈ solutionSpace → ∃ g,
      FiniteSubgradientOn objective solutionSpace x g ∧
        FiniteDimensionalNorms.l2 g ≤ C1
  target_minimizes : IsMinOn objective solutionSpace target
  target_unique : ∀ x, x ∈ solutionSpace → objective x = objective target → x = target

/--
An execution whose stochastic directions arise from a sampled convex cost.

This refines `ProjectedStochasticSubgradientExecution` with the part of a
stochastic-subgradient model that is shared across applications: each time
step selects one sample, takes a subgradient of that sample's cost, and
decomposes that direction into its conditional-mean subgradient, noise, and
bias.  It deliberately leaves the sampling law abstract, so i.i.d. sampling,
Markov sampling, and conditionally sampled observations can use the same API
once their respective conditional-moment hypotheses have been established.
-/
structure SampledProjectedStochasticSubgradientExecution
    (Coord : Type*) [Fintype Coord] extends
    ProjectedStochasticSubgradientExecution Coord where
  Sample : Type*
  sample : ℕ → Ω → Sample
  sampleCost : Sample → (Coord → ℝ) → ℝ
  sampledDirection : ℕ → Ω → Coord → ℝ
  sampled_direction_subgradient : ∀ n, ∀ᵐ omega ∂μ,
    FiniteSubgradientOn (sampleCost (sample n omega)) solutionSpace
      (trajectory n omega) (sampledDirection n omega)
  sampled_direction_decomposition : ∀ n, ∀ᵐ omega ∂μ,
    sampledDirection n omega = fun i =>
      meanSubgradient n omega i + noise n omega i + bias n i

/--
The conditional law of the samples driving a stochastic optimization
execution.  The conditional-integral identity is the reusable mathematical
content of drawing a new sample from a fixed population law at each step.  It
is deliberately stated for integrable test functions, which is the form used
to establish conditional means and moments of sampled directions.
-/
structure ConditionalLawSampleStream
    {Coord : Type*} [Fintype Coord]
    (S : SampledProjectedStochasticSubgradientExecution Coord)
    [MeasurableSpace S.Sample] where
  sampleMeasure : Measure S.Sample
  sampleProbability : IsProbabilityMeasure sampleMeasure
  sample_measurable : ∀ n,
    @Measurable S.Ω S.Sample S.measurableSpace inferInstance (S.sample n)
  conditional_integral_eq : ∀ n (test : S.Sample → ℝ),
    Integrable test sampleMeasure →
      Integrable (fun omega => test (S.sample n omega)) S.μ →
        S.μ[fun omega => test (S.sample n omega) | S.filtration n] =ᵐ[S.μ]
          fun _ => ∫ sample, test sample ∂sampleMeasure

/--
A conditionally fresh sample stream whose test statistic may depend on the
current, adapted state.  This is the reusable independence interface needed
when a sampled direction is evaluated at the current iterate: conditioning on
its filtration averages over the fresh sample while retaining the state.
-/
structure AdaptedConditionalLawSampleStream
    {Coord : Type*} [Fintype Coord]
    (S : SampledProjectedStochasticSubgradientExecution Coord)
    [MeasurableSpace S.Sample] extends ConditionalLawSampleStream S where
  conditional_integral_eq_adapted : ∀ n (test : S.Ω → S.Sample → ℝ),
    (∀ sample, StronglyMeasurable[S.filtration n] (fun omega => test omega sample)) →
      Integrable (fun omega => test omega (S.sample n omega)) S.μ →
        S.μ[fun omega => test omega (S.sample n omega) | S.filtration n] =ᵐ[S.μ]
          fun omega => ∫ sample, test omega sample ∂sampleMeasure

/--
Centering a conditionally fresh, state-dependent sample statistic by its
population mean gives a conditional mean-zero increment.  This is the
coordinatewise martingale-noise calculation used by stochastic subgradient
methods; the population mean remains state-dependent because the current
iterate is already known to the conditioning filtration.
-/
theorem AdaptedConditionalLawSampleStream.condExp_centered_statistic_eq_zero
    {Coord : Type*} [Fintype Coord]
    {S : SampledProjectedStochasticSubgradientExecution Coord}
    [MeasurableSpace S.Sample]
    (L : AdaptedConditionalLawSampleStream S)
    (n : ℕ) (test : S.Ω → S.Sample → ℝ)
    (hadapted : ∀ sample,
      StronglyMeasurable[S.filtration n] (fun omega => test omega sample))
    (hintegrable : Integrable (fun omega => test omega (S.sample n omega)) S.μ)
    (hpopulation_measurable : StronglyMeasurable[S.filtration n]
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure))
    (hpopulation_integrable : Integrable
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure) S.μ) :
    S.μ[(fun omega => test omega (S.sample n omega)) -
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure) | S.filtration n] =ᵐ[S.μ] 0 := by
  letI := S.measurableSpace
  letI := S.probability
  have hpopulation_conditional :
      S.μ[fun omega => ∫ sample, test omega sample ∂L.sampleMeasure | S.filtration n] =ᵐ[S.μ]
        fun omega => ∫ sample, test omega sample ∂L.sampleMeasure := by
    rw [condExp_of_stronglyMeasurable (S.filtration.le n) hpopulation_measurable
      hpopulation_integrable]
  filter_upwards [
    condExp_sub hintegrable hpopulation_integrable (S.filtration n),
    L.conditional_integral_eq_adapted n test hadapted hintegrable,
    hpopulation_conditional] with omega hsub hsample hpopulation
  rw [hsub]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hsample, hpopulation]
  ring

/-- The abstract update is equivalently the projected update by the realized sampled direction. -/
theorem SampledProjectedStochasticSubgradientExecution.update_eq_sampled_direction
    {Coord : Type*} [Fintype Coord]
    (S : SampledProjectedStochasticSubgradientExecution Coord) (n : ℕ) :
    ∀ᵐ omega ∂S.μ,
      S.trajectory (n + 1) omega = S.project (fun i => S.trajectory n omega i -
        S.radius (n + 1) * S.sampledDirection n omega i) := by
  filter_upwards [S.update n, S.sampled_direction_decomposition n] with omega hupdate hdirection
  rw [hupdate]
  apply congrArg S.project
  funext i
  rw [hdirection]

/--
One conditional squared-distance descent step for a projected stochastic
subgradient update with additive centered noise and bias.  The residual term
is explicit so both potential convergence and objective-gap summability can
reuse the same stochastic calculation.
-/
theorem conditional_l2Sq_descent_of_projected_ssgm
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ}
    {bias : ℕ → Coord → ℝ} {radius : ℕ → ℝ} {target : Coord → ℝ}
    {C distanceBound noiseBound : ℝ}
    (hproject : SquaredDistanceNonexpansiveOn solutionSpace project)
    (htarget : target ∈ solutionSpace)
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hgap_adapted : StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hgap_integrable : ∀ n, Integrable
      (fun omega => objective (trajectory n omega) - objective target) mu)
    (hnoise_product_integrable : ∀ n i, Integrable
      (fun omega => (trajectory n omega i - target i) * noise n omega i) mu)
    (hnoise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) mu)
    (hnoise_mean_zero : ∀ n i,
      mu[fun omega => noise n omega i | filtration n] =ᵐ[mu] 0)
    (hnoise_energy_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) mu)
    (hnoise_energy_bound : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega) | filtration n]
        ≤ᵐ[mu] fun _ => noiseBound)
    (hupdate : ∀ n, ∀ᵐ omega ∂mu,
      trajectory (n + 1) omega = project (fun i => trajectory n omega i -
        radius (n + 1) *
          (meanSubgradient n omega i + noise n omega i + bias n i)))
    (hsubgradient : ∀ n, ∀ᵐ omega ∂mu,
      FiniteSubgradientOn objective solutionSpace (trajectory n omega)
        (meanSubgradient n omega))
    (hgradient_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C)
    (hdistance_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => trajectory n omega i - target i) ≤ distanceBound)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1)) :
    ∀ n, mu[fun omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory (n + 1) omega i - target i) | filtration n] ≤ᵐ[mu]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory n omega i - target i) -
          2 * radius (n + 1) * (objective (trajectory n omega) - objective target) +
          (2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
            3 * radius (n + 1) ^ 2 *
              (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n))) := by
  intro n
  have hnoise_dot_zero :
      mu[fun omega => FiniteDimensionalNorms.dot (noise n omega)
        (fun i => trajectory n omega i - target i) | filtration n] =ᵐ[mu] 0 := by
    apply condExp_finiteDot_eq_zero_of_coordinatewise
    · intro i
      exact (htrajectory_adapted i n).sub stronglyMeasurable_const
    · intro i
      simpa [mul_comm] using hnoise_product_integrable n i
    · exact hnoise_coordinate_integrable n
    · exact hnoise_mean_zero n
  have hnext_integrable : Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => project (fun j => trajectory n omega j - radius (n + 1) *
          (meanSubgradient n omega j + noise n omega j + bias n j)) i - target i)) mu := by
    apply (hpotential_integrable (n + 1)).congr
    filter_upwards [hupdate n] with omega hupdate
    simp [hupdate]
  have hstep := conditional_l2Sq_projected_subgradient_noise_bias_step_le_bounded
    hproject (filtration.le n) htarget (hradius_nonneg n)
    (fun i => htrajectory_adapted i n) (hgap_adapted n)
    (hpotential_integrable n) (hgap_integrable n)
    (by
      simpa [FiniteDimensionalNorms.dot, mul_comm] using
        integrable_finset_sum (Finset.univ : Finset Coord)
          (fun i _ => hnoise_product_integrable n i))
    (hnoise_energy_integrable n) hnoise_dot_zero
    (hsubgradient n) (hgradient_bound n) (hdistance_bound n) hnext_integrable
  calc
    mu[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory (n + 1) omega i - target i) | filtration n] =ᵐ[mu]
        mu[fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => project (fun j => trajectory n omega j - radius (n + 1) *
            (meanSubgradient n omega j + noise n omega j + bias n j)) i - target i)
          | filtration n] := by
          apply condExp_congr_ae
          filter_upwards [hupdate n] with omega hupdate
          simp [hupdate]
    _ ≤ᵐ[mu] fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i) -
        2 * radius (n + 1) * (objective (trajectory n omega) - objective target) +
        (2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
          3 * radius (n + 1) ^ 2 *
            (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n))) := by
          filter_upwards [hstep, hnoise_energy_bound n] with omega hstep henergy
          nlinarith

/--
The quasi-Fejér half of projected stochastic-subgradient descent.  For any
feasible minimizer used as the target, the squared Euclidean potential has an
almost-sure finite limit.  No uniqueness is assumed here: this is the portion
of the argument needed by minimizer-set convergence proofs.
-/
theorem ae_tendsto_l2Sq_potential_of_projected_ssgm
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ}
    {bias : ℕ → Coord → ℝ} {radius : ℕ → ℝ} {target : Coord → ℝ}
    {C distanceBound noiseBound : ℝ} {error : ℕ → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn solutionSpace project)
    (htarget : target ∈ solutionSpace)
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hgap_adapted : StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hgap_integrable : ∀ n, Integrable
      (fun omega => objective (trajectory n omega) - objective target) mu)
    (hnoise_product_integrable : ∀ n i, Integrable
      (fun omega => (trajectory n omega i - target i) * noise n omega i) mu)
    (hnoise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) mu)
    (hnoise_mean_zero : ∀ n i,
      mu[fun omega => noise n omega i | filtration n] =ᵐ[mu] 0)
    (hnoise_energy_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) mu)
    (hnoise_energy_bound : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega) | filtration n]
        ≤ᵐ[mu] fun _ => noiseBound)
    (hupdate : ∀ n, ∀ᵐ omega ∂mu,
      trajectory (n + 1) omega = project (fun i => trajectory n omega i -
        radius (n + 1) *
          (meanSubgradient n omega i + noise n omega i + bias n i)))
    (hsubgradient : ∀ n, ∀ᵐ omega ∂mu,
      FiniteSubgradientOn objective solutionSpace (trajectory n omega)
        (meanSubgradient n omega))
    (hgradient_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C)
    (hdistance_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => trajectory n omega i - target i) ≤ distanceBound)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hstep_error : ∀ n,
      2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
        3 * radius (n + 1) ^ 2 *
          (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n)) ≤ error n)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hmin : IsMinOn objective solutionSpace target) :
    ∀ᵐ omega ∂mu, ∃ limit : ℝ, Tendsto
      (fun n => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) atTop (nhds limit) := by
  let potential : ℕ → Omega → ℝ := fun n omega =>
    FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i)
  let loss : ℕ → Omega → ℝ := fun n omega =>
    2 * radius (n + 1) * (objective (trajectory n omega) - objective target)
  have hpotential_adapted : StronglyAdapted filtration potential := by
    apply stronglyAdapted_finiteL2Sq
    intro i
    exact (htrajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
  have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega := by
    intro n
    filter_upwards [] with omega
    exact FiniteDimensionalNorms.normL2Sq_nonneg _
  have hloss_adapted : StronglyAdapted filtration loss := by
    intro n
    exact (hgap_adapted n).const_mul (2 * radius (n + 1))
  have hloss_integrable : ∀ n, Integrable (loss n) mu := by
    intro n
    exact (hgap_integrable n).const_mul (2 * radius (n + 1))
  have hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega := by
    intro n
    filter_upwards [htrajectory_mem] with omega hmem
    dsimp [loss]
    exact mul_nonneg (mul_nonneg (by norm_num) (hradius_nonneg n))
      (sub_nonneg.mpr (hmin (hmem n)))
  apply ae_tendsto_potential_of_condExp_descent (error := error) hpotential_adapted hloss_adapted
    hpotential_integrable hloss_integrable hpotential_nonneg hloss_nonneg
  · intro n
    have hdescent := conditional_l2Sq_descent_of_projected_ssgm
      hproject htarget htrajectory_adapted hgap_adapted hpotential_integrable
      hgap_integrable hnoise_product_integrable hnoise_coordinate_integrable
      hnoise_mean_zero hnoise_energy_integrable hnoise_energy_bound hupdate
      hsubgradient hgradient_bound hdistance_bound hradius_nonneg n
    filter_upwards [hdescent] with omega hdescent
    dsimp [potential, loss]
    linarith [hdescent, hstep_error n]
  · exact herror
  · exact herror_nonneg

/--
The objective-gap half of projected stochastic-subgradient descent.  For any
feasible minimizer used as a target, the weighted objective gaps are almost
surely summable.  As with the potential theorem, this statement does not use
uniqueness of the minimizer.
-/
theorem ae_summable_weighted_objective_gap_of_projected_ssgm
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ}
    {bias : ℕ → Coord → ℝ} {radius : ℕ → ℝ} {target : Coord → ℝ}
    {C distanceBound noiseBound : ℝ} {error : ℕ → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn solutionSpace project)
    (htarget : target ∈ solutionSpace)
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hgap_adapted : StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hgap_integrable : ∀ n, Integrable
      (fun omega => objective (trajectory n omega) - objective target) mu)
    (hnoise_product_integrable : ∀ n i, Integrable
      (fun omega => (trajectory n omega i - target i) * noise n omega i) mu)
    (hnoise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) mu)
    (hnoise_mean_zero : ∀ n i,
      mu[fun omega => noise n omega i | filtration n] =ᵐ[mu] 0)
    (hnoise_energy_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) mu)
    (hnoise_energy_bound : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega) | filtration n]
        ≤ᵐ[mu] fun _ => noiseBound)
    (hupdate : ∀ n, ∀ᵐ omega ∂mu,
      trajectory (n + 1) omega = project (fun i => trajectory n omega i -
        radius (n + 1) *
          (meanSubgradient n omega i + noise n omega i + bias n i)))
    (hsubgradient : ∀ n, ∀ᵐ omega ∂mu,
      FiniteSubgradientOn objective solutionSpace (trajectory n omega)
        (meanSubgradient n omega))
    (hgradient_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C)
    (hdistance_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => trajectory n omega i - target i) ≤ distanceBound)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hstep_error : ∀ n,
      2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
        3 * radius (n + 1) ^ 2 *
          (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n)) ≤ error n)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hmin : IsMinOn objective solutionSpace target) :
    ∀ᵐ omega ∂mu, Summable (fun n =>
      radius (n + 1) * (objective (trajectory n omega) - objective target)) := by
  let potential : ℕ → Omega → ℝ := fun n omega =>
    FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i)
  let loss : ℕ → Omega → ℝ := fun n omega =>
    2 * radius (n + 1) * (objective (trajectory n omega) - objective target)
  have hpotential_adapted : StronglyAdapted filtration potential := by
    apply stronglyAdapted_finiteL2Sq
    intro i
    exact (htrajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
  have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ potential n omega := by
    intro n
    filter_upwards [] with omega
    exact FiniteDimensionalNorms.normL2Sq_nonneg _
  have hloss_adapted : StronglyAdapted filtration loss := by
    intro n
    exact (hgap_adapted n).const_mul (2 * radius (n + 1))
  have hloss_integrable : ∀ n, Integrable (loss n) mu := by
    intro n
    exact (hgap_integrable n).const_mul (2 * radius (n + 1))
  have hloss_nonneg : ∀ n, ∀ᵐ omega ∂mu, 0 ≤ loss n omega := by
    intro n
    filter_upwards [htrajectory_mem] with omega hmem
    dsimp [loss]
    exact mul_nonneg (mul_nonneg (by norm_num) (hradius_nonneg n))
      (sub_nonneg.mpr (hmin (hmem n)))
  have hstep : ∀ n,
      mu[potential (n + 1) | filtration n] ≤ᵐ[mu]
        fun omega => potential n omega + error n - loss n omega := by
    intro n
    have hdescent := conditional_l2Sq_descent_of_projected_ssgm
      hproject htarget htrajectory_adapted hgap_adapted hpotential_integrable
      hgap_integrable hnoise_product_integrable hnoise_coordinate_integrable
      hnoise_mean_zero hnoise_energy_integrable hnoise_energy_bound hupdate
      hsubgradient hgradient_bound hdistance_bound hradius_nonneg n
    filter_upwards [hdescent] with omega hdescent
    dsimp [potential, loss]
    linarith [hdescent, hstep_error n]
  filter_upwards [ae_summable_loss_of_condExp_descent
    hpotential_adapted hloss_adapted hpotential_integrable hloss_integrable
    hpotential_nonneg hloss_nonneg hstep herror herror_nonneg] with omega hsum
  have hscaled := hsum.mul_left (1 / 2)
  convert hscaled using 1
  ext n
  dsimp [loss]
  ring

theorem ae_tendsto_finite_coordinate_trajectory_of_projected_ssgm
    {Omega Coord : Type*} {mOmega : MeasurableSpace Omega} {mu : Measure Omega}
    [IsProbabilityMeasure mu] [Fintype Coord]
    {filtration : Filtration (Ω := Omega) ℕ mOmega}
    {solutionSpace : Set (Coord → ℝ)} {objective : (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory meanSubgradient noise : ℕ → Omega → Coord → ℝ}
    {bias : ℕ → Coord → ℝ} {radius : ℕ → ℝ} {target : Coord → ℝ}
    {C distanceBound noiseBound : ℝ} {error : ℕ → ℝ}
    (hproject : SquaredDistanceNonexpansiveOn solutionSpace project)
    (htarget : target ∈ solutionSpace)
    (htrajectory_adapted : ∀ i,
      StronglyAdapted filtration (fun n omega => trajectory n omega i))
    (hgap_adapted : StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target))
    (hpotential_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => trajectory n omega i - target i)) mu)
    (hgap_integrable : ∀ n, Integrable
      (fun omega => objective (trajectory n omega) - objective target) mu)
    (hnoise_product_integrable : ∀ n i, Integrable
      (fun omega => (trajectory n omega i - target i) * noise n omega i) mu)
    (hnoise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) mu)
    (hnoise_mean_zero : ∀ n i,
      mu[fun omega => noise n omega i | filtration n] =ᵐ[mu] 0)
    (hnoise_energy_integrable : ∀ n, Integrable
      (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) mu)
    (hnoise_energy_bound : ∀ n,
      mu[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega) | filtration n]
        ≤ᵐ[mu] fun _ => noiseBound)
    (hupdate : ∀ n, ∀ᵐ omega ∂mu,
      trajectory (n + 1) omega = project (fun i => trajectory n omega i -
        radius (n + 1) *
          (meanSubgradient n omega i + noise n omega i + bias n i)))
    (hsubgradient : ∀ n, ∀ᵐ omega ∂mu,
      FiniteSubgradientOn objective solutionSpace (trajectory n omega)
        (meanSubgradient n omega))
    (hgradient_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C)
    (hdistance_bound : ∀ n, ∀ᵐ omega ∂mu,
      FiniteDimensionalNorms.l2 (fun i => trajectory n omega i - target i) ≤ distanceBound)
    (hradius_nonneg : ∀ n, 0 ≤ radius (n + 1))
    (hstep_error : ∀ n,
      2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
        3 * radius (n + 1) ^ 2 *
          (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n)) ≤ error n)
    (herror : Summable error) (herror_nonneg : ∀ n, 0 ≤ error n)
    (hradius_diverges : Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop)
    (htrajectory_mem : ∀ᵐ omega ∂mu, ∀ n, trajectory n omega ∈ solutionSpace)
    (hcompact : IsCompact solutionSpace)
    (hC : 0 ≤ C)
    (hsub_exists_bounded : ∀ x, x ∈ solutionSpace → ∃ g,
      FiniteSubgradientOn objective solutionSpace x g ∧
        FiniteDimensionalNorms.l2 g ≤ C)
    (hmin : IsMinOn objective solutionSpace target)
    (hunique : ∀ x, x ∈ solutionSpace → objective x = objective target → x = target) :
    ∀ᵐ omega ∂mu, Tendsto (fun n => trajectory n omega) atTop (nhds target) := by
  let loss : ℕ → Omega → ℝ := fun n omega =>
    2 * radius (n + 1) * (objective (trajectory n omega) - objective target)
  apply ae_tendsto_finite_coordinate_trajectory_of_condExp_l2Sq_descent_of_compact_bounded_subgradients
    htrajectory_adapted htrajectory_mem hpotential_integrable
  · intro n
    exact (hgap_adapted n).const_mul (2 * radius (n + 1))
  · intro n
    exact (hgap_integrable n).const_mul (2 * radius (n + 1))
  · intro n omega
    rfl
  · intro n
    have hnoise_dot_zero :
        mu[fun omega => FiniteDimensionalNorms.dot (noise n omega)
          (fun i => trajectory n omega i - target i) | filtration n] =ᵐ[mu] 0 := by
      apply condExp_finiteDot_eq_zero_of_coordinatewise
      · intro i
        exact (htrajectory_adapted i n).sub stronglyMeasurable_const
      · intro i
        simpa [mul_comm] using hnoise_product_integrable n i
      · exact hnoise_coordinate_integrable n
      · exact hnoise_mean_zero n
    have hnext_integrable : Integrable
        (fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => project (fun j => trajectory n omega j - radius (n + 1) *
            (meanSubgradient n omega j + noise n omega j + bias n j)) i - target i)) mu := by
      apply (hpotential_integrable (n + 1)).congr
      filter_upwards [hupdate n] with omega hupdate
      simp [hupdate]
    have hstep := conditional_l2Sq_projected_subgradient_noise_bias_step_le_bounded
      hproject (filtration.le n) htarget (hradius_nonneg n)
      (fun i => htrajectory_adapted i n) (hgap_adapted n)
      (hpotential_integrable n) (hgap_integrable n)
      (by
        simpa [FiniteDimensionalNorms.dot, mul_comm] using
          integrable_finset_sum (Finset.univ : Finset Coord)
            (fun i _ => hnoise_product_integrable n i))
      (hnoise_energy_integrable n) hnoise_dot_zero
      (hsubgradient n) (hgradient_bound n) (hdistance_bound n) hnext_integrable
    calc
      mu[fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => trajectory (n + 1) omega i - target i) | filtration n] =ᵐ[mu]
          mu[fun omega => FiniteDimensionalNorms.l2Sq
            (fun i => project (fun j => trajectory n omega j - radius (n + 1) *
              (meanSubgradient n omega j + noise n omega j + bias n j)) i - target i)
            | filtration n] := by
            apply condExp_congr_ae
            filter_upwards [hupdate n] with omega hupdate
            simp [hupdate]
      _ ≤ᵐ[mu] fun omega =>
          FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i) -
            loss n omega +
            (2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
              3 * radius (n + 1) ^ 2 *
                (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n))) := by
            filter_upwards [hstep, hnoise_energy_bound n] with omega hstep henergy
            dsimp [loss]
            nlinarith
      _ ≤ᵐ[mu] fun omega =>
          FiniteDimensionalNorms.l2Sq (fun i => trajectory n omega i - target i) +
            error n - loss n omega := by
            filter_upwards [] with omega
            dsimp [loss]
            linarith [hstep_error n]
  · exact herror
  · exact herror_nonneg
  · exact hradius_nonneg
  · exact hradius_diverges
  · exact hcompact
  · exact hC
  · exact hsub_exists_bounded
  · exact hmin
  · exact hunique

/--
The deterministic error budget in projected stochastic-subgradient descent is
summable when squared step sizes are summable, the step--bias products are
summable, and the bias norm is uniformly bounded.
-/
theorem summable_projected_ssgm_error
    {Coord : Type*} [Fintype Coord]
    (radius : ℕ → ℝ) (bias : ℕ → Coord → ℝ)
    (C noiseBound distanceBound biasBound : ℝ)
    (hradius_sq : Summable (fun n => radius (n + 1) ^ 2))
    (hstep_bias : Summable (fun n =>
      radius (n + 1) * FiniteDimensionalNorms.l2 (bias n)))
    (hbiasBound_nonneg : 0 ≤ biasBound)
    (hbias_bound : ∀ n,
      FiniteDimensionalNorms.l2 (bias n) ≤ biasBound) :
    Summable (fun n =>
      2 * radius (n + 1) * distanceBound * FiniteDimensionalNorms.l2 (bias n) +
        3 * radius (n + 1) ^ 2 *
          (C ^ 2 + noiseBound + FiniteDimensionalNorms.l2Sq (bias n))) := by
  have hlinear : Summable (fun n =>
      2 * distanceBound *
        (radius (n + 1) * FiniteDimensionalNorms.l2 (bias n))) :=
    hstep_bias.mul_left (2 * distanceBound)
  have hconstant : Summable (fun n =>
      3 * (C ^ 2 + noiseBound) * radius (n + 1) ^ 2) :=
    hradius_sq.mul_left (3 * (C ^ 2 + noiseBound))
  have hquadraticBound : Summable (fun n =>
      3 * biasBound ^ 2 * radius (n + 1) ^ 2) :=
    hradius_sq.mul_left (3 * biasBound ^ 2)
  have hquadratic : Summable (fun n =>
      3 * radius (n + 1) ^ 2 * FiniteDimensionalNorms.l2Sq (bias n)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (radius (n + 1))))
        (FiniteDimensionalNorms.normL2Sq_nonneg _)
    · intro n
      have hnorm_nonneg : 0 ≤ FiniteDimensionalNorms.l2 (bias n) :=
        FiniteDimensionalNorms.normL2_nonneg _
      have hsq : FiniteDimensionalNorms.l2Sq (bias n) ≤ biasBound ^ 2 := by
        rw [← FiniteDimensionalNorms.normL2_sq_eq_normL2Sq]
        exact (sq_le_sq₀ hnorm_nonneg hbiasBound_nonneg).mpr (hbias_bound n)
      calc
        3 * radius (n + 1) ^ 2 * FiniteDimensionalNorms.l2Sq (bias n) ≤
            3 * radius (n + 1) ^ 2 * biasBound ^ 2 :=
          mul_le_mul_of_nonneg_left hsq
            (mul_nonneg (by norm_num) (sq_nonneg (radius (n + 1))))
        _ = 3 * biasBound ^ 2 * radius (n + 1) ^ 2 := by ring
    · exact hquadraticBound
  convert (hlinear.add hconstant).add hquadratic using 1
  ext n
  ring

/-- The potential-convergence component available from a bundled projected
stochastic-subgradient execution, independently of how its minimizers are
identified. -/
theorem ProjectedStochasticSubgradientExecution.ae_tendsto_l2Sq_potential
    {Coord : Type*} [Fintype Coord]
    (S : ProjectedStochasticSubgradientExecution Coord) :
    ∀ᵐ omega ∂S.μ, ∃ limit : ℝ, Tendsto
      (fun n => FiniteDimensionalNorms.l2Sq
        (fun i => S.trajectory n omega i - S.target i)) atTop (nhds limit) := by
  letI := S.measurableSpace
  letI := S.probability
  let error : ℕ → ℝ := fun n =>
    2 * S.radius (n + 1) * S.distanceBound *
        FiniteDimensionalNorms.l2 (S.bias n) +
      3 * S.radius (n + 1) ^ 2 *
        (S.C1 ^ 2 + S.C2 + FiniteDimensionalNorms.l2Sq (S.bias n))
  have herror : Summable error := by
    exact summable_projected_ssgm_error
      S.radius S.bias S.C1 S.C2 S.distanceBound S.biasBound
      S.radius_sq_summable S.step_bias_summable S.biasBound_nonneg S.bias_bound
  have herror_nonneg : ∀ n, 0 ≤ error n := by
    intro n
    dsimp [error]
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
          S.distanceBound_nonneg)
        (FiniteDimensionalNorms.normL2_nonneg _)
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
        (add_nonneg
          (add_nonneg (sq_nonneg S.C1) S.C2_nonneg)
          (FiniteDimensionalNorms.normL2Sq_nonneg _))
  exact ae_tendsto_l2Sq_potential_of_projected_ssgm
    (error := error)
    S.project_nonexpansive S.target_mem_solutionSpace S.trajectory_adapted
    S.objective_gap_adapted S.potential_integrable S.objective_gap_integrable
    S.noise_product_integrable S.noise_coordinate_integrable S.noise_mean_zero
    S.noise_energy_integrable S.noise_energy_bound S.update S.subgradient
    S.gradient_bound S.distance_bound S.radius_nonneg (fun n => le_rfl)
    herror herror_nonneg S.trajectory_mem_solutionSpace S.target_minimizes

/-- Every execution satisfying the projected stochastic-subgradient hypotheses
converges almost surely to its unique feasible minimizer. -/
theorem ProjectedStochasticSubgradientExecution.ae_tendsto
    {Coord : Type*} [Fintype Coord]
    (S : ProjectedStochasticSubgradientExecution Coord) :
    ∀ᵐ omega ∂S.μ,
      Tendsto (fun n => S.trajectory n omega) atTop (nhds S.target) := by
  letI := S.measurableSpace
  letI := S.probability
  let error : ℕ → ℝ := fun n =>
    2 * S.radius (n + 1) * S.distanceBound *
        FiniteDimensionalNorms.l2 (S.bias n) +
      3 * S.radius (n + 1) ^ 2 *
        (S.C1 ^ 2 + S.C2 + FiniteDimensionalNorms.l2Sq (S.bias n))
  have herror : Summable error := by
    exact summable_projected_ssgm_error
      S.radius S.bias S.C1 S.C2 S.distanceBound S.biasBound
      S.radius_sq_summable S.step_bias_summable S.biasBound_nonneg S.bias_bound
  have herror_nonneg : ∀ n, 0 ≤ error n := by
    intro n
    dsimp [error]
    apply add_nonneg
    · exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
          S.distanceBound_nonneg)
        (FiniteDimensionalNorms.normL2_nonneg _)
    · exact mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
        (add_nonneg
          (add_nonneg (sq_nonneg S.C1) S.C2_nonneg)
          (FiniteDimensionalNorms.normL2Sq_nonneg _))
  exact ae_tendsto_finite_coordinate_trajectory_of_projected_ssgm
    (error := error)
    S.project_nonexpansive S.target_mem_solutionSpace S.trajectory_adapted
    S.objective_gap_adapted S.potential_integrable S.objective_gap_integrable
    S.noise_product_integrable S.noise_coordinate_integrable S.noise_mean_zero
    S.noise_energy_integrable S.noise_energy_bound S.update S.subgradient
    S.gradient_bound S.distance_bound S.radius_nonneg (fun n => le_rfl)
    herror herror_nonneg S.radius_diverges
    S.trajectory_mem_solutionSpace S.compact_solutionSpace S.C1_nonneg
    S.subgradient_exists_bounded S.target_minimizes S.target_unique

/--
Primitive data for projected stochastic-subgradient descent to a possibly
non-singleton minimizer set.  In contrast to the fixed-target execution, the
target-dependent integrability and distance estimates are required uniformly
as source hypotheses over the designated minimizer set.  The record contains
no convergence conclusion or result-shaped certificate.
-/
structure ProjectedStochasticSubgradientMinimizerSetExecution
    (Coord : Type*) [Fintype Coord] where
  Ω : Type*
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  filtration : Filtration (Ω := Ω) ℕ measurableSpace
  trajectory : ℕ → Ω → Coord → ℝ
  meanSubgradient : ℕ → Ω → Coord → ℝ
  noise : ℕ → Ω → Coord → ℝ
  bias : ℕ → Coord → ℝ
  radius : ℕ → ℝ
  solutionSpace : Set (Coord → ℝ)
  objective : (Coord → ℝ) → ℝ
  project : (Coord → ℝ) → Coord → ℝ
  targetSet : Set (Coord → ℝ)
  reference : Coord → ℝ
  reference_mem_targetSet : reference ∈ targetSet
  targetSet_subset_solutionSpace : targetSet ⊆ solutionSpace
  targetSet_minimizes : ∀ target, target ∈ targetSet →
    IsMinOn objective solutionSpace target
  minimizer_mem_targetSet : ∀ x, x ∈ solutionSpace →
    IsMinOn objective solutionSpace x → x ∈ targetSet
  project_nonexpansive : SquaredDistanceNonexpansiveOn solutionSpace project
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun n omega => trajectory n omega i)
  target_objective_gap_adapted : ∀ target, target ∈ targetSet →
    StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target)
  target_potential_integrable : ∀ target, target ∈ targetSet → ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory n omega i - target i)) μ
  target_objective_gap_integrable : ∀ target, target ∈ targetSet → ∀ n, Integrable
    (fun omega => objective (trajectory n omega) - objective target) μ
  target_noise_product_integrable : ∀ target, target ∈ targetSet → ∀ n i, Integrable
    (fun omega => (trajectory n omega i - target i) * noise n omega i) μ
  noise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) μ
  noise_mean_zero : ∀ n i,
    μ[fun omega => noise n omega i | filtration n] =ᵐ[μ] 0
  noise_energy_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) μ
  C : ℝ
  noiseBound : ℝ
  target_distanceBound : (Coord → ℝ) → ℝ
  C_nonneg : 0 ≤ C
  noiseBound_nonneg : 0 ≤ noiseBound
  target_distanceBound_nonneg : ∀ target, target ∈ targetSet →
    0 ≤ target_distanceBound target
  noise_energy_bound : ∀ n,
    μ[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)
      | filtration n] ≤ᵐ[μ] fun _ => noiseBound
  update : ∀ n, ∀ᵐ omega ∂μ,
    trajectory (n + 1) omega = project (fun i => trajectory n omega i -
      radius (n + 1) *
        (meanSubgradient n omega i + noise n omega i + bias n i))
  subgradient : ∀ n, ∀ᵐ omega ∂μ,
    FiniteSubgradientOn objective solutionSpace (trajectory n omega)
      (meanSubgradient n omega)
  gradient_bound : ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C
  target_distance_bound : ∀ target, target ∈ targetSet → ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2
      (fun i => trajectory n omega i - target i) ≤ target_distanceBound target
  radius_nonneg : ∀ n, 0 ≤ radius (n + 1)
  biasBound : ℝ
  biasBound_nonneg : 0 ≤ biasBound
  bias_bound : ∀ n, FiniteDimensionalNorms.l2 (bias n) ≤ biasBound
  step_bias_summable : Summable (fun n =>
    radius (n + 1) * FiniteDimensionalNorms.l2 (bias n))
  radius_sq_summable : Summable (fun n => radius (n + 1) ^ 2)
  radius_diverges : Tendsto
    (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop
  trajectory_mem_solutionSpace : ∀ᵐ omega ∂μ, ∀ n,
    trajectory n omega ∈ solutionSpace
  compact_solutionSpace : IsCompact solutionSpace
  objective_continuous : ContinuousOn objective solutionSpace

/--
Set-valued projected stochastic-subgradient data with a sample-dependent
perturbation of the realized direction.  The perturbation is controlled by a
conditional, target-dependent descent-error budget rather than by a
deterministic bias vector.  This form accommodates rare exceptional updates
without encoding any application-specific event in the reusable API.
-/
structure PerturbedProjectedStochasticSubgradientMinimizerSetExecution
    (Coord : Type*) [Fintype Coord] where
  Ω : Type*
  [measurableSpace : MeasurableSpace Ω]
  μ : Measure Ω
  probability : IsProbabilityMeasure μ
  filtration : Filtration (Ω := Ω) ℕ measurableSpace
  trajectory : ℕ → Ω → Coord → ℝ
  meanSubgradient : ℕ → Ω → Coord → ℝ
  noise : ℕ → Ω → Coord → ℝ
  perturbation : ℕ → Ω → Coord → ℝ
  radius : ℕ → ℝ
  solutionSpace : Set (Coord → ℝ)
  objective : (Coord → ℝ) → ℝ
  project : (Coord → ℝ) → Coord → ℝ
  targetSet : Set (Coord → ℝ)
  reference : Coord → ℝ
  reference_mem_targetSet : reference ∈ targetSet
  targetSet_subset_solutionSpace : targetSet ⊆ solutionSpace
  targetSet_minimizes : ∀ target, target ∈ targetSet →
    IsMinOn objective solutionSpace target
  minimizer_mem_targetSet : ∀ x, x ∈ solutionSpace →
    IsMinOn objective solutionSpace x → x ∈ targetSet
  project_nonexpansive : SquaredDistanceNonexpansiveOn solutionSpace project
  trajectory_adapted : ∀ i,
    StronglyAdapted filtration (fun n omega => trajectory n omega i)
  target_objective_gap_adapted : ∀ target, target ∈ targetSet →
    StronglyAdapted filtration
      (fun n omega => objective (trajectory n omega) - objective target)
  target_potential_integrable : ∀ target, target ∈ targetSet → ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq
      (fun i => trajectory n omega i - target i)) μ
  target_objective_gap_integrable : ∀ target, target ∈ targetSet → ∀ n, Integrable
    (fun omega => objective (trajectory n omega) - objective target) μ
  target_noise_product_integrable : ∀ target, target ∈ targetSet → ∀ n i, Integrable
    (fun omega => (trajectory n omega i - target i) * noise n omega i) μ
  noise_coordinate_integrable : ∀ n i, Integrable (fun omega => noise n omega i) μ
  noise_mean_zero : ∀ n i,
    μ[fun omega => noise n omega i | filtration n] =ᵐ[μ] 0
  noise_energy_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)) μ
  perturbation_norm_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2 (perturbation n omega)) μ
  perturbation_energy_integrable : ∀ n, Integrable
    (fun omega => FiniteDimensionalNorms.l2Sq (perturbation n omega)) μ
  C : ℝ
  noiseBound : ℝ
  target_distanceBound : (Coord → ℝ) → ℝ
  C_nonneg : 0 ≤ C
  noiseBound_nonneg : 0 ≤ noiseBound
  target_distanceBound_nonneg : ∀ target, target ∈ targetSet →
    0 ≤ target_distanceBound target
  noise_energy_bound : ∀ n,
    μ[fun omega => FiniteDimensionalNorms.l2Sq (noise n omega)
      | filtration n] ≤ᵐ[μ] fun _ => noiseBound
  perturbation_error : (Coord → ℝ) → ℕ → ℝ
  perturbation_error_nonneg : ∀ target, target ∈ targetSet → ∀ n,
    0 ≤ perturbation_error target n
  perturbation_error_summable : ∀ target, target ∈ targetSet →
    Summable (perturbation_error target)
  perturbation_error_bound : ∀ target, target ∈ targetSet → ∀ n,
    μ[fun omega =>
      2 * radius (n + 1) * target_distanceBound target *
          FiniteDimensionalNorms.l2 (perturbation n omega) +
        3 * radius (n + 1) ^ 2 *
          FiniteDimensionalNorms.l2Sq (perturbation n omega) | filtration n] ≤ᵐ[μ]
      fun _ => perturbation_error target n
  update : ∀ n, ∀ᵐ omega ∂μ,
    trajectory (n + 1) omega = project (fun i => trajectory n omega i -
      radius (n + 1) *
        (meanSubgradient n omega i + noise n omega i + perturbation n omega i))
  subgradient : ∀ n, ∀ᵐ omega ∂μ,
    FiniteSubgradientOn objective solutionSpace (trajectory n omega)
      (meanSubgradient n omega)
  gradient_bound : ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2 (meanSubgradient n omega) ≤ C
  target_distance_bound : ∀ target, target ∈ targetSet → ∀ n, ∀ᵐ omega ∂μ,
    FiniteDimensionalNorms.l2
      (fun i => trajectory n omega i - target i) ≤ target_distanceBound target
  radius_nonneg : ∀ n, 0 ≤ radius (n + 1)
  radius_sq_summable : Summable (fun n => radius (n + 1) ^ 2)
  radius_diverges : Tendsto
    (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1)) atTop atTop
  trajectory_mem_solutionSpace : ∀ᵐ omega ∂μ, ∀ n,
    trajectory n omega ∈ solutionSpace
  compact_solutionSpace : IsCompact solutionSpace
  objective_continuous : ContinuousOn objective solutionSpace

/--
A minimizer-set execution whose stochastic direction comes from one sampled
cost at each step.  This extends the set-valued convergence inputs with the
algorithmic sampling layer, but still stores no convergence conclusion.
-/
structure SampledProjectedStochasticSubgradientMinimizerSetExecution
    (Coord : Type*) [Fintype Coord] extends
    ProjectedStochasticSubgradientMinimizerSetExecution Coord where
  Sample : Type*
  sample : ℕ → Ω → Sample
  sampleCost : Sample → (Coord → ℝ) → ℝ
  sampledDirection : ℕ → Ω → Coord → ℝ
  sampled_direction_subgradient : ∀ n, ∀ᵐ omega ∂μ,
    FiniteSubgradientOn (sampleCost (sample n omega)) solutionSpace
      (trajectory n omega) (sampledDirection n omega)
  sampled_direction_decomposition : ∀ n, ∀ᵐ omega ∂μ,
    sampledDirection n omega = fun i =>
      meanSubgradient n omega i + noise n omega i + bias n i

/--
A conditionally fresh sample stream for a projected stochastic-subgradient
execution whose objective may have a non-singleton minimizer set.  This is the
same sampling notion as `AdaptedConditionalLawSampleStream`; it is stated on
the set-valued execution directly so applications need not introduce an
artificial distinguished minimizer merely to establish martingale centering.
-/
structure AdaptedConditionalLawSampledMinimizerSetStream
    {Coord : Type*} [Fintype Coord]
    (S : SampledProjectedStochasticSubgradientMinimizerSetExecution Coord)
    [MeasurableSpace S.Sample] where
  sampleMeasure : Measure S.Sample
  sampleProbability : IsProbabilityMeasure sampleMeasure
  sample_measurable : ∀ n,
    @Measurable S.Ω S.Sample S.measurableSpace inferInstance (S.sample n)
  conditional_integral_eq_adapted : ∀ n (test : S.Ω → S.Sample → ℝ),
    (∀ sample, StronglyMeasurable[S.filtration n] (fun omega => test omega sample)) →
      Integrable (fun omega => test omega (S.sample n omega)) S.μ →
        S.μ[fun omega => test omega (S.sample n omega) | S.filtration n] =ᵐ[S.μ]
          fun omega => ∫ sample, test omega sample ∂sampleMeasure

/--
Centering a state-dependent statistic of a fresh sample by its population mean
has conditional mean zero in the minimizer-set stochastic-subgradient model.
This is independent of whether the minimizer set is a singleton.
-/
theorem AdaptedConditionalLawSampledMinimizerSetStream.condExp_centered_statistic_eq_zero
    {Coord : Type*} [Fintype Coord]
    {S : SampledProjectedStochasticSubgradientMinimizerSetExecution Coord}
    [MeasurableSpace S.Sample]
    (L : AdaptedConditionalLawSampledMinimizerSetStream S)
    (n : ℕ) (test : S.Ω → S.Sample → ℝ)
    (hadapted : ∀ sample,
      StronglyMeasurable[S.filtration n] (fun omega => test omega sample))
    (hintegrable : Integrable (fun omega => test omega (S.sample n omega)) S.μ)
    (hpopulation_measurable : StronglyMeasurable[S.filtration n]
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure))
    (hpopulation_integrable : Integrable
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure) S.μ) :
    S.μ[(fun omega => test omega (S.sample n omega)) -
      (fun omega => ∫ sample, test omega sample ∂L.sampleMeasure) | S.filtration n] =ᵐ[S.μ] 0 := by
  letI := S.measurableSpace
  letI := S.probability
  have hpopulation_conditional :
      S.μ[fun omega => ∫ sample, test omega sample ∂L.sampleMeasure | S.filtration n] =ᵐ[S.μ]
        fun omega => ∫ sample, test omega sample ∂L.sampleMeasure := by
    rw [condExp_of_stronglyMeasurable (S.filtration.le n) hpopulation_measurable
      hpopulation_integrable]
  filter_upwards [
    condExp_sub hintegrable hpopulation_integrable (S.filtration n),
    L.conditional_integral_eq_adapted n test hadapted hintegrable,
    hpopulation_conditional] with omega hsub hsample hpopulation
  rw [hsub]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [hsample, hpopulation]
  ring

/--
The minimizer-set execution update is equivalently the projected update by the
realized sampled direction.  This is the direct algorithmic form used by
sampled projected methods.
-/
theorem SampledProjectedStochasticSubgradientMinimizerSetExecution.update_eq_sampled_direction
    {Coord : Type*} [Fintype Coord]
    (S : SampledProjectedStochasticSubgradientMinimizerSetExecution Coord) (n : ℕ) :
    ∀ᵐ omega ∂S.μ,
      S.trajectory (n + 1) omega = S.project (fun i => S.trajectory n omega i -
        S.radius (n + 1) * S.sampledDirection n omega i) := by
  filter_upwards [S.update n, S.sampled_direction_decomposition n] with omega hupdate hdirection
  rw [hupdate]
  apply congrArg S.project
  funext i
  rw [hdirection]

/--
The generic nonunique-minimizer convergence theorem for a projected
stochastic-subgradient execution.  Pointwise target estimates are reduced to
finite affine anchors internally; no uniqueness assumption is needed.
-/
theorem ProjectedStochasticSubgradientMinimizerSetExecution.outcomeIndexedConvergesToSet
    {Coord : Type*} [Fintype Coord]
    (S : ProjectedStochasticSubgradientMinimizerSetExecution Coord) :
    @OutcomeIndexedConvergesToSet S.Ω (Coord → ℝ) S.measurableSpace inferInstance
      S.μ S.trajectory S.targetSet := by
  letI := S.measurableSpace
  letI := S.probability
  apply outcomeIndexedConvergesToSet_of_ae_target_potential_limits_and_ae_summable_gaps
  · intro target htarget
    let error : ℕ → ℝ := fun n =>
      2 * S.radius (n + 1) * S.target_distanceBound target *
          FiniteDimensionalNorms.l2 (S.bias n) +
        3 * S.radius (n + 1) ^ 2 *
          (S.C ^ 2 + S.noiseBound + FiniteDimensionalNorms.l2Sq (S.bias n))
    have herror : Summable error := by
      exact summable_projected_ssgm_error
        S.radius S.bias S.C S.noiseBound (S.target_distanceBound target) S.biasBound
        S.radius_sq_summable S.step_bias_summable S.biasBound_nonneg S.bias_bound
    have herror_nonneg : ∀ n, 0 ≤ error n := by
      intro n
      dsimp [error]
      apply add_nonneg
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
            (S.target_distanceBound_nonneg target htarget))
          (FiniteDimensionalNorms.normL2_nonneg _)
      · exact mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
          (add_nonneg
            (add_nonneg (sq_nonneg S.C) S.noiseBound_nonneg)
            (FiniteDimensionalNorms.normL2Sq_nonneg _))
    exact ae_tendsto_l2Sq_potential_of_projected_ssgm
      (error := error)
      S.project_nonexpansive (S.targetSet_subset_solutionSpace htarget)
      S.trajectory_adapted (S.target_objective_gap_adapted target htarget)
      (S.target_potential_integrable target htarget)
      (S.target_objective_gap_integrable target htarget)
      (S.target_noise_product_integrable target htarget)
      S.noise_coordinate_integrable S.noise_mean_zero S.noise_energy_integrable
      S.noise_energy_bound S.update S.subgradient S.gradient_bound
      (S.target_distance_bound target htarget) S.radius_nonneg
      (fun n => le_rfl) herror herror_nonneg
      S.trajectory_mem_solutionSpace (S.targetSet_minimizes target htarget)
  · exact S.trajectory_mem_solutionSpace
  · exact S.compact_solutionSpace
  · exact S.objective_continuous
  · exact S.targetSet_minimizes S.reference S.reference_mem_targetSet
  · exact S.minimizer_mem_targetSet
  · exact S.radius_nonneg
  · exact S.radius_diverges
  · exact ae_summable_weighted_objective_gap_of_projected_ssgm
      (error := fun n =>
        2 * S.radius (n + 1) * S.target_distanceBound S.reference *
            FiniteDimensionalNorms.l2 (S.bias n) +
          3 * S.radius (n + 1) ^ 2 *
            (S.C ^ 2 + S.noiseBound + FiniteDimensionalNorms.l2Sq (S.bias n)))
      S.project_nonexpansive
      (S.targetSet_subset_solutionSpace S.reference_mem_targetSet)
      S.trajectory_adapted
      (S.target_objective_gap_adapted S.reference S.reference_mem_targetSet)
      (S.target_potential_integrable S.reference S.reference_mem_targetSet)
      (S.target_objective_gap_integrable S.reference S.reference_mem_targetSet)
      (S.target_noise_product_integrable S.reference S.reference_mem_targetSet)
      S.noise_coordinate_integrable S.noise_mean_zero S.noise_energy_integrable
      S.noise_energy_bound S.update S.subgradient S.gradient_bound
      (S.target_distance_bound S.reference S.reference_mem_targetSet) S.radius_nonneg
      (fun n => le_rfl)
      (summable_projected_ssgm_error
        S.radius S.bias S.C S.noiseBound (S.target_distanceBound S.reference) S.biasBound
        S.radius_sq_summable S.step_bias_summable S.biasBound_nonneg S.bias_bound)
      (fun n => by
        dsimp
        apply add_nonneg
        · exact mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
              (S.target_distanceBound_nonneg S.reference S.reference_mem_targetSet))
            (FiniteDimensionalNorms.normL2_nonneg _)
        · exact mul_nonneg
            (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
            (add_nonneg
              (add_nonneg (sq_nonneg S.C) S.noiseBound_nonneg)
              (FiniteDimensionalNorms.normL2Sq_nonneg _)))
      S.trajectory_mem_solutionSpace
      (S.targetSet_minimizes S.reference S.reference_mem_targetSet)

/--
The nonunique-minimizer convergence endpoint for projected stochastic
subgradient executions with a conditionally controlled random perturbation.
The only extra input beyond centered-noise SSGM is a summable conditional
descent-error budget for the perturbation.
-/
theorem PerturbedProjectedStochasticSubgradientMinimizerSetExecution.outcomeIndexedConvergesToSet
    {Coord : Type*} [Fintype Coord]
    (S : PerturbedProjectedStochasticSubgradientMinimizerSetExecution Coord) :
    @OutcomeIndexedConvergesToSet S.Ω (Coord → ℝ) S.measurableSpace inferInstance
      S.μ S.trajectory S.targetSet := by
  letI := S.measurableSpace
  letI := S.probability
  have hdescent : ∀ target, target ∈ S.targetSet → ∀ n,
      S.μ[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => S.trajectory (n + 1) omega i - target i) | S.filtration n] ≤ᵐ[S.μ]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => S.trajectory n omega i - target i) -
          2 * S.radius (n + 1) *
            (S.objective (S.trajectory n omega) - S.objective target) +
          (3 * S.radius (n + 1) ^ 2 * (S.C ^ 2 + S.noiseBound) +
            S.perturbation_error target n) := by
    intro target htarget n
    have hnoise_dot_zero :
        S.μ[fun omega => FiniteDimensionalNorms.dot (S.noise n omega)
          (fun i => S.trajectory n omega i - target i) | S.filtration n] =ᵐ[S.μ] 0 := by
      apply condExp_finiteDot_eq_zero_of_coordinatewise
      · intro i
        exact (S.trajectory_adapted i n).sub stronglyMeasurable_const
      · intro i
        simpa [mul_comm] using S.target_noise_product_integrable target htarget n i
      · exact S.noise_coordinate_integrable n
      · exact S.noise_mean_zero n
    have hnext_integrable : Integrable
        (fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => S.project (fun j => S.trajectory n omega j - S.radius (n + 1) *
            (S.meanSubgradient n omega j + S.noise n omega j +
              S.perturbation n omega j)) i - target i)) S.μ := by
      apply (S.target_potential_integrable target htarget (n + 1)).congr
      filter_upwards [S.update n] with omega hupdate
      simp [hupdate]
    have hstep : S.μ[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => S.project (fun j => S.trajectory n omega j - S.radius (n + 1) *
          (S.meanSubgradient n omega j + S.noise n omega j +
            S.perturbation n omega j)) i - target i) | S.filtration n] ≤ᵐ[S.μ]
        fun omega =>
          FiniteDimensionalNorms.l2Sq (fun i => S.trajectory n omega i - target i) -
            2 * S.radius (n + 1) *
              (S.objective (S.trajectory n omega) - S.objective target) +
            3 * S.radius (n + 1) ^ 2 *
              (S.C ^ 2 + S.μ[fun omega =>
                FiniteDimensionalNorms.l2Sq (S.noise n omega) | S.filtration n] omega) +
            S.μ[fun omega =>
              2 * S.radius (n + 1) * S.target_distanceBound target *
                  FiniteDimensionalNorms.l2 (S.perturbation n omega) +
                3 * S.radius (n + 1) ^ 2 *
                  FiniteDimensionalNorms.l2Sq (S.perturbation n omega) | S.filtration n] omega := by
      exact conditional_l2Sq_projected_subgradient_noise_perturbation_step_le
        (mu := S.μ) (m := S.filtration n) (X := S.solutionSpace)
        (project := S.project) (cost := S.objective) (previous := S.trajectory n)
        (gradient := S.meanSubgradient n) (noise := S.noise n)
        (perturbation := S.perturbation n) (target := target)
        (radius := S.radius (n + 1)) (C := S.C)
        (distanceBound := S.target_distanceBound target)
        S.project_nonexpansive (S.filtration.le n) (S.targetSet_subset_solutionSpace htarget)
        (S.radius_nonneg n) (fun i => S.trajectory_adapted i n)
        (S.target_objective_gap_adapted target htarget n)
        (S.target_potential_integrable target htarget n)
        (S.target_objective_gap_integrable target htarget n)
        (by
          simpa [FiniteDimensionalNorms.dot, mul_comm] using
            integrable_finset_sum (Finset.univ : Finset Coord)
              (fun i _ => S.target_noise_product_integrable target htarget n i))
        (S.noise_energy_integrable n) (S.perturbation_norm_integrable n)
        (S.perturbation_energy_integrable n) hnoise_dot_zero
        (S.subgradient n) (S.gradient_bound n)
        (S.target_distance_bound target htarget n) hnext_integrable
    have hbounded : S.μ[fun omega => FiniteDimensionalNorms.l2Sq
        (fun i => S.project (fun j => S.trajectory n omega j - S.radius (n + 1) *
          (S.meanSubgradient n omega j + S.noise n omega j +
            S.perturbation n omega j)) i - target i) | S.filtration n] ≤ᵐ[S.μ]
        fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => S.trajectory n omega i - target i) -
          2 * S.radius (n + 1) *
            (S.objective (S.trajectory n omega) - S.objective target) +
          (3 * S.radius (n + 1) ^ 2 * (S.C ^ 2 + S.noiseBound) +
            S.perturbation_error target n) :=
      by
        filter_upwards [hstep, S.noise_energy_bound n,
          S.perturbation_error_bound target htarget n] with omega hstep hnoise hperturbation
        nlinarith [sq_nonneg (S.radius (n + 1))]
    calc
      S.μ[fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => S.trajectory (n + 1) omega i - target i) | S.filtration n] =ᵐ[S.μ]
          S.μ[fun omega => FiniteDimensionalNorms.l2Sq
            (fun i => S.project (fun j => S.trajectory n omega j - S.radius (n + 1) *
              (S.meanSubgradient n omega j + S.noise n omega j +
                S.perturbation n omega j)) i - target i) | S.filtration n] := by
            apply condExp_congr_ae
            filter_upwards [S.update n] with omega hupdate
            simp [hupdate]
      _ ≤ᵐ[S.μ] fun omega => FiniteDimensionalNorms.l2Sq
          (fun i => S.trajectory n omega i - target i) -
          2 * S.radius (n + 1) *
            (S.objective (S.trajectory n omega) - S.objective target) +
          (3 * S.radius (n + 1) ^ 2 * (S.C ^ 2 + S.noiseBound) +
            S.perturbation_error target n) := hbounded
  apply outcomeIndexedConvergesToSet_of_ae_target_potential_limits_and_ae_summable_gaps
  · intro target htarget
    let potential : ℕ → S.Ω → ℝ := fun n omega =>
      FiniteDimensionalNorms.l2Sq (fun i => S.trajectory n omega i - target i)
    let loss : ℕ → S.Ω → ℝ := fun n omega =>
      2 * S.radius (n + 1) * (S.objective (S.trajectory n omega) - S.objective target)
    let error : ℕ → ℝ := fun n =>
      3 * S.radius (n + 1) ^ 2 * (S.C ^ 2 + S.noiseBound) +
        S.perturbation_error target n
    have herror : Summable error := by
      have hsquare : Summable (fun n =>
          3 * (S.C ^ 2 + S.noiseBound) * S.radius (n + 1) ^ 2) :=
        S.radius_sq_summable.mul_left (3 * (S.C ^ 2 + S.noiseBound))
      have hsum := hsquare.add (S.perturbation_error_summable target htarget)
      convert hsum using 1
      ext n
      dsimp [error]
      ring
    have herror_nonneg : ∀ n, 0 ≤ error n := by
      intro n
      dsimp [error]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
          (add_nonneg (sq_nonneg S.C) S.noiseBound_nonneg))
        (S.perturbation_error_nonneg target htarget n)
    have hpotential_adapted : StronglyAdapted S.filtration potential := by
      apply stronglyAdapted_finiteL2Sq
      intro i
      exact (S.trajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
    have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂S.μ, 0 ≤ potential n omega := by
      intro n
      filter_upwards [] with omega
      exact FiniteDimensionalNorms.normL2Sq_nonneg _
    have hloss_adapted : StronglyAdapted S.filtration loss := by
      intro n
      exact (S.target_objective_gap_adapted target htarget n).const_mul
        (2 * S.radius (n + 1))
    have hloss_integrable : ∀ n, Integrable (loss n) S.μ := by
      intro n
      exact (S.target_objective_gap_integrable target htarget n).const_mul
        (2 * S.radius (n + 1))
    have hloss_nonneg : ∀ n, ∀ᵐ omega ∂S.μ, 0 ≤ loss n omega := by
      intro n
      filter_upwards [S.trajectory_mem_solutionSpace] with omega hmem
      dsimp [loss]
      exact mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
        (sub_nonneg.mpr (S.targetSet_minimizes target htarget (hmem n)))
    apply ae_tendsto_potential_of_condExp_descent (error := error)
      hpotential_adapted hloss_adapted
      (S.target_potential_integrable target htarget)
      hloss_integrable hpotential_nonneg hloss_nonneg
    · intro n
      filter_upwards [hdescent target htarget n] with omega hstep
      dsimp [potential, loss, error]
      linarith
    · exact herror
    · exact herror_nonneg
  · exact S.trajectory_mem_solutionSpace
  · exact S.compact_solutionSpace
  · exact S.objective_continuous
  · exact S.targetSet_minimizes S.reference S.reference_mem_targetSet
  · exact S.minimizer_mem_targetSet
  · exact S.radius_nonneg
  · exact S.radius_diverges
  · let potential : ℕ → S.Ω → ℝ := fun n omega =>
      FiniteDimensionalNorms.l2Sq (fun i => S.trajectory n omega i - S.reference i)
    let loss : ℕ → S.Ω → ℝ := fun n omega =>
      2 * S.radius (n + 1) *
        (S.objective (S.trajectory n omega) - S.objective S.reference)
    let error : ℕ → ℝ := fun n =>
      3 * S.radius (n + 1) ^ 2 * (S.C ^ 2 + S.noiseBound) +
        S.perturbation_error S.reference n
    have herror : Summable error := by
      have hsquare : Summable (fun n =>
          3 * (S.C ^ 2 + S.noiseBound) * S.radius (n + 1) ^ 2) :=
        S.radius_sq_summable.mul_left (3 * (S.C ^ 2 + S.noiseBound))
      have hsum := hsquare.add
        (S.perturbation_error_summable S.reference S.reference_mem_targetSet)
      convert hsum using 1
      ext n
      dsimp [error]
      ring
    have herror_nonneg : ∀ n, 0 ≤ error n := by
      intro n
      dsimp [error]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg (S.radius (n + 1))))
          (add_nonneg (sq_nonneg S.C) S.noiseBound_nonneg))
        (S.perturbation_error_nonneg S.reference S.reference_mem_targetSet n)
    have hpotential_adapted : StronglyAdapted S.filtration potential := by
      apply stronglyAdapted_finiteL2Sq
      intro i
      exact (S.trajectory_adapted i).sub (fun _ => stronglyMeasurable_const)
    have hpotential_nonneg : ∀ n, ∀ᵐ omega ∂S.μ, 0 ≤ potential n omega := by
      intro n
      filter_upwards [] with omega
      exact FiniteDimensionalNorms.normL2Sq_nonneg _
    have hloss_adapted : StronglyAdapted S.filtration loss := by
      intro n
      exact (S.target_objective_gap_adapted S.reference S.reference_mem_targetSet n).const_mul
        (2 * S.radius (n + 1))
    have hloss_integrable : ∀ n, Integrable (loss n) S.μ := by
      intro n
      exact (S.target_objective_gap_integrable S.reference S.reference_mem_targetSet n).const_mul
        (2 * S.radius (n + 1))
    have hloss_nonneg : ∀ n, ∀ᵐ omega ∂S.μ, 0 ≤ loss n omega := by
      intro n
      filter_upwards [S.trajectory_mem_solutionSpace] with omega hmem
      dsimp [loss]
      exact mul_nonneg (mul_nonneg (by norm_num) (S.radius_nonneg n))
        (sub_nonneg.mpr (S.targetSet_minimizes S.reference S.reference_mem_targetSet (hmem n)))
    have hstep : ∀ n,
        S.μ[potential (n + 1) | S.filtration n] ≤ᵐ[S.μ]
          fun omega => potential n omega + error n - loss n omega := by
      intro n
      filter_upwards [hdescent S.reference S.reference_mem_targetSet n] with omega hdescent
      dsimp [potential, loss, error]
      linarith
    filter_upwards [ae_summable_loss_of_condExp_descent (error := error)
      hpotential_adapted hloss_adapted
      (S.target_potential_integrable S.reference S.reference_mem_targetSet)
      hloss_integrable hpotential_nonneg hloss_nonneg hstep herror herror_nonneg] with omega hsum
    have hscaled := hsum.mul_left (1 / 2)
    convert hscaled using 1
    ext n
    dsimp [loss]
    ring

end AppliedModelingLib.Optimization
