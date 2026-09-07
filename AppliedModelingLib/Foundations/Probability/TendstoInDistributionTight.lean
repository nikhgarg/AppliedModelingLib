import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Tightness consequences of convergence in distribution

This module records the elementary but useful fact that a weakly convergent
sequence of laws is uniformly tight.  The result is phrased for the random
variables appearing in `TendstoInDistribution`, so a later stochastic-process
argument can obtain compact containment for its initial coordinates without
adding a moment assumption.
-/

namespace AppliedModelingLib.Probability

open Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

/--
Almost-sure convergence of measurable random variables implies convergence in
distribution.  Unlike the metric-space convenience lemma, this test-function
proof only needs the target's open sets to be measurable: dominated
convergence is applied to every bounded continuous real-valued test function.
-/
theorem tendstoInDistribution_of_ae_tendsto
    {E Ω : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → E} {Z : Ω → E}
    (hX : ∀ n, AEMeasurable (X n) μ) (hZ : AEMeasurable Z μ)
    (hlimit : ∀ᵐ omega ∂μ,
      Tendsto (fun n : ℕ => X n omega) atTop (𝓝 (Z omega))) :
    TendstoInDistribution X atTop Z (fun _ => μ) μ := by
  refine ⟨hX, hZ, ?_⟩
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap : ∀ n,
      ∫ value, test value ∂Measure.map (X n) μ =
        ∫ omega, test (X n omega) ∂μ := by
    intro n
    exact integral_map (hX n) test.continuous.measurable.aestronglyMeasurable
  have hmapLimit :
      ∫ value, test value ∂Measure.map Z μ =
        ∫ omega, test (Z omega) ∂μ :=
    integral_map hZ test.continuous.measurable.aestronglyMeasurable
  change Tendsto (fun n => ∫ value, test value ∂Measure.map (X n) μ) atTop
    (𝓝 (∫ value, test value ∂Measure.map Z μ))
  rw [show (fun n => ∫ value, test value ∂Measure.map (X n) μ) =
      (fun n => ∫ omega, test (X n omega) ∂μ) by
        funext n
        exact hmap n,
    hmapLimit]
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : Ω => ‖test‖) ?_ (integrable_const _) ?_ ?_
  · intro n
    exact (test.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  · intro n
    exact Filter.Eventually.of_forall fun omega => test.norm_coe_le_norm (X n omega)
  · filter_upwards [hlimit] with omega homega
    exact test.continuous.continuousAt.tendsto.comp homega

/-- The probability laws occurring in a convergent-in-distribution sequence
form a tight family. -/
theorem isTightMeasureSet_laws_of_tendstoInDistribution
    {E Ω' : Type*} {Ω : ℕ → Type*}
    {m : ∀ n, MeasurableSpace (Ω n)} {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {X : (n : ℕ) → Ω n → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z μ μ') :
    IsTightMeasureSet
      {law : Measure E | ∃ n : ℕ, (μ n).map (X n) = law} := by
  let laws : ℕ → ProbabilityMeasure E := fun n =>
    ⟨(μ n).map (X n),
      Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let limitLaw : ProbabilityMeasure E :=
    ⟨μ'.map Z, Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hlaws : Tendsto laws atTop (𝓝 limitLaw) := by
    exact h.tendsto
  have hcompact : IsCompact (insert limitLaw (Set.range laws)) :=
    hlaws.isCompact_insert_range
  have hclosure : IsCompact (closure (Set.range laws)) := by
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_minimal
    · exact Set.subset_insert _ _
    · exact hcompact.isClosed
  have htight : IsTightMeasureSet
      {law : Measure E | ∃ probabilityLaw : ProbabilityMeasure E,
        probabilityLaw ∈ Set.range laws ∧ (probabilityLaw : Measure E) = law} := by
    simpa only [Set.setOf_exists] using
      (isTightMeasureSet_of_isCompact_closure (S := Set.range laws) hclosure)
  simpa [laws] using htight

/-- Convergence in distribution in a proper normed state space gives a
uniform tail bound for the laws of the prelimit random variables. -/
theorem exists_eventually_map_norm_gt_lt_of_tendstoInDistribution
    {E Ω' : Type*} {Ω : ℕ → Type*}
    {m : ∀ n, MeasurableSpace (Ω n)} {μ : ∀ n, Measure (Ω n)}
    [∀ n, IsProbabilityMeasure (μ n)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [NormedAddCommGroup E] [ProperSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    {X : (n : ℕ) → Ω n → E} {Z : Ω' → E}
    (h : TendstoInDistribution X atTop Z μ μ')
    {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ radius : ℝ, ∀ᶠ n : ℕ in atTop,
      (μ n).map (X n) {x | radius < ‖x‖} < epsilon := by
  have htight := isTightMeasureSet_laws_of_tendstoInDistribution h
  have htail := tendsto_measure_norm_gt_of_isTightMeasureSet htight
  rw [ENNReal.tendsto_atTop_zero] at htail
  obtain ⟨delta, hdelta, hdelta_epsilon⟩ := exists_between hepsilon
  obtain ⟨radius, hradius⟩ := htail delta hdelta
  refine ⟨radius, ?_⟩
  filter_upwards with n
  have hsup :
      ⨆ law : Measure E,
        ⨆ _ : law ∈ {law : Measure E | ∃ m : ℕ, (μ m).map (X m) = law},
          law {x | radius < ‖x‖} ≤ delta :=
    hradius radius le_rfl
  apply lt_of_le_of_lt ?_ (lt_of_le_of_lt hsup hdelta_epsilon)
  refine le_iSup_of_le ((μ n).map (X n)) ?_
  refine le_iSup_of_le ?_ (le_refl _)
  exact ⟨n, rfl⟩

end AppliedModelingLib.Probability
