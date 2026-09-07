import AppliedModelingLib.Foundations.Probability.Exponential

/-!
# Measure-level exponential memorylessness

This module packages the deterministic exponential residual law as a measure
identity.  After restricting a positive-rate exponential variable to survival
past `elapsed`, subtracting `elapsed` produces the original exponential
measure, multiplied by the survival mass.  Unlike a tail-probability-only
formula, the result applies to every measurable residual event and can be
used in finite-block or renewal-path constructions.
-/

namespace AppliedModelingLib.Probability.Exponential

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem expMeasure_residual_tail
    {rate elapsed future : ℝ} (hrate : 0 < rate)
    (helapsed : 0 ≤ elapsed) (hfuture : 0 ≤ future) :
    ProbabilityTheory.expMeasure rate
        {x : ℝ | elapsed < x ∧ future < x - elapsed} =
      ProbabilityTheory.expMeasure rate (Set.Ioi elapsed) *
        ProbabilityTheory.expMeasure rate (Set.Ioi future) := by
  let M : Model := ⟨rate, hrate⟩
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure rate) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simpa only [ENNReal.toReal_mul, M, Model.measure] using
    M.measure_residual_tail_toReal helapsed hfuture

private theorem expMeasure_Ioi_eq_one_of_neg
    {rate future : ℝ} (hrate : 0 < rate) (hfuture : future < 0) :
    ProbabilityTheory.expMeasure rate (Set.Ioi future) = 1 := by
  let M : Model := ⟨rate, hrate⟩
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hnull : μ (Set.Iic future) = 0 := by
    apply measure_mono_null ?_ M.measure_Iio_zero
    intro x hx
    exact lt_of_le_of_lt hx hfuture
  change μ (Set.Ioi future) = 1
  rw [show Set.Ioi future = (Set.Iic future)ᶜ by ext x; simp,
    measure_compl measurableSet_Iic (measure_ne_top _ _), hnull, measure_univ]
  norm_num

/--
Conditioning a positive-rate exponential variable on survival past a
deterministic nonnegative elapsed time and subtracting that elapsed time gives
the original exponential measure, scaled by the survival mass.
-/
theorem expMeasure_restrict_Ioi_map_sub_eq_smul
    {rate elapsed : ℝ} (hrate : 0 < rate) (helapsed : 0 ≤ elapsed) :
    ((ProbabilityTheory.expMeasure rate).restrict (Set.Ioi elapsed)).map
        (fun x : ℝ => x - elapsed) =
      (ProbabilityTheory.expMeasure rate (Set.Ioi elapsed)) •
        ProbabilityTheory.expMeasure rate := by
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let c : ℝ≥0∞ := μ (Set.Ioi elapsed)
  letI : IsProbabilityMeasure μ := by
    simpa only [μ] using ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  apply ext_of_generate_finite (Set.range Set.Ioi)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
    isPiSystem_Ioi
  · rintro _ ⟨future, rfl⟩
    change (μ.restrict (Set.Ioi elapsed)).map (fun x : ℝ => x - elapsed)
        (Set.Ioi future) = c * μ (Set.Ioi future)
    have hsub : Measurable (fun x : ℝ => x - elapsed) := by fun_prop
    rw [Measure.map_apply hsub measurableSet_Ioi,
      Measure.restrict_apply (hsub measurableSet_Ioi)]
    by_cases hfuture : 0 ≤ future
    · have hset :
        (fun x : ℝ => x - elapsed) ⁻¹' Set.Ioi future ∩ Set.Ioi elapsed =
          {x : ℝ | elapsed < x ∧ future < x - elapsed} := by
          ext x
          constructor
          · rintro ⟨hx, he⟩
            exact ⟨he, hx⟩
          · rintro ⟨he, hx⟩
            exact ⟨hx, he⟩
      rw [hset]
      simpa only [μ, c] using
        expMeasure_residual_tail hrate helapsed hfuture
    · have hfuture' : future < 0 := lt_of_not_ge hfuture
      have hset :
          (fun x : ℝ => x - elapsed) ⁻¹' Set.Ioi future ∩ Set.Ioi elapsed =
            Set.Ioi elapsed := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_preimage]
        constructor
        · exact fun hx => hx.2
        · intro hx
          constructor
          · linarith
          · exact hx
      rw [hset, expMeasure_Ioi_eq_one_of_neg hrate hfuture']
      simp [c]
  · change (μ.restrict (Set.Ioi elapsed)).map (fun x : ℝ => x - elapsed) Set.univ =
      (c • μ) Set.univ
    have hsub : Measurable (fun x : ℝ => x - elapsed) := by fun_prop
    rw [Measure.map_apply hsub MeasurableSet.univ,
      Measure.restrict_apply (hsub MeasurableSet.univ)]
    simp [c]

end
end AppliedModelingLib.Probability.Exponential
