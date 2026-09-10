import AppliedModelingLib.Foundations.Probability.Exponential
import AppliedModelingLib.Foundations.Probability.IidStatePrefixStopping

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

/-- If an exponential clock is independent of an arbitrary elapsed-time law,
then its residual after restricting to survival past that elapsed time has no
atoms.  The statement needs no regularity or atomlessness of `elapsedLaw`:
every possible residual value pins the exponential coordinate to one point.
-/
theorem map_snd_sub_fst_restrict_prod_apply_singleton_eq_zero
    (elapsedLaw : Measure ℝ) [SFinite elapsedLaw] {rate : ℝ}
    (hrate : 0 < rate) (residual : ℝ) :
    Measure.map (fun value : ℝ × ℝ => value.2 - value.1)
      ((elapsedLaw.prod (ProbabilityTheory.expMeasure rate)).restrict
        {value : ℝ × ℝ | value.1 < value.2}) ({residual} : Set ℝ) = 0 := by
  let E : Measure ℝ := ProbabilityTheory.expMeasure rate
  letI : IsProbabilityMeasure E := by
    simpa only [E] using ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  letI : NoAtoms E := by
    dsimp [E]
    unfold ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
    infer_instance
  let residualMap : ℝ × ℝ → ℝ := fun value => value.2 - value.1
  let survivorSet : Set (ℝ × ℝ) := {value | value.1 < value.2}
  have hresidualMap : Measurable residualMap := by
    exact measurable_snd.sub measurable_fst
  have htarget : MeasurableSet (residualMap ⁻¹' ({residual} : Set ℝ)) :=
    (measurableSet_singleton residual).preimage hresidualMap
  have hgraph :
      (elapsedLaw.prod E) {value : ℝ × ℝ | value.2 = value.1 + residual} = 0 := by
    exact IIDStream.measure_prod_graph_eq_zero elapsedLaw E
      (fun elapsed : ℝ => elapsed + residual) (measurable_id.add measurable_const)
  change Measure.map residualMap ((elapsedLaw.prod E).restrict survivorSet)
    ({residual} : Set ℝ) = 0
  rw [Measure.map_apply hresidualMap (measurableSet_singleton residual),
    Measure.restrict_apply htarget]
  apply measure_mono_null ?_ hgraph
  intro value hvalue
  rcases hvalue with ⟨hvalue, _⟩
  change value.2 = value.1 + residual
  change value.2 - value.1 = residual at hvalue
  calc
    value.2 = (value.2 - value.1) + value.1 := (sub_add_cancel value.2 value.1).symm
    _ = residual + value.1 := by rw [hvalue]
    _ = value.1 + residual := add_comm _ _

/-- The surviving residual of an exponential clock after an independent
arbitrary elapsed time is atomless. -/
theorem noAtoms_map_snd_sub_fst_restrict_prod
    (elapsedLaw : Measure ℝ) [SFinite elapsedLaw] {rate : ℝ}
    (hrate : 0 < rate) :
    NoAtoms (Measure.map (fun value : ℝ × ℝ => value.2 - value.1)
      ((elapsedLaw.prod (ProbabilityTheory.expMeasure rate)).restrict
        {value : ℝ × ℝ | value.1 < value.2})) := by
  refine ⟨?_⟩
  intro residual
  exact map_snd_sub_fst_restrict_prod_apply_singleton_eq_zero
    elapsedLaw hrate residual

end
end AppliedModelingLib.Probability.Exponential
