import FalahatgarEtAl2017MaxingRanking.PruneSize

/-!
# Multiplicative concentration for Prune survivor indicators

The Prune size proof uses a Chernoff calculation for independent zero-one
survival indicators.  Additive Hoeffding is insufficient for the source's
`n' = O(log² n)` first-round regime, so this file records the finite-index
exponential-moment form needed by Lemmas 14--15.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/--
The upper tail of independent zero-one indicators is controlled by their
common mean upper bound through the finite Chernoff exponential moment.
-/
theorem independentIndicatorSum_ge_probability_exponential
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (survival : Index → Ω → ℝ) (meanBound cutoff t : ℝ)
    (hindependent : iIndepFun survival law)
    (hmeasurable : ∀ index, Measurable (survival index))
    (hindicator : ∀ index outcome, survival index outcome = 0 ∨ survival index outcome = 1)
    (hmeanBound : ∀ index, law[survival index] ≤ meanBound)
    (ht : 0 ≤ t) :
    law.real {outcome | cutoff ≤ ∑ index, survival index outcome} ≤
      Real.exp (-t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
  let total : Ω → ℝ := fun outcome => ∑ index, survival index outcome
  have hsurvivalBound : ∀ index, ∀ᵐ outcome ∂law,
      survival index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    exact Filter.Eventually.of_forall fun outcome => by
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
  have hintegrableSurvival : ∀ index, Integrable (survival index) law := by
    intro index
    exact Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable
      (hsurvivalBound index)
  have htotalMeasurable : Measurable total := by
    exact Finset.measurable_sum Finset.univ fun index _ => hmeasurable index
  have htotalBound : ∀ᵐ outcome ∂law,
      total outcome ∈ Set.Icc (0 : ℝ) (Fintype.card Index : ℝ) := by
    exact Filter.Eventually.of_forall fun outcome => by
      constructor
      · dsimp [total]
        exact Finset.sum_nonneg fun index _ => by
          rcases hindicator index outcome with hzero | hone
          · simp [hzero]
          · simp [hone]
      · dsimp [total]
        calc
          (∑ index, survival index outcome) ≤ ∑ _index : Index, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            rcases hindicator index outcome with hzero | hone
            · simp [hzero]
            · simp [hone]
          _ = (Fintype.card Index : ℝ) := by simp
  have hintegrableExpTotal : Integrable (fun outcome => Real.exp (t * total outcome)) law :=
    integrable_exp_mul_of_mem_Icc htotalMeasurable.aemeasurable htotalBound
  have hfactor : ∀ index,
      law[fun outcome => Real.exp (t * survival index outcome)] =
        1 + (Real.exp t - 1) * law[survival index] := by
    intro index
    have hpoint : (fun outcome => Real.exp (t * survival index outcome)) =
        (fun outcome => 1 + (Real.exp t - 1) * survival index outcome) := by
      funext outcome
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
    rw [hpoint, integral_add (integrable_const _)
      ((hintegrableSurvival index).const_mul _)]
    rw [integral_const_mul]
    simp [integral_const]
  have hmgf : mgf total law t =
      ∏ index, law[fun outcome => Real.exp (t * survival index outcome)] := by
    unfold mgf
    have hpoint : (fun outcome => Real.exp (t * total outcome)) =
        (fun outcome => ∏ index, Real.exp (t * survival index outcome)) := by
      funext outcome
      dsimp [total]
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hpoint]
    let transform : ℝ → ℝ := fun value => Real.exp (t * value)
    have htransformMeasurable : Measurable transform := by
      exact Real.measurable_exp.comp (measurable_const.mul measurable_id)
    have hproduct := hindependent.integral_fun_prod_comp (f := fun _ : Index => transform)
      (fun index => (hmeasurable index).aemeasurable)
      (fun _ : Index => htransformMeasurable.aestronglyMeasurable)
    simpa [transform, Function.comp_def] using hproduct
  have hfactorBound : ∀ index,
      law[fun outcome => Real.exp (t * survival index outcome)] ≤
        Real.exp ((Real.exp t - 1) * meanBound) := by
    intro index
    rw [hfactor index]
    have hcoefficient : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht)
    calc
      1 + (Real.exp t - 1) * law[survival index] ≤
          1 + (Real.exp t - 1) * meanBound := by
            simpa [add_comm] using add_le_add_left
              (mul_le_mul_of_nonneg_left (hmeanBound index) hcoefficient) (1 : ℝ)
      _ ≤ Real.exp ((Real.exp t - 1) * meanBound) := by
        simpa [add_comm] using Real.add_one_le_exp ((Real.exp t - 1) * meanBound)
  have hmgfBound : mgf total law t ≤
      Real.exp ((Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
    rw [hmgf]
    calc
      (∏ index, law[fun outcome => Real.exp (t * survival index outcome)]) ≤
          ∏ _index : Index, Real.exp ((Real.exp t - 1) * meanBound) := by
            apply Finset.prod_le_prod
            · intro index _
              exact integral_nonneg fun outcome => (Real.exp_pos _).le
            · intro index _
              exact hfactorBound index
      _ = Real.exp ((Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
            rw [← Real.exp_sum]
            congr 1
            simp [mul_comm]
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := law) (X := total) cutoff ht
    hintegrableExpTotal
  calc
    law.real {outcome | cutoff ≤ ∑ index, survival index outcome} =
        law.real {outcome | cutoff ≤ total outcome} := by rfl
    _ ≤ Real.exp (-t * cutoff) * mgf total law t := hchernoff
    _ ≤ Real.exp (-t * cutoff) *
        Real.exp ((Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
          gcongr
    _ = Real.exp (-t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
          rw [Real.exp_add]

end FalahatgarEtAl2017MaxingRanking
