import AppliedModelingLib.Foundations.Probability.MeasureInequalities
import AppliedModelingLib.Foundations.Probability.IndependentProduct

/-!
# Finite independent indicator tails

An exponential-moment upper tail for a finite family of independent zero-one
observables with heterogeneous means.  This is the common concentration
primitive used by finite elimination algorithms.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory

/--
The upper tail of independent zero-one indicators is controlled by their
common mean upper bound through a finite exponential-moment calculation.
-/
theorem independentIndicatorSum_ge_probability_exponential
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (indicator : Index → Ω → ℝ) (meanBound cutoff t : ℝ)
    (hindependent : iIndepFun indicator law)
    (hmeasurable : ∀ index, Measurable (indicator index))
    (hindicator : ∀ index outcome, indicator index outcome = 0 ∨ indicator index outcome = 1)
    (hmeanBound : ∀ index, law[indicator index] ≤ meanBound)
    (ht : 0 ≤ t) :
    law.real {outcome | cutoff ≤ ∑ index, indicator index outcome} ≤
      Real.exp (-t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
  let total : Ω → ℝ := fun outcome => ∑ index, indicator index outcome
  have hindicatorBound : ∀ index, ∀ᵐ outcome ∂law,
      indicator index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    exact Filter.Eventually.of_forall fun outcome => by
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
  have hintegrableIndicator : ∀ index, Integrable (indicator index) law := by
    intro index
    exact Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable
      (hindicatorBound index)
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
          (∑ index, indicator index outcome) ≤ ∑ _index : Index, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            rcases hindicator index outcome with hzero | hone
            · simp [hzero]
            · simp [hone]
          _ = (Fintype.card Index : ℝ) := by simp
  have hintegrableExpTotal : Integrable (fun outcome => Real.exp (t * total outcome)) law :=
    integrable_exp_mul_of_mem_Icc htotalMeasurable.aemeasurable htotalBound
  have hfactor : ∀ index,
      law[fun outcome => Real.exp (t * indicator index outcome)] =
        1 + (Real.exp t - 1) * law[indicator index] := by
    intro index
    have hpoint : (fun outcome => Real.exp (t * indicator index outcome)) =
        (fun outcome => 1 + (Real.exp t - 1) * indicator index outcome) := by
      funext outcome
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
    rw [hpoint, integral_add (integrable_const _)
      ((hintegrableIndicator index).const_mul _)]
    rw [integral_const_mul]
    simp [integral_const]
  have hmgf : mgf total law t =
      ∏ index, law[fun outcome => Real.exp (t * indicator index outcome)] := by
    unfold mgf
    have hpoint : (fun outcome => Real.exp (t * total outcome)) =
        (fun outcome => ∏ index, Real.exp (t * indicator index outcome)) := by
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
      law[fun outcome => Real.exp (t * indicator index outcome)] ≤
        Real.exp ((Real.exp t - 1) * meanBound) := by
    intro index
    rw [hfactor index]
    have hcoefficient : 0 ≤ Real.exp t - 1 := sub_nonneg.mpr (Real.one_le_exp ht)
    calc
      1 + (Real.exp t - 1) * law[indicator index] ≤
          1 + (Real.exp t - 1) * meanBound := by
            simpa [add_comm] using add_le_add_left
              (mul_le_mul_of_nonneg_left (hmeanBound index) hcoefficient) (1 : ℝ)
      _ ≤ Real.exp ((Real.exp t - 1) * meanBound) := by
        simpa [add_comm] using Real.add_one_le_exp ((Real.exp t - 1) * meanBound)
  have hmgfBound : mgf total law t ≤
      Real.exp ((Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
    rw [hmgf]
    calc
      (∏ index, law[fun outcome => Real.exp (t * indicator index outcome)]) ≤
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
    law.real {outcome | cutoff ≤ ∑ index, indicator index outcome} =
        law.real {outcome | cutoff ≤ total outcome} := by rfl
    _ ≤ Real.exp (-t * cutoff) * mgf total law t := hchernoff
    _ ≤ Real.exp (-t * cutoff) *
        Real.exp ((Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
          gcongr
    _ = Real.exp (-t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp t - 1) * meanBound)) := by
          rw [Real.exp_add]

/--
The lower tail of independent zero-one indicators is controlled by a common
mean lower bound through the same finite exponential-moment calculation. The
negative exponential parameter keeps the direction of the mean comparison
explicit.
-/
theorem independentIndicatorSum_le_probability_exponential
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (indicator : Index → Ω → ℝ) (meanLower cutoff t : ℝ)
    (hindependent : iIndepFun indicator law)
    (hmeasurable : ∀ index, Measurable (indicator index))
    (hindicator : ∀ index outcome, indicator index outcome = 0 ∨ indicator index outcome = 1)
    (hmeanLower : ∀ index, meanLower ≤ law[indicator index])
    (ht : 0 ≤ t) :
    law.real {outcome | (∑ index, indicator index outcome) ≤ cutoff} ≤
      Real.exp (t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
  let total : Ω → ℝ := fun outcome => ∑ index, indicator index outcome
  have hindicatorBound : ∀ index, ∀ᵐ outcome ∂law,
      indicator index outcome ∈ Set.Icc (0 : ℝ) 1 := by
    intro index
    exact Filter.Eventually.of_forall fun outcome => by
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
  have hintegrableIndicator : ∀ index, Integrable (indicator index) law := by
    intro index
    exact Integrable.of_mem_Icc 0 1 (hmeasurable index).aemeasurable
      (hindicatorBound index)
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
          (∑ index, indicator index outcome) ≤ ∑ _index : Index, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro index _
            rcases hindicator index outcome with hzero | hone
            · simp [hzero]
            · simp [hone]
          _ = (Fintype.card Index : ℝ) := by simp
  have hintegrableExpTotal : Integrable (fun outcome => Real.exp ((-t) * total outcome)) law :=
    integrable_exp_mul_of_mem_Icc htotalMeasurable.aemeasurable htotalBound
  have hfactor : ∀ index,
      law[fun outcome => Real.exp ((-t) * indicator index outcome)] =
        1 + (Real.exp (-t) - 1) * law[indicator index] := by
    intro index
    have hpoint : (fun outcome => Real.exp ((-t) * indicator index outcome)) =
        (fun outcome => 1 + (Real.exp (-t) - 1) * indicator index outcome) := by
      funext outcome
      rcases hindicator index outcome with hzero | hone
      · simp [hzero]
      · simp [hone]
    rw [hpoint, integral_add (integrable_const _)
      ((hintegrableIndicator index).const_mul _)]
    rw [integral_const_mul]
    simp [integral_const]
  have hmgf : mgf total law (-t) =
      ∏ index, law[fun outcome => Real.exp ((-t) * indicator index outcome)] := by
    unfold mgf
    have hpoint : (fun outcome => Real.exp ((-t) * total outcome)) =
        (fun outcome => ∏ index, Real.exp ((-t) * indicator index outcome)) := by
      funext outcome
      dsimp [total]
      rw [Finset.mul_sum, Real.exp_sum]
    rw [hpoint]
    let transform : ℝ → ℝ := fun value => Real.exp ((-t) * value)
    have htransformMeasurable : Measurable transform := by
      exact Real.measurable_exp.comp (measurable_const.mul measurable_id)
    have hproduct := hindependent.integral_fun_prod_comp (f := fun _ : Index => transform)
      (fun index => (hmeasurable index).aemeasurable)
      (fun _ : Index => htransformMeasurable.aestronglyMeasurable)
    simpa [transform, Function.comp_def] using hproduct
  have hfactorBound : ∀ index,
      law[fun outcome => Real.exp ((-t) * indicator index outcome)] ≤
        Real.exp ((Real.exp (-t) - 1) * meanLower) := by
    intro index
    rw [hfactor index]
    have hcoefficient : Real.exp (-t) - 1 ≤ 0 := by
      exact sub_nonpos.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
    calc
      1 + (Real.exp (-t) - 1) * law[indicator index] ≤
          1 + (Real.exp (-t) - 1) * meanLower := by
            simpa [add_comm] using add_le_add_left
              (mul_le_mul_of_nonpos_left (hmeanLower index) hcoefficient) (1 : ℝ)
      _ ≤ Real.exp ((Real.exp (-t) - 1) * meanLower) := by
        simpa [add_comm] using Real.add_one_le_exp ((Real.exp (-t) - 1) * meanLower)
  have hmgfBound : mgf total law (-t) ≤
      Real.exp ((Fintype.card Index : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
    rw [hmgf]
    calc
      (∏ index, law[fun outcome => Real.exp ((-t) * indicator index outcome)]) ≤
          ∏ _index : Index, Real.exp ((Real.exp (-t) - 1) * meanLower) := by
            apply Finset.prod_le_prod
            · intro index _
              exact integral_nonneg fun outcome => (Real.exp_pos _).le
            · intro index _
              exact hfactorBound index
      _ = Real.exp ((Fintype.card Index : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
            rw [← Real.exp_sum]
            congr 1
            simp [mul_comm]
  have hchernoff := measure_le_le_exp_mul_mgf (μ := law) (X := total) cutoff
    (t := -t) (neg_nonpos.mpr ht) hintegrableExpTotal
  calc
    law.real {outcome | (∑ index, indicator index outcome) ≤ cutoff} =
        law.real {outcome | total outcome ≤ cutoff} := by rfl
    _ ≤ Real.exp (-(-t) * cutoff) * mgf total law (-t) := hchernoff
    _ ≤ Real.exp (-(-t) * cutoff) *
        Real.exp ((Fintype.card Index : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
          gcongr
    _ = Real.exp (t * cutoff +
        (Fintype.card Index : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
          rw [Real.exp_add]
          congr 1
          ring

/--
PMF form of the independent-indicator exponential tail. It transports a
finite iid PMF product to its canonical product measure and applies the
measure-theoretic independent-indicator bound there.
-/
theorem pmfProb_pmfProduct_indicatorSum_ge_le_exponential
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (indicator : α → ℝ) (meanBound cutoff t : ℝ)
    (hindicator : ∀ outcome, indicator outcome = 0 ∨ indicator outcome = 1)
    (hmeanBound : pmfExp μ indicator ≤ meanBound) (ht : 0 ≤ t) :
    pmfProb (pmfProduct ι α μ) (fun sample => cutoff ≤ ∑ index, indicator (sample index)) ≤
      Real.exp (-t * cutoff +
        (Fintype.card ι : ℝ) * ((Real.exp t - 1) * meanBound)) := by
  rw [pmfProb_eq_toMeasure_real]
  apply independentIndicatorSum_ge_probability_exponential
    ((pmfProduct ι α μ).toMeasure)
    (fun index sample => indicator (sample index)) meanBound cutoff t
  · have hraw : iIndepFun (fun index : ι => fun sample : ι → α => sample index)
        (pmfProduct ι α μ).toMeasure := iIndepFun_pmfProduct_eval μ
    simpa [Function.comp_def] using
      hraw.comp (fun _ value => indicator value)
        (fun _ => measurable_of_finite _)
  · intro index
    exact measurable_of_finite _
  · intro index sample
    exact hindicator (sample index)
  · intro index
    rw [← pmfExp_eq_integral_toMeasure]
    rw [pmfExp_pmfProduct_eval]
    exact hmeanBound
  · exact ht

/--
PMF form of the independent-indicator lower-tail exponential bound. It uses a
mean lower bound, as required by the negative exponential parameter.
-/
theorem pmfProb_pmfProduct_indicatorSum_le_le_exponential
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (indicator : α → ℝ) (meanLower cutoff t : ℝ)
    (hindicator : ∀ outcome, indicator outcome = 0 ∨ indicator outcome = 1)
    (hmeanLower : meanLower ≤ pmfExp μ indicator) (ht : 0 ≤ t) :
    pmfProb (pmfProduct ι α μ) (fun sample => (∑ index, indicator (sample index)) ≤ cutoff) ≤
      Real.exp (t * cutoff +
        (Fintype.card ι : ℝ) * ((Real.exp (-t) - 1) * meanLower)) := by
  rw [pmfProb_eq_toMeasure_real]
  apply independentIndicatorSum_le_probability_exponential
    ((pmfProduct ι α μ).toMeasure)
    (fun index sample => indicator (sample index)) meanLower cutoff t
  · have hraw : iIndepFun (fun index : ι => fun sample : ι → α => sample index)
        (pmfProduct ι α μ).toMeasure := iIndepFun_pmfProduct_eval μ
    simpa [Function.comp_def] using
      hraw.comp (fun _ value => indicator value)
        (fun _ => measurable_of_finite _)
  · intro index
    exact measurable_of_finite _
  · intro index sample
    exact hindicator (sample index)
  · intro index
    rw [← pmfExp_eq_integral_toMeasure]
    rw [pmfExp_pmfProduct_eval]
    exact hmeanLower
  · exact ht

end AppliedModelingLib.Probability
