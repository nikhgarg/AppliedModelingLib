import AppliedModelingLib.Foundations.Probability.IndependentIndicators

/-!
# Variance-sensitive exponential tails for bounded independent variables

This module supplies the finite exponential-moment layer behind Bernstein-type
concentration arguments. It starts from Mathlib's certified local bound on
the exponential remainder and keeps every range, variance, and dual-parameter
condition explicit.
-/

namespace AppliedModelingLib.Probability

open MeasureTheory ProbabilityTheory

/-- A unit-range exponential remainder bound in a form convenient for MGFs. -/
theorem exp_le_one_add_self_add_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hrem : |Real.exp x - 1 - x| ≤ x ^ 2 :=
    Real.abs_exp_sub_one_sub_id_le hx
  have hraw : Real.exp x - 1 - x ≤ x ^ 2 := le_trans (le_abs_self _) hrem
  linarith

/--
A centered bounded variable with second moment at most `varianceBound` has a
quadratic MGF bound whenever `t * bound ≤ 1`.
-/
theorem mgf_le_exp_variance_of_centered_abs_le
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (X : Ω → ℝ) (varianceBound bound t : ℝ)
    (hmeasurable : Measurable X) (hmean : law[X] = 0)
    (hvariance : law[fun outcome => X outcome ^ 2] ≤ varianceBound)
    (hbound : ∀ outcome, |X outcome| ≤ bound)
    (ht : 0 ≤ t) (htbound : t * bound ≤ 1) :
    mgf X law t ≤ Real.exp (t ^ 2 * varianceBound) := by
  have hbound_nonneg : 0 ≤ bound := by
    have hzero := hbound (Classical.choice (MeasureTheory.nonempty_of_isProbabilityMeasure law))
    exact le_trans (abs_nonneg _) hzero
  have hX_Icc : ∀ᵐ outcome ∂law, X outcome ∈ Set.Icc (-bound) bound := by
    exact Filter.Eventually.of_forall fun outcome => by
      have h := hbound outcome
      constructor <;> linarith [le_abs_self (X outcome), neg_le_abs (X outcome)]
  have hX_integrable : Integrable X law :=
    Integrable.of_mem_Icc (-bound) bound hmeasurable.aemeasurable hX_Icc
  have hsq_Icc : ∀ᵐ outcome ∂law, X outcome ^ 2 ∈ Set.Icc (0 : ℝ) (bound ^ 2) := by
    exact Filter.Eventually.of_forall fun outcome => by
      constructor
      · positivity
      · exact sq_le_sq.mpr (by simpa [abs_of_nonneg hbound_nonneg] using hbound outcome)
  have hsq_measurable : Measurable (fun outcome => X outcome ^ 2) := by
    simpa [pow_two] using hmeasurable.mul hmeasurable
  have hsq_integrable : Integrable (fun outcome => X outcome ^ 2) law :=
    Integrable.of_mem_Icc 0 (bound ^ 2) hsq_measurable.aemeasurable hsq_Icc
  have hexp_integrable : Integrable (fun outcome => Real.exp (t * X outcome)) law :=
    integrable_exp_mul_of_mem_Icc hmeasurable.aemeasurable hX_Icc
  have hlinear_integrable : Integrable (fun outcome => 1 + t * X outcome) law :=
    (integrable_const 1).add (hX_integrable.const_mul t)
  have hquad_integrable : Integrable
      (fun outcome => 1 + t * X outcome + t ^ 2 * X outcome ^ 2) law :=
    hlinear_integrable.add (hsq_integrable.const_mul (t ^ 2))
  have hpoint : ∀ outcome,
      Real.exp (t * X outcome) ≤ 1 + t * X outcome + t ^ 2 * X outcome ^ 2 := by
    intro outcome
    have habs : |t * X outcome| ≤ 1 := by
      calc
        |t * X outcome| = t * |X outcome| := by
          rw [abs_mul, abs_of_nonneg ht]
        _ ≤ t * bound := mul_le_mul_of_nonneg_left (hbound outcome) ht
        _ ≤ 1 := htbound
    calc
      Real.exp (t * X outcome) ≤ 1 + t * X outcome + (t * X outcome) ^ 2 :=
        exp_le_one_add_self_add_sq_of_abs_le_one habs
      _ = 1 + t * X outcome + t ^ 2 * X outcome ^ 2 := by ring
  calc
    mgf X law t = law[fun outcome => Real.exp (t * X outcome)] := rfl
    _ ≤ law[fun outcome => 1 + t * X outcome + t ^ 2 * X outcome ^ 2] := by
      apply integral_mono_ae hexp_integrable hquad_integrable
      exact Filter.Eventually.of_forall hpoint
    _ = 1 + t * law[X] + t ^ 2 * law[fun outcome => X outcome ^ 2] := by
      rw [integral_add hlinear_integrable (hsq_integrable.const_mul (t ^ 2)),
        integral_add (integrable_const 1) (hX_integrable.const_mul t),
        integral_const_mul, integral_const_mul]
      simp
    _ = 1 + t ^ 2 * law[fun outcome => X outcome ^ 2] := by rw [hmean]; ring
    _ ≤ 1 + t ^ 2 * varianceBound := by
      gcongr
    _ ≤ Real.exp (t ^ 2 * varianceBound) := by
      simpa [add_comm] using Real.add_one_le_exp (t ^ 2 * varianceBound)

/--
Finite exponential upper tail for independent centered variables with a common
second-moment bound and common absolute range bound.
-/
theorem independentCenteredBoundedSum_ge_probability_exponential
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (X : Index → Ω → ℝ) (varianceBound bound cutoff t : ℝ)
    (hindependent : iIndepFun X law)
    (hmeasurable : ∀ index, Measurable (X index))
    (hmean : ∀ index, law[X index] = 0)
    (hvariance : ∀ index, law[fun outcome => X index outcome ^ 2] ≤ varianceBound)
    (hbound : ∀ index outcome, |X index outcome| ≤ bound)
    (ht : 0 ≤ t) (htbound : t * bound ≤ 1) :
    law.real {outcome | cutoff ≤ ∑ index, X index outcome} ≤
      Real.exp (-t * cutoff + (Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := by
  let total : Ω → ℝ := fun outcome => ∑ index, X index outcome
  have htotalMeasurable : Measurable total := by
    exact Finset.measurable_sum Finset.univ fun index _ => hmeasurable index
  have htotalBound : ∀ᵐ outcome ∂law,
      total outcome ∈ Set.Icc (-(Fintype.card Index : ℝ) * bound)
        ((Fintype.card Index : ℝ) * bound) := by
    exact Filter.Eventually.of_forall fun outcome => by
      constructor
      · dsimp [total]
        calc
          -(Fintype.card Index : ℝ) * bound = ∑ _index : Index, -bound := by simp
          _ ≤ ∑ index, X index outcome := by
            apply Finset.sum_le_sum
            intro index _
            linarith [neg_le_abs (X index outcome), hbound index outcome]
      · dsimp [total]
        calc
          (∑ index, X index outcome) ≤ ∑ _index : Index, bound := by
            apply Finset.sum_le_sum
            intro index _
            exact (le_abs_self (X index outcome)).trans (hbound index outcome)
          _ = (Fintype.card Index : ℝ) * bound := by simp
  have hintegrableExpTotal : Integrable (fun outcome => Real.exp (t * total outcome)) law :=
    integrable_exp_mul_of_mem_Icc htotalMeasurable.aemeasurable htotalBound
  have hmgf : mgf total law t =
      ∏ index, law[fun outcome => Real.exp (t * X index outcome)] := by
    unfold mgf
    have hpoint : (fun outcome => Real.exp (t * total outcome)) =
        (fun outcome => ∏ index, Real.exp (t * X index outcome)) := by
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
      law[fun outcome => Real.exp (t * X index outcome)] ≤
        Real.exp (t ^ 2 * varianceBound) := by
    intro index
    exact mgf_le_exp_variance_of_centered_abs_le law (X index) varianceBound bound t
      (hmeasurable index) (hmean index) (hvariance index) (hbound index) ht htbound
  have hmgfBound : mgf total law t ≤
      Real.exp ((Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := by
    rw [hmgf]
    calc
      (∏ index, law[fun outcome => Real.exp (t * X index outcome)]) ≤
          ∏ _index : Index, Real.exp (t ^ 2 * varianceBound) := by
            apply Finset.prod_le_prod
            · intro index _
              exact integral_nonneg fun outcome => (Real.exp_pos _).le
            · intro index _
              exact hfactorBound index
      _ = Real.exp ((Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := by
            rw [← Real.exp_sum]
            congr 1
            simp [mul_comm]
  have hchernoff := measure_ge_le_exp_mul_mgf (μ := law) (X := total) cutoff ht
    hintegrableExpTotal
  calc
    law.real {outcome | cutoff ≤ ∑ index, X index outcome} =
        law.real {outcome | cutoff ≤ total outcome} := by rfl
    _ ≤ Real.exp (-t * cutoff) * mgf total law t := hchernoff
    _ ≤ Real.exp (-t * cutoff) *
        Real.exp ((Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := by
          gcongr
    _ = Real.exp (-t * cutoff +
        (Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := by
          rw [Real.exp_add]

/--
Bernstein-form simplification of the local-MGF tail. Its denominator exposes
the interpolation between the variance scale and the absolute range scale.
-/
theorem independentCenteredBoundedSum_ge_probability_bernstein
    {Ω Index : Type*} [MeasurableSpace Ω] [Fintype Index]
    (law : Measure Ω) [IsProbabilityMeasure law]
    (X : Index → Ω → ℝ) (varianceBound bound cutoff : ℝ)
    (hindependent : iIndepFun X law)
    (hmeasurable : ∀ index, Measurable (X index))
    (hmean : ∀ index, law[X index] = 0)
    (hvariance : ∀ index, law[fun outcome => X index outcome ^ 2] ≤ varianceBound)
    (hbound : ∀ index outcome, |X index outcome| ≤ bound)
    (hvariance_nonneg : 0 ≤ varianceBound) (hbound_nonneg : 0 ≤ bound)
    (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (Fintype.card Index : ℝ) * varianceBound + bound * cutoff) :
    law.real {outcome | cutoff ≤ ∑ index, X index outcome} ≤
      Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card Index : ℝ) * varianceBound + bound * cutoff))) := by
  let den : ℝ := (Fintype.card Index : ℝ) * varianceBound + bound * cutoff
  let t : ℝ := cutoff / (2 * den)
  have hcard_nonneg : 0 ≤ (Fintype.card Index : ℝ) := by positivity
  have ht_nonneg : 0 ≤ t := by
    exact div_nonneg hcutoff_nonneg (by positivity)
  have hbd_nonneg : 0 ≤ bound * cutoff :=
    mul_nonneg hbound_nonneg hcutoff_nonneg
  have hvar_nonneg : 0 ≤ (Fintype.card Index : ℝ) * varianceBound :=
    mul_nonneg hcard_nonneg hvariance_nonneg
  have htbound : t * bound ≤ 1 := by
    have hnum : cutoff * bound ≤ 2 * den := by
      dsimp [den]
      nlinarith
    rw [show t * bound = (cutoff * bound) / (2 * den) by
      dsimp [t]
      ring]
    rw [div_le_one (by positivity)]
    exact hnum
  have htail := independentCenteredBoundedSum_ge_probability_exponential
    law X varianceBound bound cutoff t hindependent hmeasurable hmean hvariance hbound
    ht_nonneg htbound
  calc
    law.real {outcome | cutoff ≤ ∑ index, X index outcome} ≤
      Real.exp (-t * cutoff + (Fintype.card Index : ℝ) * (t ^ 2 * varianceBound)) := htail
    _ ≤ Real.exp (-cutoff ^ 2 / (4 * den)) := by
      apply Real.exp_le_exp.mpr
      have hrest : 0 ≤ cutoff ^ 2 * (bound * cutoff) :=
        mul_nonneg (sq_nonneg cutoff) hbd_nonneg
      have hden_pos' : 0 < (Fintype.card Index : ℝ) * varianceBound + cutoff * bound := by
        simpa [mul_comm] using hden_pos
      dsimp [t, den]
      field_simp [hden_pos'.ne']
      nlinarith
    _ = Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card Index : ℝ) * varianceBound + bound * cutoff))) := by
      rfl

/--
PMF-product form of the variance-sensitive Bernstein tail. It transports the
finite iid PMF product to its canonical product measure.
-/
theorem pmfProb_pmfProduct_centeredBoundedSum_ge_le_bernstein
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (X : α → ℝ) (varianceBound bound cutoff : ℝ)
    (hmean : pmfExp μ X = 0)
    (hvariance : pmfExp μ (fun outcome => X outcome ^ 2) ≤ varianceBound)
    (hbound : ∀ outcome, |X outcome| ≤ bound)
    (hvariance_nonneg : 0 ≤ varianceBound) (hbound_nonneg : 0 ≤ bound)
    (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (Fintype.card ι : ℝ) * varianceBound + bound * cutoff) :
    pmfProb (pmfProduct ι α μ) (fun sample => cutoff ≤ ∑ index, X (sample index)) ≤
      Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ι : ℝ) * varianceBound + bound * cutoff))) := by
  rw [pmfProb_eq_toMeasure_real]
  apply independentCenteredBoundedSum_ge_probability_bernstein
    ((pmfProduct ι α μ).toMeasure)
    (fun index sample => X (sample index)) varianceBound bound cutoff
  · have hraw : iIndepFun (fun index : ι => fun sample : ι → α => sample index)
        (pmfProduct ι α μ).toMeasure := iIndepFun_pmfProduct_eval μ
    simpa [Function.comp_def] using
      hraw.comp (fun _ value => X value) (fun _ => measurable_of_finite _)
  · intro index
    exact measurable_of_finite _
  · intro index
    rw [← pmfExp_eq_integral_toMeasure]
    rw [pmfExp_pmfProduct_eval μ index X]
    exact hmean
  · intro index
    rw [← pmfExp_eq_integral_toMeasure]
    change pmfExp (pmfProduct ι α μ)
      (fun sample => (fun outcome => X outcome ^ 2) (sample index)) ≤ varianceBound
    rw [pmfExp_pmfProduct_eval μ index (fun outcome => X outcome ^ 2)]
    exact hvariance
  · intro index sample
    exact hbound (sample index)
  · exact hvariance_nonneg
  · exact hbound_nonneg
  · exact hcutoff_nonneg
  · exact hden_pos

/--
Two-sided Bernstein bound for a finite iid sum.  The statement is obtained by
applying the one-sided result to the statistic and its negation, followed by a
two-event union bound; no symmetry of the underlying law is assumed.
-/
theorem pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (X : α → ℝ) (varianceBound bound cutoff : ℝ)
    (hmean : pmfExp μ X = 0)
    (hvariance : pmfExp μ (fun outcome => X outcome ^ 2) ≤ varianceBound)
    (hbound : ∀ outcome, |X outcome| ≤ bound)
    (hvariance_nonneg : 0 ≤ varianceBound) (hbound_nonneg : 0 ≤ bound)
    (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (Fintype.card ι : ℝ) * varianceBound + bound * cutoff) :
    pmfProb (pmfProduct ι α μ)
      (fun sample => cutoff ≤ |∑ index, X (sample index)|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ι : ℝ) * varianceBound + bound * cutoff))) := by
  let law := pmfProduct ι α μ
  let exponent : ℝ := Real.exp (-cutoff ^ 2 /
    (4 * ((Fintype.card ι : ℝ) * varianceBound + bound * cutoff)))
  have hupper :
      pmfProb law (fun sample => cutoff ≤ ∑ index, X (sample index)) ≤ exponent := by
    simpa [law, exponent] using
      (pmfProb_pmfProduct_centeredBoundedSum_ge_le_bernstein
        (ι := ι) μ X varianceBound bound cutoff hmean hvariance hbound
        hvariance_nonneg hbound_nonneg hcutoff_nonneg hden_pos)
  have hmean_neg : pmfExp μ (fun outcome => -X outcome) = 0 := by
    simpa only [pmfExp_neg, neg_zero] using congrArg Neg.neg hmean
  have hvariance_neg :
      pmfExp μ (fun outcome => (-X outcome) ^ 2) ≤ varianceBound := by
    simpa using hvariance
  have hbound_neg : ∀ outcome, |(-X outcome)| ≤ bound := by
    intro outcome
    simpa using hbound outcome
  have hlower :
      pmfProb law (fun sample => cutoff ≤ ∑ index, -X (sample index)) ≤ exponent := by
    simpa [law, exponent] using
      (pmfProb_pmfProduct_centeredBoundedSum_ge_le_bernstein
        (ι := ι) μ (fun outcome => -X outcome) varianceBound bound cutoff
        hmean_neg hvariance_neg hbound_neg hvariance_nonneg hbound_nonneg
        hcutoff_nonneg hden_pos)
  let tail : Bool → (ι → α) → Prop := fun sign sample =>
    if sign then cutoff ≤ ∑ index, X (sample index)
    else cutoff ≤ ∑ index, -X (sample index)
  have htail : ∀ sign, pmfProb law (tail sign) ≤ exponent := by
    intro sign
    cases sign with
    | false => simpa [tail] using hlower
    | true => simpa [tail] using hupper
  have hunion := pmfProb_exists_le_card_mul law tail exponent htail
  have hevent : ∀ sample : ι → α,
      cutoff ≤ |∑ index, X (sample index)| ↔ ∃ sign : Bool, tail sign sample := by
    intro sample
    let total : ℝ := ∑ index, X (sample index)
    have hnegSum : (∑ index, -X (sample index)) = -total := by
      dsimp [total]
      rw [Finset.sum_neg_distrib]
    constructor
    · intro h
      by_cases htotal : 0 ≤ total
      · refine ⟨true, ?_⟩
        simpa [tail, total, abs_of_nonneg htotal] using h
      · refine ⟨false, ?_⟩
        have htotal_nonpos : total ≤ 0 := le_of_not_ge htotal
        change cutoff ≤ ∑ index, -X (sample index)
        rw [hnegSum, ← abs_of_nonpos htotal_nonpos]
        exact h
    · rintro ⟨sign, h⟩
      cases sign with
      | false =>
          have h' : cutoff ≤ -total := by
            simpa [tail, hnegSum] using h
          exact h'.trans (neg_le_abs total)
      | true =>
          have h' : cutoff ≤ total := by
            simpa [tail, total] using h
          exact h'.trans (le_abs_self total)
  calc
    pmfProb law (fun sample => cutoff ≤ |∑ index, X (sample index)|) =
        pmfProb law (fun sample => ∃ sign : Bool, tail sign sample) := by
          apply pmfProb_congr
          exact hevent
    _ ≤ (Fintype.card Bool : ℝ) * exponent := hunion
    _ = 2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ι : ℝ) * varianceBound + bound * cutoff))) := by
          simp [exponent]

/--
The elementary Bernstein-quantile algebra used to turn an exponential tail
into a confidence-level statement.  The deliberately conservative constants
keep the proof valid for every nonnegative variance and range scale.
-/
theorem bernstein_quantile_sq_ge
    {totalVariance bound logLevel : ℝ}
    (htotalVariance_nonneg : 0 ≤ totalVariance) (hbound_nonneg : 0 ≤ bound)
    (hlogLevel_nonneg : 0 ≤ logLevel) :
    4 * logLevel *
        (totalVariance + bound *
          (Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel)) ≤
      (Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel) ^ 2 := by
  let root : ℝ := Real.sqrt (8 * totalVariance * logLevel)
  have hroot_nonneg : 0 ≤ root := Real.sqrt_nonneg _
  have hroot_sq : root ^ 2 = 8 * totalVariance * logLevel := by
    dsimp [root]
    exact Real.sq_sqrt (by positivity)
  have hvariance_log_nonneg : 0 ≤ totalVariance * logLevel :=
    mul_nonneg htotalVariance_nonneg hlogLevel_nonneg
  have hcross_nonneg : 0 ≤ bound * logLevel * root := by positivity
  have hquadratic_nonneg : 0 ≤ bound ^ 2 * logLevel ^ 2 := by positivity
  dsimp [root] at hroot_nonneg hroot_sq hcross_nonneg ⊢
  nlinarith

/-- The Bernstein exponential evaluated at the library's explicit quantile. -/
theorem bernstein_two_sided_exponential_at_quantile_le
    {totalVariance bound logLevel : ℝ}
    (htotalVariance_nonneg : 0 ≤ totalVariance) (hbound_nonneg : 0 ≤ bound)
    (hlogLevel_nonneg : 0 ≤ logLevel)
    (hden_pos : 0 < totalVariance + bound *
      (Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel)) :
    2 * Real.exp
        (-((Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel) ^ 2) /
          (4 * (totalVariance + bound *
            (Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel)))) ≤
      2 * Real.exp (-logLevel) := by
  let cutoff : ℝ := Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel
  have hsquare : 4 * logLevel * (totalVariance + bound * cutoff) ≤ cutoff ^ 2 := by
    dsimp [cutoff]
    exact bernstein_quantile_sq_ge htotalVariance_nonneg hbound_nonneg hlogLevel_nonneg
  have hratio : logLevel ≤ cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) (by simpa [cutoff] using hden_pos))).2
    nlinarith
  have hexponent : -cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) ≤ -logLevel := by
    rw [show -cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) =
      -(cutoff ^ 2 / (4 * (totalVariance + bound * cutoff))) by ring]
    exact neg_le_neg hratio
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

/--
Confidence-level form of the two-sided finite-product Bernstein bound.  The
threshold is a concrete square-root-plus-linear quantile, so callers can use
`logLevel = log (2 / δ)` without redoing the exponential inversion algebra.
-/
theorem pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein_quantile
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (X : α → ℝ) (varianceBound bound logLevel : ℝ)
    (hmean : pmfExp μ X = 0)
    (hvariance : pmfExp μ (fun outcome => X outcome ^ 2) ≤ varianceBound)
    (hbound : ∀ outcome, |X outcome| ≤ bound)
    (hvariance_nonneg : 0 ≤ varianceBound) (hbound_nonneg : 0 ≤ bound)
    (hlogLevel_nonneg : 0 ≤ logLevel)
    (hden_pos : 0 < (Fintype.card ι : ℝ) * varianceBound + bound *
      (Real.sqrt (8 * ((Fintype.card ι : ℝ) * varianceBound) * logLevel) +
        8 * bound * logLevel)) :
    pmfProb (pmfProduct ι α μ)
      (fun sample =>
        Real.sqrt (8 * ((Fintype.card ι : ℝ) * varianceBound) * logLevel) +
            8 * bound * logLevel ≤ |∑ index, X (sample index)|) ≤
      2 * Real.exp (-logLevel) := by
  let totalVariance : ℝ := (Fintype.card ι : ℝ) * varianceBound
  let cutoff : ℝ := Real.sqrt (8 * totalVariance * logLevel) + 8 * bound * logLevel
  have htotalVariance_nonneg : 0 ≤ totalVariance := by
    dsimp [totalVariance]
    positivity
  have hcutoff_nonneg : 0 ≤ cutoff := by
    dsimp [cutoff]
    positivity
  have hsquare : 4 * logLevel * (totalVariance + bound * cutoff) ≤ cutoff ^ 2 := by
    dsimp [totalVariance, cutoff]
    exact bernstein_quantile_sq_ge htotalVariance_nonneg hbound_nonneg hlogLevel_nonneg
  have hden_pos' : 0 < totalVariance + bound * cutoff := by
    simpa [totalVariance, cutoff] using hden_pos
  have hratio : logLevel ≤ cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hden_pos')).2
    nlinarith
  have htail := pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
    (ι := ι) μ X varianceBound bound cutoff hmean hvariance hbound
    hvariance_nonneg hbound_nonneg hcutoff_nonneg (by simpa [totalVariance, cutoff] using hden_pos)
  calc
    pmfProb (pmfProduct ι α μ)
        (fun sample =>
          Real.sqrt (8 * ((Fintype.card ι : ℝ) * varianceBound) * logLevel) +
              8 * bound * logLevel ≤ |∑ index, X (sample index)|) =
        pmfProb (pmfProduct ι α μ)
          (fun sample => cutoff ≤ |∑ index, X (sample index)|) := by rfl
    _ ≤ 2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ι : ℝ) * varianceBound + bound * cutoff))) := htail
    _ = 2 * Real.exp (-cutoff ^ 2 / (4 * (totalVariance + bound * cutoff))) := by rfl
    _ ≤ 2 * Real.exp (-logLevel) := by
      have hexponent : -cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) ≤ -logLevel := by
        rw [show -cutoff ^ 2 / (4 * (totalVariance + bound * cutoff)) =
          -(cutoff ^ 2 / (4 * (totalVariance + bound * cutoff))) by ring]
        exact neg_le_neg hratio
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hexponent) (by norm_num)

/--
Two-sided Bernstein bound for iid sums of a nonnegative statistic bounded by
`range`, centered at its finite-PMF mean.  This packages the elementary range
and second-moment checks needed for finite count statistics.
-/
theorem pmfProb_pmfProduct_abs_sum_sub_mean_ge_le_bernstein_of_nonneg_le
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]
    [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (μ : PMF α) (F : α → ℝ) (range cutoff : ℝ)
    (hF_nonneg : ∀ outcome, 0 ≤ F outcome)
    (hF_le_range : ∀ outcome, F outcome ≤ range)
    (hrange_nonneg : 0 ≤ range) (hcutoff_nonneg : 0 ≤ cutoff)
    (hden_pos : 0 < (Fintype.card ι : ℝ) * range ^ 2 + range * cutoff) :
    pmfProb (pmfProduct ι α μ)
      (fun sample => cutoff ≤ |∑ index, F (sample index) -
        (Fintype.card ι : ℝ) * pmfExp μ F|) ≤
      2 * Real.exp (-cutoff ^ 2 /
        (4 * ((Fintype.card ι : ℝ) * range ^ 2 + range * cutoff))) := by
  let mean : ℝ := pmfExp μ F
  have hmean_nonneg : 0 ≤ mean := by
    dsimp [mean]
    exact pmfExp_nonneg_of_forall_nonneg μ F hF_nonneg
  have hmean_le : mean ≤ range := by
    dsimp [mean]
    exact pmfExp_le_of_forall_le μ F range hF_le_range
  have hcentered_mean : pmfExp μ (fun outcome => F outcome - mean) = 0 := by
    dsimp [mean]
    rw [pmfExp_sub, pmfExp_const]
    ring
  have hcentered_bound : ∀ outcome, |F outcome - mean| ≤ range := by
    intro outcome
    rw [abs_le]
    constructor <;> linarith [hF_nonneg outcome, hF_le_range outcome]
  have hvariance :
      pmfExp μ (fun outcome => (F outcome - mean) ^ 2) ≤ range ^ 2 := by
    apply pmfExp_le_of_forall_le
    intro outcome
    have hsq : (F outcome - mean) ^ 2 ≤ range ^ 2 := by
      have hproduct := mul_nonneg
        (sub_nonneg.mpr (hcentered_bound outcome))
        (add_nonneg hrange_nonneg (abs_nonneg (F outcome - mean)))
      rw [← sq_abs]
      nlinarith
    exact hsq
  simpa [mean] using
    (pmfProb_pmfProduct_centeredBoundedSum_abs_ge_le_bernstein
      (ι := ι) μ (fun outcome => F outcome - mean) (range ^ 2) range cutoff
      hcentered_mean hvariance hcentered_bound (sq_nonneg range) hrange_nonneg
      hcutoff_nonneg hden_pos)

end AppliedModelingLib.Probability
