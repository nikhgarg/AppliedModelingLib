import AppliedModelingLib.Privacy.MeasurePrivacyLoss

/-!
# Exponential privacy accounting for sparse outputs

This module turns the localized first and second moments of a pure-private
round with a distinguished lazy atom into a one-step exponential
supermartingale inequality.  Its compensating term charges only non-lazy
outputs, so a deterministic cap on such outputs can replace a dependence on
the total number of adaptive rounds.
-/

open MeasureTheory ProbabilityTheory Set

namespace AppliedModelingLib.Privacy

noncomputable section

/-- Real indicator that an output differs from the distinguished lazy atom. -/
noncomputable def nonLazyIndicator
    {Outcome : Type*} (bottom outcome : Outcome) : ℝ := by
  classical
  exact if outcome = bottom then 0 else 1

theorem nonLazyIndicator_eq_indicator
    {Outcome : Type*} (bottom : Outcome) :
    nonLazyIndicator bottom =
      ({bottom}ᶜ : Set Outcome).indicator (fun _ ↦ (1 : ℝ)) := by
  classical
  funext outcome
  by_cases h : outcome = bottom
  · subst outcome
    simp [nonLazyIndicator]
  · simp [nonLazyIndicator, h]

theorem measurable_nonLazyIndicator
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (bottom : Outcome) :
    Measurable (nonLazyIndicator bottom) := by
  rw [nonLazyIndicator_eq_indicator]
  exact measurable_const.indicator (measurableSet_singleton bottom).compl

theorem nonLazyIndicator_nonneg
    {Outcome : Type*} (bottom outcome : Outcome) :
    0 ≤ nonLazyIndicator bottom outcome := by
  classical
  by_cases h : outcome = bottom <;> simp [nonLazyIndicator, h]

theorem nonLazyIndicator_le_one
    {Outcome : Type*} (bottom outcome : Outcome) :
    nonLazyIndicator bottom outcome ≤ 1 := by
  classical
  by_cases h : outcome = bottom <;> simp [nonLazyIndicator, h]

/-- One-step sparse privacy-loss exponential inequality.  The compensation
`theta` is paid only when the output is non-lazy.  The displayed scalar
condition is the exact remainder needed after the localized seven-unit
second-moment bound. -/
theorem integral_exp_privacyLoss_sub_nonLazy_le_one
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    {epsilon lambda theta : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hclose : MeasureMaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hlambdaNonneg : 0 ≤ lambda) (hlambdaUnit : lambda * epsilon ≤ 1)
    (hthetaNonneg : 0 ≤ theta)
    (bottom : Outcome)
    (hfirstBottom : 0 < first.real {bottom})
    (hsecondBottom : 0 < second.real {bottom})
    (hcompensation :
      7 * lambda * (1 + lambda) * epsilon ^ 2 ≤
        (1 - Real.exp (-theta)) * (1 - lambda * epsilon)) :
    ∫ outcome, Real.exp
      (lambda * llr first second outcome -
        theta * nonLazyIndicator bottom outcome) ∂first ≤ 1 := by
  let loss := llr first second
  let rare := ({bottom}ᶜ : Set Outcome)
  let indicator := nonLazyIndicator bottom
  let discount := fun outcome ↦ Real.exp (-theta * indicator outcome)
  let charge := 1 - Real.exp (-theta)
  have hsingleton : MeasurableSet ({bottom} : Set Outcome) := measurableSet_singleton bottom
  have hrare : MeasurableSet rare := hsingleton.compl
  have hindicatorMeasurable : Measurable indicator :=
    measurable_nonLazyIndicator bottom
  have hdiscountMeasurable : Measurable discount := by
    dsimp [discount]
    fun_prop
  have hchargeNonneg : 0 ≤ charge := by
    dsimp [charge]
    have : Real.exp (-theta) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  have hchargeLeOne : charge ≤ 1 := by
    dsimp [charge]
    have hexpPositive := Real.exp_pos (-theta)
    linarith
  have hlossBound := hclose.abs_llr_le
  have hlossIntegrable : Integrable loss first :=
    integrable_llr_of_abs_le first second hlossBound
  have hlossSqIntegrable : Integrable (fun outcome ↦ loss outcome ^ 2) first := by
    refine (integrable_const (epsilon ^ 2)).mono'
      ((measurable_llr first second).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hlossBound] with outcome houtcome
    have habs : |loss outcome| ≤ |epsilon| := by
      simpa [loss, abs_of_nonneg hepsilonNonneg] using houtcome
    simpa [Real.norm_eq_abs] using (sq_le_sq.mpr habs)
  have hsecondMoment : ∫ outcome, loss outcome ^ 2 ∂first ≤
      7 * epsilon ^ 2 * first.real rare := by
    simpa [loss, rare] using
      MeasureMaxKLClose.integral_sq_llr_le_seven_mul_sq_mul_compl_atom hclose
        hepsilonNonneg hepsilonOne bottom hfirstBottom hsecondBottom
  have hmeanSecond : ∫ outcome, loss outcome ∂first ≤
      ∫ outcome, loss outcome ^ 2 ∂first := by
    exact integral_llr_le_integral_sq_of_abs_le_one first second
      hclose.1.absolutelyContinuous hclose.2.absolutelyContinuous
      hepsilonNonneg hepsilonOne hlossBound
  have hmean : ∫ outcome, loss outcome ∂first ≤
      7 * epsilon ^ 2 * first.real rare := hmeanSecond.trans hsecondMoment
  have hrareAbsIntegrable : IntegrableOn (fun outcome ↦ |loss outcome|) rare first :=
    hlossIntegrable.abs.integrableOn
  have hrareAbs : ∫ outcome in rare, |loss outcome| ∂first ≤
      epsilon * first.real rare := by
    calc
      ∫ outcome in rare, |loss outcome| ∂first ≤
          ∫ _outcome in rare, epsilon ∂first := by
        apply integral_mono_ae hrareAbsIntegrable (integrable_const epsilon)
        exact ae_restrict_of_ae hlossBound
      _ = epsilon * first.real rare := by
        rw [integral_const]
        simp [mul_comm]
  have hindicatorIntegral : ∫ outcome, indicator outcome ∂first =
      first.real rare := by
    simpa [indicator, rare, nonLazyIndicator_eq_indicator] using
      integral_indicator_one hrare
  have hindicatorIntegrable : Integrable indicator first := by
    rw [show indicator = rare.indicator (fun _ ↦ (1 : ℝ)) by
      simpa [indicator, rare] using nonLazyIndicator_eq_indicator bottom]
    exact (integrable_const 1).indicator hrare
  have hdiscountPoint : discount = fun outcome ↦
      1 - charge * indicator outcome := by
    funext outcome
    classical
    by_cases hbottom : outcome = bottom
    · subst outcome
      simp [discount, charge, indicator, nonLazyIndicator]
    · simp [discount, charge, indicator, nonLazyIndicator, hbottom]
  have hdiscountIntegrable : Integrable discount first := by
    rw [hdiscountPoint]
    exact (integrable_const 1).sub
      (hindicatorIntegrable.const_mul charge)
  have hdiscountIntegral : ∫ outcome, discount outcome ∂first =
      1 - charge * first.real rare := by
    rw [hdiscountPoint, integral_sub (integrable_const 1)
      (hindicatorIntegrable.const_mul charge), integral_const_mul,
      integral_const, hindicatorIntegral]
    simp
  have hdiscountNonneg : ∀ outcome, 0 ≤ discount outcome := fun outcome ↦ by
    dsimp [discount]
    positivity
  have hdiscountLeOne : ∀ outcome, discount outcome ≤ 1 := fun outcome ↦ by
    dsimp [discount]
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have hindicatorNonneg := nonLazyIndicator_nonneg bottom outcome
    nlinarith
  have hweightedLossPoint : ∀ outcome,
      discount outcome * loss outcome ≤
        loss outcome + charge * rare.indicator (fun value ↦ |loss value|) outcome := by
    intro outcome
    classical
    by_cases hbottom : outcome = bottom
    · subst outcome
      simp [discount, indicator, nonLazyIndicator, rare]
    · have hrareMem : outcome ∈ rare := by simpa [rare] using hbottom
      simp [discount, indicator, nonLazyIndicator, charge, rare, hbottom, hrareMem]
      have hneg : -loss outcome ≤ |loss outcome| := neg_le_abs _
      have hscaled := mul_le_mul_of_nonneg_left hneg hchargeNonneg
      nlinarith
  have hweightedLossIntegrable :
      Integrable (fun outcome ↦ discount outcome * loss outcome) first := by
    apply hlossIntegrable.bdd_mul hdiscountMeasurable.aestronglyMeasurable
    exact ae_of_all _ fun outcome ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hdiscountNonneg outcome)]
      exact hdiscountLeOne outcome
  have hweightedLoss : ∫ outcome, discount outcome * loss outcome ∂first ≤
      (7 * epsilon ^ 2 + charge * epsilon) * first.real rare := by
    calc
      ∫ outcome, discount outcome * loss outcome ∂first ≤
          ∫ outcome, (loss outcome +
            charge * rare.indicator (fun value ↦ |loss value|) outcome) ∂first := by
        apply integral_mono_ae hweightedLossIntegrable
        · exact hlossIntegrable.add
            ((hlossIntegrable.abs.indicator hrare).const_mul charge)
        · exact ae_of_all _ hweightedLossPoint
      _ = (∫ outcome, loss outcome ∂first) +
          charge * ∫ outcome in rare, |loss outcome| ∂first := by
        rw [integral_add hlossIntegrable
            ((hlossIntegrable.abs.indicator hrare).const_mul charge),
          integral_const_mul, integral_indicator hrare]
      _ ≤ 7 * epsilon ^ 2 * first.real rare +
          charge * (epsilon * first.real rare) := by
        exact add_le_add hmean
          (mul_le_mul_of_nonneg_left hrareAbs hchargeNonneg)
      _ = (7 * epsilon ^ 2 + charge * epsilon) * first.real rare := by ring
  have hweightedSqIntegrable :
      Integrable (fun outcome ↦ discount outcome * loss outcome ^ 2) first := by
    apply hlossSqIntegrable.bdd_mul hdiscountMeasurable.aestronglyMeasurable
    exact ae_of_all _ fun outcome ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hdiscountNonneg outcome)]
      exact hdiscountLeOne outcome
  have hweightedSq : ∫ outcome, discount outcome * loss outcome ^ 2 ∂first ≤
      7 * epsilon ^ 2 * first.real rare := by
    calc
      ∫ outcome, discount outcome * loss outcome ^ 2 ∂first ≤
          ∫ outcome, loss outcome ^ 2 ∂first := by
        apply integral_mono_ae hweightedSqIntegrable hlossSqIntegrable
        exact ae_of_all _ fun outcome ↦
          mul_le_of_le_one_left (sq_nonneg _) (hdiscountLeOne outcome)
      _ ≤ 7 * epsilon ^ 2 * first.real rare := hsecondMoment
  have hlambdaLossBound : ∀ᵐ outcome ∂first,
      |lambda * loss outcome| ≤ 1 := by
    filter_upwards [hlossBound] with outcome houtcome
    rw [abs_mul, abs_of_nonneg hlambdaNonneg]
    exact (mul_le_mul_of_nonneg_left houtcome hlambdaNonneg).trans hlambdaUnit
  have hexpTaylor : ∀ᵐ outcome ∂first,
      Real.exp (lambda * loss outcome) ≤
        1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2 := by
    filter_upwards [hlambdaLossBound] with outcome houtcome
    have hrem := Real.abs_exp_sub_one_sub_id_le houtcome
    have hraw := (le_abs_self
      (Real.exp (lambda * loss outcome) - 1 - lambda * loss outcome)).trans hrem
    calc
      Real.exp (lambda * loss outcome) ≤
          1 + lambda * loss outcome + (lambda * loss outcome) ^ 2 := by
        linarith
      _ = 1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2 := by ring
  have hmultiplierPoint : ∀ᵐ outcome ∂first,
      Real.exp (lambda * loss outcome - theta * indicator outcome) ≤
        discount outcome *
          (1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2) := by
    filter_upwards [hexpTaylor] with outcome houtcome
    have hfactor : Real.exp
        (lambda * loss outcome - theta * indicator outcome) =
        discount outcome * Real.exp (lambda * loss outcome) := by
      dsimp [discount]
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hfactor]
    have := mul_le_mul_of_nonneg_left houtcome (hdiscountNonneg outcome)
    nlinarith
  have hmultiplierIntegrable : Integrable (fun outcome ↦
      Real.exp (lambda * loss outcome - theta * indicator outcome)) first := by
    refine (integrable_const (Real.exp (lambda * epsilon + theta))).mono'
      (((measurable_const.mul (measurable_llr first second)).sub
        (measurable_const.mul hindicatorMeasurable)).exp.aestronglyMeasurable) ?_
    filter_upwards [hlossBound] with outcome houtcome
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hlossUpper : loss outcome ≤ epsilon := (le_abs_self _).trans houtcome
    have hindicatorUpper := nonLazyIndicator_le_one bottom outcome
    nlinarith [mul_nonneg hlambdaNonneg hepsilonNonneg,
      mul_nonneg hthetaNonneg (nonLazyIndicator_nonneg bottom outcome)]
  have hpolynomialIntegrable : Integrable (fun outcome ↦ discount outcome *
      (1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2)) first := by
    have hrewrite : (fun outcome ↦ discount outcome *
        (1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2)) =
        fun outcome ↦ discount outcome +
          lambda * (discount outcome * loss outcome) +
          lambda ^ 2 * (discount outcome * loss outcome ^ 2) := by
      funext outcome
      ring
    rw [hrewrite]
    exact (hdiscountIntegrable.add (hweightedLossIntegrable.const_mul lambda)).add
      (hweightedSqIntegrable.const_mul (lambda ^ 2))
  calc
    ∫ outcome, Real.exp
        (lambda * llr first second outcome -
          theta * nonLazyIndicator bottom outcome) ∂first =
        ∫ outcome, Real.exp
          (lambda * loss outcome - theta * indicator outcome) ∂first := by rfl
    _ ≤ ∫ outcome, discount outcome *
          (1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2) ∂first :=
      integral_mono_ae hmultiplierIntegrable hpolynomialIntegrable hmultiplierPoint
    _ = (∫ outcome, discount outcome ∂first) +
          lambda * (∫ outcome, discount outcome * loss outcome ∂first) +
          lambda ^ 2 *
            (∫ outcome, discount outcome * loss outcome ^ 2 ∂first) := by
      calc
        ∫ outcome, discount outcome *
            (1 + lambda * loss outcome + lambda ^ 2 * loss outcome ^ 2) ∂first =
            ∫ outcome, (discount outcome +
              lambda * (discount outcome * loss outcome)) +
              lambda ^ 2 * (discount outcome * loss outcome ^ 2) ∂first := by
          congr 1
          funext outcome
          ring
        _ = _ := by
          calc
            ∫ outcome, (discount outcome +
                lambda * (discount outcome * loss outcome)) +
                lambda ^ 2 * (discount outcome * loss outcome ^ 2) ∂first =
                (∫ outcome, discount outcome +
                  lambda * (discount outcome * loss outcome) ∂first) +
                ∫ outcome, lambda ^ 2 *
                  (discount outcome * loss outcome ^ 2) ∂first := by
              exact integral_add (hdiscountIntegrable.add
                (hweightedLossIntegrable.const_mul lambda))
                (hweightedSqIntegrable.const_mul (lambda ^ 2))
            _ = ((∫ outcome, discount outcome ∂first) +
                  ∫ outcome, lambda *
                    (discount outcome * loss outcome) ∂first) +
                ∫ outcome, lambda ^ 2 *
                  (discount outcome * loss outcome ^ 2) ∂first := by
              rw [integral_add hdiscountIntegrable
                (hweightedLossIntegrable.const_mul lambda)]
            _ = _ := by
              rw [integral_const_mul, integral_const_mul]
    _ ≤ (1 - charge * first.real rare) +
          lambda * ((7 * epsilon ^ 2 + charge * epsilon) * first.real rare) +
          lambda ^ 2 * (7 * epsilon ^ 2 * first.real rare) := by
      rw [hdiscountIntegral]
      gcongr
    _ ≤ 1 := by
      have hrareMass : 0 ≤ first.real rare := measureReal_nonneg
      have hcoefficient :
          -charge + lambda * (7 * epsilon ^ 2 + charge * epsilon) +
              lambda ^ 2 * (7 * epsilon ^ 2) ≤ 0 := by
        dsimp [charge] at hcompensation ⊢
        nlinarith
      nlinarith

end

end AppliedModelingLib.Privacy
