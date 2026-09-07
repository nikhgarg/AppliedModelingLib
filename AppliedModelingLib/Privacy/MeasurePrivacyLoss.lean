import AppliedModelingLib.Privacy.Measure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# Privacy loss for arbitrary probability measures

This file connects eventwise pure differential privacy on a measurable output
space to the Radon--Nikodym log-likelihood ratio used in adaptive composition.
The results are independent of any finite or discrete transcript model.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace AppliedModelingLib.Privacy

noncomputable section

/-- Pure event domination implies absolute continuity. -/
theorem MeasureApproxDomination.absolutelyContinuous
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsFiniteMeasure first] [IsFiniteMeasure second]
    (h : MeasureApproxDomination epsilon 0 first second) :
    first ≪ second := by
  refine Measure.AbsolutelyContinuous.mk fun event hevent hsecondZero ↦ ?_
  have hsecondReal : second.real event = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top second event)).2 hsecondZero
  have hfirstReal : first.real event = 0 := by
    have hbound := h event hevent
    rw [hsecondReal] at hbound
    simp only [mul_zero, add_zero] at hbound
    exact le_antisymm hbound measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top first event)).1 hfirstReal

/-- Pure event domination is equivalently a measure-order bound by the
exponential scalar. -/
theorem MeasureApproxDomination.measure_le_exp_smul
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsFiniteMeasure first] [IsFiniteMeasure second]
    (h : MeasureApproxDomination epsilon 0 first second) :
    first ≤ ENNReal.ofReal (Real.exp epsilon) • second := by
  rw [Measure.le_iff]
  intro event hevent
  rw [← ENNReal.toReal_le_toReal (measure_ne_top first event)]
  · change first.real event ≤
      (ENNReal.ofReal (Real.exp epsilon) • second).real event
    rw [measureReal_ennreal_smul_apply,
      ENNReal.toReal_ofReal (Real.exp_pos epsilon).le]
    simpa using h event hevent
  · simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top second event)

/-- Pure event domination bounds the log-likelihood ratio almost everywhere
under the first law. -/
theorem MeasureApproxDomination.llr_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureApproxDomination epsilon 0 first second) :
    ∀ᵐ outcome ∂first, llr first second outcome ≤ epsilon := by
  let c : ℝ≥0 := ⟨Real.exp epsilon, (Real.exp_pos epsilon).le⟩
  have hcpos : 0 < c := by
    change 0 < Real.exp epsilon
    exact Real.exp_pos epsilon
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hle : first ≤ c • second := by
    rw [Measure.le_iff]
    intro event hevent
    rw [← ENNReal.toReal_le_toReal (measure_ne_top first event)]
    · change first.real event ≤ (c • second).real event
      rw [measureReal_nnreal_smul_apply]
      simpa [c] using h event hevent
    · finiteness
  have hac : first ≪ second := h.absolutelyContinuous
  have hacScaled : first ≪ c • second := hle.absolutelyContinuous
  have hrnLe : ∀ᵐ outcome ∂first,
      first.rnDeriv (c • second) outcome ≤ 1 :=
    hacScaled.ae_le (Measure.rnDeriv_le_one_of_le hle)
  have hscale := llr_smul_nnreal_right hac c hc
  filter_upwards [hrnLe, hscale] with outcome houtcome hscaleOutcome
  have hscaledNonpos : llr first (c • second) outcome ≤ 0 := by
    unfold llr
    exact Real.log_nonpos ENNReal.toReal_nonneg
      (ENNReal.toReal_le_coe_of_le_coe houtcome)
  rw [hscaleOutcome] at hscaledNonpos
  have hlogc : Real.log (c : ℝ) = epsilon := by
    change Real.log (Real.exp epsilon) = epsilon
    exact Real.log_exp epsilon
  rw [hlogc] at hscaledNonpos
  linarith

/-- Two-sided pure privacy bounds the absolute privacy loss almost surely. -/
theorem MeasureMaxKLClose.abs_llr_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureMaxKLClose epsilon 0 first second) :
    ∀ᵐ outcome ∂first, |llr first second outcome| ≤ epsilon := by
  have hforward := h.1.llr_le
  have hac : first ≪ second := h.1.absolutelyContinuous
  have hreverseUnderSecond := h.2.llr_le
  have hreverseUnderFirst : ∀ᵐ outcome ∂first,
      llr second first outcome ≤ epsilon :=
    hac.ae_le hreverseUnderSecond
  have hneg := neg_llr hac
  filter_upwards [hforward, hreverseUnderFirst, hneg] with outcome hupper hlower hneg
  rw [Pi.neg_apply] at hneg
  rw [← hneg] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

/-- A first-law tail bound for the log-likelihood ratio implies directed
approximate domination.  This is the arbitrary-measurable-space version of
the standard privacy-loss bad-event argument. -/
theorem MeasureApproxDomination.of_llr_tail
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon delta : ℝ} (first second : Measure Outcome)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hforward : first ≪ second)
    (htail : first.real {outcome | epsilon < llr first second outcome} ≤ delta) :
    MeasureApproxDomination epsilon delta first second := by
  let bad : Set Outcome := {outcome | epsilon < llr first second outcome}
  have hbadMeasurable : MeasurableSet bad := by
    exact measurableSet_Ioi.preimage (measurable_llr first second)
  apply MeasureApproxDomination.of_outside_bad first second bad
    hbadMeasurable (by simpa [bad] using htail)
  intro event hevent
  let goodPart := event \ bad
  have hgoodPart : MeasurableSet goodPart := hevent.diff hbadMeasurable
  have hrnIntegrable : IntegrableOn
      (fun outcome ↦ (first.rnDeriv second outcome).toReal) goodPart second :=
    Measure.integrableOn_toReal_rnDeriv (measure_ne_top first goodPart)
  have hrnBound : ∀ outcome ∈ goodPart,
      (first.rnDeriv second outcome).toReal ≤ Real.exp epsilon := by
    intro outcome houtcome
    have hgood : llr first second outcome ≤ epsilon := by
      exact not_lt.mp houtcome.2
    by_cases hzero : (first.rnDeriv second outcome).toReal = 0
    · rw [hzero]
      exact (Real.exp_pos _).le
    · have hpos : 0 < (first.rnDeriv second outcome).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
      calc
        (first.rnDeriv second outcome).toReal =
            Real.exp (Real.log (first.rnDeriv second outcome).toReal) := by
          rw [Real.exp_log hpos]
        _ ≤ Real.exp epsilon := Real.exp_le_exp.mpr hgood
  calc
    first.real (event \ bad) =
        ∫ outcome in goodPart,
          (first.rnDeriv second outcome).toReal ∂second := by
      rw [Measure.setIntegral_toReal_rnDeriv hforward goodPart]
    _ ≤ ∫ _outcome in goodPart, Real.exp epsilon ∂second := by
      apply integral_mono_ae hrnIntegrable (integrable_const _)
      exact ae_restrict_of_forall_mem hgoodPart hrnBound
    _ = Real.exp epsilon * second.real goodPart := by
      rw [integral_const]
      simp [mul_comm]
    _ ≤ Real.exp epsilon * second.real event := by
      exact mul_le_mul_of_nonneg_left
        (measureReal_mono diff_subset (measure_ne_top second event))
        (Real.exp_pos _).le

/-- On the unit privacy range, two-sided pure privacy localizes the absolute
difference of any event probability to the first law's mass of that event. -/
theorem MeasureMaxKLClose.abs_measureReal_sub_le_two_mul
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    (h : MeasureMaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (event : Set Outcome) (hevent : MeasurableSet event) :
    |first.real event - second.real event| ≤
      2 * epsilon * first.real event := by
  have hforward := h.1 event hevent
  have hreverse := h.2 event hevent
  simp only [add_zero] at hforward hreverse
  have habsEpsilon : |epsilon| ≤ 1 := by
    rw [abs_of_nonneg hepsilonNonneg]
    exact hepsilonOne
  have hrem := Real.abs_exp_sub_one_sub_id_le habsEpsilon
  have hexpRemainder : Real.exp epsilon - 1 - epsilon ≤ epsilon ^ 2 :=
    (le_abs_self _).trans hrem
  have hexpSub : Real.exp epsilon - 1 ≤ 2 * epsilon := by
    nlinarith [mul_self_le_mul_self hepsilonNonneg hepsilonOne]
  by_cases horder : first.real event ≤ second.real event
  · rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    simp only [neg_sub]
    have hmass : 0 ≤ first.real event := measureReal_nonneg
    calc
      second.real event - first.real event ≤
          (Real.exp epsilon - 1) * first.real event := by linarith
      _ ≤ (2 * epsilon) * first.real event :=
        mul_le_mul_of_nonneg_right hexpSub hmass
      _ = 2 * epsilon * first.real event := by ring
  · have horder' : second.real event ≤ first.real event := le_of_not_ge horder
    rw [abs_of_nonneg (sub_nonneg.mpr horder')]
    have hmass : 0 ≤ second.real event := measureReal_nonneg
    calc
      first.real event - second.real event ≤
          (Real.exp epsilon - 1) * second.real event := by linarith
      _ ≤ (2 * epsilon) * second.real event :=
        mul_le_mul_of_nonneg_right hexpSub hmass
      _ ≤ (2 * epsilon) * first.real event := by
        exact mul_le_mul_of_nonneg_left horder' (mul_nonneg (by norm_num) hepsilonNonneg)
      _ = 2 * epsilon * first.real event := by ring

/-- A positive atom's weighted log-ratio is controlled by three times its
mass difference whenever the forward ratio is at most `exp(epsilon)` on the
unit privacy range. -/
theorem mul_abs_log_div_le_three_abs_sub
    {epsilon firstMass secondMass : ℝ}
    (hepsilonOne : epsilon ≤ 1)
    (hfirst : 0 < firstMass) (hsecond : 0 < secondMass)
    (hforward : firstMass ≤ Real.exp epsilon * secondMass) :
    firstMass * |Real.log (firstMass / secondMass)| ≤
      3 * |firstMass - secondMass| := by
  have hexpThree : Real.exp epsilon ≤ 3 := by
    exact (Real.exp_le_exp.mpr hepsilonOne).trans Real.exp_one_lt_three.le
  by_cases horder : firstMass ≤ secondMass
  · have hratioPos : 0 < secondMass / firstMass := div_pos hsecond hfirst
    have hlogBound := Real.log_le_sub_one_of_pos hratioPos
    have hratio : firstMass / secondMass ≤ 1 :=
      (div_le_one hsecond).2 horder
    have hlogNonpos : Real.log (firstMass / secondMass) ≤ 0 :=
      Real.log_nonpos (div_nonneg hfirst.le hsecond.le) hratio
    rw [abs_of_nonpos hlogNonpos, abs_of_nonpos (sub_nonpos.mpr horder)]
    have hlogSwap : -Real.log (firstMass / secondMass) =
        Real.log secondMass - Real.log firstMass := by
      rw [Real.log_div hfirst.ne' hsecond.ne']
      ring
    rw [hlogSwap, neg_sub]
    have hidentity : firstMass * (secondMass / firstMass - 1) =
        secondMass - firstMass := by field_simp
    have hlogBound' : Real.log secondMass - Real.log firstMass ≤
        secondMass / firstMass - 1 := by
      rw [← Real.log_div hsecond.ne' hfirst.ne']
      exact hlogBound
    calc
      firstMass * (Real.log secondMass - Real.log firstMass) ≤
          firstMass * (secondMass / firstMass - 1) :=
        mul_le_mul_of_nonneg_left hlogBound' hfirst.le
      _ = secondMass - firstMass := hidentity
      _ ≤ 3 * (secondMass - firstMass) := by nlinarith
  · have horder' : secondMass ≤ firstMass := le_of_not_ge horder
    have hratioPos : 0 < firstMass / secondMass := div_pos hfirst hsecond
    have hlogBound := Real.log_le_sub_one_of_pos hratioPos
    have hratioOne : 1 ≤ firstMass / secondMass :=
      (one_le_div hsecond).2 horder'
    have hlogNonneg : 0 ≤ Real.log (firstMass / secondMass) :=
      Real.log_nonneg hratioOne
    rw [abs_of_nonneg hlogNonneg, abs_of_nonneg (sub_nonneg.mpr horder')]
    have hratioExp : firstMass / secondMass ≤ Real.exp epsilon :=
      (div_le_iff₀ hsecond).2 hforward
    have hidentity : firstMass * (firstMass / secondMass - 1) =
        (firstMass / secondMass) * (firstMass - secondMass) := by
      field_simp
    calc
      firstMass * Real.log (firstMass / secondMass) ≤
          firstMass * (firstMass / secondMass - 1) :=
        mul_le_mul_of_nonneg_left hlogBound hfirst.le
      _ = (firstMass / secondMass) * (firstMass - secondMass) := hidentity
      _ ≤ Real.exp epsilon * (firstMass - secondMass) :=
        mul_le_mul_of_nonneg_right hratioExp (sub_nonneg.mpr horder')
      _ ≤ 3 * (firstMass - secondMass) :=
        mul_le_mul_of_nonneg_right hexpThree (sub_nonneg.mpr horder')

/-- The elementary second-order exponential remainder used to bound expected
privacy loss.  The unit interval is exactly the regime needed by HR10. -/
theorem privacyLoss_le_one_sub_exp_neg_add_sq
    {x : ℝ} (hx : |x| ≤ 1) :
    x ≤ 1 - Real.exp (-x) + x ^ 2 := by
  have hrem := Real.abs_exp_sub_one_sub_id_le (x := -x) (by simpa using hx)
  have hupper : Real.exp (-x) - 1 - (-x) ≤ (-x) ^ 2 :=
    (le_abs_self _).trans hrem
  nlinarith

/-- The reverse likelihood exponential has expectation one under the first
law when the two probability laws are mutually absolutely continuous. -/
theorem integral_exp_neg_llr_eq_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (first second : Measure Outcome)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hforward : first ≪ second) (hreverse : second ≪ first) :
    ∫ outcome, Real.exp (-llr first second outcome) ∂first = 1 := by
  rw [integral_congr_ae (exp_neg_llr hforward)]
  rw [Measure.integral_toReal_rnDeriv hreverse]
  simp

/-- A measurable privacy-loss variable bounded in `[-bound,bound]` is
integrable on a finite law. -/
theorem integrable_llr_of_abs_le
    {Outcome : Type*} [MeasurableSpace Outcome]
    (first second : Measure Outcome) [IsFiniteMeasure first]
    {bound : ℝ} (hbound : ∀ᵐ outcome ∂first, |llr first second outcome| ≤ bound) :
    Integrable (llr first second) first := by
  exact (integrable_const bound).mono'
    (measurable_llr first second).aestronglyMeasurable hbound

/-- At a positive-mass atom, the Radon--Nikodym log-likelihood is the log of
the ratio of the two atom masses. -/
theorem llr_eq_log_measureReal_div_at_atom
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    (first second : Measure Outcome) [IsFiniteMeasure first] [IsFiniteMeasure second]
    (hforward : first ≪ second) (outcome : Outcome)
    (hsecond : 0 < second.real {outcome}) :
    llr first second outcome =
      Real.log (first.real {outcome} / second.real {outcome}) := by
  have hmass := setIntegral_toReal_rnDeriv_mul
    (μ := first) (ν := second) hforward
    (f := fun _ : Outcome ↦ (1 : ℝ)) (measurableSet_singleton outcome)
  simp only [mul_one, integral_singleton, smul_eq_mul] at hmass
  have hrn : (first.rnDeriv second outcome).toReal =
      first.real {outcome} / second.real {outcome} := by
    rw [eq_div_iff hsecond.ne']
    nlinarith
  unfold llr
  rw [hrn]

/-- An almost-sure real inequality holds at every positive-mass atom. -/
theorem ae_le_at_atom
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    {measure : Measure Outcome} [IsFiniteMeasure measure]
    {f : Outcome → ℝ} {bound : ℝ} {outcome : Outcome}
    (hmass : 0 < measure.real {outcome})
    (h : ∀ᵐ value ∂measure, f value ≤ bound) :
    f outcome ≤ bound := by
  have hmono := integral_mono_ae
    (integrableOn_singleton (μ := measure) (f := f) (x := outcome))
    (integrableOn_singleton (μ := measure)
      (f := fun _ : Outcome ↦ bound) (x := outcome))
    (ae_restrict_of_ae h)
  simp only [integral_singleton, smul_eq_mul] at hmono
  nlinarith

/-- The second-order likelihood identity bounds expected privacy loss by its
second moment.  This localized form is useful when the squared loss is
supported mostly on rare transcript outcomes. -/
theorem integral_llr_le_integral_sq_of_abs_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (first second : Measure Outcome)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hforward : first ≪ second) (hreverse : second ≪ first)
    {bound : ℝ} (hboundNonneg : 0 ≤ bound) (hboundOne : bound ≤ 1)
    (hbound : ∀ᵐ outcome ∂first, |llr first second outcome| ≤ bound) :
    ∫ outcome, llr first second outcome ∂first ≤
      ∫ outcome, (llr first second outcome) ^ 2 ∂first := by
  let loss := llr first second
  have hlossIntegrable : Integrable loss first :=
    integrable_llr_of_abs_le first second hbound
  have hlossSqIntegrable : Integrable (fun outcome ↦ loss outcome ^ 2) first := by
    refine (integrable_const (bound ^ 2)).mono'
      ((measurable_llr first second).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound] with outcome houtcome
    have habs : |loss outcome| ≤ |bound| := by
      simpa [loss, abs_of_nonneg hboundNonneg] using houtcome
    simpa [Real.norm_eq_abs] using (sq_le_sq.mpr habs)
  have hexpIntegrable : Integrable (fun outcome ↦ Real.exp (-loss outcome)) first := by
    rw [integrable_congr (exp_neg_llr hforward)]
    exact Measure.integrable_toReal_rnDeriv
  have hpointwise : ∀ᵐ outcome ∂first,
      loss outcome ≤ 1 - Real.exp (-loss outcome) + loss outcome ^ 2 := by
    filter_upwards [hbound] with outcome houtcome
    exact privacyLoss_le_one_sub_exp_neg_add_sq
      (hx := houtcome.trans hboundOne)
  calc
    ∫ outcome, loss outcome ∂first ≤
        ∫ outcome, (1 - Real.exp (-loss outcome) + loss outcome ^ 2) ∂first := by
      exact integral_mono_ae hlossIntegrable
        (((integrable_const 1).sub hexpIntegrable).add hlossSqIntegrable)
        hpointwise
    _ = (∫ outcome, 1 - Real.exp (-loss outcome) ∂first) +
          ∫ outcome, loss outcome ^ 2 ∂first := by
      exact integral_add ((integrable_const 1).sub hexpIntegrable)
        hlossSqIntegrable
    _ = ∫ outcome, loss outcome ^ 2 ∂first := by
      rw [integral_sub (integrable_const 1) hexpIntegrable,
        integral_const,
        integral_exp_neg_llr_eq_one first second hforward hreverse]
      simp

/-- Sparse-output privacy loss has a localized second moment.  The constant
seven is the sum of one unit for non-atom outputs and six units for the lazy
atom's normalization loss. -/
theorem MeasureMaxKLClose.integral_sq_llr_le_seven_mul_sq_mul_compl_atom
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureMaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (bottom : Outcome)
    (hfirstBottom : 0 < first.real {bottom})
    (hsecondBottom : 0 < second.real {bottom}) :
    ∫ outcome, (llr first second outcome) ^ 2 ∂first ≤
      7 * epsilon ^ 2 * first.real ({bottom}ᶜ) := by
  let loss := llr first second
  let rare := ({bottom}ᶜ : Set Outcome)
  have hsingleton : MeasurableSet ({bottom} : Set Outcome) := measurableSet_singleton bottom
  have hrare : MeasurableSet rare := hsingleton.compl
  have hlossBound := h.abs_llr_le
  have hlossSqIntegrable : Integrable (fun outcome ↦ loss outcome ^ 2) first := by
    refine (integrable_const (epsilon ^ 2)).mono'
      ((measurable_llr first second).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hlossBound] with outcome houtcome
    have habs : |loss outcome| ≤ |epsilon| := by
      simpa [loss, abs_of_nonneg hepsilonNonneg] using houtcome
    simpa [Real.norm_eq_abs] using (sq_le_sq.mpr habs)
  have hrareSq : ∫ outcome in rare, loss outcome ^ 2 ∂first ≤
      epsilon ^ 2 * first.real rare := by
    calc
      ∫ outcome in rare, loss outcome ^ 2 ∂first ≤
          ∫ _outcome in rare, epsilon ^ 2 ∂first := by
        apply integral_mono_ae hlossSqIntegrable.integrableOn
          (integrable_const (epsilon ^ 2))
        exact ae_restrict_of_ae (hlossBound.mono fun outcome houtcome ↦ by
          have habs : |loss outcome| ≤ |epsilon| := by
            simpa [loss, abs_of_nonneg hepsilonNonneg] using houtcome
          exact sq_le_sq.mpr habs)
      _ = epsilon ^ 2 * first.real rare := by
        rw [integral_const]
        simp [mul_comm]
  have hlossBottom : loss bottom =
      Real.log (first.real {bottom} / second.real {bottom}) := by
    exact llr_eq_log_measureReal_div_at_atom first second
      h.1.absolutelyContinuous bottom hsecondBottom
  have habsBottom : |loss bottom| ≤ epsilon :=
    ae_le_at_atom (measure := first) (f := fun value ↦ |loss value|)
      (outcome := bottom) hfirstBottom hlossBound
  have hforwardBottom : first.real {bottom} ≤
      Real.exp epsilon * second.real {bottom} := by
    simpa using h.1 {bottom} hsingleton
  have hweightedLog : first.real {bottom} *
      |Real.log (first.real {bottom} / second.real {bottom})| ≤
        3 * |first.real {bottom} - second.real {bottom}| :=
    mul_abs_log_div_le_three_abs_sub hepsilonOne
      hfirstBottom hsecondBottom hforwardBottom
  have hmassDifferenceRare :
      |first.real rare - second.real rare| ≤
        2 * epsilon * first.real rare :=
    h.abs_measureReal_sub_le_two_mul hepsilonNonneg hepsilonOne rare hrare
  have hmassDifference :
      |first.real {bottom} - second.real {bottom}| ≤
        2 * epsilon * first.real rare := by
    have hfirstComplement := probReal_compl_eq_one_sub
      (μ := first) hsingleton
    have hsecondComplement := probReal_compl_eq_one_sub
      (μ := second) hsingleton
    change first.real rare = 1 - first.real {bottom} at hfirstComplement
    change second.real rare = 1 - second.real {bottom} at hsecondComplement
    calc
      |first.real {bottom} - second.real {bottom}| =
          |first.real rare - second.real rare| := by
        rw [hfirstComplement, hsecondComplement]
        have hinner :
            (1 - first.real {bottom}) - (1 - second.real {bottom}) =
              second.real {bottom} - first.real {bottom} := by ring
        rw [hinner, abs_sub_comm]
      _ ≤ 2 * epsilon * first.real rare := hmassDifferenceRare
  have hatomSq : ∫ outcome in ({bottom} : Set Outcome), loss outcome ^ 2 ∂first ≤
      6 * epsilon ^ 2 * first.real rare := by
    rw [integral_singleton]
    change first.real {bottom} * loss bottom ^ 2 ≤
      6 * epsilon ^ 2 * first.real rare
    calc
      first.real {bottom} * loss bottom ^ 2 =
          |loss bottom| * (first.real {bottom} * |loss bottom|) := by
        rw [← sq_abs]
        ring
      _ ≤ epsilon * (first.real {bottom} * |loss bottom|) :=
        mul_le_mul_of_nonneg_right habsBottom
          (mul_nonneg measureReal_nonneg (abs_nonneg _))
      _ = epsilon * (first.real {bottom} *
          |Real.log (first.real {bottom} / second.real {bottom})|) := by
        rw [hlossBottom]
      _ ≤ epsilon * (3 * |first.real {bottom} - second.real {bottom}|) :=
        mul_le_mul_of_nonneg_left hweightedLog hepsilonNonneg
      _ ≤ epsilon * (3 * (2 * epsilon * first.real rare)) := by
        gcongr
      _ = 6 * epsilon ^ 2 * first.real rare := by ring
  calc
    ∫ outcome, loss outcome ^ 2 ∂first =
        (∫ outcome in ({bottom} : Set Outcome), loss outcome ^ 2 ∂first) +
          ∫ outcome in rare, loss outcome ^ 2 ∂first := by
      simpa [rare] using
        (integral_add_compl hsingleton hlossSqIntegrable).symm
    _ ≤ 6 * epsilon ^ 2 * first.real rare +
          epsilon ^ 2 * first.real rare := add_le_add hatomSq hrareSq
    _ = 7 * epsilon ^ 2 * first.real rare := by ring

/-- Sparse-output expected privacy loss.  If two pure-private laws share a
distinguished positive-mass atom, their expected privacy loss is proportional
to the first law's probability of producing anything other than that atom.
This is the measure-theoretic localization needed for sparse-vector-style
composition. -/
theorem MeasureMaxKLClose.integral_llr_le_eight_mul_sq_mul_compl_atom
    {Outcome : Type*} [MeasurableSpace Outcome] [MeasurableSingletonClass Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureMaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (bottom : Outcome)
    (hfirstBottom : 0 < first.real {bottom})
    (hsecondBottom : 0 < second.real {bottom}) :
    ∫ outcome, llr first second outcome ∂first ≤
      8 * epsilon ^ 2 * first.real ({bottom}ᶜ) := by
  let loss := llr first second
  let rare := ({bottom}ᶜ : Set Outcome)
  have hsingleton : MeasurableSet ({bottom} : Set Outcome) := measurableSet_singleton bottom
  have hrare : MeasurableSet rare := hsingleton.compl
  have hlossBound := h.abs_llr_le
  have hlossIntegrable : Integrable loss first :=
    integrable_llr_of_abs_le first second hlossBound
  have hlossSqIntegrable : Integrable (fun outcome ↦ loss outcome ^ 2) first := by
    refine (integrable_const (epsilon ^ 2)).mono'
      ((measurable_llr first second).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hlossBound] with outcome houtcome
    have habs : |loss outcome| ≤ |epsilon| := by
      simpa [loss, abs_of_nonneg hepsilonNonneg] using houtcome
    simpa [Real.norm_eq_abs] using (sq_le_sq.mpr habs)
  have hmeanSecond : ∫ outcome, loss outcome ∂first ≤
      ∫ outcome, loss outcome ^ 2 ∂first := by
    exact integral_llr_le_integral_sq_of_abs_le_one first second
      h.1.absolutelyContinuous h.2.absolutelyContinuous
      hepsilonNonneg hepsilonOne hlossBound
  have hrareSq : ∫ outcome in rare, loss outcome ^ 2 ∂first ≤
      epsilon ^ 2 * first.real rare := by
    calc
      ∫ outcome in rare, loss outcome ^ 2 ∂first ≤
          ∫ _outcome in rare, epsilon ^ 2 ∂first := by
        apply integral_mono_ae hlossSqIntegrable.integrableOn
          (integrable_const (epsilon ^ 2))
        exact ae_restrict_of_ae (hlossBound.mono fun outcome houtcome ↦ by
          have habs : |loss outcome| ≤ |epsilon| := by
            simpa [loss, abs_of_nonneg hepsilonNonneg] using houtcome
          exact sq_le_sq.mpr habs)
      _ = epsilon ^ 2 * first.real rare := by
        rw [integral_const]
        simp [mul_comm]
  have hlossBottom : loss bottom =
      Real.log (first.real {bottom} / second.real {bottom}) := by
    exact llr_eq_log_measureReal_div_at_atom first second
      h.1.absolutelyContinuous bottom hsecondBottom
  have habsBottom : |loss bottom| ≤ epsilon :=
    ae_le_at_atom (measure := first) (f := fun value ↦ |loss value|)
      (outcome := bottom) hfirstBottom hlossBound
  have hforwardBottom : first.real {bottom} ≤
      Real.exp epsilon * second.real {bottom} := by
    simpa using h.1 {bottom} hsingleton
  have hweightedLog : first.real {bottom} *
      |Real.log (first.real {bottom} / second.real {bottom})| ≤
        3 * |first.real {bottom} - second.real {bottom}| :=
    mul_abs_log_div_le_three_abs_sub hepsilonOne
      hfirstBottom hsecondBottom hforwardBottom
  have hmassDifferenceRare :
      |first.real rare - second.real rare| ≤
        2 * epsilon * first.real rare :=
    h.abs_measureReal_sub_le_two_mul hepsilonNonneg hepsilonOne rare hrare
  have hmassDifference :
      |first.real {bottom} - second.real {bottom}| ≤
        2 * epsilon * first.real rare := by
    have hfirstComplement := probReal_compl_eq_one_sub
      (μ := first) hsingleton
    have hsecondComplement := probReal_compl_eq_one_sub
      (μ := second) hsingleton
    change first.real rare = 1 - first.real {bottom} at hfirstComplement
    change second.real rare = 1 - second.real {bottom} at hsecondComplement
    calc
      |first.real {bottom} - second.real {bottom}| =
          |first.real rare - second.real rare| := by
        rw [hfirstComplement, hsecondComplement]
        have hinner :
            (1 - first.real {bottom}) - (1 - second.real {bottom}) =
              second.real {bottom} - first.real {bottom} := by ring
        rw [hinner, abs_sub_comm]
      _ ≤ 2 * epsilon * first.real rare := hmassDifferenceRare
  have hatomSq : ∫ outcome in ({bottom} : Set Outcome), loss outcome ^ 2 ∂first ≤
      6 * epsilon ^ 2 * first.real rare := by
    rw [integral_singleton]
    change first.real {bottom} * loss bottom ^ 2 ≤
      6 * epsilon ^ 2 * first.real rare
    calc
      first.real {bottom} * loss bottom ^ 2 =
          |loss bottom| * (first.real {bottom} * |loss bottom|) := by
        rw [← sq_abs]
        ring
      _ ≤ epsilon * (first.real {bottom} * |loss bottom|) :=
        mul_le_mul_of_nonneg_right habsBottom
          (mul_nonneg measureReal_nonneg (abs_nonneg _))
      _ = epsilon * (first.real {bottom} *
          |Real.log (first.real {bottom} / second.real {bottom})|) := by
        rw [hlossBottom]
      _ ≤ epsilon * (3 * |first.real {bottom} - second.real {bottom}|) :=
        mul_le_mul_of_nonneg_left hweightedLog hepsilonNonneg
      _ ≤ epsilon * (3 * (2 * epsilon * first.real rare)) := by
        gcongr
      _ = 6 * epsilon ^ 2 * first.real rare := by ring
  calc
    ∫ outcome, loss outcome ∂first ≤
        ∫ outcome, loss outcome ^ 2 ∂first := hmeanSecond
    _ = (∫ outcome in ({bottom} : Set Outcome), loss outcome ^ 2 ∂first) +
          ∫ outcome in rare, loss outcome ^ 2 ∂first := by
      simpa [rare] using
        (integral_add_compl hsingleton hlossSqIntegrable).symm
    _ ≤ 6 * epsilon ^ 2 * first.real rare +
          epsilon ^ 2 * first.real rare := add_le_add hatomSq hrareSq
    _ ≤ 8 * epsilon ^ 2 * first.real rare := by
      nlinarith [sq_nonneg epsilon, measureReal_nonneg (μ := first) (s := rare)]

/-- A bounded likelihood ratio has expected privacy loss at most the square
of its bound.  This is the expectation estimate behind the classical
advanced-composition proof; no finiteness of the output carrier is used. -/
theorem integral_llr_le_sq_of_abs_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (first second : Measure Outcome)
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (hforward : first ≪ second) (hreverse : second ≪ first)
    {bound : ℝ} (hboundNonneg : 0 ≤ bound) (hboundOne : bound ≤ 1)
    (hbound : ∀ᵐ outcome ∂first, |llr first second outcome| ≤ bound) :
    ∫ outcome, llr first second outcome ∂first ≤ bound ^ 2 := by
  let loss := llr first second
  have hlossIntegrable : Integrable loss first :=
    integrable_llr_of_abs_le first second hbound
  have hlossSqIntegrable : Integrable (fun outcome ↦ loss outcome ^ 2) first := by
    refine (integrable_const (bound ^ 2)).mono'
      ((measurable_llr first second).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound] with outcome houtcome
    have habs : |loss outcome| ≤ |bound| := by
      simpa [loss, abs_of_nonneg hboundNonneg] using houtcome
    simpa [Real.norm_eq_abs] using (sq_le_sq.mpr habs)
  have hexpIntegrable : Integrable (fun outcome ↦ Real.exp (-loss outcome)) first := by
    rw [integrable_congr (exp_neg_llr hforward)]
    exact Measure.integrable_toReal_rnDeriv
  have hpointwise : ∀ᵐ outcome ∂first,
      loss outcome ≤ 1 - Real.exp (-loss outcome) + loss outcome ^ 2 := by
    filter_upwards [hbound] with outcome houtcome
    exact privacyLoss_le_one_sub_exp_neg_add_sq
      (hx := houtcome.trans hboundOne)
  calc
    ∫ outcome, loss outcome ∂first ≤
        ∫ outcome, (1 - Real.exp (-loss outcome) + loss outcome ^ 2) ∂first := by
      exact integral_mono_ae hlossIntegrable
        (((integrable_const 1).sub hexpIntegrable).add hlossSqIntegrable)
        hpointwise
    _ = (∫ outcome, 1 - Real.exp (-loss outcome) ∂first) +
          ∫ outcome, loss outcome ^ 2 ∂first := by
      exact integral_add ((integrable_const 1).sub hexpIntegrable)
        hlossSqIntegrable
    _ = ∫ outcome, loss outcome ^ 2 ∂first := by
      rw [integral_sub (integrable_const 1) hexpIntegrable,
        integral_const,
        integral_exp_neg_llr_eq_one first second hforward hreverse]
      simp
    _ ≤ ∫ _outcome, bound ^ 2 ∂first := by
      apply integral_mono_ae hlossSqIntegrable (integrable_const (bound ^ 2))
      filter_upwards [hbound] with outcome houtcome
      have habs : |loss outcome| ≤ |bound| := by
        simpa [loss, abs_of_nonneg hboundNonneg] using houtcome
      exact sq_le_sq.mpr habs
    _ = bound ^ 2 := by simp

/-- Expected privacy loss of two pure-private probability laws is quadratic
in the privacy parameter in the unit regime. -/
theorem MeasureMaxKLClose.integral_llr_le_sq
    {Outcome : Type*} [MeasurableSpace Outcome]
    {epsilon : ℝ} {first second : Measure Outcome}
    [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (h : MeasureMaxKLClose epsilon 0 first second)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1) :
    ∫ outcome, llr first second outcome ∂first ≤ epsilon ^ 2 := by
  exact integral_llr_le_sq_of_abs_le_one first second
    h.1.absolutelyContinuous h.2.absolutelyContinuous
    hepsilonNonneg hepsilonOne h.abs_llr_le

end

end AppliedModelingLib.Privacy
