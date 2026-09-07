import AppliedModelingLib.Learning.Online.AdaBoost
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# AdaBoost.R's continuous regression reduction

Freund--Schapire (1997), Section 5.3, reduces regression on a finite training
set with labels in `[0, 1]` to binary prediction on `Training × [0, 1]`.  The
second coordinate is equipped with Lebesgue measure restricted to the unit
interval.  This module develops the concrete normalizer and loss bridge used
by that reduction before its adaptive density analysis.
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

open scoped BigOperators Interval
open MeasureTheory

/-- Lebesgue measure on the source label interval `[0, 1]`. -/
noncomputable def adaBoostRUnitMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) 1)

/-- The source normalizer `Z = Σ_i D(i) ∫₀¹ |y - yᵢ| dy` in Eq. (25). -/
noncomputable def adaBoostRNormalizer
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ) : ℝ :=
  ∑ sample, exampleWeight sample *
    ∫ y, |y - label sample| ∂adaBoostRUnitMeasure

/-- The initial continuous density in Figure 5. -/
noncomputable def adaBoostRBaseDensity
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ) : Training → ℝ → ℝ :=
  fun sample y =>
    exampleWeight sample * |y - label sample| /
      adaBoostRNormalizer exampleWeight label

/-- The unit-interval integral of the V-shaped source density kernel. -/
theorem adaBoostR_integral_abs_sub
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (∫ y, |y - a| ∂adaBoostRUnitMeasure) =
      a ^ 2 / 2 + (1 - a) ^ 2 / 2 := by
  rw [adaBoostRUnitMeasure, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hleft : (∫ y in (0 : ℝ)..a, |y - a|) = a ^ 2 / 2 := by
    calc
      (∫ y in (0 : ℝ)..a, |y - a|) = ∫ y in Set.Ioc (0 : ℝ) a, |y - a| :=
        intervalIntegral.integral_of_le ha0
      _ = ∫ y in Ι a (0 : ℝ), |y - a| := by rw [Set.uIoc_of_ge ha0]
      _ = a ^ 2 / 2 := by
        have h := integral_pow_abs_sub_uIoc (a := a) (b := (0 : ℝ)) (n := 1)
        norm_num at h
        simpa using h
  have hright : (∫ y in a..(1 : ℝ), |y - a|) = (1 - a) ^ 2 / 2 := by
    calc
      (∫ y in a..(1 : ℝ), |y - a|) = ∫ y in Set.Ioc a (1 : ℝ), |y - a| :=
        intervalIntegral.integral_of_le ha1
      _ = ∫ y in Ι a (1 : ℝ), |y - a| := by rw [Set.uIoc_of_le ha1]
      _ = (1 - a) ^ 2 / 2 := by
        have h := integral_pow_abs_sub_uIoc (a := a) (b := (1 : ℝ)) (n := 1)
        norm_num at h
        simpa [abs_of_nonneg (by linarith : (1 : ℝ) - a ≥ 0)] using h
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · rw [hleft, hright]
  · exact (continuous_abs.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  · exact (continuous_abs.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _

/-- The V-shaped source kernel has mass between `1/4` and `1/2` on `[0,1]`. -/
theorem adaBoostR_integral_abs_sub_bounds
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (1 / 4 : ℝ) ≤ ∫ y, |y - a| ∂adaBoostRUnitMeasure ∧
      (∫ y, |y - a| ∂adaBoostRUnitMeasure) ≤ 1 / 2 := by
  rw [adaBoostR_integral_abs_sub a ha0 ha1]
  have hsq : 0 ≤ (a - 1 / 2) ^ 2 := sq_nonneg _
  have hproduct : 0 ≤ a * (1 - a) := mul_nonneg ha0 (by linarith)
  constructor <;> nlinarith

/-- Eq. (25)'s normalizer lies in the source interval `[1/4, 1/2]`. -/
theorem adaBoostR_normalizer_bounds
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) :
    (1 / 4 : ℝ) ≤ adaBoostRNormalizer exampleWeight label ∧
      adaBoostRNormalizer exampleWeight label ≤ 1 / 2 := by
  have hkernel_lower : ∀ sample,
      (1 / 4 : ℝ) ≤ ∫ y, |y - label sample| ∂adaBoostRUnitMeasure := by
    intro sample
    exact (adaBoostR_integral_abs_sub_bounds (label sample)
      (hlabel sample).1 (hlabel sample).2).1
  have hkernel_upper : ∀ sample,
      (∫ y, |y - label sample| ∂adaBoostRUnitMeasure) ≤ 1 / 2 := by
    intro sample
    exact (adaBoostR_integral_abs_sub_bounds (label sample)
      (hlabel sample).1 (hlabel sample).2).2
  unfold adaBoostRNormalizer
  constructor
  · calc
      (1 / 4 : ℝ) = ∑ sample, exampleWeight sample * (1 / 4) := by
        rw [← Finset.sum_mul, hexample_total]
        ring
      _ ≤ ∑ sample, exampleWeight sample *
          (∫ y, |y - label sample| ∂adaBoostRUnitMeasure) :=
        Finset.sum_le_sum fun sample _ =>
          mul_le_mul_of_nonneg_left (hkernel_lower sample) (hexample_nonneg sample)
  · calc
      (∑ sample, exampleWeight sample *
          (∫ y, |y - label sample| ∂adaBoostRUnitMeasure)) ≤
          ∑ sample, exampleWeight sample * (1 / 2) :=
        Finset.sum_le_sum fun sample _ =>
          mul_le_mul_of_nonneg_left (hkernel_upper sample) (hexample_nonneg sample)
      _ = (1 / 2 : ℝ) := by
        rw [← Finset.sum_mul, hexample_total]
        ring

/-- The source normalizer is positive under a normalized nonnegative training law. -/
theorem adaBoostR_normalizer_pos
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) :
    0 < adaBoostRNormalizer exampleWeight label := by
  have hbounds := adaBoostR_normalizer_bounds exampleWeight label
    hexample_nonneg hexample_total hlabel
  linarith

/-- Figure 5's initial density has total mass one. -/
theorem adaBoostR_baseDensity_total
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) :
    (∑ sample, ∫ y,
      adaBoostRBaseDensity exampleWeight label sample y ∂adaBoostRUnitMeasure) = 1 := by
  have hnormalizer_pos := adaBoostR_normalizer_pos exampleWeight label
    hexample_nonneg hexample_total hlabel
  have hnormalizer_ne : adaBoostRNormalizer exampleWeight label ≠ 0 :=
    ne_of_gt hnormalizer_pos
  have hbaseIntegral : ∀ sample,
      (∫ y, adaBoostRBaseDensity exampleWeight label sample y ∂adaBoostRUnitMeasure) =
        (exampleWeight sample / adaBoostRNormalizer exampleWeight label) *
          (∫ y, |y - label sample| ∂adaBoostRUnitMeasure) := by
    intro sample
    unfold adaBoostRBaseDensity
    rw [show (fun y => exampleWeight sample * |y - label sample| /
        adaBoostRNormalizer exampleWeight label) = fun y =>
        (exampleWeight sample / adaBoostRNormalizer exampleWeight label) *
          |y - label sample| by
      funext y
      ring]
    rw [MeasureTheory.integral_const_mul]
  simp_rw [hbaseIntegral]
  rw [show (fun sample =>
      (exampleWeight sample / adaBoostRNormalizer exampleWeight label) *
        (∫ y, |y - label sample| ∂adaBoostRUnitMeasure)) =
      fun sample =>
        (exampleWeight sample * (∫ y, |y - label sample| ∂adaBoostRUnitMeasure)) /
          adaBoostRNormalizer exampleWeight label by
    funext sample
    ring]
  rw [← Finset.sum_div]
  change adaBoostRNormalizer exampleWeight label /
    adaBoostRNormalizer exampleWeight label = 1
  exact div_self hnormalizer_ne

/-- The Figure-5 loss region between a true and predicted scalar label. -/
noncomputable def adaBoostRIntervalError (truth prediction y : ℝ) : ℝ := by
  classical
  exact if y ∈ Set.uIcc truth prediction then 1 else 0

/-- The finite weighted squared error of a scalar prediction on the source training law. -/
def adaBoostRMeanSquaredError
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label prediction : Training → ℝ) : ℝ :=
  ∑ sample, exampleWeight sample * (prediction sample - label sample) ^ 2

/-- The initial-density weighted error of the Figure-5 binary reduction. -/
noncomputable def adaBoostRBaseReducedError
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label prediction : Training → ℝ) : ℝ :=
  ∑ sample, ∫ y,
    adaBoostRIntervalError (label sample) (prediction sample) y *
      adaBoostRBaseDensity exampleWeight label sample y ∂adaBoostRUnitMeasure

/-- Integrating the source interval-error indicator recovers half the squared displacement. -/
theorem adaBoostR_intervalIndicator_abs_integral
    (a b : ℝ)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (∫ y, adaBoostRIntervalError a b y * |y - a| ∂adaBoostRUnitMeasure) =
      (b - a) ^ 2 / 2 := by
  classical
  unfold adaBoostRIntervalError
  have hrewrite : (fun y => (if y ∈ Set.uIcc a b then 1 else 0) * |y - a|) =
      (Set.uIcc a b).indicator (fun y => |y - a|) := by
    funext y
    by_cases hy : y ∈ Set.uIcc a b <;> simp [hy]
  rw [hrewrite]
  rw [adaBoostRUnitMeasure, MeasureTheory.integral_indicator measurableSet_uIcc,
    Measure.restrict_restrict_of_subset (Set.uIcc_subset_Icc ha hb)]
  rw [Set.uIcc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  have h := integral_pow_abs_sub_uIoc (a := a) (b := b) (n := 1)
  norm_num at h
  simpa [Set.uIoc] using h

/-- One source example contributes its squared residual divided by `2 Z`. -/
theorem adaBoostR_baseDensity_intervalError_integral
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label prediction : Training → ℝ)
    (sample : Training)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hprediction : ∀ sample, 0 ≤ prediction sample ∧ prediction sample ≤ 1) :
    (∫ y,
      adaBoostRIntervalError (label sample) (prediction sample) y *
        adaBoostRBaseDensity exampleWeight label sample y ∂adaBoostRUnitMeasure) =
      exampleWeight sample * (prediction sample - label sample) ^ 2 /
        (2 * adaBoostRNormalizer exampleWeight label) := by
  rw [show (fun y =>
      adaBoostRIntervalError (label sample) (prediction sample) y *
        adaBoostRBaseDensity exampleWeight label sample y) = fun y =>
      (exampleWeight sample / adaBoostRNormalizer exampleWeight label) *
        (adaBoostRIntervalError (label sample) (prediction sample) y *
          |y - label sample|) by
    funext y
    unfold adaBoostRBaseDensity
    ring]
  rw [MeasureTheory.integral_const_mul,
    adaBoostR_intervalIndicator_abs_integral (label sample) (prediction sample)
      ⟨(hlabel sample).1, (hlabel sample).2⟩
      ⟨(hprediction sample).1, (hprediction sample).2⟩]
  ring

/-- Eq. (25): reduced binary error is source MSE divided by `2 Z`. -/
theorem adaBoostR_baseReducedError_eq_meanSquaredError_div_two_mul_normalizer
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label prediction : Training → ℝ)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hprediction : ∀ sample, 0 ≤ prediction sample ∧ prediction sample ≤ 1) :
    adaBoostRBaseReducedError exampleWeight label prediction =
      adaBoostRMeanSquaredError exampleWeight label prediction /
        (2 * adaBoostRNormalizer exampleWeight label) := by
  unfold adaBoostRBaseReducedError adaBoostRMeanSquaredError
  have hsample : ∀ sample,
      (∫ y,
        adaBoostRIntervalError (label sample) (prediction sample) y *
          adaBoostRBaseDensity exampleWeight label sample y ∂adaBoostRUnitMeasure) =
        exampleWeight sample * (prediction sample - label sample) ^ 2 /
          (2 * adaBoostRNormalizer exampleWeight label) := by
    intro sample
    exact adaBoostR_baseDensity_intervalError_integral exampleWeight label prediction sample
      hlabel hprediction
  simp_rw [hsample]
  rw [← Finset.sum_div]

/-- Total unnormalized mass of a Figure-5 density on the reduced space. -/
noncomputable def adaBoostRDensityTotal
    {Training : Type*} [Fintype Training]
    (weight : Training → ℝ → ℝ) : ℝ :=
  ∑ sample, ∫ y, weight sample y ∂adaBoostRUnitMeasure

/-- A nonnegative, integrable, positive-mass density over the reduced space. -/
structure AdaBoostRDensityState (Training : Type*) [Fintype Training] where
  weight : Training → ℝ → ℝ
  integrable : ∀ sample, Integrable (weight sample) adaBoostRUnitMeasure
  nonneg : ∀ sample y, 0 ≤ weight sample y
  total_pos : 0 < adaBoostRDensityTotal weight

/-- Figure-5's normalized initial density as a concrete reduced-space state. -/
noncomputable def adaBoostRBaseState
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1) :
    AdaBoostRDensityState Training :=
  { weight := adaBoostRBaseDensity exampleWeight label
    integrable := by
      intro sample
      have habs : Integrable (fun y => |y - label sample|) adaBoostRUnitMeasure := by
        unfold adaBoostRUnitMeasure
        change IntegrableOn (fun y => |y - label sample|) (Set.Icc (0 : ℝ) 1) volume
        exact (continuous_abs.comp (continuous_id.sub continuous_const)).continuousOn
          |>.integrableOn_compact isCompact_Icc
      rw [show adaBoostRBaseDensity exampleWeight label sample = fun y =>
          (exampleWeight sample / adaBoostRNormalizer exampleWeight label) *
            |y - label sample| by
        funext y
        unfold adaBoostRBaseDensity
        ring]
      exact habs.const_mul _
    nonneg := by
      intro sample y
      unfold adaBoostRBaseDensity
      exact div_nonneg
        (mul_nonneg (hexample_nonneg sample) (abs_nonneg _))
        (adaBoostR_normalizer_pos exampleWeight label
          hexample_nonneg hexample_total hlabel).le
    total_pos := by
      unfold adaBoostRDensityTotal
      rw [adaBoostR_baseDensity_total exampleWeight label
        hexample_nonneg hexample_total hlabel]
      norm_num }

/-- Figure-5's current reduced binary error after normalizing a density. -/
noncomputable def adaBoostRReducedError
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ) : ℝ :=
  (∑ sample, ∫ y,
    adaBoostRIntervalError (label sample) (hypothesis sample) y *
      state.weight sample y ∂adaBoostRUnitMeasure) /
    adaBoostRDensityTotal state.weight

/-- The literal Figure-5 update: keep weight on the loss interval and multiply it by `β` elsewhere. -/
noncomputable def adaBoostRStepWeight
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ) (error : ℝ) : Training → ℝ → ℝ := by
  classical
  exact fun sample y =>
    if y ∈ Set.uIcc (label sample) (hypothesis sample) then state.weight sample y
    else adaBoostDiscount error * state.weight sample y

/-- Each Figure-5 update remains integrable on the source label interval. -/
theorem adaBoostRStepWeight_integrable
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ) (error : ℝ) (sample : Training) :
    Integrable (adaBoostRStepWeight state label hypothesis error sample) adaBoostRUnitMeasure := by
  classical
  let S : Set ℝ := Set.uIcc (label sample) (hypothesis sample)
  have hindicator : Integrable (S.indicator (state.weight sample)) adaBoostRUnitMeasure :=
    state.integrable sample |>.integrableOn.integrable_indicator measurableSet_uIcc
  have hrewrite : adaBoostRStepWeight state label hypothesis error sample = fun y =>
      adaBoostDiscount error * state.weight sample y +
        (1 - adaBoostDiscount error) * S.indicator (state.weight sample) y := by
    funext y
    unfold adaBoostRStepWeight
    dsimp only [S]
    by_cases hy : y ∈ Set.uIcc (label sample) (hypothesis sample)
    · simp [hy]
      ring
    · simp [hy]
  rw [hrewrite]
  exact ((state.integrable sample).const_mul (adaBoostDiscount error)).add
    (hindicator.const_mul (1 - adaBoostDiscount error))

/-- A literal Figure-5 update preserves nonnegative density values. -/
theorem adaBoostRStepWeight_nonneg
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ) (error : ℝ)
    (herror : 0 < error ∧ error < 1)
    (sample : Training) (y : ℝ) :
    0 ≤ adaBoostRStepWeight state label hypothesis error sample y := by
  classical
  unfold adaBoostRStepWeight
  split_ifs with hy
  · exact state.nonneg sample y
  · exact mul_nonneg (by
      unfold adaBoostDiscount
      exact (div_pos herror.1 (sub_pos.mpr herror.2)).le) (state.nonneg sample y)

/-- The exact one-step density integral identity used in the AdaBoost.R potential calculation. -/
theorem adaBoostRStepWeight_integral
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ) (error : ℝ) (sample : Training) :
    (∫ y, adaBoostRStepWeight state label hypothesis error sample y ∂adaBoostRUnitMeasure) =
      adaBoostDiscount error *
        (∫ y, state.weight sample y ∂adaBoostRUnitMeasure) +
      (1 - adaBoostDiscount error) *
        (∫ y, adaBoostRIntervalError (label sample) (hypothesis sample) y *
          state.weight sample y ∂adaBoostRUnitMeasure) := by
  classical
  let S : Set ℝ := Set.uIcc (label sample) (hypothesis sample)
  have hindicator : Integrable (S.indicator (state.weight sample)) adaBoostRUnitMeasure :=
    state.integrable sample |>.integrableOn.integrable_indicator measurableSet_uIcc
  have herror_indicator :
      (fun y => adaBoostRIntervalError (label sample) (hypothesis sample) y *
        state.weight sample y) = S.indicator (state.weight sample) := by
    funext y
    unfold adaBoostRIntervalError
    dsimp only [S]
    by_cases hy : y ∈ Set.uIcc (label sample) (hypothesis sample) <;> simp [hy]
  have hrewrite : adaBoostRStepWeight state label hypothesis error sample = fun y =>
      adaBoostDiscount error * state.weight sample y +
        (1 - adaBoostDiscount error) * S.indicator (state.weight sample) y := by
    funext y
    unfold adaBoostRStepWeight
    dsimp only [S]
    by_cases hy : y ∈ Set.uIcc (label sample) (hypothesis sample)
    · simp [hy]
      ring
    · simp [hy]
  rw [hrewrite, MeasureTheory.integral_add
    ((state.integrable sample).const_mul (adaBoostDiscount error))
    (hindicator.const_mul (1 - adaBoostDiscount error)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    herror_indicator]

/-- Errors at most one half make the source discount no larger than one. -/
theorem adaBoostR_discount_le_one
    {error : ℝ} (herror : 0 < error ∧ error ≤ 1 / 2) :
    adaBoostDiscount error ≤ 1 := by
  unfold adaBoostDiscount
  have hdenom : 0 < 1 - error := by linarith
  apply (div_le_iff₀ hdenom).mpr
  linarith

/-- One concrete, well-defined Figure-5 update of a reduced density. -/
noncomputable def adaBoostRStep
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ)
    (herror : 0 < adaBoostRReducedError state label hypothesis ∧
      adaBoostRReducedError state label hypothesis ≤ 1 / 2) :
    AdaBoostRDensityState Training :=
  { weight := adaBoostRStepWeight state label hypothesis
      (adaBoostRReducedError state label hypothesis)
    integrable := fun sample =>
      adaBoostRStepWeight_integrable state label hypothesis
        (adaBoostRReducedError state label hypothesis) sample
    nonneg := fun sample y =>
      adaBoostRStepWeight_nonneg state label hypothesis
        (adaBoostRReducedError state label hypothesis)
        ⟨herror.1, lt_of_le_of_lt herror.2 (by norm_num)⟩ sample y
    total_pos := by
      let error := adaBoostRReducedError state label hypothesis
      let beta := adaBoostDiscount error
      have hbeta_pos : 0 < beta := by
        unfold beta adaBoostDiscount
        exact div_pos herror.1 (by linarith)
      have hbeta_le_one : beta ≤ 1 := by
        unfold beta
        exact adaBoostR_discount_le_one herror
      have hpoint : ∀ sample y,
          beta * state.weight sample y ≤
            adaBoostRStepWeight state label hypothesis error sample y := by
        intro sample y
        unfold adaBoostRStepWeight
        dsimp only [beta]
        classical
        split_ifs with hy
        · nlinarith [state.nonneg sample y]
        · rfl
      have hlower : beta * adaBoostRDensityTotal state.weight ≤
          adaBoostRDensityTotal (adaBoostRStepWeight state label hypothesis error) := by
        unfold adaBoostRDensityTotal
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro sample _
        rw [← MeasureTheory.integral_const_mul]
        exact MeasureTheory.integral_mono
          ((state.integrable sample).const_mul beta)
          (adaBoostRStepWeight_integrable state label hypothesis error sample)
          (hpoint sample)
      exact lt_of_lt_of_le (mul_pos hbeta_pos state.total_pos) hlower }

/-- Eq. (15)'s exact continuous one-round `2 ε` mass contraction for Figure 5. -/
theorem adaBoostRStep_total_eq_twice_error
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label hypothesis : Training → ℝ)
    (herror : 0 < adaBoostRReducedError state label hypothesis ∧
      adaBoostRReducedError state label hypothesis ≤ 1 / 2) :
    adaBoostRDensityTotal (adaBoostRStep state label hypothesis herror).weight =
      adaBoostRDensityTotal state.weight *
        (2 * adaBoostRReducedError state label hypothesis) := by
  let error := adaBoostRReducedError state label hypothesis
  let beta := adaBoostDiscount error
  let total := adaBoostRDensityTotal state.weight
  let numerator := ∑ sample, ∫ y,
    adaBoostRIntervalError (label sample) (hypothesis sample) y *
      state.weight sample y ∂adaBoostRUnitMeasure
  have htotal_pos : 0 < total := state.total_pos
  have htotal_ne : total ≠ 0 := ne_of_gt htotal_pos
  change adaBoostRDensityTotal (adaBoostRStepWeight state label hypothesis error) =
    total * (2 * error)
  calc
    adaBoostRDensityTotal (adaBoostRStepWeight state label hypothesis error) =
        ∑ sample, (
          beta * (∫ y, state.weight sample y ∂adaBoostRUnitMeasure) +
          (1 - beta) * (∫ y,
            adaBoostRIntervalError (label sample) (hypothesis sample) y *
              state.weight sample y ∂adaBoostRUnitMeasure)) := by
      unfold adaBoostRDensityTotal
      apply Finset.sum_congr rfl
      intro sample _
      exact adaBoostRStepWeight_integral state label hypothesis error sample
    _ = beta * total + (1 - beta) * numerator := by
      unfold total numerator
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ = total * (2 * error) := by
      have herror_eq : error = numerator / total := rfl
      have hnumerator : numerator = total * error := by
        have hmul : error * total = numerator :=
          (eq_div_iff htotal_ne).mp herror_eq
        calc
          numerator = error * total := hmul.symm
          _ = total * error := by ring
      have hfactor : beta + (1 - beta) * error = 2 * error := by
        unfold beta adaBoostDiscount
        have herror_lt_one : error < 1 := by
          change adaBoostRReducedError state label hypothesis < 1
          exact lt_of_le_of_lt herror.2 (by norm_num)
        field_simp [show 1 - error ≠ 0 by linarith]
        ring
      rw [hnumerator]
      calc
        beta * total + (1 - beta) * (total * error) =
            total * (beta + (1 - beta) * error) := by ring
        _ = total * (2 * error) := by rw [hfactor]

/-- The recursively recorded domain conditions for a literal Figure-5 run. -/
def AdaBoostRAdmissible
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    List (Training → ℝ) → Prop
  | [] => True
  | hypothesis :: remaining =>
      ∃ herror : 0 < adaBoostRReducedError state label hypothesis ∧
          adaBoostRReducedError state label hypothesis ≤ 1 / 2,
        AdaBoostRAdmissible (adaBoostRStep state label hypothesis herror) label remaining

/-- Execute the concrete Figure-5 density updates for a certified finite run. -/
noncomputable def adaBoostRRun
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → AdaBoostRDensityState Training
  | [], _ => state
  | hypothesis :: remaining, hvalid =>
      adaBoostRRun
        (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
        (Classical.choose_spec hvalid)

/-- Extract the actual normalized Step-3 errors of a certified Figure-5 run. -/
noncomputable def adaBoostRErrors
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → List ℝ
  | [], _ => []
  | hypothesis :: remaining, hvalid =>
      adaBoostRReducedError state label hypothesis ::
        adaBoostRErrors
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- Every recorded Figure-5 error is positive and no larger than one half. -/
theorem adaBoostRErrors_mem_Ioc_half
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    ∀ error ∈ adaBoostRErrors state label hypotheses hvalid,
      0 < error ∧ error ≤ 1 / 2 := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      intro error hmem
      change error ∈ adaBoostRReducedError state label hypothesis ::
        adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest at hmem
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact herror
      · exact ih (adaBoostRStep state label hypothesis herror) hrest error htail

/-- The finite product form of the continuous Figure-5 mass calculation. -/
theorem adaBoostRRun_total_eq_errorFactors
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    adaBoostRDensityTotal (adaBoostRRun state label hypotheses hvalid).weight =
      adaBoostRDensityTotal state.weight *
        ((adaBoostRErrors state label hypotheses hvalid).map fun error => 2 * error).prod := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRRun, adaBoostRErrors]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hstep := adaBoostRStep_total_eq_twice_error state label hypothesis herror
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change adaBoostRDensityTotal
          (adaBoostRRun (adaBoostRStep state label hypothesis herror) label remaining hrest).weight =
        adaBoostRDensityTotal state.weight *
          ((2 * adaBoostRReducedError state label hypothesis) *
            ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
              fun error => 2 * error).prod)
      calc
        adaBoostRDensityTotal
            (adaBoostRRun (adaBoostRStep state label hypothesis herror) label remaining hrest).weight =
            adaBoostRDensityTotal (adaBoostRStep state label hypothesis herror).weight *
              ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
                fun error => 2 * error).prod := htail
        _ = (adaBoostRDensityTotal state.weight *
              (2 * adaBoostRReducedError state label hypothesis)) *
              ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
                fun error => 2 * error).prod := by rw [hstep]
        _ = adaBoostRDensityTotal state.weight *
          ((2 * adaBoostRReducedError state label hypothesis) *
            ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
              fun error => 2 * error).prod) := by ring

/-- The Figure-5 weighted interval error at one reduced-space point. -/
noncomputable def adaBoostRWeightedIntervalError
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → Training → ℝ → ℝ
  | [], _, _, _ => 0
  | hypothesis :: remaining, hvalid, sample, y =>
      adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          adaBoostRIntervalError (label sample) (hypothesis sample) y +
        adaBoostRWeightedIntervalError
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample y

/-- The total Figure-5 vote weight. -/
noncomputable def adaBoostRVoteWeightSum
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → ℝ
  | [], _ => 0
  | hypothesis :: remaining, hvalid =>
      adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
        adaBoostRVoteWeightSum
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The accumulated multiplicative factor of one reduced-space point. -/
noncomputable def adaBoostRSampleWeightFactor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → Training → ℝ → ℝ
  | [], _, _, _ => 1
  | hypothesis :: remaining, hvalid, sample, y =>
      adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^
          (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) *
        adaBoostRSampleWeightFactor
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample y

/-- The logarithm of a reduced point's accumulated Figure-5 weight factor. -/
noncomputable def adaBoostRLogSampleWeightFactor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → Training → ℝ → ℝ
  | [], _, _, _ => 0
  | hypothesis :: remaining, hvalid, sample, y =>
      Real.log (adaBoostDiscount (adaBoostRReducedError state label hypothesis)) *
          (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) +
        adaBoostRLogSampleWeightFactor
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample y

/-- The product of Figure-5's common half-discount factors. -/
noncomputable def adaBoostRHalfDiscountFactor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → ℝ
  | [], _ => 1
  | hypothesis :: remaining, hvalid =>
      adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) *
        adaBoostRHalfDiscountFactor
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid)

/-- The recursive Figure-5 state weight equals its initial density times the pointwise factor. -/
theorem adaBoostRRun_weight
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ) :
    (adaBoostRRun state label hypotheses hvalid).weight sample y =
      state.weight sample y * adaBoostRSampleWeightFactor state label hypotheses hvalid sample y := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRRun, adaBoostRSampleWeightFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change
        (adaBoostRRun (adaBoostRStep state label hypothesis herror) label remaining hrest).weight
            sample y =
          state.weight sample y *
            (adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^
              (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) *
              adaBoostRSampleWeightFactor
                (adaBoostRStep state label hypothesis herror) label remaining hrest sample y)
      rw [htail]
      rw [show (adaBoostRStep state label hypothesis herror).weight sample y =
        adaBoostRStepWeight state label hypothesis
          (adaBoostRReducedError state label hypothesis) sample y by rfl]
      unfold adaBoostRStepWeight
      unfold adaBoostRIntervalError
      classical
      by_cases hy : y ∈ Set.uIcc (label sample) (hypothesis sample)
      · simp [hy]
      · simp [hy]
        ring

/-- A reduced point's multiplicative factor is the exponential of its accumulated log factor. -/
theorem adaBoostRSampleWeightFactor_eq_exp_log
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ) :
    adaBoostRSampleWeightFactor state label hypotheses hvalid sample y =
      Real.exp (adaBoostRLogSampleWeightFactor state label hypotheses hvalid sample y) := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRSampleWeightFactor, adaBoostRLogSampleWeightFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (by linarith)
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change
        adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^
            (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) *
            adaBoostRSampleWeightFactor
              (adaBoostRStep state label hypothesis herror) label remaining hrest sample y =
          Real.exp
            (Real.log (adaBoostDiscount (adaBoostRReducedError state label hypothesis)) *
                (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) +
              adaBoostRLogSampleWeightFactor
                (adaBoostRStep state label hypothesis herror) label remaining hrest sample y)
      rw [Real.rpow_def_of_pos hdiscount, htail, ← Real.exp_add]

/-- The accumulated log factor is weighted interval error minus total vote weight. -/
theorem adaBoostRLogSampleWeightFactor_eq_weightedIntervalError_sub_weightSum
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ) :
    adaBoostRLogSampleWeightFactor state label hypotheses hvalid sample y =
      adaBoostRWeightedIntervalError state label hypotheses hvalid sample y -
        adaBoostRVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRLogSampleWeightFactor, adaBoostRWeightedIntervalError,
      adaBoostRVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change
        Real.log (adaBoostDiscount (adaBoostRReducedError state label hypothesis)) *
            (1 - adaBoostRIntervalError (label sample) (hypothesis sample) y) +
            adaBoostRLogSampleWeightFactor
              (adaBoostRStep state label hypothesis herror) label remaining hrest sample y =
          (adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
              adaBoostRIntervalError (label sample) (hypothesis sample) y +
            adaBoostRWeightedIntervalError
              (adaBoostRStep state label hypothesis herror) label remaining hrest sample y) -
            (adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
              adaBoostRVoteWeightSum
                (adaBoostRStep state label hypothesis herror) label remaining hrest)
      rw [htail]
      simp only [adaBoostVoteWeight, one_div, Real.log_inv]
      ring

/-- The common half-discount product is the exponential of negative half total vote weight. -/
theorem adaBoostRHalfDiscountFactor_eq_exp_neg_half_voteWeightSum
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    adaBoostRHalfDiscountFactor state label hypotheses hvalid =
      Real.exp (-(adaBoostRVoteWeightSum state label hypotheses hvalid) / 2) := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRHalfDiscountFactor, adaBoostRVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (by linarith)
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change
        adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostRHalfDiscountFactor
              (adaBoostRStep state label hypothesis herror) label remaining hrest =
          Real.exp (-(adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
              adaBoostRVoteWeightSum
                (adaBoostRStep state label hypothesis herror) label remaining hrest) / 2)
      rw [Real.rpow_def_of_pos hdiscount, htail, ← Real.exp_add]
      congr 1
      simp only [adaBoostVoteWeight, one_div, Real.log_inv]
      ring

/-- The Figure-5 half-discount product is strictly positive. -/
theorem adaBoostRHalfDiscountFactor_pos
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    0 < adaBoostRHalfDiscountFactor state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRHalfDiscountFactor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (by linarith)
      change 0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) *
        adaBoostRHalfDiscountFactor
          (adaBoostRStep state label hypothesis herror) label remaining hrest
      exact mul_pos (Real.rpow_pos_of_pos hdiscount _)
        (ih (state := adaBoostRStep state label hypothesis herror) hrest)

/-- A point whose weighted interval error reaches the half threshold gets at least the half factor. -/
theorem adaBoostR_halfDiscountFactor_le_sampleWeightFactor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ)
    (hhalf : adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
      adaBoostRWeightedIntervalError state label hypotheses hvalid sample y) :
    adaBoostRHalfDiscountFactor state label hypotheses hvalid ≤
      adaBoostRSampleWeightFactor state label hypotheses hvalid sample y := by
  rw [adaBoostRHalfDiscountFactor_eq_exp_neg_half_voteWeightSum,
    adaBoostRSampleWeightFactor_eq_exp_log]
  apply Real.exp_le_exp.mpr
  rw [adaBoostRLogSampleWeightFactor_eq_weightedIntervalError_sub_weightSum]
  linarith

/-- The unnormalized initial mass of the reduced error region of a scalar final output. -/
noncomputable def adaBoostRFinalIntervalMass
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label finalOutput : Training → ℝ) : ℝ :=
  ∑ sample, ∫ y,
    adaBoostRIntervalError (label sample) (finalOutput sample) y *
      state.weight sample y ∂adaBoostRUnitMeasure

/-- The threshold property of Figure 5's weighted-median output on its regression-error interval. -/
def AdaBoostRWeightedMedianCondition
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (finalOutput : Training → ℝ) : Prop :=
  ∀ sample y,
    y ≠ finalOutput sample →
      adaBoostRIntervalError (label sample) (finalOutput sample) y = 1 →
        adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
          adaBoostRWeightedIntervalError state label hypotheses hvalid sample y

/-- An interval-error density times a state weight is integrable. -/
theorem adaBoostR_intervalError_mul_weight_integrable
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (truth prediction : Training → ℝ) (sample : Training) :
    Integrable (fun y =>
      adaBoostRIntervalError (truth sample) (prediction sample) y * state.weight sample y)
      adaBoostRUnitMeasure := by
  classical
  let S : Set ℝ := Set.uIcc (truth sample) (prediction sample)
  have hrewrite : (fun y =>
      adaBoostRIntervalError (truth sample) (prediction sample) y * state.weight sample y) =
      S.indicator (state.weight sample) := by
    funext y
    unfold adaBoostRIntervalError
    dsimp only [S]
    by_cases hy : y ∈ Set.uIcc (truth sample) (prediction sample) <;> simp [hy]
  rw [hrewrite]
  exact state.integrable sample |>.integrableOn.integrable_indicator measurableSet_uIcc

/-- The source interval-error indicator is exactly zero when it is not one. -/
theorem adaBoostRIntervalError_eq_zero_of_ne_one
    (truth prediction y : ℝ)
    (herror : adaBoostRIntervalError truth prediction y ≠ 1) :
    adaBoostRIntervalError truth prediction y = 0 := by
  classical
  unfold adaBoostRIntervalError at herror ⊢
  by_cases hy : y ∈ Set.uIcc truth prediction
  · exact (herror (by simp [hy])).elim
  · simp [hy]

/-- Eq. (18) integrated over the final regression-error region. -/
theorem adaBoostR_finalIntervalMass_mul_halfDiscountFactor_le_runTotal
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (finalOutput : Training → ℝ)
    (hfinal : AdaBoostRWeightedMedianCondition state label hypotheses hvalid finalOutput) :
    adaBoostRFinalIntervalMass state label finalOutput *
        adaBoostRHalfDiscountFactor state label hypotheses hvalid ≤
      adaBoostRDensityTotal (adaBoostRRun state label hypotheses hvalid).weight := by
  classical
  let halfFactor := adaBoostRHalfDiscountFactor state label hypotheses hvalid
  let finalState := adaBoostRRun state label hypotheses hvalid
  have hpoint : ∀ sample y, y ≠ finalOutput sample →
      adaBoostRIntervalError (label sample) (finalOutput sample) y *
          (state.weight sample y * halfFactor) ≤
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          finalState.weight sample y := by
    intro sample y hy_final
    by_cases herror : adaBoostRIntervalError (label sample) (finalOutput sample) y = 1
    · have hfactor := adaBoostR_halfDiscountFactor_le_sampleWeightFactor
        state label hypotheses hvalid sample y (hfinal sample y hy_final herror)
      have hweight := adaBoostRRun_weight state label hypotheses hvalid sample y
      rw [show finalState.weight sample y =
        (adaBoostRRun state label hypotheses hvalid).weight sample y by rfl, hweight]
      rw [herror]
      simpa [halfFactor, mul_assoc] using
        mul_le_mul_of_nonneg_left hfactor (state.nonneg sample y)
    · have hzero := adaBoostRIntervalError_eq_zero_of_ne_one
        (label sample) (finalOutput sample) y herror
      simp [hzero]
  have hper_sample : ∀ sample,
      (∫ y,
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          (state.weight sample y * halfFactor) ∂adaBoostRUnitMeasure) ≤
        (∫ y,
          adaBoostRIntervalError (label sample) (finalOutput sample) y *
            finalState.weight sample y ∂adaBoostRUnitMeasure) := by
    intro sample
    have hleft_integrable : Integrable (fun y =>
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          (state.weight sample y * halfFactor)) adaBoostRUnitMeasure := by
      rw [show (fun y =>
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          (state.weight sample y * halfFactor)) = fun y =>
        halfFactor * (adaBoostRIntervalError (label sample) (finalOutput sample) y *
          state.weight sample y) by
        funext y
        ring]
      exact (adaBoostR_intervalError_mul_weight_integrable state label finalOutput sample).const_mul
        halfFactor
    have hright_integrable :=
      adaBoostR_intervalError_mul_weight_integrable finalState label finalOutput sample
    apply MeasureTheory.integral_mono_ae hleft_integrable hright_integrable
    have hne : ∀ᵐ y ∂adaBoostRUnitMeasure, y ≠ finalOutput sample := by
      unfold adaBoostRUnitMeasure
      apply ae_restrict_of_ae
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with y hy
    exact hpoint sample y hy
  have hright_le_total : ∀ sample,
      (∫ y,
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          finalState.weight sample y ∂adaBoostRUnitMeasure) ≤
        ∫ y, finalState.weight sample y ∂adaBoostRUnitMeasure := by
    intro sample
    apply MeasureTheory.integral_mono
      (adaBoostR_intervalError_mul_weight_integrable finalState label finalOutput sample)
      (finalState.integrable sample)
    intro y
    change adaBoostRIntervalError (label sample) (finalOutput sample) y *
      finalState.weight sample y ≤ finalState.weight sample y
    by_cases herror : adaBoostRIntervalError (label sample) (finalOutput sample) y = 1
    · simpa [herror]
    · have hzero := adaBoostRIntervalError_eq_zero_of_ne_one
        (label sample) (finalOutput sample) y herror
      rw [hzero]
      simpa using finalState.nonneg sample y
  calc
    adaBoostRFinalIntervalMass state label finalOutput * halfFactor =
        ∑ sample,
          ∫ y, adaBoostRIntervalError (label sample) (finalOutput sample) y *
            (state.weight sample y * halfFactor) ∂adaBoostRUnitMeasure := by
      unfold adaBoostRFinalIntervalMass
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro sample _
      rw [show (fun y =>
        adaBoostRIntervalError (label sample) (finalOutput sample) y *
          (state.weight sample y * halfFactor)) = fun y =>
        halfFactor * (adaBoostRIntervalError (label sample) (finalOutput sample) y *
          state.weight sample y) by
        funext y
        ring]
      rw [MeasureTheory.integral_const_mul]
      ring
    _ ≤ ∑ sample,
        ∫ y, adaBoostRIntervalError (label sample) (finalOutput sample) y *
          finalState.weight sample y ∂adaBoostRUnitMeasure :=
      Finset.sum_le_sum fun sample _ => hper_sample sample
    _ ≤ ∑ sample, ∫ y, finalState.weight sample y ∂adaBoostRUnitMeasure :=
      Finset.sum_le_sum fun sample _ => hright_le_total sample
    _ = adaBoostRDensityTotal finalState.weight := rfl

/-- The product displayed in Freund--Schapire's Theorem 12. -/
noncomputable def adaBoostRTheorem12Factor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) : ℝ :=
  ((adaBoostRErrors state label hypotheses hvalid).map fun error =>
    2 * Real.sqrt (error * (1 - error))).prod

/-- Cancelling the common half-discount factors gives Theorem 12's product. -/
theorem adaBoostRErrorFactors_div_halfDiscountFactor_eq_theorem12Factor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    ((adaBoostRErrors state label hypotheses hvalid).map fun error => 2 * error).prod /
        adaBoostRHalfDiscountFactor state label hypotheses hvalid =
      adaBoostRTheorem12Factor state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRErrors, adaBoostRHalfDiscountFactor, adaBoostRTheorem12Factor]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hdiscount : 0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) := by
        unfold adaBoostDiscount
        exact div_pos herror.1 (by linarith)
      have hhead_half_pos :
          0 < adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) :=
        Real.rpow_pos_of_pos hdiscount _
      have htail_half_pos :
          0 < adaBoostRHalfDiscountFactor
            (adaBoostRStep state label hypothesis herror) label remaining hrest :=
        adaBoostRHalfDiscountFactor_pos
          (adaBoostRStep state label hypothesis herror) label remaining hrest
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      change
        ((2 * adaBoostRReducedError state label hypothesis) *
          ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
            fun error => 2 * error).prod) /
          (adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostRHalfDiscountFactor
              (adaBoostRStep state label hypothesis herror) label remaining hrest) =
          2 * Real.sqrt
            (adaBoostRReducedError state label hypothesis *
              (1 - adaBoostRReducedError state label hypothesis)) *
            adaBoostRTheorem12Factor
              (adaBoostRStep state label hypothesis herror) label remaining hrest
      calc
        ((2 * adaBoostRReducedError state label hypothesis) *
          ((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
            fun error => 2 * error).prod) /
          (adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2) *
            adaBoostRHalfDiscountFactor
              (adaBoostRStep state label hypothesis herror) label remaining hrest) =
            ((2 * adaBoostRReducedError state label hypothesis) /
              adaBoostDiscount (adaBoostRReducedError state label hypothesis) ^ ((1 : ℝ) / 2)) *
              (((adaBoostRErrors (adaBoostRStep state label hypothesis herror) label remaining hrest).map
                fun error => 2 * error).prod /
                adaBoostRHalfDiscountFactor
                  (adaBoostRStep state label hypothesis herror) label remaining hrest) := by
          field_simp [hhead_half_pos.ne', htail_half_pos.ne']
        _ = 2 * Real.sqrt
            (adaBoostRReducedError state label hypothesis *
              (1 - adaBoostRReducedError state label hypothesis)) *
            adaBoostRTheorem12Factor
              (adaBoostRStep state label hypothesis herror) label remaining hrest := by
          rw [adaBoost_twice_error_div_half_discount_eq_source_factor
            ⟨herror.1, lt_of_le_of_lt herror.2 (by norm_num)⟩, htail]

/-- A weighted-median output has final interval mass at most the source product times initial mass. -/
theorem adaBoostR_finalIntervalMass_le_initialTotal_mul_theorem12Factor
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (finalOutput : Training → ℝ)
    (hfinal : AdaBoostRWeightedMedianCondition state label hypotheses hvalid finalOutput) :
    adaBoostRFinalIntervalMass state label finalOutput ≤
      adaBoostRDensityTotal state.weight *
        adaBoostRTheorem12Factor state label hypotheses hvalid := by
  have hhalf_pos := adaBoostRHalfDiscountFactor_pos state label hypotheses hvalid
  have hlower := adaBoostR_finalIntervalMass_mul_halfDiscountFactor_le_runTotal
    state label hypotheses hvalid finalOutput hfinal
  have hupper := adaBoostRRun_total_eq_errorFactors state label hypotheses hvalid
  have hcombined :
      adaBoostRFinalIntervalMass state label finalOutput *
          adaBoostRHalfDiscountFactor state label hypotheses hvalid ≤
        adaBoostRDensityTotal state.weight *
          ((adaBoostRErrors state label hypotheses hvalid).map fun error => 2 * error).prod :=
    hlower.trans_eq hupper
  calc
    adaBoostRFinalIntervalMass state label finalOutput ≤
        (adaBoostRDensityTotal state.weight *
          ((adaBoostRErrors state label hypotheses hvalid).map fun error => 2 * error).prod) /
          adaBoostRHalfDiscountFactor state label hypotheses hvalid :=
      (le_div_iff₀ hhalf_pos).mpr hcombined
    _ = adaBoostRDensityTotal state.weight *
        (((adaBoostRErrors state label hypotheses hvalid).map fun error => 2 * error).prod /
          adaBoostRHalfDiscountFactor state label hypotheses hvalid) := by
      field_simp [hhalf_pos.ne']
    _ = adaBoostRDensityTotal state.weight *
        adaBoostRTheorem12Factor state label hypotheses hvalid := by
      rw [adaBoostRErrorFactors_div_halfDiscountFactor_eq_theorem12Factor]

/-- Every final interval mass of a nonnegative density is nonnegative. -/
theorem adaBoostRFinalIntervalMass_nonneg
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training)
    (label finalOutput : Training → ℝ) :
    0 ≤ adaBoostRFinalIntervalMass state label finalOutput := by
  unfold adaBoostRFinalIntervalMass
  apply Finset.sum_nonneg
  intro sample _
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [] with y
  by_cases herror : adaBoostRIntervalError (label sample) (finalOutput sample) y = 1
  · rw [herror]
    simpa using state.nonneg sample y
  · have hzero := adaBoostRIntervalError_eq_zero_of_ne_one
      (label sample) (finalOutput sample) y herror
    rw [hzero]
    norm_num

/-- Theorem 12 after the concrete Eq. (25) source reduction, under its weighted-median condition. -/
theorem adaBoostR_meanSquaredError_le_theorem12Factor_of_weightedMedianCondition
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible (adaBoostRBaseState exampleWeight label
      hexample_nonneg hexample_total hlabel) label hypotheses)
    (finalOutput : Training → ℝ)
    (hfinalOutput : ∀ sample, 0 ≤ finalOutput sample ∧ finalOutput sample ≤ 1)
    (hfinal : AdaBoostRWeightedMedianCondition
      (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
      label hypotheses hvalid finalOutput) :
    adaBoostRMeanSquaredError exampleWeight label finalOutput ≤
      adaBoostRTheorem12Factor
        (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
        label hypotheses hvalid := by
  let baseState := adaBoostRBaseState exampleWeight label
    hexample_nonneg hexample_total hlabel
  have hbase_total : adaBoostRDensityTotal baseState.weight = 1 := by
    unfold baseState adaBoostRDensityTotal
    exact adaBoostR_baseDensity_total exampleWeight label
      hexample_nonneg hexample_total hlabel
  have hmass_le := adaBoostR_finalIntervalMass_le_initialTotal_mul_theorem12Factor
    baseState label hypotheses hvalid finalOutput hfinal
  have hreduced_le : adaBoostRBaseReducedError exampleWeight label finalOutput ≤
      adaBoostRTheorem12Factor baseState label hypotheses hvalid := by
    change adaBoostRFinalIntervalMass baseState label finalOutput ≤ _ at hmass_le
    rw [hbase_total] at hmass_le
    simpa [adaBoostRBaseReducedError, baseState] using hmass_le
  have hbridge := adaBoostR_baseReducedError_eq_meanSquaredError_div_two_mul_normalizer
    exampleWeight label finalOutput hlabel hfinalOutput
  have hnormalizer_pos := adaBoostR_normalizer_pos exampleWeight label
    hexample_nonneg hexample_total hlabel
  have hnormalizer_upper := (adaBoostR_normalizer_bounds exampleWeight label
    hexample_nonneg hexample_total hlabel).2
  have hmass_nonneg : 0 ≤ adaBoostRBaseReducedError exampleWeight label finalOutput := by
    change 0 ≤ adaBoostRFinalIntervalMass baseState label finalOutput
    exact adaBoostRFinalIntervalMass_nonneg baseState label finalOutput
  have hmse_eq : adaBoostRMeanSquaredError exampleWeight label finalOutput =
      (2 * adaBoostRNormalizer exampleWeight label) *
        adaBoostRBaseReducedError exampleWeight label finalOutput := by
    have hmul : adaBoostRBaseReducedError exampleWeight label finalOutput *
        (2 * adaBoostRNormalizer exampleWeight label) =
        adaBoostRMeanSquaredError exampleWeight label finalOutput :=
      (eq_div_iff (by positivity : 2 * adaBoostRNormalizer exampleWeight label ≠ 0)).mp hbridge
    calc
      adaBoostRMeanSquaredError exampleWeight label finalOutput =
          adaBoostRBaseReducedError exampleWeight label finalOutput *
            (2 * adaBoostRNormalizer exampleWeight label) := hmul.symm
      _ = (2 * adaBoostRNormalizer exampleWeight label) *
          adaBoostRBaseReducedError exampleWeight label finalOutput := by ring
  calc
    adaBoostRMeanSquaredError exampleWeight label finalOutput =
        (2 * adaBoostRNormalizer exampleWeight label) *
          adaBoostRBaseReducedError exampleWeight label finalOutput := hmse_eq
    _ ≤ 1 * adaBoostRBaseReducedError exampleWeight label finalOutput :=
      mul_le_mul_of_nonneg_right (by linarith) hmass_nonneg
    _ = adaBoostRBaseReducedError exampleWeight label finalOutput := by ring
    _ ≤ adaBoostRTheorem12Factor baseState label hypotheses hvalid := hreduced_le

/-- The weighted binary vote of Figure 5's thresholded weak regressors. -/
noncomputable def adaBoostRVote
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ) :
    (hypotheses : List (Training → ℝ)) →
      AdaBoostRAdmissible state label hypotheses → Training → ℝ → ℝ
  | [], _, _, _ => 0
  | hypothesis :: remaining, hvalid, sample, y =>
      adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ y then 1 else 0) +
        adaBoostRVote
          (adaBoostRStep state label hypothesis (Classical.choose hvalid)) label remaining
          (Classical.choose_spec hvalid) sample y

/-- A Figure-5 vote weight is nonnegative on the source weak-learning domain. -/
theorem adaBoostRVoteWeight_nonneg
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    0 ≤ adaBoostRVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      change 0 ≤ adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
        adaBoostRVoteWeightSum
          (adaBoostRStep state label hypothesis herror) label remaining hrest
      exact add_nonneg
        (adaBoostVoteWeight_nonneg_of_error_le_half herror)
        (ih (adaBoostRStep state label hypothesis herror) hrest)

/-- With weak regressors in `[0,1]`, the Figure-5 vote at one is its total weight. -/
theorem adaBoostRVote_one_eq_voteWeightSum
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) :
    adaBoostRVote state label hypotheses hvalid sample 1 =
      adaBoostRVoteWeightSum state label hypotheses hvalid := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVote, adaBoostRVoteWeightSum]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhead : hypothesis sample ≤ 1 :=
        (hhypotheses hypothesis (by simp) sample).2
      have htail_hypotheses : ∀ next ∈ remaining, ∀ other,
          0 ≤ next other ∧ next other ≤ 1 := by
        intro next hnext other
        exact hhypotheses next (by simp [hnext]) other
      have htail := ih (state := adaBoostRStep state label hypothesis herror)
        htail_hypotheses hrest
      change adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ 1 then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample 1 =
        adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
          adaBoostRVoteWeightSum
            (adaBoostRStep state label hypothesis herror) label remaining hrest
      rw [if_pos hhead, htail]
      ring

/-- The finite set of possible Figure-5 weighted-median breakpoints for one training example. -/
noncomputable def adaBoostRMedianCandidates
    {Training : Type*} (hypotheses : List (Training → ℝ)) (sample : Training) : Finset ℝ := by
  classical
  exact insert 0 (insert 1 (hypotheses.map fun hypothesis => hypothesis sample).toFinset)

/-- Candidate breakpoints where the Figure-5 weighted vote reaches its half threshold. -/
noncomputable def adaBoostRGoodMedianCandidates
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) : Finset ℝ := by
  classical
  exact (adaBoostRMedianCandidates hypotheses sample).filter fun y =>
    adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
      adaBoostRVote state label hypotheses hvalid sample y

/-- At least one Figure-5 median candidate reaches the half threshold. -/
theorem adaBoostRGoodMedianCandidates_nonempty
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) :
    (adaBoostRGoodMedianCandidates state label hypotheses hvalid sample).Nonempty := by
  refine ⟨1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · simp [adaBoostRMedianCandidates]
  · rw [adaBoostRVote_one_eq_voteWeightSum state label hypotheses hhypotheses hvalid sample]
    linarith [adaBoostRVoteWeight_nonneg state label hypotheses hvalid]

/-- Figure 5's finite weighted-median output, reduced to the minimum good breakpoint. -/
noncomputable def adaBoostRFinalHypothesis
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses) : Training → ℝ :=
  fun sample => (adaBoostRGoodMedianCandidates state label hypotheses hvalid sample).min'
    (adaBoostRGoodMedianCandidates_nonempty state label hypotheses hhypotheses hvalid sample)

/-- The concrete Figure-5 weighted-median output remains in the source label interval. -/
theorem adaBoostRFinalHypothesis_mem_Icc
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) :
    0 ≤ adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ∧
      adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ≤ 1 := by
  classical
  let good := adaBoostRGoodMedianCandidates state label hypotheses hvalid sample
  have hgood_mem : adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ∈ good := by
    unfold adaBoostRFinalHypothesis
    exact Finset.min'_mem good
      (adaBoostRGoodMedianCandidates_nonempty state label hypotheses hhypotheses hvalid sample)
  have hcandidate_mem :
      adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ∈
        adaBoostRMedianCandidates hypotheses sample :=
    (Finset.mem_filter.mp hgood_mem).1
  simp only [adaBoostRMedianCandidates] at hcandidate_mem
  rcases Finset.mem_insert.mp hcandidate_mem with hzero | hrest
  · rw [hzero]
    norm_num
  rcases Finset.mem_insert.mp hrest with hone | hvalues
  · rw [hone]
    norm_num
  rcases List.mem_toFinset.mp hvalues with hvalues
  rcases List.mem_map.mp hvalues with ⟨hypothesis, hhypothesis_mem, hvalue⟩
  rw [← hvalue]
  exact hhypotheses hypothesis hhypothesis_mem sample

/-- The Figure-5 thresholded vote is monotone in its scalar threshold. -/
theorem adaBoostRVote_mono
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) {y z : ℝ} (hyz : y ≤ z) :
    adaBoostRVote state label hypotheses hvalid sample y ≤
      adaBoostRVote state label hypotheses hvalid sample z := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVote]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      have hweight : 0 ≤ adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) :=
        adaBoostVoteWeight_nonneg_of_error_le_half herror
      change adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ y then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y ≤
        adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ z then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample z
      by_cases hy : hypothesis sample ≤ y
      · have hz : hypothesis sample ≤ z := hy.trans hyz
        simp [hy, hz]
        linarith
      · by_cases hz : hypothesis sample ≤ z
        · simp [hy, hz]
          linarith
        · simp [hy, hz]
          exact htail

/-- If two thresholds select exactly the same weak-regressor values, their Figure-5 votes agree. -/
theorem adaBoostRVote_eq_of_threshold_iff
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y z : ℝ)
    (hthreshold : ∀ hypothesis ∈ hypotheses,
      hypothesis sample ≤ y ↔ hypothesis sample ≤ z) :
    adaBoostRVote state label hypotheses hvalid sample y =
      adaBoostRVote state label hypotheses hvalid sample z := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVote]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have hhead : hypothesis sample ≤ y ↔ hypothesis sample ≤ z :=
        hthreshold hypothesis (by simp)
      have htail_threshold : ∀ next ∈ remaining,
          next sample ≤ y ↔ next sample ≤ z := by
        intro next hnext
        exact hthreshold next (by simp [hnext])
      have htail := ih (state := adaBoostRStep state label hypothesis herror)
        hrest htail_threshold
      change adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ y then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y =
        adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ z then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample z
      rcases hhead with ⟨hyz, hzy⟩
      by_cases hy : hypothesis sample ≤ y
      · simp [hy, hyz hy, htail]
      · have hz : ¬ hypothesis sample ≤ z := fun hz => hy (hzy hz)
        simp [hy, hz, htail]

/-- The finite minimum defining the Figure-5 output is itself a good breakpoint. -/
theorem adaBoostRFinalHypothesis_mem_goodMedianCandidates
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) :
    adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ∈
      adaBoostRGoodMedianCandidates state label hypotheses hvalid sample := by
  unfold adaBoostRFinalHypothesis
  exact Finset.min'_mem _
    (adaBoostRGoodMedianCandidates_nonempty state label hypotheses hhypotheses hvalid sample)

/-- The Figure-5 output is no larger than every good candidate breakpoint. -/
theorem adaBoostRFinalHypothesis_le_of_mem_goodMedianCandidates
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) {y : ℝ}
    (hy : y ∈ adaBoostRGoodMedianCandidates state label hypotheses hvalid sample) :
    adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ≤ y := by
  unfold adaBoostRFinalHypothesis
  exact Finset.min'_le _ y hy

/-- Above the Figure-5 output, the weighted vote reaches its half threshold. -/
theorem adaBoostRVote_half_le_of_finalHypothesis_le
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) {y : ℝ}
    (hy : adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample ≤ y) :
    adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
      adaBoostRVote state label hypotheses hvalid sample y := by
  have hfinal_mem := adaBoostRFinalHypothesis_mem_goodMedianCandidates
    state label hypotheses hhypotheses hvalid sample
  have hfinal_threshold :
      adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
        adaBoostRVote state label hypotheses hvalid sample
          (adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample) :=
    (Finset.mem_filter.mp hfinal_mem).2
  exact hfinal_threshold.trans
    (adaBoostRVote_mono state label hypotheses hvalid sample hy)

/-- Below the Figure-5 output, the weighted vote is strictly below its half threshold. -/
theorem adaBoostRVote_lt_half_of_lt_finalHypothesis
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y < adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample) :
    adaBoostRVote state label hypotheses hvalid sample y <
      adaBoostRVoteWeightSum state label hypotheses hvalid / 2 := by
  classical
  by_contra hnot
  have hhalf : adaBoostRVoteWeightSum state label hypotheses hvalid / 2 ≤
      adaBoostRVote state label hypotheses hvalid sample y := le_of_not_gt hnot
  let candidates := adaBoostRMedianCandidates hypotheses sample
  let lower := candidates.filter fun threshold => threshold ≤ y
  have hzero_candidate : 0 ∈ candidates := by
    simp [candidates, adaBoostRMedianCandidates]
  have hzero_lower : 0 ∈ lower :=
    Finset.mem_filter.mpr ⟨hzero_candidate, hy0⟩
  have hlower_nonempty : lower.Nonempty := ⟨0, hzero_lower⟩
  let cutoff := lower.max' hlower_nonempty
  have hcutoff_lower : cutoff ∈ lower :=
    Finset.max'_mem lower hlower_nonempty
  have hcutoff_candidate : cutoff ∈ candidates :=
    (Finset.mem_filter.mp hcutoff_lower).1
  have hcutoff_le_y : cutoff ≤ y :=
    (Finset.mem_filter.mp hcutoff_lower).2
  have hthreshold : ∀ hypothesis ∈ hypotheses,
      hypothesis sample ≤ y ↔ hypothesis sample ≤ cutoff := by
    intro hypothesis hhypothesis
    constructor
    · intro hvalue_le_y
      have hvalue_candidate : hypothesis sample ∈ candidates := by
        change hypothesis sample ∈ insert 0
          (insert 1 (List.map (fun next => next sample) hypotheses).toFinset)
        apply Finset.mem_insert.mpr
        right
        apply Finset.mem_insert.mpr
        right
        exact List.mem_toFinset.mpr
          (List.mem_map.mpr ⟨hypothesis, hhypothesis, rfl⟩)
      have hvalue_lower : hypothesis sample ∈ lower :=
        Finset.mem_filter.mpr ⟨hvalue_candidate, hvalue_le_y⟩
      exact Finset.le_max' lower (hypothesis sample) hvalue_lower
    · intro hvalue_le_cutoff
      exact hvalue_le_cutoff.trans hcutoff_le_y
  have hvote_eq := adaBoostRVote_eq_of_threshold_iff
    state label hypotheses hvalid sample y cutoff hthreshold
  have hcutoff_good : cutoff ∈
      adaBoostRGoodMedianCandidates state label hypotheses hvalid sample :=
    Finset.mem_filter.mpr ⟨by simpa [candidates] using hcutoff_candidate, by
      rw [← hvote_eq]
      exact hhalf⟩
  have hfinal_le_cutoff := adaBoostRFinalHypothesis_le_of_mem_goodMedianCandidates
    state label hypotheses hhypotheses hvalid sample hcutoff_good
  linarith

/-- Below a true label, every thresholded weak-regressor vote is covered by its interval error. -/
theorem adaBoostRVote_le_weightedIntervalError_of_le_label
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ) (hy : y ≤ label sample) :
    adaBoostRVote state label hypotheses hvalid sample y ≤
      adaBoostRWeightedIntervalError state label hypotheses hvalid sample y := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVote, adaBoostRWeightedIntervalError]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      have hweight : 0 ≤ adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) :=
        adaBoostVoteWeight_nonneg_of_error_le_half herror
      change adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ y then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y ≤
        adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          adaBoostRIntervalError (label sample) (hypothesis sample) y +
          adaBoostRWeightedIntervalError
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y
      by_cases hthreshold : hypothesis sample ≤ y
      · have hinterval : y ∈ Set.uIcc (label sample) (hypothesis sample) :=
          Set.mem_uIcc_of_ge hthreshold hy
        have hinterval : adaBoostRIntervalError (label sample) (hypothesis sample) y = 1 := by
          simp [adaBoostRIntervalError, hinterval]
        simp [hthreshold, hinterval]
        linarith
      · have hinterval_nonneg :
          0 ≤ adaBoostRIntervalError (label sample) (hypothesis sample) y := by
          unfold adaBoostRIntervalError
          split <;> norm_num
        simp [hthreshold]
        linarith [mul_nonneg hweight hinterval_nonneg]

/-- At or above a true label, the complement of the thresholded vote is covered by interval error. -/
theorem adaBoostRVoteWeightSum_le_vote_add_weightedIntervalError_of_label_le
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hvalid : AdaBoostRAdmissible state label hypotheses)
    (sample : Training) (y : ℝ) (hy : label sample ≤ y) :
    adaBoostRVoteWeightSum state label hypotheses hvalid ≤
      adaBoostRVote state label hypotheses hvalid sample y +
        adaBoostRWeightedIntervalError state label hypotheses hvalid sample y := by
  induction hypotheses generalizing state with
  | nil => simp [adaBoostRVoteWeightSum, adaBoostRVote, adaBoostRWeightedIntervalError]
  | cons hypothesis remaining ih =>
      let herror := Classical.choose hvalid
      have hrest : AdaBoostRAdmissible
          (adaBoostRStep state label hypothesis herror) label remaining :=
        Classical.choose_spec hvalid
      have htail := ih (state := adaBoostRStep state label hypothesis herror) hrest
      have hweight : 0 ≤ adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) :=
        adaBoostVoteWeight_nonneg_of_error_le_half herror
      change adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) +
          adaBoostRVoteWeightSum
            (adaBoostRStep state label hypothesis herror) label remaining hrest ≤
        (adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
          (if hypothesis sample ≤ y then 1 else 0) +
          adaBoostRVote
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y) +
          (adaBoostVoteWeight (adaBoostRReducedError state label hypothesis) *
            adaBoostRIntervalError (label sample) (hypothesis sample) y +
          adaBoostRWeightedIntervalError
            (adaBoostRStep state label hypothesis herror) label remaining hrest sample y)
      by_cases hthreshold : hypothesis sample ≤ y
      · have hinterval_nonneg :
          0 ≤ adaBoostRIntervalError (label sample) (hypothesis sample) y := by
          unfold adaBoostRIntervalError
          split <;> norm_num
        simp [hthreshold]
        linarith [mul_nonneg hweight hinterval_nonneg]
      · have hthreshold_lt : y < hypothesis sample := lt_of_not_ge hthreshold
        have hinterval : y ∈ Set.uIcc (label sample) (hypothesis sample) :=
          Set.mem_uIcc_of_le hy hthreshold_lt.le
        have hinterval : adaBoostRIntervalError (label sample) (hypothesis sample) y = 1 := by
          simp [adaBoostRIntervalError, hinterval]
        simp [hthreshold, hinterval]
        linarith

/-- The source weighted-median condition holds for the literal Figure-5 finite output. -/
theorem adaBoostRFinalHypothesis_weightedMedianCondition
    {Training : Type*} [Fintype Training]
    (state : AdaBoostRDensityState Training) (label : Training → ℝ)
    (hypotheses : List (Training → ℝ))
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible state label hypotheses) :
    AdaBoostRWeightedMedianCondition state label hypotheses hvalid
      (adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid) := by
  intro sample y hyne hinterval
  have hmem : y ∈ Set.uIcc (label sample)
      (adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample) := by
    unfold adaBoostRIntervalError at hinterval
    split at hinterval
    · exact ‹y ∈ Set.uIcc (label sample)
        (adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample)›
    · norm_num at hinterval
  rw [Set.mem_uIcc] at hmem
  rcases hmem with hleft | hright
  · have hy_lt_final : y <
        adaBoostRFinalHypothesis state label hypotheses hhypotheses hvalid sample :=
      lt_of_le_of_ne hleft.2 hyne
    have hvote_lt := adaBoostRVote_lt_half_of_lt_finalHypothesis
      state label hypotheses hhypotheses hvalid sample
      ((hlabel sample).1.trans hleft.1) hy_lt_final
    have hcover := adaBoostRVoteWeightSum_le_vote_add_weightedIntervalError_of_label_le
      state label hypotheses hvalid sample y hleft.1
    linarith
  · have hvote_le := adaBoostRVote_half_le_of_finalHypothesis_le
      state label hypotheses hhypotheses hvalid sample hright.1
    have hcover := adaBoostRVote_le_weightedIntervalError_of_le_label
      state label hypotheses hvalid sample y hright.2
    exact hvote_le.trans hcover

/-- Freund--Schapire Theorem 12 for the literal Figure-5 AdaBoost.R output. -/
theorem adaBoostR_meanSquaredError_le_theorem12Factor
    {Training : Type*} [Fintype Training]
    (exampleWeight : Training → ℝ) (label : Training → ℝ)
    (hexample_nonneg : ∀ sample, 0 ≤ exampleWeight sample)
    (hexample_total : ∑ sample, exampleWeight sample = 1)
    (hlabel : ∀ sample, 0 ≤ label sample ∧ label sample ≤ 1)
    (hypotheses : List (Training → ℝ))
    (hhypotheses : ∀ hypothesis ∈ hypotheses, ∀ sample,
      0 ≤ hypothesis sample ∧ hypothesis sample ≤ 1)
    (hvalid : AdaBoostRAdmissible (adaBoostRBaseState exampleWeight label
      hexample_nonneg hexample_total hlabel) label hypotheses) :
    adaBoostRMeanSquaredError exampleWeight label
      (adaBoostRFinalHypothesis
        (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
        label hypotheses hhypotheses hvalid) ≤
      adaBoostRTheorem12Factor
        (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
        label hypotheses hvalid := by
  apply adaBoostR_meanSquaredError_le_theorem12Factor_of_weightedMedianCondition
    exampleWeight label hexample_nonneg hexample_total hlabel hypotheses hhypotheses hvalid
  · exact adaBoostRFinalHypothesis_mem_Icc
      (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
      label hypotheses hhypotheses hvalid
  · exact adaBoostRFinalHypothesis_weightedMedianCondition
      (adaBoostRBaseState exampleWeight label hexample_nonneg hexample_total hlabel)
      label hypotheses hlabel hhypotheses hvalid

end Online
end Learning
end AppliedModelingLib
