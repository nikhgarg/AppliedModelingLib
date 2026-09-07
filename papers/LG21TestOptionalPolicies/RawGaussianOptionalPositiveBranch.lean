import LG21TestOptionalPolicies.ObservedAccessPositiveMass

/-!
# Raw positive-branch PBO bridge for LG21 optional reporting

This support module keeps the positive-mass convention literal.  A no-report
PBO is defined only after a proof that the no-report action has positive mass;
it is the integral of the reported posterior under the normalized restriction
of the actual score law to that action event.

The first lemmas identify an a.e. cutoff action event with the Gaussian lower
tail.  The remaining theorem is intended to derive the exact lower-tail PBO
formula used by `ObservedAccessPositiveMass` without a standalone strategic
consistency field.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory
open Set

/--
The actual positive-mass no-report PBO: an integral over a measurable action
event.  Measurability is part of the source-level conditional-probability
claim, rather than an inference from a Boolean decision function's name.
-/
def lg21OptionalPositiveNoReportPBO
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool)
    (reportedPBO : ℝ → ℝ)
    (_hmeasurable : MeasurableSet {score | reportDecision score = false})
    (_hpositive :
      0 < scoreLaw.toMeasure {score | reportDecision score = false}) : ℝ :=
  ∫ score, reportedPBO score ∂
    lg21NormalizedRestriction scoreLaw.toMeasure
      {score | reportDecision score = false}

/-- An a.e. cutoff report rule identifies the actual no-report action event a.e. -/
theorem lg21_optional_noReport_event_ae_eq_Iio_of_cutoff_ae
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool) (cutoff : ℝ)
    (hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score)) :
    {score | reportDecision score = false} =ᵐ[scoreLaw.toMeasure]
      Set.Iio cutoff := by
  filter_upwards [hcutoff] with score hscore
  apply propext
  change (reportDecision score = false) ↔ score < cutoff
  rw [hscore]
  simp

/-- A Gaussian lower tail is unchanged a.e. by including its cutoff point. -/
theorem lg21_optional_Iio_ae_eq_Iic
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    Set.Iio cutoff =ᵐ[scoreLaw.toMeasure] Set.Iic cutoff := by
  have hne : ∀ᵐ score ∂scoreLaw.toMeasure, score ≠ cutoff := by
    rw [MeasureTheory.ae_iff]
    simpa using scoreLaw.toMeasure_singleton_eq_zero cutoff
  filter_upwards [hne] with score hscore
  apply propext
  change score < cutoff ↔ score ≤ cutoff
  constructor
  · intro hlt
    exact le_of_lt hlt
  · intro hle
    exact lt_of_le_of_ne hle hscore

/-- A Gaussian upper tail is unchanged a.e. by including its cutoff point. -/
theorem lg21_optional_Ioi_ae_eq_Ici
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    Set.Ioi cutoff =ᵐ[scoreLaw.toMeasure] Set.Ici cutoff := by
  have hne : ∀ᵐ score ∂scoreLaw.toMeasure, score ≠ cutoff := by
    rw [MeasureTheory.ae_iff]
    simpa using scoreLaw.toMeasure_singleton_eq_zero cutoff
  filter_upwards [hne] with score hscore
  apply propext
  change cutoff < score ↔ cutoff ≤ score
  constructor
  · intro hlt
    exact le_of_lt hlt
  · intro hle
    exact lt_of_le_of_ne hle (Ne.symm hscore)

/-- An a.e. cutoff report rule identifies no-report with the closed lower tail a.e. -/
theorem lg21_optional_noReport_event_ae_eq_Iic_of_cutoff_ae
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool) (cutoff : ℝ)
    (hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score)) :
    {score | reportDecision score = false} =ᵐ[scoreLaw.toMeasure]
      Set.Iic cutoff :=
  (lg21_optional_noReport_event_ae_eq_Iio_of_cutoff_ae
    scoreLaw reportDecision cutoff hcutoff).trans
      (lg21_optional_Iio_ae_eq_Iic scoreLaw cutoff)

/-- Normalized restriction respects equality of events almost everywhere. -/
theorem lg21_optional_normalizedRestriction_congr_ae
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) {s t : Set Outcome}
    (hset : s =ᵐ[law] t) :
    lg21NormalizedRestriction law s = lg21NormalizedRestriction law t := by
  unfold lg21NormalizedRestriction
  rw [measure_congr hset, Measure.restrict_congr_set hset]

/-- The literal action-event PBO reduces to the Gaussian lower-tail PBO. -/
theorem lg21OptionalPositiveNoReportPBO_eq_lowerTailPBO_of_cutoff_ae
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool)
    (reportedPBO : ℝ → ℝ) (cutoff : ℝ)
    (hmeasurable : MeasurableSet {score | reportDecision score = false})
    (hpositive :
      0 < scoreLaw.toMeasure {score | reportDecision score = false})
    (hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score)) :
    lg21OptionalPositiveNoReportPBO
        scoreLaw reportDecision reportedPBO hmeasurable hpositive =
      ∫ score, reportedPBO score ∂
        lg21NormalizedRestriction scoreLaw.toMeasure (Set.Iio cutoff) := by
  unfold lg21OptionalPositiveNoReportPBO
  rw [lg21_optional_normalizedRestriction_congr_ae]
  exact lg21_optional_noReport_event_ae_eq_Iio_of_cutoff_ae
    scoreLaw reportDecision cutoff hcutoff

/-- The standard Gaussian's unnormalized lower-tail first moment. -/
theorem lg21_optional_standardGaussian_firstMoment_Iic (cutoff : ℝ) :
    (∫ score in Set.Iic cutoff,
      score * standardGaussianDensity score) =
      -standardGaussianDensity cutoff := by
  have h := standardGaussian_firstMoment_affineCDF_integral_Iic 0 0 cutoff
  simp only [zero_mul, zero_add] at h
  rw [standardGaussianCDF_zero_eq_half] at h
  have hrewrite :
      (∫ score in Set.Iic cutoff,
        score * standardGaussianDensity score * (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) *
          ∫ score in Set.Iic cutoff,
            score * standardGaussianDensity score := by
    rw [← integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro score _hscore
    ring
  rw [hrewrite] at h
  ring_nf at h
  linarith

/-- The standard Gaussian lower-tail first moment in measure form. -/
theorem lg21_optional_standardGaussianMeasure_integral_id_Iic (cutoff : ℝ) :
    (∫ score in Set.Iic cutoff, score ∂standardGaussianMeasure) =
      -standardGaussianDensity cutoff := by
  have hgaussian :=
    ProbabilityTheory.integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : NNReal))
      (f := Set.Iic cutoff |>.indicator (fun score : ℝ => score)) (by norm_num)
  have hleft :
      (∫ score,
        (Set.Iic cutoff).indicator (fun score : ℝ => score) score
          ∂standardGaussianMeasure) =
        ∫ score in Set.Iic cutoff, score ∂standardGaussianMeasure := by
    rw [MeasureTheory.integral_indicator measurableSet_Iic]
  have hright :
      (∫ score,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
          (Set.Iic cutoff).indicator (fun score : ℝ => score) score) =
        ∫ score in Set.Iic cutoff,
          score * standardGaussianDensity score := by
    rw [← MeasureTheory.integral_indicator measurableSet_Iic]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with score
    by_cases hscore : score ∈ Set.Iic cutoff
    · simp [Set.indicator, hscore, standardGaussianDensity]
      ring
    · simp [Set.indicator, hscore]
  have hgaussian' :
      (∫ score,
        (Set.Iic cutoff).indicator (fun score : ℝ => score) score
          ∂standardGaussianMeasure) =
        ∫ score,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
            (Set.Iic cutoff).indicator (fun score : ℝ => score) score := by
    simpa [standardGaussianMeasure] using hgaussian
  calc
    (∫ score in Set.Iic cutoff, score ∂standardGaussianMeasure) =
        ∫ score,
          (Set.Iic cutoff).indicator (fun score : ℝ => score) score
            ∂standardGaussianMeasure := hleft.symm
    _ = ∫ score,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
            (Set.Iic cutoff).indicator (fun score : ℝ => score) score := hgaussian'
    _ = ∫ score in Set.Iic cutoff,
          score * standardGaussianDensity score := hright
    _ = -standardGaussianDensity cutoff :=
      lg21_optional_standardGaussian_firstMoment_Iic cutoff

/-- Every `GaussianScaleLaw` is the positive affine image of the standard law. -/
theorem lg21_optional_gaussianScaleLaw_toMeasure_eq_standard_map
    (scoreLaw : GaussianScaleLaw) :
    scoreLaw.toMeasure =
      standardGaussianMeasure.map scoreLaw.unstandardize := by
  symm
  calc
    standardGaussianMeasure.map scoreLaw.unstandardize =
        (standardGaussianMeasure.map (scoreLaw.scale * ·)).map
          (scoreLaw.mean + ·) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (ProbabilityTheory.gaussianReal
          (scoreLaw.scale * 0)
          (NNReal.mk (scoreLaw.scale ^ 2) (sq_nonneg scoreLaw.scale) *
            (1 : NNReal))).map (scoreLaw.mean + ·) := by
      change
        Measure.map (fun x : ℝ => scoreLaw.mean + x)
          (Measure.map (fun x : ℝ => scoreLaw.scale * x)
            (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))) = _
      rw [ProbabilityTheory.gaussianReal_map_const_mul]
    _ = ProbabilityTheory.gaussianReal
          (scoreLaw.scale * 0 + scoreLaw.mean)
          (NNReal.mk (scoreLaw.scale ^ 2) (sq_nonneg scoreLaw.scale) *
            (1 : NNReal)) := by
      rw [ProbabilityTheory.gaussianReal_map_const_add]
    _ = scoreLaw.toMeasure := by
      dsimp [GaussianScaleLaw.toMeasure, GaussianScaleLaw.varianceNNReal]
      congr 1
      · ring
      · apply NNReal.eq
        simp only [mul_one, NNReal.coe_mk]
        change scoreLaw.scale ^ 2 = scoreLaw.scale ^ 2
        rfl

/-- The literal lower-tail conditional mean of a Gaussian score law. -/
def lg21OptionalGaussianLowerTailConditionalMean
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) : ℝ :=
  ∫ score, score ∂
    lg21NormalizedRestriction scoreLaw.toMeasure (Set.Iic cutoff)

/-- The standard Gaussian lower-tail conditional mean is its density/CDF ratio. -/
theorem lg21_optional_standardGaussian_lowerTailConditionalMean_eq
    (cutoff : ℝ) :
    (∫ score, score ∂
      lg21NormalizedRestriction standardGaussianMeasure (Set.Iic cutoff)) =
      -standardGaussianDensity cutoff / standardGaussianCDF cutoff := by
  have hmass :
      standardGaussianMeasure (Set.Iic cutoff) =
        ENNReal.ofReal (standardGaussianCDF cutoff) := by
    simpa [standardGaussianCDF] using
      (ProbabilityTheory.ofReal_cdf standardGaussianMeasure cutoff).symm
  unfold lg21NormalizedRestriction
  rw [MeasureTheory.integral_smul_measure, smul_eq_mul,
    lg21_optional_standardGaussianMeasure_integral_id_Iic, hmass,
    ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (standardGaussianCDF_nonneg cutoff)]
  ring

/-- Equivalent hazard-rate form of the standard Gaussian lower-tail mean. -/
theorem lg21_optional_standardGaussian_lowerTailConditionalMean_eq_neg_hazard
    (cutoff : ℝ) :
    (∫ score, score ∂
      lg21NormalizedRestriction standardGaussianMeasure (Set.Iic cutoff)) =
      -standardGaussianHazard (-cutoff) := by
  rw [lg21_optional_standardGaussian_lowerTailConditionalMean_eq,
    standardGaussianHazard_eq, standardGaussianDensity_neg,
    standardGaussianCDF_neg_eq_one_sub]
  ring

/-- Standardization takes a lower score tail to the corresponding standard tail. -/
theorem lg21_optional_unstandardize_preimage_Iic
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.unstandardize ⁻¹' Set.Iic cutoff =
      Set.Iic (scoreLaw.standardize cutoff) := by
  ext score
  change scoreLaw.mean + scoreLaw.scale * score ≤ cutoff ↔
    score ≤ (cutoff - scoreLaw.mean) / scoreLaw.scale
  constructor
  · intro hscore
    apply (le_div_iff₀ scoreLaw.scale_pos).2
    nlinarith
  · intro hscore
    have hmul := (le_div_iff₀ scoreLaw.scale_pos).1 hscore
    nlinarith

/-- Restricting a Gaussian score law to a lower tail commutes with standardization. -/
theorem lg21_optional_gaussianScaleLaw_lowerTail_restrict_eq_standard_map
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.toMeasure.restrict (Set.Iic cutoff) =
      (standardGaussianMeasure.restrict
        (Set.Iic (scoreLaw.standardize cutoff))).map scoreLaw.unstandardize := by
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  rw [lg21_optional_gaussianScaleLaw_toMeasure_eq_standard_map]
  rw [Measure.restrict_map hunstandardize measurableSet_Iic]
  rw [lg21_optional_unstandardize_preimage_Iic]

/-- Lower-tail masses are preserved by the positive affine standardization map. -/
theorem lg21_optional_gaussianScaleLaw_lowerTail_mass_eq_standard
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.toMeasure (Set.Iic cutoff) =
      standardGaussianMeasure (Set.Iic (scoreLaw.standardize cutoff)) := by
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  rw [lg21_optional_gaussianScaleLaw_toMeasure_eq_standard_map,
    Measure.map_apply hunstandardize measurableSet_Iic,
    lg21_optional_unstandardize_preimage_Iic]

/-- Normalized lower-tail restrictions commute with the Gaussian affine map. -/
theorem lg21_optional_gaussianScaleLaw_normalizedLowerTail_eq_standard_map
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21NormalizedRestriction scoreLaw.toMeasure (Set.Iic cutoff) =
      (lg21NormalizedRestriction standardGaussianMeasure
        (Set.Iic (scoreLaw.standardize cutoff))).map scoreLaw.unstandardize := by
  unfold lg21NormalizedRestriction
  rw [lg21_optional_gaussianScaleLaw_lowerTail_mass_eq_standard,
    lg21_optional_gaussianScaleLaw_lowerTail_restrict_eq_standard_map,
    Measure.map_smul]

/-- Integrability is preserved by conditioning on a finite positive event. -/
theorem lg21_optional_integrable_id_normalizedRestriction
    (law : Measure ℝ) (event : Set ℝ)
    (hpositive : law event ≠ 0)
    (hintegrable : Integrable (fun score : ℝ => score) law) :
    Integrable (fun score : ℝ => score)
      (lg21NormalizedRestriction law event) := by
  unfold lg21NormalizedRestriction
  exact hintegrable.restrict.smul_measure (ENNReal.inv_ne_top.mpr hpositive)

/-- The actual normalized lower-tail mean has the Gaussian hazard formula. -/
theorem lg21_optional_gaussian_lower_tail_conditional_mean_eq
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianLowerTailConditionalMean scoreLaw cutoff =
      scoreLaw.mean - scoreLaw.scale *
        standardGaussianHazard (-(scoreLaw.standardize cutoff)) := by
  let standardCutoff := scoreLaw.standardize cutoff
  have hstandardMass :
      standardGaussianMeasure (Set.Iic standardCutoff) ≠ 0 := by
    have hmass :
        standardGaussianMeasure (Set.Iic standardCutoff) =
          ENNReal.ofReal (standardGaussianCDF standardCutoff) := by
      simpa [standardGaussianCDF] using
        (ProbabilityTheory.ofReal_cdf standardGaussianMeasure standardCutoff).symm
    rw [hmass]
    exact (ENNReal.ofReal_pos.mpr
      (standardGaussianCDF_pos standardCutoff)).ne'
  let standardTailLaw :=
    lg21NormalizedRestriction standardGaussianMeasure
      (Set.Iic standardCutoff)
  letI : IsProbabilityMeasure standardTailLaw :=
    lg21NormalizedRestriction_isProbability
      standardGaussianMeasure (Set.Iic standardCutoff) hstandardMass
      (measure_ne_top _ _)
  have hstandardId :
      Integrable (fun score : ℝ => score) standardGaussianMeasure := by
    change Integrable (fun score : ℝ => score)
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))
    exact
      (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
  have hstandardTailId :
      Integrable (fun score : ℝ => score) standardTailLaw := by
    exact lg21_optional_integrable_id_normalizedRestriction
      standardGaussianMeasure (Set.Iic standardCutoff)
      hstandardMass hstandardId
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  unfold lg21OptionalGaussianLowerTailConditionalMean
  rw [lg21_optional_gaussianScaleLaw_normalizedLowerTail_eq_standard_map]
  change
    (∫ score,
      score ∂(standardTailLaw.map scoreLaw.unstandardize)) = _
  change
    (∫ score,
      id score ∂(standardTailLaw.map scoreLaw.unstandardize)) = _
  rw [MeasureTheory.integral_map hunstandardize.aemeasurable
    aestronglyMeasurable_id]
  change
    (∫ score,
      scoreLaw.mean + scoreLaw.scale * score ∂standardTailLaw) = _
  rw [MeasureTheory.integral_add (integrable_const scoreLaw.mean)
    (hstandardTailId.const_mul scoreLaw.scale),
    MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  change
    scoreLaw.mean + scoreLaw.scale *
        (∫ score, score ∂standardTailLaw) = _
  change
    scoreLaw.mean + scoreLaw.scale *
        (∫ score, score ∂
          lg21NormalizedRestriction standardGaussianMeasure
            (Set.Iic standardCutoff)) = _
  rw [lg21_optional_standardGaussian_lowerTailConditionalMean_eq_neg_hazard]
  dsimp [standardCutoff]
  ring

/-- The literal conditional integral is the library's Gaussian lower-tail mean. -/
theorem lg21_optional_gaussian_lower_tail_conditional_mean_eq_standardGaussianLowerTailMean
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianLowerTailConditionalMean scoreLaw cutoff =
      standardGaussianLowerTailMean scoreLaw cutoff := by
  rw [lg21_optional_gaussian_lower_tail_conditional_mean_eq]
  rfl

/-- Conditioning a nondegenerate Gaussian score below a cutoff lowers its mean. -/
theorem lg21_optional_gaussian_lower_tail_conditional_mean_lt_cutoff
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianLowerTailConditionalMean scoreLaw cutoff < cutoff := by
  rw [lg21_optional_gaussian_lower_tail_conditional_mean_eq_standardGaussianLowerTailMean]
  exact standardGaussianLowerTailMean_lt_threshold scoreLaw cutoff

/-- Conditioning a nondegenerate Gaussian score below a cutoff lowers its mean below the parent. -/
theorem lg21_optional_gaussian_lower_tail_conditional_mean_lt_parent_mean
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianLowerTailConditionalMean scoreLaw cutoff < scoreLaw.mean := by
  rw [lg21_optional_gaussian_lower_tail_conditional_mean_eq]
  have hhazard : 0 < standardGaussianHazard (-(scoreLaw.standardize cutoff)) :=
    standardGaussianHazard_pos _
  nlinarith [scoreLaw.scale_pos]

/--
For a literal positive-mass no-report action, an a.e. cutoff rule makes the
actual PBO of an affine reported payoff equal to that affine payoff evaluated
at the literal conditional Gaussian lower-tail mean.
-/
theorem lg21OptionalPositiveNoReportPBO_eq_affineConditionalMean_of_cutoff_ae
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool)
    (intercept slope cutoff : ℝ)
    (hmeasurable : MeasurableSet {score | reportDecision score = false})
    (hpositive :
      0 < scoreLaw.toMeasure {score | reportDecision score = false})
    (hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score)) :
    lg21OptionalPositiveNoReportPBO scoreLaw reportDecision
      (fun score => intercept + slope * score) hmeasurable hpositive =
      intercept + slope *
        lg21OptionalGaussianLowerTailConditionalMean scoreLaw cutoff := by
  have htailPositive : 0 < scoreLaw.toMeasure (Set.Iic cutoff) := by
    apply lt_of_lt_of_le
      (scoreLaw.toMeasure_Ioc_pos (show cutoff - 1 < cutoff by linarith))
    apply measure_mono
    intro score hscore
    exact hscore.2
  let tailLaw :=
    lg21NormalizedRestriction scoreLaw.toMeasure (Set.Iic cutoff)
  letI : IsProbabilityMeasure tailLaw := by
    exact lg21NormalizedRestriction_isProbability
      scoreLaw.toMeasure (Set.Iic cutoff) (ne_of_gt htailPositive)
      (measure_ne_top _ _)
  have hfullId :
      Integrable (fun score : ℝ => score) scoreLaw.toMeasure := by
    change Integrable (fun score : ℝ => score)
      (ProbabilityTheory.gaussianReal scoreLaw.mean scoreLaw.varianceNNReal)
    exact
      (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
  have htailId : Integrable (fun score : ℝ => score) tailLaw := by
    exact lg21_optional_integrable_id_normalizedRestriction
      scoreLaw.toMeasure (Set.Iic cutoff) (ne_of_gt htailPositive) hfullId
  unfold lg21OptionalPositiveNoReportPBO
  rw [lg21_optional_normalizedRestriction_congr_ae]
  · change
      (∫ score, intercept + slope * score ∂tailLaw) =
        intercept + slope * (∫ score, score ∂tailLaw)
    rw [MeasureTheory.integral_add (integrable_const intercept)
      (htailId.const_mul slope), MeasureTheory.integral_const,
      MeasureTheory.integral_const_mul]
    simp only [MeasureTheory.measureReal_def, measure_univ,
      ENNReal.toReal_one, one_smul]
  · exact lg21_optional_noReport_event_ae_eq_Iic_of_cutoff_ae
      scoreLaw reportDecision cutoff hcutoff

/--
Under a positive-slope affine reported PBO and an a.e. cutoff report rule, the
actual positive-mass no-report PBO lies strictly below the reported PBO at the
cutoff.  This is the direct conditional-expectation route, with no opaque
positive-branch consistency premise.
-/
theorem lg21OptionalPositiveNoReportPBO_lt_affineAtCutoff_of_cutoff_ae
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool)
    (intercept slope cutoff : ℝ) (hslope : 0 < slope)
    (hmeasurable : MeasurableSet {score | reportDecision score = false})
    (hpositive :
      0 < scoreLaw.toMeasure {score | reportDecision score = false})
    (hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score)) :
    lg21OptionalPositiveNoReportPBO scoreLaw reportDecision
      (fun score => intercept + slope * score) hmeasurable hpositive <
      intercept + slope * cutoff := by
  rw [lg21OptionalPositiveNoReportPBO_eq_affineConditionalMean_of_cutoff_ae
    scoreLaw reportDecision intercept slope cutoff hmeasurable hpositive hcutoff]
  exact affine_strictMono intercept hslope
    (lg21_optional_gaussian_lower_tail_conditional_mean_lt_cutoff
      scoreLaw cutoff)

/-! ## Upper-tail conditional means -/

/-- The standard Gaussian's unnormalized upper-tail first moment. -/
theorem lg21_optional_standardGaussian_firstMoment_Ioi (cutoff : ℝ) :
    (∫ score in Set.Ioi cutoff,
      score * standardGaussianDensity score) =
      standardGaussianDensity cutoff := by
  have h := standardGaussian_firstMoment_affineCDF_integral_Ioi 0 0 cutoff
  simp only [zero_mul, zero_add] at h
  rw [standardGaussianCDF_zero_eq_half] at h
  have hrewrite :
      (∫ score in Set.Ioi cutoff,
        score * standardGaussianDensity score * (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) *
          ∫ score in Set.Ioi cutoff,
            score * standardGaussianDensity score := by
    rw [← integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro score _hscore
    ring
  rw [hrewrite] at h
  ring_nf at h
  linarith

/-- The standard Gaussian upper-tail first moment in measure form. -/
theorem lg21_optional_standardGaussianMeasure_integral_id_Ioi (cutoff : ℝ) :
    (∫ score in Set.Ioi cutoff, score ∂standardGaussianMeasure) =
      standardGaussianDensity cutoff := by
  have hgaussian :=
    ProbabilityTheory.integral_gaussianReal_eq_integral_smul
      (μ := (0 : ℝ)) (v := (1 : NNReal))
      (f := Set.Ioi cutoff |>.indicator (fun score : ℝ => score)) (by norm_num)
  have hleft :
      (∫ score,
        (Set.Ioi cutoff).indicator (fun score : ℝ => score) score
          ∂standardGaussianMeasure) =
        ∫ score in Set.Ioi cutoff, score ∂standardGaussianMeasure := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioi]
  have hright :
      (∫ score,
        ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
          (Set.Ioi cutoff).indicator (fun score : ℝ => score) score) =
        ∫ score in Set.Ioi cutoff,
          score * standardGaussianDensity score := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with score
    by_cases hscore : score ∈ Set.Ioi cutoff
    · simp [Set.indicator, hscore, standardGaussianDensity]
      ring
    · simp [Set.indicator, hscore]
  have hgaussian' :
      (∫ score,
        (Set.Ioi cutoff).indicator (fun score : ℝ => score) score
          ∂standardGaussianMeasure) =
        ∫ score,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
            (Set.Ioi cutoff).indicator (fun score : ℝ => score) score := by
    simpa [standardGaussianMeasure] using hgaussian
  calc
    (∫ score in Set.Ioi cutoff, score ∂standardGaussianMeasure) =
        ∫ score,
          (Set.Ioi cutoff).indicator (fun score : ℝ => score) score
            ∂standardGaussianMeasure := hleft.symm
    _ = ∫ score,
          ProbabilityTheory.gaussianPDFReal 0 (1 : NNReal) score •
            (Set.Ioi cutoff).indicator (fun score : ℝ => score) score := hgaussian'
    _ = ∫ score in Set.Ioi cutoff,
          score * standardGaussianDensity score := hright
    _ = standardGaussianDensity cutoff :=
      lg21_optional_standardGaussian_firstMoment_Ioi cutoff

/-- The actual normalized upper-tail mean of a Gaussian score law. -/
def lg21OptionalGaussianUpperTailConditionalMean
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) : ℝ :=
  ∫ score, score ∂
    lg21NormalizedRestriction scoreLaw.toMeasure (Set.Ioi cutoff)

/-- The standard Gaussian upper-tail conditional mean is its density/tail ratio. -/
theorem lg21_optional_standardGaussian_upperTailConditionalMean_eq
    (cutoff : ℝ) :
    (∫ score, score ∂
      lg21NormalizedRestriction standardGaussianMeasure (Set.Ioi cutoff)) =
      standardGaussianDensity cutoff /
        (1 - standardGaussianCDF cutoff) := by
  have hmass :
      standardGaussianMeasure (Set.Ioi cutoff) =
        ENNReal.ofReal (1 - standardGaussianCDF cutoff) := by
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal
      (sub_nonneg.mpr (standardGaussianCDF_le_one cutoff))]
    simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
      (MeasureTheory.probReal_compl_eq_one_sub
        (μ := standardGaussianMeasure) (s := Set.Iic cutoff) measurableSet_Iic)
  unfold lg21NormalizedRestriction
  rw [MeasureTheory.integral_smul_measure, smul_eq_mul,
    lg21_optional_standardGaussianMeasure_integral_id_Ioi, hmass,
    ENNReal.toReal_inv,
    ENNReal.toReal_ofReal
      (sub_nonneg.mpr (standardGaussianCDF_le_one cutoff))]
  ring

/-- Equivalent hazard-rate form of the standard Gaussian upper-tail mean. -/
theorem lg21_optional_standardGaussian_upperTailConditionalMean_eq_hazard
    (cutoff : ℝ) :
    (∫ score, score ∂
      lg21NormalizedRestriction standardGaussianMeasure (Set.Ioi cutoff)) =
      standardGaussianHazard cutoff := by
  rw [lg21_optional_standardGaussian_upperTailConditionalMean_eq,
    standardGaussianHazard_eq]

/-- Standardization takes an upper score tail to the corresponding standard tail. -/
theorem lg21_optional_unstandardize_preimage_Ioi
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.unstandardize ⁻¹' Set.Ioi cutoff =
      Set.Ioi (scoreLaw.standardize cutoff) := by
  ext score
  change cutoff < scoreLaw.mean + scoreLaw.scale * score ↔
    (cutoff - scoreLaw.mean) / scoreLaw.scale < score
  constructor
  · intro hscore
    apply (div_lt_iff₀ scoreLaw.scale_pos).2
    nlinarith
  · intro hscore
    have hmul := (div_lt_iff₀ scoreLaw.scale_pos).1 hscore
    nlinarith

/-- Restricting a Gaussian score law to an upper tail commutes with standardization. -/
theorem lg21_optional_gaussianScaleLaw_upperTail_restrict_eq_standard_map
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.toMeasure.restrict (Set.Ioi cutoff) =
      (standardGaussianMeasure.restrict
        (Set.Ioi (scoreLaw.standardize cutoff))).map scoreLaw.unstandardize := by
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  rw [lg21_optional_gaussianScaleLaw_toMeasure_eq_standard_map]
  rw [Measure.restrict_map hunstandardize measurableSet_Ioi]
  rw [lg21_optional_unstandardize_preimage_Ioi]

/-- Upper-tail masses are preserved by the positive affine standardization map. -/
theorem lg21_optional_gaussianScaleLaw_upperTail_mass_eq_standard
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    scoreLaw.toMeasure (Set.Ioi cutoff) =
      standardGaussianMeasure (Set.Ioi (scoreLaw.standardize cutoff)) := by
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  rw [lg21_optional_gaussianScaleLaw_toMeasure_eq_standard_map,
    Measure.map_apply hunstandardize measurableSet_Ioi,
    lg21_optional_unstandardize_preimage_Ioi]

/-- Normalized upper-tail restrictions commute with the Gaussian affine map. -/
theorem lg21_optional_gaussianScaleLaw_normalizedUpperTail_eq_standard_map
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21NormalizedRestriction scoreLaw.toMeasure (Set.Ioi cutoff) =
      (lg21NormalizedRestriction standardGaussianMeasure
        (Set.Ioi (scoreLaw.standardize cutoff))).map scoreLaw.unstandardize := by
  unfold lg21NormalizedRestriction
  rw [lg21_optional_gaussianScaleLaw_upperTail_mass_eq_standard,
    lg21_optional_gaussianScaleLaw_upperTail_restrict_eq_standard_map,
    Measure.map_smul]

/-- The actual normalized upper-tail mean has the Gaussian hazard formula. -/
theorem lg21_optional_gaussian_upper_tail_conditional_mean_eq
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianUpperTailConditionalMean scoreLaw cutoff =
      scoreLaw.mean + scoreLaw.scale *
        standardGaussianHazard (scoreLaw.standardize cutoff) := by
  let standardCutoff := scoreLaw.standardize cutoff
  have hstandardMass :
      standardGaussianMeasure (Set.Ioi standardCutoff) ≠ 0 := by
    have hmass :
        standardGaussianMeasure (Set.Ioi standardCutoff) =
          ENNReal.ofReal (1 - standardGaussianCDF standardCutoff) := by
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      rw [ENNReal.toReal_ofReal
        (sub_nonneg.mpr (standardGaussianCDF_le_one standardCutoff))]
      simpa [standardGaussianCDF, ProbabilityTheory.cdf_eq_real, compl_Iic] using
        (MeasureTheory.probReal_compl_eq_one_sub
          (μ := standardGaussianMeasure) (s := Set.Iic standardCutoff)
          measurableSet_Iic)
    rw [hmass]
    exact (ENNReal.ofReal_pos.mpr
      (standardGaussianTail_pos standardCutoff)).ne'
  let standardTailLaw :=
    lg21NormalizedRestriction standardGaussianMeasure
      (Set.Ioi standardCutoff)
  letI : IsProbabilityMeasure standardTailLaw :=
    lg21NormalizedRestriction_isProbability
      standardGaussianMeasure (Set.Ioi standardCutoff) hstandardMass
      (measure_ne_top _ _)
  have hstandardId :
      Integrable (fun score : ℝ => score) standardGaussianMeasure := by
    change Integrable (fun score : ℝ => score)
      (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))
    exact
      (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
  have hstandardTailId :
      Integrable (fun score : ℝ => score) standardTailLaw := by
    exact lg21_optional_integrable_id_normalizedRestriction
      standardGaussianMeasure (Set.Ioi standardCutoff)
      hstandardMass hstandardId
  have hunstandardize : Measurable scoreLaw.unstandardize := by
    unfold GaussianScaleLaw.unstandardize
    fun_prop
  unfold lg21OptionalGaussianUpperTailConditionalMean
  rw [lg21_optional_gaussianScaleLaw_normalizedUpperTail_eq_standard_map]
  change
    (∫ score,
      score ∂(standardTailLaw.map scoreLaw.unstandardize)) = _
  change
    (∫ score,
      id score ∂(standardTailLaw.map scoreLaw.unstandardize)) = _
  rw [MeasureTheory.integral_map hunstandardize.aemeasurable
    aestronglyMeasurable_id]
  change
    (∫ score,
      scoreLaw.mean + scoreLaw.scale * score ∂standardTailLaw) = _
  rw [MeasureTheory.integral_add (integrable_const scoreLaw.mean)
    (hstandardTailId.const_mul scoreLaw.scale),
    MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  change
    scoreLaw.mean + scoreLaw.scale *
        (∫ score, score ∂standardTailLaw) = _
  change
    scoreLaw.mean + scoreLaw.scale *
        (∫ score, score ∂
          lg21NormalizedRestriction standardGaussianMeasure
            (Set.Ioi standardCutoff)) = _
  rw [lg21_optional_standardGaussian_upperTailConditionalMean_eq_hazard]

/-- The literal conditional integral is the library's Gaussian upper-tail mean. -/
theorem lg21_optional_gaussian_upper_tail_conditional_mean_eq_normalUpperTailMean
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    lg21OptionalGaussianUpperTailConditionalMean scoreLaw cutoff =
      (standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
        |>.normalUpperTailMean scoreLaw cutoff) := by
  rw [lg21_optional_gaussian_upper_tail_conditional_mean_eq]
  rfl

/-- The upper-tail formula is unchanged by the null cutoff boundary. -/
theorem lg21_optional_gaussian_upper_closed_tail_conditional_mean_eq
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    (∫ score, score ∂
      lg21NormalizedRestriction scoreLaw.toMeasure (Set.Ici cutoff)) =
      scoreLaw.mean + scoreLaw.scale *
        standardGaussianHazard (scoreLaw.standardize cutoff) := by
  have htail :
      lg21NormalizedRestriction scoreLaw.toMeasure (Set.Ici cutoff) =
        lg21NormalizedRestriction scoreLaw.toMeasure (Set.Ioi cutoff) := by
    rw [lg21_optional_normalizedRestriction_congr_ae]
    exact (lg21_optional_Ioi_ae_eq_Ici scoreLaw cutoff).symm
  rw [htail]
  exact lg21_optional_gaussian_upper_tail_conditional_mean_eq scoreLaw cutoff

/-- Conditioning a nondegenerate Gaussian score above a cutoff raises its mean. -/
theorem lg21_optional_gaussian_upper_tail_conditional_mean_gt_cutoff
    (scoreLaw : GaussianScaleLaw) (cutoff : ℝ) :
    cutoff < lg21OptionalGaussianUpperTailConditionalMean scoreLaw cutoff := by
  rw [lg21_optional_gaussian_upper_tail_conditional_mean_eq_normalUpperTailMean]
  exact standardGaussian_normalUpperTailMean_gt_threshold scoreLaw cutoff

end

end LG21TestOptionalPolicies
