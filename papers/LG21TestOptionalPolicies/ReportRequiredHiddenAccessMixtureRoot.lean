import LG21TestOptionalPolicies.HiddenAccessTheorem31RawCandidateActions
import LG21TestOptionalPolicies.ReportRequiredSelectedUpperTailCandidate

/-!
# Literal hidden-access mixture root for report-required LG21 candidates

The report-required candidate leaves a literal public `X = 0` mixture: every
student without access, together with the access students below the candidate
latent-skill cutoff.  This module analyzes that mixture in scalar Gaussian
coordinates and proves the endpoint crossing needed for a cutoff root.

The weights remain explicit throughout.  In particular, no-access students
are never silently removed from the no-report posterior.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open AppliedModelingLib Probability

/--
The scalar no-report posterior mean for the literal hidden-access
report-required cutoff candidate.  `noAccessWeight` is the mass of students
without access, and `accessWeight` is the mass with access; among the latter,
only the Gaussian lower tail remains at `X = 0`.
-/
def lg21ReportRequiredRawNoReportMixturePBO
    (skillLaw : GaussianScaleLaw)
    (noAccessWeight accessWeight cutoff : ℝ) : ℝ :=
  (noAccessWeight + accessWeight *
      standardGaussianCDF (skillLaw.standardize cutoff))⁻¹ *
    (noAccessWeight * skillLaw.mean +
      accessWeight * standardGaussianCDF (skillLaw.standardize cutoff) *
        standardGaussianLowerTailMean skillLaw cutoff)

/-- The open Gaussian lower-tail mass is the standard CDF at the standardized cutoff. -/
theorem lg21GaussianScaleLaw_Iio_mass_toReal_eq_standardGaussianCDF
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ) :
    (skillLaw.toMeasure (Set.Iio cutoff)).toReal =
      standardGaussianCDF (skillLaw.standardize cutoff) := by
  have hIioIic : skillLaw.toMeasure (Set.Iio cutoff) =
      skillLaw.toMeasure (Set.Iic cutoff) := by
    exact measure_congr (lg21_optional_Iio_ae_eq_Iic skillLaw cutoff)
  rw [hIioIic, lg21_optional_gaussianScaleLaw_lowerTail_mass_eq_standard]
  change (standardGaussianMeasure (Set.Iic (skillLaw.standardize cutoff))).toReal =
    standardGaussianCDF (skillLaw.standardize cutoff)
  rw [standardGaussianCDF, ProbabilityTheory.cdf_eq_real]
  rfl

/-- The open-tail normalized Gaussian mean is the concrete lower-tail mean. -/
theorem lg21GaussianScaleLaw_normalizedIio_mean_eq_lowerTailMean
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ) :
    (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)) =
      standardGaussianLowerTailMean skillLaw cutoff := by
  calc
    (∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)) =
      ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction skillLaw.toMeasure (Set.Iic cutoff) := by
          rw [lg21_optional_normalizedRestriction_congr_ae
            skillLaw.toMeasure (lg21_optional_Iio_ae_eq_Iic skillLaw cutoff)]
    _ = standardGaussianLowerTailMean skillLaw cutoff := by
      rw [← lg21_optional_gaussian_lower_tail_conditional_mean_eq_standardGaussianLowerTailMean]
      rfl

/-- Positive no-access mass keeps the scalar raw-mixture denominator nonzero. -/
theorem lg21ReportRequiredRawNoReportMixture_denominator_pos
    (skillLaw : GaussianScaleLaw)
    {noAccessWeight accessWeight cutoff : ℝ}
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight) :
    0 < noAccessWeight + accessWeight *
      standardGaussianCDF (skillLaw.standardize cutoff) := by
  have hcdf : 0 ≤ standardGaussianCDF (skillLaw.standardize cutoff) :=
    standardGaussianCDF_nonneg _
  nlinarith [mul_nonneg haccessWeight hcdf]

/-- The literal scalar raw-mixture no-report PBO is continuous in the cutoff. -/
theorem lg21ReportRequiredRawNoReportMixturePBO_continuous
    (skillLaw : GaussianScaleLaw)
    {noAccessWeight accessWeight : ℝ}
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight) :
    Continuous
      (lg21ReportRequiredRawNoReportMixturePBO
        skillLaw noAccessWeight accessWeight) := by
  let cdf : ℝ → ℝ := fun cutoff =>
    standardGaussianCDF (skillLaw.standardize cutoff)
  let lowerMean : ℝ → ℝ := fun cutoff =>
    standardGaussianLowerTailMean skillLaw cutoff
  have hstandardize : Continuous (fun cutoff : ℝ => skillLaw.standardize cutoff) := by
    unfold GaussianScaleLaw.standardize
    fun_prop
  have hcdf : Continuous cdf := by
    dsimp [cdf]
    exact standardGaussianCDF_continuous.comp hstandardize
  have hlowerMean : Continuous lowerMean := by
    exact standardGaussianLowerTailMean_continuous skillLaw
  have hdenom : Continuous (fun cutoff : ℝ =>
      noAccessWeight + accessWeight * cdf cutoff) := by
    exact continuous_const.add (continuous_const.mul hcdf)
  have hdenomNe : ∀ cutoff : ℝ,
      noAccessWeight + accessWeight * cdf cutoff ≠ 0 := by
    intro cutoff
    exact ne_of_gt
      (lg21ReportRequiredRawNoReportMixture_denominator_pos
        skillLaw hnoAccessWeight haccessWeight)
  have hnumerator : Continuous (fun cutoff : ℝ =>
      noAccessWeight * skillLaw.mean +
        accessWeight * cdf cutoff * lowerMean cutoff) := by
    exact continuous_const.add
      ((continuous_const.mul hcdf).mul hlowerMean)
  change Continuous (fun cutoff : ℝ =>
    (noAccessWeight + accessWeight * cdf cutoff)⁻¹ *
      (noAccessWeight * skillLaw.mean +
        accessWeight * cdf cutoff * lowerMean cutoff))
  exact (hdenom.inv₀ hdenomNe).mul hnumerator

/-- The standard Gaussian CDF times its argument vanishes at `-∞`. -/
theorem lg21_standardGaussianCDF_mul_id_tendsto_atBot_zero :
    Tendsto (fun cutoff : ℝ => standardGaussianCDF cutoff * cutoff)
      atBot (𝓝 0) := by
  have hneg :=
    (standardGaussianCDF_neg_mul_id_tendsto_atTop_zero.comp
      tendsto_neg_atBot_atTop).neg
  simpa using hneg

/--
At a low cutoff, the literal hidden-access no-report mixture returns to the
unselected Gaussian mean.  The potentially unbounded lower-tail conditional
mean is controlled only through its actual vanishing tail mass.
-/
theorem lg21ReportRequiredRawNoReportMixturePBO_tendsto_atBot
    (skillLaw : GaussianScaleLaw)
    {noAccessWeight accessWeight : ℝ}
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight) :
    Tendsto
      (lg21ReportRequiredRawNoReportMixturePBO
        skillLaw noAccessWeight accessWeight)
      atBot (𝓝 skillLaw.mean) := by
  let cdf : ℝ → ℝ := fun cutoff =>
    standardGaussianCDF (skillLaw.standardize cutoff)
  let lowerMean : ℝ → ℝ := fun cutoff =>
    standardGaussianLowerTailMean skillLaw cutoff
  let denominator : ℝ → ℝ := fun cutoff =>
    noAccessWeight + accessWeight * cdf cutoff
  have hstandardizeAtBot : Tendsto
      (fun cutoff : ℝ => skillLaw.standardize cutoff) atBot atBot := by
    have hlinear : Tendsto
        (fun cutoff : ℝ => skillLaw.scale⁻¹ * cutoff +
          (-skillLaw.mean / skillLaw.scale)) atBot atBot :=
      ((Filter.tendsto_const_mul_atBot_of_pos
        (inv_pos.mpr skillLaw.scale_pos)).2 tendsto_id).atBot_add
        tendsto_const_nhds
    convert hlinear using 1
    ext cutoff
    unfold GaussianScaleLaw.standardize
    field_simp [ne_of_gt skillLaw.scale_pos]
    ring
  have hcdfAtBot : Tendsto cdf atBot (𝓝 0) := by
    simpa [cdf] using
      (standardGaussianCDF_tendsto_atBot.comp hstandardizeAtBot)
  have htailGap : Tendsto
      (fun cutoff : ℝ => cdf cutoff * (lowerMean cutoff - cutoff))
      atBot (𝓝 0) := by
    simpa [cdf, lowerMean] using
      (standardGaussian_normalCDF_mul_lowerTailMean_sub_tendsto_atBot skillLaw)
  have hlinearTail : Tendsto
      (fun cutoff : ℝ => cdf cutoff * (cutoff - skillLaw.mean))
      atBot (𝓝 0) := by
    have hstandard :=
      lg21_standardGaussianCDF_mul_id_tendsto_atBot_zero.comp hstandardizeAtBot
    have hscaled := (tendsto_const_nhds (x := skillLaw.scale)).mul hstandard
    have hscaledZero : Tendsto
        (fun cutoff : ℝ => skillLaw.scale *
          (standardGaussianCDF (skillLaw.standardize cutoff) *
            skillLaw.standardize cutoff)) atBot (𝓝 0) := by
      simpa using hscaled
    refine hscaledZero.congr' ?_
    filter_upwards with cutoff
    dsimp [cdf]
    unfold GaussianScaleLaw.standardize
    field_simp [ne_of_gt skillLaw.scale_pos]
  have htailCentered : Tendsto
      (fun cutoff : ℝ => cdf cutoff * (lowerMean cutoff - skillLaw.mean))
      atBot (𝓝 0) := by
    have hsum := htailGap.add hlinearTail
    have hsumZero : Tendsto
        (fun cutoff : ℝ =>
          cdf cutoff * (lowerMean cutoff - cutoff) +
            cdf cutoff * (cutoff - skillLaw.mean))
        atBot (𝓝 0) := by
      simpa using hsum
    refine hsumZero.congr' ?_
    filter_upwards with cutoff
    ring
  have hdenominator : Tendsto denominator atBot (𝓝 noAccessWeight) := by
    dsimp [denominator]
    simpa using
      (tendsto_const_nhds.add
        ((tendsto_const_nhds (x := accessWeight)).mul hcdfAtBot))
  have hnoAccessNe : noAccessWeight ≠ 0 := ne_of_gt hnoAccessWeight
  have hdenominatorInv : Tendsto
      (fun cutoff : ℝ => (denominator cutoff)⁻¹)
      atBot (𝓝 noAccessWeight⁻¹) :=
    hdenominator.inv₀ hnoAccessNe
  have hcorrection : Tendsto
      (fun cutoff : ℝ => (denominator cutoff)⁻¹ *
        (accessWeight * (cdf cutoff *
          (lowerMean cutoff - skillLaw.mean))))
      atBot (𝓝 0) := by
    have hterm := (tendsto_const_nhds (x := accessWeight)).mul htailCentered
    have hproduct := hdenominatorInv.mul hterm
    simpa using hproduct
  have hformula : ∀ cutoff : ℝ,
      lg21ReportRequiredRawNoReportMixturePBO
          skillLaw noAccessWeight accessWeight cutoff =
        skillLaw.mean + (denominator cutoff)⁻¹ *
          (accessWeight * (cdf cutoff *
            (lowerMean cutoff - skillLaw.mean))) := by
    intro cutoff
    have hdenomNe : denominator cutoff ≠ 0 := by
      exact ne_of_gt
        (lg21ReportRequiredRawNoReportMixture_denominator_pos
          skillLaw hnoAccessWeight haccessWeight)
    unfold lg21ReportRequiredRawNoReportMixturePBO
    dsimp [denominator, cdf, lowerMean] at hdenomNe ⊢
    field_simp [hdenomNe]
    ring
  have hsum :=
    (tendsto_const_nhds : Tendsto (fun _cutoff : ℝ => skillLaw.mean)
      atBot (𝓝 skillLaw.mean)).add hcorrection
  have hsumMean : Tendsto
      (fun cutoff : ℝ => skillLaw.mean + (denominator cutoff)⁻¹ *
        (accessWeight * (cdf cutoff *
          (lowerMean cutoff - skillLaw.mean))))
      atBot (𝓝 skillLaw.mean) := by
    simpa using hsum
  refine hsumMean.congr' ?_
  filter_upwards with cutoff
  exact (hformula cutoff).symm

/--
Above the unselected Gaussian mean, the literal raw `X = 0` mixture is below
the displayed cutoff.  The strict inequality is supplied by the retained
positive no-access component; the access lower tail only weakens the mixture
further.
-/
theorem lg21ReportRequiredRawNoReportMixturePBO_lt_cutoff
    (skillLaw : GaussianScaleLaw)
    {noAccessWeight accessWeight cutoff : ℝ}
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight)
    (hmean_lt_cutoff : skillLaw.mean < cutoff) :
    lg21ReportRequiredRawNoReportMixturePBO
      skillLaw noAccessWeight accessWeight cutoff < cutoff := by
  let cdf : ℝ := standardGaussianCDF (skillLaw.standardize cutoff)
  let denominator : ℝ := noAccessWeight + accessWeight * cdf
  let numerator : ℝ := noAccessWeight * skillLaw.mean +
    accessWeight * cdf * standardGaussianLowerTailMean skillLaw cutoff
  have hcdf : 0 ≤ cdf := by
    exact standardGaussianCDF_nonneg _
  have haccessTail : 0 ≤ accessWeight * cdf :=
    mul_nonneg haccessWeight hcdf
  have hdenominator : 0 < denominator := by
    exact lg21ReportRequiredRawNoReportMixture_denominator_pos
      skillLaw hnoAccessWeight haccessWeight
  have hlower : standardGaussianLowerTailMean skillLaw cutoff < cutoff :=
    standardGaussianLowerTailMean_lt_threshold skillLaw cutoff
  have hbaseTerm : noAccessWeight * skillLaw.mean <
      noAccessWeight * cutoff :=
    mul_lt_mul_of_pos_left hmean_lt_cutoff hnoAccessWeight
  have htailTerm : accessWeight * cdf *
      standardGaussianLowerTailMean skillLaw cutoff ≤
      accessWeight * cdf * cutoff := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hlower) haccessTail
  have hnumerator : numerator < cutoff * denominator := by
    dsimp [numerator, denominator]
    calc
      noAccessWeight * skillLaw.mean +
          accessWeight * cdf * standardGaussianLowerTailMean skillLaw cutoff <
          noAccessWeight * cutoff + accessWeight * cdf * cutoff :=
        add_lt_add_of_lt_of_le hbaseTerm htailTerm
      _ = cutoff * (noAccessWeight + accessWeight * cdf) := by ring
  change denominator⁻¹ * numerator < cutoff
  calc
    denominator⁻¹ * numerator = numerator / denominator := by
      rw [div_eq_mul_inv]
      ring
    _ < cutoff := (div_lt_iff₀ hdenominator).2 hnumerator

/--
Translating a Gaussian latent mean translates the literal hidden-access
no-report mixture by the same amount.  The cutoff offset and both component
weights are unchanged.
-/
theorem lg21ReportRequiredRawNoReportMixturePBO_translate
    (mean : ℝ) (variance : NNReal) (hvariance : variance ≠ 0)
    (noAccessWeight accessWeight gap : ℝ)
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight) :
    lg21ReportRequiredRawNoReportMixturePBO
      (lg21GaussianScaleLawOfNNRealVariance mean variance hvariance)
      noAccessWeight accessWeight (mean + gap) =
      mean + lg21ReportRequiredRawNoReportMixturePBO
        (lg21GaussianScaleLawOfNNRealVariance 0 variance hvariance)
        noAccessWeight accessWeight gap := by
  let shiftedLaw :=
    lg21GaussianScaleLawOfNNRealVariance mean variance hvariance
  let centeredLaw :=
    lg21GaussianScaleLawOfNNRealVariance 0 variance hvariance
  have hstandardize : shiftedLaw.standardize (mean + gap) =
      centeredLaw.standardize gap := by
    dsimp [shiftedLaw, centeredLaw,
      lg21GaussianScaleLawOfNNRealVariance, GaussianScaleLaw.standardize]
    ring
  have hlowerMean : standardGaussianLowerTailMean shiftedLaw (mean + gap) =
      mean + standardGaussianLowerTailMean centeredLaw gap := by
    unfold standardGaussianLowerTailMean
    rw [hstandardize]
    dsimp [shiftedLaw, centeredLaw, lg21GaussianScaleLawOfNNRealVariance]
    ring
  have hdenom : noAccessWeight + accessWeight *
      standardGaussianCDF (centeredLaw.standardize gap) ≠ 0 := by
    exact ne_of_gt
      (lg21ReportRequiredRawNoReportMixture_denominator_pos
        centeredLaw hnoAccessWeight haccessWeight)
  change lg21ReportRequiredRawNoReportMixturePBO
      shiftedLaw noAccessWeight accessWeight (mean + gap) = _
  unfold lg21ReportRequiredRawNoReportMixturePBO
  rw [hstandardize, hlowerMean]
  dsimp [shiftedLaw, centeredLaw, lg21GaussianScaleLawOfNNRealVariance] at hdenom ⊢
  field_simp [hdenom]
  ring

/--
The literal report-required hidden-access candidate has a finite cutoff root.
At low cutoffs, the selected reporter boundary tends to `-∞` while the raw
`X = 0` mixture tends to the unselected mean.  At a cutoff above that mean,
the raw mixture is below the cutoff and the selected reporter boundary is
strictly above it.  Thus the result is a derived root, not a caller-supplied
equilibrium condition.
-/
theorem lg21ReportRequiredHiddenAccessMixture_exists_cutoff_root
    (priorMean priorVariance noiseVariance : ℝ)
    {noAccessWeight accessWeight : ℝ}
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hnoAccessWeight : 0 < noAccessWeight)
    (haccessWeight : 0 ≤ accessWeight) :
    ∃ cutoff : ℝ,
      lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance cutoff =
      lg21ReportRequiredRawNoReportMixturePBO
        (lg21GaussianScaleLawOfNNRealVariance priorMean
          priorVariance.toNNReal
          (ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)))
        noAccessWeight accessWeight cutoff := by
  let skillLaw := lg21GaussianScaleLawOfNNRealVariance priorMean
    priorVariance.toNNReal
    (ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance))
  let noReportPBO : ℝ → ℝ :=
    lg21ReportRequiredRawNoReportMixturePBO
      skillLaw noAccessWeight accessWeight
  let high : ℝ := priorMean + 1
  have hboundaryAtBot : Tendsto
      (lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance)
      atBot atBot :=
    lg21SelectedGaussianCutoffBoundaryPayoff_tendsto_atBot
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hnoReportAtBot : Tendsto noReportPBO atBot (𝓝 priorMean) := by
    simpa [noReportPBO, skillLaw] using
      (lg21ReportRequiredRawNoReportMixturePBO_tendsto_atBot
        skillLaw hnoAccessWeight haccessWeight)
  have hlowEvent : ∀ᶠ cutoff in atBot,
      lg21SelectedGaussianCutoffBoundaryPayoff
          priorMean priorVariance noiseVariance cutoff <
        noReportPBO cutoff := by
    filter_upwards
      [hboundaryAtBot.eventually (Filter.eventually_lt_atBot (priorMean - 1)),
        hnoReportAtBot.eventually
          (isOpen_Ioi.mem_nhds (show priorMean - 1 < priorMean by linarith))]
      with cutoff hboundary hnoReport
    linarith
  have hlowBelowHigh : ∀ᶠ cutoff in atBot, cutoff < high :=
    Filter.eventually_lt_atBot high
  obtain ⟨low, hlow, hlowHigh⟩ := (hlowEvent.and hlowBelowHigh).exists
  have hhighMean : skillLaw.mean < high := by
    change priorMean < priorMean + 1
    linarith
  have hhighNoReport : noReportPBO high < high := by
    exact lg21ReportRequiredRawNoReportMixturePBO_lt_cutoff
      skillLaw hnoAccessWeight haccessWeight hhighMean
  have hhigh : noReportPBO high <
      lg21SelectedGaussianCutoffBoundaryPayoff
        priorMean priorVariance noiseVariance high :=
    lg21SelectedGaussianCutoff_high_sign_of_noReport_lt_cutoff
      priorMean priorVariance noiseVariance high (noReportPBO high)
      hpriorVariance hnoiseVariance hhighNoReport
  rcases lg21SelectedGaussianCutoff_exists_root_of_finite_signs
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance
      noReportPBO
      (lg21ReportRequiredRawNoReportMixturePBO_continuous
        skillLaw hnoAccessWeight haccessWeight)
      hlowHigh hlow hhigh with
    ⟨cutoff, _hinterval, hroot⟩
  exact ⟨cutoff, hroot⟩

/--
The scalar raw-mixture PBO is exactly the mean of the literal hidden-access
candidate kernel at a public base.  This is the bridge that retains both the
unselected no-access Gaussian and the selected access lower tail.
-/
theorem lg21HiddenAccessTailCandidateNoReportValue_eq_scalarMixture
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass) (haccess : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base → ℝ) (hthreshold : Measurable threshold)
    (publicBase : Base) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    lg21HiddenAccessTailCandidateNoReportValue
      (gaussianLocationKernel baseMean hbaseMean baseVariance)
      noAccessMass accessMass hnoAccessFinite haccessFinite
      threshold publicBase =
      lg21ReportRequiredRawNoReportMixturePBO
        (lg21GaussianScaleLawOfNNRealVariance
          (baseMean publicBase) baseVariance hbaseVariance)
        noAccessMass.toReal accessMass.toReal (threshold publicBase) := by
  let κ : Kernel Base ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  let lowerTail : Set ℝ := Set.Iio (threshold publicBase)
  let lowerMass : ENNReal := κ publicBase lowerTail
  let lowerLaw : Measure ℝ :=
    lg21NormalizedRestriction (κ publicBase) lowerTail
  let skillLaw := lg21GaussianScaleLawOfNNRealVariance
    (baseMean publicBase) baseVariance hbaseVariance
  letI : IsMarkovKernel κ := by
    simpa [κ] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance)
  letI : IsFiniteMeasure (κ publicBase) := by infer_instance
  have hκ : κ publicBase = skillLaw.toMeasure := by
    rw [show κ publicBase = gaussianReal (baseMean publicBase) baseVariance by
      exact gaussianLocationKernel_apply
        baseMean hbaseMean baseVariance publicBase]
    symm
    exact lg21GaussianScaleLawOfNNRealVariance_toMeasure _ _ _
  have hlowerPositive : 0 < lowerMass := by
    change 0 < κ publicBase (Set.Iio (threshold publicBase))
    rw [show κ publicBase = gaussianReal (baseMean publicBase) baseVariance by
      exact gaussianLocationKernel_apply
        baseMean hbaseMean baseVariance publicBase]
    exact lg21_gaussianReal_Iio_pos
      (baseMean publicBase) (threshold publicBase) hbaseVariance
  have hlowerFinite : lowerMass ≠ ⊤ := measure_ne_top _ _
  letI : IsProbabilityMeasure lowerLaw := by
    simpa [lowerLaw] using
      (lg21NormalizedRestriction_isProbability
        (κ publicBase) lowerTail (ne_of_gt hlowerPositive) hlowerFinite)
  have hweightOne : 0 < accessMass * lowerMass := by
    exact ENNReal.mul_pos (ne_of_gt haccess) (ne_of_gt hlowerPositive)
  have hweightOneFinite : accessMass * lowerMass ≠ ⊤ := by
    exact ENNReal.mul_ne_top haccessFinite hlowerFinite
  have hrawKernel :
      lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold publicBase =
        noAccessMass • κ publicBase +
          (accessMass * lowerMass) • lowerLaw := by
    rw [lg21HiddenAccessTailRawKernel_apply κ noAccessMass accessMass
      threshold hthreshold publicBase,
      ← lg21_smul_normalizedRestriction_eq_restrict
        (κ publicBase) lowerTail hlowerPositive,
      ← smul_smul]
  have hnormalizedKernel :
      lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
          hnoAccessFinite haccessFinite threshold publicBase =
        (noAccessMass + accessMass * lowerMass)⁻¹ •
          (noAccessMass • κ publicBase +
            (accessMass * lowerMass) • lowerLaw) := by
    rw [lg21HiddenAccessTailNormalizedKernel_apply
      κ noAccessMass accessMass hnoAccessFinite haccessFinite threshold
      hthreshold publicBase, hrawKernel]
    rfl
  have hbaseIntegral :
      (∫ latentSkill, latentSkill ∂κ publicBase) = baseMean publicBase := by
    simpa [κ] using
      (lg21_gaussianLocationKernel_skill_mean
        baseMean hbaseMean baseVariance publicBase)
  have hlowerMean :
      (∫ latentSkill, latentSkill ∂lowerLaw) =
        standardGaussianLowerTailMean skillLaw (threshold publicBase) := by
    change (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction (κ publicBase) lowerTail) = _
    rw [hκ]
    simpa [lowerTail] using
      (lg21GaussianScaleLaw_normalizedIio_mean_eq_lowerTailMean
        skillLaw (threshold publicBase))
  have hlowerMassReal : lowerMass.toReal =
      standardGaussianCDF (skillLaw.standardize (threshold publicBase)) := by
    change (κ publicBase (Set.Iio (threshold publicBase))).toReal = _
    rw [hκ]
    exact lg21GaussianScaleLaw_Iio_mass_toReal_eq_standardGaussianCDF
      skillLaw (threshold publicBase)
  have hweightOneReal : (accessMass * lowerMass).toReal =
      accessMass.toReal *
        standardGaussianCDF (skillLaw.standardize (threshold publicBase)) := by
    rw [ENNReal.toReal_mul, hlowerMassReal]
  change (∫ latentSkill, latentSkill ∂
      lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold publicBase) = _
  calc
    (∫ latentSkill, latentSkill ∂
        lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
          hnoAccessFinite haccessFinite threshold publicBase) =
        ∫ latentSkill, latentSkill ∂
          ((noAccessMass + accessMass * lowerMass)⁻¹ •
            (noAccessMass • κ publicBase +
              (accessMass * lowerMass) • lowerLaw)) := by
          rw [hnormalizedKernel]
    _ = (noAccessMass.toReal + (accessMass * lowerMass).toReal)⁻¹ *
        (noAccessMass.toReal * (∫ latentSkill, latentSkill ∂κ publicBase) +
          (accessMass * lowerMass).toReal *
            (∫ latentSkill, latentSkill ∂lowerLaw)) := by
          exact lg21_normalizedTwoComponentMean_eq
            (κ publicBase) lowerLaw (fun latentSkill : ℝ => latentSkill)
            noAccessMass (accessMass * lowerMass)
            hnoAccessFinite hweightOneFinite
            (lg21_gaussianLocationKernel_skill_integrable
              baseMean hbaseMean baseVariance publicBase)
            (lg21_gaussianLocationKernel_lowerTail_integrable
              baseMean hbaseMean baseVariance hbaseVariance publicBase
              (threshold publicBase))
    _ = lg21ReportRequiredRawNoReportMixturePBO
        skillLaw noAccessMass.toReal accessMass.toReal
          (threshold publicBase) := by
          rw [hbaseIntegral, hlowerMean, hweightOneReal]
          rfl

/--
One scalar cutoff offset solves the literal raw `X = 0` root at every public
base when the conditional latent laws differ only by translation.  The
right-hand side is the actual candidate kernel mean, not an access-only
posterior or a separately postulated continuation value.
-/
theorem lg21ReportRequiredHiddenAccessMixture_exists_uniform_raw_root
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass) (haccess : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (noiseVariance : ℝ) (hnoiseVariance : 0 < noiseVariance) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    ∃ gap : ℝ, ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) (baseVariance : ℝ) noiseVariance
        (baseMean publicBase + gap) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance)
        noAccessMass accessMass hnoAccessFinite haccessFinite
        (fun publicBase => baseMean publicBase + gap) publicBase := by
  let κ : Kernel Base ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  letI : IsMarkovKernel κ := by
    simpa [κ] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance)
  have hpriorVariance : 0 < (baseVariance : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hbaseVariance : 0 < baseVariance)
  have hnoAccessWeight : 0 < noAccessMass.toReal :=
    ENNReal.toReal_pos (ne_of_gt hnoAccess) hnoAccessFinite
  have haccessWeight : 0 ≤ accessMass.toReal := ENNReal.toReal_nonneg
  obtain ⟨gap, hroot⟩ :=
    lg21ReportRequiredHiddenAccessMixture_exists_cutoff_root
      0 (baseVariance : ℝ) noiseVariance hpriorVariance hnoiseVariance
      hnoAccessWeight haccessWeight
  have hrootCentered :
      lg21SelectedGaussianCutoffBoundaryPayoff
          0 (baseVariance : ℝ) noiseVariance gap =
        lg21ReportRequiredRawNoReportMixturePBO
          (lg21GaussianScaleLawOfNNRealVariance 0 baseVariance hbaseVariance)
          noAccessMass.toReal accessMass.toReal gap := by
    simpa using hroot
  let threshold : Base → ℝ := fun publicBase => baseMean publicBase + gap
  have hthreshold : Measurable threshold := by
    exact hbaseMean.add measurable_const
  refine ⟨gap, ?_⟩
  intro publicBase
  calc
    lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) (baseVariance : ℝ) noiseVariance
        (baseMean publicBase + gap) =
      baseMean publicBase +
        lg21SelectedGaussianCutoffBoundaryPayoff
          0 (baseVariance : ℝ) noiseVariance gap := by
          exact lg21SelectedGaussianCutoffBoundaryPayoff_translate
            (baseMean publicBase) (baseVariance : ℝ) noiseVariance gap
            hpriorVariance hnoiseVariance
    _ = baseMean publicBase +
        lg21ReportRequiredRawNoReportMixturePBO
          (lg21GaussianScaleLawOfNNRealVariance 0 baseVariance hbaseVariance)
          noAccessMass.toReal accessMass.toReal gap := by
          rw [hrootCentered]
    _ = lg21ReportRequiredRawNoReportMixturePBO
        (lg21GaussianScaleLawOfNNRealVariance
          (baseMean publicBase) baseVariance hbaseVariance)
        noAccessMass.toReal accessMass.toReal
        (baseMean publicBase + gap) := by
          symm
          exact lg21ReportRequiredRawNoReportMixturePBO_translate
            (baseMean publicBase) baseVariance hbaseVariance
            noAccessMass.toReal accessMass.toReal gap
            hnoAccessWeight haccessWeight
    _ = lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance)
        noAccessMass accessMass hnoAccessFinite haccessFinite
        threshold publicBase := by
          symm
          simpa [κ, threshold] using
            (lg21HiddenAccessTailCandidateNoReportValue_eq_scalarMixture
              baseMean hbaseMean baseVariance hbaseVariance
              noAccessMass accessMass hnoAccess haccess
              hnoAccessFinite haccessFinite threshold hthreshold publicBase)

end

end LG21TestOptionalPolicies
