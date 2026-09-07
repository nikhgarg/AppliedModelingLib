import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge
import LG21TestOptionalPolicies.SelectedConditionalRestrictionMap
import LG21TestOptionalPolicies.RawGaussianOptionalPositiveBranch

/-!
# Literal all-access/high-score candidate for LG21 Theorem 3.1

This module develops the concrete candidate relevant to a zero-reporter
region in the optional-reporting part of Theorem 3.1.  Every student with
access takes the test, and an access student reports exactly when the realized
score is at least the conditional base mean plus a positive gap.  The public
`X = 0` law retains the literal no-access population, so its PBO is a
two-component raw-population conditional law rather than an access-only
selected law.

Nothing here treats a positive current reporter population.  That is the
separate on-path branch of the source proof.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-! ## Gaussian score-law identification -/

/-- The concrete location-scale score law associated with a positive Gaussian
variance.  It is used only to identify literal Gaussian measures with the
scalar CDF notation already used by the source cutoff equation. -/
noncomputable def lg21HiddenAccessGaussianScoreLaw
    (mean variance : ℝ) (hvariance : 0 < variance) : GaussianScaleLaw where
  mean := mean
  scale := Real.sqrt variance
  scale_pos := Real.sqrt_pos.mpr hvariance

/-- The location-scale score law denotes the same mathlib Gaussian measure as
the corresponding positive variance parameter. -/
theorem lg21HiddenAccessGaussianScoreLaw_toMeasure
    (mean variance : ℝ) (hvariance : 0 < variance) :
    (lg21HiddenAccessGaussianScoreLaw mean variance hvariance).toMeasure =
      gaussianReal mean variance.toNNReal := by
  unfold lg21HiddenAccessGaussianScoreLaw GaussianScaleLaw.toMeasure
  congr 1
  apply NNReal.eq
  change Real.sqrt variance ^ 2 = (variance.toNNReal : ℝ)
  rw [Real.sq_sqrt (le_of_lt hvariance),
    Real.toNNReal_of_nonneg (le_of_lt hvariance)]
  simp

/-- The literal lower-score mass of a concrete Gaussian law is the scalar CDF
used in `lg21OptionalNoReportMixtureEstimate`.  The open cutoff convention of
the action and the closed CDF convention agree because the Gaussian has no
atoms. -/
theorem lg21HiddenAccessGaussianScoreLaw_Iio_toReal_eq_normalCDF
    (mean variance : ℝ) (hvariance : 0 < variance) (cutoff : ℝ) :
    (gaussianReal mean variance.toNNReal (Set.Iio cutoff)).toReal =
      standardGaussianCDFAPI.normalCDF
        (lg21HiddenAccessGaussianScoreLaw mean variance hvariance) cutoff := by
  let scoreLaw := lg21HiddenAccessGaussianScoreLaw mean variance hvariance
  have hIioIic : scoreLaw.toMeasure (Set.Iio cutoff) =
      scoreLaw.toMeasure (Set.Iic cutoff) := by
    exact measure_congr (lg21_optional_Iio_ae_eq_Iic scoreLaw cutoff)
  have hclosed : (scoreLaw.toMeasure (Set.Iic cutoff)).toReal =
      standardGaussianCDFAPI.normalCDF scoreLaw cutoff := by
    rw [lg21_optional_gaussianScaleLaw_lowerTail_mass_eq_standard]
    change (standardGaussianMeasure (Set.Iic (scoreLaw.standardize cutoff))).toReal =
      standardGaussianCDF (scoreLaw.standardize cutoff)
    rw [standardGaussianCDF, ProbabilityTheory.cdf_eq_real]
    rfl
  rw [← lg21HiddenAccessGaussianScoreLaw_toMeasure mean variance hvariance]
  exact (congrArg ENNReal.toReal hIioIic).trans hclosed

/-- The literal lower-score selection mass in a Gaussian score/skill fibre is
exactly the CDF term used by the scalar optional-reporting equation. -/
theorem lg21HiddenAccessGaussianSignal_lowerScoreMass_toReal_eq_normalCDF
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (publicBase : Base) :
    let scoreVariance := baseVariance + noiseVariance
    let scoreLaw := lg21HiddenAccessGaussianScoreLaw
      (baseMean publicBase) scoreVariance (by linarith)
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    (joint publicBase
      (selectedFiber
        (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) publicBase)).toReal =
      standardGaussianCDFAPI.normalCDF scoreLaw anchor := by
  intro scoreVariance scoreLaw joint
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  rw [show joint publicBase =
      gaussianReal (baseMean publicBase) scoreVariance.toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) publicBase by
        simpa [joint, scoreVariance] using
          (lg21_optional_fullBaseGaussian_jointKernel_apply
            baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance publicBase)]
  rw [lg21OptionalFullBaseNoReportEvent_selectedFiber]
  rw [lg21_optional_compProd_score_lowerTail_mass]
  simpa [scoreLaw] using
    (lg21HiddenAccessGaussianScoreLaw_Iio_toReal_eq_normalCDF
      (baseMean publicBase) scoreVariance (by linarith) anchor)

/-- For the binary source access law, the no-access mass is literally the
complement of the access fraction in real probability coordinates. -/
theorem lg21HiddenAccess_accessLaw_false_toReal_eq_one_sub_true
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    (M.accessLaw {false}).toReal = 1 - (M.accessLaw {true}).toReal := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hcomplement : ({true} : Set Bool)ᶜ = {false} := by
    ext access
    cases access <;> simp
  simpa [hcomplement] using
    (MeasureTheory.probReal_compl_eq_one_sub
      (μ := M.accessLaw) (s := ({true} : Set Bool))
      (measurableSet_singleton true))

/-- The literal selected-access no-report value is the affine Gaussian
posterior evaluated at the literal lower-score conditional mean.  This is the
analytic specialization needed to reuse the scalar continuity and endpoint
lemmas; it follows from the measure definition of the PBO. -/
theorem lg21OptionalFullBaseNoReportValue_eq_affine_standardGaussianLowerTailMean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (publicBase : Base) :
    let scoreVariance := baseVariance + noiseVariance
    let scoreLaw := lg21HiddenAccessGaussianScoreLaw
      (baseMean publicBase) scoreVariance (by linarith)
    lg21OptionalFullBaseNoReportValue
      baseMean hbaseMean baseVariance noiseVariance anchor publicBase =
      gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase +
        gaussianSignalWeight baseVariance noiseVariance *
          standardGaussianLowerTailMean scoreLaw anchor := by
  intro scoreVariance scoreLaw
  let rawScoreLaw := gaussianReal (baseMean publicBase) scoreVariance.toNNReal
  let posterior := Kernel.sectR (gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean baseVariance noiseVariance) publicBase
  let lowerRawLaw := lg21NormalizedRestriction rawScoreLaw (Set.Iio anchor)
  have hscoreLaw : scoreLaw.toMeasure = rawScoreLaw := by
    simpa [scoreLaw, rawScoreLaw] using
      (lg21HiddenAccessGaussianScoreLaw_toMeasure
        (baseMean publicBase) scoreVariance (by linarith))
  have hlowerPositive : rawScoreLaw (Set.Iio anchor) ≠ 0 := by
    apply ne_of_gt
    dsimp [rawScoreLaw]
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase) anchor
      (ne_of_gt (Real.toNNReal_pos.mpr (by linarith)))
  have hintegrableRaw : Integrable (fun score : ℝ => score) rawScoreLaw := by
    dsimp [rawScoreLaw]
    exact
      (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
  letI : IsProbabilityMeasure lowerRawLaw := by
    simpa [lowerRawLaw] using
      (lg21NormalizedRestriction_isProbability
        rawScoreLaw (Set.Iio anchor) hlowerPositive (measure_ne_top _ _))
  have hintegrableLower : Integrable (fun score : ℝ => score) lowerRawLaw := by
    simpa [lowerRawLaw] using
      (lg21_optional_integrable_id_normalizedRestriction
        rawScoreLaw (Set.Iio anchor) hlowerPositive hintegrableRaw)
  have hlowerMean : (∫ score, score ∂lowerRawLaw) =
      standardGaussianLowerTailMean scoreLaw anchor := by
    calc
      (∫ score, score ∂lowerRawLaw) =
          ∫ score, score ∂
            lg21NormalizedRestriction scoreLaw.toMeasure (Set.Iic anchor) := by
              rw [show lowerRawLaw =
                lg21NormalizedRestriction rawScoreLaw (Set.Iio anchor) by rfl,
                ← hscoreLaw]
              rw [lg21_optional_normalizedRestriction_congr_ae
                scoreLaw.toMeasure
                (lg21_optional_Iio_ae_eq_Iic scoreLaw anchor)]
      _ = standardGaussianLowerTailMean scoreLaw anchor := by
            rw [← lg21_optional_gaussian_lower_tail_conditional_mean_eq_standardGaussianLowerTailMean
              scoreLaw anchor]
            rfl
  change (∫ score, (∫ skill, skill ∂posterior score) ∂lowerRawLaw) = _
  have hposteriorMean : (fun score : ℝ =>
      ∫ skill, skill ∂posterior score) =
      fun score =>
        gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase +
          gaussianSignalWeight baseVariance noiseVariance * score := by
    funext score
    change lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance publicBase score = _
    rw [lg21_optional_rawGaussianPosteriorMean_eq_affine]
    ring
  rw [hposteriorMean]
  rw [MeasureTheory.integral_add
      (integrable_const
        (gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase))
      (hintegrableLower.const_mul
        (gaussianSignalWeight baseVariance noiseVariance)),
    MeasureTheory.integral_const, MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.measureReal_def, measure_univ,
    ENNReal.toReal_one, one_smul]
  rw [hlowerMean]

/-- At a fixed public base profile, the literal selected-access lower-score
value varies continuously with the displayed cutoff.  Together with the
literal mixture identity below, this supplies the analytic side condition for
the source cutoff crossing argument without replacing the raw `X = 0` law by
an access-only conditional law. -/
theorem lg21OptionalFullBaseNoReportValue_continuous_anchor
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    Continuous (fun anchor : ℝ =>
      lg21OptionalFullBaseNoReportValue
        baseMean hbaseMean baseVariance noiseVariance anchor publicBase) := by
  let scoreVariance := baseVariance + noiseVariance
  let scoreLaw := lg21HiddenAccessGaussianScoreLaw
    (baseMean publicBase) scoreVariance (by linarith)
  have hformula :
      (fun anchor : ℝ =>
        lg21OptionalFullBaseNoReportValue
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase) =
        fun anchor : ℝ =>
          gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase +
            gaussianSignalWeight baseVariance noiseVariance *
              standardGaussianLowerTailMean scoreLaw anchor := by
    funext anchor
    simpa [scoreVariance, scoreLaw] using
      (lg21OptionalFullBaseNoReportValue_eq_affine_standardGaussianLowerTailMean
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase)
  rw [hformula]
  exact continuous_const.add
    (continuous_const.mul (standardGaussianLowerTailMean_continuous scoreLaw))

/-- The literal source `X = 0` mixture is continuous in its displayed score
cutoff.  The access component is the selected-access conditional mean, while
the denominator retains the base-only no-access component. -/
theorem lg21OptionalNoReportMixtureEstimate_fullBase_continuous_anchor
    {Base : Type*} [MeasurableSpace Base]
    {accessFraction : ℝ} (haccessNonneg : 0 ≤ accessFraction)
    (haccessLtOne : accessFraction < 1)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    let scoreVariance := baseVariance + noiseVariance
    let scoreLaw := lg21HiddenAccessGaussianScoreLaw
      (baseMean publicBase) scoreVariance (by linarith)
    Continuous (fun anchor : ℝ =>
      lg21OptionalNoReportMixtureEstimate
        accessFraction (baseMean publicBase) scoreLaw
        (fun cutoff =>
          lg21OptionalFullBaseNoReportValue
            baseMean hbaseMean baseVariance noiseVariance cutoff publicBase)
        anchor) := by
  intro scoreVariance scoreLaw
  apply lg21OptionalNoReportMixtureEstimate_continuous
    haccessNonneg haccessLtOne (baseMean publicBase) scoreLaw
  simpa [scoreVariance, scoreLaw] using
    (lg21OptionalFullBaseNoReportValue_continuous_anchor
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase)

/-- For a literal hidden-access population with positive no-access mass, the
actual `X = 0` candidate mixture satisfies the probability bounds required by
the scalar cutoff-continuity and endpoint arguments. -/
theorem lg21HiddenAccessOptionalNoReportMixture_continuous_anchor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : LG21NonTestFeature Feature testFeature → ℝ) :
    let scoreVariance := baseVariance + noiseVariance
    let scoreLaw := lg21HiddenAccessGaussianScoreLaw
      (baseMean publicBase) scoreVariance (by linarith)
    Continuous (fun anchor : ℝ =>
      lg21OptionalNoReportMixtureEstimate
        (M.accessLaw {true}).toReal (baseMean publicBase) scoreLaw
        (fun cutoff =>
          lg21OptionalFullBaseNoReportValue
            baseMean hbaseMean baseVariance noiseVariance cutoff publicBase)
        anchor) := by
  intro scoreVariance scoreLaw
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have haccessNonneg : 0 ≤ (M.accessLaw {true}).toReal := ENNReal.toReal_nonneg
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have hnoAccessRealPos : 0 < (M.accessLaw {false}).toReal :=
    ENNReal.toReal_pos (ne_of_gt hnoAccess) hnoAccessFinite
  have hcomplement := lg21HiddenAccess_accessLaw_false_toReal_eq_one_sub_true M
  have haccessLtOne : (M.accessLaw {true}).toReal < 1 := by
    rw [hcomplement] at hnoAccessRealPos
    linarith
  simpa [scoreVariance, scoreLaw] using
    (lg21OptionalNoReportMixtureEstimate_fullBase_continuous_anchor
      haccessNonneg haccessLtOne baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase)

/-! ## Candidate actions -/

/-- The source-timed candidate makes every access student take the test. -/
def lg21HiddenAccessAllTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool :=
  fun _ _ => true

/-- A base-dependent high-score reporting action.  The threshold is evaluated
only after the score is realized; it never uses the hidden access bit. -/
def lg21HiddenAccessMeanGapReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
  fun publicBase score => decide (baseMean publicBase + gap ≤ score)

theorem lg21HiddenAccessAllTake_eq_true
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (skill : ℝ)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    lg21HiddenAccessAllTake testFeature skill publicBase = true := by
  rfl

theorem lg21HiddenAccessMeanGapReport_eq_true_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap score : ℝ)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    lg21HiddenAccessMeanGapReport testFeature baseMean gap publicBase score = true ↔
      baseMean publicBase + gap ≤ score := by
  simp [lg21HiddenAccessMeanGapReport]

theorem lg21HiddenAccessMeanGapReport_eq_false_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap score : ℝ)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    lg21HiddenAccessMeanGapReport testFeature baseMean gap publicBase score = false ↔
      score < baseMean publicBase + gap := by
  simp [lg21HiddenAccessMeanGapReport, not_le]

theorem lg21HiddenAccessAllTake_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessAllTake testFeature pair.1 pair.2) := by
  exact measurable_const

theorem lg21HiddenAccessMeanGapReport_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ) :
    Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessMeanGapReport testFeature baseMean gap pair.1 pair.2) := by
  apply measurable_to_bool
  have htail : MeasurableSet {pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
      baseMean pair.1 + gap ≤ pair.2} :=
    measurableSet_le ((hbaseMean.comp measurable_fst).add measurable_const)
      measurable_snd
  convert htail using 1
  ext pair
  simp [lg21HiddenAccessMeanGapReport]

/-! ## Literal action events -/

/-- The access component of the candidate's no-report action: an access
student took the test and obtained a score below the displayed threshold. -/
def lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) : Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | student.1 = true ∧
    lg21HiddenAccessStudentScore testFeature student.2 <
      baseMean (lg21HiddenAccessStudentBase testFeature student.2) + gap}

theorem lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ) :
    MeasurableSet
      (lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent testFeature baseMean gap) := by
  have haccess : MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true} :=
    (measurableSet_singleton true).preimage measurable_fst
  have hscore : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentScore testFeature student.2) :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  change MeasurableSet ({student : Bool × (ℝ × (Feature -> ℝ)) |
    student.1 = true} ∩
      {student | lg21HiddenAccessStudentScore testFeature student.2 <
        baseMean (lg21HiddenAccessStudentBase testFeature student.2) + gap})
  exact haccess.inter (measurableSet_lt hscore
    ((hbaseMean.comp hbase).add measurable_const))

theorem lg21HiddenAccessAllTake_candidateAccessNoTakeEvent_eq_empty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    lg21HiddenAccessCandidateAccessNoTakeEvent testFeature
      (lg21HiddenAccessAllTake testFeature) = ∅ := by
  ext student
  simp [lg21HiddenAccessCandidateAccessNoTakeEvent,
    lg21HiddenAccessStudentTake, lg21HiddenAccessAllTake]

theorem lg21HiddenAccessAllTakeMeanGap_candidateAccessTakeNoReportEvent_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent testFeature baseMean gap := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨skill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessCandidateAccessTakeNoReportEvent,
      lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessAllTake, lg21HiddenAccessMeanGapReport,
      lg21HiddenAccessStudentScore, not_le]

/-- Exact literal `X = 0` event for the all-access/high-score candidate.
The first component is all no-access students, including their literal
unobserved scores; the second is the low-score access component. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawCandidateNoReportEvent_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    lg21HiddenAccessRawCandidateNoReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessAllTakeMeanGapAccessNoReportEvent testFeature baseMean gap := by
  rw [lg21HiddenAccessRawCandidateNoReportEvent_eq_components]
  rw [lg21HiddenAccessAllTake_candidateAccessNoTakeEvent_eq_empty,
    lg21HiddenAccessAllTakeMeanGap_candidateAccessTakeNoReportEvent_eq]
  simp

/-- Exact literal `X = 1` event for the all-access/high-score candidate. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      {student | student.1 = true ∧
        baseMean (lg21HiddenAccessStudentBase testFeature student.2) + gap ≤
          lg21HiddenAccessStudentScore testFeature student.2} := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨skill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessAllTake, lg21HiddenAccessMeanGapReport,
      lg21HiddenAccessStudentScore]

/-! ## Score-selected raw PBO kernel -/

/-- The base-indexed lower-score event in the literal score/skill source
kernel.  This is a selection on the observed score, rather than a latent
skill tail. -/
def lg21HiddenAccessBaseScoreLowerTailEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | baseScoreSkill.2.1 < threshold baseScoreSkill.1}

theorem lg21HiddenAccessBaseScoreLowerTailEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21HiddenAccessBaseScoreLowerTailEvent threshold) := by
  exact measurableSet_lt (measurable_fst.comp measurable_snd)
    (hthreshold.comp measurable_fst)

/-- The base-indexed upper-score event used by the literal report branch of
the all-take candidate.  Keeping this event explicit is important: the
candidate cutoff may vary with the public base profile. -/
def lg21HiddenAccessBaseScoreUpperTailEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | threshold baseScoreSkill.1 ≤ baseScoreSkill.2.1}

theorem lg21HiddenAccessBaseScoreUpperTailEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21HiddenAccessBaseScoreUpperTailEvent threshold) := by
  exact measurableSet_le (hthreshold.comp measurable_fst)
    (measurable_fst.comp measurable_snd)

theorem lg21HiddenAccessBaseScoreUpperTailEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (publicBase : Base) :
    selectedFiber (lg21HiddenAccessBaseScoreUpperTailEvent threshold) publicBase =
      Set.Ici (threshold publicBase) ×ˢ Set.univ := by
  ext scoreSkill
  simp [selectedFiber, lg21HiddenAccessBaseScoreUpperTailEvent]

/-- Selecting a positive-mass base-dependent upper score tail does not alter
the Gaussian posterior conditional on the disclosed `(base, score)` record.
The statement is deliberately almost everywhere under the selected action
law, so it does not assign a posterior to unselected score fibres. -/
theorem lg21HiddenAccessGaussian_selectedUpperTail_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold)
    (hpositive : 0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21HiddenAccessBaseScoreUpperTailEvent threshold)) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21HiddenAccessBaseScoreUpperTailEvent threshold)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib
      (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
      selectedLaw =ᵐ[selectedLaw.map
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
      gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance := by
  intro selectedLaw
  let rawLaw := baseLaw ⊗ₘ gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (baseVariance + noiseVariance).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean baseVariance noiseVariance
  let observedLaw := baseLaw ⊗ₘ scoreKernel
  let observationEvent : Set (Base × ℝ) :=
    {baseScore | threshold baseScore.1 ≤ baseScore.2}
  let reportEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) -> Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) -> ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsProbabilityMeasure observedLaw := by
    dsimp [observedLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hreportEvent : MeasurableSet reportEvent := by
    simpa [reportEvent] using
      lg21HiddenAccessBaseScoreUpperTailEvent_measurable threshold hthreshold
  have hobservationEvent : MeasurableSet observationEvent := by
    exact measurableSet_le (hthreshold.comp measurable_fst) measurable_snd
  have hassociation : Measurable association := by
    dsimp [association]
    fun_prop
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hreportPreimage :
      reportEvent = association ⁻¹' (observationEvent ×ˢ Set.univ) := by
    ext scoreSkill
    simp [reportEvent, association, observationEvent,
      lg21HiddenAccessBaseScoreUpperTailEvent]
  have hrawAssoc : rawLaw.map association = observedLaw ⊗ₘ posteriorKernel := by
    simpa [rawLaw, association, observedLaw, posteriorKernel,
      gaussianSignalBaseScoreLatentLaw] using
      (gaussianSignalBaseScoreLatentLaw_factorization
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance)
  have hselectedAssoc :
      selectedLaw.map association =
        lg21NormalizedRestriction (rawLaw.map association)
          (observationEvent ×ˢ Set.univ) := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw reportEvent by rfl,
      hreportPreimage]
    exact lg21_optional_normalizedRestriction_map_preimage
      rawLaw association hassociation (observationEvent ×ˢ Set.univ)
      (hobservationEvent.prod MeasurableSet.univ)
  have hselectedFactor :
      selectedLaw.map association =
        lg21NormalizedRestriction observedLaw observationEvent ⊗ₘ posteriorKernel := by
    calc
      selectedLaw.map association =
          lg21NormalizedRestriction (rawLaw.map association)
            (observationEvent ×ˢ Set.univ) := hselectedAssoc
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
            (observationEvent ×ˢ Set.univ) := by rw [hrawAssoc]
      _ = lg21NormalizedRestriction observedLaw observationEvent ⊗ₘ posteriorKernel :=
        lg21_normalizedRestriction_compProd_left
          observedLaw posteriorKernel observationEvent hobservationEvent
  letI : SFinite (lg21NormalizedRestriction observedLaw observationEvent) := by
    unfold lg21NormalizedRestriction
    infer_instance
  have hselectedObservation :
      selectedLaw.map observation =
        lg21NormalizedRestriction observedLaw observationEvent := by
    calc
      selectedLaw.map observation = (selectedLaw.map association).map Prod.fst := by
        rw [Measure.map_map measurable_fst hassociation]
        rfl
      _ = (lg21NormalizedRestriction observedLaw observationEvent ⊗ₘ
          posteriorKernel).map Prod.fst := by rw [hselectedFactor]
      _ = lg21NormalizedRestriction observedLaw observationEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      selectedLaw.map (fun scoreSkill => (observation scoreSkill, latent scoreSkill)) =
        selectedLaw.map observation ⊗ₘ posteriorKernel := by
    calc
      selectedLaw.map (fun scoreSkill =>
          (observation scoreSkill, latent scoreSkill)) =
          selectedLaw.map association := by rfl
      _ = lg21NormalizedRestriction observedLaw observationEvent ⊗ₘ posteriorKernel :=
        hselectedFactor
      _ = selectedLaw.map observation ⊗ₘ posteriorKernel := by
        rw [hselectedObservation]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hobservation hlatent hselectedJoint

/-- The all-take candidate's literal report event is precisely positive
access together with the base-dependent public upper-score event. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      {student | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21HiddenAccessBaseScoreUpperTailEvent
            (fun publicBase => baseMean publicBase + gap)) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨skill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessAllTake, lg21HiddenAccessMeanGapReport,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessStudentScore,
      lg21HiddenAccessBaseScoreSkillObservation,
      lg21HiddenAccessBaseScoreUpperTailEvent]

/-- A nondegenerate Gaussian score experiment assigns positive mass to every
measurable base-dependent closed upper tail. -/
theorem lg21HiddenAccessGaussian_selectedUpperTail_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21HiddenAccessBaseScoreUpperTailEvent threshold) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hevent : MeasurableSet event := by
    simpa [event] using
      lg21HiddenAccessBaseScoreUpperTailEvent_measurable threshold hthreshold
  have hfibre : ∀ publicBase,
      0 < rawKernel publicBase (selectedFiber event publicBase) := by
    intro publicBase
    rw [show selectedFiber event publicBase =
        selectedFiber
          (lg21OptionalFullBaseReportEvent (Base := Base)
            (threshold publicBase)) publicBase by
          rw [lg21HiddenAccessBaseScoreUpperTailEvent_selectedFiber,
            lg21OptionalFullBaseReportEvent_selectedFiber]]
    exact lg21_optional_fullBaseGaussian_report_fibre_positive
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance (threshold publicBase) publicBase
  have hmassMeasurable : Measurable
      (fun publicBase => rawKernel publicBase (selectedFiber event publicBase)) := by
    exact Kernel.measurable_kernel_prodMk_left hevent
  change 0 < (baseLaw ⊗ₘ rawKernel) event
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsupp : Function.support
      (fun publicBase => rawKernel publicBase (selectedFiber event publicBase)) =
        Set.univ := by
    ext publicBase
    simp [Function.mem_support, ne_of_gt (hfibre publicBase)]
  rw [hsupp, IsProbabilityMeasure.measure_univ]
  norm_num

/-- The unnormalized latent-skill kernel induced by selecting the literal
lower-score access population.  Its total mass is the score-selection mass
in each public-base fibre. -/
def lg21HiddenAccessScoreSelectedSkillKernel
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (threshold : Base -> ℝ) : Kernel Base ℝ :=
  (selectedRestrictionKernel joint
    (lg21HiddenAccessBaseScoreLowerTailEvent threshold)).map Prod.snd

instance lg21HiddenAccessScoreSelectedSkillKernel_isFinite
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (threshold : Base -> ℝ) :
    IsFiniteKernel (lg21HiddenAccessScoreSelectedSkillKernel joint threshold) := by
  letI : IsFiniteKernel joint := by infer_instance
  letI : IsFiniteKernel (selectedRestrictionKernel joint
      (lg21HiddenAccessBaseScoreLowerTailEvent threshold)) :=
    selectedRestrictionKernel_isFinite
      (lg21HiddenAccessBaseScoreLowerTailEvent threshold)
  unfold lg21HiddenAccessScoreSelectedSkillKernel
  infer_instance

/-- The literal unnormalized raw `X = 0` skill kernel.  The first summand is
the full no-access population; the second is the access population selected
by the observed lower-score event. -/
def lg21HiddenAccessScoreRawKernel
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsSFiniteKernel noAccessKernel] [IsSFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal) : Kernel Base ℝ :=
  noAccessKernel.withDensity (fun _ _ => noAccessMass) +
    accessSelectedSkillKernel.withDensity (fun _ _ => accessMass)

/-- The total mass of a raw score-selected `X = 0` fibre. -/
def lg21HiddenAccessScoreRawFibreMass
    {Base : Type*} [MeasurableSpace Base]
    (accessSelectedSkillKernel : Kernel Base ℝ)
    (noAccessMass accessMass : ENNReal) (publicBase : Base) : ENNReal :=
  noAccessMass + accessMass * accessSelectedSkillKernel publicBase Set.univ

theorem lg21HiddenAccessScoreRawKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsSFiniteKernel noAccessKernel] [IsSFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal) (publicBase : Base) :
    lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass publicBase =
      noAccessMass • noAccessKernel publicBase +
        accessMass • accessSelectedSkillKernel publicBase := by
  rw [lg21HiddenAccessScoreRawKernel, Kernel.add_apply,
    Kernel.withDensity_apply _ measurable_const,
    Kernel.withDensity_apply _ measurable_const,
    withDensity_const, withDensity_const]

theorem lg21HiddenAccessScoreRawKernel_apply_univ
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsSFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal) (publicBase : Base) :
    lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass publicBase Set.univ =
      lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
        noAccessMass accessMass publicBase := by
  rw [lg21HiddenAccessScoreRawKernel_apply]
  simp [lg21HiddenAccessScoreRawFibreMass]

theorem lg21HiddenAccessScoreSelectedSkillKernel_apply_univ
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold)
    (publicBase : Base) :
    lg21HiddenAccessScoreSelectedSkillKernel joint threshold publicBase Set.univ =
      joint publicBase
        (selectedFiber (lg21HiddenAccessBaseScoreLowerTailEvent threshold)
          publicBase) := by
  unfold lg21HiddenAccessScoreSelectedSkillKernel
  rw [Kernel.map_apply _ measurable_snd publicBase,
    Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ,
    selectedRestrictionKernel_apply
      (lg21HiddenAccessBaseScoreLowerTailEvent_measurable threshold hthreshold)]
  simp

theorem lg21HiddenAccessScoreRawFibreMass_measurable
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) :
    Measurable (lg21HiddenAccessScoreRawFibreMass
      (lg21HiddenAccessScoreSelectedSkillKernel joint threshold)
      noAccessMass accessMass) := by
  have hevent : MeasurableSet
      (lg21HiddenAccessBaseScoreLowerTailEvent threshold) :=
    lg21HiddenAccessBaseScoreLowerTailEvent_measurable threshold hthreshold
  have hselection : Measurable (fun publicBase : Base =>
      joint publicBase
        (selectedFiber (lg21HiddenAccessBaseScoreLowerTailEvent threshold)
          publicBase)) :=
    Kernel.measurable_kernel_prodMk_left hevent
  unfold lg21HiddenAccessScoreRawFibreMass
  simp_rw [lg21HiddenAccessScoreSelectedSkillKernel_apply_univ
    joint threshold hthreshold]
  exact measurable_const.add (measurable_const.mul hselection)

theorem lg21HiddenAccessScoreRawFibreMass_pos_of_noAccess
    {Base : Type*} [MeasurableSpace Base]
    (accessSelectedSkillKernel : Kernel Base ℝ)
    (noAccessMass accessMass : ENNReal) (hnoAccess : 0 < noAccessMass)
    (publicBase : Base) :
    0 < lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
      noAccessMass accessMass publicBase := by
  unfold lg21HiddenAccessScoreRawFibreMass
  exact lt_of_lt_of_le hnoAccess (le_add_of_nonneg_right bot_le)

theorem lg21HiddenAccessScoreRawFibreMass_ne_top
    {Base : Type*} [MeasurableSpace Base]
    (accessSelectedSkillKernel : Kernel Base ℝ) [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (publicBase : Base) :
    lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
      noAccessMass accessMass publicBase ≠ ⊤ := by
  unfold lg21HiddenAccessScoreRawFibreMass
  apply ENNReal.add_ne_top.mpr
  refine ⟨hnoAccessFinite, ENNReal.mul_ne_top haccessFinite ?_⟩
  exact measure_ne_top _ _

theorem lg21HiddenAccessScoreRawKernel_isFinite
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    IsFiniteKernel
      (lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass) := by
  letI : IsFiniteKernel (noAccessKernel.withDensity
      (fun _ _ => noAccessMass)) := by
    apply Kernel.isFiniteKernel_withDensity_of_bounded noAccessKernel
      hnoAccessFinite
    intro publicBase latentSkill
    simp
  letI : IsFiniteKernel (accessSelectedSkillKernel.withDensity
      (fun _ _ => accessMass)) := by
    apply Kernel.isFiniteKernel_withDensity_of_bounded accessSelectedSkillKernel
      haccessFinite
    intro publicBase latentSkill
    simp
  change IsFiniteKernel
    (noAccessKernel.withDensity (fun _ _ => noAccessMass) +
      accessSelectedSkillKernel.withDensity (fun _ _ => accessMass))
  exact inferInstance

/-- Normalize the literal raw score-selected kernel by its own positive
fibre mass.  Positive no-access mass rules out an arbitrary zero-fibre PBO. -/
noncomputable def lg21HiddenAccessScoreNormalizedKernel
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) : Kernel Base ℝ :=
  letI : IsFiniteKernel
      (lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass) :=
    lg21HiddenAccessScoreRawKernel_isFinite noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass hnoAccessFinite haccessFinite
  (lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
    noAccessMass accessMass).withDensity
      (fun publicBase _ =>
        (lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
          noAccessMass accessMass publicBase)⁻¹)

theorem lg21HiddenAccessScoreNormalizedKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (hfibreMass : Measurable (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass))
    (publicBase : Base) :
    lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
      hnoAccessFinite haccessFinite publicBase =
      (lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
        noAccessMass accessMass publicBase)⁻¹ •
        lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
          noAccessMass accessMass publicBase := by
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessScoreRawKernel_isFinite
        noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
        hnoAccessFinite haccessFinite)
  unfold lg21HiddenAccessScoreNormalizedKernel
  have hdensity : Measurable (Function.uncurry (fun (publicBase : Base) (_ : ℝ) =>
      (lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
        noAccessMass accessMass publicBase)⁻¹)) := by
    change Measurable (fun pair : Base × ℝ =>
      (lg21HiddenAccessScoreRawFibreMass accessSelectedSkillKernel
        noAccessMass accessMass pair.1)⁻¹)
    exact hfibreMass.inv.comp measurable_fst
  rw [Kernel.withDensity_apply _ hdensity,
    withDensity_const]

theorem lg21HiddenAccessScoreNormalizedKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (hfibreMass : Measurable (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass)) :
    IsMarkovKernel
      (lg21HiddenAccessScoreNormalizedKernel
        noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
        hnoAccessFinite haccessFinite) := by
  constructor
  intro publicBase
  apply IsProbabilityMeasure.mk
  rw [lg21HiddenAccessScoreNormalizedKernel_apply
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
    hnoAccessFinite haccessFinite hfibreMass publicBase,
    Measure.smul_apply,
    lg21HiddenAccessScoreRawKernel_apply_univ]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (lg21HiddenAccessScoreRawFibreMass_pos_of_noAccess
      accessSelectedSkillKernel noAccessMass accessMass hnoAccess publicBase))
    (lg21HiddenAccessScoreRawFibreMass_ne_top
      accessSelectedSkillKernel noAccessMass accessMass
      hnoAccessFinite haccessFinite publicBase)

/-- The raw score-selected mixture factorizes before normalization.  This
keeps the no-access component and the observed-score selected access
component separate in the source law. -/
theorem lg21HiddenAccessScoreRawKernel_compProd_eq_raw_mixture
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    baseLaw ⊗ₘ lg21HiddenAccessScoreRawKernel
      noAccessKernel accessSelectedSkillKernel noAccessMass accessMass =
      noAccessMass • (baseLaw ⊗ₘ noAccessKernel) +
        accessMass • (baseLaw ⊗ₘ accessSelectedSkillKernel) := by
  letI : IsFiniteKernel (noAccessKernel.withDensity
      (fun _ _ => noAccessMass)) := by
    apply Kernel.isFiniteKernel_withDensity_of_bounded noAccessKernel
      hnoAccessFinite
    intro publicBase latentSkill
    simp
  letI : IsFiniteKernel (accessSelectedSkillKernel.withDensity
      (fun _ _ => accessMass)) := by
    apply Kernel.isFiniteKernel_withDensity_of_bounded accessSelectedSkillKernel
      haccessFinite
    intro publicBase latentSkill
    simp
  change baseLaw ⊗ₘ
      (noAccessKernel.withDensity (fun _ _ => noAccessMass) +
        accessSelectedSkillKernel.withDensity (fun _ _ => accessMass)) = _
  rw [Measure.compProd_add_right,
    Measure.compProd_withDensity measurable_const,
    Measure.compProd_withDensity measurable_const,
    withDensity_const, withDensity_const]

/-- Reweighting the base marginal by the raw score-selected fibre mass and
then using its normalized conditional kernel recovers the unnormalized raw
candidate law exactly. -/
theorem lg21HiddenAccessScoreWeightedBase_compProd_normalizedKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (noAccessKernel accessSelectedSkillKernel : Kernel Base ℝ)
    [IsMarkovKernel noAccessKernel] [IsFiniteKernel accessSelectedSkillKernel]
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (hfibreMass : Measurable (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass)) :
    (baseLaw.withDensity (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass)) ⊗ₘ
        lg21HiddenAccessScoreNormalizedKernel
          noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
            hnoAccessFinite haccessFinite =
      baseLaw ⊗ₘ lg21HiddenAccessScoreRawKernel
        noAccessKernel accessSelectedSkillKernel noAccessMass accessMass := by
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
  let fibreMass := lg21HiddenAccessScoreRawFibreMass
    accessSelectedSkillKernel noAccessMass accessMass
  let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
      hnoAccessFinite haccessFinite
  let massLift : Base × ℝ -> ENNReal := fun baseSkill => fibreMass baseSkill.1
  let invMassLift : Base × ℝ -> ENNReal := fun baseSkill =>
    (fibreMass baseSkill.1)⁻¹
  have hmassLift : Measurable massLift :=
    hfibreMass.comp measurable_fst
  have hinvMassLift : Measurable invMassLift :=
    hfibreMass.inv.comp measurable_fst
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessScoreRawKernel_isFinite
        noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
        hnoAccessFinite haccessFinite)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel] using
      (lg21HiddenAccessScoreNormalizedKernel_isMarkov
        noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
        hnoAccess hnoAccessFinite haccessFinite hfibreMass)
  have hnormalizedKernel : normalizedKernel = rawKernel.withDensity
      (fun publicBase _ => (fibreMass publicBase)⁻¹) := by
    rfl
  letI : IsSFiniteKernel (rawKernel.withDensity
      (fun publicBase _ => (fibreMass publicBase)⁻¹)) := by
    rw [← hnormalizedKernel]
    infer_instance
  have hweightedRaw :
      (baseLaw.withDensity fibreMass) ⊗ₘ rawKernel =
        (baseLaw ⊗ₘ rawKernel).withDensity massLift := by
    simpa [massLift] using
      (compProd_withDensity_left (μ := baseLaw) (κ := rawKernel)
        hfibreMass)
  have hcancel : massLift * invMassLift = 1 := by
    funext baseSkill
    change fibreMass baseSkill.1 * (fibreMass baseSkill.1)⁻¹ = 1
    exact ENNReal.mul_inv_cancel
      (ne_of_gt (lg21HiddenAccessScoreRawFibreMass_pos_of_noAccess
        accessSelectedSkillKernel noAccessMass accessMass hnoAccess baseSkill.1))
      (lg21HiddenAccessScoreRawFibreMass_ne_top
        accessSelectedSkillKernel noAccessMass accessMass
        hnoAccessFinite haccessFinite baseSkill.1)
  change (baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel =
    baseLaw ⊗ₘ rawKernel
  calc
    (baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel =
        ((baseLaw.withDensity fibreMass) ⊗ₘ rawKernel).withDensity invMassLift := by
          rw [hnormalizedKernel, Measure.compProd_withDensity hinvMassLift]
    _ = ((baseLaw ⊗ₘ rawKernel).withDensity massLift).withDensity invMassLift := by
          rw [hweightedRaw]
    _ = (baseLaw ⊗ₘ rawKernel).withDensity (massLift * invMassLift) := by
          rw [withDensity_mul (baseLaw ⊗ₘ rawKernel) hmassLift hinvMassLift]
    _ = baseLaw ⊗ₘ rawKernel := by rw [hcancel, withDensity_one]

/-! ## Source transport of the score-selected component -/

/-- The all-take candidate's access `Y = 1, X = 0` event is exactly the
positive-access preimage of the lower-score event in the full public
score/skill observation. -/
theorem lg21HiddenAccessAllTakeMeanGap_accessTakeNoReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (gap : ℝ) :
    lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      {student | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21HiddenAccessBaseScoreLowerTailEvent
            (fun publicBase => baseMean publicBase + gap)) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨skill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessCandidateAccessTakeNoReportEvent,
      lg21HiddenAccessAllTake, lg21HiddenAccessMeanGapReport,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessStudentScore,
      lg21HiddenAccessBaseScoreSkillObservation,
      lg21HiddenAccessBaseScoreLowerTailEvent, not_le]

/-- The literal raw positive-access lower-score component transports to the
base-indexed selected score/skill kernel.  The source factorization is used
only as a measure equality; it does not identify an access-only law with the
candidate's public `X = 0` PBO. -/
theorem lg21HiddenAccessAllTakeMeanGap_accessTakeNoReportBaseSkillMeasure_eq_smul_selected
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      M.accessLaw {true} •
        (baseLaw ⊗ₘ lg21HiddenAccessScoreSelectedSkillKernel
          (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
          (fun publicBase => baseMean publicBase + gap)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseSkillObservation := lg21HiddenAccessBaseSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let lowerEvent := lg21HiddenAccessBaseScoreLowerTailEvent threshold
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let accessMass := M.accessLaw {true}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hrawProbability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hrawProbability
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hlowerEvent : MeasurableSet lowerEvent := by
    simpa [lowerEvent] using
      lg21HiddenAccessBaseScoreLowerTailEvent_measurable threshold hthreshold
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hbaseSkillObservation : Measurable baseSkillObservation := by
    simpa [baseSkillObservation] using
      lg21HiddenAccessBaseSkillObservation_measurable testFeature
  have hrawAccessMass : rawLaw accessEvent = accessMass := by
    rw [show accessEvent = ({true} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [accessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa [accessMass]
  have haccessMass_ne_zero : accessMass ≠ 0 := ne_of_gt haccess
  have haccessMass_ne_top : accessMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hrawAccessRestrict : rawLaw.restrict accessEvent = accessMass • accessLaw := by
    calc
      rawLaw.restrict accessEvent = (1 : ENNReal) • rawLaw.restrict accessEvent := by simp
      _ = (accessMass * accessMass⁻¹) • rawLaw.restrict accessEvent := by
        rw [ENNReal.mul_inv_cancel haccessMass_ne_zero haccessMass_ne_top]
      _ = accessMass • (accessMass⁻¹ • rawLaw.restrict accessEvent) := by
        rw [smul_smul]
      _ = accessMass • accessLaw := by
        congr 1
        simp [accessLaw, lg21ContinuousGaussianAccessPopulationLaw, rawLaw,
          accessEvent, lg21ContinuousPopulationAccess,
          lg21NormalizedRestriction, hrawAccessMass]
  have hrawLowerRestrict :
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' lowerEvent) =
        accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' lowerEvent)) := by
    calc
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' lowerEvent) =
          (rawLaw.restrict accessEvent).restrict
            (scoreSkillObservation ⁻¹' lowerEvent) := by
              rw [Measure.restrict_restrict]
              · rw [Set.inter_comm]
              · exact hlowerEvent.preimage hscoreSkillObservation
      _ = (accessMass • accessLaw).restrict
          (scoreSkillObservation ⁻¹' lowerEvent) := by
            rw [hrawAccessRestrict]
      _ = accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' lowerEvent)) := by
            rw [Measure.restrict_smul]
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  have haccessMapRestrict :
      (accessLaw.restrict (scoreSkillObservation ⁻¹' lowerEvent)).map
          baseSkillObservation =
        baseLaw ⊗ₘ lg21HiddenAccessScoreSelectedSkillKernel joint threshold := by
    calc
      (accessLaw.restrict (scoreSkillObservation ⁻¹' lowerEvent)).map
          baseSkillObservation =
          ((accessLaw.restrict (scoreSkillObservation ⁻¹' lowerEvent)).map
            scoreSkillObservation).map (Prod.map id Prod.snd) := by
              rw [Measure.map_map (by fun_prop) hscoreSkillObservation]
              rfl
      _ = ((accessLaw.map scoreSkillObservation).restrict lowerEvent).map
          (Prod.map id Prod.snd) := by
            rw [← Measure.restrict_map hscoreSkillObservation hlowerEvent]
      _ = ((baseLaw ⊗ₘ joint).restrict lowerEvent).map
          (Prod.map id Prod.snd) := by rw [haccessScoreSkill]
      _ = baseLaw ⊗ₘ lg21HiddenAccessScoreSelectedSkillKernel joint threshold := by
            symm
            unfold lg21HiddenAccessScoreSelectedSkillKernel
            exact compProd_selectedRestrictionKernel_map_snd hlowerEvent
  change (rawLaw.restrict
      (lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))).map
      baseSkillObservation = _
  rw [lg21HiddenAccessAllTakeMeanGap_accessTakeNoReportEvent_eq_access_inter_preimage]
  calc
    (rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' lowerEvent)).map
        baseSkillObservation =
        (accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' lowerEvent))).map baseSkillObservation := by
            rw [hrawLowerRestrict]
    _ = accessMass •
        ((accessLaw.restrict (scoreSkillObservation ⁻¹' lowerEvent)).map
          baseSkillObservation) := by rw [Measure.map_smul]
    _ = accessMass •
        (baseLaw ⊗ₘ lg21HiddenAccessScoreSelectedSkillKernel joint threshold) := by
          rw [haccessMapRestrict]

/-- Before normalizing the candidate report branch, its literal raw source
measure is exactly the positive-access mass times the Gaussian public
upper-tail restriction.  This is only a transport of measures; it does not
replace the candidate's raw `X = 0` PBO by an access-conditioned one. -/
theorem lg21HiddenAccessAllTakeMeanGap_reportBaseScoreSkillMeasure_eq_smul_upperRestriction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    (lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap)) |>.map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      M.accessLaw {true} •
        ((baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance).restrict
          (lg21HiddenAccessBaseScoreUpperTailEvent
            (fun publicBase => baseMean publicBase + gap))) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let upperEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let accessMass := M.accessLaw {true}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hrawProbability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hrawProbability
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hupperEvent : MeasurableSet upperEvent := by
    simpa [upperEvent] using
      lg21HiddenAccessBaseScoreUpperTailEvent_measurable threshold hthreshold
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hrawAccessMass : rawLaw accessEvent = accessMass := by
    rw [show accessEvent = ({true} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [accessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa [accessMass]
  have haccessMass_ne_zero : accessMass ≠ 0 := ne_of_gt haccess
  have haccessMass_ne_top : accessMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hrawAccessRestrict : rawLaw.restrict accessEvent = accessMass • accessLaw := by
    calc
      rawLaw.restrict accessEvent = (1 : ENNReal) • rawLaw.restrict accessEvent := by simp
      _ = (accessMass * accessMass⁻¹) • rawLaw.restrict accessEvent := by
        rw [ENNReal.mul_inv_cancel haccessMass_ne_zero haccessMass_ne_top]
      _ = accessMass • (accessMass⁻¹ • rawLaw.restrict accessEvent) := by
        rw [smul_smul]
      _ = accessMass • accessLaw := by
        congr 1
        simp [accessLaw, lg21ContinuousGaussianAccessPopulationLaw, rawLaw,
          accessEvent, lg21ContinuousPopulationAccess,
          lg21NormalizedRestriction, hrawAccessMass]
  have hrawUpperRestrict :
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' upperEvent) =
        accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' upperEvent)) := by
    calc
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' upperEvent) =
          (rawLaw.restrict accessEvent).restrict
            (scoreSkillObservation ⁻¹' upperEvent) := by
              rw [Measure.restrict_restrict]
              · rw [Set.inter_comm]
              · exact hupperEvent.preimage hscoreSkillObservation
      _ = (accessMass • accessLaw).restrict
          (scoreSkillObservation ⁻¹' upperEvent) := by
            rw [hrawAccessRestrict]
      _ = accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' upperEvent)) := by
            rw [Measure.restrict_smul]
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  have haccessMapRestrict :
      (accessLaw.restrict (scoreSkillObservation ⁻¹' upperEvent)).map
          scoreSkillObservation =
        (baseLaw ⊗ₘ joint).restrict upperEvent := by
    calc
      (accessLaw.restrict (scoreSkillObservation ⁻¹' upperEvent)).map
          scoreSkillObservation =
          (accessLaw.map scoreSkillObservation).restrict upperEvent := by
            rw [← Measure.restrict_map hscoreSkillObservation hupperEvent]
      _ = (baseLaw ⊗ₘ joint).restrict upperEvent := by rw [haccessScoreSkill]
  change (rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))).map
      scoreSkillObservation =
      accessMass • ((baseLaw ⊗ₘ joint).restrict upperEvent)
  rw [lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq_access_inter_preimage]
  calc
    (rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' upperEvent)).map
        scoreSkillObservation =
        (accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' upperEvent))).map scoreSkillObservation := by
            rw [hrawUpperRestrict]
    _ = accessMass •
        ((accessLaw.restrict (scoreSkillObservation ⁻¹' upperEvent)).map
          scoreSkillObservation) := by rw [Measure.map_smul]
    _ = accessMass • ((baseLaw ⊗ₘ joint).restrict upperEvent) := by
          rw [haccessMapRestrict]

/-- The literal all-take/high-score candidate has a positive report branch
whenever access has positive source mass.  Positivity comes from the actual
raw action event, then from every Gaussian upper-score fibre. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawCandidateReport_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let upperEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let accessMass := M.accessLaw {true}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hupperPositive : 0 < (baseLaw ⊗ₘ joint) upperEvent := by
    simpa [joint, upperEvent] using
      (lg21HiddenAccessGaussian_selectedUpperTail_positive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold
        (by simpa [threshold] using hbaseMean.add measurable_const))
  have htransport :=
    lg21HiddenAccessAllTakeMeanGap_reportBaseScoreSkillMeasure_eq_smul_upperRestriction
      M haccess testFeature baseLaw baseMean hbaseMean gap
      baseVariance noiseVariance hsourceFactor
  have hmass : rawLaw reportEvent = accessMass * (baseLaw ⊗ₘ joint) upperEvent := by
    have htransportUniv := congrArg (fun measure => measure Set.univ) htransport
    simpa [rawLaw, scoreSkillObservation, reportEvent, accessMass,
      joint, upperEvent, Measure.map_apply hscoreSkillObservation
        MeasurableSet.univ, Measure.restrict_apply_univ] using htransportUniv
  rw [hmass]
  exact ENNReal.mul_pos (ne_of_gt haccess) (ne_of_gt hupperPositive)

/-- After normalizing the literal raw report action, forgetting hidden access
gives exactly the Gaussian law selected by the same public upper-tail event.
The equality is a law transport, not a replacement of the raw candidate
population by an access-labelled PBO. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawCandidateReportBaseScoreSkillLaw_eq_normalizedUpperTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21HiddenAccessBaseScoreUpperTailEvent
          (fun publicBase => baseMean publicBase + gap)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let upperEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hupperEvent : MeasurableSet upperEvent := by
    simpa [upperEvent] using
      lg21HiddenAccessBaseScoreUpperTailEvent_measurable threshold hthreshold
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have haccessLaw : accessLaw = lg21NormalizedRestriction rawLaw accessEvent := by
    rfl
  have hreportEvent : reportEvent =
      accessEvent ∩ scoreSkillObservation ⁻¹' upperEvent := by
    simpa [reportEvent, accessEvent, scoreSkillObservation, upperEvent, threshold] using
      (lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature baseMean gap)
  have hnormalizedRaw :
      lg21NormalizedRestriction rawLaw reportEvent =
        lg21NormalizedRestriction accessLaw
          (scoreSkillObservation ⁻¹' upperEvent) := by
    calc
      lg21NormalizedRestriction rawLaw reportEvent =
          lg21NormalizedRestriction rawLaw
            (accessEvent ∩ scoreSkillObservation ⁻¹' upperEvent) := by rw [hreportEvent]
      _ = lg21NormalizedRestriction
          (lg21NormalizedRestriction rawLaw accessEvent)
            (scoreSkillObservation ⁻¹' upperEvent) := by
              symm
              exact lg21_normalizedRestriction_normalizedRestriction_eq_inter
                rawLaw accessEvent (scoreSkillObservation ⁻¹' upperEvent)
                haccessEvent (hupperEvent.preimage hscoreSkillObservation)
      _ = lg21NormalizedRestriction accessLaw
          (scoreSkillObservation ⁻¹' upperEvent) := by rw [haccessLaw]
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  change (lg21NormalizedRestriction rawLaw reportEvent).map scoreSkillObservation =
    lg21NormalizedRestriction (baseLaw ⊗ₘ joint) upperEvent
  rw [hnormalizedRaw]
  calc
    (lg21NormalizedRestriction accessLaw
      (scoreSkillObservation ⁻¹' upperEvent)).map scoreSkillObservation =
        lg21NormalizedRestriction (accessLaw.map scoreSkillObservation) upperEvent := by
          exact lg21_normalizedRestriction_map_preimage accessLaw
            scoreSkillObservation hscoreSkillObservation upperEvent hupperEvent
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ joint) upperEvent := by
          rw [haccessScoreSkill]

/-- Forgetting the observed score in the full score/skill Gaussian source
factorization recovers the same full base/skill source law that appears in
the literal no-access component. -/
theorem lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
      baseLaw ⊗ₘ
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance).map Prod.snd := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseSkillObservation := lg21HiddenAccessBaseSkillObservation testFeature
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have haccessBaseSkill : accessLaw.map baseSkillObservation =
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
    simpa [accessLaw, baseSkillObservation] using
      (lg21ContinuousGaussianAccessPopulation_base_skill_law M haccess testFeature)
  have hrawScoreSkill : rawLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := hrawScoreSkill
  calc
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        accessLaw.map baseSkillObservation := haccessBaseSkill.symm
    _ = (accessLaw.map scoreSkillObservation).map (Prod.map id Prod.snd) := by
          symm
          rw [Measure.map_map (by fun_prop) hscoreSkillObservation]
          rfl
    _ = (baseLaw ⊗ₘ joint).map (Prod.map id Prod.snd) := by
          rw [haccessScoreSkill]
    _ = baseLaw ⊗ₘ joint.map Prod.snd := by
          exact map_compProd_eq_compProd_map measurable_snd

/-- The latent-skill marginal of the score/skill Gaussian joint kernel is
the original full-base Gaussian skill law. -/
theorem lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ) (publicBase : Base) :
    (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance publicBase).map Prod.snd =
      gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
  rw [gaussianSignalJointKernel_apply]
  let primitive := gaussianSignalPair
    (baseMean publicBase) baseVariance noiseVariance
  let scoreSkill : ℝ × ℝ -> ℝ × ℝ :=
    fun pair => (gaussianSignalScore pair, pair.1)
  have hscoreSkill : Measurable scoreSkill := by
    dsimp [scoreSkill]
    fun_prop
  calc
    (primitive.map scoreSkill).map Prod.snd =
        primitive.map (Prod.snd ∘ scoreSkill) := by
          rw [Measure.map_map measurable_snd hscoreSkill]
    _ = primitive.map Prod.fst := by rfl
    _ = gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
      change Measure.map Prod.fst
        ((gaussianReal (baseMean publicBase) baseVariance.toNNReal).prod
          (gaussianReal 0 noiseVariance.toNNReal)) = _
      rw [Measure.map_fst_prod]
      simp

/-- Exact normalized base/skill law of the literal all-take/high-score
candidate's public no-report branch.  The right hand side is the raw
two-component kernel before conditioning: all no-access students and the
observed-score-selected access students. -/
theorem lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_eq_normalized_scoreRawKernel
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature)
          (lg21HiddenAccessMeanGapReport testFeature baseMean gap)))⁻¹ •
        (baseLaw ⊗ₘ lg21HiddenAccessScoreRawKernel
          ((gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance).map Prod.snd)
          (lg21HiddenAccessScoreSelectedSkillKernel
            (gaussianSignalJointKernel
              baseMean hbaseMean baseVariance noiseVariance)
            (fun publicBase => baseMean publicBase + gap))
          (M.accessLaw {false}) (M.accessLaw {true})) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateTake := lg21HiddenAccessAllTake testFeature
  let candidateReport := lg21HiddenAccessMeanGapReport testFeature baseMean gap
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  let noAccessKernel := joint.map Prod.snd
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  let accessSelectedSkillKernel :=
    lg21HiddenAccessScoreSelectedSkillKernel joint threshold
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true})
  have htakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2) := by
    simpa [candidateTake] using lg21HiddenAccessAllTake_measurable testFeature
  have hreportMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2) := by
    simpa [candidateReport] using
      lg21HiddenAccessMeanGapReport_measurable testFeature baseMean hbaseMean gap
  have hnoTakeComponent :
      lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure M testFeature
        candidateTake = 0 := by
    unfold lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure
    rw [show lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake = ∅ by
      simpa [candidateTake] using
        lg21HiddenAccessAllTake_candidateAccessNoTakeEvent_eq_empty testFeature]
    simp
  have hnoAccessComponent :
      lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature =
        M.accessLaw {false} • (baseLaw ⊗ₘ noAccessKernel) := by
    calc
      lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature =
          M.accessLaw {false} •
            lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature :=
        lg21HiddenAccessNoAccessBaseSkillMeasure_eq_smul_fullBaseLatent
          M hnoAccess testFeature
      _ = M.accessLaw {false} • (baseLaw ⊗ₘ noAccessKernel) := by
        rw [show lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
            baseLaw ⊗ₘ noAccessKernel by
          simpa [noAccessKernel, joint] using
            (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
              M haccess testFeature baseLaw baseMean hbaseMean
              baseVariance noiseVariance hsourceFactor)]
  have hselectedComponent :
      lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure M testFeature
        candidateTake candidateReport =
        M.accessLaw {true} •
          (baseLaw ⊗ₘ accessSelectedSkillKernel) := by
    simpa [candidateTake, candidateReport, accessSelectedSkillKernel,
      joint, threshold] using
      (lg21HiddenAccessAllTakeMeanGap_accessTakeNoReportBaseSkillMeasure_eq_smul_selected
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor)
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    exact measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    exact measure_ne_top _ _
  change lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      candidateTake candidateReport = (rawLaw noReportEvent)⁻¹ •
        (baseLaw ⊗ₘ rawKernel)
  rw [lg21HiddenAccessRawCandidate_noReportBaseSkillLaw_eq_normalized_components
    M testFeature candidateTake candidateReport htakeMeasurable hreportMeasurable,
    hnoAccessComponent, hnoTakeComponent, hselectedComponent]
  simp only [add_zero]
  rw [← lg21HiddenAccessScoreRawKernel_compProd_eq_raw_mixture
    baseLaw noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite]

/-! ## Fibrewise PBO inequalities -/

/-- The no-access component retains the conditional base mean.  At a score
one positive gap above that mean, the genuine Gaussian report posterior is
strictly higher.  This is the first component of the raw `X = 0` comparison. -/
theorem lg21HiddenAccessAllTakeMeanGap_noAccessMean_lt_reportedAtThreshold
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ) (hgap : 0 < gap) (publicBase : Base) :
    (∫ skill, skill ∂gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal publicBase) <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase
          (baseMean publicBase + gap) := by
  rw [lg21_gaussianLocationKernel_skill_mean,
    lg21_optional_rawGaussianPosteriorMean_eq_affine]
  have hden : 0 < baseVariance + noiseVariance := by linarith
  have hden_ne : baseVariance + noiseVariance ≠ 0 := ne_of_gt hden
  have hweight : 0 < gaussianSignalWeight baseVariance noiseVariance :=
    gaussianSignalWeight_pos hbaseVariance hnoiseVariance
  change baseMean publicBase <
    baseVariance / (baseVariance + noiseVariance) *
        (baseMean publicBase + gap) +
      noiseVariance / (baseVariance + noiseVariance) * baseMean publicBase
  field_simp [hden_ne]
  nlinarith

/-- Exact fibrewise no-report PBO formula for the all-take score-cutoff
candidate.  The first component is the full no-access Gaussian law; the
second is the literal access population selected by the observed lower-score
event.  This equality is the semantic bridge to a scalar cutoff equation,
without discarding either source component. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawMixtureMean_eq
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (publicBase : Base) :
    let anchor := baseMean publicBase + gap
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let lowerMass := joint publicBase
      (selectedFiber (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
        publicBase)
    let noAccessLaw := gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal publicBase
    let accessLowerLaw :=
      (lg21OptionalFullBaseSelectedNoReportKernel
        baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map Prod.snd
    (∫ skill, skill ∂
      ((noAccessMass + accessMass * lowerMass)⁻¹ •
        (noAccessMass • noAccessLaw +
          (accessMass * lowerMass) • accessLowerLaw))) =
      (noAccessMass.toReal + (accessMass * lowerMass).toReal)⁻¹ *
        (noAccessMass.toReal * baseMean publicBase +
          (accessMass * lowerMass).toReal *
            lg21OptionalFullBaseNoReportValue
              baseMean hbaseMean baseVariance noiseVariance anchor publicBase) := by
  intro anchor joint lowerMass noAccessLaw accessLowerLaw
  let selected := lg21OptionalFullBaseSelectedNoReportKernel
    baseMean hbaseMean baseVariance noiseVariance anchor
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let κ := gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel joint := by
    dsimp [joint]
    exact gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel κ := by
    dsimp [κ]
    exact gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance.toNNReal
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor)
  have hselectionPositive : ∀ base,
      selectionMass joint event base ≠ 0 := by
    intro base
    exact ne_of_gt
      (lg21_optional_fullBaseGaussian_noReport_fibre_positive
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor base)
  letI : IsMarkovKernel selected := by
    dsimp [selected]
    exact selectedNormalizedKernel_isMarkov hevent hselectionPositive
  let μ₀ : Measure ℝ := κ publicBase
  let μ₁ : Measure ℝ := (selected publicBase).map Prod.snd
  letI : IsProbabilityMeasure μ₀ := by
    dsimp [μ₀]
    infer_instance
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hlowerMassFinite : lowerMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hweight₁Finite : accessMass * lowerMass ≠ ⊤ := by
    exact ENNReal.mul_ne_top haccessFinite hlowerMassFinite
  have hintegrable₀ : Integrable (fun skill : ℝ => skill) μ₀ := by
    simpa [μ₀, κ] using
      (lg21_gaussianLocationKernel_skill_integrable
        baseMean hbaseMean baseVariance.toNNReal publicBase)
  have hintegrableSelected : Integrable Prod.snd (selected publicBase) := by
    rw [show selected publicBase =
        lg21NormalizedRestriction (joint publicBase)
          (selectedFiber event publicBase) by
          change selectedNormalizedKernel joint event publicBase = _
          rw [selectedNormalizedKernel_apply hevent]]
    rw [show joint publicBase =
        gaussianReal (baseMean publicBase)
          (baseVariance + noiseVariance).toNNReal ⊗ₘ
          Kernel.sectR (gaussianSignalPosteriorBaseKernel
            baseMean hbaseMean baseVariance noiseVariance) publicBase by
          dsimp [joint]
          exact lg21_optional_fullBaseGaussian_jointKernel_apply
            baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance publicBase]
    rw [show selectedFiber event publicBase =
        lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ by
          simpa [event] using
            (lg21OptionalFullBaseNoReportEvent_selectedFiber (Base := Base)
              anchor publicBase)]
    exact lg21_optional_canonicalGaussianScorePosterior_lowerTail_integrable
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase anchor
  have hintegrable₁ : Integrable (fun skill : ℝ => skill) μ₁ := by
    apply (integrable_map_measure
      stronglyMeasurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mpr
    simpa [Function.comp_def, μ₁] using hintegrableSelected
  have hmean₀ : (∫ skill, skill ∂μ₀) = baseMean publicBase := by
    simpa [μ₀, κ] using
      (lg21_gaussianLocationKernel_skill_mean
        baseMean hbaseMean baseVariance.toNNReal publicBase)
  have hmean₁ : (∫ skill, skill ∂μ₁) =
      lg21OptionalFullBaseNoReportValue
        baseMean hbaseMean baseVariance noiseVariance anchor publicBase := by
    calc
      (∫ skill, skill ∂μ₁) = ∫ scoreSkill, scoreSkill.2 ∂selected publicBase := by
        simpa [μ₁] using (integral_map_of_stronglyMeasurable
          (μ := selected publicBase) (φ := Prod.snd)
          measurable_snd
          ((measurable_id : Measurable (fun skill : ℝ => skill)).stronglyMeasurable))
      _ = lg21OptionalFullBaseNoReportValue
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase := by
        symm
        exact lg21_optional_fullBaseNoReportValue_eq_selectedKernelMean
          baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor publicBase
  have hformula := lg21_normalizedTwoComponentMean_eq
    μ₀ μ₁ (fun skill : ℝ => skill)
    noAccessMass (accessMass * lowerMass)
    hnoAccessFinite hweight₁Finite hintegrable₀ hintegrable₁
  rw [hmean₀, hmean₁] at hformula
  simpa [μ₀, μ₁, noAccessLaw, accessLowerLaw, κ, selected,
    lowerMass, joint, event] using hformula

/-- Exact mean of the normalized literal score-selected `X = 0` kernel.
This is the kernel used by the all-take cutoff candidate itself, not an
access-only proxy. -/
theorem lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_eq_rawMixture
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (publicBase : Base)
    (hjoint : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance)) :
    let anchor := baseMean publicBase + gap
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let lowerMass := joint publicBase
      (selectedFiber (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
        publicBase)
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel joint
        (fun base => baseMean base + gap)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel_isFinite joint
        (fun base => baseMean base + gap)
    (∫ skill, skill ∂lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass hnoAccessFinite haccessFinite publicBase) =
      (noAccessMass.toReal + (accessMass * lowerMass).toReal)⁻¹ *
        (noAccessMass.toReal * baseMean publicBase +
          (accessMass * lowerMass).toReal *
            lg21OptionalFullBaseNoReportValue
              baseMean hbaseMean baseVariance noiseVariance anchor publicBase) := by
  intro anchor joint lowerMass noAccessKernel accessSelectedSkillKernel
  letI : IsMarkovKernel joint := by
    simpa [joint] using hjoint
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  let threshold : Base -> ℝ := fun base => baseMean base + gap
  let event := lg21HiddenAccessBaseScoreLowerTailEvent threshold
  let constantEvent := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let noAccessLaw := gaussianLocationKernel
    baseMean hbaseMean baseVariance.toNNReal publicBase
  let accessLowerLaw :=
    (lg21OptionalFullBaseSelectedNoReportKernel
      baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map Prod.snd
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hevent : MeasurableSet event := by
    simpa [event] using
      lg21HiddenAccessBaseScoreLowerTailEvent_measurable threshold hthreshold
  have hconstantEvent : MeasurableSet constantEvent := by
    simpa [constantEvent] using
      lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have hselectedFiber : selectedFiber event publicBase =
      selectedFiber constantEvent publicBase := by
    ext scoreSkill
    simp [event, constantEvent, threshold, anchor,
      selectedFiber, lg21HiddenAccessBaseScoreLowerTailEvent,
      lg21OptionalFullBaseNoReportEvent]
  have hlowerMass : 0 < lowerMass := by
    change 0 < joint publicBase (selectedFiber event publicBase)
    rw [hselectedFiber]
    simpa [joint, constantEvent] using
      (lg21_optional_fullBaseGaussian_noReport_fibre_positive
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase)
  have hselectedUniv : accessSelectedSkillKernel publicBase Set.univ = lowerMass := by
    rw [show accessSelectedSkillKernel =
        lg21HiddenAccessScoreSelectedSkillKernel joint threshold by rfl,
      lg21HiddenAccessScoreSelectedSkillKernel_apply_univ
        joint threshold hthreshold publicBase]
    rw [hselectedFiber]
  have hnoAccessLaw : noAccessKernel publicBase = noAccessLaw := by
    calc
      noAccessKernel publicBase = (joint publicBase).map Prod.snd := by
        rw [show noAccessKernel = joint.map Prod.snd by rfl,
          Kernel.map_apply joint measurable_snd publicBase]
      _ = gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
        simpa [joint] using
          (lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
            baseMean hbaseMean baseVariance noiseVariance publicBase)
      _ = noAccessLaw := by
        symm
        exact gaussianLocationKernel_apply
          baseMean hbaseMean baseVariance.toNNReal publicBase
  have hselectedNormalized :
      lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase =
        lg21NormalizedRestriction (joint publicBase)
          (selectedFiber constantEvent publicBase) := by
    change selectedNormalizedKernel joint constantEvent publicBase = _
    rw [selectedNormalizedKernel_apply hconstantEvent]
  have hrestricted : lowerMass •
      lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase =
        (joint publicBase).restrict (selectedFiber event publicBase) := by
    rw [hselectedNormalized, ← hselectedFiber]
    exact lg21_smul_normalizedRestriction_eq_restrict
      (joint publicBase) (selectedFiber event publicBase) hlowerMass
  have haccessSelected : accessSelectedSkillKernel publicBase =
      lowerMass • accessLowerLaw := by
    change (selectedRestrictionKernel joint event).map Prod.snd publicBase = _
    rw [Kernel.map_apply _ measurable_snd publicBase,
      selectedRestrictionKernel_apply hevent]
    calc
      ((joint publicBase).restrict (selectedFiber event publicBase)).map Prod.snd =
          (lowerMass •
            lg21OptionalFullBaseSelectedNoReportKernel
              baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map
            Prod.snd := by rw [hrestricted]
      _ = lowerMass • accessLowerLaw := by
        rw [Measure.map_smul]
  have hfibreMass : Measurable (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass) := by
    simpa [accessSelectedSkillKernel, joint, threshold] using
      (lg21HiddenAccessScoreRawFibreMass_measurable
        joint noAccessMass accessMass threshold hthreshold)
  have hrawKernel :
      lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass publicBase =
        noAccessMass • noAccessLaw +
          (accessMass * lowerMass) • accessLowerLaw := by
    rw [lg21HiddenAccessScoreRawKernel_apply, hnoAccessLaw, haccessSelected,
      ← smul_smul]
  have hrawFibreMass : lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass publicBase =
      noAccessMass + accessMass * lowerMass := by
    unfold lg21HiddenAccessScoreRawFibreMass
    rw [hselectedUniv]
  rw [lg21HiddenAccessScoreNormalizedKernel_apply
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
    hnoAccessFinite haccessFinite hfibreMass publicBase,
    hrawKernel, hrawFibreMass]
  simpa [joint, threshold, event, anchor, constantEvent, lowerMass,
    noAccessLaw, accessLowerLaw, noAccessKernel,
    accessSelectedSkillKernel,
    lg21HiddenAccessBaseScoreLowerTailEvent,
    lg21OptionalFullBaseNoReportEvent, selectedFiber] using
    (lg21HiddenAccessAllTakeMeanGap_rawMixtureMean_eq
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite gap publicBase)

/-- The literal normalized hidden-access no-report kernel is exactly the
source's scalar optional-report mixture at the candidate cutoff.  The
identification uses the actual Gaussian score-selection mass and the Boolean
source-law complement relation; it is not a redefinition of the PBO. -/
theorem lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_eq_optionalNoReportMixture
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessComplement : noAccessMass.toReal = 1 - accessMass.toReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (publicBase : Base)
    (hjoint : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance)) :
    let scoreVariance := baseVariance + noiseVariance
    let scoreLaw := lg21HiddenAccessGaussianScoreLaw
      (baseMean publicBase) scoreVariance (by linarith)
    let anchor := baseMean publicBase + gap
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel joint
        (fun base => baseMean base + gap)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel_isFinite joint
        (fun base => baseMean base + gap)
    (∫ skill, skill ∂lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass hnoAccessFinite haccessFinite publicBase) =
      lg21OptionalNoReportMixtureEstimate
        accessMass.toReal (baseMean publicBase) scoreLaw
        (fun cutoff => lg21OptionalFullBaseNoReportValue
          baseMean hbaseMean baseVariance noiseVariance cutoff publicBase)
        anchor := by
  intro scoreVariance scoreLaw anchor joint noAccessKernel accessSelectedSkillKernel
  letI : IsMarkovKernel joint := by
    simpa [joint] using hjoint
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  let lowerMass := joint publicBase
    (selectedFiber (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
      publicBase)
  have hraw :
      (∫ skill, skill ∂lg21HiddenAccessScoreNormalizedKernel
        noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass hnoAccessFinite haccessFinite publicBase) =
        (noAccessMass.toReal + (accessMass * lowerMass).toReal)⁻¹ *
          (noAccessMass.toReal * baseMean publicBase +
            (accessMass * lowerMass).toReal *
              lg21OptionalFullBaseNoReportValue
                baseMean hbaseMean baseVariance noiseVariance anchor publicBase) := by
    simpa [lowerMass, anchor, joint, noAccessKernel,
      accessSelectedSkillKernel] using
      (lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_eq_rawMixture
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessFinite haccessFinite gap publicBase hjoint)
  have hlowerMass : lowerMass.toReal =
      standardGaussianCDFAPI.normalCDF scoreLaw anchor := by
    simpa [lowerMass, scoreLaw, scoreVariance, anchor, joint] using
      (lg21HiddenAccessGaussianSignal_lowerScoreMass_toReal_eq_normalCDF
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase)
  have hweightedMass : (accessMass * lowerMass).toReal =
      accessMass.toReal * standardGaussianCDFAPI.normalCDF scoreLaw anchor := by
    rw [ENNReal.toReal_mul, hlowerMass]
  rw [hraw, hweightedMass, hnoAccessComplement]
  simp only [lg21OptionalNoReportMixtureEstimate]
  rw [div_eq_mul_inv]
  ring

/-- At one public base, the literal all-access/high-score candidate's raw
no-report fibre is a normalized mixture of the unselected no-access Gaussian
law and the access lower-score selected law.  Both component means lie below
the report posterior at the threshold, so the raw mixture does too.  The
statement is deliberately fibrewise: the later RCD bridge must still identify
this explicit kernel with the candidate's actual public `X = 0` law. -/
theorem lg21HiddenAccessAllTakeMeanGap_rawMixtureMean_lt_reportedAtThreshold
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessMass : 0 < noAccessMass) (haccessMass : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (hgap : 0 < gap) (publicBase : Base) :
    let anchor := baseMean publicBase + gap
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let lowerMass := joint publicBase
      (selectedFiber (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
        publicBase)
    let noAccessLaw := gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal publicBase
    let accessLowerLaw :=
      (lg21OptionalFullBaseSelectedNoReportKernel
        baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map Prod.snd
    (∫ skill, skill ∂
      ((noAccessMass + accessMass * lowerMass)⁻¹ •
        (noAccessMass • noAccessLaw +
          (accessMass * lowerMass) • accessLowerLaw))) <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase anchor := by
  intro anchor joint lowerMass noAccessLaw accessLowerLaw
  let selected := lg21OptionalFullBaseSelectedNoReportKernel
    baseMean hbaseMean baseVariance noiseVariance anchor
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let κ := gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel joint := by
    dsimp [joint]
    exact gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel κ := by
    dsimp [κ]
    exact gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance.toNNReal
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor)
  have hselectionPositive : ∀ base,
      selectionMass joint event base ≠ 0 := by
    intro base
    exact ne_of_gt
      (lg21_optional_fullBaseGaussian_noReport_fibre_positive
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor base)
  letI : IsMarkovKernel selected := by
    dsimp [selected]
    exact selectedNormalizedKernel_isMarkov hevent hselectionPositive
  let μ₀ : Measure ℝ := κ publicBase
  let μ₁ : Measure ℝ := (selected publicBase).map Prod.snd
  letI : IsProbabilityMeasure μ₀ := by
    dsimp [μ₀]
    infer_instance
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  have hlowerMass : 0 < lowerMass := by
    change 0 < joint publicBase (selectedFiber event publicBase)
    exact lg21_optional_fullBaseGaussian_noReport_fibre_positive
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  have hlowerMassFinite : lowerMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hweight₁ : 0 < accessMass * lowerMass := by
    exact ENNReal.mul_pos (ne_of_gt haccessMass) (ne_of_gt hlowerMass)
  have hweight₁Finite : accessMass * lowerMass ≠ ⊤ := by
    exact ENNReal.mul_ne_top haccessFinite hlowerMassFinite
  have hintegrable₀ : Integrable (fun skill : ℝ => skill) μ₀ := by
    simpa [μ₀, κ] using
      (lg21_gaussianLocationKernel_skill_integrable
        baseMean hbaseMean baseVariance.toNNReal publicBase)
  have hintegrableSelected : Integrable Prod.snd (selected publicBase) := by
    rw [show selected publicBase =
        lg21NormalizedRestriction (joint publicBase)
          (selectedFiber event publicBase) by
          change selectedNormalizedKernel joint event publicBase = _
          rw [selectedNormalizedKernel_apply hevent]]
    rw [show joint publicBase =
        gaussianReal (baseMean publicBase)
          (baseVariance + noiseVariance).toNNReal ⊗ₘ
          Kernel.sectR (gaussianSignalPosteriorBaseKernel
            baseMean hbaseMean baseVariance noiseVariance) publicBase by
          dsimp [joint]
          exact lg21_optional_fullBaseGaussian_jointKernel_apply
            baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance publicBase]
    rw [show selectedFiber event publicBase =
        lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ by
          simpa [event] using
            (lg21OptionalFullBaseNoReportEvent_selectedFiber (Base := Base)
              anchor publicBase)]
    exact lg21_optional_canonicalGaussianScorePosterior_lowerTail_integrable
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase anchor
  have hintegrable₁ : Integrable (fun skill : ℝ => skill) μ₁ := by
    apply (integrable_map_measure
      stronglyMeasurable_id.aestronglyMeasurable measurable_snd.aemeasurable).mpr
    simpa [Function.comp_def, μ₁] using hintegrableSelected
  have hmean₀ : (∫ skill, skill ∂μ₀) <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase anchor := by
    simpa [μ₀, κ, anchor] using
      (lg21HiddenAccessAllTakeMeanGap_noAccessMean_lt_reportedAtThreshold
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance gap hgap publicBase)
  have hmean₁ : (∫ skill, skill ∂μ₁) <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase anchor := by
    calc
      (∫ skill, skill ∂μ₁) = ∫ scoreSkill, scoreSkill.2 ∂selected publicBase := by
        simpa [μ₁] using (integral_map_of_stronglyMeasurable
          (μ := selected publicBase) (φ := Prod.snd)
          measurable_snd
          ((measurable_id : Measurable (fun skill : ℝ => skill)).stronglyMeasurable))
      _ = lg21OptionalFullBaseNoReportValue
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase := by
        symm
        exact lg21_optional_fullBaseNoReportValue_eq_selectedKernelMean
          baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor publicBase
      _ < lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase anchor := by
        exact lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
          baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor publicBase
  simpa [μ₀, μ₁, noAccessLaw, accessLowerLaw, κ, selected,
    lowerMass, joint, event] using
    (lg21_normalizedTwoComponentMean_lt_upper
      μ₀ μ₁ (fun skill : ℝ => skill)
      (lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase anchor)
      noAccessMass (accessMass * lowerMass)
      hnoAccessMass hweight₁ hnoAccessFinite hweight₁Finite
      hintegrable₀ hintegrable₁ hmean₀ hmean₁)

/-- The actual normalized raw score-selected no-report kernel has mean
strictly below the Gaussian reported posterior at its own threshold.  The
proof first exposes the literal score-selected fibre and only then invokes
the two-component mixture inequality. -/
theorem lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_lt_reportedAtThreshold
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessMass : 0 < noAccessMass) (haccessMass : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (hgap : 0 < gap) (publicBase : Base)
    (hjoint : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance)) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel joint
        (fun base => baseMean base + gap)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel_isFinite joint
        (fun base => baseMean base + gap)
    (∫ skill, skill ∂lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass hnoAccessFinite haccessFinite publicBase) <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase
          (baseMean publicBase + gap) := by
  intro joint noAccessKernel accessSelectedSkillKernel
  letI : IsMarkovKernel joint := by
    simpa [joint] using hjoint
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  let threshold : Base -> ℝ := fun base => baseMean base + gap
  let event := lg21HiddenAccessBaseScoreLowerTailEvent threshold
  let anchor := baseMean publicBase + gap
  let constantEvent := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let lowerMass : ENNReal := joint publicBase (selectedFiber event publicBase)
  let noAccessLaw := gaussianLocationKernel
    baseMean hbaseMean baseVariance.toNNReal publicBase
  let accessLowerLaw :=
    (lg21OptionalFullBaseSelectedNoReportKernel
      baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map Prod.snd
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hevent : MeasurableSet event := by
    simpa [event] using
      lg21HiddenAccessBaseScoreLowerTailEvent_measurable threshold hthreshold
  have hconstantEvent : MeasurableSet constantEvent := by
    simpa [constantEvent] using
      lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have hselectedFiber : selectedFiber event publicBase =
      selectedFiber constantEvent publicBase := by
    ext scoreSkill
    simp [event, constantEvent, threshold, anchor,
      selectedFiber, lg21HiddenAccessBaseScoreLowerTailEvent,
      lg21OptionalFullBaseNoReportEvent]
  have hlowerMass : 0 < lowerMass := by
    change 0 < joint publicBase (selectedFiber event publicBase)
    rw [hselectedFiber]
    simpa [joint, constantEvent] using
      (lg21_optional_fullBaseGaussian_noReport_fibre_positive
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase)
  have hselectedUniv : accessSelectedSkillKernel publicBase Set.univ = lowerMass := by
    rw [show accessSelectedSkillKernel =
        lg21HiddenAccessScoreSelectedSkillKernel joint threshold by rfl,
      lg21HiddenAccessScoreSelectedSkillKernel_apply_univ
        joint threshold hthreshold publicBase]
  have hnoAccessLaw : noAccessKernel publicBase = noAccessLaw := by
    calc
      noAccessKernel publicBase = (joint publicBase).map Prod.snd := by
        rw [show noAccessKernel = joint.map Prod.snd by rfl,
          Kernel.map_apply joint measurable_snd publicBase]
      _ = gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
        simpa [joint] using
          (lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
            baseMean hbaseMean baseVariance noiseVariance publicBase)
      _ = noAccessLaw := by
        symm
        exact gaussianLocationKernel_apply
          baseMean hbaseMean baseVariance.toNNReal publicBase
  have hselectedNormalized :
      lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase =
        lg21NormalizedRestriction (joint publicBase)
          (selectedFiber constantEvent publicBase) := by
    change selectedNormalizedKernel joint constantEvent publicBase = _
    rw [selectedNormalizedKernel_apply hconstantEvent]
  have hrestricted : lowerMass •
      lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase =
        (joint publicBase).restrict (selectedFiber event publicBase) := by
    rw [hselectedNormalized, ← hselectedFiber]
    exact lg21_smul_normalizedRestriction_eq_restrict
      (joint publicBase) (selectedFiber event publicBase) hlowerMass
  have haccessSelected : accessSelectedSkillKernel publicBase =
      lowerMass • accessLowerLaw := by
    change (selectedRestrictionKernel joint event).map Prod.snd publicBase = _
    rw [Kernel.map_apply _ measurable_snd publicBase,
      selectedRestrictionKernel_apply hevent]
    calc
      ((joint publicBase).restrict (selectedFiber event publicBase)).map Prod.snd =
          (lowerMass •
            lg21OptionalFullBaseSelectedNoReportKernel
              baseMean hbaseMean baseVariance noiseVariance anchor publicBase).map
            Prod.snd := by rw [hrestricted]
      _ = lowerMass • accessLowerLaw := by
            rw [Measure.map_smul]
  have hfibreMass : Measurable (lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass) := by
    simpa [accessSelectedSkillKernel, joint, threshold] using
      (lg21HiddenAccessScoreRawFibreMass_measurable
        joint noAccessMass accessMass threshold hthreshold)
  have hrawKernel :
      lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass publicBase =
        noAccessMass • noAccessLaw +
          (accessMass * lowerMass) • accessLowerLaw := by
    rw [lg21HiddenAccessScoreRawKernel_apply, hnoAccessLaw, haccessSelected,
      ← smul_smul]
  have hrawFibreMass : lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass publicBase =
      noAccessMass + accessMass * lowerMass := by
    unfold lg21HiddenAccessScoreRawFibreMass
    rw [hselectedUniv]
  rw [lg21HiddenAccessScoreNormalizedKernel_apply
    noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
    hnoAccessFinite haccessFinite hfibreMass publicBase,
    hrawKernel, hrawFibreMass]
  simpa [joint, threshold, event, anchor, constantEvent, lowerMass,
    noAccessLaw, accessLowerLaw, noAccessKernel,
    accessSelectedSkillKernel,
    lg21HiddenAccessBaseScoreLowerTailEvent,
    lg21OptionalFullBaseNoReportEvent, selectedFiber] using
    (lg21HiddenAccessAllTakeMeanGap_rawMixtureMean_lt_reportedAtThreshold
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessMass haccessMass hnoAccessFinite haccessFinite
      gap hgap publicBase)

/-- The all-access/high-score candidate with a literal raw-population
no-report value.  Its `X = 0` value is the mean of the normalized mixture
kernel, while its reported value is the Gaussian posterior at the disclosed
score. -/
noncomputable def lg21HiddenAccessAllTakeMeanGapScoreCandidate
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)] :
    LG21OptionalCandidateBranchData ℝ Base ℝ := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let noAccessKernel := joint.map Prod.snd
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  let accessSelectedSkillKernel :=
    lg21HiddenAccessScoreSelectedSkillKernel joint
      (fun publicBase => baseMean publicBase + gap)
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  exact {
    testLaw := fun latentSkill _publicBase =>
      gaussianReal latentSkill noiseVariance.toNNReal
    testLaw_isProbability := by
      intro latentSkill publicBase
      infer_instance
    reportDecision := fun publicBase score =>
      decide (baseMean publicBase + gap ≤ score)
    reportedValue := fun publicBase score =>
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase score
    noReportValue := fun publicBase =>
      ∫ latentSkill, latentSkill ∂
        lg21HiddenAccessScoreNormalizedKernel
          noAccessKernel accessSelectedSkillKernel
          noAccessMass accessMass hnoAccessFinite haccessFinite publicBase
    continuationValue_integrable := by
      intro latentSkill publicBase
      have hpAffine : lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase = fun score =>
          gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase +
            gaussianSignalWeight baseVariance noiseVariance * score := by
        funext score
        rw [lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance noiseVariance publicBase score]
        ring
      rw [hpAffine]
      simpa using
        (lg21_optional_highScoreCandidate_continuation_integrable_of_affine
          (baseMean publicBase + gap)
          (∫ latentSkill, latentSkill ∂
            lg21HiddenAccessScoreNormalizedKernel
              noAccessKernel accessSelectedSkillKernel
              noAccessMass accessMass hnoAccessFinite haccessFinite publicBase)
          (gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase)
          (gaussianSignalWeight baseVariance noiseVariance)
          noiseVariance.toNNReal latentSkill)
  }

/-- The cutoff candidate's report action is exactly its displayed literal
score cutoff.  This projection is kept separate from the later PBO bridge so
the cutoff can be supplied by a fixed-point argument rather than inferred
from a strategy name. -/
@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportDecision
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (publicBase : Base) (score : ℝ) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap).reportDecision
        publicBase score =
      decide (baseMean publicBase + gap ≤ score) := by
  rfl

/-- The candidate's reported value is the raw Gaussian posterior for the
literal public `(base, score)` record. -/
@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportedValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (publicBase : Base) (score : ℝ) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap).reportedValue
        publicBase score =
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase score := by
  rfl

/-- The candidate's pre-score experiment is the literal Gaussian test law. -/
@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_testLaw
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap).testLaw
        latentSkill publicBase =
      gaussianReal latentSkill noiseVariance.toNNReal := by
  rfl

/-- The candidate's `X = 0` value is the mean of the normalized *raw*
score-selected mixture.  In particular, the no-access component has not been
discarded before the conditional expectation is taken. -/
@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (publicBase : Base) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap).noReportValue
        publicBase =
      let joint := gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance
      let noAccessKernel := joint.map Prod.snd
      letI : IsMarkovKernel noAccessKernel :=
        Kernel.IsMarkovKernel.map joint measurable_snd
      let accessSelectedSkillKernel :=
        lg21HiddenAccessScoreSelectedSkillKernel joint
          (fun base => baseMean base + gap)
      ∫ latentSkill, latentSkill ∂
        lg21HiddenAccessScoreNormalizedKernel
          noAccessKernel accessSelectedSkillKernel
          noAccessMass accessMass hnoAccessFinite haccessFinite publicBase := by
  rfl

/-- The all-taking candidate record induces the same literal report action
event as the source-timed all-take/high-score action pair. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportEvent_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)] :
    lg21HiddenAccessCandidateReportEvent testFeature
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        noAccessMass accessMass hnoAccessFinite haccessFinite gap).reportDecision =
      lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap) := by
  ext student
  rfl

/-- The all-taking candidate record induces the same literal no-report action
event as the source-timed all-take/high-score action pair. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportEvent_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)] :
    lg21HiddenAccessCandidateNoReportEvent testFeature
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        noAccessMass accessMass hnoAccessFinite haccessFinite gap).reportDecision =
      lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap) := by
  ext student
  rfl

/-- The all-take/high-score candidate's displayed report payoff is the
conditional skill mean on its own literal positive-mass raw report branch.
The branch is first transported to the matching Gaussian upper-tail law; the
PBO equality then holds only almost everywhere under its selected public
observation marginal. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportedValue_eq_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite gap
    let reportLaw := (lg21NormalizedRestriction
      (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    letI : IsProbabilityMeasure reportLaw := by
      letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
        lg21ContinuousGaussianPopulationLaw_isProbability M
      letI : IsFiniteMeasure (lg21ContinuousGaussianPopulationLaw M) := ⟨by simp⟩
      letI : IsProbabilityMeasure (lg21NormalizedRestriction
          (lg21ContinuousGaussianPopulationLaw M)
          (lg21HiddenAccessRawCandidateReportEvent testFeature
            (lg21HiddenAccessAllTake testFeature)
            (lg21HiddenAccessMeanGapReport testFeature baseMean gap))) :=
        lg21NormalizedRestriction_isProbability _ _
          (ne_of_gt
            (lg21HiddenAccessAllTakeMeanGap_rawCandidateReport_positive
              M haccess testFeature baseLaw baseMean hbaseMean gap
              baseVariance noiseVariance hbaseVariance hnoiseVariance hsourceFactor))
          (measure_ne_top _ _)
      exact Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
    letI : IsFiniteMeasure reportLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂reportLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
      candidate.reportedValue publicObservation.1 publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            scoreSkill.2.2)
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            (scoreSkill.1, scoreSkill.2.1))
          reportLaw publicObservation := by
  intro candidate reportLaw
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let upperEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let selectedLaw := lg21NormalizedRestriction (baseLaw ⊗ₘ joint) upperEvent
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  have hreportPositive : 0 < rawLaw reportEvent := by
    simpa [rawLaw, reportEvent] using
      (lg21HiddenAccessAllTakeMeanGap_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hbaseVariance hnoiseVariance hsourceFactor)
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure reportLaw := by
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure reportLaw := ⟨by simp⟩
  have hupperPositive : 0 < (baseLaw ⊗ₘ joint) upperEvent := by
    simpa [joint, upperEvent] using
      (lg21HiddenAccessGaussian_selectedUpperTail_positive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold
        (by simpa [threshold] using hbaseMean.add measurable_const))
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability (baseLaw ⊗ₘ joint) upperEvent
      (ne_of_gt hupperPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hactionLaw : reportLaw = selectedLaw := by
    simpa [reportLaw, selectedLaw, rawLaw, reportEvent, scoreSkillObservation,
      upperEvent, threshold, joint] using
      (lg21HiddenAccessAllTakeMeanGap_rawCandidateReportBaseScoreSkillLaw_eq_normalizedUpperTail
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor)
  have hRCD := lg21HiddenAccessGaussian_selectedUpperTail_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance threshold
    (by simpa [threshold] using hbaseMean.add measurable_const)
    hupperPositive
  have hPBOSelected : ∀ᵐ publicObservation ∂selectedLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
      candidate.reportedValue publicObservation.1 publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            scoreSkill.2.2)
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            (scoreSkill.1, scoreSkill.2.1))
          selectedLaw publicObservation := by
    filter_upwards [hRCD] with publicObservation hposterior
    rw [hposterior]
    rfl
  simpa only [hactionLaw] using hPBOSelected

/-- On every score at or above the candidate's displayed cutoff, the literal
raw-mixture `X = 0` payoff is weakly below the disclosed-score payoff. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReport_le_reported_of_threshold_le
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessMass : 0 < noAccessMass) (haccessMass : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (hgap : 0 < gap)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (publicBase : Base) (score : ℝ)
    (hthreshold : baseMean publicBase + gap ≤ score) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
    candidate.noReportValue publicBase ≤ candidate.reportedValue publicBase score := by
  intro candidate
  have hanchor : candidate.noReportValue publicBase <
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase
          (baseMean publicBase + gap) := by
    simpa [candidate] using
      (lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_lt_reportedAtThreshold
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessMass haccessMass hnoAccessFinite haccessFinite
        gap hgap publicBase (by infer_instance))
  have hmono := lg21_optional_rawGaussianPosteriorMean_strictMono
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance publicBase
  calc
    candidate.noReportValue publicBase ≤
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase
            (baseMean publicBase + gap) := le_of_lt hanchor
    _ ≤ lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase score :=
      hmono.monotone hthreshold
    _ = candidate.reportedValue publicBase score := by rfl

/-- Every latent type has a strict expected gain from the all-take candidate
test experiment.  The proof uses the literal raw-mixture no-report value and
only the candidate's own upper-score report branch. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_pointwise_test_gain
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessMass : 0 < noAccessMass) (haccessMass : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (hgap : 0 < gap)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (latentSkill : ℝ) (publicBase : Base) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
    candidate.noReportValue publicBase <
      lg21OptionalCandidateTestExpectedValue candidate latentSkill publicBase := by
  intro candidate
  have hnoiseVarianceNN : noiseVariance.toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hnoiseVariance)
  have hanchor : candidate.noReportValue publicBase <
      candidate.reportedValue publicBase (baseMean publicBase + gap) := by
    simpa [candidate] using
      (lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_lt_reportedAtThreshold
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessMass haccessMass hnoAccessFinite haccessFinite
        gap hgap publicBase (by infer_instance))
  apply lg21_optional_candidate_gaussian_pointwise_test_gain
    candidate publicBase latentSkill noiseVariance.toNNReal hnoiseVarianceNN
  · intro sourceSkill
    rfl
  · intro score hreport
    have hthreshold : baseMean publicBase + gap ≤ score := by
      simpa [candidate] using hreport
    exact lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReport_le_reported_of_threshold_le
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessMass haccessMass hnoAccessFinite haccessFinite
      gap hgap publicBase score hthreshold
  · simpa [candidate] using
      (lg21_optional_rawGaussianPosteriorMean_strictMono
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance publicBase)
  · exact hanchor
  · intro score hscore
    change decide (baseMean publicBase + gap ≤ score) = true
    simp [le_of_lt hscore]

/-- Normalizing the whole raw population on the whole public-base region is
the original population law.  This makes the all-base candidate's branch PBO
identities usable without a second, vacuous localization layer. -/
theorem lg21HiddenAccessLocalRawLaw_univ
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    lg21HiddenAccessLocalRawLaw M testFeature Set.univ =
      lg21ContinuousGaussianPopulationLaw M := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  have hregion : lg21HiddenAccessBaseRegionEvent testFeature (Set.univ :
      Set (LG21NonTestFeature Feature testFeature -> ℝ)) = Set.univ := by
    ext student
    simp [lg21HiddenAccessBaseRegionEvent]
  simp [lg21HiddenAccessLocalRawLaw, rawLaw, hregion, lg21NormalizedRestriction]

/-! ## Public-base localization of literal candidate action laws -/

/-- Every positive public-base region has a positive literal report branch
under the all-access/high-score candidate.  The proof first retains the
region in the Gaussian base law, then transports that positive upper tail back
to the raw population together with its positive access component. -/
theorem lg21HiddenAccessAllTakeMeanGap_localCandidateReport_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region)) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      (by
        letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
        letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
        exact measure_ne_top _ _)
      (by
        letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
        letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
        exact measure_ne_top _ _) gap
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision) := by
  intro candidate
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let rawObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let upperEvent := lg21HiddenAccessBaseScoreUpperTailEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let regionProduct : Set ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) := region ×ˢ Set.univ
  let selectedBase : Set ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) := Prod.fst ⁻¹' region
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrawObservation : Measurable rawObservation := by
    simpa [rawObservation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent, base] using hregion.preimage hbase
  have hthreshold : Measurable threshold := by
    simpa [threshold] using hbaseMean.add measurable_const
  have hupperEvent : MeasurableSet upperEvent := by
    simpa [upperEvent] using
      (lg21HiddenAccessBaseScoreUpperTailEvent_measurable threshold hthreshold)
  have hreportEvent : MeasurableSet reportEvent := by
    rw [show reportEvent = {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true ∧
        baseMean (lg21HiddenAccessStudentBase testFeature student.2) + gap ≤
          lg21HiddenAccessStudentScore testFeature student.2} by
      simpa [reportEvent] using
        (lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq
          testFeature baseMean gap)]
    have haccess : MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
        student.1 = true} :=
      (measurableSet_singleton true).preimage measurable_fst
    have hscore : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
        lg21HiddenAccessStudentScore testFeature student.2) :=
      (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
    exact haccess.inter (measurableSet_le
      ((hbaseMean.comp hbase).add measurable_const) hscore)
  have hselectedBase : MeasurableSet selectedBase := by
    simpa [selectedBase] using hregion.preimage measurable_fst
  have hregionProduct : MeasurableSet regionProduct := by
    simpa [regionProduct] using hregion.prod MeasurableSet.univ
  have hselectedBaseEq : selectedBase = regionProduct := by
    ext baseScoreSkill
    simp [selectedBase, regionProduct]
  have hregionPreimage : rawObservation ⁻¹' selectedBase = regionEvent := by
    ext student
    change base student ∈ region ↔ base student ∈ region
    rfl
  have hbaseMap : rawLaw.map base = baseLaw := by
    calc
      rawLaw.map base = (rawLaw.map rawObservation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hrawObservation]
        rfl
      _ = (baseLaw ⊗ₘ joint).map Prod.fst := by
        rw [show rawLaw.map rawObservation = baseLaw ⊗ₘ joint by
          simpa [rawLaw, rawObservation, joint] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ joint).fst = baseLaw
        rw [Measure.fst_compProd]
  have hbaseRegionPositive : 0 < baseLaw region := by
    have hrawRegionPositive : 0 < rawLaw (base ⁻¹' region) := by
      simpa [rawLaw, base, regionEvent] using hregionPositive
    rw [← Measure.map_apply hbase hregion, hbaseMap] at hrawRegionPositive
    exact hrawRegionPositive
  let localBaseLaw := lg21NormalizedRestriction baseLaw region
  letI : IsProbabilityMeasure localBaseLaw := by
    dsimp [localBaseLaw]
    exact lg21NormalizedRestriction_isProbability baseLaw region
      (ne_of_gt hbaseRegionPositive) (measure_ne_top _ _)
  have hupperLocalPositive : 0 < (localBaseLaw ⊗ₘ joint) upperEvent := by
    simpa [localBaseLaw, joint, upperEvent, threshold] using
      (lg21HiddenAccessGaussian_selectedUpperTail_positive
        localBaseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have hupperNormalizedPositive : 0 <
      (lg21NormalizedRestriction (baseLaw ⊗ₘ joint) regionProduct) upperEvent := by
    rw [lg21_normalizedRestriction_compProd_left baseLaw joint region hregion]
    simpa [localBaseLaw] using hupperLocalPositive
  have hjointIntersectionPositive : 0 < (baseLaw ⊗ₘ joint)
      (upperEvent ∩ regionProduct) := by
    rw [lg21NormalizedRestriction_apply (baseLaw ⊗ₘ joint) hupperEvent]
      at hupperNormalizedPositive
    exact (ENNReal.mul_pos_iff.mp hupperNormalizedPositive).2
  have htransport : (rawLaw.restrict reportEvent).map rawObservation =
      M.accessLaw {true} • ((baseLaw ⊗ₘ joint).restrict upperEvent) := by
    simpa [rawLaw, reportEvent, rawObservation, joint, upperEvent, threshold] using
      (lg21HiddenAccessAllTakeMeanGap_reportBaseScoreSkillMeasure_eq_smul_upperRestriction
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor)
  have hrawIntersectionPositive : 0 < rawLaw (reportEvent ∩ regionEvent) := by
    have hmeasure : rawLaw (reportEvent ∩ regionEvent) =
        M.accessLaw {true} * (baseLaw ⊗ₘ joint)
          (upperEvent ∩ regionProduct) := by
      calc
        rawLaw (reportEvent ∩ regionEvent) = rawLaw (regionEvent ∩ reportEvent) := by
          rw [inter_comm]
        _ = (rawLaw.restrict reportEvent) regionEvent := by
          rw [Measure.restrict_apply hregionEvent]
        _ = ((rawLaw.restrict reportEvent).map rawObservation) selectedBase := by
          symm
          rw [Measure.map_apply hrawObservation hselectedBase, hregionPreimage]
        _ = (M.accessLaw {true} •
            ((baseLaw ⊗ₘ joint).restrict upperEvent)) selectedBase := by
          rw [htransport]
        _ = M.accessLaw {true} *
            ((baseLaw ⊗ₘ joint).restrict upperEvent) selectedBase := by
          rw [Measure.smul_apply, smul_eq_mul]
        _ = M.accessLaw {true} * (baseLaw ⊗ₘ joint)
            (selectedBase ∩ upperEvent) := by
          rw [Measure.restrict_apply hselectedBase]
        _ = M.accessLaw {true} * (baseLaw ⊗ₘ joint)
            (upperEvent ∩ regionProduct) := by
          rw [hselectedBaseEq, inter_comm]
    rw [hmeasure]
    exact ENNReal.mul_pos (ne_of_gt haccess)
      (ne_of_gt hjointIntersectionPositive)
  have hcandidateEvent :
      lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision =
        reportEvent := by
    simpa [candidate, reportEvent] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportEvent_eq
        testFeature baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _) gap)
  change 0 < localLaw
    (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision)
  rw [hcandidateEvent]
  change 0 < lg21NormalizedRestriction rawLaw regionEvent reportEvent
  exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw regionEvent reportEvent
    hregionEvent (by simpa [inter_comm] using hrawIntersectionPositive)

/-- The literal report action law in a public-base region is exactly the
global literal report action law conditioned on that same retained base.
This transport is purely measure-theoretic and does not reuse a global PBO
value on the local branch. -/
theorem lg21HiddenAccessAllTakeMeanGap_localReportActionLaw_eq_selectedGlobal
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
    let reportEvent := lg21HiddenAccessCandidateReportEvent testFeature
      candidate.reportDecision
    let globalActionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    let localActionLaw := (lg21NormalizedRestriction localLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
  intro rawLaw localLaw candidate reportEvent globalActionLaw localActionLaw
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let record := lg21HiddenAccessBaseScoreSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidate.reportDecision pair.1 pair.2) := by
    simpa [candidate] using
      (lg21HiddenAccessMeanGapReport_measurable
        testFeature baseMean hbaseMean gap)
  have hreportEvent : MeasurableSet reportEvent := by
    simpa [reportEvent] using
      (lg21HiddenAccessCandidateReportEvent_measurable testFeature
        candidate.reportDecision hcandidateReport)
  simpa [localLaw, globalActionLaw, localActionLaw, rawLaw, base, record] using
    (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw
      rawLaw base record Prod.fst hbase hrecord measurable_fst
      (fun student => rfl) region hregion reportEvent hreportEvent)

/-- The literal no-report action law in a public-base region is exactly the
global literal no-report action law conditioned on the retained public base.
The hidden no-access component remains in both sides of this equality. -/
theorem lg21HiddenAccessAllTakeMeanGap_localNoReportActionLaw_eq_selectedGlobal
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
    let noReportEvent := lg21HiddenAccessCandidateNoReportEvent testFeature
      candidate.reportDecision
    let globalActionLaw := (lg21NormalizedRestriction rawLaw noReportEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature)
    let localActionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature)
    localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
  intro rawLaw localLaw candidate noReportEvent globalActionLaw localActionLaw
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidate.reportDecision pair.1 pair.2) := by
    simpa [candidate] using
      (lg21HiddenAccessMeanGapReport_measurable
        testFeature baseMean hbaseMean gap)
  have hnoReportEvent : MeasurableSet noReportEvent := by
    simpa [noReportEvent] using
      (lg21HiddenAccessCandidateNoReportEvent_measurable testFeature
        candidate.reportDecision hcandidateReport)
  simpa [localLaw, globalActionLaw, localActionLaw, rawLaw, base, record] using
    (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw
      rawLaw base record Prod.fst hbase hrecord measurable_fst
      (fun student => rfl) region hregion noReportEvent hnoReportEvent)

/-- The all-take/high-score candidate's literal report PBO remains a
conditional-mean PBO after localizing to any positive public-base region.
The candidate value is unchanged; only the action law and its `condDistrib`
are localized. -/
theorem lg21HiddenAccessAllTakeMeanGap_localCandidateReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤)
    (hlocalReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateReportEvent testFeature
        (lg21HiddenAccessAllTakeMeanGapScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance
          (M.accessLaw {false}) (M.accessLaw {true})
          hnoAccessFinite haccessFinite gap).reportDecision)) :
    LG21HiddenAccessCandidateReportPBOOn M testFeature region hregionPositive
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap)
      (by
        simpa using
          (lg21HiddenAccessMeanGapReport_measurable
            testFeature baseMean hbaseMean gap))
      hlocalReportPositive := by
  let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite gap
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21HiddenAccessCandidateReportEvent testFeature
    candidate.reportDecision
  let rawObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let globalActionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map
    rawObservation
  let localActionLaw := (lg21NormalizedRestriction localLaw reportEvent).map
    rawObservation
  let publicObservation :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun baseScoreSkill => (baseScoreSkill.1, baseScoreSkill.2.1)
  let latent :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun baseScoreSkill => baseScoreSkill.2.2
  let selected : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    region ×ˢ Set.univ
  have hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidate.reportDecision pair.1 pair.2) := by
    simpa [candidate] using
      (lg21HiddenAccessMeanGapReport_measurable
        testFeature baseMean hbaseMean gap)
  change LG21HiddenAccessCandidateReportPBOOn M testFeature region hregionPositive
    candidate hcandidateReport hlocalReportPositive
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw := by
    dsimp [localLaw]
    exact lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have hglobalReportPositive : 0 < rawLaw reportEvent := by
    have hrawPositive :=
      lg21HiddenAccessAllTakeMeanGap_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hbaseVariance hnoiseVariance hsourceFactor
    simpa [rawLaw, reportEvent, candidate,
      lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportEvent_eq] using hrawPositive
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hglobalReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw := by
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw reportEvent
      (ne_of_gt hlocalReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw := by
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  have hreportEvent : MeasurableSet reportEvent := by
    exact lg21HiddenAccessCandidateReportEvent_measurable testFeature
      candidate.reportDecision hcandidateReport
  have hregionEvent : MeasurableSet
      (lg21HiddenAccessBaseRegionEvent testFeature region) :=
    lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion
  have hlocalIntersectionPositive : 0 < rawLaw
      (reportEvent ∩ lg21HiddenAccessBaseRegionEvent testFeature region) := by
    change 0 < lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region) reportEvent
      at hlocalReportPositive
    rw [lg21NormalizedRestriction_apply rawLaw hreportEvent]
      at hlocalReportPositive
    exact (ENNReal.mul_pos_iff.mp hlocalReportPositive).2
  have hpublicObservation : Measurable publicObservation :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hlatent : Measurable latent := measurable_snd.comp measurable_snd
  have hselected : MeasurableSet selected := by
    simpa [selected] using hregion.prod MeasurableSet.univ
  have hselectionPreimage : rawObservation ⁻¹'
      (publicObservation ⁻¹' selected) =
        lg21HiddenAccessBaseRegionEvent testFeature region := by
    ext student
    simp [rawObservation, publicObservation, selected,
      lg21HiddenAccessBaseRegionEvent,
      lg21HiddenAccessBaseScoreSkillObservation]
  have hglobalSelectedPositive : 0 < globalActionLaw
      (publicObservation ⁻¹' selected) := by
    change 0 < (lg21NormalizedRestriction rawLaw reportEvent).map rawObservation
      (publicObservation ⁻¹' selected)
    rw [Measure.map_apply
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
      (hselected.preimage hpublicObservation), hselectionPreimage]
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw reportEvent
      (lg21HiddenAccessBaseRegionEvent testFeature region) hreportEvent
      hlocalIntersectionPositive
  have hglobalPBO : ∀ᵐ publicRecord ∂globalActionLaw.map publicObservation,
      candidate.reportedValue publicRecord.1 publicRecord.2 =
        ∫ latentSkill, latentSkill ∂
          condDistrib latent publicObservation globalActionLaw publicRecord := by
    simpa [candidate, rawLaw, reportEvent, rawObservation,
      globalActionLaw, publicObservation, latent,
      lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportEvent_eq] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportedValue_eq_condDistribMean_ae
        M haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        hsourceFactor hnoAccessFinite haccessFinite)
  have hactionLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [candidate, rawLaw, localLaw, reportEvent, rawObservation,
      globalActionLaw, localActionLaw] using
      (lg21HiddenAccessAllTakeMeanGap_localReportActionLaw_eq_selectedGlobal
        M testFeature baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap region hregion)
  have hselectionBase : publicObservation ⁻¹' selected = Prod.fst ⁻¹' region := by
    ext baseScoreSkill
    simp [publicObservation, selected]
  have hlocalPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw publicObservation latent
    (fun publicRecord => candidate.reportedValue publicRecord.1 publicRecord.2)
    hpublicObservation hlatent hglobalPBO selected hselected hglobalSelectedPositive
  unfold LG21HiddenAccessCandidateReportPBOOn
  dsimp only
  simpa only [localLaw, reportEvent, rawObservation, localActionLaw,
    publicObservation, latent, hselectionBase, ← hactionLaw] using hlocalPBO

/-- The preceding local report PBO in the source-timed carrier.  Here the
all-take and high-score actions are written explicitly, so later local action
patches can transport this fact by equality of their attained action events. -/
theorem lg21HiddenAccessAllTakeMeanGap_localSourceTimedReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤)
    (hlocalReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))) :
    LG21HiddenAccessSourceTimedCandidateReportPBOOn M testFeature region
      hregionPositive (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap)
      hlocalReportPositive := by
  let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite gap
  have hcandidateEvent :
      lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision =
        lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature)
          (lg21HiddenAccessMeanGapReport testFeature baseMean gap) := by
    simpa [candidate] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_reportEvent_eq
        testFeature baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap)
  have hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidate.reportDecision pair.1 pair.2) := by
    simpa [candidate] using
      (lg21HiddenAccessMeanGapReport_measurable testFeature baseMean hbaseMean gap)
  have hcandidatePositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision) := by
    rw [hcandidateEvent]
    exact hlocalReportPositive
  have hPBO := lg21HiddenAccessAllTakeMeanGap_localCandidateReportPBO
    M haccess testFeature baseLaw baseMean hbaseMean gap
    baseVariance noiseVariance hbaseVariance hnoiseVariance
    hsourceFactor region hregion hregionPositive hnoAccessFinite haccessFinite
    hcandidatePositive
  change LG21HiddenAccessSourceTimedCandidateReportPBOOn M testFeature region
    hregionPositive (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap) candidate
    hlocalReportPositive
  simpa only [LG21HiddenAccessSourceTimedCandidateReportPBOOn,
    LG21HiddenAccessCandidateReportPBOOn, hcandidateEvent] using hPBO

/-! ## Literal candidate no-report RCD -/

/-- The normalized base/skill law of the all-take/high-score candidate is a
probability measure because the literal raw `X = 0` event contains the
positive no-access population. -/
theorem lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ) :
    IsProbabilityMeasure
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateTake := lg21HiddenAccessAllTake testFeature
  let candidateReport := lg21HiddenAccessMeanGapReport testFeature baseMean gap
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  have htakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2) := by
    simpa [candidateTake] using lg21HiddenAccessAllTake_measurable testFeature
  have hreportMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2) := by
    simpa [candidateReport] using
      lg21HiddenAccessMeanGapReport_measurable testFeature baseMean hbaseMean gap
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature candidateTake candidateReport hnoAccess))
      (measure_ne_top _ _)
  change IsProbabilityMeasure
    ((lg21NormalizedRestriction rawLaw noReportEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature))
  exact Measure.isProbabilityMeasure_map
    (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable

/-- The actual literal candidate no-report law factors through its own
normalized raw score-selected conditional kernel.  The base marginal is
reweighted by the raw `X = 0` fibre mass before the conditional kernel is
applied. -/
theorem lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel joint
        (fun publicBase => baseMean publicBase + gap)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel_isFinite joint
        (fun publicBase => baseMean publicBase + gap)
    let rawKernel := lg21HiddenAccessScoreRawKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true})
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
    let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
      ((rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass) ⊗ₘ
        normalizedKernel := by
  intro joint noAccessKernel accessSelectedSkillKernel rawKernel fibreMass
    normalizedKernel rawLaw noReportEvent
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  have hthreshold : Measurable (fun publicBase :
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      baseMean publicBase + gap) := hbaseMean.add measurable_const
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessScoreRawFibreMass_measurable
        joint (M.accessLaw {false}) (M.accessLaw {true})
        (fun publicBase => baseMean publicBase + gap) hthreshold)
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessScoreRawKernel_isFinite
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel] using
      (lg21HiddenAccessScoreNormalizedKernel_isMarkov
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess
        hnoAccessFinite haccessFinite hfibreMass)
  have hcandidateRaw :
      lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
        (rawLaw noReportEvent)⁻¹ • (baseLaw ⊗ₘ rawKernel) := by
    simpa [rawLaw, noReportEvent, rawKernel, noAccessKernel,
      accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_eq_normalized_scoreRawKernel
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor)
  have hweightedFactor :
      (baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel =
        baseLaw ⊗ₘ rawKernel := by
    simpa [fibreMass, normalizedKernel, rawKernel,
      noAccessKernel, accessSelectedSkillKernel] using
      (lg21HiddenAccessScoreWeightedBase_compProd_normalizedKernel
        baseLaw noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess
        hnoAccessFinite haccessFinite hfibreMass)
  calc
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap) =
        (rawLaw noReportEvent)⁻¹ • (baseLaw ⊗ₘ rawKernel) := hcandidateRaw
    _ = (rawLaw noReportEvent)⁻¹ •
        ((baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel) := by
          rw [hweightedFactor]
    _ = ((rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass) ⊗ₘ
        normalizedKernel := by
          rw [Measure.compProd_smul_left]

/-- The candidate's literal raw `X = 0` law has the displayed normalized
score-selected mixture as its actual conditional distribution of skill given
the public base, almost everywhere under its own retained base marginal. -/
theorem lg21HiddenAccessAllTakeMeanGap_noReport_condDistrib_skill_base_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel joint
        (fun publicBase => baseMean publicBase + gap)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessScoreSelectedSkillKernel_isFinite joint
        (fun publicBase => baseMean publicBase + gap)
    let rawKernel := lg21HiddenAccessScoreRawKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true})
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
    let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
    letI : IsProbabilityMeasure candidateLaw :=
      lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap
    condDistrib Prod.snd Prod.fst candidateLaw =ᵐ[candidateLaw.map Prod.fst]
      normalizedKernel := by
  intro joint noAccessKernel accessSelectedSkillKernel rawKernel fibreMass
    normalizedKernel candidateLaw
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  have hthreshold : Measurable (fun publicBase :
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      baseMean publicBase + gap) := hbaseMean.add measurable_const
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessScoreRawFibreMass_measurable
        joint (M.accessLaw {false}) (M.accessLaw {true})
        (fun publicBase => baseMean publicBase + gap) hthreshold)
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessScoreRawKernel_isFinite
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel] using
      (lg21HiddenAccessScoreNormalizedKernel_isMarkov
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess
        hnoAccessFinite haccessFinite hfibreMass)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let candidateBaseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ) :=
    (rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap)
  have hcandidateFactor : candidateLaw = candidateBaseLaw ⊗ₘ normalizedKernel := by
    simpa [candidateLaw, candidateBaseLaw, rawLaw, noReportEvent,
      normalizedKernel, fibreMass, rawKernel, noAccessKernel,
      accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_factorization
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor
        hnoAccessFinite haccessFinite)
  have hbaseMarginal : candidateLaw.map Prod.fst = candidateBaseLaw := by
    calc
      candidateLaw.map Prod.fst =
          (candidateBaseLaw ⊗ₘ normalizedKernel).map Prod.fst := by
            rw [hcandidateFactor]
      _ = candidateBaseLaw := by
            change (candidateBaseLaw ⊗ₘ normalizedKernel).fst = candidateBaseLaw
            rw [Measure.fst_compProd]
  have hjoint : candidateLaw.map (fun baseSkill =>
      (Prod.fst baseSkill, Prod.snd baseSkill)) =
      candidateLaw.map Prod.fst ⊗ₘ normalizedKernel := by
    calc
      candidateLaw.map (fun baseSkill =>
          (Prod.fst baseSkill, Prod.snd baseSkill)) = candidateLaw := by
            change candidateLaw.map id = candidateLaw
            rw [Measure.map_id]
      _ = candidateBaseLaw ⊗ₘ normalizedKernel := hcandidateFactor
      _ = candidateLaw.map Prod.fst ⊗ₘ normalizedKernel := by
            rw [hbaseMarginal]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_fst measurable_snd hjoint

/-- The all-take cutoff candidate's displayed `X = 0` value is its literal
raw-population PBO almost everywhere under the candidate's own retained base
marginal.  This is the branch equation a cutoff fixed-point construction may
use: it conditions on all raw no-reporters, including `Z = 0`, rather than on
an access-labelled subpopulation. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
    letI : IsProbabilityMeasure candidateLaw :=
      lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap
    ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
      candidate.noReportValue publicBase =
        ∫ skill, skill ∂condDistrib Prod.snd Prod.fst candidateLaw publicBase := by
  intro candidate candidateLaw
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    infer_instance
  let noAccessKernel := joint.map Prod.snd
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  let accessSelectedSkillKernel :=
    lg21HiddenAccessScoreSelectedSkillKernel joint
      (fun publicBase => baseMean publicBase + gap)
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    dsimp [accessSelectedSkillKernel]
    infer_instance
  have hRCD : condDistrib Prod.snd Prod.fst candidateLaw =ᵐ[candidateLaw.map Prod.fst]
      lg21HiddenAccessScoreNormalizedKernel
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite := by
    simpa [candidateLaw, joint, noAccessKernel, accessSelectedSkillKernel] using
      (lg21HiddenAccessAllTakeMeanGap_noReport_condDistrib_skill_base_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite)
  change ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
    (∫ skill, skill ∂
      lg21HiddenAccessScoreNormalizedKernel
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite publicBase) =
      ∫ skill, skill ∂condDistrib Prod.snd Prod.fst candidateLaw publicBase
  filter_upwards [hRCD] with publicBase hconditional
  rw [hconditional]

/-- The all-take/high-score candidate's literal no-report PBO remains valid
after localizing to a positive public-base region.  The localized law is the
candidate's literal `(base, skill)` action law, so its hidden no-access mass
is retained before conditioning. -/
theorem lg21HiddenAccessAllTakeMeanGap_localSourceTimedNoReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤)
    (hlocalNoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))) :
    LG21HiddenAccessSourceTimedCandidateNoReportPBOOn M testFeature region
      hregionPositive (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap)
      hlocalNoReportPositive := by
  let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite gap
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
  let rawObservation := lg21HiddenAccessBaseSkillObservation testFeature
  let globalActionLaw := (lg21NormalizedRestriction rawLaw noReportEvent).map
    rawObservation
  let localActionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map
    rawObservation
  let publicObservation :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ ->
        (LG21NonTestFeature Feature testFeature -> ℝ) := Prod.fst
  let latent :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ -> ℝ := Prod.snd
  let selected : Set (LG21NonTestFeature Feature testFeature -> ℝ) := region
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw := by
    dsimp [localLaw]
    exact lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have htake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      (lg21HiddenAccessAllTake testFeature) pair.1 pair.2) :=
    lg21HiddenAccessAllTake_measurable testFeature
  have hreport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) pair.1 pair.2) :=
    lg21HiddenAccessMeanGapReport_measurable testFeature baseMean hbaseMean gap
  have hnoReportEvent : MeasurableSet noReportEvent := by
    change MeasurableSet
      (lg21HiddenAccessOptionalNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap))
    exact lg21HiddenAccessOptionalNoReportEvent_measurable testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap) htake hreport
  have hglobalNoReportPositive : 0 < rawLaw noReportEvent := by
    simpa [rawLaw, noReportEvent] using
      (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess M testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessMeanGapReport testFeature baseMean gap) hnoAccess)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt hglobalNoReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw := by
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw noReportEvent
      (ne_of_gt hlocalNoReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw := by
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet
      (lg21HiddenAccessBaseRegionEvent testFeature region) :=
    lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion
  have hlocalIntersectionPositive : 0 < rawLaw
      (noReportEvent ∩ lg21HiddenAccessBaseRegionEvent testFeature region) := by
    change 0 < lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region) noReportEvent
      at hlocalNoReportPositive
    rw [lg21NormalizedRestriction_apply rawLaw hnoReportEvent]
      at hlocalNoReportPositive
    exact (ENNReal.mul_pos_iff.mp hlocalNoReportPositive).2
  have hglobalPBO : ∀ᵐ publicBase ∂globalActionLaw.map publicObservation,
      candidate.noReportValue publicBase =
        ∫ skill, skill ∂condDistrib latent publicObservation
          globalActionLaw publicBase := by
    simpa [candidate, rawLaw, noReportEvent, rawObservation,
      globalActionLaw, publicObservation, latent] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_condDistribMean_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
        baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite)
  have hglobalSelectedPositive : 0 < globalActionLaw
      (publicObservation ⁻¹' selected) := by
    change 0 < (lg21NormalizedRestriction rawLaw noReportEvent).map rawObservation
      (publicObservation ⁻¹' selected)
    rw [Measure.map_apply
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
      (hregion.preimage measurable_fst)]
    change 0 < lg21NormalizedRestriction rawLaw noReportEvent
      (lg21HiddenAccessBaseRegionEvent testFeature region)
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw noReportEvent
      (lg21HiddenAccessBaseRegionEvent testFeature region) hnoReportEvent
      hlocalIntersectionPositive
  have hactionLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, noReportEvent, rawObservation,
      globalActionLaw, localActionLaw] using
      (lg21HiddenAccessAllTakeMeanGap_localNoReportActionLaw_eq_selectedGlobal
        M testFeature baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite gap region hregion)
  have hlocalPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw publicObservation latent candidate.noReportValue
    measurable_fst measurable_snd hglobalPBO selected hregion hglobalSelectedPositive
  unfold LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
  dsimp only
  simpa only [localLaw, noReportEvent, rawObservation, localActionLaw,
    publicObservation, latent, selected, ← hactionLaw] using hlocalPBO

/-- The all-take cutoff candidate's displayed no-report payoff has the exact
literal raw-population mixture formula almost everywhere on its retained
public-base support.  In particular, the `Z = 0` component remains present
with its original source mass; this is not an access-only posterior. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_rawMixture_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
    letI : IsProbabilityMeasure candidateLaw :=
      lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap
    ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
      let anchor := baseMean publicBase + gap
      let joint := gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance
      let lowerMass := joint publicBase
        (selectedFiber (lg21OptionalFullBaseNoReportEvent
          (Base := LG21NonTestFeature Feature testFeature -> ℝ) anchor) publicBase)
      candidate.noReportValue publicBase =
        ((M.accessLaw {false}).toReal +
          ((M.accessLaw {true}) * lowerMass).toReal)⁻¹ *
          ((M.accessLaw {false}).toReal * baseMean publicBase +
            ((M.accessLaw {true}) * lowerMass).toReal *
              lg21OptionalFullBaseNoReportValue
                baseMean hbaseMean baseVariance noiseVariance anchor publicBase) := by
  intro candidate candidateLaw
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap)
  have hPBO :=
    lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_condDistribMean_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
      baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite
  have hRCD :=
    lg21HiddenAccessAllTakeMeanGap_noReport_condDistrib_skill_base_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
      baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite
  filter_upwards [hPBO, hRCD] with publicBase hPBO hRCD
  rw [hPBO, hRCD]
  simpa [candidate] using
    (lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_eq_rawMixture
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite gap publicBase (by infer_instance))

/-- Source-facing scalar form of the all-take/high-score candidate's literal
no-report PBO.  At every retained public base outside a null set, the displayed
candidate value is exactly the paper's optional-report mixture evaluated at
the actual score cutoff `m(base) + gap`. -/
theorem lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_optionalNoReportMixture_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (gap : ℝ)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      hnoAccessFinite haccessFinite gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature)
      (lg21HiddenAccessMeanGapReport testFeature baseMean gap)
    letI : IsProbabilityMeasure candidateLaw :=
      lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap
    ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
      let scoreVariance := baseVariance + noiseVariance
      let scoreLaw := lg21HiddenAccessGaussianScoreLaw
        (baseMean publicBase) scoreVariance (by linarith)
      let anchor := baseMean publicBase + gap
      candidate.noReportValue publicBase =
        lg21OptionalNoReportMixtureEstimate
          (M.accessLaw {true}).toReal (baseMean publicBase) scoreLaw
          (fun cutoff => lg21OptionalFullBaseNoReportValue
            baseMean hbaseMean baseVariance noiseVariance cutoff publicBase)
          anchor := by
  intro candidate candidateLaw
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw] using
      (lg21HiddenAccessAllTakeMeanGap_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature baseMean hbaseMean gap)
  have hPBO :=
    lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportValue_eq_condDistribMean_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
      baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite
  have hRCD :=
    lg21HiddenAccessAllTakeMeanGap_noReport_condDistrib_skill_base_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean gap
      baseVariance noiseVariance hsourceFactor hnoAccessFinite haccessFinite
  filter_upwards [hPBO, hRCD] with publicBase hPBO hRCD
  rw [hPBO, hRCD]
  simpa [candidate] using
    (lg21HiddenAccessAllTakeMeanGap_scoreNormalizedKernel_mean_eq_optionalNoReportMixture
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance
      (M.accessLaw {false}) (M.accessLaw {true})
      (lg21HiddenAccess_accessLaw_false_toReal_eq_one_sub_true M)
      hnoAccessFinite haccessFinite gap publicBase (by infer_instance))

end

end LG21TestOptionalPolicies
