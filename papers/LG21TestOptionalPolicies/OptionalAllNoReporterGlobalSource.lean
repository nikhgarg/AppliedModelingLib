import AppliedModelingLib.Foundations.Probability.FiniteGaussianSignalKernelRCD
import LG21TestOptionalPolicies.FullProfileGaussianSequentialBridge
import LG21TestOptionalPolicies.OptionalAllNoReporterCandidateSource
import LG21TestOptionalPolicies.SelectedConditionalRCD
import LG21TestOptionalPolicies.SelectedConditionalRestriction
import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge

/-!
# Full-base candidate entry at the optional all-no-reporter endpoint

This module keeps the entire non-test public base profile in the candidate
action law.  In particular, it never applies a fixed-base calculation to a
population mixed over base profiles.  The raw source law is factored as a
base law followed by a base-indexed score/skill kernel; the candidate's
no-report value is the literal lower-score selected mean of that kernel.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability

/-! ## Global candidate-entry certificate -/

/-- A positive-mass entry certificate over a literal population whose members
may have different public base profiles. -/
def LG21OptionalGlobalPositiveMassEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega → Base) (skill : Omega → ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Prop :=
  ∃ entrants : Set Omega,
    0 < sourceLaw entrants ∧
      ∀ omega, omega ∈ entrants →
        candidate.noReportValue (base omega) <
          lg21OptionalCandidateTestExpectedValue candidate (skill omega) (base omega)

/-- Pointwise strict gain from testing under a Gaussian candidate.  This is
the one-agent form of the existing positive-mass entry calculation. -/
theorem lg21_optional_candidate_gaussian_pointwise_test_gain
    {Base : Type*}
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (base : Base) (skill : ℝ) (noiseVariance : NNReal) (hvariance : noiseVariance ≠ 0)
    (htestLaw : ∀ latentSkill,
      candidate.testLaw latentSkill base = gaussianReal latentSkill noiseVariance)
    (hreportedWeakGain : ∀ score,
      candidate.reportDecision base score = true →
        candidate.noReportValue base ≤ candidate.reportedValue base score)
    (hstrict : StrictMono (candidate.reportedValue base))
    (anchor : ℝ)
    (hanchor : candidate.noReportValue base < candidate.reportedValue base anchor)
    (hreportsAboveAnchor : ∀ score, anchor < score →
      candidate.reportDecision base score = true) :
    candidate.noReportValue base <
      lg21OptionalCandidateTestExpectedValue candidate skill base := by
  have hentry : LG21OptionalPositiveMassEntry (Measure.dirac skill) Set.univ
      candidate base := by
    exact lg21_optional_positiveMassEntry_of_candidate_gaussian_report_gain
      (Measure.dirac skill) Set.univ (by simp) candidate base noiseVariance
      hvariance htestLaw hreportedWeakGain hstrict anchor hanchor hreportsAboveAnchor
  exact hentry.2 skill (Set.mem_univ skill)

/-- Lift a pointwise Gaussian candidate gain to a positive-mass certificate
over the actual source population.  No marginalization over base profiles is
performed: every member is evaluated at its own `base omega`. -/
theorem lg21_optional_globalEntry_of_candidate_gaussian_report_gain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (skill : Omega → ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (noiseVariance : NNReal) (hvariance : noiseVariance ≠ 0)
    (htestLaw : ∀ latentSkill publicBase,
      candidate.testLaw latentSkill publicBase = gaussianReal latentSkill noiseVariance)
    (hreportedWeakGain : ∀ publicBase score,
      candidate.reportDecision publicBase score = true →
        candidate.noReportValue publicBase ≤ candidate.reportedValue publicBase score)
    (hstrict : ∀ publicBase, StrictMono (candidate.reportedValue publicBase))
    (anchor : ℝ)
    (hanchor : ∀ publicBase,
      candidate.noReportValue publicBase < candidate.reportedValue publicBase anchor)
    (hreportsAboveAnchor : ∀ publicBase score, anchor < score →
      candidate.reportDecision publicBase score = true) :
    LG21OptionalGlobalPositiveMassEntry sourceLaw base skill candidate := by
  refine ⟨Set.univ, ?_, ?_⟩
  · rw [IsProbabilityMeasure.measure_univ]
    exact zero_lt_one
  · intro omega _
    exact lg21_optional_candidate_gaussian_pointwise_test_gain
      candidate (base omega) (skill omega) noiseVariance hvariance
      (fun latentSkill => htestLaw latentSkill (base omega))
      (fun score => hreportedWeakGain (base omega) score)
      (hstrict (base omega)) anchor (hanchor (base omega))
      (fun score hscore => hreportsAboveAnchor (base omega) score hscore)

/-! ## Full-base Gaussian candidate action law -/

/-- The public score/skill event corresponding to a high-score candidate's
literal no-report branch, retaining the full base profile. -/
def lg21OptionalFullBaseNoReportEvent {Base : Type*} (anchor : ℝ) :
    Set (Base × (ℝ × ℝ)) :=
  {pair | pair.2.1 < anchor}

theorem lg21OptionalFullBaseNoReportEvent_measurable
    {Base : Type*} [MeasurableSpace Base] (anchor : ℝ) :
    MeasurableSet (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) := by
  change MeasurableSet
    ((fun pair : Base × (ℝ × ℝ) => pair.2.1) ⁻¹' Set.Iio anchor)
  exact measurableSet_Iio.preimage (measurable_fst.comp measurable_snd)

theorem lg21OptionalFullBaseNoReportEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (anchor : ℝ) (base : Base) :
    selectedFiber (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) base =
      lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ := by
  ext scoreSkill
  simp [selectedFiber, lg21OptionalFullBaseNoReportEvent,
    lg21OptionalHighScoreCandidateNoReportEvent]

/-- The public score/skill event corresponding to the high-score candidate's
literal report branch.  The base profile is retained even though the action
threshold itself only uses the realized score. -/
def lg21OptionalFullBaseReportEvent {Base : Type*} (anchor : ℝ) :
    Set (Base × (ℝ × ℝ)) :=
  {pair | anchor ≤ pair.2.1}

theorem lg21OptionalFullBaseReportEvent_measurable
    {Base : Type*} [MeasurableSpace Base] (anchor : ℝ) :
    MeasurableSet (lg21OptionalFullBaseReportEvent (Base := Base) anchor) := by
  change MeasurableSet
    ((fun pair : Base × (ℝ × ℝ) => pair.2.1) ⁻¹' Set.Ici anchor)
  exact measurableSet_Ici.preimage (measurable_fst.comp measurable_snd)

theorem lg21OptionalFullBaseReportEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (anchor : ℝ) (base : Base) :
    selectedFiber (lg21OptionalFullBaseReportEvent (Base := Base) anchor) base =
      Set.Ici anchor ×ˢ Set.univ := by
  ext scoreSkill
  simp [selectedFiber, lg21OptionalFullBaseReportEvent]

/-- The base-indexed lower-score conditional mean used by the candidate. -/
def lg21OptionalFullBaseNoReportValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ) (anchor : ℝ) (base : Base) : ℝ :=
  lg21OptionalScorePosteriorLowerTailMean
    (gaussianReal (baseMean base)
      (baseVariance + noiseVariance).toNNReal)
    (Kernel.sectR (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) base)
    anchor

/-- The full-base high-score candidate uses the raw posterior at a reported
score and the literal lower-score conditional mean at a non-report. -/
def lg21OptionalFullBaseRawGaussianHighScoreCandidate
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ) (anchor : ℝ) :
    LG21OptionalCandidateBranchData ℝ Base ℝ where
  testLaw := fun latentSkill _base => gaussianReal latentSkill noiseVariance.toNNReal
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  reportDecision := fun _base score => lg21OptionalHighScoreCandidateReports anchor score
  reportedValue := fun publicBase score =>
    lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance publicBase score
  noReportValue := fun publicBase =>
    lg21OptionalFullBaseNoReportValue
      baseMean hbaseMean baseVariance noiseVariance anchor publicBase
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
    simpa [lg21OptionalHighScoreCandidateReports] using
      (lg21_optional_highScoreCandidate_continuation_integrable_of_affine
        anchor
        (lg21OptionalFullBaseNoReportValue
          baseMean hbaseMean baseVariance noiseVariance anchor publicBase)
        (gaussianSignalPriorWeight baseVariance noiseVariance * baseMean publicBase)
        (gaussianSignalWeight baseVariance noiseVariance)
        noiseVariance.toNNReal latentSkill)

/-- The candidate's high-score report decision is measurable in the full
public `(base, score)` observation. -/
theorem lg21OptionalFullBaseRawGaussianHighScoreCandidate_reportDecision_measurable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ) :
    Measurable (fun pair : Base × ℝ =>
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          pair.1 pair.2) := by
  apply measurable_to_bool
  have htail : MeasurableSet {pair : Base × ℝ | anchor ≤ pair.2} :=
    (measurableSet_Ici : MeasurableSet (Set.Ici anchor)).preimage
      (measurable_snd : Measurable fun pair : Base × ℝ => pair.2)
  convert htail using 1
  ext pair
  simp [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
    lg21OptionalHighScoreCandidateReports]

/-- The candidate's literal source report event is exactly the preimage of
the full-base report action event. -/
theorem lg21_optional_fullBaseCandidate_sourceReportEvent_eq_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ) :
    {omega |
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          (base omega) (score omega) = true} =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21OptionalFullBaseReportEvent (Base := Base) anchor := by
  ext omega
  simp [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
    lg21OptionalHighScoreCandidateReports, lg21OptionalFullBaseReportEvent]

/-- At each retained base profile, the raw full-base score/skill kernel is
the displayed score law followed by the Gaussian posterior kernel. -/
theorem lg21_optional_fullBaseGaussian_jointKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : Base) :
    gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance base =
      gaussianReal (baseMean base)
        (baseVariance + noiseVariance).toNNReal ⊗ₘ
        Kernel.sectR (gaussianSignalPosteriorBaseKernel
          baseMean hbaseMean baseVariance noiseVariance) base := by
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  rw [gaussianSignalJointKernel_factorization
    baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance]
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    gaussianLocationKernel_apply]

/-- A score-lower-tail rectangle has the same mass under a score/posterior
composition product as under its score marginal. -/
theorem lg21_optional_compProd_score_lowerTail_mass
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (posterior : Kernel ℝ ℝ) [IsMarkovKernel posterior]
    (anchor : ℝ) :
    (scoreLaw ⊗ₘ posterior)
        (lg21OptionalHighScoreCandidateNoReportEvent anchor ×ˢ Set.univ) =
      scoreLaw (lg21OptionalHighScoreCandidateNoReportEvent anchor) := by
  let lower := lg21OptionalHighScoreCandidateNoReportEvent anchor
  have hlower : MeasurableSet lower := measurableSet_Iio
  calc
    (scoreLaw ⊗ₘ posterior) (lower ×ˢ Set.univ) =
        ((scoreLaw ⊗ₘ posterior).map Prod.fst) lower := by
          symm
          rw [Measure.map_apply measurable_fst hlower]
          congr 1
          ext pair
          simp
    _ = scoreLaw lower := by
      change (scoreLaw ⊗ₘ posterior).fst lower = scoreLaw lower
      rw [Measure.fst_compProd]

/-- A score-upper-tail rectangle has the same mass under a score/posterior
composition product as under its score marginal. -/
theorem lg21_optional_compProd_score_upperTail_mass
    (scoreLaw : Measure ℝ) [IsProbabilityMeasure scoreLaw]
    (posterior : Kernel ℝ ℝ) [IsMarkovKernel posterior]
    (anchor : ℝ) :
    (scoreLaw ⊗ₘ posterior) (Set.Ici anchor ×ˢ Set.univ) =
      scoreLaw (Set.Ici anchor) := by
  calc
    (scoreLaw ⊗ₘ posterior) (Set.Ici anchor ×ˢ Set.univ) =
        ((scoreLaw ⊗ₘ posterior).map Prod.fst) (Set.Ici anchor) := by
          symm
          rw [Measure.map_apply measurable_fst measurableSet_Ici]
          congr 1
          ext pair
          simp
    _ = scoreLaw (Set.Ici anchor) := by
      change (scoreLaw ⊗ₘ posterior).fst (Set.Ici anchor) = scoreLaw (Set.Ici anchor)
      rw [Measure.fst_compProd]

/-- Every retained base fibre gives the candidate's literal no-report action
strictly positive mass.  This is a fibrewise fact, not a pointwise value
assigned on a null fibre. -/
theorem lg21_optional_fullBaseGaussian_noReport_fibre_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (base : Base) :
    0 < gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance base
      (selectedFiber
        (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) base) := by
  have hscoreVariancePos : 0 < baseVariance + noiseVariance := by linarith
  have hscoreVarianceNN : (baseVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariancePos)
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  rw [lg21_optional_fullBaseGaussian_jointKernel_apply
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance base]
  rw [lg21OptionalFullBaseNoReportEvent_selectedFiber]
  rw [lg21_optional_compProd_score_lowerTail_mass]
  exact lg21_gaussianReal_Iio_pos (baseMean base) anchor hscoreVarianceNN

/-- Every retained base fibre gives the candidate's literal report action
strictly positive mass.  Positivity is established before normalizing the
selected report branch. -/
theorem lg21_optional_fullBaseGaussian_report_fibre_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (base : Base) :
    0 < gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance base
      (selectedFiber
        (lg21OptionalFullBaseReportEvent (Base := Base) anchor) base) := by
  have hscoreVariancePos : 0 < baseVariance + noiseVariance := by linarith
  have hscoreVarianceNN : (baseVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariancePos)
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  rw [lg21_optional_fullBaseGaussian_jointKernel_apply
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance base]
  rw [lg21OptionalFullBaseReportEvent_selectedFiber]
  rw [lg21_optional_compProd_score_upperTail_mass]
  exact lt_of_lt_of_le
    (lg21_gaussianReal_Ioi_pos (baseMean base) anchor hscoreVarianceNN)
    (measure_mono Set.Ioi_subset_Ici_self)

/-- The source kernel after selecting the literal full-base no-report action.
Every fibre is normalized only after its positive action mass has been
established by `lg21_optional_fullBaseGaussian_noReport_fibre_positive`. -/
def lg21OptionalFullBaseSelectedNoReportKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ) : Kernel Base (ℝ × ℝ) := by
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  exact selectedNormalizedKernel
    (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
    (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)

/-- The candidate's base-indexed no-report value is exactly the mean of the
literal selected raw source kernel.  The equality is fibrewise, retaining the
base coordinate instead of collapsing it into a mixed score distribution. -/
theorem lg21_optional_fullBaseNoReportValue_eq_selectedKernelMean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (base : Base) :
    lg21OptionalFullBaseNoReportValue
      baseMean hbaseMean baseVariance noiseVariance anchor base =
      ∫ scoreSkill, scoreSkill.2 ∂
        lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor base := by
  let scoreLaw := gaussianReal (baseMean base)
    (baseVariance + noiseVariance).toNNReal
  let posterior := Kernel.sectR (gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean baseVariance noiseVariance) base
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let lower := lg21OptionalHighScoreCandidateNoReportEvent anchor
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hrawApply : rawKernel base = scoreLaw ⊗ₘ posterior := by
    exact lg21_optional_fullBaseGaussian_jointKernel_apply
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance base
  have hselectedApply :
      lg21OptionalFullBaseSelectedNoReportKernel
          baseMean hbaseMean baseVariance noiseVariance anchor base =
        lg21NormalizedRestriction (rawKernel base) (selectedFiber event base) := by
    change selectedNormalizedKernel rawKernel event base = _
    rw [selectedNormalizedKernel_apply
      (lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor)]
  have hselectedFactor :
      lg21NormalizedRestriction (rawKernel base) (selectedFiber event base) =
        lg21NormalizedRestriction scoreLaw lower ⊗ₘ posterior := by
    rw [hrawApply, lg21OptionalFullBaseNoReportEvent_selectedFiber]
    exact lg21_optional_normalizedRestriction_compProd_score_lowerTail
      scoreLaw posterior anchor
  have hintegrableSelected : Integrable Prod.snd
      (lg21NormalizedRestriction (rawKernel base) (selectedFiber event base)) := by
    rw [hrawApply, lg21OptionalFullBaseNoReportEvent_selectedFiber]
    exact lg21_optional_canonicalGaussianScorePosterior_lowerTail_integrable
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance base anchor
  have hintegrableComp : Integrable Prod.snd
      (lg21NormalizedRestriction scoreLaw lower ⊗ₘ posterior) := by
    rw [← hselectedFactor]
    exact hintegrableSelected
  letI : IsFiniteMeasure scoreLaw := by
    dsimp [scoreLaw]
    infer_instance
  letI : SFinite (lg21NormalizedRestriction scoreLaw lower) := by
    unfold lg21NormalizedRestriction
    infer_instance
  unfold lg21OptionalFullBaseNoReportValue
    lg21OptionalScorePosteriorLowerTailMean
  rw [hselectedApply, hselectedFactor]
  symm
  simpa using (Measure.integral_compProd hintegrableComp)

/-- The base-indexed candidate no-report value is strictly below its reported
posterior value at the reporting boundary. -/
theorem lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (base : Base) :
    (lg21OptionalFullBaseRawGaussianHighScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance anchor).noReportValue base <
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportedValue base anchor := by
  have hscoreVariancePos : 0 < baseVariance + noiseVariance := by linarith
  have hscoreVarianceNN : (baseVariance + noiseVariance).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hscoreVariancePos)
  have htailPositive : 0 <
      gaussianReal (baseMean base) (baseVariance + noiseVariance).toNNReal
        (lg21OptionalHighScoreCandidateNoReportEvent anchor) := by
    exact lg21_gaussianReal_Iio_pos (baseMean base) anchor hscoreVarianceNN
  change lg21OptionalFullBaseNoReportValue
      baseMean hbaseMean baseVariance noiseVariance anchor base <
    lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance base anchor
  exact lg21_optional_scorePosteriorLowerTailMean_lt_rawGaussianAt_anchor
    (baseMean base) (baseVariance + noiseVariance).toNNReal
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance base anchor htailPositive

/-- The explicit full-base candidate gives strict expected testing gain to
every source member, evaluated at that member's retained base profile. -/
theorem lg21_optional_globalEntry_of_fullBaseGaussianCandidate
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    LG21OptionalGlobalPositiveMassEntry sourceLaw base skill
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor) := by
  have hnoiseVarianceNN : noiseVariance.toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hnoiseVariance)
  apply lg21_optional_globalEntry_of_candidate_gaussian_report_gain
    sourceLaw base skill
    (lg21OptionalFullBaseRawGaussianHighScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance anchor)
    noiseVariance.toNNReal hnoiseVarianceNN
  · intro latentSkill publicBase
    rfl
  · intro publicBase score hreport
    have hge : anchor ≤ score := by
      simpa [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
        lg21OptionalHighScoreCandidateReports] using hreport
    have hanchor :=
      lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase
    have hstrict := lg21_optional_rawGaussianPosteriorMean_strictMono
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase
    have hmono := hstrict.monotone hge
    change lg21OptionalFullBaseNoReportValue
        baseMean hbaseMean baseVariance noiseVariance anchor publicBase ≤
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase score
    exact le_trans (le_of_lt hanchor) hmono
  · intro publicBase
    exact lg21_optional_rawGaussianPosteriorMean_strictMono
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase
  · intro publicBase
    exact lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  · intro publicBase score hscore
    simp [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
      lg21OptionalHighScoreCandidateReports, le_of_lt hscore]

/-! ## Literal-source transport of the base-indexed candidate -/

/-- The candidate's source no-report event is exactly the preimage of its
full-base public action event.  The retained base and realized score are both
visible in this equality. -/
theorem lg21_optional_fullBaseCandidate_sourceNoReportEvent_eq_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ) :
    {omega |
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          (base omega) (score omega) = false} =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21OptionalFullBaseNoReportEvent (Base := Base) anchor := by
  ext omega
  simp [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
    lg21OptionalHighScoreCandidateReports,
    lg21OptionalFullBaseNoReportEvent]

/-- The selected full-base no-report event has positive mass under the
Gaussian base/score/skill experiment.  Positivity is obtained from every
base fibre's nondegenerate Gaussian lower tail, not from totalized
normalization. -/
theorem lg21_optional_fullBaseGaussian_selectedNoReport_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have hfibre : ∀ base,
      0 < rawKernel base (selectedFiber event base) := by
    intro base
    exact lg21_optional_fullBaseGaussian_noReport_fibre_positive
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor base
  have hmassMeasurable : Measurable
      (fun base => rawKernel base (selectedFiber event base)) := by
    exact Kernel.measurable_kernel_prodMk_left hevent
  change 0 < (baseLaw ⊗ₘ rawKernel) event
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsupp : Function.support
      (fun base => rawKernel base (selectedFiber event base)) = Set.univ := by
    ext base
    simp [Function.mem_support, ne_of_gt (hfibre base)]
  rw [hsupp, IsProbabilityMeasure.measure_univ]
  norm_num

/-- The selected full-base report event has positive mass under the Gaussian
base/score/skill experiment.  This is the literal high-score action event,
not an assumed reporter population. -/
theorem lg21_optional_fullBaseGaussian_selectedReport_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalFullBaseReportEvent (Base := Base) anchor) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21OptionalFullBaseReportEvent (Base := Base) anchor
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseReportEvent_measurable (Base := Base) anchor
  have hfibre : ∀ base,
      0 < rawKernel base (selectedFiber event base) := by
    intro base
    exact lg21_optional_fullBaseGaussian_report_fibre_positive
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor base
  have hmassMeasurable : Measurable
      (fun base => rawKernel base (selectedFiber event base)) := by
    exact Kernel.measurable_kernel_prodMk_left hevent
  change 0 < (baseLaw ⊗ₘ rawKernel) event
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsupp : Function.support
      (fun base => rawKernel base (selectedFiber event base)) = Set.univ := by
    ext base
    simp [Function.mem_support, ne_of_gt (hfibre base)]
  rw [hsupp, IsProbabilityMeasure.measure_univ]
  norm_num

/-- The selected full-base no-report kernel is an actual regular conditional
law of `(score, skill)` given the retained base under the normalized
candidate no-report experiment.  The equality is correctly almost everywhere
under that selected base marginal. -/
theorem lg21_optional_fullBaseGaussian_selectedNoReport_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_optional_fullBaseGaussian_selectedNoReport_positive
            baseLaw baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance anchor))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst selectedLaw =ᵐ[selectedLaw.map Prod.fst]
      lg21OptionalFullBaseSelectedNoReportKernel
        baseMean hbaseMean baseVariance noiseVariance anchor := by
  intro selectedLaw
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  let rawLaw := baseLaw ⊗ₘ rawKernel
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have hfibre : ∀ publicBase,
      selectionMass rawKernel event publicBase ≠ 0 := by
    intro publicBase
    change rawKernel publicBase (selectedFiber event publicBase) ≠ 0
    exact ne_of_gt
      (lg21_optional_fullBaseGaussian_noReport_fibre_positive
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor publicBase)
  have hselected : rawLaw event ≠ 0 := by
    exact ne_of_gt
      (lg21_optional_fullBaseGaussian_selectedNoReport_positive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor)
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw event hselected
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  change condDistrib Prod.snd Prod.fst selectedLaw =ᵐ[selectedLaw.map Prod.fst]
    lg21OptionalFullBaseSelectedNoReportKernel
      baseMean hbaseMean baseVariance noiseVariance anchor
  simpa [selectedLaw, rawLaw, rawKernel, event,
    lg21OptionalFullBaseSelectedNoReportKernel] using
    (condDistrib_snd_given_fst_normalizedRestriction_ae
      (μ := baseLaw) (κ := rawKernel) hevent hfibre hselected)

/-- The candidate no-report value is the actual selected-law conditional
mean of skill, almost everywhere at the retained public base profiles. -/
theorem lg21_optional_fullBaseCandidate_noReportValue_eq_condDistribMean_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_optional_fullBaseGaussian_selectedNoReport_positive
            baseLaw baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance anchor))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    ∀ᵐ publicBase ∂selectedLaw.map Prod.fst,
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).noReportValue publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂
          condDistrib Prod.snd Prod.fst selectedLaw publicBase := by
  intro selectedLaw
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt
        (lg21_optional_fullBaseGaussian_selectedNoReport_positive
          baseLaw baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hRCD := lg21_optional_fullBaseGaussian_selectedNoReport_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance anchor
  have hcandidate : ∀ publicBase,
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).noReportValue publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂
          lg21OptionalFullBaseSelectedNoReportKernel
            baseMean hbaseMean baseVariance noiseVariance anchor publicBase := by
    intro publicBase
    exact lg21_optional_fullBaseNoReportValue_eq_selectedKernelMean
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  filter_upwards [hRCD] with publicBase hkernel
  rw [hcandidate publicBase, hkernel]

/-- On the candidate's positive-mass report branch, selection is measurable
in the retained public `(base, score)` observation.  Consequently the raw
Gaussian posterior remains the conditional skill law, correctly only almost
everywhere under the selected report observation marginal. -/
theorem lg21_optional_fullBaseGaussian_selectedReport_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21OptionalFullBaseReportEvent (Base := Base) anchor)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_optional_fullBaseGaussian_selectedReport_positive
            baseLaw baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance anchor))
        (measure_ne_top _ _)
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
  let observationEvent : Set (Base × ℝ) := {score | anchor ≤ score.2}
  let reportEvent := lg21OptionalFullBaseReportEvent (Base := Base) anchor
  let association : Base × (ℝ × ℝ) → (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) → Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) → ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
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
      (ne_of_gt
        (lg21_optional_fullBaseGaussian_selectedReport_positive
          baseLaw baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hreportEvent : MeasurableSet reportEvent :=
    lg21OptionalFullBaseReportEvent_measurable (Base := Base) anchor
  have hobservationEvent : MeasurableSet observationEvent := by
    exact measurableSet_Ici.preimage measurable_snd
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
    dsimp [reportEvent, association, observationEvent,
      lg21OptionalFullBaseReportEvent]
    simp
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

/-- The candidate's reported score value is the literal selected-report
conditional mean of skill.  It is asserted only on the positive-mass report
action law and only almost everywhere in the full `(base, score)` public
observation. -/
theorem lg21_optional_fullBaseCandidate_reportedValue_eq_condDistribMean_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21OptionalFullBaseReportEvent (Base := Base) anchor)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_optional_fullBaseGaussian_selectedReport_positive
            baseLaw baseMean hbaseMean baseVariance noiseVariance
            hbaseVariance hnoiseVariance anchor))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂selectedLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportedValue
          publicObservation.1 publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
          (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
          selectedLaw publicObservation := by
  intro selectedLaw
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt
        (lg21_optional_fullBaseGaussian_selectedReport_positive
          baseLaw baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance anchor))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hRCD := lg21_optional_fullBaseGaussian_selectedReport_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance anchor
  filter_upwards [hRCD] with publicObservation hposterior
  rw [hposterior]
  change lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance
      publicObservation.1 publicObservation.2 =
    ∫ latentSkill, latentSkill ∂gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance publicObservation
  rfl

/-- Exact transport of the candidate's literal no-report population through
an actual base-indexed score/skill source factorization. -/
theorem lg21_optional_fullBaseCandidate_selectedNoReport_mappedLaw_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    (lg21NormalizedRestriction sourceLaw
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = false}).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor) := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have haction :
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = false} = observation ⁻¹' event := by
    simpa [observation, event] using
      (lg21_optional_fullBaseCandidate_sourceNoReportEvent_eq_preimage
        base score skill baseMean hbaseMean baseVariance noiseVariance anchor)
  rw [haction]
  calc
    (lg21NormalizedRestriction sourceLaw (observation ⁻¹' event)).map observation =
        lg21NormalizedRestriction (sourceLaw.map observation) event :=
      lg21_optional_normalizedRestriction_map_preimage
        sourceLaw observation hobservation event hevent
    _ = lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) event := by
          rw [show sourceLaw.map observation =
            baseLaw ⊗ₘ gaussianSignalJointKernel
              baseMean hbaseMean baseVariance noiseVariance by
              simpa [observation] using hsourceFactor]

/-- The literal source no-report action has positive mass under the exact
full-base Gaussian source factorization. -/
theorem lg21_optional_fullBaseCandidate_sourceNoReport_positive_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    0 < sourceLaw {omega |
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          (base omega) (score omega) = false} := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21OptionalFullBaseNoReportEvent (Base := Base) anchor
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseNoReportEvent_measurable (Base := Base) anchor
  have haction :
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = false} = observation ⁻¹' event := by
    simpa [observation, event] using
      (lg21_optional_fullBaseCandidate_sourceNoReportEvent_eq_preimage
        base score skill baseMean hbaseMean baseVariance noiseVariance anchor)
  rw [haction, ← Measure.map_apply hobservation hevent]
  rw [show sourceLaw.map observation =
    baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance by
      simpa [observation] using hsourceFactor]
  exact lg21_optional_fullBaseGaussian_selectedNoReport_positive
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance anchor

/-- Exact transport of the candidate's literal report population through an
actual base-indexed score/skill source factorization. -/
theorem lg21_optional_fullBaseCandidate_selectedReport_mappedLaw_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    (lg21NormalizedRestriction sourceLaw
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = true}).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalFullBaseReportEvent (Base := Base) anchor) := by
  let actionObservation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21OptionalFullBaseReportEvent (Base := Base) anchor
  have hactionObservation : Measurable actionObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseReportEvent_measurable (Base := Base) anchor
  have haction :
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = true} = actionObservation ⁻¹' event := by
    simpa [actionObservation, event] using
      (lg21_optional_fullBaseCandidate_sourceReportEvent_eq_preimage
        base score skill baseMean hbaseMean baseVariance noiseVariance anchor)
  rw [haction]
  calc
    (lg21NormalizedRestriction sourceLaw (actionObservation ⁻¹' event)).map
        actionObservation =
        lg21NormalizedRestriction (sourceLaw.map actionObservation) event :=
      lg21_optional_normalizedRestriction_map_preimage
        sourceLaw actionObservation hactionObservation event hevent
    _ = lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) event := by
          rw [show sourceLaw.map actionObservation =
            baseLaw ⊗ₘ gaussianSignalJointKernel
              baseMean hbaseMean baseVariance noiseVariance by
              simpa [actionObservation] using hsourceFactor]

/-- The literal source report action has positive mass under the exact
full-base Gaussian source factorization. -/
theorem lg21_optional_fullBaseCandidate_sourceReport_positive_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    0 < sourceLaw {omega |
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          (base omega) (score omega) = true} := by
  let actionObservation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21OptionalFullBaseReportEvent (Base := Base) anchor
  have hactionObservation : Measurable actionObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21OptionalFullBaseReportEvent_measurable (Base := Base) anchor
  have haction :
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = true} = actionObservation ⁻¹' event := by
    simpa [actionObservation, event] using
      (lg21_optional_fullBaseCandidate_sourceReportEvent_eq_preimage
        base score skill baseMean hbaseMean baseVariance noiseVariance anchor)
  rw [haction, ← Measure.map_apply hactionObservation hevent]
  rw [show sourceLaw.map actionObservation =
    baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance by
      simpa [actionObservation] using hsourceFactor]
  exact lg21_optional_fullBaseGaussian_selectedReport_positive
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance anchor

/-- On a literal source population, the high-score candidate's reported
value is the conditional skill mean on the candidate's own positive-mass
report action law.  The conditioning observation is exactly the retained
full `(base, score)` report observation. -/
theorem lg21_optional_fullBaseCandidate_reportedValue_eq_condDistribMean_ae_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance anchor
    let actionLaw :=
      (lg21NormalizedRestriction sourceLaw
        {omega | candidate.reportDecision (base omega) (score omega) = true}).map
        (fun omega => (base omega, (score omega, skill omega)))
    letI : IsProbabilityMeasure actionLaw := by
      letI : IsProbabilityMeasure
          (lg21NormalizedRestriction sourceLaw
            {omega | candidate.reportDecision (base omega) (score omega) = true}) :=
        lg21NormalizedRestriction_isProbability sourceLaw _
          (ne_of_gt
            (lg21_optional_fullBaseCandidate_sourceReport_positive_of_factorization
              sourceLaw base score skill hbase hscore hskill baseLaw
              baseMean hbaseMean baseVariance noiseVariance
              hbaseVariance hnoiseVariance anchor hsourceFactor))
          (measure_ne_top _ _)
      exact Measure.isProbabilityMeasure_map
        (hbase.prodMk (hscore.prodMk hskill)).aemeasurable
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
      candidate.reportedValue publicObservation.1 publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
          (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
          actionLaw publicObservation := by
  intro candidate actionLaw
  let selectedGaussianLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance)
    (lg21OptionalFullBaseReportEvent (Base := Base) anchor)
  have hactionLaw : actionLaw = selectedGaussianLaw := by
    exact lg21_optional_fullBaseCandidate_selectedReport_mappedLaw_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance anchor hsourceFactor
  have hconditionalMean :=
    lg21_optional_fullBaseCandidate_reportedValue_eq_condDistribMean_ae
      baseLaw baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor
  simpa only [hactionLaw] using hconditionalMean

/-- Source-facing global certificate for the optional all-no-reporter
candidate.  It retains the entire base profile in the source disintegration,
proves the candidate no-report event has actual positive mass, identifies the
literal selected action law, and gives a positive-mass entry certificate over
the source population itself. -/
theorem lg21_optional_fullBaseGaussian_candidate_source_certificate_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    (0 < sourceLaw {omega |
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          (base omega) (score omega) = false}) ∧
    ((lg21NormalizedRestriction sourceLaw
      {omega |
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega) = false}).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)) ∧
    (∀ publicBase,
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).noReportValue publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂
          lg21OptionalFullBaseSelectedNoReportKernel
            baseMean hbaseMean baseVariance noiseVariance anchor publicBase) ∧
    LG21OptionalGlobalPositiveMassEntry sourceLaw base skill
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lg21_optional_fullBaseCandidate_sourceNoReport_positive_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor hsourceFactor
  · exact lg21_optional_fullBaseCandidate_selectedNoReport_mappedLaw_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance anchor hsourceFactor
  · intro publicBase
    exact lg21_optional_fullBaseNoReportValue_eq_selectedKernelMean
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  · exact lg21_optional_globalEntry_of_fullBaseGaussianCandidate
      sourceLaw base skill baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor

/-- The literal LG21 positive-access population has an exact full-base
factorization through the base-indexed raw Gaussian score/skill kernel.  This
is stronger than an a.e. posterior statement and is the transport required by
the global candidate certificate. -/
theorem lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21ContinuousPopulationBase testFeature student,
              (lg21ContinuousPopulationFeature testFeature student,
                lg21ContinuousPopulationSkill student))) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hfullBaseFactorization⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let law := lg21ContinuousGaussianAccessPopulationLaw M
  let base := lg21ContinuousPopulationBase testFeature
  let score := lg21ContinuousPopulationFeature testFeature
  let skill := lg21ContinuousPopulationSkill (Feature := Feature)
  have hskill : Measurable skill := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable score := by
    exact hskill.add hnoise
  have hbase : Measurable base :=
    lg21ContinuousPopulationBase_measurable testFeature
  let scoreKernel : Kernel (LG21NonTestFeature Feature testFeature → ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let posteriorKernel : Kernel
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  have hprimitiveExtend :
      (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        (fun primitive =>
          (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
            primitive.1)) =
        gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) :=
    lg21ContinuousGaussianFullProfilePrimitiveLaw_eq_extend_fullBaseLatent
      M testFeature
  have hupdate :
      gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) =
        gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) :=
    gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
      baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
      (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
      hfullBaseFactorization
  have hfactorAssoc : law.map (fun student =>
      ((base student, score student), skill student)) =
        baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
    calc
      law.map (fun student =>
          ((base student, score student), skill student)) =
          (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
            (fun primitive =>
              (lg21ContinuousGaussianFullProfileObservation testFeature primitive,
                primitive.1)) := by
            simpa [law, base, score, skill] using
              (lg21ContinuousGaussianAccessPopulation_full_base_score_skill_law
                M haccess testFeature)
      _ = gaussianSignalExtendBaseLatentLaw
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature)
          (M.noiseVariance testFeature : ℝ) := hprimitiveExtend
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) := hupdate
      _ = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
        exact gaussianSignalBaseScoreLatentLaw_factorization
          baseLaw baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ)
          hbaseVariance htestNoiseVariance
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  have hassocObservation : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      ((base student, score student), skill student)) :=
    (hbase.prodMk hscore).prodMk hskill
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21ContinuousPopulationBase testFeature student,
            (lg21ContinuousPopulationFeature testFeature student,
              lg21ContinuousPopulationSkill student))) =
        (law.map (fun student =>
          ((base student, score student), skill student))).map
          MeasurableEquiv.prodAssoc := by
          rw [Measure.map_map (MeasurableEquiv.measurable _) hassocObservation]
          rfl
    _ = (baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel).map
          MeasurableEquiv.prodAssoc := by rw [hfactorAssoc]
    _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
          rw [Measure.compProd_assoc']
          rw [← gaussianSignalJointKernel_factorization
            baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ)
            hbaseVariance htestNoiseVariance]

/-- Literal-access-population source certificate for the optional
all-no-reporter endpoint.  The output retains the full non-test profile in
both the action law and the active-entry certificate; it does not invoke a
fixed-base theorem on the mixed population. -/
theorem lg21ContinuousGaussianAccessPopulation_optional_allNoReporter_candidate_source_certificate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (anchor : ℝ) :
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
      (0 < (lg21ContinuousGaussianAccessPopulationLaw M)
        {student |
          (lg21OptionalFullBaseRawGaussianHighScoreCandidate
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ) anchor).reportDecision
              (lg21ContinuousPopulationBase testFeature student)
              (lg21ContinuousPopulationFeature testFeature student) = false}) ∧
      ((lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        {student |
          (lg21OptionalFullBaseRawGaussianHighScoreCandidate
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ) anchor).reportDecision
              (lg21ContinuousPopulationBase testFeature student)
              (lg21ContinuousPopulationFeature testFeature student) = false}).map
          (fun student =>
            (lg21ContinuousPopulationBase testFeature student,
              (lg21ContinuousPopulationFeature testFeature student,
                lg21ContinuousPopulationSkill student))) =
        lg21NormalizedRestriction
          (baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ))
          (lg21OptionalFullBaseNoReportEvent
            (Base := LG21NonTestFeature Feature testFeature → ℝ) anchor)) ∧
      (∀ publicBase,
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ) anchor).noReportValue publicBase =
          ∫ scoreSkill, scoreSkill.2 ∂
            lg21OptionalFullBaseSelectedNoReportKernel
              baseMean hbaseMean baseVariance
                (M.noiseVariance testFeature : ℝ) anchor publicBase) ∧
      LG21OptionalGlobalPositiveMassEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        lg21ContinuousPopulationSkill
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ) anchor) := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hnoise : Measurable
      (lg21ContinuousPopulationNoise (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.2 testFeature
    exact (measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd)
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    exact hskill.add hnoise
  have hbase : Measurable
      (lg21ContinuousPopulationBase (Feature := Feature) testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  exact lg21_optional_fullBaseGaussian_candidate_source_certificate_of_factorization
    (lg21ContinuousGaussianAccessPopulationLaw M)
    (lg21ContinuousPopulationBase testFeature)
    (lg21ContinuousPopulationFeature testFeature)
    lg21ContinuousPopulationSkill
    hbase hscore hskill baseLaw baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
    hbaseVariance htestNoiseVariance anchor hsourceFactor

/-- On a literal source population, the all-no-reporter candidate's no-report
value is the conditional mean on the candidate's own positive-mass no-report
action law.  The law is first normalized on the literal source action event
and only then mapped to the full `(base, score, skill)` public experiment.
The conclusion is almost everywhere under that mapped law's retained-base
marginal; it does not define a belief on an unselected or null action branch. -/
theorem lg21_optional_fullBaseCandidate_sourceNoReportValue_eq_condDistribMean_ae_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance anchor
    let actionLaw :=
      (lg21NormalizedRestriction sourceLaw
        {omega | candidate.reportDecision (base omega) (score omega) = false}).map
        (fun omega => (base omega, (score omega, skill omega)))
    letI : IsProbabilityMeasure actionLaw := by
      letI : IsProbabilityMeasure
          (lg21NormalizedRestriction sourceLaw
            {omega | candidate.reportDecision (base omega) (score omega) = false}) :=
        lg21NormalizedRestriction_isProbability sourceLaw _
          (ne_of_gt
            (lg21_optional_fullBaseCandidate_sourceNoReport_positive_of_factorization
              sourceLaw base score skill hbase hscore hskill baseLaw
              baseMean hbaseMean baseVariance noiseVariance
              hbaseVariance hnoiseVariance anchor hsourceFactor))
          (measure_ne_top _ _)
      exact Measure.isProbabilityMeasure_map
        (hbase.prodMk (hscore.prodMk hskill)).aemeasurable
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
      candidate.noReportValue publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂
          condDistrib Prod.snd Prod.fst actionLaw publicBase := by
  intro candidate actionLaw
  let selectedGaussianLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance)
    (lg21OptionalFullBaseNoReportEvent (Base := Base) anchor)
  have hactionLaw : actionLaw = selectedGaussianLaw := by
    exact lg21_optional_fullBaseCandidate_selectedNoReport_mappedLaw_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance anchor hsourceFactor
  have hconditionalMean :=
    lg21_optional_fullBaseCandidate_noReportValue_eq_condDistribMean_ae
      baseLaw baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor
  simpa only [hactionLaw] using hconditionalMean

end

end LG21TestOptionalPolicies
