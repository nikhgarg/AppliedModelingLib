import LG21TestOptionalPolicies.ReportRequiredZeroTakerRecalibratedEntry
import LG21TestOptionalPolicies.OptionalSourceLocalRecalibratedEntry
import LG21TestOptionalPolicies.SelectedConditionalExpectation
import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredRegionSupport

/-!
# Local Gaussian candidates for report-required testing

This module constructs the literal high-skill candidate used to test a
positive public-base region with no current takers.  Its action rule is
`q >= 0` on the candidate region, leaving a strictly positive lower branch
`q < 0` from which the no-take PBO is recalibrated.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open AppliedModelingLib Probability

/-- The upper candidate branch is the nonnegative latent-skill tail. -/
def lg21ReportRequiredUpperTailTake (skill : ℝ) : Bool := decide (0 ≤ skill)

/-- The full source observation event on which the local upper candidate takes. -/
def lg21ReportRequiredUpperTailTakeEvent
    {Base : Type*} [MeasurableSpace Base] : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | 0 ≤ baseScoreSkill.2.2}

/-- The complementary full source observation event on which it does not take. -/
def lg21ReportRequiredUpperTailNoTakeEvent
    {Base : Type*} [MeasurableSpace Base] : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | baseScoreSkill.2.2 < 0}

theorem lg21ReportRequiredUpperTailTakeEvent_measurable
    {Base : Type*} [MeasurableSpace Base] :
    MeasurableSet (lg21ReportRequiredUpperTailTakeEvent (Base := Base)) := by
  change MeasurableSet
    ((fun baseScoreSkill : Base × (ℝ × ℝ) => baseScoreSkill.2.2) ⁻¹' Set.Ici 0)
  exact measurableSet_Ici.preimage (measurable_snd.comp measurable_snd)

theorem lg21ReportRequiredUpperTailNoTakeEvent_measurable
    {Base : Type*} [MeasurableSpace Base] :
    MeasurableSet (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)) := by
  change MeasurableSet
    ((fun baseScoreSkill : Base × (ℝ × ℝ) => baseScoreSkill.2.2) ⁻¹' Set.Iio 0)
  exact measurableSet_Iio.preimage (measurable_snd.comp measurable_snd)

theorem lg21ReportRequiredUpperTailTakeEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base] (publicBase : Base) :
    selectedFiber (lg21ReportRequiredUpperTailTakeEvent (Base := Base)) publicBase =
      Set.univ ×ˢ Set.Ici 0 := by
  ext scoreSkill
  simp [selectedFiber, lg21ReportRequiredUpperTailTakeEvent]

theorem lg21ReportRequiredUpperTailNoTakeEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base] (publicBase : Base) :
    selectedFiber (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)) publicBase =
      Set.univ ×ˢ Set.Iio 0 := by
  ext scoreSkill
  simp [selectedFiber, lg21ReportRequiredUpperTailNoTakeEvent]

/-- The high-tail candidate with literal Gaussian selected posterior means. -/
noncomputable def lg21ReportRequiredGaussianUpperTailCandidate
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ where
  testLaw := fun latentSkill _publicBase =>
    gaussianReal latentSkill noiseVariance.toNNReal
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  takeDecision := fun latentSkill _publicBase =>
    lg21ReportRequiredUpperTailTake latentSkill
  reportedPayoff := fun publicBase observedScore =>
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance)
      (Set.univ ×ˢ Set.Ici 0) observedScore
  noReportPayoff := fun publicBase =>
    ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
      (gaussianReal (baseMean publicBase) priorVariance.toNNReal)
      (Set.Iio 0)
  reportedPayoff_integrable := by
    intro latentSkill publicBase
    have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
    have hselected : 0 < gaussianReal (baseMean publicBase)
        priorVariance.toNNReal (Set.Ici 0) := by
      exact lt_of_lt_of_le
        (lg21_gaussianReal_Ioi_pos (baseMean publicBase) 0 hpriorVarianceNN)
        (measure_mono Set.Ioi_subset_Ici_self)
    simpa only using
      (lg21_selectedGaussianSignal_posteriorMean_integrable_gaussianShift
        (baseMean publicBase) priorVariance noiseVariance (Set.Ici 0)
        hpriorVariance hnoiseVariance measurableSet_Ici hselected latentSkill)
  estimationConsistent := True

theorem lg21ReportRequiredGaussianUpperTailCandidate_takeDecision_eq_true_iff
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).takeDecision
        latentSkill publicBase = true ↔ 0 ≤ latentSkill := by
  simp [lg21ReportRequiredGaussianUpperTailCandidate,
    lg21ReportRequiredUpperTailTake]

theorem lg21ReportRequiredGaussianUpperTailCandidate_takeDecision_eq_false_iff
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).takeDecision
        latentSkill publicBase = false ↔ latentSkill < 0 := by
  simp [lg21ReportRequiredGaussianUpperTailCandidate,
    lg21ReportRequiredUpperTailTake]

theorem lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedPosterior
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) (observedScore : ℝ) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).reportedPayoff
        publicBase observedScore =
      ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ Set.Ici 0) observedScore := by
  rfl

theorem lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedMean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) (observedScore : ℝ) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).reportedPayoff
        publicBase observedScore =
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        (Set.Ici 0) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  rw [lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedPosterior]
  rw [selectedNormalizedKernel_apply (MeasurableSet.univ.prod measurableSet_Ici)]
  congr 2
  ext latentSkill
  simp [selectedFiber]

theorem lg21_reportRequiredGaussianUpperTailCandidate_noReportPayoff_lt_zero
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).noReportPayoff
        publicBase < 0 := by
  let priorLaw : Measure ℝ :=
    gaussianReal (baseMean publicBase) priorVariance.toNNReal
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have hlowerPositive : 0 < priorLaw (Set.Iio 0) := by
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase) 0 hpriorVarianceNN
  have hintegrable : Integrable (fun latentSkill : ℝ => latentSkill)
      (lg21NormalizedRestriction priorLaw (Set.Iio 0)) := by
    have hraw : Integrable (fun latentSkill : ℝ => latentSkill) priorLaw := by
      dsimp [priorLaw]
      exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
    unfold lg21NormalizedRestriction
    exact hraw.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hlowerPositive))
  change (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction priorLaw (Set.Iio 0)) < 0
  apply lg21NormalizedRestriction_mean_lt_upper priorLaw (Set.Iio 0)
    (fun latentSkill : ℝ => latentSkill) 0 measurableSet_Iio hlowerPositive
    hintegrable
  intro latentSkill hlatentSkill
  exact hlatentSkill

theorem lg21_reportRequiredGaussianUpperTailCandidate_noReportPayoff_lt_reportedPayoff
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) (observedScore : ℝ) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).noReportPayoff
        publicBase <
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).reportedPayoff
          publicBase observedScore := by
  let posterior : Measure ℝ := gaussianSignalPosteriorKernel
    (baseMean publicBase) priorVariance noiseVariance observedScore
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  letI : IsFiniteMeasure posterior := by
    dsimp [posterior]
    rw [gaussianSignalPosteriorKernel_apply]
    infer_instance
  have hnoTake : candidate.noReportPayoff publicBase < 0 := by
    exact lg21_reportRequiredGaussianUpperTailCandidate_noReportPayoff_lt_zero
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance publicBase
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have hpriorTail : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal (Set.Ioi 0) :=
    lg21_gaussianReal_Ioi_pos (baseMean publicBase) 0 hpriorVarianceNN
  have hselectedPositive : 0 < posterior (Set.Ici 0) := by
    apply lt_of_lt_of_le
      (lg21_gaussianSignalPosterior_selected_pos
        (baseMean publicBase) priorVariance noiseVariance (Set.Ioi 0)
        hpriorVariance hnoiseVariance hpriorTail observedScore)
    exact measure_mono Set.Ioi_subset_Ici_self
  have hintegrable : Integrable (fun latentSkill : ℝ => latentSkill)
      (lg21NormalizedRestriction posterior (Set.Ici 0)) := by
    have hraw : Integrable (fun latentSkill : ℝ => latentSkill) posterior := by
      dsimp [posterior]
      rw [gaussianSignalPosteriorKernel_apply]
      exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
    unfold lg21NormalizedRestriction
    exact hraw.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hselectedPositive))
  rw [show candidate.reportedPayoff publicBase observedScore =
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction posterior (Set.Ici 0) by
    simpa [candidate, posterior] using
      (lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedMean
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance publicBase observedScore)]
  apply lg21NormalizedRestriction_mean_gt_lower posterior (Set.Ici 0)
    (fun latentSkill : ℝ => latentSkill) (candidate.noReportPayoff publicBase)
    measurableSet_Ici hselectedPositive hintegrable
  intro latentSkill hlatentSkill
  exact lt_of_lt_of_le hnoTake hlatentSkill

theorem lg21_reportRequiredGaussianUpperTailCandidate_takeMembers_bestRespond
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega → Base) (score skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    PositiveMassBranchMembersBestRespond sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance))
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
      (fun candidate omega =>
        candidate.noReportPayoff (base omega) ≤
          lg21ReportRequiredSequentialTakeExpectedPayoff candidate
            (skill omega) (base omega)) := by
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance
  rw [PositiveMassBranchMembersBestRespond]
  filter_upwards with omega
  letI : IsProbabilityMeasure (candidate.testLaw (skill omega) (base omega)) :=
    candidate.testLaw_isProbability (skill omega) (base omega)
  have hpoint : ∀ observedScore,
      candidate.noReportPayoff (base omega) <
        candidate.reportedPayoff (base omega) observedScore := by
    intro observedScore
    exact lg21_reportRequiredGaussianUpperTailCandidate_noReportPayoff_lt_reportedPayoff
      baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance (base omega) observedScore
  have hintegral := lg21_integral_lt_integral_of_ae_lt_probability
    (candidate.testLaw (skill omega) (base omega))
    (integrable_const (candidate.noReportPayoff (base omega)))
    (candidate.reportedPayoff_integrable (skill omega) (base omega))
    (Filter.Eventually.of_forall hpoint)
  change candidate.noReportPayoff (base omega) ≤
    ∫ observedScore, candidate.reportedPayoff (base omega) observedScore ∂
      candidate.testLaw (skill omega) (base omega)
  exact le_of_lt (by simpa using hintegral)

/-- The Gaussian joint kernel's latent-skill marginal is its displayed prior. -/
theorem lg21_gaussianSignalJointKernel_skill_marginal
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (publicBase : Base) :
    (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase).map
      Prod.snd = gaussianReal (baseMean publicBase) priorVariance.toNNReal := by
  rw [gaussianSignalJointKernel_apply]
  let primitive := gaussianSignalPair
    (baseMean publicBase) priorVariance noiseVariance
  let scoreSkill : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  have hscoreSkill : Measurable scoreSkill := by
    dsimp [scoreSkill]
    fun_prop
  calc
    (primitive.map scoreSkill).map Prod.snd =
        primitive.map (Prod.snd ∘ scoreSkill) := by
          rw [Measure.map_map measurable_snd hscoreSkill]
    _ = primitive.map Prod.fst := by rfl
    _ = gaussianReal (baseMean publicBase) priorVariance.toNNReal := by
      change Measure.map Prod.fst
        ((gaussianReal (baseMean publicBase) priorVariance.toNNReal).prod
          (gaussianReal 0 noiseVariance.toNNReal)) = _
      rw [Measure.map_fst_prod]
      simp

/-- The local upper candidate selects a positive mass in every Gaussian base
fibre before any normalization is performed. -/
theorem lg21_gaussianSignalJointKernel_upperTail_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (publicBase : Base) :
    0 < gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase
      (Set.univ ×ˢ Set.Ici 0) := by
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have htail : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal (Set.Ici 0) := by
    exact lt_of_lt_of_le
      (lg21_gaussianReal_Ioi_pos (baseMean publicBase) 0 hpriorVarianceNN)
      (measure_mono Set.Ioi_subset_Ici_self)
  calc
    gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase
        (Set.univ ×ˢ Set.Ici 0) =
        (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase).map
          Prod.snd (Set.Ici 0) := by
          symm
          rw [Measure.map_apply measurable_snd measurableSet_Ici]
          congr 1
          ext scoreSkill
          simp
    _ = gaussianReal (baseMean publicBase) priorVariance.toNNReal (Set.Ici 0) := by
      rw [lg21_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean priorVariance noiseVariance publicBase]
    _ > 0 := htail

/-- The local lower candidate branch also has positive mass in every
nondegenerate Gaussian base fibre. -/
theorem lg21_gaussianSignalJointKernel_lowerTail_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (publicBase : Base) :
    0 < gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase
      (Set.univ ×ˢ Set.Iio 0) := by
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have htail : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal (Set.Iio 0) :=
    lg21_gaussianReal_Iio_pos (baseMean publicBase) 0 hpriorVarianceNN
  calc
    gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase
        (Set.univ ×ˢ Set.Iio 0) =
        (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase).map
          Prod.snd (Set.Iio 0) := by
          symm
          rw [Measure.map_apply measurable_snd measurableSet_Iio]
          congr 1
          ext scoreSkill
          simp
    _ = gaussianReal (baseMean publicBase) priorVariance.toNNReal (Set.Iio 0) := by
      rw [lg21_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean priorVariance noiseVariance publicBase]
    _ > 0 := htail

theorem lg21_reportRequiredGaussianUpperTail_take_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredUpperTailTakeEvent (Base := Base)) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredUpperTailTakeEvent (Base := Base)
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailTakeEvent_measurable
  have hfibre : ∀ publicBase,
      0 < rawKernel publicBase (selectedFiber event publicBase) := by
    intro publicBase
    rw [lg21ReportRequiredUpperTailTakeEvent_selectedFiber]
    exact lg21_gaussianSignalJointKernel_upperTail_positive
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance publicBase
  have hmassMeasurable : Measurable
      (fun publicBase => rawKernel publicBase (selectedFiber event publicBase)) :=
    Kernel.measurable_kernel_prodMk_left hevent
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

theorem lg21_reportRequiredGaussianUpperTail_noTake_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailNoTakeEvent_measurable
  have hfibre : ∀ publicBase,
      0 < rawKernel publicBase (selectedFiber event publicBase) := by
    intro publicBase
    rw [lg21ReportRequiredUpperTailNoTakeEvent_selectedFiber]
    exact lg21_gaussianSignalJointKernel_lowerTail_positive
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance publicBase
  have hmassMeasurable : Measurable
      (fun publicBase => rawKernel publicBase (selectedFiber event publicBase)) :=
    Kernel.measurable_kernel_prodMk_left hevent
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

theorem lg21_reportRequiredGaussianUpperTailCandidate_sourceTakeEvent_eq_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    lg21ReportRequiredCandidateSourceTakeEvent base skill
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance) =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21ReportRequiredUpperTailTakeEvent (Base := Base) := by
  ext omega
  change
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).takeDecision
        (skill omega) (base omega) = true ↔ 0 ≤ skill omega
  exact lg21ReportRequiredGaussianUpperTailCandidate_takeDecision_eq_true_iff
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
    (skill omega) (base omega)

theorem lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTakeEvent_eq_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    lg21ReportRequiredCandidateSourceNoTakeEvent base skill
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance) =
      (fun omega => (base omega, (score omega, skill omega))) ⁻¹'
        lg21ReportRequiredUpperTailNoTakeEvent (Base := Base) := by
  ext omega
  change
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).takeDecision
        (skill omega) (base omega) = false ↔ skill omega < 0
  exact lg21ReportRequiredGaussianUpperTailCandidate_takeDecision_eq_false_iff
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
    (skill omega) (base omega)

theorem lg21_reportRequiredGaussianUpperTailCandidate_sourceTake_positive_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    0 < sourceLaw (lg21ReportRequiredCandidateSourceTakeEvent base skill
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)) := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21ReportRequiredUpperTailTakeEvent (Base := Base)
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailTakeEvent_measurable
  rw [lg21_reportRequiredGaussianUpperTailCandidate_sourceTakeEvent_eq_preimage
    base score skill baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance]
  rw [← Measure.map_apply hobservation hevent]
  rw [show sourceLaw.map observation =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance by
    simpa [observation] using hsourceFactor]
  exact lg21_reportRequiredGaussianUpperTail_take_positive
    baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance

theorem lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTake_positive_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    0 < sourceLaw (lg21ReportRequiredCandidateSourceNoTakeEvent base skill
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)) := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailNoTakeEvent_measurable
  rw [lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTakeEvent_eq_preimage
    base score skill baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance]
  rw [← Measure.map_apply hobservation hevent]
  rw [show sourceLaw.map observation =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance by
    simpa [observation] using hsourceFactor]
  exact lg21_reportRequiredGaussianUpperTail_noTake_positive
    baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance

theorem lg21_reportRequiredGaussianUpperTailCandidate_selectedTake_mappedLaw_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    (lg21NormalizedRestriction sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance))).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
        (lg21ReportRequiredUpperTailTakeEvent (Base := Base)) := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21ReportRequiredUpperTailTakeEvent (Base := Base)
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailTakeEvent_measurable
  have haction :
      lg21ReportRequiredCandidateSourceTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance) = observation ⁻¹' event := by
    simpa [observation, event] using
      (lg21_reportRequiredGaussianUpperTailCandidate_sourceTakeEvent_eq_preimage
        base score skill baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
  rw [haction]
  calc
    (lg21NormalizedRestriction sourceLaw (observation ⁻¹' event)).map observation =
        lg21NormalizedRestriction (sourceLaw.map observation) event :=
      lg21_normalizedRestriction_map_preimage sourceLaw observation
        hobservation event hevent
    _ = lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) event := by
      rw [show sourceLaw.map observation =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean priorVariance noiseVariance by
        simpa [observation] using hsourceFactor]

theorem lg21_reportRequiredGaussianUpperTailCandidate_selectedNoTake_mappedLaw_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    (lg21NormalizedRestriction sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance))).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
        (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)) := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailNoTakeEvent_measurable
  have haction :
      lg21ReportRequiredCandidateSourceNoTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance) = observation ⁻¹' event := by
    simpa [observation, event] using
      (lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTakeEvent_eq_preimage
        base score skill baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
  rw [haction]
  calc
    (lg21NormalizedRestriction sourceLaw (observation ⁻¹' event)).map observation =
        lg21NormalizedRestriction (sourceLaw.map observation) event :=
      lg21_normalizedRestriction_map_preimage sourceLaw observation
        hobservation event hevent
    _ = lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) event := by
      rw [show sourceLaw.map observation =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean priorVariance noiseVariance by
        simpa [observation] using hsourceFactor]

/-- The candidate's literal conditional `(score, skill)` law after selecting
the lower no-take branch at a public base. -/
noncomputable def lg21ReportRequiredUpperTailSelectedNoTakeKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) : Kernel Base (ℝ × ℝ) := by
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  exact selectedNormalizedKernel
    (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance)
    (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base))

theorem lg21_reportRequiredGaussianUpperTail_selectedNoTake_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredUpperTailNoTakeEvent (Base := Base))
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_reportRequiredGaussianUpperTail_noTake_positive
            baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst selectedLaw =ᵐ[selectedLaw.map Prod.fst]
      lg21ReportRequiredUpperTailSelectedNoTakeKernel
        baseMean hbaseMean priorVariance noiseVariance := by
  intro selectedLaw
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  let rawLaw := baseLaw ⊗ₘ rawKernel
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailNoTakeEvent_measurable
  have hfibre : ∀ publicBase,
      selectionMass rawKernel event publicBase ≠ 0 := by
    intro publicBase
    change rawKernel publicBase (selectedFiber event publicBase) ≠ 0
    rw [lg21ReportRequiredUpperTailNoTakeEvent_selectedFiber]
    exact ne_of_gt
      (lg21_gaussianSignalJointKernel_lowerTail_positive
        baseMean hbaseMean priorVariance noiseVariance hpriorVariance publicBase)
  have hselected : rawLaw event ≠ 0 := by
    exact ne_of_gt
      (lg21_reportRequiredGaussianUpperTail_noTake_positive
        baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance)
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw event hselected
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  change condDistrib Prod.snd Prod.fst selectedLaw =ᵐ[selectedLaw.map Prod.fst]
    lg21ReportRequiredUpperTailSelectedNoTakeKernel
      baseMean hbaseMean priorVariance noiseVariance
  simpa [selectedLaw, rawLaw, rawKernel, event,
    lg21ReportRequiredUpperTailSelectedNoTakeKernel] using
    (condDistrib_snd_given_fst_normalizedRestriction_ae
      (μ := baseLaw) (κ := rawKernel) hevent hfibre hselected)

theorem lg21ReportRequiredUpperTailSelectedNoTakeKernel_skill_marginal
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (publicBase : Base) :
    (lg21ReportRequiredUpperTailSelectedNoTakeKernel
      baseMean hbaseMean priorVariance noiseVariance publicBase).map Prod.snd =
      lg21NormalizedRestriction
        (gaussianReal (baseMean publicBase) priorVariance.toNNReal) (Set.Iio 0) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event :=
    lg21ReportRequiredUpperTailNoTakeEvent_measurable
  change (selectedNormalizedKernel rawKernel event publicBase).map Prod.snd = _
  rw [selectedNormalizedKernel_apply hevent]
  rw [lg21ReportRequiredUpperTailNoTakeEvent_selectedFiber]
  have hpreimage : (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' (Set.Iio 0) =
      Set.univ ×ˢ Set.Iio 0 := by
    ext scoreSkill
    simp
  rw [← hpreimage]
  calc
    (lg21NormalizedRestriction (rawKernel publicBase)
      ((Prod.snd : ℝ × ℝ → ℝ) ⁻¹' (Set.Iio 0))).map Prod.snd =
        lg21NormalizedRestriction ((rawKernel publicBase).map Prod.snd)
          (Set.Iio 0) :=
      lg21_normalizedRestriction_map_preimage
        (rawKernel publicBase) Prod.snd measurable_snd (Set.Iio 0) measurableSet_Iio
    _ = lg21NormalizedRestriction
        (gaussianReal (baseMean publicBase) priorVariance.toNNReal)
          (Set.Iio 0) := by
      rw [lg21_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean priorVariance noiseVariance publicBase]

theorem lg21ReportRequiredUpperTailSelectedNoTakeKernel_skill_mean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (publicBase : Base) :
    (∫ scoreSkill, scoreSkill.2 ∂
      lg21ReportRequiredUpperTailSelectedNoTakeKernel
        baseMean hbaseMean priorVariance noiseVariance publicBase) =
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianReal (baseMean publicBase) priorVariance.toNNReal) (Set.Iio 0) := by
  rw [← lg21ReportRequiredUpperTailSelectedNoTakeKernel_skill_marginal
    baseMean hbaseMean priorVariance noiseVariance publicBase]
  symm
  simpa only [Function.comp_apply] using
    (integral_map_of_stronglyMeasurable measurable_snd stronglyMeasurable_id)

/-- The high-tail candidate's no-take payoff is the literal conditional mean
on its own positive lower-tail action law.  The source factorization is used
only to transport that selected law; no value is assigned to a null branch. -/
theorem lg21_reportRequiredGaussianUpperTailCandidate_noTakePBO_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hnoTakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance))) :
    LG21ReportRequiredCandidateNoTakePBO sourceLaw base score skill
      (hbase.prodMk (hscore.prodMk hskill))
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
      hnoTakePositive := by
  classical
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  let sourceActionLaw : Measure Omega := lg21NormalizedRestriction sourceLaw
    (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate)
  letI : IsProbabilityMeasure sourceActionLaw := by
    dsimp [sourceActionLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hnoTakePositive) (measure_ne_top _ _)
  let actionLaw : Measure (Base × (ℝ × ℝ)) := sourceActionLaw.map
    (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure actionLaw := by
    dsimp [actionLaw]
    exact Measure.isProbabilityMeasure_map
      (hbase.prodMk (hscore.prodMk hskill)).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  let event := lg21ReportRequiredUpperTailNoTakeEvent (Base := Base)
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let selectedLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) event
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw, event]
    exact lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt (lg21_reportRequiredGaussianUpperTail_noTake_positive
        baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedLaw :
      actionLaw = selectedLaw := by
    simpa [actionLaw, sourceActionLaw, candidate, selectedLaw, event] using
      (lg21_reportRequiredGaussianUpperTailCandidate_selectedNoTake_mappedLaw_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor)
  have hRCD := lg21_reportRequiredGaussianUpperTail_selectedNoTake_condDistrib_ae
    baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance
  have hmean : ∀ publicBase,
      candidate.noReportPayoff publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂
          lg21ReportRequiredUpperTailSelectedNoTakeKernel
            baseMean hbaseMean priorVariance noiseVariance publicBase := by
    intro publicBase
    simpa [candidate] using
      (lg21ReportRequiredUpperTailSelectedNoTakeKernel_skill_mean
        baseMean hbaseMean priorVariance noiseVariance publicBase).symm
  unfold LG21ReportRequiredCandidateNoTakePBO
  dsimp only
  change ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportPayoff publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        Prod.fst actionLaw publicBase
  have hRCDAction :
      condDistrib Prod.snd Prod.fst actionLaw =ᵐ[actionLaw.map Prod.fst]
        lg21ReportRequiredUpperTailSelectedNoTakeKernel
          baseMean hbaseMean priorVariance noiseVariance := by
    simpa only [hselectedLaw] using hRCD
  have hskillRCD :
      condDistrib (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        Prod.fst actionLaw =ᵐ[actionLaw.map Prod.fst]
          (condDistrib Prod.snd Prod.fst actionLaw).map Prod.snd := by
    simpa only [Function.comp_apply] using
      (condDistrib_comp (μ := actionLaw)
        (X := (Prod.fst : Base × (ℝ × ℝ) → Base))
        (Y := (Prod.snd : Base × (ℝ × ℝ) → ℝ × ℝ))
        measurable_snd.aemeasurable measurable_snd)
  filter_upwards [hRCDAction, hskillRCD] with publicBase hkernel hskillKernel
  have hkernelMap :
      ((condDistrib Prod.snd Prod.fst actionLaw).map Prod.snd) publicBase =
        (lg21ReportRequiredUpperTailSelectedNoTakeKernel
          baseMean hbaseMean priorVariance noiseVariance).map Prod.snd publicBase := by
    rw [Kernel.map_apply _ measurable_snd, Kernel.map_apply _ measurable_snd]
    exact congrArg (Measure.map Prod.snd) hkernel
  rw [hmean publicBase, hskillKernel, hkernelMap]
  symm
  rw [Kernel.map_apply _ measurable_snd]
  simpa only [Function.comp_apply] using
    (integral_map_of_stronglyMeasurable
      (μ := (lg21ReportRequiredUpperTailSelectedNoTakeKernel
        baseMean hbaseMean priorVariance noiseVariance publicBase))
      measurable_snd stronglyMeasurable_id)

/-- After the candidate's upper-tail taking selection, this is the literal
posterior kernel given the actually visible `(base, score)` pair. -/
noncomputable def lg21ReportRequiredUpperTailSelectedTakeKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) : Kernel (Base × ℝ) ℝ := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  exact selectedNormalizedKernel
    (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance)
    (Set.univ ×ˢ Set.Ici 0)

theorem lg21ReportRequiredUpperTailSelectedTakeKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (publicBase : Base) (observedScore : ℝ) :
    lg21ReportRequiredUpperTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance (publicBase, observedScore) =
      lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        (Set.Ici 0) := by
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  change selectedNormalizedKernel posteriorKernel (Set.univ ×ˢ Set.Ici 0)
      (publicBase, observedScore) = _
  rw [selectedNormalizedKernel_apply (MeasurableSet.univ.prod measurableSet_Ici)]
  rw [gaussianSignalPosteriorBaseKernel_apply,
    gaussianSignalPosteriorKernel_apply]
  congr 1
  ext latentSkill
  simp [selectedFiber]

theorem lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedTakeKernelMean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicBase : Base) (observedScore : ℝ) :
    (lg21ReportRequiredGaussianUpperTailCandidate
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance).reportedPayoff
        publicBase observedScore =
      ∫ latentSkill, latentSkill ∂
        lg21ReportRequiredUpperTailSelectedTakeKernel
          baseMean hbaseMean priorVariance noiseVariance (publicBase, observedScore) := by
  rw [lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedMean]
  rw [lg21ReportRequiredUpperTailSelectedTakeKernel_apply]

private theorem lg21ReportRequiredUpperTail_selectedTake_fibre_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (publicObservation : Base × ℝ) :
    selectionMass
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (Set.univ ×ˢ Set.Ici 0) publicObservation ≠ 0 := by
  unfold selectionMass
  rw [gaussianSignalPosteriorBaseKernel_apply]
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have htail : 0 < gaussianReal (baseMean publicObservation.1)
      priorVariance.toNNReal (Set.Ioi 0) :=
    lg21_gaussianReal_Ioi_pos
      (baseMean publicObservation.1) 0 hpriorVarianceNN
  have hselected : 0 < gaussianSignalPosteriorKernel
      (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
      (Set.Ici 0) :=
    lt_of_lt_of_le
      (lg21_gaussianSignalPosterior_selected_pos
        (baseMean publicObservation.1) priorVariance noiseVariance (Set.Ioi 0)
        hpriorVariance hnoiseVariance htail publicObservation.2)
      (measure_mono Set.Ioi_subset_Ici_self)
  have hfibre : selectedFiber (Set.univ ×ˢ Set.Ici 0) publicObservation = Set.Ici 0 := by
    ext latentSkill
    simp [selectedFiber]
  have hkernelEq : gaussianReal
      (AppliedModelingLib.Probability.gaussianSignalWeight priorVariance noiseVariance *
          publicObservation.2 +
        AppliedModelingLib.Probability.gaussianSignalPriorWeight priorVariance noiseVariance *
          baseMean publicObservation.1)
      (AppliedModelingLib.Probability.gaussianSignalPosteriorVariance
        priorVariance noiseVariance)
      (selectedFiber (Set.univ ×ˢ Set.Ici 0) publicObservation) =
      gaussianSignalPosteriorKernel
        (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
        (Set.Ici 0) := by
    rw [gaussianSignalPosteriorKernel_apply]
    congr 1
    ext latentSkill
    simp [selectedFiber]
  rw [hkernelEq]
  exact ne_of_gt hselected

/-- The high-tail candidate's reported-score PBO is a regular conditional
skill law on its own selected positive taking branch.  Selection is by the
known public decision rule, while conditioning is only on the observed
`(base, score)` pair. -/
theorem lg21_reportRequiredGaussianUpperTail_selectedTake_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredUpperTailTakeEvent (Base := Base))
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21_reportRequiredGaussianUpperTail_take_positive
            baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib
      (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
      selectedLaw =ᵐ[selectedLaw.map
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
      lg21ReportRequiredUpperTailSelectedTakeKernel
        baseMean hbaseMean priorVariance noiseVariance := by
  intro selectedLaw
  let rawLaw := baseLaw ⊗ₘ gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + noiseVariance).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  let observedLaw := baseLaw ⊗ₘ scoreKernel
  let selectedEvent := lg21ReportRequiredUpperTailTakeEvent (Base := Base)
  let observedEvent : Set ((Base × ℝ) × ℝ) := Set.univ ×ˢ Set.Ici 0
  let association : Base × (ℝ × ℝ) → (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) → Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) → ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure observedLaw := by
    dsimp [observedLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw selectedEvent
      (ne_of_gt
        (lg21_reportRequiredGaussianUpperTail_take_positive
          baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedEvent : MeasurableSet selectedEvent :=
    lg21ReportRequiredUpperTailTakeEvent_measurable
  have hobservedEvent : MeasurableSet observedEvent :=
    MeasurableSet.univ.prod measurableSet_Ici
  have hassociation : Measurable association := by
    dsimp [association]
    fun_prop
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hselectionPositive : ∀ publicObservation,
      selectionMass posteriorKernel observedEvent publicObservation ≠ 0 := by
    intro publicObservation
    simpa [posteriorKernel, observedEvent] using
      (lg21ReportRequiredUpperTail_selectedTake_fibre_positive
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance publicObservation)
  letI : IsMarkovKernel
      (selectedNormalizedKernel posteriorKernel observedEvent) :=
    selectedNormalizedKernel_isMarkov hobservedEvent hselectionPositive
  have hselectedPreimage :
      selectedEvent = association ⁻¹' observedEvent := by
    ext scoreSkill
    simp [selectedEvent, association, observedEvent,
      lg21ReportRequiredUpperTailTakeEvent]
  have hrawAssoc : rawLaw.map association = observedLaw ⊗ₘ posteriorKernel := by
    simpa [rawLaw, association, observedLaw, posteriorKernel,
      gaussianSignalBaseScoreLatentLaw] using
      (gaussianSignalBaseScoreLatentLaw_factorization
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
  have hselectedAssoc :
      selectedLaw.map association =
        lg21NormalizedRestriction (rawLaw.map association) observedEvent := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw selectedEvent by rfl,
      hselectedPreimage]
    exact lg21_normalizedRestriction_map_preimage
      rawLaw association hassociation observedEvent hobservedEvent
  have hselectedFactor :
      selectedLaw.map association =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map association =
          lg21NormalizedRestriction (rawLaw.map association) observedEvent := hselectedAssoc
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
            observedEvent := by rw [hrawAssoc]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent :=
        normalizedRestriction_compProd_selectedNormalizedKernel
          (μ := observedLaw) (κ := posteriorKernel)
          hobservedEvent hselectionPositive
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel observedEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have hselectedObservation :
      selectedLaw.map observation =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent := by
    calc
      selectedLaw.map observation = (selectedLaw.map association).map Prod.fst := by
        rw [Measure.map_map measurable_fst hassociation]
        rfl
      _ = (normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent).map Prod.fst := by
        rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      selectedLaw.map (fun scoreSkill => (observation scoreSkill, latent scoreSkill)) =
        selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map (fun scoreSkill =>
          (observation scoreSkill, latent scoreSkill)) =
          selectedLaw.map association := by rfl
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := hselectedFactor
      _ = selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
        rw [hselectedObservation]
  change condDistrib latent observation selectedLaw =ᵐ[selectedLaw.map observation]
    lg21ReportRequiredUpperTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance
  simpa [posteriorKernel, observedEvent,
    lg21ReportRequiredUpperTailSelectedTakeKernel] using
    (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hlatent hselectedJoint)

/-- The high-tail candidate's reported payoff is the literal conditional mean
on its own positive taking/reporting law. -/
theorem lg21_reportRequiredGaussianUpperTailCandidate_reportedPBO_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (htakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill
        (lg21ReportRequiredGaussianUpperTailCandidate
          baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance))) :
    LG21ReportRequiredCandidateReportedPBO sourceLaw base score skill
      (hbase.prodMk (hscore.prodMk hskill))
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
      htakePositive := by
  classical
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  let sourceActionLaw : Measure Omega := lg21NormalizedRestriction sourceLaw
    (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate)
  letI : IsProbabilityMeasure sourceActionLaw := by
    dsimp [sourceActionLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  let actionLaw : Measure (Base × (ℝ × ℝ)) := sourceActionLaw.map
    (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure actionLaw := by
    dsimp [actionLaw]
    exact Measure.isProbabilityMeasure_map
      (hbase.prodMk (hscore.prodMk hskill)).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let selectedLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance)
    (lg21ReportRequiredUpperTailTakeEvent (Base := Base))
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt (lg21_reportRequiredGaussianUpperTail_take_positive
        baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedLaw : actionLaw = selectedLaw := by
    simpa [actionLaw, sourceActionLaw, candidate, selectedLaw] using
      (lg21_reportRequiredGaussianUpperTailCandidate_selectedTake_mappedLaw_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor)
  have hRCD := lg21_reportRequiredGaussianUpperTail_selectedTake_condDistrib_ae
    baseLaw baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance
  have hRCDAction :
      condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw =ᵐ[actionLaw.map
          (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
        lg21ReportRequiredUpperTailSelectedTakeKernel
          baseMean hbaseMean priorVariance noiseVariance := by
    simpa only [hselectedLaw] using hRCD
  unfold LG21ReportRequiredCandidateReportedPBO
  dsimp only
  change ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedPayoff publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation
  filter_upwards [hRCDAction] with publicObservation hkernel
  rw [lg21ReportRequiredGaussianUpperTailCandidate_reportedPayoff_eq_selectedTakeKernelMean,
    hkernel]

/-- The high-tail candidate has both literal selected-action PBOs and its
changed taking members weakly best respond before the score is drawn. -/
theorem lg21_reportRequiredGaussianUpperTailCandidate_recalibratedSourceBranchEntry_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    LG21ReportRequiredRecalibratedSourceBranchEntry sourceLaw base score skill
      (hbase.prodMk (hscore.prodMk hskill))
      (lg21ReportRequiredGaussianUpperTailCandidate
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance) := by
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  have htakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceTakeEvent base skill candidate) := by
    simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_sourceTake_positive_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor)
  have hnoTakePositive : 0 < sourceLaw
      (lg21ReportRequiredCandidateSourceNoTakeEvent base skill candidate) := by
    simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_sourceNoTake_positive_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor)
  refine ⟨htakePositive, hnoTakePositive, ?_, ?_, ?_⟩
  · simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_reportedPBO_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor htakePositive)
  · simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_noTakePBO_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor hnoTakePositive)
  · simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_takeMembers_bestRespond
        sourceLaw base score skill baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)

/-- The literal positive-access `LG21ContinuousGaussianPopulation` supplies
the report-required upper-tail candidate without a caller-supplied posterior
or generic factorization certificate.  The candidate sees the full non-test
profile before testing, takes on the latent upper tail, and every PBO in the
result is calibrated on its own positive source action law. -/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_upperTail_recalibratedSourceBranchEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      IsProbabilityMeasure baseLaw ∧
        LG21ReportRequiredRecalibratedSourceBranchEntry
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          lg21ContinuousPopulationSkill
          (lg21ContinuousPopulationFullPublicObservation_measurable testFeature)
          (lg21ReportRequiredGaussianUpperTailCandidate
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ)
            hbaseVariance htestNoiseVariance) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseVariance, hbaseLaw, ?_⟩
  simpa only [lg21ContinuousPopulationFullPublicObservation] using
    (lg21_reportRequiredGaussianUpperTailCandidate_recalibratedSourceBranchEntry_of_factorization
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
      hbaseVariance htestNoiseVariance hsourceFactor)

def LG21ReportRequiredSourcePositiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ → Base → Bool) (region : Set Base)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Prop :=
  MeasurableSet region ∧
    ∃ hregionPositive : 0 < sourceLaw (base ⁻¹' region),
      sourceLaw (base ⁻¹' region ∩
        {omega | currentTake (skill omega) (base omega) = true}) = 0 ∧
      let localLaw : Measure Omega :=
        lg21NormalizedRestriction sourceLaw (base ⁻¹' region)
      letI : IsProbabilityMeasure localLaw :=
        lg21NormalizedRestriction_isProbability sourceLaw _
          (ne_of_gt hregionPositive) (measure_ne_top _ _)
      (∀ᵐ omega ∂localLaw, currentTake (skill omega) (base omega) = false) ∧
      LG21ReportRequiredRecalibratedSourceBranchEntry
        localLaw base score skill hpublic candidate

def LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ → Base → Bool) : Prop :=
  ∀ region candidate,
    ¬ LG21ReportRequiredSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake region candidate

/-- Report-required local stability restricted to deviations that preserve
the fixed score law of the source equilibrium. -/
def LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (fixedTestLaw : ℝ → Base → Measure ℝ)
    (currentTake : ℝ → Base → Bool) : Prop :=
  ∀ region candidate,
    (∀ latentSkill publicBase,
      candidate.testLaw latentSkill publicBase =
        fixedTestLaw latentSkill publicBase) ->
    ¬ LG21ReportRequiredSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake region candidate

theorem lg21_reportRequired_source_not_stable_of_positiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ → Base → Bool)
    (region : Set Base)
    (candidate : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hentry : LG21ReportRequiredSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake region candidate) :
    ¬ LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake := by
  intro hstable
  exact hstable region candidate hentry

theorem lg21_reportRequired_localGaussian_not_stable_of_positive_zeroTaker_region
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (currentTake : ℝ → Base → Bool)
    (hcurrentTake : Measurable (fun omega =>
      currentTake (skill omega) (base omega)))
    (region : Set Base) (hregion : MeasurableSet region)
    (hregionPositive : 0 < sourceLaw (base ⁻¹' region))
    (hcurrentZero : sourceLaw (base ⁻¹' region ∩
      {omega | currentTake (skill omega) (base omega) = true}) = 0) :
    ¬ LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
        currentTake := by
  let sourceRegion : Set Omega := base ⁻¹' region
  let publicObservation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  have hsourceRegionMeasurable : MeasurableSet sourceRegion := by
    simpa [sourceRegion] using hregion.preimage hbase
  have hpublicObservation : Measurable publicObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hbaseMarginal : sourceLaw.map base = baseLaw := by
    calc
      sourceLaw.map base = (sourceLaw.map publicObservation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hpublicObservation]
        rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).map Prod.fst := by
        rw [show sourceLaw.map publicObservation =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean priorVariance noiseVariance by
            simpa [publicObservation] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).fst = baseLaw
        rw [Measure.fst_compProd]
  have hbaseRegionPositive : 0 < baseLaw region := by
    rw [← hbaseMarginal, Measure.map_apply hbase hregion]
    exact hregionPositive
  let localLaw : Measure Omega := lg21NormalizedRestriction sourceLaw sourceRegion
  let localBaseLaw : Measure Base := lg21NormalizedRestriction baseLaw region
  letI : IsProbabilityMeasure localLaw := by
    dsimp [localLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw sourceRegion
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localBaseLaw := by
    dsimp [localBaseLaw]
    exact lg21NormalizedRestriction_isProbability baseLaw region
      (ne_of_gt hbaseRegionPositive) (measure_ne_top _ _)
  have hlocalFactor :
      localLaw.map publicObservation = localBaseLaw ⊗ₘ
        gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance := by
    simpa [localLaw, localBaseLaw, sourceRegion, publicObservation] using
      (lg21_optional_normalizedBaseRegion_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean priorVariance noiseVariance region hregion hsourceFactor)
  let candidate := lg21ReportRequiredGaussianUpperTailCandidate
    baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hbranch : LG21ReportRequiredRecalibratedSourceBranchEntry
      localLaw base score skill (hbase.prodMk (hscore.prodMk hskill)) candidate := by
    simpa [candidate] using
      (lg21_reportRequiredGaussianUpperTailCandidate_recalibratedSourceBranchEntry_of_factorization
        localLaw base score skill hbase hscore hskill localBaseLaw
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hlocalFactor)
  let currentTakeEvent : Set Omega :=
    {omega | currentTake (skill omega) (base omega) = true}
  have hcurrentTakeEventMeasurable : MeasurableSet currentTakeEvent := by
    change MeasurableSet
      ((fun omega => currentTake (skill omega) (base omega)) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage hcurrentTake
  have hcurrentTakeLocalZero : localLaw currentTakeEvent = 0 := by
    rw [show localLaw = lg21NormalizedRestriction sourceLaw sourceRegion by rfl,
      lg21NormalizedRestriction_apply sourceLaw
        (event := sourceRegion) (target := currentTakeEvent)
        hcurrentTakeEventMeasurable]
    have hintersectionZero : sourceLaw (currentTakeEvent ∩ sourceRegion) = 0 := by
      simpa [currentTakeEvent, sourceRegion, inter_comm] using hcurrentZero
    rw [hintersectionZero]
    simp
  have hcurrentFalseLocal : ∀ᵐ omega ∂localLaw,
      currentTake (skill omega) (base omega) = false := by
    have hnotTake : ∀ᵐ omega ∂localLaw, omega ∉ currentTakeEvent := by
      rw [ae_iff]
      simpa [currentTakeEvent] using hcurrentTakeLocalZero
    filter_upwards [hnotTake] with omega hnot
    cases hdecision : currentTake (skill omega) (base omega) <;>
      simp [currentTakeEvent, hdecision] at hnot ⊢
  apply lg21_reportRequired_source_not_stable_of_positiveMassLocalRecalibratedEntry
    sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      currentTake region candidate
  refine ⟨hregion, hregionPositive, ?_, ?_, ?_⟩
  · simpa [sourceRegion, currentTakeEvent] using hcurrentZero
  · simpa [localLaw, sourceRegion] using hcurrentFalseLocal
  · simpa [localLaw, sourceRegion, candidate] using hbranch

theorem lg21_reportRequired_sourceBaseSkill_factorization_of_sourceFactor
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega)
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance) :
    sourceLaw.map (fun omega => (base omega, skill omega)) =
      baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean priorVariance.toNNReal := by
  let observation : Omega → Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  let baseSkill : Omega → Base × ℝ := fun omega => (base omega, skill omega)
  let projection : Base × (ℝ × ℝ) → Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.2)
  let jointKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  have hobservation : Measurable observation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hprojection : Measurable projection := by
    dsimp [projection]
    fun_prop
  letI : IsMarkovKernel jointKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hskillMarginal : jointKernel.map Prod.snd =
      gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean priorVariance noiseVariance publicBase,
      gaussianLocationKernel_apply]
  calc
    sourceLaw.map baseSkill = (sourceLaw.map observation).map projection := by
      rw [Measure.map_map hprojection hobservation]
      rfl
    _ = (baseLaw ⊗ₘ jointKernel).map projection := by
      rw [show sourceLaw.map observation = baseLaw ⊗ₘ jointKernel by
        simpa [observation, jointKernel] using hsourceFactor]
    _ = baseLaw ⊗ₘ jointKernel.map Prod.snd := by
      change Measure.map (Prod.map id Prod.snd) (baseLaw ⊗ₘ jointKernel) = _
      rw [← Measure.compProd_map measurable_snd]
    _ = baseLaw ⊗ₘ gaussianLocationKernel
        baseMean hbaseMean priorVariance.toNNReal := by
      rw [hskillMarginal]

theorem lg21_reportRequired_allTake_of_ae_selectedGaussianPBO_and_sourceFactor
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (hbest : ∀ publicBase,
      NoProfitableBinaryChoiceDeviation
        (fun skill ↦ E.takeDecision skill publicBase = true)
        (fun skill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E skill publicBase)
        (fun _skill ↦ E.noReportPayoff publicBase))
    (haction : Measurable (fun profileSkill : Base × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1))
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill noiseVariance.toNNReal)
    (hreportedPBO : ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.reportedPayoff publicBase =ᵐ[
        normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance)
          (Set.univ ×ˢ {latentSkill |
            E.takeDecision latentSkill publicBase = true})]
        fun observedScore => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance observedScore)
          {latentSkill | E.takeDecision latentSkill publicBase = true})
    (hnoTakePBO : ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianReal (baseMean publicBase) priorVariance.toNNReal)
          {latentSkill | E.takeDecision latentSkill publicBase = false})
    (hstable : LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      (fun latentSkill publicBase => E.takeDecision latentSkill publicBase)) :
    sourceLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let currentTake : ℝ -> Base -> Bool := fun latentSkill publicBase =>
    E.takeDecision latentSkill publicBase
  let take : Base -> ℝ -> Bool := fun publicBase latentSkill =>
    currentTake latentSkill publicBase
  let takeEvent := lg21ReportRequiredFullPublicTakeSet take
  let noTakeEvent := lg21ReportRequiredFullPublicNoTakeSet take
  let noTakeMass := selectionMass skillKernel noTakeEvent
  let takeMass := selectionMass skillKernel takeEvent
  let region : Set Base := Function.support noTakeMass ∩
    {publicBase | takeMass publicBase = 0}
  let baseSkill : Omega -> Base × ℝ := fun omega => (base omega, skill omega)
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2) := by
    simpa [take, currentTake] using haction
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using lg21ReportRequiredFullPublicTakeSet_measurable take htake
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using lg21ReportRequiredFullPublicNoTakeSet_measurable take htake
  have hbaseSkill : Measurable baseSkill := hbase.prodMk hskill
  have hbaseSkillFactor : sourceLaw.map baseSkill = baseLaw ⊗ₘ skillKernel := by
    simpa [baseSkill, skillKernel] using
      (lg21_reportRequired_sourceBaseSkill_factorization_of_sourceFactor
        sourceLaw base score skill hbase hscore hskill baseLaw baseMean hbaseMean
        priorVariance noiseVariance hsourceFactor)
  have hbaseMarginal : sourceLaw.map base = baseLaw := by
    calc
      sourceLaw.map base = (sourceLaw.map baseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hbaseSkill]
        rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by
        rw [hbaseSkillFactor]
      _ = baseLaw := Measure.fst_compProd _ _
  have hcoexistingFibresNull : baseLaw
      (Function.support noTakeMass ∩ Function.support takeMass) = 0 := by
    simpa [skillKernel, take, noTakeEvent, takeEvent] using
      (lg21_reportRequired_coexistingFibres_null_of_ae_selectedGaussianPBO
        baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
        hbest haction htestLaw hreportedPBO hnoTakePBO)
  have hregionMeasurable : MeasurableSet region := by
    simpa [region, noTakeMass, takeMass, skillKernel, noTakeEvent, takeEvent] using
      (lg21_reportRequired_zeroReporterBaseRegion_measurable
        skillKernel take htake)
  by_contra hnoTakeNonzero
  have hsourceNoTakePositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false} :=
    pos_iff_ne_zero.mpr hnoTakeNonzero
  have hproductNoTakePositive : 0 < (baseLaw ⊗ₘ skillKernel) noTakeEvent := by
    rw [← hbaseSkillFactor, Measure.map_apply hbaseSkill hnoTakeEvent]
    simpa [baseSkill, noTakeEvent, take, currentTake] using hsourceNoTakePositive
  have hregionPositive : 0 < baseLaw region := by
    simpa [region, noTakeMass, takeMass, skillKernel, noTakeEvent, takeEvent] using
      (lg21_reportRequired_positive_noTake_mass_forces_reporterZeroFibres
        baseLaw skillKernel take htake hcoexistingFibresNull hproductNoTakePositive)
  have hsourceRegionPositive : 0 < sourceLaw (base ⁻¹' region) := by
    rw [← Measure.map_apply hbase hregionMeasurable, hbaseMarginal]
    exact hregionPositive
  have hsourceTakeZero : sourceLaw (base ⁻¹' region ∩
      {omega | currentTake (skill omega) (base omega) = true}) = 0 := by
    apply lg21_reportRequired_source_currentTake_mass_zero_on_region
      sourceLaw base skill hbase hskill baseLaw skillKernel hbaseSkillFactor
      currentTake
    · simpa [currentTake, Function.comp_def] using haction
    · exact hregionMeasurable
    · intro publicBase hpublicBase
      exact hpublicBase.2
  have hcurrentTake : Measurable (fun omega =>
      currentTake (skill omega) (base omega)) := by
    simpa [currentTake] using haction.comp (hbase.prodMk hskill)
  exact (lg21_reportRequired_localGaussian_not_stable_of_positive_zeroTaker_region
    sourceLaw base score skill hbase hscore hskill baseLaw baseMean hbaseMean
    priorVariance noiseVariance hpriorVariance hnoiseVariance hsourceFactor
    currentTake hcurrentTake region hregionMeasurable hsourceRegionPositive
    hsourceTakeZero) hstable

def LG21ReportRequiredSelectedGaussianPBO
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base)
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Prop :=
  (∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
    (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
    (lg21ReportRequiredFullPublicTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
    E.reportedPayoff publicBase =ᵐ[
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill |
          E.takeDecision latentSkill publicBase = true})]
      fun observedScore => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        {latentSkill | E.takeDecision latentSkill publicBase = true}) ∧
  (∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
    (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
    (lg21ReportRequiredFullPublicNoTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
    E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction
        (gaussianReal (baseMean publicBase) priorVariance.toNNReal)
        {latentSkill | E.takeDecision latentSkill publicBase = false})

theorem lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_sourceSelectedGaussianPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ)
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (haction : Measurable (fun profileSkill :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1))
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (hsourcePBO : ∀ (baseLaw : Measure
        (LG21NonTestFeature Feature testFeature → ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
        IsProbabilityMeasure baseLaw →
        0 < baseVariance →
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21ContinuousPopulationBase testFeature student,
              (lg21ContinuousPopulationFeature testFeature student,
                lg21ContinuousPopulationSkill student))) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ) →
        LG21ReportRequiredSelectedGaussianPBO
          baseLaw baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ) E)
    : letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill
      (lg21ContinuousPopulationFullPublicObservation_measurable testFeature)
      (fun latentSkill publicBase => E.takeDecision latentSkill publicBase) →
    (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false} = 0 := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro hstable
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hselectedPBO := hsourcePBO baseLaw baseMean baseVariance hbaseMean
    hbaseLaw hbaseVariance hsourceFactor
  exact lg21_reportRequired_allTake_of_ae_selectedGaussianPBO_and_sourceFactor
    (lg21ContinuousGaussianAccessPopulationLaw M)
    (lg21ContinuousPopulationBase testFeature)
    (lg21ContinuousPopulationFeature testFeature)
    lg21ContinuousPopulationSkill hbase hscore hskill baseLaw baseMean hbaseMean
    baseVariance (M.noiseVariance testFeature : ℝ)
    hbaseVariance htestNoiseVariance hsourceFactor E
    (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq) haction htestLaw
    hselectedPBO.1 hselectedPBO.2 hstable

end

end LG21TestOptionalPolicies
