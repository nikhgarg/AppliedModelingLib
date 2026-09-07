import LG21TestOptionalPolicies.OptionalAllNoReporterRecalibratedEntry

/-!
# Source-local recalibrated entry for optional reporting

This is the source-semantic connector for a zero-reporter region.  It records
a literal candidate action change on a measurable public-base region, its
candidate-selected PBOs, and the response check for the members whose action
changes to reporting.  It is intentionally a relation, not a theorem that
declares such an entry profitable or stable.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability

/-- Turn on testing only on a designated public-base region. -/
noncomputable def lg21OptionalLocalRegionTake
    {Base : Type*} [MeasurableSpace Base]
    (region : Set Base) (currentTake : ℝ -> Base -> Bool) : ℝ -> Base -> Bool := by
  classical
  exact fun _skill publicBase =>
    if publicBase ∈ region then true else currentTake _skill publicBase

/-- Replace the post-score action only on a designated public-base region. -/
noncomputable def lg21OptionalLocalRegionReport
    {Base : Type*} [MeasurableSpace Base]
    (region : Set Base) (currentReport insideReport : Base -> ℝ -> Bool) :
    Base -> ℝ -> Bool := by
  classical
  exact fun publicBase score =>
    if publicBase ∈ region then insideReport publicBase score else currentReport publicBase score

theorem lg21OptionalLocalRegionTake_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (region : Set Base) (hregion : MeasurableSet region)
    (currentTake : ℝ -> Base -> Bool)
    (hcurrentTake : Measurable (fun omega => currentTake (skill omega) (base omega)))
    (hbase : Measurable base) :
    Measurable (fun omega =>
      lg21OptionalLocalRegionTake region currentTake (skill omega) (base omega)) := by
  classical
  unfold lg21OptionalLocalRegionTake
  apply Measurable.ite (hregion.preimage hbase)
  · exact measurable_const
  · exact hcurrentTake

theorem lg21OptionalLocalRegionReport_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score : Omega -> ℝ)
    (region : Set Base) (hregion : MeasurableSet region)
    (currentReport insideReport : Base -> ℝ -> Bool)
    (hcurrentReport : Measurable (fun omega => currentReport (base omega) (score omega)))
    (hinsideReport : Measurable (fun omega => insideReport (base omega) (score omega)))
    (hbase : Measurable base) :
    Measurable (fun omega =>
      lg21OptionalLocalRegionReport region currentReport insideReport
        (base omega) (score omega)) := by
  classical
  unfold lg21OptionalLocalRegionReport
  apply Measurable.ite (hregion.preimage hbase)
  · exact hinsideReport
  · exact hcurrentReport

/-- A public-base restriction of a Gaussian source retains its Gaussian
score/skill kernel and only reweights the base law. -/
theorem lg21_optional_normalizedBaseRegion_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (region : Set Base) (hregion : MeasurableSet region)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    (lg21NormalizedRestriction sourceLaw (base ⁻¹' region)).map
        (fun omega => (base omega, (score omega, skill omega))) =
      lg21NormalizedRestriction baseLaw region ⊗ₘ
        gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance := by
  let publicObservation : Omega -> Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  have hpublicObservation : Measurable publicObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hpublicRegion : MeasurableSet (region ×ˢ (Set.univ : Set (ℝ × ℝ))) :=
    hregion.prod MeasurableSet.univ
  have hpreimage : publicObservation ⁻¹' (region ×ˢ Set.univ) = base ⁻¹' region := by
    ext omega
    simp [publicObservation]
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  calc
    (lg21NormalizedRestriction sourceLaw (base ⁻¹' region)).map publicObservation =
        lg21NormalizedRestriction (sourceLaw.map publicObservation)
          (region ×ˢ Set.univ) := by
          rw [← hpreimage]
          exact lg21_normalizedRestriction_map_preimage sourceLaw publicObservation
            hpublicObservation (region ×ˢ Set.univ) hpublicRegion
    _ = lg21NormalizedRestriction
          (baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
          (region ×ˢ Set.univ) := by
          rw [show sourceLaw.map publicObservation =
            baseLaw ⊗ₘ gaussianSignalJointKernel
              baseMean hbaseMean baseVariance noiseVariance by
              simpa [publicObservation] using hsourceFactor]
    _ = lg21NormalizedRestriction baseLaw region ⊗ₘ
          gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance :=
      lg21_normalizedRestriction_compProd_left baseLaw
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        region hregion

/-- The source event on which a sequential action profile actually reports. -/
def lg21OptionalSourceReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) : Set Omega :=
  {omega | take (skill omega) (base omega) = true ∧
    report (base omega) (score omega) = true}

/-- The complementary source event on which the sequential profile does not report. -/
def lg21OptionalSourceNoReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (take : ℝ -> Base -> Bool) (report : Base -> ℝ -> Bool) : Set Omega :=
  {omega | take (skill omega) (base omega) = false ∨
    report (base omega) (score omega) = false}

/-- The candidate's actual source report event, including the pre-score take action. -/
def lg21OptionalSourceCandidateReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Set Omega :=
  lg21OptionalSourceReportEvent base score skill candidateTake candidate.reportDecision

/-- The candidate's actual source no-report event, including non-takers. -/
def lg21OptionalSourceCandidateNoReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Set Omega :=
  lg21OptionalSourceNoReportEvent base score skill candidateTake candidate.reportDecision

/-- Source agents whose pre-score action changes from no-test to test. -/
def lg21OptionalSourceChangedTesterEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (skill : Omega -> ℝ)
    (currentTake candidateTake : ℝ -> Base -> Bool) : Set Omega :=
  {omega | currentTake (skill omega) (base omega) = false ∧
    candidateTake (skill omega) (base omega) = true}

/-- Source agents whose realized action changes from no-report to report. -/
def lg21OptionalSourceChangedToReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Set Omega :=
  {omega | candidateTake (skill omega) (base omega) = true ∧
    candidate.reportDecision (base omega) (score omega) = true ∧
    (currentTake (skill omega) (base omega) = false ∨
      currentReport (base omega) (score omega) = false)}

/-- Candidate report PBO on its literal sequential report population. -/
def LG21OptionalSequentialCandidateReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedValue publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Candidate no-report PBO on its literal sequential no-report population. -/
def LG21OptionalSequentialCandidateNoReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ scoreSkill, scoreSkill.2 ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-- Candidate report PBO on a public-base-localized source population. -/
def LG21OptionalSequentialCandidateReportPBOOn
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (population : Set Omega) (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw (population ∩
      lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw (population ∩
      lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw (population ∩
        lg21OptionalSourceCandidateReportEvent base score skill candidateTake candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedValue publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Candidate no-report PBO on a public-base-localized source population. -/
def LG21OptionalSequentialCandidateNoReportPBOOn
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (population : Set Omega) (candidateTake : ℝ -> Base -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw (population ∩
      lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw (population ∩
      lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw (population ∩
        lg21OptionalSourceCandidateNoReportEvent base score skill candidateTake candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ scoreSkill, scoreSkill.2 ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-- Candidate report PBO with an explicitly supplied sequential report action. -/
def LG21OptionalSequentialCandidateReportPBOForAction
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedValue publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Candidate no-report PBO with an explicitly supplied sequential report action. -/
def LG21OptionalSequentialCandidateNoReportPBOForAction
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ scoreSkill, scoreSkill.2 ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-- Source agents whose realized action changes to report under an explicit candidate action. -/
def lg21OptionalSourceChangedToReportForActionEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool) : Set Omega :=
  {omega | candidateTake (skill omega) (base omega) = true ∧
    candidateReport (base omega) (score omega) = true ∧
    (currentTake (skill omega) (base omega) = false ∨
      currentReport (base omega) (score omega) = false)}

/-- The existing full-base Gaussian candidate is also a literal sequential
candidate when every member of the candidate population takes the test. -/
theorem lg21_optional_fullBaseGaussian_sequentialSourceCertificate_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
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
    let candidateTake : ℝ -> Base -> Bool := fun _ _ => true
    ∃ hreportPositive :
        0 < sourceLaw
          (lg21OptionalSourceReportEvent base score skill candidateTake
            candidate.reportDecision),
      ∃ hnoReportPositive :
          0 < sourceLaw
            (lg21OptionalSourceNoReportEvent base score skill candidateTake
              candidate.reportDecision),
        LG21OptionalSequentialCandidateReportPBO sourceLaw base score skill
          (hbase.prodMk (hscore.prodMk hskill)) candidateTake candidate hreportPositive ∧
          LG21OptionalSequentialCandidateNoReportPBO sourceLaw base score skill
            (hbase.prodMk (hscore.prodMk hskill)) candidateTake candidate hnoReportPositive ∧
          PositiveMassBranchMembersBestRespond sourceLaw
            (lg21OptionalSourceReportEvent base score skill candidateTake
              candidate.reportDecision)
            candidate
            (fun P omega =>
              P.noReportValue (base omega) ≤
                P.reportedValue (base omega) (score omega)) ∧
          LG21OptionalGlobalPositiveMassEntry sourceLaw base skill candidate := by
  intro candidate candidateTake
  have hcertificate :=
    lg21_optional_fullBaseGaussian_recalibratedSourceBranchEntry_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
      anchor hsourceFactor
  rcases hcertificate with
    ⟨hreportPositive, hnoReportPositive, hreportPBO, hnoReportPBO,
      hreportMembers, hentry⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hentry⟩
  · simpa [lg21OptionalSourceReportEvent, candidateTake,
      lg21OptionalCandidateSourceReportEvent] using hreportPositive
  · simpa [lg21OptionalSourceNoReportEvent, candidateTake,
      lg21OptionalCandidateSourceNoReportEvent] using hnoReportPositive
  · simpa [LG21OptionalSequentialCandidateReportPBO,
      LG21OptionalCandidateReportPBO,
      lg21OptionalSourceReportEvent, candidateTake,
      lg21OptionalSourceCandidateReportEvent,
      lg21OptionalCandidateSourceReportEvent] using hreportPBO
  · simpa [LG21OptionalSequentialCandidateNoReportPBO,
      LG21OptionalCandidateNoReportPBO,
      lg21OptionalSourceNoReportEvent, candidateTake,
      lg21OptionalSourceCandidateNoReportEvent,
      lg21OptionalCandidateSourceNoReportEvent] using hnoReportPBO
  · simpa [PositiveMassBranchMembersBestRespond,
      lg21OptionalSourceReportEvent, candidateTake,
      lg21OptionalCandidateSourceReportEvent] using hreportMembers

theorem lg21_optional_fullBaseGaussianCandidate_pointwise_test_gain
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) (latentSkill : ℝ) (publicBase : Base) :
    let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
      baseMean hbaseMean baseVariance noiseVariance anchor
    candidate.noReportValue publicBase <
      lg21OptionalCandidateTestExpectedValue candidate latentSkill publicBase := by
  intro candidate
  have hnoiseVarianceNN : noiseVariance.toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr hnoiseVariance)
  apply lg21_optional_candidate_gaussian_pointwise_test_gain candidate publicBase
    latentSkill noiseVariance.toNNReal hnoiseVarianceNN
  · intro sourceSkill
    rfl
  · intro score hreport
    change lg21OptionalHighScoreCandidateReports anchor score = true at hreport
    have hge : anchor ≤ score := by
      simpa [lg21OptionalHighScoreCandidateReports] using hreport
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
  · exact lg21_optional_rawGaussianPosteriorMean_strictMono
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance publicBase
  · exact lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  · intro score hscore
    change lg21OptionalHighScoreCandidateReports anchor score = true
    simp [lg21OptionalHighScoreCandidateReports, le_of_lt hscore]

theorem lg21_optional_sequentialReportPBOForAction_of_ae_eq
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hTake : (fun omega => candidateTake (skill omega) (base omega)) =ᵐ[sourceLaw]
      fun _ => true)
    (hReport : (fun omega => candidateReport (base omega) (score omega)) =ᵐ[sourceLaw]
      fun omega => candidate.reportDecision (base omega) (score omega))
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport))
    (hcanonicalPositive : 0 < sourceLaw
      (lg21OptionalSourceReportEvent base score skill (fun _ _ => true)
        candidate.reportDecision))
    (hcanonical : LG21OptionalSequentialCandidateReportPBO sourceLaw base score skill hpublic
      (fun _ _ => true) candidate hcanonicalPositive) :
    LG21OptionalSequentialCandidateReportPBOForAction sourceLaw base score skill hpublic
      candidateTake candidateReport candidate hpositive := by
  have hevent :
      lg21OptionalSourceReportEvent base score skill candidateTake candidateReport =ᵐ[sourceLaw]
        lg21OptionalSourceReportEvent base score skill (fun _ _ => true)
          candidate.reportDecision := by
    filter_upwards [hTake, hReport] with omega htake hreport
    apply propext
    dsimp [lg21OptionalSourceReportEvent]
    change (candidateTake (skill omega) (base omega) = true ∧
      candidateReport (base omega) (score omega) = true) ↔
      (true = true ∧ candidate.reportDecision (base omega) (score omega) = true)
    rw [htake, hreport]
  have hnormalized :
      lg21NormalizedRestriction sourceLaw
          (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport) =
        lg21NormalizedRestriction sourceLaw
          (lg21OptionalSourceReportEvent base score skill (fun _ _ => true)
            candidate.reportDecision) :=
    by
      unfold lg21NormalizedRestriction
      rw [measure_congr hevent, Measure.restrict_congr_set hevent]
  simpa [LG21OptionalSequentialCandidateReportPBOForAction,
    LG21OptionalSequentialCandidateReportPBO, hnormalized] using hcanonical

theorem lg21_optional_sequentialNoReportPBOForAction_of_ae_eq
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hTake : (fun omega => candidateTake (skill omega) (base omega)) =ᵐ[sourceLaw]
      fun _ => true)
    (hReport : (fun omega => candidateReport (base omega) (score omega)) =ᵐ[sourceLaw]
      fun omega => candidate.reportDecision (base omega) (score omega))
    (hpositive : 0 < sourceLaw
      (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport))
    (hcanonicalPositive : 0 < sourceLaw
      (lg21OptionalSourceNoReportEvent base score skill (fun _ _ => true)
        candidate.reportDecision))
    (hcanonical : LG21OptionalSequentialCandidateNoReportPBO sourceLaw base score skill hpublic
      (fun _ _ => true) candidate hcanonicalPositive) :
    LG21OptionalSequentialCandidateNoReportPBOForAction sourceLaw base score skill hpublic
      candidateTake candidateReport candidate hpositive := by
  have hevent :
      lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport =ᵐ[sourceLaw]
        lg21OptionalSourceNoReportEvent base score skill (fun _ _ => true)
          candidate.reportDecision := by
    filter_upwards [hTake, hReport] with omega htake hreport
    apply propext
    dsimp [lg21OptionalSourceNoReportEvent]
    change (candidateTake (skill omega) (base omega) = false ∨
      candidateReport (base omega) (score omega) = false) ↔
      (true = false ∨ candidate.reportDecision (base omega) (score omega) = false)
    rw [htake, hreport]
  have hnormalized :
      lg21NormalizedRestriction sourceLaw
          (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport) =
        lg21NormalizedRestriction sourceLaw
          (lg21OptionalSourceNoReportEvent base score skill (fun _ _ => true)
            candidate.reportDecision) :=
    by
      unfold lg21NormalizedRestriction
      rw [measure_congr hevent, Measure.restrict_congr_set hevent]
  simpa [LG21OptionalSequentialCandidateNoReportPBOForAction,
    LG21OptionalSequentialCandidateNoReportPBO, hnormalized] using hcanonical

/--
A literal positive-mass sequential entry localized to a measurable public-base
region with zero current report mass.  Candidate PBOs are calibrated under
the source law normalized on that public region; this is valid at its bases
because membership in the region is public-base measurable.  Both decision
stages are present explicitly.
-/
def LG21OptionalSourcePositiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (region : Set Base)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Prop :=
  MeasurableSet region ∧
    ∃ hregionPositive : 0 < sourceLaw (base ⁻¹' region),
      sourceLaw (base ⁻¹' region ∩
        lg21OptionalSourceReportEvent base score skill currentTake currentReport) = 0 ∧
      Measurable (fun omega => candidateTake (skill omega) (base omega)) ∧
      Measurable (fun omega => candidateReport (base omega) (score omega)) ∧
      (∀ᵐ omega ∂sourceLaw,
        base omega ∉ region ->
        candidateTake (skill omega) (base omega) =
          currentTake (skill omega) (base omega) ∧
        candidateReport (base omega) (score omega) =
          currentReport (base omega) (score omega)) ∧
      0 < sourceLaw
        (lg21OptionalSourceChangedTesterEvent base skill currentTake candidateTake ∪
          lg21OptionalSourceChangedToReportForActionEvent base score skill
            currentTake currentReport candidateTake candidateReport) ∧
      (∀ omega, omega ∈
          lg21OptionalSourceChangedTesterEvent base skill currentTake candidateTake ->
        candidate.noReportValue (base omega) <
          lg21OptionalCandidateTestExpectedValue candidate (skill omega) (base omega)) ∧
      let localLaw : Measure Omega :=
        lg21NormalizedRestriction sourceLaw (base ⁻¹' region)
      letI : IsProbabilityMeasure localLaw :=
        lg21NormalizedRestriction_isProbability sourceLaw _
          (ne_of_gt hregionPositive) (measure_ne_top _ _)
      (fun omega => candidateReport (base omega) (score omega)) =ᵐ[localLaw]
        (fun omega => candidate.reportDecision (base omega) (score omega)) ∧
      ∃ hreportPositive :
          0 < localLaw
            (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport),
        ∃ hnoReportPositive :
            0 < localLaw
              (lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport),
          LG21OptionalSequentialCandidateReportPBOForAction localLaw base score skill hpublic
            candidateTake candidateReport candidate hreportPositive ∧
            LG21OptionalSequentialCandidateNoReportPBOForAction localLaw base score skill hpublic
              candidateTake candidateReport candidate hnoReportPositive ∧
            PositiveMassBranchMembersBestRespond localLaw
              (lg21OptionalSourceReportEvent base score skill
                candidateTake candidateReport)
              candidate
              (fun P omega =>
                P.noReportValue (base omega) ≤
                  P.reportedValue (base omega) (score omega))

/-- Source stability against the local sequential recalibrated entries above. -/
def LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool) : Prop :=
  ∀ region candidateTake candidateReport candidate,
    ¬ LG21OptionalSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake currentReport region
        candidateTake candidateReport candidate

/-- Source stability for deviations that preserve a fixed exogenous test law.
The additional equality is the paper-model restriction: a strategic candidate
may change actions and hence its selected branch PBOs, but not the Gaussian
score technology. -/
def LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (fixedTestLaw : ℝ -> Base -> Measure ℝ)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool) : Prop :=
  ∀ region candidateTake candidateReport candidate,
    (∀ latentSkill publicBase,
      candidate.testLaw latentSkill publicBase =
        fixedTestLaw latentSkill publicBase) ->
    ¬ LG21OptionalSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake currentReport region
        candidateTake candidateReport candidate

/-- A concrete local source entry refutes the corresponding stability predicate. -/
theorem lg21_optional_source_not_stable_of_positiveMassLocalRecalibratedEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (region : Set Base)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hentry : LG21OptionalSourcePositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake currentReport region
        candidateTake candidateReport candidate) :
    ¬ LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill hpublic currentTake currentReport := by
  intro hstable
  exact hstable region candidateTake candidateReport candidate hentry

theorem lg21_optional_localGaussian_not_stable_of_positive_zeroReporter_region
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (hcurrentTake : Measurable (fun omega => currentTake (skill omega) (base omega)))
    (hcurrentReport : Measurable (fun omega => currentReport (base omega) (score omega)))
    (region : Set Base) (hregion : MeasurableSet region)
    (hregionPositive : 0 < sourceLaw (base ⁻¹' region))
    (hcurrentZero : sourceLaw (base ⁻¹' region ∩
      lg21OptionalSourceReportEvent base score skill currentTake currentReport) = 0)
    (anchor : ℝ) :
    ¬ LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
        currentTake currentReport := by
  classical
  let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance anchor
  let candidateTake : ℝ -> Base -> Bool :=
    lg21OptionalLocalRegionTake region currentTake
  let candidateReport : Base -> ℝ -> Bool :=
    lg21OptionalLocalRegionReport region currentReport candidate.reportDecision
  let sourceRegion : Set Omega := base ⁻¹' region
  let canonicalReportEvent : Set Omega :=
    lg21OptionalSourceReportEvent base score skill (fun _ _ => true)
      candidate.reportDecision
  let canonicalNoReportEvent : Set Omega :=
    lg21OptionalSourceNoReportEvent base score skill (fun _ _ => true)
      candidate.reportDecision
  let actualReportEvent : Set Omega :=
    lg21OptionalSourceReportEvent base score skill candidateTake candidateReport
  let actualNoReportEvent : Set Omega :=
    lg21OptionalSourceNoReportEvent base score skill candidateTake candidateReport
  let changedEvent : Set Omega :=
    lg21OptionalSourceChangedTesterEvent base skill currentTake candidateTake ∪
      lg21OptionalSourceChangedToReportForActionEvent base score skill
        currentTake currentReport candidateTake candidateReport
  have hsourceRegionMeasurable : MeasurableSet sourceRegion := by
    simpa [sourceRegion] using hregion.preimage hbase
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  let publicObservation : Omega -> Base × (ℝ × ℝ) :=
    fun omega => (base omega, (score omega, skill omega))
  have hpublicObservation : Measurable publicObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  have hbaseMarginal : sourceLaw.map base = baseLaw := by
    calc
      sourceLaw.map base = (sourceLaw.map publicObservation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hpublicObservation]
        rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance).map Prod.fst := by
        rw [show sourceLaw.map publicObservation =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance by
            simpa [publicObservation] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance).fst = baseLaw
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
        gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance := by
    simpa [localLaw, localBaseLaw, sourceRegion, publicObservation] using
      (lg21_optional_normalizedBaseRegion_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance region hregion hsourceFactor)
  have hcertificate :=
    lg21_optional_fullBaseGaussian_sequentialSourceCertificate_of_factorization
      localLaw base score skill hbase hscore hskill localBaseLaw
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor hlocalFactor
  dsimp only at hcertificate
  rcases hcertificate with
    ⟨hcanonicalReportPositive, hcanonicalNoReportPositive,
      hcanonicalReportPBO, hcanonicalNoReportPBO,
      hcanonicalReportMembers, _hglobalEntry⟩
  have hlocalRegion : ∀ᵐ omega ∂localLaw, base omega ∈ region := by
    simpa [localLaw, sourceRegion] using
      (lg21NormalizedRestriction_ae_mem sourceLaw sourceRegion
        hsourceRegionMeasurable (measure_ne_top _ _))
  have htakeLocal :
      (fun omega => candidateTake (skill omega) (base omega)) =ᵐ[localLaw]
        fun _ => true := by
    filter_upwards [hlocalRegion] with omega hmem
    simp [candidateTake, lg21OptionalLocalRegionTake, hmem]
  have hreportLocal :
      (fun omega => candidateReport (base omega) (score omega)) =ᵐ[localLaw]
        fun omega => candidate.reportDecision (base omega) (score omega) := by
    filter_upwards [hlocalRegion] with omega hmem
    simp [candidateReport, lg21OptionalLocalRegionReport, hmem]
  have hinsideReport : Measurable (fun omega =>
      candidate.reportDecision (base omega) (score omega)) := by
    simpa [candidate] using
      ((lg21OptionalFullBaseRawGaussianHighScoreCandidate_reportDecision_measurable
        baseMean hbaseMean baseVariance noiseVariance anchor).comp
          (hbase.prodMk hscore))
  have hcandidateTakeMeasurable : Measurable (fun omega =>
      candidateTake (skill omega) (base omega)) := by
    simpa [candidateTake] using
      (lg21OptionalLocalRegionTake_measurable base skill region hregion
        currentTake hcurrentTake hbase)
  have hcandidateReportMeasurable : Measurable (fun omega =>
      candidateReport (base omega) (score omega)) := by
    simpa [candidateReport] using
      (lg21OptionalLocalRegionReport_measurable base score region hregion
        currentReport candidate.reportDecision hcurrentReport hinsideReport hbase)
  have hagreeOutside : ∀ᵐ omega ∂sourceLaw,
      base omega ∉ region ->
        candidateTake (skill omega) (base omega) =
          currentTake (skill omega) (base omega) ∧
        candidateReport (base omega) (score omega) =
          currentReport (base omega) (score omega) := by
    exact Filter.Eventually.of_forall fun omega houtside => by
      constructor <;>
        simp [candidateTake, candidateReport,
          lg21OptionalLocalRegionTake, lg21OptionalLocalRegionReport, houtside]
  have hactualReportEventAE : actualReportEvent =ᵐ[localLaw] canonicalReportEvent := by
    filter_upwards [htakeLocal, hreportLocal] with omega htake hreport
    apply propext
    dsimp [actualReportEvent, canonicalReportEvent,
      lg21OptionalSourceReportEvent]
    change (candidateTake (skill omega) (base omega) = true ∧
      candidateReport (base omega) (score omega) = true) ↔
      (true = true ∧ candidate.reportDecision (base omega) (score omega) = true)
    rw [htake, hreport]
  have hactualNoReportEventAE : actualNoReportEvent =ᵐ[localLaw]
      canonicalNoReportEvent := by
    filter_upwards [htakeLocal, hreportLocal] with omega htake hreport
    apply propext
    dsimp [actualNoReportEvent, canonicalNoReportEvent,
      lg21OptionalSourceNoReportEvent]
    change (candidateTake (skill omega) (base omega) = false ∨
      candidateReport (base omega) (score omega) = false) ↔
      (true = false ∨ candidate.reportDecision (base omega) (score omega) = false)
    rw [htake, hreport]
  have hactualReportPositive : 0 < localLaw actualReportEvent := by
    rw [measure_congr hactualReportEventAE]
    exact hcanonicalReportPositive
  have hactualNoReportPositive : 0 < localLaw actualNoReportEvent := by
    rw [measure_congr hactualNoReportEventAE]
    exact hcanonicalNoReportPositive
  have hchangedPositive : 0 < sourceLaw changedEvent := by
    by_contra hnot
    have hchangedZero : sourceLaw changedEvent = 0 := by
      exact le_antisymm (not_lt.mp hnot) (zero_le _)
    have hunionZero : sourceLaw
        (changedEvent ∪ (sourceRegion ∩
          lg21OptionalSourceReportEvent base score skill currentTake currentReport)) = 0 :=
      measure_union_null hchangedZero (by simpa [sourceRegion] using hcurrentZero)
    have hsubset : sourceRegion ∩ canonicalReportEvent ⊆
        changedEvent ∪ (sourceRegion ∩
          lg21OptionalSourceReportEvent base score skill currentTake currentReport) := by
      intro omega homega
      rcases homega with ⟨hregionMem, hcanonical⟩
      by_cases htake : currentTake (skill omega) (base omega) = false
      · left
        left
        refine ⟨htake, ?_⟩
        simp [candidateTake, lg21OptionalLocalRegionTake,
          show base omega ∈ region by simpa [sourceRegion] using hregionMem]
      · by_cases hreport : currentReport (base omega) (score omega) = false
        · left
          right
          refine ⟨?_, ?_, Or.inr hreport⟩
          · simp [candidateTake, lg21OptionalLocalRegionTake,
              show base omega ∈ region by simpa [sourceRegion] using hregionMem]
          · have : candidate.reportDecision (base omega) (score omega) = true := by
              simpa [canonicalReportEvent, lg21OptionalSourceReportEvent] using hcanonical
            simpa [candidateReport, lg21OptionalLocalRegionReport,
              show base omega ∈ region by simpa [sourceRegion] using hregionMem] using this
        · right
          refine ⟨hregionMem, ?_⟩
          have htakeTrue : currentTake (skill omega) (base omega) = true := by
            cases hcurrent : currentTake (skill omega) (base omega) <;> simp_all
          have hreportTrue : currentReport (base omega) (score omega) = true := by
            cases hcurrent : currentReport (base omega) (score omega) <;> simp_all
          exact ⟨htakeTrue, hreportTrue⟩
    have hcanonicalRawZero : sourceLaw (sourceRegion ∩ canonicalReportEvent) = 0 :=
      measure_mono_null hsubset hunionZero
    have hcanonicalEventMeasurable : MeasurableSet canonicalReportEvent := by
      change MeasurableSet {omega |
        (true : Bool) = true ∧
          candidate.reportDecision (base omega) (score omega) = true}
      convert (measurableSet_singleton true).preimage hinsideReport using 1
      ext omega
      simp
    have hcanonicalLocalZero : localLaw canonicalReportEvent = 0 := by
      rw [show localLaw = lg21NormalizedRestriction sourceLaw sourceRegion by rfl,
        lg21NormalizedRestriction_apply sourceLaw
          (event := sourceRegion) (target := canonicalReportEvent)
          hcanonicalEventMeasurable]
      have hintersectionZero :
          sourceLaw (canonicalReportEvent ∩ sourceRegion) = 0 := by
        simpa [inter_comm] using hcanonicalRawZero
      rw [hintersectionZero]
      simp
    exact (ne_of_gt hcanonicalReportPositive) hcanonicalLocalZero
  have hchangedTesterGain : ∀ omega, omega ∈
      lg21OptionalSourceChangedTesterEvent base skill currentTake candidateTake ->
      candidate.noReportValue (base omega) <
        lg21OptionalCandidateTestExpectedValue candidate (skill omega) (base omega) := by
    intro omega _
    exact lg21_optional_fullBaseGaussianCandidate_pointwise_test_gain
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor (skill omega) (base omega)
  have hactualReportPBO : LG21OptionalSequentialCandidateReportPBOForAction
      localLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      candidateTake candidateReport candidate hactualReportPositive := by
    exact lg21_optional_sequentialReportPBOForAction_of_ae_eq
      localLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      candidateTake candidateReport candidate htakeLocal hreportLocal
      hactualReportPositive hcanonicalReportPositive hcanonicalReportPBO
  have hactualNoReportPBO : LG21OptionalSequentialCandidateNoReportPBOForAction
      localLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      candidateTake candidateReport candidate hactualNoReportPositive := by
    exact lg21_optional_sequentialNoReportPBOForAction_of_ae_eq
      localLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
      candidateTake candidateReport candidate htakeLocal hreportLocal
      hactualNoReportPositive hcanonicalNoReportPositive hcanonicalNoReportPBO
  have hactualReportMembers : PositiveMassBranchMembersBestRespond localLaw
      actualReportEvent candidate
      (fun P omega => P.noReportValue (base omega) ≤
        P.reportedValue (base omega) (score omega)) := by
    rw [PositiveMassBranchMembersBestRespond] at hcanonicalReportMembers ⊢
    exact (ae_restrict_congr_set hactualReportEventAE).mpr
      hcanonicalReportMembers
  apply lg21_optional_source_not_stable_of_positiveMassLocalRecalibratedEntry
    sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
    currentTake currentReport region candidateTake candidateReport candidate
  refine ⟨hregion, hregionPositive, hcurrentZero,
    hcandidateTakeMeasurable, hcandidateReportMeasurable, hagreeOutside,
    ?_, hchangedTesterGain, ?_⟩
  · simpa [changedEvent, candidateTake, candidateReport] using hchangedPositive
  · refine ⟨?_, hactualReportPositive, hactualNoReportPositive,
      hactualReportPBO, hactualNoReportPBO, hactualReportMembers⟩
    exact hreportLocal

end

end LG21TestOptionalPolicies
