import LG21TestOptionalPolicies.HiddenAccessTheorem31ScoreLocalPatchMeanBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeReporterPBOBridge

/-!
# Semantic support for the LG21 score-local patch

The candidate patch is defined from the public `(base, score)` observation.
This module records the literal raw-population event on which it changes a
visible action.  The statements deliberately quantify an arbitrary Boolean
promotion rule, rather than relying on a threshold or function name.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The literal access/no-report population selected by a public promotion
rule. -/
def lg21HiddenAccessAccessNoReportPromotionEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (promote : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  lg21HiddenAccessAccessNoReportEvent testFeature reportDecision ∩
    {student | promote (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2) = true}

/-- The semantic event targeted by the posterior-improving score-local
promotion. -/
def lg21HiddenAccessAccessNoReportStrictGainEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (incumbentNoReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
    (scoreValue : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → ℝ) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  lg21HiddenAccessAccessNoReportEvent testFeature reportDecision ∩
    {student | incumbentNoReport (lg21HiddenAccessStudentBase testFeature student.2) <
      scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2)}

/-- The public score-local patch is measurable when both public action rules
are measurable. -/
theorem lg21HiddenAccessScoreLocalReportPatch_measurable
    {Base : Type*} [MeasurableSpace Base]
    (currentReport promote : Base → ℝ → Bool)
    (hcurrentReport : Measurable (fun pair : Base × ℝ =>
      currentReport pair.1 pair.2))
    (hpromote : Measurable (fun pair : Base × ℝ => promote pair.1 pair.2)) :
    Measurable (fun pair : Base × ℝ =>
      lg21HiddenAccessScoreLocalReportPatch currentReport promote pair.1 pair.2) := by
  apply measurable_to_bool
  have hcurrent : MeasurableSet {pair : Base × ℝ |
      currentReport pair.1 pair.2 = true} :=
    (measurableSet_singleton true).preimage hcurrentReport
  have hpromotion : MeasurableSet {pair : Base × ℝ |
      promote pair.1 pair.2 = true} :=
    (measurableSet_singleton true).preimage hpromote
  convert hcurrent.union hpromotion using 1
  ext pair
  simp [lg21HiddenAccessScoreLocalReportPatch]

/-- The promotion event associated with the strict raw-posterior comparison
is exactly the semantic strict-gain event. -/
theorem lg21HiddenAccess_accessNoReportPromotionEvent_eq_strictGainEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (incumbentNoReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
    (scoreValue : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → ℝ) :
    lg21HiddenAccessAccessNoReportPromotionEvent testFeature reportDecision
      (lg21ScoreLocalPromotion incumbentNoReport scoreValue) =
      lg21HiddenAccessAccessNoReportStrictGainEvent testFeature reportDecision
        incumbentNoReport scoreValue := by
  ext student
  simp [lg21HiddenAccessAccessNoReportPromotionEvent,
    lg21HiddenAccessAccessNoReportStrictGainEvent]

/-- The actual score-stage best-response condition transports from the
positive-access decision law to the literal raw population.  This is valid
because the hidden access bit is independent of the source's `(base, score)`
observation; it does not identify an action event with a named function. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportBestResponse_ae_on_rawPopulation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE) :
    ∀ᵐ student ∂lg21ContinuousGaussianPopulationLaw M,
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseScore : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
  let forgetSkill :
      ((LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun baseScoreSkill => (baseScoreSkill.1, baseScoreSkill.2.1)
  have hbaseScore : Measurable baseScore := by
    simpa [baseScore] using
      lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hobservation : Measurable observation := by
    simpa [observation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hforgetSkill : Measurable forgetSkill := by
    exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hrawBaseScoreLaw : rawLaw.map baseScore =
      lg21HiddenAccessAccessBaseScoreLaw M testFeature := by
    calc
      rawLaw.map baseScore = (rawLaw.map observation).map forgetSkill := by
        rw [Measure.map_map hforgetSkill hobservation]
        rfl
      _ = (accessLaw.map observation).map forgetSkill := by
        rw [lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
          M E.access_positive testFeature]
      _ = accessLaw.map baseScore := by
        rw [Measure.map_map hforgetSkill hobservation]
        rfl
      _ = lg21HiddenAccessAccessBaseScoreLaw M testFeature := by rfl
  have hbestBaseScore : ∀ᵐ publicScore ∂rawLaw.map baseScore,
      E.reportDecision publicScore.1 publicScore.2 = true →
        E.noReportPayoff publicScore.1 ≤
          E.reportedPayoff publicScore.1 publicScore.2 := by
    rw [hrawBaseScoreLaw]
    exact (E.optionalReportBestResponse_ae hreportBest).1
  simpa [rawLaw, baseScore] using
    (ae_of_ae_map hbaseScore.aemeasurable hbestBaseScore)

/-- On an attained positive reporter branch, the actual reported payoff is
the raw Gaussian posterior mean.  The conclusion is deliberately restricted
to that literal branch; no value is assigned to an unreached report history. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportedPayoff_eq_rawGaussianPosterior_ae_on_actualReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision),
      E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let reporterLaw := lg21NormalizedRestriction rawLaw reportEvent
  let baseScore : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
  have hbaseScore : Measurable baseScore := by
    simpa [baseScore] using
      lg21HiddenAccessBaseScoreObservation_measurable testFeature
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hPBOBaseScore : (fun publicScore =>
      E.reportedPayoff publicScore.1 publicScore.2) =ᵐ[
        reporterLaw.map baseScore]
      fun publicScore => lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        publicScore.1 publicScore.2 := by
    simpa only [reporterLaw, rawLaw, reportEvent, baseScore,
      lg21OptionalRawGaussianPosteriorMean] using
      (E.reportedPayoff_eq_rawGaussianPosterior_ae_of_allTake
        hactiveNoTakeZero hreporterPositive baseLaw baseMean hbaseMean
        baseVariance hbaseVariance hnoiseVariance hsourceFactor)
  have hPBOReporterLaw : ∀ᵐ student ∂reporterLaw,
      E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
    simpa [baseScore] using
      (ae_of_ae_map hbaseScore.aemeasurable hPBOBaseScore)
  change ∀ᵐ student ∂rawLaw.restrict reportEvent,
    E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2) =
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2)
  change ∀ᵐ student ∂(rawLaw reportEvent)⁻¹ • rawLaw.restrict reportEvent,
    E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2) =
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) at hPBOReporterLaw
  rw [Measure.ae_ennreal_smul_measure_iff
    (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw reportEvent))] at hPBOReporterLaw
  exact hPBOReporterLaw

/-- If a candidate keeps the incumbent pre-score action, an incumbent
reporter inside its report branch is necessarily an actual incumbent reporter.
This is a pointwise action identity and does not inspect candidate values. -/
theorem lg21HiddenAccess_currentReporter_candidateReport_subset_actualReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision candidateReport ∩
      {student | E.reportDecision
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true} ⊆
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision := by
  rintro ⟨access, primitive⟩ ⟨hcandidate, hcurrent⟩
  cases access with
  | false =>
      simp [lg21HiddenAccessRawCandidateReportEvent,
        lg21HiddenAccessOptionalObservedAction] at hcandidate
  | true =>
      cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
      | false =>
          simp [lg21HiddenAccessRawCandidateReportEvent,
            lg21HiddenAccessOptionalObservedAction, htake] at hcandidate
      | true =>
          have htake' : E.takeDecision primitive.1
              (lg21HiddenAccessStudentBase testFeature primitive) = true := by
            simpa [lg21HiddenAccessStudentTake] using htake
          change E.reportDecision
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true at hcurrent
          change lg21HiddenAccessOptionalObservedAction testFeature
            E.takeDecision E.reportDecision (true, primitive) = true
          simp [lg21HiddenAccessOptionalObservedAction,
            lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
            htake', hcurrent]

/-- An on-path payoff identity transports to incumbent reporters inside any
candidate report branch that preserves the incumbent pre-score action. -/
theorem lg21HiddenAccess_currentReportedValue_ae_on_candidateReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (scoreValue : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → ℝ)
    (hactualValue : ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision),
      E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2)) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision candidateReport),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    E.takeDecision candidateReport
  let currentEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | E.reportDecision
      (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2) = true}
  have hcandidateEvent : MeasurableSet candidateEvent := by
    change MeasurableSet
      ((lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        candidateReport) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (lg21HiddenAccessOptionalObservedAction_measurable testFeature
        E.takeDecision candidateReport E.takeDecision_measurable hcandidateReport)
  have hcurrentEvent : MeasurableSet currentEvent := by
    change MeasurableSet
      ((fun student : Bool × (ℝ × (Feature → ℝ)) =>
        E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2)) ⁻¹'
        ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (E.reportDecision_measurable.comp
        (((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd).prodMk
          ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)))
  have hsubset : candidateEvent ∩ currentEvent ⊆
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision := by
    simpa [candidateEvent, currentEvent] using
      (lg21HiddenAccess_currentReporter_candidateReport_subset_actualReport
        E candidateReport)
  have hintersectionValue : ∀ᵐ student ∂rawLaw.restrict
      (candidateEvent ∩ currentEvent),
      E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) :=
    ae_restrict_of_ae_restrict_of_subset hsubset hactualValue
  rw [ae_restrict_iff' (hcandidateEvent.inter hcurrentEvent)] at hintersectionValue
  rw [ae_restrict_iff' hcandidateEvent]
  filter_upwards [hintersectionValue] with student hvalue
  intro hcandidate hcurrent
  exact hvalue ⟨hcandidate, hcurrent⟩

/-- If the actual reporter branch is null, incumbent reporters inside a
candidate branch form a null set as well.  Thus the candidate branch needs no
off-path completion of the incumbent reported payoff. -/
theorem lg21HiddenAccess_currentReportedValue_ae_on_candidateReport_of_actualReport_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (scoreValue : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → ℝ)
    (hactualReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) = 0) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision candidateReport),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    E.takeDecision candidateReport
  have hcandidateEvent : MeasurableSet candidateEvent := by
    change MeasurableSet
      ((lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        candidateReport) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (lg21HiddenAccessOptionalObservedAction_measurable testFeature
        E.takeDecision candidateReport E.takeDecision_measurable hcandidateReport)
  have hnotActual : ∀ᵐ student ∂rawLaw,
      student ∉ lg21HiddenAccessOptionalReportEvent testFeature
        E.takeDecision E.reportDecision := by
    rw [ae_iff]
    simpa [rawLaw] using hactualReportZero
  rw [ae_restrict_iff' hcandidateEvent]
  filter_upwards [hnotActual] with student hnotActual
  intro hcandidate hcurrent
  exact (hnotActual
    (lg21HiddenAccess_currentReporter_candidateReport_subset_actualReport
      E candidateReport ⟨hcandidate, hcurrent⟩)).elim

/-- Source-PBO classification of the score-local candidate report branch.
The positive and null incumbent reporter cases are handled separately, so the
argument never assigns a posterior to a null incumbent report history. -/
theorem lg21HiddenAccess_scoreLocalPatch_reportMember_classifies_of_sourcePBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (incumbentNoReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hcandidateReported : ∀ publicBase score,
      candidate.reportedValue publicBase score =
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          publicBase score)
    (hpatchMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessScoreLocalReportPatch E.reportDecision
        (lg21ScoreLocalPromotion incumbentNoReport
          (lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)))
          pair.1 pair.2)) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport
            (lg21OptionalRawGaussianPosteriorMean
              baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))))),
      (E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true ∧
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) ∨
      incumbentNoReport (lg21HiddenAccessStudentBase testFeature student.2) <
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let patch := lg21HiddenAccessScoreLocalReportPatch E.reportDecision
    (lg21ScoreLocalPromotion incumbentNoReport scoreValue)
  let actualReportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  have hclassifies_of_current (hcurrentReported : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision patch),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) :
      ∀ᵐ student ∂rawLaw.restrict
        (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision patch),
        (E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) = true ∧
          candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) =
            E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
              (lg21HiddenAccessStudentScore testFeature student.2)) ∨
        incumbentNoReport (lg21HiddenAccessStudentBase testFeature student.2) <
          candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
    have hreportEvent : MeasurableSet
        (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision patch) := by
      change MeasurableSet
        ((lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision patch) ⁻¹'
          ({true} : Set Bool))
      exact (measurableSet_singleton true).preimage
        (lg21HiddenAccessOptionalObservedAction_measurable testFeature
          E.takeDecision patch E.takeDecision_measurable
          (by simpa [patch] using hpatchMeasurable))
    rw [ae_restrict_iff' hreportEvent] at hcurrentReported
    rw [ae_restrict_iff' hreportEvent]
    filter_upwards [hcurrentReported] with student hcurrentValue
    intro hmember
    rcases student with ⟨access, primitive⟩
    cases access with
    | false =>
        simp [lg21HiddenAccessRawCandidateReportEvent,
          lg21HiddenAccessOptionalObservedAction] at hmember
    | true =>
        cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
        | false =>
            simp [lg21HiddenAccessRawCandidateReportEvent,
              lg21HiddenAccessOptionalObservedAction, htake] at hmember
        | true =>
            have htake' : E.takeDecision primitive.1
                (lg21HiddenAccessStudentBase testFeature primitive) = true := by
              simpa [lg21HiddenAccessStudentTake] using htake
            by_cases hcurrent : E.reportDecision
                (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive) = true
            · left
              refine ⟨hcurrent, ?_⟩
              rw [hcandidateReported]
              exact (hcurrentValue hmember hcurrent).symm
            · right
              have hpromote : lg21ScoreLocalPromotion incumbentNoReport scoreValue
                  (lg21HiddenAccessStudentBase testFeature primitive)
                  (lg21HiddenAccessStudentScore testFeature primitive) = true := by
                simpa [lg21HiddenAccessRawCandidateReportEvent,
                  lg21HiddenAccessOptionalObservedAction,
                  lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
                  lg21HiddenAccessScoreLocalReportPatch,
                  htake', hcurrent, patch] using hmember
              rw [hcandidateReported]
              exact (lg21ScoreLocalPromotion_eq_true_iff
                incumbentNoReport scoreValue
                (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive)).1 hpromote
  by_cases hreporterPositive : 0 < rawLaw actualReportEvent
  · have hactualValue : ∀ᵐ student ∂rawLaw.restrict actualReportEvent,
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
      simpa [rawLaw, actualReportEvent, scoreValue] using
        (E.reportedPayoff_eq_rawGaussianPosterior_ae_on_actualReport
          hactiveNoTakeZero (by simpa [rawLaw, actualReportEvent] using hreporterPositive)
          baseLaw baseMean hbaseMean baseVariance hbaseVariance hnoiseVariance
          hsourceFactor)
    have hcurrentValue : ∀ᵐ student ∂rawLaw.restrict
        (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision patch),
        E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true →
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) =
            scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
              (lg21HiddenAccessStudentScore testFeature student.2) := by
      simpa [rawLaw, patch, actualReportEvent] using
        (lg21HiddenAccess_currentReportedValue_ae_on_candidateReport
          E patch (by simpa [patch] using hpatchMeasurable) scoreValue
          hactualValue)
    simpa [rawLaw, scoreValue, patch] using hclassifies_of_current hcurrentValue
  · have hactualReportZero : rawLaw actualReportEvent = 0 :=
      bot_unique (le_of_not_gt hreporterPositive)
    have hcurrentValue : ∀ᵐ student ∂rawLaw.restrict
        (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision patch),
        E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true →
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) =
            scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
              (lg21HiddenAccessStudentScore testFeature student.2) := by
      simpa [rawLaw, patch, actualReportEvent] using
        (lg21HiddenAccess_currentReportedValue_ae_on_candidateReport_of_actualReport_zero
          E patch (by simpa [patch] using hpatchMeasurable) scoreValue
          (by simpa [rawLaw, actualReportEvent] using hactualReportZero))
    simpa [rawLaw, scoreValue, patch] using hclassifies_of_current hcurrentValue

/-- On the literal candidate report branch, a score-local patch has only two
semantic kinds of members: incumbent reporters whose attained value is
preserved, or newly promoted scores whose raw posterior strictly exceeds the
incumbent no-report value. -/
theorem lg21HiddenAccess_scoreLocalPatch_reportMember_classifies
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (incumbentNoReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ)
    (scoreValue : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hcandidateReported : ∀ publicBase score,
      candidate.reportedValue publicBase score = scoreValue publicBase score)
    (hpatchMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessScoreLocalReportPatch E.reportDecision
        (lg21ScoreLocalPromotion incumbentNoReport scoreValue) pair.1 pair.2))
    (hcurrentReported : ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport scoreValue))),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport scoreValue))),
      (E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true ∧
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) ∨
      incumbentNoReport (lg21HiddenAccessStudentBase testFeature student.2) <
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
  have hreportEvent : MeasurableSet
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport scoreValue))) := by
    change MeasurableSet
      ((lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport scoreValue))) ⁻¹'
        ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (lg21HiddenAccessOptionalObservedAction_measurable testFeature
        E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision
          (lg21ScoreLocalPromotion incumbentNoReport scoreValue))
        E.takeDecision_measurable hpatchMeasurable)
  rw [ae_restrict_iff' hreportEvent] at hcurrentReported
  rw [ae_restrict_iff' hreportEvent]
  filter_upwards [hcurrentReported] with student hcurrentValue
  intro hmember
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      simp [lg21HiddenAccessRawCandidateReportEvent,
        lg21HiddenAccessOptionalObservedAction] at hmember
  | true =>
      cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
      | false =>
          simp [lg21HiddenAccessRawCandidateReportEvent,
            lg21HiddenAccessOptionalObservedAction, htake] at hmember
      | true =>
          have htake' : E.takeDecision primitive.1
              (lg21HiddenAccessStudentBase testFeature primitive) = true := by
            simpa [lg21HiddenAccessStudentTake] using htake
          by_cases hcurrent : E.reportDecision
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) = true
          · left
            refine ⟨hcurrent, ?_⟩
            rw [hcandidateReported]
            exact (hcurrentValue hmember hcurrent).symm
          · right
            have hpromote : lg21ScoreLocalPromotion incumbentNoReport scoreValue
                (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive) = true := by
              simpa [lg21HiddenAccessRawCandidateReportEvent,
                lg21HiddenAccessOptionalObservedAction,
                lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
                lg21HiddenAccessScoreLocalReportPatch,
                htake', hcurrent] using hmember
            rw [hcandidateReported]
            exact (lg21ScoreLocalPromotion_eq_true_iff
              incumbentNoReport scoreValue
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive)).1 hpromote

/-- Once actual no-takers have null raw mass, a score-local patch changes the
literal visible action exactly on the access/no-report population selected by
its public promotion rule. -/
theorem lg21HiddenAccess_scoreLocalPatch_changedToReportEvent_ae_eq_accessNoReportPromotion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (promote : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
      (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote) =ᵐ[
        lg21ContinuousGaussianPopulationLaw M]
      lg21HiddenAccessAccessNoReportPromotionEvent testFeature E.reportDecision
        promote := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  filter_upwards [hactiveNull] with student hnotActive
  apply propext
  rcases student with ⟨access, primitive⟩
  cases access with
  | false =>
      change
        (lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
          (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote)
          (false, primitive) = true ∧
          ¬ lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
            E.reportDecision (false, primitive) = true) ↔
        ((false = true ∧
          lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false) ∧
          promote (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) = true)
      simp [lg21HiddenAccessOptionalObservedAction]
  | true =>
      cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
      | false =>
          exact (hnotActive (by
            simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
              htake])).elim
      | true =>
          have htake' : E.takeDecision primitive.1
              (lg21HiddenAccessStudentBase testFeature primitive) = true := by
            simpa [lg21HiddenAccessStudentTake] using htake
          change
            (lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
              (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote)
              (true, primitive) = true ∧
              ¬ lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
                E.reportDecision (true, primitive) = true) ↔
            ((true = true ∧
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false) ∧
              promote (lg21HiddenAccessStudentBase testFeature primitive)
                (lg21HiddenAccessStudentScore testFeature primitive) = true)
          cases hpromote : promote
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) <;>
            cases hreport : E.reportDecision
              (lg21HiddenAccessStudentBase testFeature primitive)
              (lg21HiddenAccessStudentScore testFeature primitive) <;>
            simp [lg21HiddenAccessOptionalObservedAction,
              lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
              lg21HiddenAccessScoreLocalReportPatch,
              htake', hpromote, hreport]

/-- The preceding semantic action identity yields equality of literal raw
source masses. -/
theorem lg21HiddenAccess_scoreLocalPatch_changedToReport_mass_eq_accessNoReportPromotion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (promote : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote)) =
      lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportPromotionEvent testFeature E.reportDecision
          promote) := by
  exact measure_congr
    (lg21HiddenAccess_scoreLocalPatch_changedToReportEvent_ae_eq_accessNoReportPromotion
      E promote hactiveNoTakeZero)

/-- A positive selected access/no-report population gives the score-local
patch a positive changed visible-action branch after all taking. -/
theorem lg21HiddenAccess_scoreLocalPatch_changedToReport_positive_of_accessNoReportPromotion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (promote : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hpromotionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportPromotionEvent testFeature E.reportDecision
        promote)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote)) := by
  rw [lg21HiddenAccess_scoreLocalPatch_changedToReport_mass_eq_accessNoReportPromotion
    E promote hactiveNoTakeZero]
  exact hpromotionPositive

/-- A positive changed report-action population gives the candidate a
positive literal report branch. -/
theorem lg21HiddenAccess_scoreLocalPatch_report_positive_of_accessNoReportPromotion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (promote : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hpromotionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportPromotionEvent testFeature E.reportDecision
        promote)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        (lg21HiddenAccessScoreLocalReportPatch E.reportDecision promote)) := by
  apply lt_of_lt_of_le
    (lg21HiddenAccess_scoreLocalPatch_changedToReport_positive_of_accessNoReportPromotion
      E promote hactiveNoTakeZero hpromotionPositive)
  apply measure_mono
  intro student hchanged
  exact hchanged.1

end

end LG21TestOptionalPolicies
