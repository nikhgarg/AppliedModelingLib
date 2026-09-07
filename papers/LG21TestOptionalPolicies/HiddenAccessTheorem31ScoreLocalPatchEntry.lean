import LG21TestOptionalPolicies.HiddenAccessTheorem31ScoreLocalPatchSupport
import LG21TestOptionalPolicies.HiddenAccessTheorem31PublicSelectionPosterior

/-!
# Literal source entry for the LG21 score-local patch

This module assembles the source-timed local candidate once the candidate's
literal no-report PBO has been compared to the incumbent no-report PBO.  The
comparison is intentionally a semantic premise here: its source-law proof is
the remaining base-fibre transport, while every action, positivity, PBO, and
best-response obligation below is discharged from the literal source model.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The public score-local report rule used in the literal Theorem 3.1
candidate.  It promotes exactly scores whose raw Gaussian posterior is
strictly above the incumbent base-only no-report value. -/
def lg21HiddenAccessRawPosteriorScoreLocalPatch
    {Base : Type*} [MeasurableSpace Base]
    (currentReport : Base → ℝ → Bool) (incumbentNoReport : Base → ℝ)
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ) : Base → ℝ → Bool :=
  lg21HiddenAccessScoreLocalReportPatch currentReport
    (lg21ScoreLocalPromotion incumbentNoReport
      (lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance))

/-- A positive literal access/no-report population on which the raw posterior
strictly exceeds the incumbent no-report value yields a source-local entry,
provided the candidate's own literal `X = 0` value weakly lowers that value on
its positive report branch. -/
theorem lg21HiddenAccess_not_stable_of_positive_rawPosteriorGain_scoreLocalPatch
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hnoiseVariance_eq : noiseVariance = (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (hstrictGainPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportStrictGainEvent testFeature E.reportDecision
        E.noReportPayoff
          (lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance)))
    (hcandidateNoReport_le : ∀ᵐ student ∂
      (lg21ContinuousGaussianPopulationLaw M).restrict
        (lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature)
          (lg21HiddenAccessRawPosteriorScoreLocalPatch E.reportDecision
            E.noReportPayoff baseMean hbaseMean baseVariance noiseVariance)),
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
        (lg21HiddenAccessRawPosteriorScoreLocalPatch E.reportDecision
          E.noReportPayoff baseMean hbaseMean baseVariance noiseVariance)
        (lg21HiddenAccessStudentBase testFeature student.2) ≤
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2)) :
    ¬ LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess := by
  subst noiseVariance
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let promote := lg21ScoreLocalPromotion E.noReportPayoff scoreValue
  let candidateReport := lg21HiddenAccessRawPosteriorScoreLocalPatch
    E.reportDecision E.noReportPayoff baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  let candidate := lg21HiddenAccessAllTakeLiteralCandidate M hnoAccess testFeature
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) candidateReport (by
      apply lg21HiddenAccessScoreLocalReportPatch_measurable
      · exact E.reportDecision_measurable
      · apply lg21ScoreLocalPromotion_measurable
        · exact E.noReportPayoff_measurable
        · rw [show (fun pair :
            (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
            scoreValue pair.1 pair.2) =
            (fun pair =>
              gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) * pair.2 +
                gaussianSignalPriorWeight baseVariance (M.noiseVariance testFeature : ℝ) *
                  baseMean pair.1) by
            funext pair
            exact lg21_optional_rawGaussianPosteriorMean_eq_affine
              baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) pair.1 pair.2]
          fun_prop)
  have hscoreValueMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      scoreValue pair.1 pair.2) := by
    rw [show (fun pair :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        scoreValue pair.1 pair.2) =
        (fun pair =>
          gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) * pair.2 +
            gaussianSignalPriorWeight baseVariance (M.noiseVariance testFeature : ℝ) * baseMean pair.1) by
        funext pair
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) pair.1 pair.2]
    fun_prop
  have haccessSourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    calc
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          (lg21ContinuousGaussianPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
              symm
              simpa using
                (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                  M haccess testFeature)
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
            exact hsourceFactor
  have hpromoteMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      promote pair.1 pair.2) :=
    lg21ScoreLocalPromotion_measurable E.noReportPayoff scoreValue
      E.noReportPayoff_measurable hscoreValueMeasurable
  have hcandidateReportMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2) :=
    lg21HiddenAccessScoreLocalReportPatch_measurable E.reportDecision promote
      E.reportDecision_measurable hpromoteMeasurable
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  have hrawActionAE :
      (fun student => lg21HiddenAccessOptionalObservedAction testFeature
        E.takeDecision candidateReport student) =ᵐ[rawLaw]
      (fun student => lg21HiddenAccessOptionalObservedAction testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport student) := by
    filter_upwards [hactiveNull] with student hnot
    rcases student with ⟨access, primitive⟩
    cases access with
    | false =>
        simp [lg21HiddenAccessOptionalObservedAction]
    | true =>
        cases htake : lg21HiddenAccessStudentTake testFeature E.takeDecision primitive with
        | false =>
            exact (hnot (by
              simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
                htake])).elim
        | true =>
            have htake' : E.takeDecision primitive.1
                (lg21HiddenAccessStudentBase testFeature primitive) = true := by
              simpa [lg21HiddenAccessStudentTake] using htake
            simp [lg21HiddenAccessOptionalObservedAction,
              lg21HiddenAccessStudentTake, lg21HiddenAccessAllTake, htake']
  have hcandidateReportAE :
      lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision candidateReport =ᵐ[
        rawLaw]
      lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport := by
    filter_upwards [hrawActionAE] with student haction
    apply propext
    change lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        candidateReport student = true ↔
      lg21HiddenAccessOptionalObservedAction testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport student = true
    rw [haction]
  have hcandidateNoReportAE :
      lg21HiddenAccessRawCandidateNoReportEvent testFeature E.takeDecision candidateReport =ᵐ[
        rawLaw]
      lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport := by
    filter_upwards [hrawActionAE] with student haction
    apply propext
    change lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        candidateReport student = false ↔
      lg21HiddenAccessOptionalObservedAction testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport student = false
    rw [haction]
  have hchangedToReportAE :
      lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision candidateReport =ᵐ[
        rawLaw]
      lg21HiddenAccessCandidateChangedToReportEvent E
        (lg21HiddenAccessAllTake testFeature) candidateReport := by
    filter_upwards [hcandidateReportAE] with student hreport
    apply propext
    change
      (student ∈ lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
          candidateReport ∧ student ∉ lg21HiddenAccessActualReportEvent E) ↔
        (student ∈ lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature) candidateReport ∧
          student ∉ lg21HiddenAccessActualReportEvent E)
    have hreportIff :
        student ∈ lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
            candidateReport ↔
          student ∈ lg21HiddenAccessRawCandidateReportEvent testFeature
            (lg21HiddenAccessAllTake testFeature) candidateReport :=
      Iff.of_eq hreport
    constructor
    · rintro ⟨hold, hactual⟩
      exact ⟨hreportIff.mp hold, hactual⟩
    · rintro ⟨hnew, hactual⟩
      exact ⟨hreportIff.mpr hnew, hactual⟩
  have hpromotionPositive : 0 < rawLaw
      (lg21HiddenAccessAccessNoReportPromotionEvent testFeature E.reportDecision
        promote) := by
    rw [lg21HiddenAccess_accessNoReportPromotionEvent_eq_strictGainEvent]
    simpa [rawLaw, scoreValue] using hstrictGainPositive
  have hchangedReportPositive : 0 < rawLaw
      (lg21HiddenAccessCandidateChangedToReportEvent E E.takeDecision
        candidateReport) := by
    simpa [rawLaw, candidateReport, promote] using
      (lg21HiddenAccess_scoreLocalPatch_changedToReport_positive_of_accessNoReportPromotion
        E promote hactiveNoTakeZero hpromotionPositive)
  have hcandidateReportPositive : 0 < rawLaw
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        candidateReport) := by
    simpa [rawLaw, candidateReport, promote] using
      (lg21HiddenAccess_scoreLocalPatch_report_positive_of_accessNoReportPromotion
        E promote hactiveNoTakeZero hpromotionPositive)
  have hcandidateNoReportPositive : 0 < rawLaw
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature E.takeDecision
        candidateReport) := by
    exact lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess M testFeature
      E.takeDecision candidateReport hnoAccess
  have hchangedReportPositiveAllTake : 0 < rawLaw
      (lg21HiddenAccessCandidateChangedToReportEvent E
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
    rw [← measure_congr hchangedToReportAE]
    exact hchangedReportPositive
  have hcandidateReportPositiveAllTake : 0 < rawLaw
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
    rw [← measure_congr hcandidateReportAE]
    exact hcandidateReportPositive
  have hcandidateNoReportPositiveAllTake : 0 < rawLaw
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
    rw [← measure_congr hcandidateNoReportAE]
    exact hcandidateNoReportPositive
  have hmemberClassifies : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        candidateReport),
      (E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true ∧
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) ∨
      E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
    simpa [rawLaw, candidate, candidateReport, promote, scoreValue] using
      (lg21HiddenAccess_scoreLocalPatch_reportMember_classifies_of_sourcePBO
        E E.noReportPayoff baseLaw baseMean hbaseMean baseVariance hbaseVariance
        hnoiseVariance haccessSourceFactor
        hactiveNoTakeZero candidate (by
          intro publicBase score
          rfl) hcandidateReportMeasurable)
  have hincumbentBestResponse : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature E.takeDecision
        candidateReport),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) :=
    ae_restrict_of_ae (E.reportBestResponse_ae_on_rawPopulation hreportBest)
  have hmemberClassifiesAllTake : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport),
      (E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) = true ∧
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) ∨
      E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        candidate.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
    exact (ae_restrict_congr_set hcandidateReportAE).mp hmemberClassifies
  have hincumbentBestResponseAllTake : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport),
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true →
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
    exact (ae_restrict_congr_set hcandidateReportAE).mp hincumbentBestResponse
  have hcandidateNoReport_le' : ∀ᵐ student ∂rawLaw.restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport),
      candidate.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) ≤
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) := by
    simpa [rawLaw, candidate, candidateReport,
      lg21HiddenAccessAllTakeLiteralCandidate] using hcandidateNoReport_le
  have hcandidateMembersAllTake : PositiveMassBranchMembersBestRespond rawLaw
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) candidate
      (fun P student =>
        P.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) ≤
          P.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)) := by
    exact lg21_positiveMassBranchMembersBestRespond_of_preserved_or_improved
      rawLaw
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)
      (fun student => lg21HiddenAccessStudentBase testFeature student.2)
      (fun student => lg21HiddenAccessStudentScore testFeature student.2)
      E.reportDecision E.noReportPayoff E.reportedPayoff candidate
      hcandidateNoReport_le' hincumbentBestResponseAllTake hmemberClassifiesAllTake
  have hchangedTesterEq : lg21HiddenAccessCandidateChangedTesterEvent E
      (lg21HiddenAccessAllTake testFeature) = E.activeNoTakeEvent := by
    ext student
    rcases student with ⟨access, primitive⟩
    simp [lg21HiddenAccessCandidateChangedTesterEvent,
      LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
      lg21HiddenAccessAllTake, lg21HiddenAccessStudentTake,
      lg21ContinuousPopulationSkill]
  have hchangedTesterZero : rawLaw
      (lg21HiddenAccessCandidateChangedTesterEvent E
        (lg21HiddenAccessAllTake testFeature)) = 0 := by
    simpa [rawLaw, hchangedTesterEq] using hactiveNoTakeZero
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature Set.univ
  have hentry : LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess := {
    region := Set.univ
    region_measurable := MeasurableSet.univ
    region_positive := lg21HiddenAccessBaseRegion_univ_positive M testFeature
    candidateTake := lg21HiddenAccessAllTake testFeature
    candidateReport := candidateReport
    candidate := candidate
    candidate_test_law := by
      intro latentSkill publicBase
      rw [E.raw_test_law]
      simp [candidate, lg21HiddenAccessAllTakeLiteralCandidate,
        lg21HiddenAccessGaussianCandidateWithReportAction]
    candidate_report_action := by rfl
    candidate_take_measurable := lg21HiddenAccessAllTake_measurable testFeature
    candidate_report_measurable := hcandidateReportMeasurable
    candidate_agrees_outside_region := by
      filter_upwards with student
      intro houtside
      exact (houtside (Set.mem_univ student)).elim
    candidate_changed_action_positive := by
      change 0 < localLaw
        (lg21HiddenAccessCandidateChangedActionEvent E
          (lg21HiddenAccessAllTake testFeature) candidateReport)
      have hlocalChangedReportPositive : 0 < localLaw
          (lg21HiddenAccessCandidateChangedToReportEvent E
            (lg21HiddenAccessAllTake testFeature) candidateReport) := by
        simpa only [localLaw, lg21HiddenAccessLocalRawLaw_univ] using
          hchangedReportPositiveAllTake
      apply lt_of_lt_of_le hlocalChangedReportPositive
      apply measure_mono
      intro student hchanged
      exact Or.inr hchanged
    candidate_report_positive := by
      simpa only [lg21HiddenAccessLocalRawLaw_univ] using
        hcandidateReportPositiveAllTake
    candidate_noReport_positive := by
      simpa only [lg21HiddenAccessLocalRawLaw_univ] using
        hcandidateNoReportPositiveAllTake
    candidate_report_pbo := by
      simpa [localLaw, candidate, candidateReport, scoreValue] using
        (lg21HiddenAccessAllTakeLiteralCandidate_sourceTimedReportPBO
          M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
          baseVariance (M.noiseVariance testFeature : ℝ) hbaseVariance hnoiseVariance hsourceFactor
          candidateReport hcandidateReportMeasurable
          (by
            simpa only [lg21HiddenAccessLocalRawLaw_univ] using
              hcandidateReportPositiveAllTake))
    candidate_noReport_pbo := by
      simpa [localLaw, candidate, candidateReport, scoreValue] using
        (lg21HiddenAccessAllTakeLiteralCandidate_sourceTimedNoReportPBO
          M hnoAccess testFeature baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ)
          candidateReport hcandidateReportMeasurable
          (by
            simpa only [lg21HiddenAccessLocalRawLaw_univ] using
              hcandidateNoReportPositiveAllTake))
    candidate_report_members_best_respond := by
      simpa only [lg21HiddenAccessLocalRawLaw_univ] using hcandidateMembersAllTake
    candidate_tester_strict_gain := by
      have hzero : localLaw.restrict
          (lg21HiddenAccessCandidateChangedTesterEvent E
            (lg21HiddenAccessAllTake testFeature)) = 0 := by
        simpa only [localLaw, lg21HiddenAccessLocalRawLaw_univ,
          Measure.restrict_eq_zero] using
          hchangedTesterZero
      rw [hzero]
      simp }
  intro hstable
  exact hstable ⟨hentry⟩

end

end LG21TestOptionalPolicies
