import LG21TestOptionalPolicies.HiddenAccessTheorem31RawCandidateActions

/-!
# Source-timed local candidate entries for LG21 Theorem 3.1

The older local-entry carrier was deliberately limited to a candidate that
made every access student take.  That special case is useful, but it cannot
stand in for a proof about arbitrary source-timed deviations.  This module
records the general carrier explicitly: `Y` is chosen from latent skill and
public base before the score is drawn, while `X` is chosen from public base
and score afterwards.  Every candidate PBO below is evaluated on the literal
raw `Z,Y,X` action event, so a hidden no-access population is retained in the
candidate's `X = 0` law.

An inside-region candidate may replace the predecessor's report action.  Its
positive-mass witness is therefore the literal changed action event, not an
assumption that the predecessor had no reporters in that region.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal source-timed candidate PBOs -/

/-- Candidate report-branch PBO on a localized raw source population.  The
report event includes both the pre-score candidate take action and the
post-score candidate report action. -/
def LG21HiddenAccessSourceTimedCandidateReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        candidateTake candidateReport)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    candidateTake candidateReport
  let actionLaw := (lg21NormalizedRestriction localLaw reportEvent).map
    (lg21HiddenAccessBaseScoreSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
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
        actionLaw publicObservation

/-- Candidate no-report-branch PBO on a localized raw source population.
Unlike an access-conditioned selected law, this event contains literal
no-access students whenever they are in the localized population. -/
def LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        candidateTake candidateReport)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  let actionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map
    (lg21HiddenAccessBaseSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw noReportEvent
      (ne_of_gt hnoReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ skill, skill ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-! ## Changed source actions -/

/-- Access students whose pre-score action changes from not taking to taking
under a source-timed candidate. -/
def lg21HiddenAccessCandidateChangedTesterEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true ∧
    E.takeDecision (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = false ∧
    candidateTake (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true}

/-- Students whose final visible action changes from no report to report under
a candidate.  The candidate report event is literal and therefore cannot
contain a no-access student. -/
def lg21HiddenAccessCandidateChangedToReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake candidateReport ∩
    (lg21HiddenAccessActualReportEvent E)ᶜ

/-- The candidate action change relevant to the paper's positive-mass
recalibration reading: either a previously inactive access student starts to
take, or a final report action becomes newly visible. -/
def lg21HiddenAccessCandidateChangedActionEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  lg21HiddenAccessCandidateChangedTesterEvent E candidateTake ∪
    lg21HiddenAccessCandidateChangedToReportEvent E candidateTake candidateReport

/-! ## General local entry and closure -/

/-- A source-local positive-mass entry with separate candidate `Y` and `X`
actions.  The equality tying `candidateReport` to the candidate payoff record
prevents the PBO branch and the continuation payoff from silently using
different report decisions. -/
structure LG21HiddenAccessSourceLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) where
  region : Set (LG21NonTestFeature Feature testFeature -> ℝ)
  region_measurable : MeasurableSet region
  region_positive : 0 < lg21ContinuousGaussianPopulationLaw M
    (lg21HiddenAccessBaseRegionEvent testFeature region)
  candidateTake : ℝ → (LG21NonTestFeature Feature testFeature -> ℝ) → Bool
  candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool
  candidate : LG21OptionalCandidateBranchData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  /-- A local deviation changes actions and the induced action-branch PBOs,
  not the paper's exogenous score technology.  In particular, every candidate
  is evaluated under the same Gaussian score law as the source equilibrium. -/
  candidate_test_law : ∀ latentSkill publicBase,
    candidate.testLaw latentSkill publicBase = E.testLaw latentSkill publicBase
  candidate_report_action : candidate.reportDecision = candidateReport
  candidate_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) => candidateTake pair.1 pair.2)
  candidate_report_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    candidateReport pair.1 pair.2)
  candidate_agrees_outside_region : ∀ᵐ student ∂lg21ContinuousGaussianPopulationLaw M,
    lg21HiddenAccessStudentBase testFeature student.2 ∉ region →
      candidateTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) =
          E.takeDecision (lg21ContinuousPopulationSkill student)
            (lg21HiddenAccessStudentBase testFeature student.2) ∧
      candidateReport (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
          E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)
  candidate_changed_action_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessCandidateChangedActionEvent E candidateTake candidateReport)
  candidate_report_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake candidateReport)
  candidate_noReport_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake candidateReport)
  candidate_report_pbo : LG21HiddenAccessSourceTimedCandidateReportPBOOn
    M testFeature region region_positive candidateTake candidateReport candidate
      candidate_report_positive
  candidate_noReport_pbo : LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
    M testFeature region region_positive candidateTake candidateReport candidate
      candidate_noReport_positive
  candidate_report_members_best_respond :
    PositiveMassBranchMembersBestRespond
      (lg21HiddenAccessLocalRawLaw M testFeature region)
      (lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake candidateReport)
      candidate
      (fun P student =>
        P.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) ≤
          P.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2))
  candidate_tester_strict_gain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21HiddenAccessCandidateChangedTesterEvent E candidateTake),
      candidate.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21OptionalCandidateTestExpectedValue candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2)

/-- Stability against the source's positive-mass candidate recalibration
semantics.  This definition contains no PBO completion at a null branch. -/
def LG21HiddenAccessSourceStableAgainstLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) : Prop :=
  ¬ Nonempty (LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess)

theorem lg21HiddenAccess_not_stable_of_sourceLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hentry : LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess) :
    ¬ LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess := by
  intro hstable
  exact hstable ⟨hentry⟩

end

end LG21TestOptionalPolicies
