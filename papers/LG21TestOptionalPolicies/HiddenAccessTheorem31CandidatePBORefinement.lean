import LG21TestOptionalPolicies.HiddenAccessTheorem31PositiveReporterClosure
import LG21TestOptionalPolicies.OptionalZeroReporterActiveEntry
import LG21TestOptionalPolicies.RecalibratedBranchMemberEntry

/-!
# Hidden-access local candidate-PBO refinement for LG21 Theorem 3.1

This module is the Section 3 counterpart of the positive-mass candidate
semantics.  It intentionally does *not* reuse the observed-access candidate
construction: when the school does not observe access, a candidate's `X = 0`
law is formed on the literal raw population and therefore includes both
students without access and access students who withhold their score.

The candidate is local to a measurable public-base region.  This is enough
because region membership is public information, while it avoids assigning a
PBO to an individual null base fibre.  The candidate takes all students with
access in that region and has its own positive action-branch PBOs.  Only
members whose actions change are required to best respond to the candidate
PBO; the candidate is not silently declared to be a whole-population
equilibrium.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal candidate action events -/

/-- A candidate considered at a hidden-access null-report region lets every
student with access take the test.  Its only post-score action is the supplied
reporting function; students without access remain unable to report. -/
def lg21HiddenAccessCandidateObservedAction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (student : Bool × (ℝ × (Feature -> ℝ))) : Bool :=
  lg21HiddenAccessOptionalObservedAction testFeature (fun _ _ => true)
    candidateReport student

/-- The literal `X = 1` event of a candidate that lets every access student
take and then uses `candidateReport`. -/
def lg21HiddenAccessCandidateReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessCandidateObservedAction testFeature candidateReport student = true}

/-- The literal `X = 0` event of the same all-access-taking candidate. -/
def lg21HiddenAccessCandidateNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessCandidateObservedAction testFeature candidateReport student = false}

theorem lg21HiddenAccessCandidateObservedAction_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (student : Bool × (ℝ × (Feature -> ℝ))) :
    lg21HiddenAccessCandidateObservedAction testFeature candidateReport student =
      if student.1 = true then
        lg21HiddenAccessStudentReport testFeature candidateReport student.2
      else false := by
  simp [lg21HiddenAccessCandidateObservedAction,
    lg21HiddenAccessOptionalObservedAction, lg21HiddenAccessStudentTake]

theorem lg21HiddenAccessCandidateNoReportEvent_eq_noAccess_union_accessNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    lg21HiddenAccessCandidateNoReportEvent testFeature candidateReport =
      lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessAccessNoReportEvent testFeature candidateReport := by
  simpa only [lg21HiddenAccessCandidateNoReportEvent,
    lg21HiddenAccessCandidateObservedAction] using
    (lg21HiddenAccessOptionalNoReportEvent_eq_noAccess_union_accessNoReport
      testFeature (fun _ _ => true) candidateReport (by
        intro student
        rfl))

theorem lg21HiddenAccessCandidateReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessCandidateReportEvent testFeature candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessCandidateObservedAction testFeature candidateReport) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature (fun _ _ => true)
      candidateReport measurable_const hcandidateReport)

theorem lg21HiddenAccessCandidateNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessCandidateNoReportEvent testFeature candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessCandidateObservedAction testFeature candidateReport) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature (fun _ _ => true)
      candidateReport measurable_const hcandidateReport)

/-! ## Public-base-local raw population -/

/-- The raw source event associated with a public non-test base region. -/
def lg21HiddenAccessBaseRegionEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ)) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessStudentBase testFeature student.2 ∈ region}

theorem lg21HiddenAccessBaseRegionEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region) :
    MeasurableSet (lg21HiddenAccessBaseRegionEvent testFeature region) := by
  exact hregion.preimage
    ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)

/-- The literal raw law restricted and normalized on a measurable public-base
region.  It retains the unobserved access coordinate. -/
def lg21HiddenAccessLocalRawLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ)) :
    Measure (Bool × (ℝ × (Feature -> ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    (lg21HiddenAccessBaseRegionEvent testFeature region)

/-- The full public/base-score-skill observation used to express a candidate
PBO.  The access bit is deliberately absent from the observation. -/
def lg21HiddenAccessBaseScoreSkillObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
  fun student =>
    (lg21HiddenAccessStudentBase testFeature student.2,
      (lg21HiddenAccessStudentScore testFeature student.2,
        lg21ContinuousPopulationSkill student))

theorem lg21HiddenAccessBaseScoreSkillObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessBaseScoreSkillObservation (Feature := Feature)
      testFeature) := by
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentScore testFeature student.2) :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  exact hbase.prodMk (hscore.prodMk hskill)

/-- The independent access draw gives every positive base region positive
no-access mass whenever `P(Z = 0) > 0`.  This is the fact that makes the
candidate's hidden-access `X = 0` PBO a genuine mixed-population PBO. -/
theorem lg21HiddenAccess_noAccess_inter_baseRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hnoAccess : 0 < M.accessLaw {false})
    (hregion : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessNoAccessEvent ∩
        lg21HiddenAccessBaseRegionEvent testFeature region) := by
  let primitiveRegion : Set (ℝ × (Feature -> ℝ)) :=
    {primitive | lg21HiddenAccessStudentBase testFeature primitive ∈ region}
  have hregionEq : lg21HiddenAccessBaseRegionEvent testFeature region =
      Set.univ ×ˢ primitiveRegion := by
    ext student
    simp [lg21HiddenAccessBaseRegionEvent, primitiveRegion]
  have hintersectionEq : lg21HiddenAccessNoAccessEvent ∩
      lg21HiddenAccessBaseRegionEvent testFeature region =
      ({false} : Set Bool) ×ˢ primitiveRegion := by
    rw [hregionEq, lg21HiddenAccessNoAccessEvent_eq_false_rectangle]
    ext student
    simp
  have hprimitivePositive : 0 <
      lg21ContinuousGaussianStudentPrimitiveLaw M primitiveRegion := by
    rw [hregionEq,
      lg21ContinuousGaussianPopulation_access_student_factorization] at hregion
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    rw [IsProbabilityMeasure.measure_univ, one_mul] at hregion
    exact hregion
  rw [hintersectionEq,
    lg21ContinuousGaussianPopulation_access_student_factorization]
  exact ENNReal.mul_pos (ne_of_gt hnoAccess) (ne_of_gt hprimitivePositive)

/-- Under a positive raw base region and positive no-access mass, the local
candidate's `X = 0` event has positive mass before any posterior is written.
The proof uses the literal no-access component, not the access-conditioned
population law. -/
theorem lg21HiddenAccess_localCandidateNoReport_positive_of_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateNoReportEvent testFeature candidateReport) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let candidateNoReport :=
    lg21HiddenAccessCandidateNoReportEvent testFeature candidateReport
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hcandidateNoReport : MeasurableSet candidateNoReport := by
    simpa [candidateNoReport] using
      (lg21HiddenAccessCandidateNoReportEvent_measurable testFeature
        candidateReport hcandidateReport)
  have hcomponentPositive : 0 < rawLaw (noAccess ∩ regionEvent) := by
    simpa [rawLaw, noAccess, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive M testFeature region
        hnoAccess hregionPositive)
  have hsubset : noAccess ∩ regionEvent ⊆ candidateNoReport ∩ regionEvent := by
    intro student hstudent
    rcases hstudent with ⟨hnoAccessStudent, hregionStudent⟩
    refine ⟨?_, hregionStudent⟩
    change student ∈ lg21HiddenAccessCandidateNoReportEvent testFeature candidateReport
    rw [lg21HiddenAccessCandidateNoReportEvent_eq_noAccess_union_accessNoReport]
    exact Or.inl (by simpa [noAccess] using hnoAccessStudent)
  have htargetPositive : 0 < rawLaw (candidateNoReport ∩ regionEvent) :=
    lt_of_lt_of_le hcomponentPositive (measure_mono hsubset)
  change 0 < lg21NormalizedRestriction rawLaw regionEvent candidateNoReport
  rw [lg21NormalizedRestriction_apply rawLaw hcandidateNoReport]
  have hintersection : candidateNoReport ∩ regionEvent =
      candidateNoReport ∩ regionEvent := rfl
  rw [hintersection]
  exact ENNReal.mul_pos
    (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw regionEvent))
    (ne_of_gt htargetPositive)

/-! ## Candidate PBOs on the literal local law -/

/-- Candidate report-branch PBO on a raw, public-base-localized source law.
`X = 1` implies access, but the conditional law is still induced by the
candidate's literal action event rather than an access-only source law. -/
def LG21HiddenAccessCandidateReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidate.reportDecision pair.1 pair.2))
    (hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision)) : Prop :=
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision
  let actionLaw :=
    (lg21NormalizedRestriction localLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure (lg21ContinuousGaussianPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability
      (lg21ContinuousGaussianPopulationLaw M)
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

/-- Candidate no-report-branch PBO on the same literal local law.  In
particular, the action law being conditioned includes its no-access component
whenever that component has positive mass. -/
def LG21HiddenAccessCandidateNoReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessCandidateNoReportEvent testFeature candidate.reportDecision)) : Prop :=
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21HiddenAccessCandidateNoReportEvent testFeature candidate.reportDecision
  let actionLaw :=
    (lg21NormalizedRestriction localLaw noReportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure (lg21ContinuousGaussianPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability
      (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw noReportEvent
      (ne_of_gt hnoReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ scoreSkill, scoreSkill.2 ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-! ## Source-local candidate entry and refinement -/

/-- The literal current `X = 1` event of a hidden-access source equilibrium.
It is stated as an action event rather than inferred from a strategy name. -/
def lg21HiddenAccessActualReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
    E.reportDecision student = true}

theorem lg21HiddenAccessActualReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    MeasurableSet (lg21HiddenAccessActualReportEvent E) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision E.reportDecision) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature E.takeDecision
      E.reportDecision E.takeDecision_measurable E.reportDecision_measurable)

/-- A source-local positive-mass candidate entry at a region on which the
current hidden-access action has no reporters.  The candidate lets every
access student in the local population take, and evaluates its reporting and
no-reporting branches under the candidate's own literal raw action laws.

`candidate_tester_strict_gain` is checked only for members whose pre-score
action changes from no-take.  `candidate_report_members_best_respond` is the
post-score Definition-1 check for the positive reporting branch.  The
candidate is intentionally not required to be a full alternate equilibrium.
-/
structure LG21HiddenAccessAllTakeLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) where
  region : Set (LG21NonTestFeature Feature testFeature -> ℝ)
  region_measurable : MeasurableSet region
  region_positive : 0 < lg21ContinuousGaussianPopulationLaw M
    (lg21HiddenAccessBaseRegionEvent testFeature region)
  current_reporter_zero : lg21ContinuousGaussianPopulationLaw M
    (lg21HiddenAccessBaseRegionEvent testFeature region ∩
      lg21HiddenAccessActualReportEvent E) = 0
  candidate : LG21OptionalCandidateBranchData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  candidate_report_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    candidate.reportDecision pair.1 pair.2)
  candidate_report_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision)
  candidate_report_pbo : LG21HiddenAccessCandidateReportPBOOn M testFeature region
    region_positive candidate candidate_report_measurable candidate_report_positive
  candidate_noReport_pbo :
    LG21HiddenAccessCandidateNoReportPBOOn M testFeature region region_positive candidate
      (lg21HiddenAccess_localCandidateNoReport_positive_of_noAccess M testFeature region
        region_measurable region_positive hnoAccess candidate.reportDecision
        candidate_report_measurable)
  candidate_report_members_best_respond :
    PositiveMassBranchMembersBestRespond
      (lg21HiddenAccessLocalRawLaw M testFeature region)
      (lg21HiddenAccessCandidateReportEvent testFeature candidate.reportDecision)
      candidate
      (fun P student =>
        P.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) ≤
          P.reportedValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2))
  candidate_tester_strict_gain : ∀ student,
    student ∈ lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.activeNoTakeEvent ->
      candidate.noReportValue (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21OptionalCandidateTestExpectedValue candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2)

/-- An equilibrium is stable against the source's positive-mass action/PBO
fixed-point semantics only if it admits no hidden-access local candidate entry
of the preceding form.  This is a semantic stability predicate, not a belief
completion on an unused branch. -/
def LG21HiddenAccessStableAgainstAllTakeLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) : Prop :=
  ¬ Nonempty (LG21HiddenAccessAllTakeLocalCandidateEntry E hnoAccess)

/-- A concrete literal candidate entry refutes local candidate-PBO stability.
The theorem's conclusion is deliberately only the failure of the refinement;
it does not claim that the candidate is itself a global equilibrium. -/
theorem lg21HiddenAccess_not_stable_of_allTakeLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hentry : LG21HiddenAccessAllTakeLocalCandidateEntry E hnoAccess) :
    ¬ LG21HiddenAccessStableAgainstAllTakeLocalCandidateEntry E hnoAccess := by
  intro hstable
  exact hstable ⟨hentry⟩

/-- The exact global closure needed for the all-taking portion of Theorem
3.1.  If actual access no-takers have positive raw mass, then either their
attained public bases have the positive reporter fibres handled by the
on-path PBO bridge, or a positive raw region with zero current reporter mass
has the literal hidden-access candidate entry above.

The alternatives are stated extensionally in terms of action events and
candidate conditional means.  In particular, this does not classify a case
from names such as `allNoReporter`, nor does it normalize an access-only law
at the zero-reporter branch.
-/
def LG21HiddenAccessPositiveReporterOrAllTakeEntrySplit
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false}) : Prop :=
  ∀ hactive : 0 < lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent,
    LG21HiddenAccessPositiveReporterFibreClosure E ∨
      Nonempty (LG21HiddenAccessAllTakeLocalCandidateEntry E hnoAccess)

/-- Positive attained reporter fibres close the first branch of the split;
the source-local candidate refinement closes the second.  This combines the
two alternatives without assigning a PBO at a null reporter branch. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent_measure_zero_of_allTakeReporterSplit
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hsplit : LG21HiddenAccessPositiveReporterOrAllTakeEntrySplit E hnoAccess)
    (hstable : LG21HiddenAccessStableAgainstAllTakeLocalCandidateEntry E hnoAccess) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  by_contra hnotZero
  have hactive : 0 < lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent :=
    pos_iff_ne_zero.mpr hnotZero
  rcases hsplit hactive with hpositiveReporter | hentry
  · have hzero := E.activeNoTakeEvent_measure_zero_of_positiveReporterFibreClosure
      hpositiveReporter
    exact hnotZero hzero
  · exact hstable hentry

end

end LG21TestOptionalPolicies
