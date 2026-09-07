import LG21TestOptionalPolicies.ReportRequiredHiddenAccessMixtureRoot
import LG21TestOptionalPolicies.ReportRequiredBaseDependentTailSourceBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate
import LG21TestOptionalPolicies.SelectedObservationConditionalInvariance

/-!
# Report-required hidden-access local-tail closeout

This module deliberately contains only the report-required local-tail
semantics.  A candidate chooses its test action before its score is drawn and
must report after taking.  Its no-report branch is normalized from the raw
hidden-access population, so it retains no-access students.

The final source endpoint takes literal branch-PBO evidence explicitly.  That
evidence is the remaining source bridge: it cannot be replaced by a whole
equilibrium record or an arbitrary off-path posterior.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open Probability

/-- The only data used by a report-required local candidate.  In particular,
this is not a global sequential-equilibrium record and carries no opaque
estimator-consistency field. -/
structure LG21ReportRequiredTailCandidateData
    (Skill Base Test : Type*) [MeasurableSpace Test] where
  testLaw : Skill -> Base -> Measure Test
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : Skill -> Base -> Bool
  reportedPayoff : Base -> Test -> ℝ
  noReportPayoff : Base -> ℝ
  reportedPayoff_integrable : ∀ skill base,
    Integrable (reportedPayoff base) (testLaw skill base)

/-- Expected payoff of the only strategic decision in report-required timing. -/
def lg21ReportRequiredTailTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (candidate : LG21ReportRequiredTailCandidateData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  ∫ test, candidate.reportedPayoff base test ∂candidate.testLaw skill base

/-- A report-required candidate reports exactly when an access student takes.
There is no post-score decision in this event. -/
def lg21ReportRequiredTailReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake (fun _ _ => true)

/-- The complementary report-required branch contains all no-access students
and access students who do not take. -/
def lg21ReportRequiredTailNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake (fun _ _ => true)

/-- The access students whose pre-score testing action changes under a local
candidate. -/
def lg21ReportRequiredTailChangedTesterEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (currentTake candidateTake :
      ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | student.1 = true ∧
    currentTake (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = false ∧
    candidateTake (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true}

/-- Literal local PBO obligation on the report branch. -/
def LG21ReportRequiredTailReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21ReportRequiredTailCandidateData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision
  let actionLaw := (lg21NormalizedRestriction localLaw reportEvent).map
    (lg21HiddenAccessBaseScoreSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw := lg21ContinuousGaussianPopulationLaw_isProbability M
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
    candidate.reportedPayoff publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          scoreSkill.2.2)
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Literal local PBO obligation on the raw no-report branch. -/
def LG21ReportRequiredTailNoReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21ReportRequiredTailCandidateData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision
  let actionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map
    (lg21HiddenAccessBaseSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw := lg21ContinuousGaussianPopulationLaw_isProbability M
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
    candidate.noReportPayoff publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-- A verified local entry has positive changed mass, literal PBOs on both
positive action branches, and strict pre-score gain for changed takers. -/
structure LG21ReportRequiredLocalTailEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) where
  region : Set (LG21NonTestFeature Feature testFeature -> ℝ)
  region_measurable : MeasurableSet region
  region_positive : 0 < lg21ContinuousGaussianPopulationLaw M
    (lg21HiddenAccessBaseRegionEvent testFeature region)
  current_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2)
  current_take_zero : lg21HiddenAccessLocalRawLaw M testFeature region
    {student | student.1 = true ∧
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0
  candidate : LG21ReportRequiredTailCandidateData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  /-- The deviation preserves the paper's fixed Gaussian test technology. -/
  candidate_test_law : ∀ latentSkill publicBase,
    candidate.testLaw latentSkill publicBase =
      gaussianReal latentSkill (M.noiseVariance testFeature)
  candidate_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) =>
    candidate.takeDecision pair.1 pair.2)
  candidate_report_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision)
  candidate_noReport_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision)
  candidate_report_pbo : LG21ReportRequiredTailReportPBOOn M testFeature region
    region_positive candidate candidate_report_positive
  candidate_noReport_pbo : LG21ReportRequiredTailNoReportPBOOn M testFeature region
    region_positive candidate candidate_noReport_positive
  candidate_changed_taker_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
      candidate.takeDecision)
  candidate_changed_taker_strict_gain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredTailTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2)

/-- Stability rules out exactly the locally recalibrated entries above. -/
def LG21ReportRequiredStableAgainstLocalTailEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) : Prop :=
  ¬ Nonempty (LG21ReportRequiredLocalTailEntry
    (M := M) (testFeature := testFeature) currentTake)

theorem lg21ReportRequired_not_stable_of_localTailEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (entry : LG21ReportRequiredLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake) :
    ¬ LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake := by
  intro hstable
  exact hstable ⟨entry⟩

/-- The concrete selected upper-tail candidate with a literal raw-mixture
no-report value. -/
noncomputable def lg21ReportRequiredHiddenAccessTailCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    LG21ReportRequiredTailCandidateData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ := by
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  exact
    { testLaw := fun latentSkill _publicBase =>
        gaussianReal latentSkill noiseVariance.toNNReal
      testLaw_isProbability := by
        intro latentSkill publicBase
        infer_instance
      takeDecision := fun latentSkill publicBase =>
        decide (threshold publicBase ≤ latentSkill)
      reportedPayoff := fun publicBase observedScore =>
        lg21SelectedGaussianUpperTailReporterPBO
          (baseMean publicBase) baseVariance noiseVariance
          (threshold publicBase) observedScore
      noReportPayoff := fun publicBase =>
        lg21HiddenAccessTailCandidateNoReportValue
          (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
          noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase
      reportedPayoff_integrable := by
        intro latentSkill publicBase
        exact lg21SelectedGaussianUpperTailReporterPBO_integrable
          (baseMean publicBase) baseVariance noiseVariance
          (threshold publicBase) latentSkill hbaseVariance hnoiseVariance }

theorem lg21ReportRequiredHiddenAccessTailCandidate_take_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤) (haccessFinite : accessMass ≠ ⊤)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    (lg21ReportRequiredHiddenAccessTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite).takeDecision skill publicBase = true ↔
      threshold publicBase ≤ skill := by
  simp [lg21ReportRequiredHiddenAccessTailCandidate]

/-- At a literal raw-mixture root, every tail taker strictly above its cutoff
has a strict pre-score gain.  This uses only the selected reporter formula;
it does not impose a score-contingent reporting action. -/
theorem lg21ReportRequiredHiddenAccessTail_strictGain_of_take_off_boundary
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤) (haccessFinite : accessMass ≠ ⊤)
    [IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)]
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance (threshold publicBase) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase)
    (skill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (htake :
      (lg21ReportRequiredHiddenAccessTailCandidate
        baseMean threshold hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessFinite haccessFinite).takeDecision skill publicBase = true)
    (hboundary : skill ≠ threshold publicBase) :
    (lg21ReportRequiredHiddenAccessTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite).noReportPayoff publicBase <
      lg21ReportRequiredTailTakeExpectedPayoff
        (lg21ReportRequiredHiddenAccessTailCandidate
          baseMean threshold hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance noAccessMass accessMass
          hnoAccessFinite haccessFinite)
        skill publicBase := by
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance noAccessMass accessMass hnoAccessFinite haccessFinite
  have hcutoff : threshold publicBase ≤ skill :=
    (lg21ReportRequiredHiddenAccessTailCandidate_take_iff
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass hnoAccessFinite haccessFinite
      skill publicBase).1 htake
  have hstrictCutoff : threshold publicBase < skill :=
    lt_of_le_of_ne hcutoff (Ne.symm hboundary)
  have hstrict : StrictMono (fun latentSkill =>
      lg21ReportRequiredTailTakeExpectedPayoff candidate latentSkill publicBase) := by
    simpa [candidate, lg21ReportRequiredTailTakeExpectedPayoff,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_strictMono
        baseMean threshold
        (fun base => lg21HiddenAccessTailCandidateNoReportValue
          (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
          noAccessMass accessMass hnoAccessFinite haccessFinite threshold base)
        baseVariance noiseVariance hbaseVariance hnoiseVariance publicBase)
  have hcutoffValue :
      lg21ReportRequiredTailTakeExpectedPayoff candidate
        (threshold publicBase) publicBase = candidate.noReportPayoff publicBase := by
    calc
      lg21ReportRequiredTailTakeExpectedPayoff candidate
          (threshold publicBase) publicBase =
          lg21SelectedGaussianCutoffBoundaryPayoff
            (baseMean publicBase) baseVariance noiseVariance (threshold publicBase) := by
              simpa [candidate, lg21ReportRequiredTailTakeExpectedPayoff,
                lg21ReportRequiredHiddenAccessTailCandidate] using
                (lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_at_cutoff_eq_boundary
                  baseMean threshold
                  (fun base => lg21HiddenAccessTailCandidateNoReportValue
                    (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
                    noAccessMass accessMass hnoAccessFinite haccessFinite threshold base)
                  baseVariance noiseVariance hbaseVariance hnoiseVariance publicBase)
      _ = candidate.noReportPayoff publicBase := by
        simpa [candidate, lg21ReportRequiredHiddenAccessTailCandidate] using hroot publicBase
  calc
    candidate.noReportPayoff publicBase =
        lg21ReportRequiredTailTakeExpectedPayoff candidate
          (threshold publicBase) publicBase := hcutoffValue.symm
    _ < lg21ReportRequiredTailTakeExpectedPayoff candidate skill publicBase :=
      hstrict hstrictCutoff

/-- If current taker mass is zero, every positive candidate report branch has
positive changed-taker mass. -/
theorem lg21ReportRequiredTail_changedTaker_positive_of_currentTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (currentTake candidateTake :
      ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0)
    (hcandidateReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailReportEvent testFeature candidateTake)) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake candidateTake) := by
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let currentTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true ∧
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
  let reportEvent := lg21ReportRequiredTailReportEvent testFeature candidateTake
  let changedEvent := lg21ReportRequiredTailChangedTesterEvent testFeature
    currentTake candidateTake
  have hreportEvent : reportEvent =
      {student | student.1 = true ∧
        candidateTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} := by
    ext student
    rcases student with ⟨access, primitive⟩
    rcases primitive with ⟨skill, noise⟩
    cases access <;>
      simp [reportEvent, lg21ReportRequiredTailReportEvent,
        lg21HiddenAccessRawCandidateReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
        lg21ContinuousPopulationSkill]
  by_contra hnotPositive
  have hchangedZero : localLaw changedEvent = 0 :=
    le_antisymm (not_lt.mp hnotPositive) (zero_le _)
  have hunionZero : localLaw (changedEvent ∪ currentTakeEvent) = 0 :=
    measure_union_null hchangedZero (by simpa [localLaw, currentTakeEvent] using hcurrentZero)
  have hsubset : reportEvent ⊆ changedEvent ∪ currentTakeEvent := by
    intro student hreport
    rw [hreportEvent] at hreport
    by_cases hcurrent : currentTake
        (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = false
    · left
      exact ⟨hreport.1, hcurrent, hreport.2⟩
    · right
      have hcurrentTrue : currentTake
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true := by
        cases hdecision : currentTake
            (lg21ContinuousPopulationSkill student)
            (lg21HiddenAccessStudentBase testFeature student.2) <;> simp_all
      exact ⟨hreport.1, hcurrentTrue⟩
  have hreportZero : localLaw reportEvent = 0 := measure_mono_null hsubset hunionZero
  exact (ne_of_gt hcandidateReportPositive)
    (by simpa [localLaw, reportEvent] using hreportZero)

/-- Exact branch evidence needed to complete the zero-current-taker local
contradiction.  Each field is a literal action-law statement, not an
equilibrium-consistency placeholder. -/
structure LG21ReportRequiredTailLocalBranchEvidence
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21ReportRequiredTailCandidateData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ) where
  candidate_test_law : ∀ latentSkill publicBase,
    candidate.testLaw latentSkill publicBase =
      gaussianReal latentSkill (M.noiseVariance testFeature)
  candidate_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) =>
    candidate.takeDecision pair.1 pair.2)
  report_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision)
  noReport_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision)
  report_pbo : LG21ReportRequiredTailReportPBOOn M testFeature region
    hregionPositive candidate report_positive
  noReport_pbo : LG21ReportRequiredTailNoReportPBOOn M testFeature region
    hregionPositive candidate noReport_positive
  changed_taker_strict_gain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredTailTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2)

/-- The zero-current-taker contradiction from literal report-required branch
evidence.  The hypotheses visibly isolate the outstanding source-selected
posterior bridge rather than disguising it as a global equilibrium field. -/
theorem lg21ReportRequired_not_stable_of_zeroCurrentTakeRegion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hcurrentTakeZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0)
    (candidate : LG21ReportRequiredTailCandidateData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (evidence : LG21ReportRequiredTailLocalBranchEvidence
      currentTake region hregionPositive candidate) :
    ¬ LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake := by
  have hchangedPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
        candidate.takeDecision) :=
    lg21ReportRequiredTail_changedTaker_positive_of_currentTake_zero
      region currentTake candidate.takeDecision hcurrentTakeZero evidence.report_positive
  apply lg21ReportRequired_not_stable_of_localTailEntry currentTake
  exact
    { region := region
      region_measurable := hregion
      region_positive := hregionPositive
      current_take_measurable := hcurrentTake
      current_take_zero := hcurrentTakeZero
      candidate := candidate
      candidate_test_law := evidence.candidate_test_law
      candidate_take_measurable := evidence.candidate_take_measurable
      candidate_report_positive := evidence.report_positive
      candidate_noReport_positive := evidence.noReport_positive
      candidate_report_pbo := evidence.report_pbo
      candidate_noReport_pbo := evidence.noReport_pbo
      candidate_changed_taker_positive := hchangedPositive
      candidate_changed_taker_strict_gain := evidence.changed_taker_strict_gain }

/-- On the literal global raw population, the selected-tail candidate has a
strict gain on its changed tester branch except on its Gaussian-null cutoff
graph. -/
theorem lg21ReportRequiredHiddenAccessTail_changedTaker_strictGain_ae_of_source
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    [IsFiniteMeasure M.accessLaw]
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    [IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)]
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance
        (baseMean publicBase + gap) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _)
        (fun publicBase => baseMean publicBase + gap) publicBase) :
    ∀ᵐ student ∂
      (lg21ContinuousGaussianPopulationLaw M).restrict
        (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
          (lg21ReportRequiredHiddenAccessTailCandidate
            baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            (M.accessLaw {false}) (M.accessLaw {true})
            (measure_ne_top _ _) (measure_ne_top _ _)).takeDecision),
      (lg21ReportRequiredHiddenAccessTailCandidate
        baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _)).noReportPayoff
          (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredTailTakeExpectedPayoff
          (lg21ReportRequiredHiddenAccessTailCandidate
            baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            (M.accessLaw {false}) (M.accessLaw {true})
            (measure_ne_top _ _) (measure_ne_top _ _))
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) := by
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    (measure_ne_top _ _) (measure_ne_top _ _)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let baseSkill := lg21HiddenAccessBaseSkillObservation testFeature
  let graph : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    {baseSkill | baseSkill.2 = threshold baseSkill.1}
  let boundaryEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    baseSkill ⁻¹' graph
  let changedEvent := lg21ReportRequiredTailChangedTesterEvent
    testFeature currentTake candidate.takeDecision
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hbaseSkill : Measurable baseSkill := by
    simpa [baseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hgraph : MeasurableSet graph := by
    simpa [graph] using
      measurableSet_eq_fun measurable_snd (hthreshold.comp measurable_fst)
  have hboundaryEvent : MeasurableSet boundaryEvent :=
    hgraph.preimage hbaseSkill
  have hrawBaseSkillFactor : rawLaw.map baseSkill =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        baseVariance.toNNReal := by
    simpa [rawLaw, baseSkill] using
      (lg21ReportRequiredBaseDependentTail_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
        M testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
        hsourceFactor)
  have hrawBoundary : rawLaw boundaryEvent = 0 := by
    calc
      rawLaw boundaryEvent = rawLaw.map baseSkill graph := by
        symm
        exact Measure.map_apply hbaseSkill hgraph
      _ = (baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) graph := by
            rw [hrawBaseSkillFactor]
      _ = 0 :=
        lg21ReportRequiredBaseDependentTail_gaussianLocation_graph_measure_zero
          baseLaw baseMean hbaseMean baseVariance hbaseVariance threshold hthreshold
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hskill : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21ContinuousPopulationSkill student) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have htailTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2) := by
    simpa [candidate, threshold, lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21HiddenAccessConditionalMeanTailTake_measurable
        testFeature threshold hthreshold)
  have hcurrentRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    hcurrentTake.comp (hskill.prodMk hbase)
  have htailRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      candidate.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    htailTake.comp (hskill.prodMk hbase)
  have hchangedEvent : MeasurableSet changedEvent := by
    dsimp only [changedEvent, lg21ReportRequiredTailChangedTesterEvent]
    change MeasurableSet ({student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true} ∩
        ({student | currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = false} ∩
        {student | candidate.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true}))
    exact ((measurableSet_singleton true).preimage measurable_fst).inter
      (((measurableSet_singleton false).preimage hcurrentRaw).inter
        ((measurableSet_singleton true).preimage htailRaw))
  have hboundaryChanged : (rawLaw.restrict changedEvent) boundaryEvent = 0 := by
    rw [Measure.restrict_apply hboundaryEvent]
    exact measure_mono_null inter_subset_left hrawBoundary
  have hnotBoundary : ∀ᵐ student ∂rawLaw.restrict changedEvent,
      student ∉ boundaryEvent := by
    rw [ae_iff]
    simpa using hboundaryChanged
  have hchangedMember : ∀ᵐ student ∂rawLaw.restrict changedEvent,
      student ∈ changedEvent := ae_restrict_mem hchangedEvent
  filter_upwards [hnotBoundary, hchangedMember] with student hnotBoundary hchanged
  have htake : candidate.takeDecision (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true := hchanged.2.2
  have hnotEqual : lg21ContinuousPopulationSkill student ≠
      threshold (lg21HiddenAccessStudentBase testFeature student.2) := by
    intro heq
    apply hnotBoundary
    change lg21ContinuousPopulationSkill student =
      threshold (lg21HiddenAccessStudentBase testFeature student.2)
    exact heq
  simpa [candidate, threshold] using
    (lg21ReportRequiredHiddenAccessTail_strictGain_of_take_off_boundary
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
      (measure_ne_top _ _) (measure_ne_top _ _)
      (by simpa [threshold] using hroot)
      (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) htake hnotEqual)

/-- A literal source Gaussian population with no current access takers is
not stable against the report-required upper-tail entry.  Both candidate PBOs
are derived from its actual positive raw action branches. -/
theorem lg21ReportRequired_not_stable_of_globalCurrentTake_zero_of_source
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (hcurrentTakeZero : lg21ContinuousGaussianPopulationLaw M
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0) :
    ¬ LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake := by
  classical
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := measure_ne_top _ _
  have hregionPositive : 0 < rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature Set.univ) := by
    have hregion : lg21HiddenAccessBaseRegionEvent testFeature
        (Set.univ : Set (LG21NonTestFeature Feature testFeature -> ℝ)) = Set.univ := by
      ext student
      simp [lg21HiddenAccessBaseRegionEvent]
    rw [hregion]
    simp [rawLaw]
  have hlocalCurrentTakeZero : lg21HiddenAccessLocalRawLaw M testFeature Set.univ
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0 := by
    rw [lg21HiddenAccessLocalRawLaw_univ]
    simpa [rawLaw] using hcurrentTakeZero
  rcases
      lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
          htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let noiseVariance : ℝ := (M.noiseVariance testFeature : ℝ)
  have hnoiseVariance : 0 < noiseVariance := by
    simpa [noiseVariance] using htestNoiseVariance
  have hbaseVarianceNN : baseVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance)
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  obtain ⟨gap, hroot⟩ :=
    lg21ReportRequiredHiddenAccessMixture_exists_uniform_raw_root
      baseMean hbaseMean baseVariance.toNNReal hbaseVarianceNN
      (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess haccess
      hnoAccessFinite haccessFinite noiseVariance hnoiseVariance
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hroot' : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance (threshold publicBase) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite threshold publicBase := by
    intro publicBase
    simpa [threshold, noiseVariance,
      Real.coe_toNNReal _ hbaseVariance.le] using hroot publicBase
  let candidate := lg21ReportRequiredHiddenAccessTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite
  have hcandidateTakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2) := by
    simpa [candidate, lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21HiddenAccessConditionalMeanTailTake_measurable
        testFeature threshold hthreshold)
  have hreportPositiveRaw : 0 < rawLaw
      (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision) := by
    simpa [rawLaw, candidate, lg21ReportRequiredTailReportEvent,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  have hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature Set.univ
      (lg21ReportRequiredTailReportEvent testFeature candidate.takeDecision) := by
    rw [lg21HiddenAccessLocalRawLaw_univ]
    simpa [rawLaw] using hreportPositiveRaw
  have hnoReportPositiveRaw : 0 < rawLaw
      (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision) := by
    simpa [rawLaw, candidate, lg21ReportRequiredTailNoReportEvent,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hnoAccess)
  have hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature Set.univ
      (lg21ReportRequiredTailNoReportEvent testFeature candidate.takeDecision) := by
    rw [lg21HiddenAccessLocalRawLaw_univ]
    simpa [rawLaw] using hnoReportPositiveRaw
  have hreportPBO : LG21ReportRequiredTailReportPBOOn M testFeature Set.univ
      hregionPositive candidate hreportPositive := by
    simpa [LG21ReportRequiredTailReportPBOOn, candidate,
      lg21ReportRequiredTailReportEvent,
      lg21ReportRequiredHiddenAccessTailCandidate,
      lg21HiddenAccessLocalRawLaw_univ, rawLaw] using
      (lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  have hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal :=
    lg21ReportRequiredBaseDependentTail_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
      hsourceFactor
  have hnoReportPBO : LG21ReportRequiredTailNoReportPBOOn M testFeature Set.univ
      hregionPositive candidate hnoReportPositive := by
    simpa [LG21ReportRequiredTailNoReportPBOOn, candidate,
      lg21ReportRequiredTailNoReportEvent,
      lg21ReportRequiredHiddenAccessTailCandidate,
      lg21HiddenAccessLocalRawLaw_univ, rawLaw, threshold] using
      (lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance.toNNReal hfullBaseFactor gap hnoAccessFinite haccessFinite)
  have hstrictGain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature Set.univ).restrict
        (lg21ReportRequiredTailChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredTailTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) := by
    rw [lg21HiddenAccessLocalRawLaw_univ]
    simpa [rawLaw, candidate, threshold,
      lg21ReportRequiredHiddenAccessTailCandidate] using
      (lg21ReportRequiredHiddenAccessTail_changedTaker_strictGain_ae_of_source
        currentTake hcurrentTake baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance gap
        hsourceFactor hroot')
  exact
    lg21ReportRequired_not_stable_of_zeroCurrentTakeRegion
      currentTake hcurrentTake Set.univ MeasurableSet.univ hregionPositive
      hlocalCurrentTakeZero candidate
      { candidate_test_law := by
          intro latentSkill publicBase
          simp [candidate, lg21ReportRequiredHiddenAccessTailCandidate,
            noiseVariance]
        candidate_take_measurable := hcandidateTakeMeasurable
        report_positive := hreportPositive
        noReport_positive := hnoReportPositive
        report_pbo := hreportPBO
        noReport_pbo := hnoReportPBO
        changed_taker_strict_gain := hstrictGain }

end

end LG21TestOptionalPolicies
