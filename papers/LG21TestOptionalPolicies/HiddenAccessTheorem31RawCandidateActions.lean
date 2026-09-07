import LG21TestOptionalPolicies.HiddenAccessTheorem31CandidatePBORefinement
import LG21TestOptionalPolicies.HiddenAccessTheorem31ComponentConditionalBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31NoReportMixtureBridge
import LG21TestOptionalPolicies.OptionalAllNoReporterGlobalSource

/-!
# Literal raw candidate actions for LG21 Theorem 3.1

The Section 3 protocol hides test access from the school.  Consequently a
candidate's public `X = 0` population is never an access-conditioned law: it
is the raw population event consisting of no-access students, access students
who do not take, and access students who take but do not report.  This file
states and proves that event identity before introducing any candidate PBO.

The final definition specializes to the source-timed candidate `Y(q, b) = 1`
exactly when `q` is at least the Gaussian conditional mean at public base
`b`, with `X = Y`.  It is an action profile permitted by `Z >= Y >= X`; it is
not a score-withholding convention and does not reveal the hidden `Z` bit to
the school.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-! ## General literal candidate action events -/

/-- The `Z = 1, Y = 0` component of a literal hidden-access candidate.
It is kept separate from `Z = 1, Y = 1, X = 0`, because these are distinct
source-timed actions. -/
def lg21HiddenAccessCandidateAccessNoTakeEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true /\
    lg21HiddenAccessStudentTake testFeature candidateTake student.2 = false}

/-- The `Z = 1, Y = 1, X = 0` component of a literal hidden-access
candidate.  It is distinct from a non-taker and remains a post-score action. -/
def lg21HiddenAccessCandidateAccessTakeNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true /\
    lg21HiddenAccessStudentTake testFeature candidateTake student.2 = true /\
    lg21HiddenAccessStudentReport testFeature candidateReport student.2 = false}

/-- The literal candidate `X = 1` event, parameterized by both source-timed
candidate actions. -/
def lg21HiddenAccessRawCandidateReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | lg21HiddenAccessOptionalObservedAction testFeature
    candidateTake candidateReport student = true}

/-- The literal candidate `X = 0` event, parameterized by both source-timed
candidate actions. -/
def lg21HiddenAccessRawCandidateNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | lg21HiddenAccessOptionalObservedAction testFeature
    candidateTake candidateReport student = false}

/-- Exact source-timed decomposition of a candidate's public no-report
population.  This is the key semantic guard: subsequent PBO calculations
must use the union on the right under the raw population law. -/
theorem lg21HiddenAccessRawCandidateNoReportEvent_eq_components
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake candidateReport =
    lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake ∪
          lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
            candidateTake candidateReport := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  cases access
  · simp [lg21HiddenAccessRawCandidateNoReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessNoAccessEvent,
      lg21HiddenAccessCandidateAccessNoTakeEvent,
      lg21HiddenAccessCandidateAccessTakeNoReportEvent,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport]
  · cases htake : candidateTake latentSkill
        (lg21HiddenAccessStudentBase testFeature (latentSkill, noise)) <;>
      simp [lg21HiddenAccessRawCandidateNoReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessNoAccessEvent,
        lg21HiddenAccessCandidateAccessNoTakeEvent,
        lg21HiddenAccessCandidateAccessTakeNoReportEvent,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport, htake]

/-- Positive no-access mass makes every literal candidate's public `X = 0`
branch positive before a candidate PBO is formed.  This uses the raw event
inclusion `Z = 0 ⊆ {X = 0}`, not a normalized access-only law. -/
theorem lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hnoAccess : 0 < M.accessLaw {false}) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        candidateTake candidateReport) := by
  have hnoAccessPositive :
      0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessNoAccessEvent (Feature := Feature)) := by
    rw [lg21HiddenAccessNoAccessEvent_eq_false_rectangle,
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa using hnoAccess
  apply lt_of_lt_of_le hnoAccessPositive
  apply measure_mono
  intro student hstudent
  rw [lg21HiddenAccessRawCandidateNoReportEvent_eq_components]
  exact Or.inl (Or.inl hstudent)

/-! ## Source-permitted latent-tail candidate -/

/-- The pre-score action `Y(q,b)`: take exactly on the upper latent-skill
tail relative to the source conditional mean at the public base. -/
def lg21HiddenAccessConditionalMeanTailTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool :=
  fun latentSkill publicBase => decide (baseMean publicBase <= latentSkill)

/-- The candidate's visible action sets `X = Y`; every candidate tester
reports the realized score. -/
def lg21HiddenAccessConditionalMeanTailReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    Bool × (ℝ × (Feature → ℝ)) → Bool :=
  lg21HiddenAccessOptionalObservedAction testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean)
    (fun _ _ => true)

/-- The candidate's literal public `X = 0` event. -/
def lg21HiddenAccessConditionalMeanTailNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | lg21HiddenAccessConditionalMeanTailReport testFeature baseMean student = false}

/-- The source-timed `Z = 1, Y = 0` component for the conditional-mean-tail
candidate. -/
def lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true /\
    student.2.1 < baseMean (lg21HiddenAccessStudentBase testFeature student.2)}

theorem lg21HiddenAccessConditionalMeanTailTake_eq_true_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (latentSkill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    lg21HiddenAccessConditionalMeanTailTake testFeature baseMean latentSkill publicBase = true ↔
      baseMean publicBase <= latentSkill := by
  simp [lg21HiddenAccessConditionalMeanTailTake]

theorem lg21HiddenAccessConditionalMeanTailTake_eq_false_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (latentSkill : ℝ) (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    lg21HiddenAccessConditionalMeanTailTake testFeature baseMean latentSkill publicBase = false ↔
      latentSkill < baseMean publicBase := by
  simp [lg21HiddenAccessConditionalMeanTailTake, not_le]

theorem lg21HiddenAccessConditionalMeanTailNoReportEvent_eq_noAccess_union_accessNoTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessConditionalMeanTailNoReportEvent testFeature baseMean =
    lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent testFeature baseMean := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  cases access <;> simp [lg21HiddenAccessConditionalMeanTailNoReportEvent,
    lg21HiddenAccessConditionalMeanTailReport,
    lg21HiddenAccessOptionalObservedAction,
    lg21HiddenAccessConditionalMeanTailTake,
    lg21HiddenAccessNoAccessEvent,
    lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent,
    lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport, not_le]

theorem lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent_eq_general
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent testFeature baseMean =
      lg21HiddenAccessCandidateAccessNoTakeEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean) := by
  ext student
  change (student.1 = true /\
      student.2.1 < baseMean (lg21HiddenAccessStudentBase testFeature student.2)) ↔
    (student.1 = true /\
      lg21HiddenAccessStudentTake testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean) student.2 = false)
  constructor
  · rintro ⟨haccess, htail⟩
    exact ⟨haccess,
      (lg21HiddenAccessConditionalMeanTailTake_eq_false_iff testFeature baseMean
        student.2.1 (lg21HiddenAccessStudentBase testFeature student.2)).2 htail⟩
  · rintro ⟨haccess, hnoTake⟩
    exact ⟨haccess,
      (lg21HiddenAccessConditionalMeanTailTake_eq_false_iff testFeature baseMean
        student.2.1 (lg21HiddenAccessStudentBase testFeature student.2)).1 hnoTake⟩

/-- The permitted candidate has no `Z = 1, Y = 1, X = 0` component because
it sets `X = Y`.  Its no-report population is therefore exactly `Z = 0` plus
the access students who choose not to take. -/
theorem lg21HiddenAccessConditionalMeanTailNoReportEvent_eq_raw_components
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessConditionalMeanTailNoReportEvent testFeature baseMean =
      lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessCandidateAccessNoTakeEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean) := by
  rw [lg21HiddenAccessConditionalMeanTailNoReportEvent_eq_noAccess_union_accessNoTake,
    lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent_eq_general]

/-- Measurability of the candidate's pre-score action. -/
theorem lg21HiddenAccessConditionalMeanTailTake_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) :
    Measurable (fun pair : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) =>
      lg21HiddenAccessConditionalMeanTailTake testFeature baseMean pair.1 pair.2) := by
  apply measurable_to_bool
  change MeasurableSet {pair : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) |
    decide (baseMean pair.2 <= pair.1) = true}
  have hset : {pair : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) |
      decide (baseMean pair.2 <= pair.1) = true} =
      (fun pair : ℝ × (LG21NonTestFeature Feature testFeature → ℝ) =>
        pair.1 - baseMean pair.2) ⁻¹' Set.Ici 0 := by
    ext pair
    simp
  rw [hset]
  exact measurableSet_Ici.preimage
    (measurable_fst.sub (hbaseMean.comp measurable_snd))

/-- Measurability of the candidate's literal observed action. -/
theorem lg21HiddenAccessConditionalMeanTailReport_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) :
    Measurable (lg21HiddenAccessConditionalMeanTailReport testFeature baseMean) := by
  apply lg21HiddenAccessOptionalObservedAction_measurable
  · exact lg21HiddenAccessConditionalMeanTailTake_measurable testFeature
      baseMean hbaseMean
  · exact measurable_const

/-! ## Raw source-law transport -/

/-- Forgetting the hidden access bit gives the same full `(base, score,
skill)` law before and after conditioning on positive access.  This is a
product-law fact about the source, not a statement about a candidate action
population. -/
theorem lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let primitiveObservation : ℝ × (Feature → ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × (ℝ × ℝ) :=
    fun primitive =>
      (lg21HiddenAccessStudentBase testFeature primitive,
        (lg21HiddenAccessStudentScore testFeature primitive, primitive.1))
  have hprimitiveObservation : Measurable primitiveObservation := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).prodMk
      ((lg21HiddenAccessStudentScore_measurable testFeature).prodMk measurable_fst)
  letI : IsProbabilityMeasure primitiveLaw := by
    dsimp [primitiveLaw, lg21ContinuousGaussianStudentPrimitiveLaw,
      lg21ContinuousGaussianNoiseLaw]
    infer_instance
  have hrawStudent : rawLaw.map Prod.snd = primitiveLaw := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    rw [show rawLaw = M.accessLaw.prod primitiveLaw by rfl,
      Measure.map_snd_prod, IsProbabilityMeasure.measure_univ, one_smul]
  have haccessStudent : accessLaw.map Prod.snd = primitiveLaw := by
    simpa [accessLaw, primitiveLaw] using
      (lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess)
  calc
    rawLaw.map (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        (rawLaw.map Prod.snd).map primitiveObservation := by
          rw [Measure.map_map hprimitiveObservation measurable_snd]
          rfl
    _ = primitiveLaw.map primitiveObservation := by rw [hrawStudent]
    _ = (accessLaw.map Prod.snd).map primitiveObservation := by rw [haccessStudent]
    _ = accessLaw.map (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
          rw [Measure.map_map hprimitiveObservation measurable_snd]
          rfl

/-- The literal raw hidden-access source therefore has the same exact
full-base Gaussian score/skill factorization as its access-conditioned
counterpart.  The equality is written for the raw population so later
candidate branch PBOs cannot silently discard `Z = 0` mass. -/
theorem lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
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
        (lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hfactor⟩
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  calc
    (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) :=
      lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw M haccess testFeature
    _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
      simpa [lg21HiddenAccessBaseScoreSkillObservation,
        lg21HiddenAccessStudentBase, lg21HiddenAccessStudentScore,
        lg21ContinuousPopulationBase, lg21ContinuousPopulationFeature,
        lg21ContinuousPopulationSkill, lg21ContinuousPopulationNoise] using hfactor

/-! ## Exact raw candidate no-report law -/

/-- The candidate's normalized `(base, skill)` law on its literal `X = 0`
population.  This is intentionally a raw-population law. -/
def lg21HiddenAccessRawCandidateNoReportBaseSkillLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    (lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake candidateReport)).map
      (lg21HiddenAccessBaseSkillObservation testFeature)

/-- The unnormalized `(base, skill)` component arising from access students
who choose `Y = 0` under a candidate. -/
def lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  ((lg21ContinuousGaussianPopulationLaw M).restrict
    (lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake)).map
      (lg21HiddenAccessBaseSkillObservation testFeature)

/-- The unnormalized `(base, skill)` component arising from access students
who choose `Y = 1` and then `X = 0` under a candidate. -/
def lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  ((lg21ContinuousGaussianPopulationLaw M).restrict
    (lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
      candidateTake candidateReport)).map
      (lg21HiddenAccessBaseSkillObservation testFeature)

theorem lg21HiddenAccessCandidateAccessNoTakeEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      candidateTake pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake) := by
  have htake : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentTake testFeature candidateTake student.2) :=
    (lg21HiddenAccessStudentTake_measurable testFeature candidateTake hcandidateTake).comp
      measurable_snd
  change MeasurableSet
    ({student : Bool × (ℝ × (Feature → ℝ)) | student.1 = true} ∩
      {student : Bool × (ℝ × (Feature → ℝ)) |
        lg21HiddenAccessStudentTake testFeature candidateTake student.2 = false})
  exact ((measurableSet_singleton true).preimage measurable_fst).inter
    ((measurableSet_singleton false).preimage htake)

theorem lg21HiddenAccessCandidateAccessTakeNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
        candidateTake candidateReport) := by
  have htake : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentTake testFeature candidateTake student.2) :=
    (lg21HiddenAccessStudentTake_measurable testFeature candidateTake hcandidateTake).comp
      measurable_snd
  have hreport : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentReport testFeature candidateReport student.2) :=
    (lg21HiddenAccessStudentReport_measurable testFeature candidateReport
      hcandidateReport).comp measurable_snd
  change MeasurableSet {student : Bool × (ℝ × (Feature → ℝ)) |
    student.1 = true ∧
      lg21HiddenAccessStudentTake testFeature candidateTake student.2 = true ∧
        lg21HiddenAccessStudentReport testFeature candidateReport student.2 = false}
  exact ((measurableSet_singleton true).preimage measurable_fst).inter
    (((measurableSet_singleton true).preimage htake).inter
      ((measurableSet_singleton false).preimage hreport))

/-- Exact normalized mixture for any literal source-timed candidate.  It
has three components because `Y = 0` and `Y = 1, X = 0` are different source
actions.  In particular, this theorem prevents later code from replacing the
raw public `X = 0` branch by an access-conditioned selected law. -/
theorem lg21HiddenAccessRawCandidate_noReportBaseSkillLaw_eq_normalized_components
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (candidateTake : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        candidateTake candidateReport =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          candidateTake candidateReport))⁻¹ •
        (lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature +
          lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure M testFeature
            candidateTake +
          lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure M testFeature
            candidateTake candidateReport) := by
  let law := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let accessNoTake := lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake
  let accessTakeNoReport := lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
    candidateTake candidateReport
  let observation := lg21HiddenAccessBaseSkillObservation testFeature
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseSkillObservation_measurable (Feature := Feature) testFeature)
  have hnoAccessMeasurable : MeasurableSet noAccess := by
    change MeasurableSet {student : Bool × (ℝ × (Feature → ℝ)) | student.1 = false}
    exact (measurableSet_singleton false).preimage measurable_fst
  have haccessNoTakeMeasurable : MeasurableSet accessNoTake := by
    simpa [accessNoTake] using
      (lg21HiddenAccessCandidateAccessNoTakeEvent_measurable testFeature
        candidateTake hcandidateTake)
  have haccessTakeNoReportMeasurable : MeasurableSet accessTakeNoReport := by
    simpa [accessTakeNoReport] using
      (lg21HiddenAccessCandidateAccessTakeNoReportEvent_measurable testFeature
        candidateTake candidateReport hcandidateTake hcandidateReport)
  have hdisjointNoAccessNoTake : Disjoint noAccess accessNoTake := by
    apply Set.disjoint_left.2
    rintro ⟨access, primitive⟩ hnoAccess haccessNoTake
    change access = false at hnoAccess
    change access = true ∧ _ at haccessNoTake
    simp_all
  have hdisjointNoAccessOrNoTakeTakeNoReport :
      Disjoint (noAccess ∪ accessNoTake) accessTakeNoReport := by
    apply Set.disjoint_left.2
    rintro ⟨access, primitive⟩ (hnoAccess | haccessNoTake) haccessTakeNoReport
    · change access = false at hnoAccess
      change access = true ∧ _ at haccessTakeNoReport
      simp_all
    · change access = true ∧ _ at haccessNoTake
      change access = true ∧ _ ∧ _ at haccessTakeNoReport
      rcases haccessNoTake with ⟨_, hnoTake⟩
      rcases haccessTakeNoReport with ⟨_, htake, _⟩
      simp_all
  have hcomponents : law.restrict noReport =
      (law.restrict noAccess + law.restrict accessNoTake) +
        law.restrict accessTakeNoReport := by
    have hnoAccessNoTake : law.restrict (noAccess ∪ accessNoTake) =
        law.restrict noAccess + law.restrict accessNoTake :=
      Measure.restrict_union hdisjointNoAccessNoTake haccessNoTakeMeasurable
    have hunion : noReport = (noAccess ∪ accessNoTake) ∪ accessTakeNoReport := by
      simpa [noReport, noAccess, accessNoTake, accessTakeNoReport] using
        (lg21HiddenAccessRawCandidateNoReportEvent_eq_components testFeature
          candidateTake candidateReport)
    rw [hunion, Measure.restrict_union
      hdisjointNoAccessOrNoTakeTakeNoReport haccessTakeNoReportMeasurable,
      hnoAccessNoTake]
  change Measure.map observation (lg21NormalizedRestriction law noReport) =
    (law noReport)⁻¹ •
      (Measure.map observation (law.restrict noAccess) +
        Measure.map observation (law.restrict accessNoTake) +
        Measure.map observation (law.restrict accessTakeNoReport))
  unfold lg21NormalizedRestriction
  rw [Measure.map_smul, hcomponents]
  rw [Measure.map_add _ _ hobservation]
  rw [Measure.map_add _ _ hobservation]

/-- The conditional-mean-tail candidate has no post-score withholding
component: every candidate taker reports. -/
theorem lg21HiddenAccessConditionalMeanTail_accessTakeNoReportEvent_eq_empty
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ) :
    lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean)
      (fun _ _ => true) = ∅ := by
  ext student
  simp [lg21HiddenAccessCandidateAccessTakeNoReportEvent,
    lg21HiddenAccessStudentReport]

/-! ## No-access component under the raw source law -/

/-- The unnormalized raw no-access component is exactly its literal access
mass times the full base/skill source law.  This is the component that stays
inside the candidate's public `X = 0` PBO when the school does not observe
access. -/
theorem lg21HiddenAccessNoAccessBaseSkillMeasure_eq_smul_fullBaseLatent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
    lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature =
      M.accessLaw {false} •
        lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let noAccessLaw := lg21HiddenAccessNoAccessLaw M
  let observation := lg21HiddenAccessBaseSkillObservation testFeature
  let component := lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature
  let fullBaseLatent := lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature
  let accessMass := M.accessLaw {false}
  have hrawProbability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hrawProbability
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  have haccessMass_ne_zero : accessMass ≠ 0 := by
    exact ne_of_gt hnoAccess
  have haccessMass_ne_top : accessMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hrawNoAccessMass : rawLaw noAccess = accessMass := by
    rw [show noAccess = ({false} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [noAccess, lg21HiddenAccessNoAccessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa [accessMass]
  have hnormalizedMap : fullBaseLatent = accessMass⁻¹ • component := by
    calc
      fullBaseLatent = noAccessLaw.map observation := by
        simpa [noAccessLaw, observation, fullBaseLatent] using
          (lg21HiddenAccessNoAccessLaw_base_skill_law M hnoAccess testFeature).symm
      _ = (accessMass⁻¹ • rawLaw.restrict noAccess).map observation := by
        congr 1
        unfold noAccessLaw lg21HiddenAccessNoAccessLaw lg21NormalizedRestriction
        rw [hrawNoAccessMass]
      _ = accessMass⁻¹ • component := by
        rw [Measure.map_smul]
        rfl
  calc
    component = (1 : ENNReal) • component := by simp
    _ = (accessMass * accessMass⁻¹) • component := by
      rw [ENNReal.mul_inv_cancel haccessMass_ne_zero haccessMass_ne_top]
    _ = accessMass • (accessMass⁻¹ • component) := by
      rw [smul_smul]
    _ = accessMass • fullBaseLatent := by rw [← hnormalizedMap]

/-! ## Access non-taker component under the raw source law -/

/-- Conditioning the literal positive-access source on access and then
forgetting the access coordinate leaves exactly the same full base/skill law
as the no-access component.  This is a source-product calculation, not a
candidate-belief identification. -/
theorem lg21ContinuousGaussianAccessPopulation_base_skill_law
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21HiddenAccessBaseSkillObservation testFeature) =
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
  let fullPrimitive := lg21ContinuousPopulationFullPrimitive testFeature
  let fullBaseSkill :=
    lg21HiddenAccessFullPrimitiveBaseSkillObservation testFeature
  have hfullPrimitive : Measurable fullPrimitive := by
    exact (measurable_fst.comp measurable_snd).prodMk
      ((measurable_pi_lambda _ fun feature =>
        (measurable_pi_apply feature.1).comp (measurable_snd.comp measurable_snd)).prodMk
          ((measurable_pi_apply testFeature).comp
            (measurable_snd.comp measurable_snd)))
  have hfullBaseSkill : Measurable fullBaseSkill := by
    exact lg21HiddenAccessFullPrimitiveBaseSkillObservation_measurable testFeature
  calc
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (lg21HiddenAccessBaseSkillObservation testFeature) =
      ((lg21ContinuousGaussianAccessPopulationLaw M).map fullPrimitive).map
        fullBaseSkill := by
          rw [Measure.map_map hfullBaseSkill hfullPrimitive]
          rfl
    _ = (lg21ContinuousGaussianFullProfilePrimitiveLaw M testFeature).map
        fullBaseSkill := by
          rw [lg21ContinuousGaussianAccessPopulation_full_primitive_law
            M haccess testFeature]
    _ = lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
          exact lg21ContinuousGaussianFullProfilePrimitiveLaw_map_base_skill_eq
            M testFeature

/-- The lower latent-skill event of a base-dependent tail candidate, stated
on the public-base/skill carrier that is used for the raw `X = 0` PBO. -/
def lg21HiddenAccessBaseSkillLowerTailEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set (Base × ℝ) :=
  {baseSkill | baseSkill.2 < threshold baseSkill.1}

theorem lg21HiddenAccessBaseSkillLowerTailEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21HiddenAccessBaseSkillLowerTailEvent threshold) := by
  exact measurableSet_lt measurable_snd (hthreshold.comp measurable_fst)

/-- The literal access non-taker event of the tail candidate is exactly the
positive-access preimage of its lower base/skill tail. -/
theorem lg21HiddenAccessConditionalMeanTail_accessNoTakeEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent testFeature baseMean =
      {student | student.1 = true} ∩
        (lg21HiddenAccessBaseSkillObservation testFeature) ⁻¹'
          lg21HiddenAccessBaseSkillLowerTailEvent baseMean := by
  ext student
  change (student.1 = true /\
      student.2.1 < baseMean
        (lg21HiddenAccessStudentBase testFeature student.2)) ↔
    (student.1 = true /\
      (lg21HiddenAccessStudentBase testFeature student.2, student.2.1) ∈
        lg21HiddenAccessBaseSkillLowerTailEvent baseMean)
  rfl

/-- The raw access non-taker component of a latent-tail candidate is the
literal positive-access source mass times the full base/skill law restricted
to that candidate's lower tail.  This keeps the `Z = 0` population separate;
the two components are only combined in the subsequent public `X = 0` law. -/
theorem lg21HiddenAccessConditionalMeanTail_accessNoTakeBaseSkillMeasure_eq_smul_restrict
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) :
    lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure M testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean) =
      M.accessLaw {true} •
        (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
          (lg21HiddenAccessBaseSkillLowerTailEvent baseMean) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let observation := lg21HiddenAccessBaseSkillObservation testFeature
  let lowerTail := lg21HiddenAccessBaseSkillLowerTailEvent baseMean
  let accessMass := M.accessLaw {true}
  have hrawProbability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hrawProbability
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hlowerTail : MeasurableSet lowerTail := by
    simpa [lowerTail] using
      (lg21HiddenAccessBaseSkillLowerTailEvent_measurable baseMean hbaseMean)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseSkillObservation_measurable (Feature := Feature) testFeature)
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
  have hrawTailRestrict :
      rawLaw.restrict (accessEvent ∩ observation ⁻¹' lowerTail) =
        accessMass • (accessLaw.restrict (observation ⁻¹' lowerTail)) := by
    calc
      rawLaw.restrict (accessEvent ∩ observation ⁻¹' lowerTail) =
          (rawLaw.restrict accessEvent).restrict (observation ⁻¹' lowerTail) := by
            rw [Measure.restrict_restrict]
            · rw [Set.inter_comm]
            · exact hlowerTail.preimage hobservation
      _ = (accessMass • accessLaw).restrict (observation ⁻¹' lowerTail) := by
            rw [hrawAccessRestrict]
      _ = accessMass • (accessLaw.restrict (observation ⁻¹' lowerTail)) := by
            rw [Measure.restrict_smul]
  have haccessMapRestrict :
      (accessLaw.restrict (observation ⁻¹' lowerTail)).map observation =
        (accessLaw.map observation).restrict lowerTail := by
    rw [← Measure.restrict_map hobservation hlowerTail]
  have haccessBaseSkill : accessLaw.map observation =
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
    simpa [accessLaw, observation] using
      (lg21ContinuousGaussianAccessPopulation_base_skill_law M haccess testFeature)
  change (rawLaw.restrict
      (lg21HiddenAccessCandidateAccessNoTakeEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean))).map observation = _
  rw [← lg21HiddenAccessConditionalMeanTailAccessNoTakeEvent_eq_general,
    lg21HiddenAccessConditionalMeanTail_accessNoTakeEvent_eq_access_inter_preimage]
  calc
    (rawLaw.restrict (accessEvent ∩ observation ⁻¹' lowerTail)).map observation =
        (accessMass • (accessLaw.restrict (observation ⁻¹' lowerTail))).map
          observation := by rw [hrawTailRestrict]
    _ = accessMass •
        ((accessLaw.restrict (observation ⁻¹' lowerTail)).map observation) := by
          rw [Measure.map_smul]
    _ = accessMass • ((accessLaw.map observation).restrict lowerTail) := by
          rw [haccessMapRestrict]
    _ = accessMass •
        (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
          lowerTail := by rw [haccessBaseSkill]

/-- Exact raw `(base, skill)` law of the positive-gap tail candidate's public
`X = 0` branch.  The normalized law contains both the whole no-access source
law and the access lower-tail restriction.  In particular it is not an
access-conditioned candidate population. -/
theorem lg21HiddenAccessConditionalMeanTail_noReportBaseSkillLaw_eq_normalized_raw_mixture
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) :
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean)
      (fun _ _ => true) =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean)
          (fun _ _ => true)))⁻¹ •
        (M.accessLaw {false} •
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature +
        M.accessLaw {true} •
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
            (lg21HiddenAccessBaseSkillLowerTailEvent baseMean)) := by
  have htakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessConditionalMeanTailTake testFeature baseMean pair.1 pair.2) := by
    exact lg21HiddenAccessConditionalMeanTailTake_measurable testFeature
      baseMean hbaseMean
  have hreportMeasurable : Measurable (fun _pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => true) :=
    measurable_const
  rw [lg21HiddenAccessRawCandidate_noReportBaseSkillLaw_eq_normalized_components
    M testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature baseMean)
    (fun _ _ => true) htakeMeasurable hreportMeasurable,
    lg21HiddenAccessNoAccessBaseSkillMeasure_eq_smul_fullBaseLatent
      M hnoAccess testFeature,
    lg21HiddenAccessConditionalMeanTail_accessNoTakeBaseSkillMeasure_eq_smul_restrict
      M haccess testFeature baseMean hbaseMean]
  simp only [lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure,
    lg21HiddenAccessConditionalMeanTail_accessTakeNoReportEvent_eq_empty,
    Measure.restrict_empty, Measure.map_zero, add_zero]

/-! ## Base-conditioned raw-tail mixture kernel -/

/-- The unnormalized latent-skill fibre induced by an unobserved access draw
and a lower-tail taking action.  Its density is the literal sum of the
no-access component and the positive-access lower-tail component. -/
def lg21HiddenAccessTailRawKernel
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ) : Kernel Base ℝ :=
  κ.withDensity fun publicBase latentSkill =>
    noAccessMass + accessMass *
      (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1
        (publicBase, latentSkill)

/-- The total mass of the preceding unnormalized fibre. -/
def lg21HiddenAccessTailRawFibreMass
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) (noAccessMass accessMass : ENNReal)
    (threshold : Base -> ℝ) (publicBase : Base) : ENNReal :=
  noAccessMass + accessMass * κ publicBase (Set.Iio (threshold publicBase))

theorem lg21HiddenAccessTailRawKernel_density_measurable
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) :
    Measurable (Function.uncurry (fun publicBase latentSkill =>
      noAccessMass + accessMass *
        (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1
          (publicBase, latentSkill))) := by
  change Measurable fun baseSkill : Base × ℝ =>
    noAccessMass + accessMass *
      (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1 baseSkill
  exact measurable_const.add
    (measurable_const.mul (measurable_one.indicator
      (lg21HiddenAccessBaseSkillLowerTailEvent_measurable threshold hthreshold)))

/-- Every raw mixture fibre is exactly the sum of the whole no-access law and
the lower-tail access restriction. -/
theorem lg21HiddenAccessTailRawKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) (publicBase : Base) :
    lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold publicBase =
      noAccessMass • κ publicBase +
        accessMass • (κ publicBase).restrict (Set.Iio (threshold publicBase)) := by
  let lowerTail : Set ℝ := Set.Iio (threshold publicBase)
  have hlowerTail : MeasurableSet lowerTail := measurableSet_Iio
  have hdensity := lg21HiddenAccessTailRawKernel_density_measurable
    κ noAccessMass accessMass threshold hthreshold
  rw [lg21HiddenAccessTailRawKernel, Kernel.withDensity_apply _ hdensity]
  change (κ publicBase).withDensity (fun latentSkill =>
      noAccessMass + accessMass *
        (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1
          (publicBase, latentSkill)) = _
  have hdensityAt : (fun latentSkill : ℝ =>
      noAccessMass + accessMass *
        (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1
          (publicBase, latentSkill)) =
      (fun _ : ℝ => noAccessMass) +
        accessMass • lowerTail.indicator 1 := by
    funext latentSkill
    by_cases htail : latentSkill < threshold publicBase <;>
      simp [lowerTail, lg21HiddenAccessBaseSkillLowerTailEvent, htail,
        Pi.smul_apply, smul_eq_mul]
  rw [hdensityAt, withDensity_add_left measurable_const,
    withDensity_const, withDensity_smul accessMass
      (measurable_one.indicator hlowerTail),
    withDensity_indicator_one hlowerTail]

/-- The raw-fibre total is the displayed no-access mass plus the selected
access lower-tail mass. -/
theorem lg21HiddenAccessTailRawKernel_apply_univ
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) (publicBase : Base) :
    lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold publicBase
      Set.univ =
      lg21HiddenAccessTailRawFibreMass κ noAccessMass accessMass threshold publicBase := by
  rw [lg21HiddenAccessTailRawKernel_apply κ noAccessMass accessMass threshold
    hthreshold publicBase]
  simp [lg21HiddenAccessTailRawFibreMass]

/-- Finite source weights make the raw-tail mixture a finite kernel. -/
theorem lg21HiddenAccessTailRawKernel_isFinite
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) :
    IsFiniteKernel
      (lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold) := by
  apply Kernel.isFiniteKernel_withDensity_of_bounded κ
    (ENNReal.add_ne_top.mpr ⟨hnoAccessFinite, haccessFinite⟩)
  intro publicBase latentSkill
  change noAccessMass + accessMass *
      (lg21HiddenAccessBaseSkillLowerTailEvent threshold).indicator 1
        (publicBase, latentSkill) ≤ noAccessMass + accessMass
  gcongr
  by_cases htail : (publicBase, latentSkill) ∈
      lg21HiddenAccessBaseSkillLowerTailEvent threshold <;>
    simp [Set.indicator, htail]

/-- The raw source mixture factorizes through the unnormalized tail kernel.
This is an equality of measures, before the public base marginal is
renormalized and before any conditional distribution is invoked. -/
theorem lg21HiddenAccessTailRawKernel_compProd_eq_raw_mixture
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    baseLaw ⊗ₘ lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold =
      noAccessMass • (baseLaw ⊗ₘ κ) +
        accessMass • (baseLaw ⊗ₘ κ).restrict
          (lg21HiddenAccessBaseSkillLowerTailEvent threshold) := by
  let rawKernel :=
    lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold
  let tailEvent := lg21HiddenAccessBaseSkillLowerTailEvent threshold
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21HiddenAccessBaseSkillLowerTailEvent_measurable threshold hthreshold)
  have hdensity := lg21HiddenAccessTailRawKernel_density_measurable
    κ noAccessMass accessMass threshold hthreshold
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessTailRawKernel_isFinite κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold)
  letI : IsSFiniteKernel
      (κ.withDensity (fun publicBase latentSkill =>
        noAccessMass + accessMass * tailEvent.indicator 1
          (publicBase, latentSkill))) := by
    simpa [rawKernel] using
      (inferInstance : IsSFiniteKernel rawKernel)
  have hdensityLift : (fun pair : Base × ℝ =>
      noAccessMass + accessMass * tailEvent.indicator 1 pair) =
      (fun _ : Base × ℝ => noAccessMass) + accessMass • tailEvent.indicator 1 := by
    funext pair
    rfl
  change baseLaw ⊗ₘ rawKernel = _
  rw [show rawKernel =
      κ.withDensity (fun publicBase latentSkill =>
        noAccessMass + accessMass * tailEvent.indicator 1
          (publicBase, latentSkill)) by rfl,
    Measure.compProd_withDensity]
  · rw [hdensityLift, withDensity_add_left measurable_const,
      withDensity_const, withDensity_smul accessMass
        (measurable_one.indicator htailEvent),
      withDensity_indicator_one htailEvent]
  · simpa [tailEvent] using hdensity

/-- The literal lower-tail mass is measurable as a function of the public
base, hence so is the raw hidden-access fibre mass. -/
theorem lg21HiddenAccessTailRawFibreMass_measurable
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) :
    Measurable (lg21HiddenAccessTailRawFibreMass
      κ noAccessMass accessMass threshold) := by
  let tailEvent := lg21HiddenAccessBaseSkillLowerTailEvent threshold
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21HiddenAccessBaseSkillLowerTailEvent_measurable threshold hthreshold)
  have hselection : Measurable (fun publicBase : Base =>
      κ publicBase (Prod.mk publicBase ⁻¹' tailEvent)) :=
    Kernel.measurable_kernel_prodMk_left htailEvent
  change Measurable (fun publicBase : Base =>
    noAccessMass + accessMass * κ publicBase
      (Set.Iio (threshold publicBase)))
  convert measurable_const.add (measurable_const.mul hselection) using 1

/-- Positive no-access mass makes every raw mixture fibre positive, including
at bases where the access lower tail is arbitrarily small. -/
theorem lg21HiddenAccessTailRawFibreMass_pos_of_noAccess
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ)
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hnoAccess : 0 < noAccessMass) (publicBase : Base) :
    0 < lg21HiddenAccessTailRawFibreMass
      κ noAccessMass accessMass threshold publicBase := by
  unfold lg21HiddenAccessTailRawFibreMass
  exact lt_of_lt_of_le hnoAccess (le_add_of_nonneg_right bot_le)

/-- Every raw mixture fibre has finite total mass when the two literal access
weights are finite. -/
theorem lg21HiddenAccessTailRawFibreMass_ne_top
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (publicBase : Base) :
    lg21HiddenAccessTailRawFibreMass
      κ noAccessMass accessMass threshold publicBase ≠ ⊤ := by
  unfold lg21HiddenAccessTailRawFibreMass
  apply ENNReal.add_ne_top.mpr
  refine ⟨hnoAccessFinite, ENNReal.mul_ne_top haccessFinite ?_⟩
  exact measure_ne_top _ _

/-- The base-dependent probability kernel used by the candidate's raw
no-report PBO.  It is the literal raw-tail fibre divided by its own total
mass; no zero-fibre value is selected because positive no-access mass proves
every denominator nonzero below. -/
noncomputable def lg21HiddenAccessTailNormalizedKernel
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) : Kernel Base ℝ :=
  letI : IsFiniteKernel
      (lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold) :=
    lg21HiddenAccessTailRawKernel_isFinite κ noAccessMass accessMass
      hnoAccessFinite haccessFinite threshold
  (lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold).withDensity
    (fun publicBase _ =>
      (lg21HiddenAccessTailRawFibreMass
        κ noAccessMass accessMass threshold publicBase)⁻¹)

theorem lg21HiddenAccessTailNormalizedKernel_density_measurable
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold) :
    Measurable (Function.uncurry (fun (publicBase : Base) (_ : ℝ) =>
      (lg21HiddenAccessTailRawFibreMass
        κ noAccessMass accessMass threshold publicBase)⁻¹)) := by
  change Measurable fun baseSkill : Base × ℝ =>
    (lg21HiddenAccessTailRawFibreMass
      κ noAccessMass accessMass threshold baseSkill.1)⁻¹
  exact (lg21HiddenAccessTailRawFibreMass_measurable
    κ noAccessMass accessMass threshold hthreshold).inv.comp measurable_fst

/-- Pointwise form of the candidate PBO fibre before evaluating its mean. -/
theorem lg21HiddenAccessTailNormalizedKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold)
    (publicBase : Base) :
    lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
      hnoAccessFinite haccessFinite threshold publicBase =
      (lg21HiddenAccessTailRawFibreMass
        κ noAccessMass accessMass threshold publicBase)⁻¹ •
        lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold publicBase := by
  let rawKernel :=
    lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessTailRawKernel_isFinite κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold)
  have hdensity := lg21HiddenAccessTailNormalizedKernel_density_measurable
    κ noAccessMass accessMass threshold hthreshold
  unfold lg21HiddenAccessTailNormalizedKernel
  rw [Kernel.withDensity_apply _ hdensity, withDensity_const]

/-- The normalized literal raw-tail kernel is Markov on every base because
the no-access component gives every fibre strictly positive finite mass. -/
theorem lg21HiddenAccessTailNormalizedKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    IsMarkovKernel
      (lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold) := by
  constructor
  intro publicBase
  apply IsProbabilityMeasure.mk
  rw [lg21HiddenAccessTailNormalizedKernel_apply
    κ noAccessMass accessMass hnoAccessFinite haccessFinite threshold
    hthreshold publicBase,
    Measure.smul_apply,
    lg21HiddenAccessTailRawKernel_apply_univ κ noAccessMass accessMass
      threshold hthreshold publicBase]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt (lg21HiddenAccessTailRawFibreMass_pos_of_noAccess
      κ noAccessMass accessMass threshold hnoAccess publicBase))
    (lg21HiddenAccessTailRawFibreMass_ne_top κ noAccessMass accessMass
      hnoAccessFinite haccessFinite threshold publicBase)

/-- Reweighting the public-base law by the literal raw fibre mass and then
using the normalized raw fibre recovers the unnormalized hidden-access
candidate law exactly.  This is the factorization used to identify the
candidate PBO with a regular conditional distribution. -/
theorem lg21HiddenAccessTailWeightedBase_compProd_normalizedKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    (baseLaw.withDensity (lg21HiddenAccessTailRawFibreMass
      κ noAccessMass accessMass threshold)) ⊗ₘ
        lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
          hnoAccessFinite haccessFinite threshold =
      baseLaw ⊗ₘ
        lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold := by
  let rawKernel :=
    lg21HiddenAccessTailRawKernel κ noAccessMass accessMass threshold
  let fibreMass := lg21HiddenAccessTailRawFibreMass
    κ noAccessMass accessMass threshold
  let normalizedKernel :=
    lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
      hnoAccessFinite haccessFinite threshold
  let massLift : Base × ℝ -> ENNReal := fun baseSkill => fibreMass baseSkill.1
  let invMassLift : Base × ℝ -> ENNReal := fun baseSkill =>
    (fibreMass baseSkill.1)⁻¹
  have hfibreMassMeasurable : Measurable fibreMass := by
    simpa [fibreMass] using
      (lg21HiddenAccessTailRawFibreMass_measurable
        κ noAccessMass accessMass threshold hthreshold)
  have hmassLift : Measurable massLift :=
    hfibreMassMeasurable.comp measurable_fst
  have hinvMassLift : Measurable invMassLift :=
    hfibreMassMeasurable.inv.comp measurable_fst
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessTailRawKernel_isFinite κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel] using
      (lg21HiddenAccessTailNormalizedKernel_isMarkov
        κ noAccessMass accessMass hnoAccess hnoAccessFinite haccessFinite
        threshold hthreshold)
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
        hfibreMassMeasurable)
  have hcancel : massLift * invMassLift = 1 := by
    funext baseSkill
    change fibreMass baseSkill.1 * (fibreMass baseSkill.1)⁻¹ = 1
    exact ENNReal.mul_inv_cancel
      (ne_of_gt (lg21HiddenAccessTailRawFibreMass_pos_of_noAccess
        κ noAccessMass accessMass threshold hnoAccess baseSkill.1))
      (lg21HiddenAccessTailRawFibreMass_ne_top κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold baseSkill.1)
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

/-- Multiplying a normalized restriction back by its positive finite event
mass recovers the literal restricted measure. -/
theorem lg21_smul_normalizedRestriction_eq_restrict
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsFiniteMeasure law]
    (event : Set Outcome)
    (heventPositive : 0 < law event) :
    law event • lg21NormalizedRestriction law event = law.restrict event := by
  have hevent_ne_zero : law event ≠ 0 := ne_of_gt heventPositive
  have hevent_ne_top : law event ≠ ⊤ := measure_ne_top _ _
  unfold lg21NormalizedRestriction
  rw [smul_smul, ENNReal.mul_inv_cancel hevent_ne_zero hevent_ne_top, one_smul]

/-! ## Fibrewise Gaussian candidate inequalities -/

/-- The conditional mean of the full base/skill Gaussian source fibre is the
displayed base mean. -/
theorem lg21_gaussianLocationKernel_skill_mean
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (publicBase : Base) :
    (∫ latentSkill, latentSkill ∂
      gaussianLocationKernel baseMean hbaseMean baseVariance publicBase) =
      baseMean publicBase := by
  rw [gaussianLocationKernel_apply]
  exact integral_id_gaussianReal

/-- The latent-skill coordinate is integrable under every full Gaussian
base fibre. -/
theorem lg21_gaussianLocationKernel_skill_integrable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (publicBase : Base) :
    Integrable (fun latentSkill : ℝ => latentSkill)
      (gaussianLocationKernel baseMean hbaseMean baseVariance publicBase) := by
  rw [gaussianLocationKernel_apply]
  exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl

/-- The conditional mean on the lower latent tail of a nondegenerate source
fibre is strictly below its threshold.  This is a literal normalized
restriction, not a chosen value for an off-path PBO. -/
theorem lg21_gaussianLocationKernel_lowerTail_mean_lt_threshold
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (publicBase : Base) (threshold : ℝ) :
    (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction
        (gaussianLocationKernel baseMean hbaseMean baseVariance publicBase)
        (Set.Iio threshold)) < threshold := by
  let fibre := gaussianLocationKernel baseMean hbaseMean baseVariance publicBase
  have hfibre : fibre = gaussianReal (baseMean publicBase) baseVariance := by
    exact gaussianLocationKernel_apply baseMean hbaseMean baseVariance publicBase
  letI : IsFiniteMeasure fibre := by
    rw [hfibre]
    infer_instance
  have hpositive : 0 < fibre (Set.Iio threshold) := by
    rw [hfibre]
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase) threshold hbaseVariance
  have hintegrableRaw : Integrable (fun latentSkill : ℝ => latentSkill) fibre := by
    rw [hfibre]
    exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
  have hintegrable : Integrable (fun latentSkill : ℝ => latentSkill)
      (lg21NormalizedRestriction fibre (Set.Iio threshold)) := by
    unfold lg21NormalizedRestriction
    exact hintegrableRaw.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hpositive))
  exact lg21NormalizedRestriction_mean_lt_upper fibre (Set.Iio threshold)
    (fun latentSkill : ℝ => latentSkill) threshold measurableSet_Iio hpositive
    hintegrable (by
      intro latentSkill hlatentSkill
      exact hlatentSkill)

/-- The latent-skill coordinate remains integrable after normalizing a
positive Gaussian lower tail. -/
theorem lg21_gaussianLocationKernel_lowerTail_integrable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (publicBase : Base) (threshold : ℝ) :
    Integrable (fun latentSkill : ℝ => latentSkill)
      (lg21NormalizedRestriction
        (gaussianLocationKernel baseMean hbaseMean baseVariance publicBase)
        (Set.Iio threshold)) := by
  let fibre := gaussianLocationKernel baseMean hbaseMean baseVariance publicBase
  have hfibre : fibre = gaussianReal (baseMean publicBase) baseVariance := by
    exact gaussianLocationKernel_apply baseMean hbaseMean baseVariance publicBase
  letI : IsFiniteMeasure fibre := by
    rw [hfibre]
    infer_instance
  have hpositive : 0 < fibre (Set.Iio threshold) := by
    rw [hfibre]
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase) threshold hbaseVariance
  have hintegrableRaw : Integrable (fun latentSkill : ℝ => latentSkill) fibre := by
    rw [hfibre]
    exact (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
  unfold lg21NormalizedRestriction
  exact hintegrableRaw.restrict.smul_measure
    (ENNReal.inv_ne_top.mpr (ne_of_gt hpositive))

/-- With any positive gap, the no-access conditional mean lies strictly
below the latent-tail candidate threshold `m(base) + gap`. -/
theorem lg21_gaussianLocationKernel_skill_mean_lt_mean_add_gap
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (publicBase : Base) (gap : ℝ) (hgap : 0 < gap) :
    (∫ latentSkill, latentSkill ∂
      gaussianLocationKernel baseMean hbaseMean baseVariance publicBase) <
      baseMean publicBase + gap := by
  rw [lg21_gaussianLocationKernel_skill_mean]
  linarith

/-- The selected access non-taker fibre is also strictly below a positive-gap
candidate threshold.  Together with the preceding result, these are the two
strict component inequalities required by the raw hidden-access mixture. -/
theorem lg21_gaussianLocationKernel_lowerTail_mean_lt_mean_add_gap
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (publicBase : Base) (gap : ℝ) (hgap : 0 < gap) :
    (∫ latentSkill, latentSkill ∂
      lg21NormalizedRestriction
        (gaussianLocationKernel baseMean hbaseMean baseVariance publicBase)
        (Set.Iio (baseMean publicBase + gap))) <
      baseMean publicBase + gap := by
  exact lg21_gaussianLocationKernel_lowerTail_mean_lt_threshold
    baseMean hbaseMean baseVariance hbaseVariance publicBase
    (baseMean publicBase + gap)

/-! ## Reusable normalized-mixture mean algebra -/

/-- Exact mean formula for a finite normalized mixture of two probability
laws.  This keeps both source components and their literal masses explicit,
which is useful before imposing any qualitative inequality on the mixture. -/
theorem lg21_normalizedTwoComponentMean_eq
    {Outcome : Type*} [MeasurableSpace Outcome]
    (μ₀ μ₁ : Measure Outcome) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (value : Outcome → ℝ)
    (weight₀ weight₁ : ENNReal)
    (hweight₀Finite : weight₀ ≠ ⊤) (hweight₁Finite : weight₁ ≠ ⊤)
    (hintegrable₀ : Integrable value μ₀)
    (hintegrable₁ : Integrable value μ₁) :
    (∫ outcome, value outcome ∂
      ((weight₀ + weight₁)⁻¹ •
        (weight₀ • μ₀ + weight₁ • μ₁))) =
      (weight₀.toReal + weight₁.toReal)⁻¹ *
        (weight₀.toReal * (∫ outcome, value outcome ∂μ₀) +
          weight₁.toReal * (∫ outcome, value outcome ∂μ₁)) := by
  have hintegrableWeighted₀ : Integrable value (weight₀ • μ₀) :=
    hintegrable₀.smul_measure hweight₀Finite
  have hintegrableWeighted₁ : Integrable value (weight₁ • μ₁) :=
    hintegrable₁.smul_measure hweight₁Finite
  rw [MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_add_measure hintegrableWeighted₀ hintegrableWeighted₁,
    MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure,
    ENNReal.toReal_inv,
    ENNReal.toReal_add hweight₀Finite hweight₁Finite]
  ring

/-- A normalized positive mixture of two probability laws whose means are
strictly below a common bound also has mean strictly below that bound.  The
weights are explicit finite source masses; no probabilistic component is
dropped or silently renormalized. -/
theorem lg21_normalizedTwoComponentMean_lt_upper
    {Outcome : Type*} [MeasurableSpace Outcome]
    (μ₀ μ₁ : Measure Outcome) [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    (value : Outcome → ℝ) (upper : ℝ)
    (weight₀ weight₁ : ENNReal)
    (hweight₀ : 0 < weight₀) (hweight₁ : 0 < weight₁)
    (hweight₀Finite : weight₀ ≠ ⊤) (hweight₁Finite : weight₁ ≠ ⊤)
    (hintegrable₀ : Integrable value μ₀)
    (hintegrable₁ : Integrable value μ₁)
    (hmean₀ : (∫ outcome, value outcome ∂μ₀) < upper)
    (hmean₁ : (∫ outcome, value outcome ∂μ₁) < upper) :
    (∫ outcome, value outcome ∂
      ((weight₀ + weight₁)⁻¹ •
        (weight₀ • μ₀ + weight₁ • μ₁))) < upper := by
  let w₀Real : ℝ := weight₀.toReal
  let w₁Real : ℝ := weight₁.toReal
  have hw₀Real_pos : 0 < w₀Real := by
    exact ENNReal.toReal_pos (ne_of_gt hweight₀) hweight₀Finite
  have hw₁Real_pos : 0 < w₁Real := by
    exact ENNReal.toReal_pos (ne_of_gt hweight₁) hweight₁Finite
  have hsumReal_pos : 0 < w₀Real + w₁Real := by linarith
  have hintegrableWeighted₀ : Integrable value (weight₀ • μ₀) :=
    hintegrable₀.smul_measure hweight₀Finite
  have hintegrableWeighted₁ : Integrable value (weight₁ • μ₁) :=
    hintegrable₁.smul_measure hweight₁Finite
  have hintegrableSum : Integrable value (weight₀ • μ₀ + weight₁ • μ₁) :=
    hintegrableWeighted₀.add_measure hintegrableWeighted₁
  have hmeanFormula :
      (∫ outcome, value outcome ∂
        ((weight₀ + weight₁)⁻¹ • (weight₀ • μ₀ + weight₁ • μ₁))) =
        (w₀Real + w₁Real)⁻¹ *
          (w₀Real * (∫ outcome, value outcome ∂μ₀) +
            w₁Real * (∫ outcome, value outcome ∂μ₁)) := by
    rw [MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_add_measure hintegrableWeighted₀ hintegrableWeighted₁,
      MeasureTheory.integral_smul_measure,
      MeasureTheory.integral_smul_measure]
    have hsum_toReal : (weight₀ + weight₁).toReal = w₀Real + w₁Real := by
      rw [ENNReal.toReal_add hweight₀Finite hweight₁Finite]
    rw [ENNReal.toReal_inv, hsum_toReal]
    ring
  have hweighted₀ : w₀Real * (∫ outcome, value outcome ∂μ₀) <
      w₀Real * upper :=
    mul_lt_mul_of_pos_left hmean₀ hw₀Real_pos
  have hweighted₁ : w₁Real * (∫ outcome, value outcome ∂μ₁) <
      w₁Real * upper :=
    mul_lt_mul_of_pos_left hmean₁ hw₁Real_pos
  have hweighted :
      w₀Real * (∫ outcome, value outcome ∂μ₀) +
        w₁Real * (∫ outcome, value outcome ∂μ₁) <
      (w₀Real + w₁Real) * upper := by
    rw [add_mul]
    exact add_lt_add hweighted₀ hweighted₁
  rw [hmeanFormula]
  calc
    (w₀Real + w₁Real)⁻¹ *
        (w₀Real * (∫ outcome, value outcome ∂μ₀) +
          w₁Real * (∫ outcome, value outcome ∂μ₁)) <
        (w₀Real + w₁Real)⁻¹ * ((w₀Real + w₁Real) * upper) :=
      mul_lt_mul_of_pos_left hweighted (inv_pos.mpr hsumReal_pos)
    _ = upper := by
      field_simp [ne_of_gt hsumReal_pos]

/-- At every public base, the literal hidden-access candidate no-report
fibre for the positive-gap tail action has mean strictly below its taking
threshold.  The calculation keeps the no-access Gaussian component and the
access lower-tail component visible throughout. -/
theorem lg21_gaussianHiddenAccessTailNormalizedKernel_mean_lt_mean_add_gap
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base → ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (noAccessMass accessMass : ENNReal)
    (hnoAccess : 0 < noAccessMass) (haccess : 0 < accessMass)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (gap : ℝ) (hgap : 0 < gap) (publicBase : Base) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    (∫ latentSkill, latentSkill ∂
      lg21HiddenAccessTailNormalizedKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance)
        noAccessMass accessMass hnoAccessFinite haccessFinite
        (fun base => baseMean base + gap) publicBase) <
      baseMean publicBase + gap := by
  let κ : Kernel Base ℝ := gaussianLocationKernel baseMean hbaseMean baseVariance
  let threshold : Base → ℝ := fun base => baseMean base + gap
  let lowerTail : Set ℝ := Set.Iio (threshold publicBase)
  let lowerMass : ENNReal := κ publicBase lowerTail
  let lowerLaw : Measure ℝ := lg21NormalizedRestriction (κ publicBase) lowerTail
  letI : IsMarkovKernel κ := by
    simpa [κ] using gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
  letI : IsFiniteMeasure (κ publicBase) := by infer_instance
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hlowerPositive : 0 < lowerMass := by
    change 0 < κ publicBase (Set.Iio (threshold publicBase))
    rw [show κ publicBase = gaussianReal (baseMean publicBase) baseVariance by
      exact gaussianLocationKernel_apply baseMean hbaseMean baseVariance publicBase]
    exact lg21_gaussianReal_Iio_pos (baseMean publicBase)
      (threshold publicBase) hbaseVariance
  have hlowerFinite : lowerMass ≠ ⊤ := by
    exact measure_ne_top _ _
  letI : IsProbabilityMeasure lowerLaw := by
    simpa [lowerLaw] using
      (lg21NormalizedRestriction_isProbability (κ publicBase) lowerTail
        (ne_of_gt hlowerPositive) hlowerFinite)
  have hweight₁ : 0 < accessMass * lowerMass := by
    exact ENNReal.mul_pos (ne_of_gt haccess) (ne_of_gt hlowerPositive)
  have hweight₁Finite : accessMass * lowerMass ≠ ⊤ := by
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
        ((noAccessMass + accessMass * lowerMass)⁻¹) •
          (noAccessMass • κ publicBase +
            (accessMass * lowerMass) • lowerLaw) := by
    rw [lg21HiddenAccessTailNormalizedKernel_apply
      κ noAccessMass accessMass hnoAccessFinite haccessFinite threshold
      hthreshold publicBase, hrawKernel]
    rfl
  rw [show lg21HiddenAccessTailNormalizedKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance)
      noAccessMass accessMass hnoAccessFinite haccessFinite
      (fun base => baseMean base + gap) publicBase =
      lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
        hnoAccessFinite haccessFinite threshold publicBase by rfl,
    hnormalizedKernel]
  exact lg21_normalizedTwoComponentMean_lt_upper
    (κ publicBase) lowerLaw (fun latentSkill : ℝ => latentSkill)
    (threshold publicBase) noAccessMass (accessMass * lowerMass)
    hnoAccess hweight₁ hnoAccessFinite hweight₁Finite
    (lg21_gaussianLocationKernel_skill_integrable
      baseMean hbaseMean baseVariance publicBase)
    (lg21_gaussianLocationKernel_lowerTail_integrable
      baseMean hbaseMean baseVariance hbaseVariance publicBase
      (threshold publicBase))
    (lg21_gaussianLocationKernel_skill_mean_lt_mean_add_gap
      baseMean hbaseMean baseVariance publicBase gap hgap)
    (lg21_gaussianLocationKernel_lowerTail_mean_lt_mean_add_gap
      baseMean hbaseMean baseVariance hbaseVariance publicBase gap hgap)

/-! ## Raw candidate conditional distribution -/

/-- The literal raw `(base, skill)` law of any measurable tail candidate has
total mass one once positive no-access mass is retained. -/
theorem lg21HiddenAccessConditionalMeanTail_noReportBaseSkillLaw_isProbability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (candidateBaseMean :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hcandidateBaseMean : Measurable candidateBaseMean) :
    IsProbabilityMeasure
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
        (fun _ _ => true)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
    (fun _ _ => true)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
        (fun _ _ => true) hnoAccess))
      (measure_ne_top _ _)
  change IsProbabilityMeasure
    ((lg21NormalizedRestriction rawLaw noReportEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature))
  exact Measure.isProbabilityMeasure_map
    (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable

/-- The source-timed positive-gap tail candidate has the displayed normalized
raw-tail kernel as its actual conditional latent-skill law on the public
`X = 0` branch.  The conditioning measure is the candidate's normalized raw
population law, so hidden `Z = 0` students remain in the branch throughout.

This is an almost-everywhere RCD identification, rather than a choice of a
pointwise belief on an atomless singleton. -/
theorem lg21HiddenAccessConditionalMeanTail_noReport_condDistrib_skill_base_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal)
    (hsourceFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance)
    (gap : ℝ)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    let candidateBaseMean :
        (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
      fun publicBase => baseMean publicBase + gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
      (fun _ _ => true)
    letI : IsProbabilityMeasure candidateLaw := by
      let rawLaw := lg21ContinuousGaussianPopulationLaw M
      let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
        (fun _ _ => true)
      letI : IsProbabilityMeasure rawLaw :=
        lg21ContinuousGaussianPopulationLaw_isProbability M
      letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
      letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
        lg21NormalizedRestriction_isProbability rawLaw noReportEvent
          (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
            M testFeature
            (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
            (fun _ _ => true) hnoAccess))
          (measure_ne_top _ _)
      exact Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
    condDistrib Prod.snd Prod.fst candidateLaw =ᵐ[candidateLaw.map Prod.fst]
      lg21HiddenAccessTailNormalizedKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite
        candidateBaseMean := by
  intro candidateBaseMean candidateLaw
  letI : IsMarkovKernel (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateTake :=
    lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean
  let candidateReport :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
    fun _ _ => true
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  let rawMass : ENNReal := rawLaw noReportEvent
  let κ : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  let rawKernel := lg21HiddenAccessTailRawKernel κ
    (M.accessLaw {false}) (M.accessLaw {true}) candidateBaseMean
  let fibreMass := lg21HiddenAccessTailRawFibreMass κ
    (M.accessLaw {false}) (M.accessLaw {true}) candidateBaseMean
  let normalizedKernel := lg21HiddenAccessTailNormalizedKernel κ
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite candidateBaseMean
  let candidateBaseLaw : Measure
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    rawMass⁻¹ • baseLaw.withDensity fibreMass
  letI : IsProbabilityMeasure candidateLaw := by
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
      lg21NormalizedRestriction_isProbability rawLaw noReportEvent
        (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
          M testFeature candidateTake candidateReport hnoAccess))
        (measure_ne_top _ _)
    change IsProbabilityMeasure
      ((lg21NormalizedRestriction rawLaw noReportEvent).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
    exact Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsMarkovKernel κ := by
    simpa [κ] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance)
  have hcandidateBaseMean : Measurable candidateBaseMean := by
    simpa [candidateBaseMean] using hbaseMean.add measurable_const
  letI : IsFiniteKernel rawKernel := by
    simpa [rawKernel] using
      (lg21HiddenAccessTailRawKernel_isFinite κ
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite candidateBaseMean)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel] using
      (lg21HiddenAccessTailNormalizedKernel_isMarkov κ
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess hnoAccessFinite haccessFinite
        candidateBaseMean hcandidateBaseMean)
  have hcandidateMixture : candidateLaw = rawMass⁻¹ •
      (M.accessLaw {false} •
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature +
        M.accessLaw {true} •
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
            (lg21HiddenAccessBaseSkillLowerTailEvent candidateBaseMean)) := by
    simpa [candidateLaw, rawLaw, noReportEvent, candidateTake, candidateReport] using
      (lg21HiddenAccessConditionalMeanTail_noReportBaseSkillLaw_eq_normalized_raw_mixture
        M hnoAccess haccess testFeature candidateBaseMean hcandidateBaseMean)
  have hrawFactor :
      M.accessLaw {false} •
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature +
        M.accessLaw {true} •
          (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
            (lg21HiddenAccessBaseSkillLowerTailEvent candidateBaseMean) =
        baseLaw ⊗ₘ rawKernel := by
    rw [hsourceFactor]
    symm
    simpa [rawKernel, κ] using
      (lg21HiddenAccessTailRawKernel_compProd_eq_raw_mixture baseLaw κ
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite candidateBaseMean hcandidateBaseMean)
  have hweightedFactor :
      (baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel =
        baseLaw ⊗ₘ rawKernel := by
    simpa [fibreMass, normalizedKernel, rawKernel] using
      (lg21HiddenAccessTailWeightedBase_compProd_normalizedKernel baseLaw κ
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess
        hnoAccessFinite haccessFinite candidateBaseMean hcandidateBaseMean)
  have hcandidateFactor : candidateLaw = candidateBaseLaw ⊗ₘ normalizedKernel := by
    calc
      candidateLaw = rawMass⁻¹ •
          (M.accessLaw {false} •
              lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature +
            M.accessLaw {true} •
              (lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature).restrict
                (lg21HiddenAccessBaseSkillLowerTailEvent candidateBaseMean)) :=
        hcandidateMixture
      _ = rawMass⁻¹ • (baseLaw ⊗ₘ rawKernel) := by rw [hrawFactor]
      _ = rawMass⁻¹ • ((baseLaw.withDensity fibreMass) ⊗ₘ normalizedKernel) := by
        rw [hweightedFactor]
      _ = candidateBaseLaw ⊗ₘ normalizedKernel := by
        rw [Measure.compProd_smul_left]
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
  simpa [normalizedKernel, κ] using
    (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      measurable_fst measurable_snd hjoint)

/-- The no-report PBO value induced by the literal raw hidden-access
candidate population.  It is a conditional mean under the normalized raw
mixture kernel, not an access-only posterior. -/
noncomputable def lg21HiddenAccessTailCandidateNoReportValue
    {Base : Type*} [MeasurableSpace Base]
    (κ : Kernel Base ℝ) [IsMarkovKernel κ]
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (threshold : Base -> ℝ) (publicBase : Base) : ℝ :=
  ∫ latentSkill, latentSkill ∂
    lg21HiddenAccessTailNormalizedKernel κ noAccessMass accessMass
      hnoAccessFinite haccessFinite threshold publicBase

/-- The literal raw-tail candidate no-report value is the actual conditional
mean of latent skill on its own `X = 0` source population, almost everywhere
under that population's public-base marginal. -/
theorem lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal)
    (hsourceFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance)
    (gap : ℝ)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    let candidateBaseMean :
        (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
      fun publicBase => baseMean publicBase + gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
      (fun _ _ => true)
    letI : IsProbabilityMeasure candidateLaw := by
      let rawLaw := lg21ContinuousGaussianPopulationLaw M
      let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
        (fun _ _ => true)
      letI : IsProbabilityMeasure rawLaw :=
        lg21ContinuousGaussianPopulationLaw_isProbability M
      letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
      letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
        lg21NormalizedRestriction_isProbability rawLaw noReportEvent
          (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
            M testFeature
            (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
            (fun _ _ => true) hnoAccess))
          (measure_ne_top _ _)
      exact Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
    ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite candidateBaseMean publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
        candidateLaw publicBase := by
  intro candidateBaseMean candidateLaw
  let κ : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  letI : IsMarkovKernel κ := by
    simpa [κ] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance)
  have hcond :=
    lg21HiddenAccessConditionalMeanTail_noReport_condDistrib_skill_base_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hsourceFactor gap hnoAccessFinite haccessFinite
  filter_upwards [hcond] with publicBase hcondAt
  rw [hcondAt]
  rfl

/-- On the literal raw `X = 0` candidate population, the conditional mean
of skill is strictly below the positive-gap taking threshold.  This is only
the no-report PBO comparison for the tail action; an all-taking conclusion
requires a separate action-set closure. -/
theorem lg21HiddenAccessConditionalMeanTail_noReport_condDistribMean_lt_threshold_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : NNReal) (hbaseVariance : baseVariance ≠ 0)
    (hsourceFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance)
    (gap : ℝ) (hgap : 0 < gap)
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    letI : IsMarkovKernel
        (gaussianLocationKernel baseMean hbaseMean baseVariance) :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance
    let candidateBaseMean :
        (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
      fun publicBase => baseMean publicBase + gap
    let candidateLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature candidateBaseMean)
      (fun _ _ => true)
    letI : IsProbabilityMeasure candidateLaw :=
      lg21HiddenAccessConditionalMeanTail_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateBaseMean
        (hbaseMean.add measurable_const)
    ∀ᵐ publicBase ∂candidateLaw.map Prod.fst,
      (∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
        candidateLaw publicBase) < candidateBaseMean publicBase := by
  intro candidateBaseMean candidateLaw
  let κ : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean baseVariance
  letI : IsMarkovKernel κ := by
    simpa [κ] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance)
  have hcandidateBaseMean : Measurable candidateBaseMean := by
    simpa [candidateBaseMean] using hbaseMean.add measurable_const
  letI : IsProbabilityMeasure candidateLaw := by
    simpa [candidateLaw] using
      (lg21HiddenAccessConditionalMeanTail_noReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateBaseMean hcandidateBaseMean)
  have hpbo :=
    lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hsourceFactor gap hnoAccessFinite haccessFinite
  have hbound : ∀ publicBase,
      lg21HiddenAccessTailCandidateNoReportValue κ
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite candidateBaseMean publicBase <
        candidateBaseMean publicBase := by
    intro publicBase
    simpa [κ, candidateBaseMean,
      lg21HiddenAccessTailCandidateNoReportValue] using
      (lg21_gaussianHiddenAccessTailNormalizedKernel_mean_lt_mean_add_gap
        baseMean hbaseMean baseVariance hbaseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess haccess hnoAccessFinite haccessFinite gap hgap publicBase)
  filter_upwards [hpbo] with publicBase hpboAt
  rw [← hpboAt]
  exact hbound publicBase

end

end LG21TestOptionalPolicies
