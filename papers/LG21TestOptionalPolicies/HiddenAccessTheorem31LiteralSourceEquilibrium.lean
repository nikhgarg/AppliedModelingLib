import LG21TestOptionalPolicies.HiddenAccessTheorem31ComponentConditionalBridge
import LG21TestOptionalPolicies.OptionalAllTakeSemanticBridge

/-!
# Literal source equilibrium for LG21 Theorem 3.1

This is a deliberately narrow carrier for the optional hidden-access regime.
It retains the literal population, the pre-score taking action, the post-score
reporting action, Definition 1's two best-response inequalities, and the
PBO as conditional expectation on the actual public-action laws.

It does not carry a cutoff, a posterior formula, a candidate replacement
profile, or `estimationConsistent : Prop`.  The first theorem below uses the
carrier immediately: a positive-slope source payoff and nondegenerate source
test noise give a strict expected gain from taking, so an active positive-mass
no-take deviation is impossible.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal PBO predicates -/

/-- The payoff assigned by the school at the literal complete public record. -/
def lg21HiddenAccessOptionalPublicPayoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (student : Bool × (ℝ × (Feature → ℝ))) : ℝ :=
  if lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision student = true then
    reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2)
  else
    noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2)

/-- PBO semantics at the literal complete public record, rather than an
uninterpreted equilibrium-consistency proposition. -/
def LG21HiddenAccessActualPublicPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ) : Prop :=
  let law := lg21ContinuousGaussianPopulationLaw M
  let observation := lg21HiddenAccessOptionalPublicObservation testFeature
    takeDecision reportDecision
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure law := ⟨by simp⟩
  lg21HiddenAccessOptionalPublicPayoff testFeature takeDecision reportDecision
    reportedPayoff noReportPayoff =ᵐ[law]
      law[lg21ContinuousPopulationSkill |
        MeasurableSpace.comap observation inferInstance]

/-- PBO semantics at the actual on-path `X = 0` public action.  The equality
is guarded by positive branch mass and is only almost everywhere under the
literal normalized no-report law. -/
def LG21HiddenAccessActualNoReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ) : Prop :=
  ∀ hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision),
    let law := lg21ContinuousGaussianPopulationLaw M
    let noReportLaw := lg21HiddenAccessOptionalNoReportLaw M testFeature
      takeDecision reportDecision
    let base : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure law := ⟨by simp⟩
    letI : IsProbabilityMeasure noReportLaw :=
      lg21NormalizedRestriction_isProbability law
        (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure noReportLaw := ⟨by simp⟩
    (fun student => noReportPayoff (base student)) =ᵐ[noReportLaw]
      noReportLaw[lg21ContinuousPopulationSkill |
        MeasurableSpace.comap base inferInstance]

/-! ## Source-equilibrium carrier and active deviations -/

/--
A pointwise source-timed hidden-access optional equilibrium with literal PBO
semantics.

This is retained as a non-credit behavioral auxiliary: a regular conditional
distribution only identifies a public PBO almost everywhere on an attained
information law, so its pointwise best-response fields cannot be used to turn
an a.e. PBO identity into a pointwise conclusion.  The downstream
source-facing carrier is `LG21HiddenAccessLiteralSourceEquilibriumAE` below.
-/
structure LG21HiddenAccessLiteralSourceEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) where
  takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool
  reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool
  reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ
  noReportPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ
  testLaw : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Measure ℝ
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature → ℝ) => takeDecision pair.1 pair.2)
  reportDecision_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ => reportDecision pair.1 pair.2)
  reportedPayoff_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ => reportedPayoff pair.1 pair.2)
  noReportPayoff_measurable : Measurable noReportPayoff
  continuationPayoff_integrable : ∀ skill base,
    Integrable (fun score =>
      if reportDecision base score then reportedPayoff base score else noReportPayoff base)
      (testLaw skill base)
  take_best_response : ∀ base,
    NoProfitableBinaryChoiceDeviation
      (fun skill => takeDecision skill base = true)
      (fun skill => ∫ score,
        if reportDecision base score then reportedPayoff base score else noReportPayoff base
        ∂testLaw skill base)
      (fun _skill => noReportPayoff base)
  report_best_response : ∀ base,
    NoProfitableBinaryChoiceDeviation
      (fun score => reportDecision base score = true)
      (reportedPayoff base) (fun _score => noReportPayoff base)
  raw_test_law : ∀ skill base,
    testLaw skill base = gaussianReal skill (M.noiseVariance testFeature)
  test_noise_nonzero : M.noiseVariance testFeature ≠ 0
  reportedIntercept : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ
  reportedSlope : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ
  reportedSlope_pos : ∀ base, 0 < reportedSlope base
  reportedPayoff_affine : ∀ base score,
    reportedPayoff base score = reportedIntercept base + reportedSlope base * score
  public_pbo : LG21HiddenAccessActualPublicPBO M testFeature takeDecision
    reportDecision reportedPayoff noReportPayoff
  noReport_pbo : LG21HiddenAccessActualNoReportPBO M testFeature takeDecision
    reportDecision noReportPayoff

namespace LG21HiddenAccessLiteralSourceEquilibrium

/-- The legacy record is only a behavioral adapter.  Its opaque consistency
slot is never used: the literal PBO identities remain explicit fields of the
source-equilibrium carrier. -/
def toSequentialData
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) :
    LG21OptionalSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ where
  testLaw := E.testLaw
  testLaw_isProbability := E.testLaw_isProbability
  takeDecision := E.takeDecision
  reportDecision := E.reportDecision
  reportedPayoff := E.reportedPayoff
  noReportPayoff := E.noReportPayoff
  continuationPayoff_integrable := E.continuationPayoff_integrable
  estimationConsistent := True

theorem toSequentialEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) :
    lg21OptionalSequentialEquilibrium E.toSequentialData := by
  refine ⟨?_, ?_, trivial⟩
  · intro base
    simpa [toSequentialData, lg21OptionalSequentialTakeExpectedPayoff,
      lg21OptionalSequentialContinuationPayoff] using E.take_best_response base
  · intro base
    simpa [toSequentialData] using E.report_best_response base

/-- The literal actual population event whose members have test access but
choose the source's pre-score no-take action. -/
def activeNoTakeEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true ∧
    lg21HiddenAccessStudentTake testFeature E.takeDecision student.2 = false}

/-- A positive-mass active no-take deviation is measured in the literal
population, not at a named strategy fibre or an off-path conditional value. -/
def ActiveNoTakePositiveMassDeviation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) : Prop :=
  0 < lg21ContinuousGaussianPopulationLaw M (E.activeNoTakeEvent)

/-! ## Strict expected gain and contradiction -/

/-- Every latent skill has a strict source-timed expected gain from taking.
The proof uses a positive Gaussian upper tail and the actual ex-post
best-response inequality; no cutoff is assumed. -/
theorem takeExpectedPayoff_strictly_exceeds_noReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature)
    (skill : ℝ) (base : LG21NonTestFeature Feature testFeature → ℝ) :
    E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E.toSequentialData skill base := by
  let intercept := E.reportedIntercept base
  let slope := E.reportedSlope base
  have hslope : 0 < slope := by
    simpa [slope] using E.reportedSlope_pos base
  have hreported : ∀ score,
      E.toSequentialData.reportedPayoff base score = intercept + slope * score := by
    intro score
    simpa [toSequentialData, intercept, slope] using E.reportedPayoff_affine base score
  let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
  have htail : 0 < E.testLaw skill base (Set.Ioi cutoff) := by
    rw [E.raw_test_law skill base]
    exact lg21_gaussianReal_Ioi_pos skill cutoff E.test_noise_nonzero
  have hstrictMass : 0 < E.testLaw skill base
      {score | E.noReportPayoff base < E.reportedPayoff base score} := by
    apply lt_of_lt_of_le htail
    apply measure_mono
    intro score hscore
    change E.noReportPayoff base < E.reportedPayoff base score
    rw [E.reportedPayoff_affine base score]
    have hcutoffValue : intercept + slope * cutoff = E.noReportPayoff base := by
      dsimp [cutoff]
      apply le_antisymm
      · exact (affine_le_threshold_iff_le_cutoff hslope).2 le_rfl
      · exact (threshold_le_affine_iff_cutoff_le hslope).2 le_rfl
    rw [← hcutoffValue]
    exact affine_strictMono intercept hslope hscore
  have hpositive : 0 < E.testLaw skill base
      {score | E.reportDecision base score = true ∧
        E.noReportPayoff base < E.reportedPayoff base score} := by
    apply lt_of_lt_of_le hstrictMass
    apply measure_mono
    intro score hgain
    refine ⟨?_, hgain⟩
    by_contra hnotReport
    have hbest := (E.report_best_response base).2 score hnotReport
    exact (not_le_of_gt hgain) hbest
  exact lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
    E.toSequentialData E.toSequentialEquilibrium skill base hpositive

/-- The source best-response condition contradicts any actual positive-mass
active no-take deviation.  The result is stronger pointwise, but is stated in
positive-mass form so it can be used directly with the literal population
action event. -/
theorem not_activeNoTakePositiveMassDeviation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) :
    ¬ E.ActiveNoTakePositiveMassDeviation := by
  intro hpositive
  change 0 < lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent at hpositive
  have hempty : E.activeNoTakeEvent = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨access, primitive⟩ hmember
    change access = true ∧
      E.takeDecision primitive.1
        (lg21HiddenAccessStudentBase testFeature primitive) = false at hmember
    have hstrict := E.takeExpectedPayoff_strictly_exceeds_noReport primitive.1
      (lg21HiddenAccessStudentBase testFeature primitive)
    have hbest := (E.take_best_response
      (lg21HiddenAccessStudentBase testFeature primitive)).2 primitive.1
        (by simpa [lg21HiddenAccessStudentTake] using hmember.2)
    exact (not_le_of_gt hstrict) hbest
  rw [hempty] at hpositive
  simpa using hpositive

/-- Pointwise all-taking follows from the same strict source-timed gain.
This is the behavioral bridge needed before the literal `X = 0` mixture may
be reduced to the two action components. -/
theorem all_take
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibrium M testFeature) :
    ∀ skill base, E.takeDecision skill base = true := by
  intro skill base
  by_contra hnotTake
  have hstrict := E.takeExpectedPayoff_strictly_exceeds_noReport skill base
  have hbest := (E.take_best_response base).2 skill hnotTake
  exact (not_le_of_gt hstrict) hbest

end LG21HiddenAccessLiteralSourceEquilibrium

/-! ## Source-faithful a.e. behavioral wrapper -/

/-- The literal access-population law of the pre-score decision inputs,
ordered as `(skill, public non-test base)`. -/
def lg21HiddenAccessAccessLatentBaseLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure (ℝ × (LG21NonTestFeature Feature testFeature → ℝ)) :=
  (lg21ContinuousGaussianAccessPopulationLaw M).map
    (fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21HiddenAccessStudentBase testFeature student.2))

/-- The literal access-population law of the post-score decision inputs,
ordered as `(public non-test base, score)`. -/
def lg21HiddenAccessAccessBaseScoreLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  (lg21ContinuousGaussianAccessPopulationLaw M).map
    (fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2))

theorem lg21HiddenAccessLatentBaseObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      (lg21ContinuousPopulationSkill student,
        lg21HiddenAccessStudentBase testFeature student.2)) := by
  exact (measurable_fst.comp measurable_snd).prodMk
    ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)

theorem lg21HiddenAccessBaseScoreObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)) := by
  exact ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd).prodMk
    ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)

/--
The source-facing hidden-access equilibrium carrier shared by the two timing
regimes.  It keeps the literal source population and public PBO equations and
states the pre-score part of Definition 1 pointwise for every public base and
latent skill.  The `AE` suffix is retained for compatibility with the actual
conditional-PBO layers; it does not weaken the Section 3 action response.

There is deliberately no score-stage report-versus-withhold best-response
field here.  That comparison belongs to the optional-reporting regime only;
under report-required-after-taking it is infeasible.  Optional closeouts take
that source condition explicitly.  The carrier also has no affine-PBO, cutoff,
or posterior-representative field: such identities must be derived from
`public_pbo` on an actual positive action event.
-/
structure LG21HiddenAccessLiteralSourceEquilibriumAE
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) where
  takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool
  reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool
  reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ
  noReportPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ
  testLaw : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Measure ℝ
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature → ℝ) => takeDecision pair.1 pair.2)
  reportDecision_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ => reportDecision pair.1 pair.2)
  reportedPayoff_measurable : Measurable (fun pair :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ => reportedPayoff pair.1 pair.2)
  noReportPayoff_measurable : Measurable noReportPayoff
  continuationPayoff_integrable : ∀ skill base,
    Integrable (fun score =>
      if reportDecision base score then reportedPayoff base score else noReportPayoff base)
      (testLaw skill base)
  access_positive : 0 < M.accessLaw {true}
  /-- Definition 1 is pointwise in every pre-score type `(skill, base)`.
  This Section 3 field deliberately does not use the separate Section 4
  almost-everywhere active-branch convention. -/
  take_best_response : ∀ publicBase,
    NoProfitableBinaryChoiceDeviation
      (fun latentSkill => takeDecision latentSkill publicBase = true)
      (fun latentSkill => ∫ score,
        if reportDecision publicBase score then reportedPayoff publicBase score
        else noReportPayoff publicBase ∂testLaw latentSkill publicBase)
      (fun _latentSkill => noReportPayoff publicBase)
  raw_test_law : ∀ skill base,
    testLaw skill base = gaussianReal skill (M.noiseVariance testFeature)
  test_noise_nonzero : M.noiseVariance testFeature ≠ 0
  public_pbo : LG21HiddenAccessActualPublicPBO M testFeature takeDecision
    reportDecision reportedPayoff noReportPayoff
  noReport_pbo : LG21HiddenAccessActualNoReportPBO M testFeature takeDecision
    reportDecision noReportPayoff

namespace LG21HiddenAccessLiteralSourceEquilibriumAE

/-- The pointwise Definition-1 take response, viewed on the actual source law
for measure-theoretic downstream arguments. -/
theorem take_best_response_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature)
      (fun profile => E.takeDecision profile.1 profile.2 = true)
      (fun profile => ∫ score,
        if E.reportDecision profile.2 score then E.reportedPayoff profile.2 score
        else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2)
      (fun profile => E.noReportPayoff profile.2) := by
  apply noProfitableBinaryChoiceDeviationAE_of_pointwise
  constructor
  · intro profile htake
    exact (E.take_best_response profile.2).1 profile.1 htake
  · intro profile hnoTake
    exact (E.take_best_response profile.2).2 profile.1 hnoTake

/-- The score-stage Definition-1 condition for the optional-reporting
regime.  It is intentionally a separate proposition rather than a field of
the shared carrier, because taking and withholding is infeasible when
reporting is required after taking. -/
abbrev OptionalReportBestResponse
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  ∀ publicBase,
    NoProfitableBinaryChoiceDeviation
      (fun score => E.reportDecision publicBase score = true)
      (E.reportedPayoff publicBase)
      (fun _score => E.noReportPayoff publicBase)

/-- Compatibility spelling retained for existing Section 3 callers.  Its
content is pointwise; the suffix records only that older proof layers consume
the derived a.e. projection below. -/
abbrev OptionalReportBestResponseAE
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  E.OptionalReportBestResponse

/-- Project the universal score-stage response onto the source law. -/
theorem optionalReportBestResponse_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hbest : E.OptionalReportBestResponseAE) :
    NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessBaseScoreLaw M testFeature)
      (fun profile => E.reportDecision profile.1 profile.2 = true)
      (fun profile => E.reportedPayoff profile.1 profile.2)
      (fun profile => E.noReportPayoff profile.1) := by
  apply noProfitableBinaryChoiceDeviationAE_of_pointwise
  constructor
  · intro profile hreport
    exact (hbest profile.1).1 profile.2 hreport
  · intro profile hwithhold
    exact (hbest profile.1).2 profile.2 hwithhold

/-- The literal pre-score no-take event measured under the actual
positive-access population. -/
def accessNoTakeEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | lg21HiddenAccessStudentTake testFeature E.takeDecision student.2 = false}

/-- The same event as a literal raw-population event; the access coordinate is
kept explicit rather than represented by an externally supplied cohort. -/
def activeNoTakeEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = true ∧
    lg21HiddenAccessStudentTake testFeature E.takeDecision student.2 = false}

theorem accessNoTakeEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    MeasurableSet E.accessNoTakeEvent := by
  unfold accessNoTakeEvent
  exact (measurableSet_singleton false).preimage
    ((lg21HiddenAccessStudentTake_measurable testFeature E.takeDecision
      E.takeDecision_measurable).comp measurable_snd)

/-- The unchosen side of the pointwise Definition 1 response, projected onto
the literal pre-score source law for the measure-theoretic closeout. -/
theorem take_noTake_best_response_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
      E.takeDecision profile.1 profile.2 = false →
        (∫ score,
          if E.reportDecision profile.2 score then E.reportedPayoff profile.2 score
          else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2) ≤
          E.noReportPayoff profile.2 := by
  filter_upwards [E.take_best_response_ae.2] with profile hbest hnoTake
  exact hbest (by simp [hnoTake])

/--
The a.e. Definition-1 closure used downstream.  Once the literal source law
and positive-event PBO calculation establish a strict test gain on actual
no-takers, an access student declines the test only on a null population set.

`hstrictGain` is deliberately an a.e. population obligation.  The theorem
does not turn an a.e. selected-posterior identity into a pointwise payoff, and
does not evaluate a null public action branch.
-/
theorem accessNoTakeEvent_measure_zero_of_globalStrictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstrictGain :
      ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
        E.takeDecision profile.1 profile.2 = false →
          E.noReportPayoff profile.2 <
            ∫ score,
              if E.reportDecision profile.2 score then E.reportedPayoff profile.2 score
              else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2) :
    lg21ContinuousGaussianAccessPopulationLaw M E.accessNoTakeEvent = 0 := by
  have himpossible :
      ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
        E.takeDecision profile.1 profile.2 ≠ false := by
    filter_upwards [E.take_noTake_best_response_ae, hstrictGain] with
      profile hbest hstrict hnoTake
    exact (not_le_of_gt (hstrict hnoTake)) (hbest hnoTake)
  have hpullback :
      ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
        E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) ≠ false := by
    exact ae_of_ae_map
      (lg21HiddenAccessLatentBaseObservation_measurable testFeature).aemeasurable
      himpossible
  have hzero := ae_iff.mp hpullback
  simpa [accessNoTakeEvent, lg21HiddenAccessStudentTake] using hzero

/-- The source's raw-population statement follows from the access-conditioned
a.e. conclusion because the literal access event has positive finite mass. -/
theorem activeNoTakeEvent_measure_zero_of_globalStrictGain
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstrictGain :
      ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
        E.takeDecision profile.1 profile.2 = false →
          E.noReportPayoff profile.2 <
            ∫ score,
              if E.reportDecision profile.2 score then E.reportedPayoff profile.2 score
              else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature → ℝ))) :=
    {student | student.1 = true}
  letI : IsProbabilityMeasure rawLaw := by
    dsimp [rawLaw]
    exact lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haccessNoTake :
      lg21ContinuousGaussianAccessPopulationLaw M E.accessNoTakeEvent = 0 :=
    E.accessNoTakeEvent_measure_zero_of_globalStrictGain hstrictGain
  have hnormalized :
      lg21NormalizedRestriction rawLaw accessEvent E.accessNoTakeEvent = 0 := by
    simpa [rawLaw, accessEvent, lg21ContinuousGaussianAccessPopulationLaw] using
      haccessNoTake
  have hintersection : rawLaw (E.accessNoTakeEvent ∩ accessEvent) = 0 := by
    rw [lg21NormalizedRestriction_apply rawLaw E.accessNoTakeEvent_measurable] at hnormalized
    exact (mul_eq_zero.mp hnormalized).resolve_left
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw accessEvent))
  have hevent : E.activeNoTakeEvent = E.accessNoTakeEvent ∩ accessEvent := by
    ext student
    simp [activeNoTakeEvent, accessNoTakeEvent, accessEvent, and_comm]
  simpa [rawLaw, hevent] using hintersection

end LG21HiddenAccessLiteralSourceEquilibriumAE

end

end LG21TestOptionalPolicies
