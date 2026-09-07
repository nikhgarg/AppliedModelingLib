import LG21TestOptionalPolicies.ObservedAccessContinuous
import LG21TestOptionalPolicies.MandatoryGivenAccessSection4Bridge
import LG21TestOptionalPolicies.Theorem44SourceGaussianResamplingRepair
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Transparent source semantics for the LG21 review surface

This file separates the paper's semantic objects from older implementation
carriers used to prove measure-theoretic support lemmas.  Source-facing
equilibrium statements expose feasibility, pointwise best response, and
policy-consistency equations directly.  The theorem helpers below may package
those primitives into legacy proof records locally, but those records are not
part of the reviewed proposition.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## Definition 1 -/

/--
Definition 1 with its source timing, arbitrary requirement policy, and
strategy-induced estimation policy.  A student chooses whether to take before
seeing the test score and chooses a score-contingent reporting rule afterward.
The three payoff functions distinguish the source action pairs `(Y, X) =
(false, false)`, `(true, false)`, and `(true, true)`.  Feasible reporting rules
are measurable, and every score-dependent payoff whose expectation is compared
is integrable under the student's test law.  The comparison is therefore the
source's expected-payoff argmax over all admissible feasible action-pair
strategies.  The policy operators already average any randomization internal to
the school's estimation rule; the displayed integral averages the remaining
test-score randomness.  The final equalities impose Definition 1's fixed point
by deriving all three estimates from the same taking and reporting functions
being optimized.
-/
def LG21Definition1ExactEquilibrium
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (requirementPolicy : LG21RequirementPolicy)
    (testLaw : Skill -> Base -> Measure Test)
    (takeDecision : Skill -> Base -> Bool)
    (reportDecision : Base -> Test -> Bool)
    (estimatedReportedPayoff : Base -> Test -> Real)
    (estimatedWithheldPayoff : Base -> Real)
    (estimatedNoTakePayoff : Base -> Real)
    (estimationPolicyReportedPayoff :
      (Skill -> Base -> Bool) -> (Base -> Test -> Bool) ->
        Base -> Test -> Real)
    (estimationPolicyWithheldPayoff :
      (Skill -> Base -> Bool) -> (Base -> Test -> Bool) -> Base -> Real)
    (estimationPolicyNoTakePayoff :
      (Skill -> Base -> Bool) -> (Base -> Test -> Bool) -> Base -> Real) : Prop :=
  (forall skill base, IsProbabilityMeasure (testLaw skill base)) /\
    (forall base, Measurable (reportDecision base)) /\
    (forall skill base,
      Integrable (fun test =>
        if reportDecision base test then
          estimatedReportedPayoff base test
        else estimatedWithheldPayoff base) (testLaw skill base)) /\
    (forall skill base test,
      LG21AccessAction.feasible
        (LG21RequirementPolicy.accessRequirement requirementPolicy)
        { takesTest := takeDecision skill base
          reportsScore :=
            takeDecision skill base && reportDecision base test }) /\
    (forall skill base (alternativeTake : Bool)
        (alternativeReport : Test -> Bool),
      (forall test,
        LG21AccessAction.feasible
          (LG21RequirementPolicy.accessRequirement requirementPolicy)
          { takesTest := alternativeTake
            reportsScore := alternativeTake && alternativeReport test }) ->
        Measurable alternativeReport ->
        (alternativeTake = true ->
          Integrable (fun test =>
            if alternativeReport test then
              estimatedReportedPayoff base test
            else estimatedWithheldPayoff base) (testLaw skill base)) ->
        (if alternativeTake then
            integral (testLaw skill base) (fun test =>
              if alternativeReport test then
                estimatedReportedPayoff base test
              else estimatedWithheldPayoff base)
          else estimatedNoTakePayoff base) <=
        (if takeDecision skill base then
            integral (testLaw skill base) (fun test =>
              if reportDecision base test then
                estimatedReportedPayoff base test
              else estimatedWithheldPayoff base)
          else estimatedNoTakePayoff base)) /\
    estimatedReportedPayoff =
      estimationPolicyReportedPayoff takeDecision reportDecision /\
    estimatedWithheldPayoff =
      estimationPolicyWithheldPayoff takeDecision reportDecision /\
    estimatedNoTakePayoff =
      estimationPolicyNoTakePayoff takeDecision reportDecision

/-! ## Pointwise voluntary schedules -/

/-- Realized continuation estimate after an optional test draw. -/
def lg21OptionalSourceContinuationPayoff
    {Base Test : Type*}
    (reportDecision : Base -> Test -> Bool)
    (reportedPayoff : Base -> Test -> Real)
    (noReportPayoff : Base -> Real)
    (base : Base) (test : Test) : Real :=
  if reportDecision base test then reportedPayoff base test
  else noReportPayoff base

/-- Ex-ante estimate from taking before the test score is realized. -/
def lg21OptionalSourceTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (testLaw : Skill -> Base -> Measure Test)
    (reportDecision : Base -> Test -> Bool)
    (reportedPayoff : Base -> Test -> Real)
    (noReportPayoff : Base -> Real)
    (skill : Skill) (base : Base) : Real :=
  integral (testLaw skill base) (fun test => lg21OptionalSourceContinuationPayoff
    reportDecision reportedPayoff noReportPayoff base test)

/--
Definition 1's two pointwise best-response clauses under optional reporting.
Taking is evaluated before the score draw and reporting after it.
-/
def LG21OptionalPointwiseBestResponses
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (testLaw : Skill -> Base -> Measure Test)
    (takeDecision : Skill -> Base -> Bool)
    (reportDecision : Base -> Test -> Bool)
    (reportedPayoff : Base -> Test -> Real)
    (noReportPayoff : Base -> Real) : Prop :=
  (forall base,
      NoProfitableBinaryChoiceDeviation
        (fun skill => takeDecision skill base = true)
        (fun skill => lg21OptionalSourceTakeExpectedPayoff testLaw
          reportDecision reportedPayoff noReportPayoff skill base)
        (fun _skill => noReportPayoff base)) /\
    forall base,
      NoProfitableBinaryChoiceDeviation
        (fun test => reportDecision base test = true)
        (reportedPayoff base)
        (fun _test => noReportPayoff base)

/-- Expected estimate from taking when every taken score must be reported. -/
def lg21ReportRequiredSourceTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (testLaw : Skill -> Base -> Measure Test)
    (reportedPayoff : Base -> Test -> Real)
    (skill : Skill) (base : Base) : Real :=
  integral (testLaw skill base) (reportedPayoff base)

/-- Definition 1's pointwise pre-score best response under required reporting. -/
def LG21ReportRequiredPointwiseBestResponse
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (testLaw : Skill -> Base -> Measure Test)
    (takeDecision : Skill -> Base -> Bool)
    (reportedPayoff : Base -> Test -> Real)
    (noReportPayoff : Base -> Real) : Prop :=
  forall base,
    NoProfitableBinaryChoiceDeviation
      (fun skill => takeDecision skill base = true)
      (fun skill => lg21ReportRequiredSourceTakeExpectedPayoff
        testLaw reportedPayoff skill base)
      (fun _skill => noReportPayoff base)

/-! ## Reuse of the checked pointwise proof kernels -/

/-- Package transparent optional primitives only inside the proof. -/
theorem lg21_optional_source_exact_cutoff_all_take_and_withholding
    {Base : Type*}
    (testLaw : Real -> Base -> Measure Real)
    (testLaw_isProbability :
      forall skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : Real -> Base -> Bool)
    (reportDecision : Base -> Real -> Bool)
    (reportedPayoff : Base -> Real -> Real)
    (noReportPayoff : Base -> Real)
    (continuationPayoff_integrable :
      forall skill base,
        Integrable
          (fun score => lg21OptionalSourceContinuationPayoff
            reportDecision reportedPayoff noReportPayoff base score)
          (testLaw skill base))
    (hbest : LG21OptionalPointwiseBestResponses testLaw takeDecision
      reportDecision reportedPayoff noReportPayoff)
    (scoreVariance : NNReal) (hvariance : scoreVariance ≠ 0)
    (htestLaw : forall skill base,
      testLaw skill base = gaussianReal skill scoreVariance)
    (intercept slope : Base -> Real)
    (hslope : forall base, 0 < slope base)
    (hreported : forall base score,
      reportedPayoff base score = intercept base + slope base * score)
    (htie : forall base score,
      reportedPayoff base score = noReportPayoff base ->
        reportDecision base score = true) :
    (forall skill base, takeDecision skill base = true) /\
      forall base,
        exists cutoff : Real,
          (forall score,
            reportDecision base score = true <-> cutoff <= score) /\
          forall skill,
            0 < testLaw skill base
              {score | reportDecision base score = false} := by
  let E : LG21OptionalSequentialEquilibriumData Real Base Real :=
    { testLaw := testLaw
      testLaw_isProbability := testLaw_isProbability
      takeDecision := takeDecision
      reportDecision := reportDecision
      reportedPayoff := reportedPayoff
      noReportPayoff := noReportPayoff
      continuationPayoff_integrable := by
        intro skill base
        simpa [lg21OptionalSequentialContinuationPayoff,
          lg21OptionalSourceContinuationPayoff] using
          continuationPayoff_integrable skill base
      estimationConsistent := True }
  have hEq : lg21OptionalSequentialEquilibrium E := by
    simpa [E, lg21OptionalSequentialEquilibrium,
      lg21OptionalSequentialTakeExpectedPayoff,
      lg21OptionalSequentialContinuationPayoff,
      LG21OptionalPointwiseBestResponses,
      lg21OptionalSourceTakeExpectedPayoff,
      lg21OptionalSourceContinuationPayoff] using
      And.intro hbest trivial
  constructor
  · intro skill base
    exact paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
      hEq base scoreVariance hvariance (fun skill => htestLaw skill base)
      (intercept base) (slope base) (hslope base) (hreported base) skill
  · intro base
    let cutoff := affineCutoff (intercept base) (slope base)
      (noReportPayoff base)
    refine ⟨cutoff, ?_, ?_⟩
    · intro score
      exact paper_theorem3_1_arbitrary_optional_sequential_equilibrium_exact_cutoff_of_tiebreak
        hEq base (intercept base) (slope base) (hslope base)
        (hreported base) (htie base) score
    · intro skill
      rw [htestLaw skill base]
      exact paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass_gaussian
        hEq base skill scoreVariance hvariance
        (intercept base) (slope base) (hslope base) (hreported base)

/-- Package transparent report-required primitives only inside the proof. -/
theorem lg21_report_required_source_exact_cutoff_and_withholding
    {Base Test : Type*} [MeasurableSpace Test]
    (testLaw : Real -> Base -> Measure Test)
    (testLaw_isProbability :
      forall skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : Real -> Base -> Bool)
    (reportedPayoff : Base -> Test -> Real)
    (noReportPayoff : Base -> Real)
    (reportedPayoff_integrable :
      forall skill base, Integrable (reportedPayoff base) (testLaw skill base))
    (hbest : LG21ReportRequiredPointwiseBestResponse testLaw takeDecision
      reportedPayoff noReportPayoff)
    (intercept slope : Base -> Real)
    (hslope : forall base, 0 < slope base)
    (htakePayoff : forall skill base,
      lg21ReportRequiredSourceTakeExpectedPayoff testLaw reportedPayoff
          skill base =
        intercept base + slope base * skill)
    (htie : forall skill base,
      lg21ReportRequiredSourceTakeExpectedPayoff testLaw reportedPayoff
          skill base = noReportPayoff base ->
        takeDecision skill base = true)
    (skillMean : Base -> Real) (skillVariance : NNReal)
    (hskillVariance : skillVariance ≠ 0) :
    forall base,
      exists cutoff : Real,
        (forall skill,
          takeDecision skill base = true <-> cutoff <= skill) /\
        0 < gaussianReal (skillMean base) skillVariance
          {skill | takeDecision skill base = false} := by
  let E : LG21ReportRequiredSequentialEquilibriumData Real Base Test :=
    { testLaw := testLaw
      testLaw_isProbability := testLaw_isProbability
      takeDecision := takeDecision
      reportedPayoff := reportedPayoff
      noReportPayoff := noReportPayoff
      reportedPayoff_integrable := reportedPayoff_integrable
      estimationConsistent := True }
  have hEq : lg21ReportRequiredSequentialEquilibrium E := by
    simpa [E, lg21ReportRequiredSequentialEquilibrium,
      lg21ReportRequiredSequentialTakeExpectedPayoff,
      LG21ReportRequiredPointwiseBestResponse,
      lg21ReportRequiredSourceTakeExpectedPayoff] using
      And.intro hbest trivial
  intro base
  let cutoff := affineCutoff (intercept base) (slope base)
    (noReportPayoff base)
  refine ⟨cutoff, ?_, ?_⟩
  · intro skill
    exact paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_exact_cutoff_of_tiebreak
      hEq base (intercept base) (slope base) (hslope base)
      (fun skill => htakePayoff skill base) (fun skill => htie skill base) skill
  · exact paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_withholding_mass_gaussian
      hEq base (skillMean base) skillVariance hskillVariance
      (intercept base) (slope base) (hslope base)
      (fun skill => htakePayoff skill base)

/--
Pointwise Lemma 4.1 for the two voluntary schedules.  The posterior-consistency
identities used in the source proof are explicit hypotheses; no active-branch
selection record appears in the reviewed statement.
-/
theorem lg21_observed_access_source_exact_all_take_and_report
    {Base : Type*}
    (optionalTestLaw : Real -> Base -> Measure Real)
    (optionalTestLaw_isProbability :
      forall skill base, IsProbabilityMeasure (optionalTestLaw skill base))
    (optionalTakeDecision : Real -> Base -> Bool)
    (optionalReportDecision : Base -> Real -> Bool)
    (optionalReportedPayoff : Base -> Real -> Real)
    (optionalNoReportPayoff : Base -> Real)
    (optionalContinuationIntegrable : forall skill base,
      Integrable
        (fun score => lg21OptionalSourceContinuationPayoff
          optionalReportDecision optionalReportedPayoff
          optionalNoReportPayoff base score)
        (optionalTestLaw skill base))
    (hOptionalBest : LG21OptionalPointwiseBestResponses optionalTestLaw
      optionalTakeDecision optionalReportDecision optionalReportedPayoff
      optionalNoReportPayoff)
    (optionalScoreLaw : Base -> GaussianScaleLaw)
    (optionalTestVariance : NNReal)
    (hOptionalVariance : optionalTestVariance ≠ 0)
    (hOptionalTestLaw : forall skill base,
      optionalTestLaw skill base = gaussianReal skill optionalTestVariance)
    (optionalIntercept optionalSlope : Base -> Real)
    (hOptionalSlope : forall base, 0 < optionalSlope base)
    (hOptionalReported : forall base score,
      optionalReportedPayoff base score =
        optionalIntercept base + optionalSlope base * score)
    (hOptionalNoReportConsistency : forall base,
      (forall skill, optionalTakeDecision skill base = true) ->
        forall cutoff : Real,
          (forall score, score < cutoff ->
            optionalReportDecision base score = false) ->
          ¬ (forall score, optionalReportDecision base score = true) ->
          optionalNoReportPayoff base =
            optionalIntercept base + optionalSlope base *
              standardGaussianLowerTailMean (optionalScoreLaw base) cutoff)
    {RequiredTest : Type*} [MeasurableSpace RequiredTest]
    (requiredTestLaw : Real -> Base -> Measure RequiredTest)
    (requiredTestLaw_isProbability : forall skill base,
      IsProbabilityMeasure (requiredTestLaw skill base))
    (requiredTakeDecision : Real -> Base -> Bool)
    (requiredReportedPayoff : Base -> RequiredTest -> Real)
    (requiredNoReportPayoff : Base -> Real)
    (requiredReportedIntegrable : forall skill base,
      Integrable (requiredReportedPayoff base) (requiredTestLaw skill base))
    (hRequiredBest : LG21ReportRequiredPointwiseBestResponse requiredTestLaw
      requiredTakeDecision requiredReportedPayoff requiredNoReportPayoff)
    (requiredSkillLaw : Base -> GaussianScaleLaw)
    (requiredWeight : Base -> Real)
    (hRequiredWeight : forall base, 0 < requiredWeight base)
    (hRequiredWeight_lt_one : forall base, requiredWeight base < 1)
    (hRequiredTakeExpected : forall skill base,
      lg21ReportRequiredSourceTakeExpectedPayoff requiredTestLaw
          requiredReportedPayoff skill base =
        lg21ObservedAccessReportedPosterior
          (requiredSkillLaw base).mean (requiredWeight base) skill)
    (hRequiredCutoffConsistency : forall base,
      ¬ (forall skill, requiredTakeDecision skill base = true) ->
        exists takingCutoff : Real,
          (forall skill, skill < takingCutoff ->
            requiredTakeDecision skill base = false) /\
          requiredNoReportPayoff base =
            standardGaussianLowerTailMean
              (requiredSkillLaw base) takingCutoff) :
    (forall skill base,
      optionalTakeDecision skill base = true) /\
      (forall base score,
        optionalReportDecision base score = true) /\
      forall skill base,
        requiredTakeDecision skill base = true := by
  let Eoptional : LG21OptionalSequentialEquilibriumData Real Base Real :=
    { testLaw := optionalTestLaw
      testLaw_isProbability := optionalTestLaw_isProbability
      takeDecision := optionalTakeDecision
      reportDecision := optionalReportDecision
      reportedPayoff := optionalReportedPayoff
      noReportPayoff := optionalNoReportPayoff
      continuationPayoff_integrable := by
        intro skill base
        simpa [lg21OptionalSequentialContinuationPayoff,
          lg21OptionalSourceContinuationPayoff] using
          optionalContinuationIntegrable skill base
      estimationConsistent := True }
  let Erequired : LG21ReportRequiredSequentialEquilibriumData Real Base RequiredTest :=
    { testLaw := requiredTestLaw
      testLaw_isProbability := requiredTestLaw_isProbability
      takeDecision := requiredTakeDecision
      reportedPayoff := requiredReportedPayoff
      noReportPayoff := requiredNoReportPayoff
      reportedPayoff_integrable := requiredReportedIntegrable
      estimationConsistent := True }
  have hOptionalEq : lg21OptionalSequentialEquilibrium Eoptional := by
    simpa [Eoptional, lg21OptionalSequentialEquilibrium,
      lg21OptionalSequentialTakeExpectedPayoff,
      lg21OptionalSequentialContinuationPayoff,
      LG21OptionalPointwiseBestResponses,
      lg21OptionalSourceTakeExpectedPayoff,
      lg21OptionalSourceContinuationPayoff] using
      And.intro hOptionalBest trivial
  have hRequiredEq : lg21ReportRequiredSequentialEquilibrium Erequired := by
    simpa [Erequired, lg21ReportRequiredSequentialEquilibrium,
      lg21ReportRequiredSequentialTakeExpectedPayoff,
      LG21ReportRequiredPointwiseBestResponse,
      lg21ReportRequiredSourceTakeExpectedPayoff] using
      And.intro hRequiredBest trivial
  have hOptionalTake : forall skill base,
      optionalTakeDecision skill base = true := by
    intro skill base
    exact paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
      hOptionalEq base optionalTestVariance hOptionalVariance
      (fun skill => hOptionalTestLaw skill base)
      (optionalIntercept base) (optionalSlope base) (hOptionalSlope base)
      (hOptionalReported base) skill
  have hOptionalReport : forall base score,
      optionalReportDecision base score = true := by
    intro base score
    exact paper_lemma4_1_arbitrary_optional_sequential_equilibrium_all_report
      hOptionalEq base (optionalScoreLaw base)
      (optionalIntercept base) (optionalSlope base) (hOptionalSlope base)
      (hOptionalReported base)
      (hOptionalNoReportConsistency base (fun skill => hOptionalTake skill base))
      score
  have hRequiredTake : forall skill base,
      requiredTakeDecision skill base = true := by
    intro skill base
    exact paper_lemma4_1_arbitrary_report_required_sequential_equilibrium_all_take
      hRequiredEq base (requiredSkillLaw base) (requiredWeight base)
      (hRequiredWeight base) (hRequiredWeight_lt_one base)
      (fun skill => hRequiredTakeExpected skill base)
      (hRequiredCutoffConsistency base) skill
  exact ⟨hOptionalTake, hOptionalReport, hRequiredTake⟩

/-! ## Definition 6 and Theorem 4.4 -/

/--
Definition 6 with both information branches explicit.  An access student's
Bayesian estimate is measurable with respect to the report-dependent
information `(base, X, score-if-reported)`.  A no-access student receives an
independent synthetic score from the conditional test law given the first
`K - 1` features, and the policy outputs the Bayesian posterior mean after
adding that draw.  The final kernel identity is the induced randomized output
law, rather than merely a stored score kernel.
-/
structure LG21Definition6ExactResamplingPolicy
    (Omega Base Test : Type*) [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test] where
  /-- The source population on which latent skill and the observed features live. -/
  studentLaw : Measure Omega
  studentLaw_isProbability : IsProbabilityMeasure studentLaw
  latentSkill : Omega -> Real
  baseObservation : Omega -> Base
  testObservation : Omega -> Test
  /-- Whether an access student reports the realized test score. -/
  reportObservation : Omega -> Bool
  baseTestObservation_measurable : Measurable (fun omega : Omega =>
    (baseObservation omega, testObservation omega))
  latentSkill_integrable : Integrable latentSkill studentLaw
  /--
  Access-side estimator on the source information set.  The optional score is
  present exactly on the reporting branch, so the withheld branch cannot
  condition on a hidden realized score.
  -/
  accessPosteriorEstimate : Base -> Bool -> (Unit ⊕ Test) -> Real
  accessPosteriorEstimate_is_conditionalSkillMean :
    (fun omega => accessPosteriorEstimate
        (baseObservation omega) (reportObservation omega)
        (if reportObservation omega then
          Sum.inr (testObservation omega)
        else Sum.inl ())) =ᵐ[
      studentLaw]
      studentLaw[latentSkill |
        MeasurableSpace.comap
          (fun omega =>
            (baseObservation omega,
              (reportObservation omega,
                if reportObservation omega then
                  Sum.inr (testObservation omega)
                else Sum.inl ())))
          inferInstance]
  /-- The law of the first `K - 1` features. -/
  baseLaw : Measure Base
  /-- The actual conditional law of the test score given those features. -/
  testGivenBase : Kernel Base Test
  testGivenBase_isMarkov : IsMarkovKernel testGivenBase
  actual_base_test_law :
    studentLaw.map (fun omega =>
        (baseObservation omega, testObservation omega)) =
      Measure.bind baseLaw (Kernel.id ×ₖ testGivenBase)
  /-- Bayesian estimator after a base profile and a present score are observed. -/
  posteriorEstimate : Base -> Test -> Real
  posteriorEstimate_measurable : Measurable (fun z : Base × Test =>
    posteriorEstimate z.1 z.2)
  /-- The estimator is genuinely a Bayesian conditional mean of latent skill. -/
  posteriorEstimate_is_conditionalSkillMean :
    (fun omega => posteriorEstimate
        (baseObservation omega) (testObservation omega)) =ᵐ[studentLaw]
      studentLaw[latentSkill |
        MeasurableSpace.comap
          (fun omega => (baseObservation omega, testObservation omega))
          inferInstance]
  /-- The reported access branch uses that same base-and-score posterior. -/
  access_reported_estimate_eq :
    forall base test,
      accessPosteriorEstimate base true (Sum.inr test) =
        posteriorEstimate base test
  /-- The randomized no-access output law induced by the synthetic draw. -/
  noAccessEstimateKernel : Kernel Base Real
  noAccessEstimateKernel_isMarkov : IsMarkovKernel noAccessEstimateKernel
  noAccessEstimateKernel_eq :
    noAccessEstimateKernel =
      (Kernel.id ×ₖ testGivenBase).map
        (fun z => posteriorEstimate z.1 z.2)

attribute [instance] LG21Definition6ExactResamplingPolicy.testGivenBase_isMarkov

/--
The access-side estimate law induced by the source information actually
observed for each access student.  A reported score is present in the input to
the Bayesian estimator exactly when `reportObservation` is true; the withheld
branch therefore cannot use the realized score.
-/
def lg21Definition6ExactObservedAccessEstimateLaw
    {Omega Base Test : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test]
    (policy : LG21Definition6ExactResamplingPolicy Omega Base Test)
    (_hAccessEstimateMeasurable : AEMeasurable (fun omega =>
      policy.accessPosteriorEstimate
        (policy.baseObservation omega) (policy.reportObservation omega)
        (if policy.reportObservation omega then
          Sum.inr (policy.testObservation omega)
        else Sum.inl ())) policy.studentLaw) : Measure Real :=
  policy.studentLaw.map (fun omega =>
    policy.accessPosteriorEstimate
      (policy.baseObservation omega) (policy.reportObservation omega)
      (if policy.reportObservation omega then
        Sum.inr (policy.testObservation omega)
      else Sum.inl ()))

/-- No-access synthetic-score conditional estimate law in Definition 6. -/
def lg21Definition6ExactNoAccessEstimateKernel
    {Omega Base Test : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test]
    (policy : LG21Definition6ExactResamplingPolicy Omega Base Test) : Kernel Base Real :=
  policy.noAccessEstimateKernel

/--
After Lemma 4.1's all-report conclusion, the access branch uses the actual
base-conditioned score and full-score posterior.  Definition 6 gives the
no-access branch exactly the same conditional output law by resampling that
score, so the two laws agree pointwise and after mixing over base profiles.
-/
theorem lg21Definition6ExactResamplingPolicy_fair
    {Omega Base Test : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test]
    (policy : LG21Definition6ExactResamplingPolicy Omega Base Test)
    (baseLaw : Measure Base) :
    (forall base,
      ((Kernel.id ×ₖ policy.testGivenBase).map
          (fun z => policy.posteriorEstimate z.1 z.2)) base =
        lg21Definition6ExactNoAccessEstimateKernel policy base) /\
      Measure.bind baseLaw
          ((Kernel.id ×ₖ policy.testGivenBase).map
            (fun z => policy.posteriorEstimate z.1 z.2)) =
        Measure.bind baseLaw (lg21Definition6ExactNoAccessEstimateKernel policy) := by
  constructor
  · intro base
    rw [lg21Definition6ExactNoAccessEstimateKernel,
      policy.noAccessEstimateKernel_eq]
  · rw [lg21Definition6ExactNoAccessEstimateKernel,
      policy.noAccessEstimateKernel_eq]

end

end LG21TestOptionalPolicies
