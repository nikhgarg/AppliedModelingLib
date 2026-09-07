import LG21TestOptionalPolicies.Theorem32RandomizedPolicy
import LG21TestOptionalPolicies.SequentialEquilibrium
import AppliedModelingLib.Foundations.Probability.GaussianMathlib
import Mathlib.Probability.ConditionalProbability

/-!
# A Gaussian policy-surface diagnostic for LG21 Theorem 3.2

The finite countermodel in `Theorem32RandomizedPolicy` isolates the logical
problem with identifying an output distribution from its mean.  This file
records the corresponding Gaussian policy surface and the equilibrium-indexed
conditional reporter mixture used by the exact construction.

We use the source model with one optional feature: latent skill is Gaussian,
test noise is an independent Gaussian, and the potential test score is their
sum.  Every reported-score output law has expected estimate zero, but the law
depends on the sign of the real test score.  For every measurable equilibrium
reporter event, the no-report/no-access law is computed by one uniform rule:
it is the mixture of the two output laws among that equilibrium's reporters
(with the zero law as the source's zero-reporter fallback).  Giving the same
mixture to nonreporters makes the whole access-side law equal the no-access
law in every equilibrium.

The observable-access field in this module is intentionally only an algebraic
surface diagnostic: it mixes the reporter aggregate with itself.  It must not
be used as source-domain theorem credit on its own.  The companion
`Theorem32GaussianKernelCounterexample` module defines one score estimator
kernel, derives the operational access population law by binding the Gaussian
population to that kernel, and only there proves the exact counterexample.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## Measurable source strategies and the Gaussian population -/

/--
All measurable pure strategy profiles in the one-feature Gaussian source
model.  The test-taking decision is made from latent skill; reporting is made
after observing the realized real test score.
-/
structure LG21GaussianRandomizedPolicyEquilibrium where
  takeDecision : ℝ → Bool
  reportDecision : ℝ → Bool
  takeDecision_measurable : Measurable takeDecision
  reportDecision_measurable : Measurable reportDecision

/-- Independent Gaussian latent skill and optional-test noise. -/
def lg21GaussianRandomizedPrimitiveLaw
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal) :
    Measure (ℝ × ℝ) :=
  (gaussianReal priorMean priorVariance).prod
    (gaussianReal 0 noiseVariance)

theorem lg21GaussianRandomizedPrimitiveLaw_isProbability
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal) :
    IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) := by
  unfold lg21GaussianRandomizedPrimitiveLaw
  infer_instance

/-- The source potential test score `theta = q + epsilon`. -/
def lg21GaussianRandomizedPotentialTest (student : ℝ × ℝ) : ℝ :=
  student.1 + student.2

theorem lg21GaussianRandomizedPotentialTest_measurable :
    Measurable lg21GaussianRandomizedPotentialTest := by
  simpa [lg21GaussianRandomizedPotentialTest] using
    (measurable_fst.add measurable_snd)

/-- Students who both take and report in the supplied strategy profile. -/
def lg21GaussianRandomizedReporterEvent
    (E : LG21GaussianRandomizedPolicyEquilibrium) : Set (ℝ × ℝ) :=
  {student |
    E.takeDecision student.1 = true ∧
      E.reportDecision (lg21GaussianRandomizedPotentialTest student) = true}

theorem lg21GaussianRandomizedReporterEvent_measurable
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    MeasurableSet (lg21GaussianRandomizedReporterEvent E) := by
  have htake :
      Measurable (fun student : ℝ × ℝ => E.takeDecision student.1) :=
    E.takeDecision_measurable.comp measurable_fst
  have hreport :
      Measurable
        (fun student : ℝ × ℝ =>
          E.reportDecision (lg21GaussianRandomizedPotentialTest student)) :=
    E.reportDecision_measurable.comp
      lg21GaussianRandomizedPotentialTest_measurable
  exact
    (htake (measurableSet_singleton true)).inter
      (hreport (measurableSet_singleton true))

/-- Population states whose potential real test score is nonnegative. -/
def lg21GaussianRandomizedHighScoreEvent : Set (ℝ × ℝ) :=
  {student | 0 ≤ lg21GaussianRandomizedPotentialTest student}

theorem lg21GaussianRandomizedHighScoreEvent_measurable :
    MeasurableSet lg21GaussianRandomizedHighScoreEvent := by
  exact measurableSet_Ici.preimage
    lg21GaussianRandomizedPotentialTest_measurable

/-! ## The uniform conditional-reporter-mixture operator -/

/-- Probability of an event, represented in the `NNReal` mixture API. -/
def lg21EventProbabilityNNReal
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (event : Set Outcome) : NNReal :=
  (law event).toNNReal

theorem lg21EventProbabilityNNReal_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (event : Set Outcome) :
    lg21EventProbabilityNNReal law event ≤ 1 := by
  unfold lg21EventProbabilityNNReal
  have hle : law event ≤ (1 : ENNReal) := by
    calc
      law event ≤ law Set.univ := measure_mono (Set.subset_univ event)
      _ = 1 := measure_univ
  simpa using
    (ENNReal.toNNReal_mono (a := law event) (b := 1) (by norm_num) hle)

/--
Conditional probability of `highEvent` among reporters.  When the reporter
event has zero mass, the source treats the equilibrium as test-blank; the
operator therefore uses the zero-law fallback weight `0`.
-/
def lg21ReporterHighShareNNReal
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (reporterEvent highEvent : Set Outcome) : NNReal :=
  if law reporterEvent = 0 then
    0
  else
    ((ProbabilityTheory.cond law reporterEvent) highEvent).toNNReal

theorem lg21ReporterHighShareNNReal_le_one
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (reporterEvent highEvent : Set Outcome) :
    lg21ReporterHighShareNNReal law reporterEvent highEvent ≤ 1 := by
  by_cases hzero : law reporterEvent = 0
  · simp [lg21ReporterHighShareNNReal, hzero]
  · letI : IsProbabilityMeasure
        (ProbabilityTheory.cond law reporterEvent) :=
      cond_isProbabilityMeasure_of_finite hzero (measure_ne_top law reporterEvent)
    simpa [lg21ReporterHighShareNNReal, hzero] using
      (lg21EventProbabilityNNReal_le_one
        (ProbabilityTheory.cond law reporterEvent) highEvent)

/--
The single policy rule used at every equilibrium: mix the high-score and
low-score randomized output laws according to their conditional reporter
share, with the low-score zero law as the no-reporter fallback.
-/
def lg21ConditionalReporterOutputLaw
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (reporterEvent highEvent : Set Outcome) :
    PMF LG21RandomizedCounterexampleEstimate :=
  lg21BinaryMixturePMF
    (lg21ReporterHighShareNNReal law reporterEvent highEvent)
    (lg21ReporterHighShareNNReal_le_one law reporterEvent highEvent)
    lg21RandomizedCounterexampleSymmetricLaw
    lg21RandomizedCounterexampleZeroLaw

/--
The access population is the reporter aggregate on the reporter branch and
the same resampled aggregate on the nonreporter branch.  This is the source's
conditional-reporter-mixture construction at the two population branches.
-/
def lg21ReporterResampledAccessOutputLaw
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (reporterEvent highEvent : Set Outcome) :
    PMF LG21RandomizedCounterexampleEstimate :=
  let aggregate :=
    lg21ConditionalReporterOutputLaw law reporterEvent highEvent
  lg21BinaryMixturePMF
    (lg21EventProbabilityNNReal law reporterEvent)
    (lg21EventProbabilityNNReal_le_one law reporterEvent)
    aggregate aggregate

/-- The whole access law equals the resampled no-access law in every event. -/
theorem lg21ReporterResampledAccessOutputLaw_eq_conditionalReporterOutputLaw
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (reporterEvent highEvent : Set Outcome) :
    lg21ReporterResampledAccessOutputLaw law reporterEvent highEvent =
      lg21ConditionalReporterOutputLaw law reporterEvent highEvent := by
  unfold lg21ReporterResampledAccessOutputLaw
  exact
    lg21BinaryMixturePMF_eq_noReporter_of_eq
      (lg21EventProbabilityNNReal law reporterEvent)
      (lg21EventProbabilityNNReal_le_one law reporterEvent)
      (lg21ConditionalReporterOutputLaw law reporterEvent highEvent)
      (lg21ConditionalReporterOutputLaw law reporterEvent highEvent) rfl

/-- Both score-dependent randomized laws have expected estimate zero. -/
theorem lg21GaussianRandomizedFullFeatureLaw_mean_zero (score : ℝ) :
    pmfExp
        (if 0 ≤ score then
          lg21RandomizedCounterexampleSymmetricLaw
        else
          lg21RandomizedCounterexampleZeroLaw)
        lg21RandomizedCounterexampleEstimateValue =
      0 := by
  by_cases hscore : 0 ≤ score <;> simp [hscore]

/-- Every conditional reporter mixture also has expected estimate zero. -/
theorem lg21ConditionalReporterOutputLaw_mean_zero
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (reporterEvent highEvent : Set Outcome) :
    pmfExp
        (lg21ConditionalReporterOutputLaw law reporterEvent highEvent)
        lg21RandomizedCounterexampleEstimateValue =
      0 := by
  unfold lg21ConditionalReporterOutputLaw
  exact
    lg21_pmfExp_binaryMixture_eq_zero_of_component_means_zero
      (lg21ReporterHighShareNNReal law reporterEvent highEvent)
      (lg21ReporterHighShareNNReal_le_one law reporterEvent highEvent)
      lg21RandomizedCounterexampleSymmetricLaw
      lg21RandomizedCounterexampleZeroLaw
      lg21RandomizedCounterexampleEstimateValue
      lg21RandomizedCounterexampleSymmetricLaw_mean
      lg21RandomizedCounterexampleZeroLaw_mean

/-! ## Global and skill-conditioned source laws -/

def lg21GaussianRandomizedGlobalReporterAggregate
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    PMF LG21RandomizedCounterexampleEstimate := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  exact
    lg21ConditionalReporterOutputLaw
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance)
      (lg21GaussianRandomizedReporterEvent E)
      lg21GaussianRandomizedHighScoreEvent

def lg21GaussianRandomizedGlobalAccessLaw
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    PMF LG21RandomizedCounterexampleEstimate := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  exact
    lg21ReporterResampledAccessOutputLaw
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance)
      (lg21GaussianRandomizedReporterEvent E)
      lg21GaussianRandomizedHighScoreEvent

theorem lg21GaussianRandomizedGlobalAccessLaw_eq_aggregate
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    lg21GaussianRandomizedGlobalAccessLaw
        priorMean priorVariance noiseVariance E =
      lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance E := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  exact
    lg21ReporterResampledAccessOutputLaw_eq_conditionalReporterOutputLaw
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance)
      (lg21GaussianRandomizedReporterEvent E)
      lg21GaussianRandomizedHighScoreEvent

/-- Reporter event conditional on a fixed latent skill. -/
def lg21GaussianRandomizedReporterNoiseEvent
    (E : LG21GaussianRandomizedPolicyEquilibrium) (skill : ℝ) : Set ℝ :=
  {noise |
    E.takeDecision skill = true ∧
      E.reportDecision (skill + noise) = true}

theorem lg21GaussianRandomizedReporterNoiseEvent_measurable
    (E : LG21GaussianRandomizedPolicyEquilibrium) (skill : ℝ) :
    MeasurableSet (lg21GaussianRandomizedReporterNoiseEvent E skill) := by
  by_cases htakes : E.takeDecision skill = true
  · have hreport : Measurable (fun noise : ℝ => E.reportDecision (skill + noise)) :=
      E.reportDecision_measurable.comp (measurable_const.add measurable_id)
    rw [lg21GaussianRandomizedReporterNoiseEvent]
    simp only [htakes, true_and]
    exact hreport (measurableSet_singleton true)
  · simp [lg21GaussianRandomizedReporterNoiseEvent, htakes]

/-- High-score event conditional on fixed skill. -/
def lg21GaussianRandomizedHighNoiseEvent (skill : ℝ) : Set ℝ :=
  {noise | 0 ≤ skill + noise}

theorem lg21GaussianRandomizedHighNoiseEvent_measurable (skill : ℝ) :
    MeasurableSet (lg21GaussianRandomizedHighNoiseEvent skill) := by
  exact measurableSet_Ici.preimage (measurable_const.add measurable_id)

def lg21GaussianRandomizedLatentAccessLaw
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) (skill : ℝ) :
    PMF LG21RandomizedCounterexampleEstimate :=
  lg21BinaryMixturePMF
    (lg21EventProbabilityNNReal
      (gaussianReal 0 noiseVariance)
      (lg21GaussianRandomizedReporterNoiseEvent E skill))
    (lg21EventProbabilityNNReal_le_one
      (gaussianReal 0 noiseVariance)
      (lg21GaussianRandomizedReporterNoiseEvent E skill))
    (lg21ConditionalReporterOutputLaw
      (gaussianReal 0 noiseVariance)
      (lg21GaussianRandomizedReporterNoiseEvent E skill)
      (lg21GaussianRandomizedHighNoiseEvent skill))
    (lg21GaussianRandomizedGlobalReporterAggregate
      priorMean priorVariance noiseVariance E)

/-! ## The actual Gaussian policy surface -/

/--
The uniform randomized policy on the inherited Gaussian source model.  Its
observable and demographic access laws are the actual reporter/nonreporter
mixtures; no-access students receive the same equilibrium-specific reporter
aggregate.  At a fixed latent skill, reporters use the skill-conditional
score mixture while nonreporters still receive the single global base-only
law, as the school cannot condition that branch on unobserved skill.  The
full-feature law remains score-dependent.
-/
def lg21GaussianRandomizedPolicySurface
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal) :
    LG21SourcePolicySurface
      ℝ PUnit ℝ LG21RandomizedCounterexampleEstimate where
  Equilibrium := LG21GaussianRandomizedPolicyEquilibrium
  latentAccessEstimate := fun E skill _base =>
    lg21GaussianRandomizedLatentAccessLaw
      priorMean priorVariance noiseVariance E skill
  latentNoAccessEstimate := fun E _skill _base =>
    lg21GaussianRandomizedGlobalReporterAggregate
      priorMean priorVariance noiseVariance E
  observableAccessEstimate := fun E _base =>
    lg21GaussianRandomizedGlobalAccessLaw
      priorMean priorVariance noiseVariance E
  observableNoAccessEstimate := fun E _base =>
    lg21GaussianRandomizedGlobalReporterAggregate
      priorMean priorVariance noiseVariance E
  demographicAccessEstimate := fun E =>
    lg21GaussianRandomizedGlobalAccessLaw
      priorMean priorVariance noiseVariance E
  demographicNoAccessEstimate := fun E =>
    lg21GaussianRandomizedGlobalReporterAggregate
      priorMean priorVariance noiseVariance E
  baseOnlyEstimate := fun E _base =>
    lg21GaussianRandomizedGlobalReporterAggregate
      priorMean priorVariance noiseVariance E
  fullFeatureEstimate := fun _E _base score =>
    if 0 ≤ score then
      lg21RandomizedCounterexampleSymmetricLaw
    else
      lg21RandomizedCounterexampleZeroLaw

/-- Observable fairness holds for every measurable pure equilibrium. -/
theorem lg21GaussianRandomizedPolicySurface_observablyFair
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal) :
    lg21SourceObservablyFair
      (lg21GaussianRandomizedPolicySurface
        priorMean priorVariance noiseVariance) := by
  intro E _base
  exact
    lg21GaussianRandomizedGlobalAccessLaw_eq_aggregate
      priorMean priorVariance noiseVariance E

/-- Demographic fairness follows from the same exact population mixture. -/
theorem lg21GaussianRandomizedPolicySurface_demographicallyFair
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal) :
    lg21SourceDemographicallyFair
      (lg21GaussianRandomizedPolicySurface
        priorMean priorVariance noiseVariance) := by
  intro E
  exact
    lg21GaussianRandomizedGlobalAccessLaw_eq_aggregate
      priorMean priorVariance noiseVariance E

/-! ## Every measurable strategy is a source-timed weak equilibrium -/

/--
Concrete estimator consistency for the Gaussian counterexample.  The
base-only, full-feature, observable-access, and observable-no-access laws in
the strategic game are exactly the laws generated by the one uniform policy
surface above; this is not an unconstrained Boolean consistency flag.
-/
def lg21GaussianRandomizedEstimationConsistent
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) : Prop :=
  let S : LG21SourcePolicySurface
      ℝ PUnit.{1} ℝ LG21RandomizedCounterexampleEstimate :=
    lg21GaussianRandomizedPolicySurface
      priorMean priorVariance noiseVariance
  S.baseOnlyEstimate E PUnit.unit =
      lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance E ∧
    (∀ skill,
      S.latentAccessEstimate E skill PUnit.unit =
        lg21GaussianRandomizedLatentAccessLaw
          priorMean priorVariance noiseVariance E skill) ∧
    (∀ skill,
      S.latentNoAccessEstimate E skill PUnit.unit =
        lg21GaussianRandomizedGlobalReporterAggregate
          priorMean priorVariance noiseVariance E) ∧
    (∀ score,
      S.fullFeatureEstimate E PUnit.unit score =
        if 0 ≤ score then
          lg21RandomizedCounterexampleSymmetricLaw
        else
          lg21RandomizedCounterexampleZeroLaw) ∧
    S.observableAccessEstimate E PUnit.unit =
      lg21GaussianRandomizedGlobalAccessLaw
        priorMean priorVariance noiseVariance E ∧
    S.observableNoAccessEstimate E PUnit.unit =
      lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance E

theorem lg21GaussianRandomizedEstimationConsistent_holds
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    lg21GaussianRandomizedEstimationConsistent
      priorMean priorVariance noiseVariance E := by
  simp [lg21GaussianRandomizedEstimationConsistent,
    lg21GaussianRandomizedPolicySurface]

def lg21GaussianRandomizedSequentialEquilibriumData
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    LG21OptionalSequentialEquilibriumData ℝ PUnit ℝ where
  testLaw := fun skill _base => gaussianReal skill noiseVariance
  testLaw_isProbability := by
    intro skill base
    infer_instance
  takeDecision := fun skill _base => E.takeDecision skill
  reportDecision := fun _base score => E.reportDecision score
  reportedPayoff := fun _base score =>
    pmfExp
      (if 0 ≤ score then
        lg21RandomizedCounterexampleSymmetricLaw
      else
        lg21RandomizedCounterexampleZeroLaw)
      lg21RandomizedCounterexampleEstimateValue
  noReportPayoff := fun _base =>
    pmfExp
      (lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance E)
      lg21RandomizedCounterexampleEstimateValue
  continuationPayoff_integrable := by
    intro skill base
    have hreported :
        ∀ score : ℝ,
          pmfExp
              (if 0 ≤ score then
                lg21RandomizedCounterexampleSymmetricLaw
              else
                lg21RandomizedCounterexampleZeroLaw)
              lg21RandomizedCounterexampleEstimateValue =
            0 :=
      lg21GaussianRandomizedFullFeatureLaw_mean_zero
    have hnoReport :
        pmfExp
            (lg21GaussianRandomizedGlobalReporterAggregate
              priorMean priorVariance noiseVariance E)
            lg21RandomizedCounterexampleEstimateValue =
          0 := by
      letI : IsProbabilityMeasure
          (lg21GaussianRandomizedPrimitiveLaw
            priorMean priorVariance noiseVariance) :=
        lg21GaussianRandomizedPrimitiveLaw_isProbability
          priorMean priorVariance noiseVariance
      exact
        lg21ConditionalReporterOutputLaw_mean_zero
          (lg21GaussianRandomizedPrimitiveLaw
            priorMean priorVariance noiseVariance)
          (lg21GaussianRandomizedReporterEvent E)
          lg21GaussianRandomizedHighScoreEvent
    simpa [lg21OptionalSequentialContinuationPayoff, hreported, hnoReport]
      using (integrable_zero : Integrable (fun _score : ℝ => (0 : ℝ))
        (gaussianReal skill noiseVariance))
  estimationConsistent :=
    lg21GaussianRandomizedEstimationConsistent
      priorMean priorVariance noiseVariance E

@[simp] theorem lg21GaussianRandomizedSequential_reportedPayoff_eq_zero
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) (score : ℝ) :
    (lg21GaussianRandomizedSequentialEquilibriumData
      priorMean priorVariance noiseVariance E).reportedPayoff
        PUnit.unit score = 0 := by
  exact lg21GaussianRandomizedFullFeatureLaw_mean_zero score

@[simp] theorem lg21GaussianRandomizedSequential_noReportPayoff_eq_zero
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    (lg21GaussianRandomizedSequentialEquilibriumData
      priorMean priorVariance noiseVariance E).noReportPayoff PUnit.unit = 0 := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  exact
    lg21ConditionalReporterOutputLaw_mean_zero
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance)
      (lg21GaussianRandomizedReporterEvent E)
      lg21GaussianRandomizedHighScoreEvent

@[simp] theorem lg21GaussianRandomizedSequential_takeExpectedPayoff_eq_zero
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) (skill : ℝ) :
    lg21OptionalSequentialTakeExpectedPayoff
        (lg21GaussianRandomizedSequentialEquilibriumData
          priorMean priorVariance noiseVariance E)
        skill PUnit.unit =
      0 := by
  simp [lg21OptionalSequentialTakeExpectedPayoff,
    lg21OptionalSequentialContinuationPayoff]

/-- Every measurable pure strategy profile is a Definition 1 weak equilibrium. -/
theorem lg21GaussianRandomized_every_measurable_strategy_sequential_equilibrium
    (priorMean : ℝ) (priorVariance noiseVariance : NNReal)
    (E : LG21GaussianRandomizedPolicyEquilibrium) :
    lg21OptionalSequentialEquilibrium
      (lg21GaussianRandomizedSequentialEquilibriumData
        priorMean priorVariance noiseVariance E) := by
  constructor
  · rintro ⟨⟩
    constructor
    · intro skill _htakes
      dsimp only
      rw [lg21GaussianRandomizedSequential_noReportPayoff_eq_zero,
        lg21GaussianRandomizedSequential_takeExpectedPayoff_eq_zero]
    · intro skill _hnotTake
      dsimp only
      rw [lg21GaussianRandomizedSequential_takeExpectedPayoff_eq_zero,
        lg21GaussianRandomizedSequential_noReportPayoff_eq_zero]
  · constructor
    · rintro ⟨⟩
      constructor
      · intro score _hreports
        rw [lg21GaussianRandomizedSequential_noReportPayoff_eq_zero,
          lg21GaussianRandomizedSequential_reportedPayoff_eq_zero]
      · intro score _hnotReport
        rw [lg21GaussianRandomizedSequential_reportedPayoff_eq_zero,
          lg21GaussianRandomizedSequential_noReportPayoff_eq_zero]
    · exact
        lg21GaussianRandomizedEstimationConsistent_holds
          priorMean priorVariance noiseVariance E

/-! ## Nonblank report-all Gaussian equilibrium -/

def lg21GaussianRandomizedReportAllEquilibrium :
    LG21GaussianRandomizedPolicyEquilibrium where
  takeDecision := fun _skill => true
  reportDecision := fun _score => true
  takeDecision_measurable := measurable_const
  reportDecision_measurable := measurable_const

theorem lg21GaussianRandomizedReportAll_reporterEvent :
    lg21GaussianRandomizedReporterEvent
        lg21GaussianRandomizedReportAllEquilibrium =
      Set.univ := by
  ext student
  simp [lg21GaussianRandomizedReporterEvent,
    lg21GaussianRandomizedReportAllEquilibrium]

/-- Positive Gaussian mass on nonnegative potential scores. -/
theorem lg21GaussianRandomizedHighScoreEvent_pos
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    0 < lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance
        lg21GaussianRandomizedHighScoreEvent := by
  have hskill :
      0 < gaussianReal priorMean priorVariance (Set.Ioo 0 1) :=
    gaussianReal_Ioo_pos priorMean hpriorVariance (by norm_num)
  have hnoise :
      0 < gaussianReal 0 noiseVariance (Set.Ioo 0 1) :=
    gaussianReal_Ioo_pos 0 hnoiseVariance (by norm_num)
  have hrectangle :
      0 < lg21GaussianRandomizedPrimitiveLaw
          priorMean priorVariance noiseVariance
          (Set.Ioo 0 1 ×ˢ Set.Ioo 0 1) := by
    have hprod :
        0 < gaussianReal priorMean priorVariance (Set.Ioo 0 1) *
          gaussianReal 0 noiseVariance (Set.Ioo 0 1) :=
      ENNReal.mul_pos hskill.ne' hnoise.ne'
    simpa [lg21GaussianRandomizedPrimitiveLaw, Measure.prod_prod] using hprod
  apply lt_of_lt_of_le hrectangle
  apply measure_mono
  intro student hstudent
  rcases hstudent with ⟨hskillRange, hnoiseRange⟩
  rcases hskillRange with ⟨hskillLower, hskillUpper⟩
  rcases hnoiseRange with ⟨hnoiseLower, hnoiseUpper⟩
  change 0 ≤ student.1 + student.2
  linarith

/-- Positive Gaussian mass on negative potential scores as well. -/
theorem lg21GaussianRandomizedNegativeScoreEvent_pos
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    0 < lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance
        {student | lg21GaussianRandomizedPotentialTest student < 0} := by
  have hskill :
      0 < gaussianReal priorMean priorVariance (Set.Ioo (-1) 0) :=
    gaussianReal_Ioo_pos priorMean hpriorVariance (by norm_num)
  have hnoise :
      0 < gaussianReal 0 noiseVariance (Set.Ioo (-1) 0) :=
    gaussianReal_Ioo_pos 0 hnoiseVariance (by norm_num)
  have hrectangle :
      0 < lg21GaussianRandomizedPrimitiveLaw
          priorMean priorVariance noiseVariance
          (Set.Ioo (-1) 0 ×ˢ Set.Ioo (-1) 0) := by
    have hprod :
        0 < gaussianReal priorMean priorVariance (Set.Ioo (-1) 0) *
          gaussianReal 0 noiseVariance (Set.Ioo (-1) 0) :=
      ENNReal.mul_pos hskill.ne' hnoise.ne'
    simpa [lg21GaussianRandomizedPrimitiveLaw, Measure.prod_prod] using hprod
  apply lt_of_lt_of_le hrectangle
  apply measure_mono
  intro student hstudent
  rcases hstudent with ⟨hskillRange, hnoiseRange⟩
  rcases hskillRange with ⟨hskillLower, hskillUpper⟩
  rcases hnoiseRange with ⟨hnoiseLower, hnoiseUpper⟩
  change student.1 + student.2 < 0
  linarith

theorem lg21GaussianRandomizedReportAll_highShare_pos
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    0 < lg21ReporterHighShareNNReal
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance)
      (lg21GaussianRandomizedReporterEvent
        lg21GaussianRandomizedReportAllEquilibrium)
      lg21GaussianRandomizedHighScoreEvent := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  rw [lg21GaussianRandomizedReportAll_reporterEvent]
  simp only [lg21ReporterHighShareNNReal, measure_univ, one_ne_zero,
    if_false, cond_univ]
  apply ENNReal.toNNReal_pos
  · exact ne_of_gt
      (lg21GaussianRandomizedHighScoreEvent_pos
        priorMean hpriorVariance hnoiseVariance)
  · exact measure_ne_top _ _

/-- The report-all base law differs from the negative-score output law. -/
theorem lg21GaussianRandomizedReportAll_aggregate_ne_zeroLaw
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance
        lg21GaussianRandomizedReportAllEquilibrium ≠
      lg21RandomizedCounterexampleZeroLaw := by
  letI : IsProbabilityMeasure
      (lg21GaussianRandomizedPrimitiveLaw
        priorMean priorVariance noiseVariance) :=
    lg21GaussianRandomizedPrimitiveLaw_isProbability
      priorMean priorVariance noiseVariance
  unfold lg21GaussianRandomizedGlobalReporterAggregate
  apply lg21BinaryMixturePMF_ne_noReporter_of_pos_of_ne
  · simpa using
      (lg21GaussianRandomizedReportAll_highShare_pos
        priorMean hpriorVariance hnoiseVariance)
  · exact lg21RandomizedCounterexampleSymmetricLaw_ne_zeroLaw

/-- The real-Gaussian randomized policy is not test-blank. -/
theorem lg21GaussianRandomizedPolicySurface_not_testBlank
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    ¬ lg21SourceTestBlank
      (lg21GaussianRandomizedPolicySurface
        priorMean priorVariance noiseVariance) := by
  intro hblank
  have heq := hblank
    lg21GaussianRandomizedReportAllEquilibrium PUnit.unit (-1)
  apply
    (lg21GaussianRandomizedReportAll_aggregate_ne_zeroLaw
      priorMean hpriorVariance hnoiseVariance)
  change
    lg21GaussianRandomizedGlobalReporterAggregate
        priorMean priorVariance noiseVariance
        lg21GaussianRandomizedReportAllEquilibrium =
      (if 0 ≤ (-1 : ℝ) then
        lg21RandomizedCounterexampleSymmetricLaw
      else lg21RandomizedCounterexampleZeroLaw) at heq
  norm_num at heq
  exact heq

/--
Gaussian policy-surface diagnostic.  This carries no paper-facing `paper_`
prefix because the observable-access law below has not yet been derived from
one operational estimator kernel.  The exact theorem is in
`Theorem32GaussianKernelCounterexample`.
-/
theorem lg21_gaussian_randomized_policy_surface_diagnostic
    (priorMean : ℝ) {priorVariance noiseVariance : NNReal}
    (hpriorVariance : priorVariance ≠ 0)
    (hnoiseVariance : noiseVariance ≠ 0) :
    (∀ E : LG21GaussianRandomizedPolicyEquilibrium,
      lg21OptionalSequentialEquilibrium
        (lg21GaussianRandomizedSequentialEquilibriumData
          priorMean priorVariance noiseVariance E)) ∧
      lg21SourceObservablyFair
        (lg21GaussianRandomizedPolicySurface
          priorMean priorVariance noiseVariance) ∧
      ¬ lg21SourceTestBlank
        (lg21GaussianRandomizedPolicySurface
          priorMean priorVariance noiseVariance) := by
  exact
    ⟨lg21GaussianRandomized_every_measurable_strategy_sequential_equilibrium
      priorMean priorVariance noiseVariance,
    lg21GaussianRandomizedPolicySurface_observablyFair
      priorMean priorVariance noiseVariance,
    lg21GaussianRandomizedPolicySurface_not_testBlank
      priorMean hpriorVariance hnoiseVariance⟩

end

end LG21TestOptionalPolicies
