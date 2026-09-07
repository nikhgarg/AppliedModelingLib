import LG21TestOptionalPolicies.SequentialEquilibrium
import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ConditionalProbability

/-!
# Observed-access Gaussian correction for LG21 Lemma 4.1

The report-required part of the source proof defines a test-score value at
which the reported Bayesian posterior equals the no-take estimate.  It later
identifies that score with the posterior-estimate value itself.  Those are
different coordinates: the score is the affine inverse of the posterior map.

This file makes that inverse explicit, proves that the source's profitable
non-taker interval survives the correction, and states the continuous observed
test law as the exact Gaussian-kernel mixture over the upper-truncated
posterior skill distribution.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## The affine inverse in Equation (1) -/

/--
At fixed base features, write the Bayesian posterior after a reported test as
the convex affine update `(1 - weight) * baseMean + weight * test`.
-/
def lg21ObservedAccessReportedPosterior
    (baseMean weight test : ℝ) : ℝ :=
  (1 - weight) * baseMean + weight * test

/-- The test-score coordinate at which the posterior equals `noTakeEstimate`. -/
def lg21ObservedAccessIndifferentTestScore
    (baseMean weight noTakeEstimate : ℝ) : ℝ :=
  affineCutoff ((1 - weight) * baseMean) weight noTakeEstimate

/-- Corrected Equation (1): posterior evaluated at its affine inverse. -/
theorem paper_lemma4_1_taking_indifference_affine_inverse
    (baseMean noTakeEstimate : ℝ) {weight : ℝ}
    (hweight : 0 < weight) :
    lg21ObservedAccessReportedPosterior baseMean weight
        (lg21ObservedAccessIndifferentTestScore
          baseMean weight noTakeEstimate) =
      noTakeEstimate := by
  apply le_antisymm
  · exact
      (affine_le_threshold_iff_le_cutoff hweight).2 le_rfl
  · exact
      (threshold_le_affine_iff_cutoff_le hweight).2 le_rfl

/-- Strict payoff comparison is exactly strict comparison with the inverse. -/
theorem paper_lemma4_1_reported_posterior_gt_no_take_iff_indifferent_score_lt
    (baseMean noTakeEstimate test : ℝ) {weight : ℝ}
    (hweight : 0 < weight) :
    noTakeEstimate <
        lg21ObservedAccessReportedPosterior baseMean weight test ↔
      lg21ObservedAccessIndifferentTestScore
          baseMean weight noTakeEstimate < test := by
  simpa [lg21ObservedAccessReportedPosterior,
    lg21ObservedAccessIndifferentTestScore, not_le] using
    not_congr
      (affine_le_threshold_iff_le_cutoff
        (intercept := (1 - weight) * baseMean)
        (threshold := noTakeEstimate) (x := test) hweight)

/--
For a proper Bayesian update (`0 < weight < 1`), a no-take lower-tail mean
below the base posterior mean has an indifferent *test score* strictly below
that no-take estimate.  This is the inequality lost by identifying the two
coordinates in the source proof.
-/
theorem lg21ObservedAccessIndifferentTestScore_lt_noTakeEstimate
    (baseMean noTakeEstimate : ℝ) {weight : ℝ}
    (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (hnoTake_lt_base : noTakeEstimate < baseMean) :
    lg21ObservedAccessIndifferentTestScore
        baseMean weight noTakeEstimate < noTakeEstimate := by
  rw [lg21ObservedAccessIndifferentTestScore, affineCutoff]
  rw [div_lt_iff₀ hweight]
  have hone_sub_pos : 0 < 1 - weight := sub_pos.mpr hweight_lt_one
  have hgap_pos : 0 < baseMean - noTakeEstimate :=
    sub_pos.mpr hnoTake_lt_base
  have hproduct_pos :
      0 < (1 - weight) * (baseMean - noTakeEstimate) :=
    mul_pos hone_sub_pos hgap_pos
  nlinarith

/-- A Gaussian lower-tail conditional mean is also below the parent mean. -/
theorem lg21_standardGaussianLowerTailMean_lt_parent_mean
    (law : GaussianScaleLaw) (threshold : ℝ) :
    standardGaussianLowerTailMean law threshold < law.mean := by
  rw [standardGaussianLowerTailMean]
  have hproduct_pos :
      0 < law.scale *
        standardGaussianHazard (-(law.standardize threshold)) :=
    mul_pos law.scale_pos
      (standardGaussianHazard_pos (-(law.standardize threshold)))
  linarith

/--
The corrected source deviation interval is nonempty: some skill lies below
the proposed taking cutoff but above the true affine-inverse indifference
score, and hence strictly prefers the expected reported estimate.
-/
theorem paper_lemma4_1_no_taker_profitable_deviation_with_affine_inverse
    (baseMean noTakeEstimate takingCutoff : ℝ) {weight : ℝ}
    (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (hnoTake_lt_base : noTakeEstimate < baseMean)
    (hnoTake_lt_cutoff : noTakeEstimate < takingCutoff) :
    ∃ skill : ℝ,
      skill < takingCutoff ∧
        noTakeEstimate <
          lg21ObservedAccessReportedPosterior baseMean weight skill := by
  let scoreCutoff :=
    lg21ObservedAccessIndifferentTestScore
      baseMean weight noTakeEstimate
  have hscore_lt_noTake : scoreCutoff < noTakeEstimate := by
    exact
      lg21ObservedAccessIndifferentTestScore_lt_noTakeEstimate
        baseMean noTakeEstimate hweight hweight_lt_one hnoTake_lt_base
  have hscore_lt_taking : scoreCutoff < takingCutoff :=
    lt_trans hscore_lt_noTake hnoTake_lt_cutoff
  let skill := (scoreCutoff + takingCutoff) / 2
  have hscore_lt_skill : scoreCutoff < skill := by
    dsimp [skill]
    linarith
  have hskill_lt_taking : skill < takingCutoff := by
    dsimp [skill]
    linarith
  refine ⟨skill, hskill_lt_taking, ?_⟩
  exact
    (paper_lemma4_1_reported_posterior_gt_no_take_iff_indifferent_score_lt
      baseMean noTakeEstimate skill hweight).2 hscore_lt_skill

/--
Concrete lower-tail specialization of the corrected deviation.  It uses both
strict facts supplied by the nondegenerate Gaussian formula: the lower-tail
mean lies below the parent mean and below the truncation threshold.
-/
theorem paper_lemma4_1_no_taker_profitable_deviation_of_gaussian_lower_tail
    (skillLaw : GaussianScaleLaw) (takingCutoff : ℝ) {weight : ℝ}
    (hweight : 0 < weight) (hweight_lt_one : weight < 1) :
    ∃ skill : ℝ,
      skill < takingCutoff ∧
        standardGaussianLowerTailMean skillLaw takingCutoff <
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill := by
  exact
    paper_lemma4_1_no_taker_profitable_deviation_with_affine_inverse
      skillLaw.mean
      (standardGaussianLowerTailMean skillLaw takingCutoff)
      takingCutoff hweight hweight_lt_one
      (lg21_standardGaussianLowerTailMean_lt_parent_mean
        skillLaw takingCutoff)
      (standardGaussianLowerTailMean_lt_threshold skillLaw takingCutoff)

/-! ## Arbitrary-equilibrium Lemma 4.1 endpoints -/

/--
Optional-reporting Lemma 4.1 for an arbitrary supplied sequential equilibrium.
Best response supplies the actual strict lower side of the affine reporting
cutoff.  Bayesian consistency says that, if anyone fails to report, the
no-report estimate is the reported posterior evaluated at the Gaussian
lower-tail mean of precisely that side.  Strict monotonicity then contradicts
the defining affine indifference equation, so every score is reported.
-/
theorem paper_lemma4_1_arbitrary_optional_sequential_equilibrium_all_report
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreLaw : GaussianScaleLaw)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (hnoReportConsistency :
      ∀ cutoff : ℝ,
        (∀ score, score < cutoff →
          E.reportDecision base score = false) →
        ¬ (∀ score, E.reportDecision base score = true) →
        E.noReportPayoff base =
          intercept + slope *
            standardGaussianLowerTailMean scoreLaw cutoff) :
    ∀ score, E.reportDecision base score = true := by
  by_contra hnotAll
  let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
  have hstrict :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope hreported
  have hbelow :
      ∀ score, score < cutoff →
        E.reportDecision base score = false := by
    intro score hscore
    have hnot : E.reportDecision base score ≠ true := by
      intro hreport
      exact (not_le_of_gt hscore) (hstrict.1 score hreport)
    cases hdecision : E.reportDecision base score
    · rfl
    · exact False.elim (hnot hdecision)
  have hconsistent := hnoReportConsistency cutoff hbelow hnotAll
  have hlower : standardGaussianLowerTailMean scoreLaw cutoff < cutoff :=
    standardGaussianLowerTailMean_lt_threshold scoreLaw cutoff
  have hposterior_lt :
      intercept + slope * standardGaussianLowerTailMean scoreLaw cutoff <
        intercept + slope * cutoff :=
    affine_strictMono intercept hslope hlower
  have hindifferent :
      intercept + slope * cutoff = E.noReportPayoff base := by
    dsimp [cutoff]
    apply le_antisymm
    · exact (affine_le_threshold_iff_le_cutoff hslope).2 le_rfl
    · exact (threshold_le_affine_iff_cutoff_le hslope).2 le_rfl
  rw [← hconsistent, hindifferent] at hposterior_lt
  exact (lt_irrefl _ hposterior_lt)

/--
Full optional-reporting endpoint of Lemma 4.1 for an arbitrary supplied
source-timed equilibrium.  Nondegenerate Gaussian test noise first gives every
latent type positive mass on scores whose positive-slope posterior exceeds
the no-report estimate, so ex-ante best response forces everyone to take.
Only then is the lower-tail consistency identity invoked to force reporting at
every realized score.  This ordering avoids assuming all-taking inside the
consistency step that is meant to prove the equilibrium conclusion.
-/
theorem paper_lemma4_1_arbitrary_optional_sequential_equilibrium_all_take_and_report
    {E : LG21OptionalSequentialEquilibriumData ℝ PUnit ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (scoreLaw : GaussianScaleLaw)
    (testVariance : NNReal) (hvariance : testVariance ≠ 0)
    (htestLaw :
      ∀ skill, E.testLaw skill PUnit.unit =
        gaussianReal skill testVariance)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score,
        E.reportedPayoff PUnit.unit score = intercept + slope * score)
    (hnoReportConsistency :
      (∀ skill, E.takeDecision skill PUnit.unit = true) →
        ∀ cutoff : ℝ,
          (∀ score, score < cutoff →
            E.reportDecision PUnit.unit score = false) →
          ¬ (∀ score, E.reportDecision PUnit.unit score = true) →
          E.noReportPayoff PUnit.unit =
            intercept + slope *
              standardGaussianLowerTailMean scoreLaw cutoff) :
    (∀ skill, E.takeDecision skill PUnit.unit = true) ∧
      ∀ score, E.reportDecision PUnit.unit score = true := by
  have htake :
      ∀ skill, E.takeDecision skill PUnit.unit = true :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
      hEq PUnit.unit testVariance hvariance htestLaw
      intercept slope hslope hreported
  have hreport :
      ∀ score, E.reportDecision PUnit.unit score = true :=
    paper_lemma4_1_arbitrary_optional_sequential_equilibrium_all_report
      hEq PUnit.unit scoreLaw intercept slope hslope hreported
      (hnoReportConsistency htake)
  exact ⟨htake, hreport⟩

/--
Report-required Lemma 4.1 under the actual Definition 1 objective.  The test
remains noisy; expected posterior payoff is affine in latent skill.  If a
non-all-taking equilibrium induced a lower-tail no-take estimate, the corrected
affine-inverse lemma supplies a below-cutoff non-taker with a strictly
profitable taking deviation.
-/
theorem paper_lemma4_1_arbitrary_report_required_sequential_equilibrium_all_take
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : GaussianScaleLaw)
    (weight : ℝ) (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (htakeExpected :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill)
    (hcutoffConsistencyIfNotAll :
      ¬ (∀ skill, E.takeDecision skill base = true) →
        ∃ takingCutoff : ℝ,
          (∀ skill, skill < takingCutoff →
            E.takeDecision skill base = false) ∧
          E.noReportPayoff base =
            standardGaussianLowerTailMean skillLaw takingCutoff) :
    ∀ skill, E.takeDecision skill base = true := by
  by_contra hnotAll
  rcases hcutoffConsistencyIfNotAll hnotAll with
    ⟨takingCutoff, hbelow, hnoReport⟩
  rcases
      paper_lemma4_1_no_taker_profitable_deviation_of_gaussian_lower_tail
        skillLaw takingCutoff hweight hweight_lt_one with
    ⟨skill, hskill_lt, hprofitable⟩
  have hdecision_false := hbelow skill hskill_lt
  have hnotTake : E.takeDecision skill base ≠ true := by
    simp [hdecision_false]
  have hbest :=
    (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base).2
      skill hnotTake
  change
    lg21ReportRequiredSequentialTakeExpectedPayoff E skill base ≤
      E.noReportPayoff base at hbest
  rw [htakeExpected skill, hnoReport] at hbest
  exact (not_le_of_gt hprofitable) hbest

/--
With Gaussian test noise centered at true skill, the ex-ante reported
posterior is the same affine function of skill.  This keeps the source's
nondegenerate noise instead of identifying realized test and latent skill.
-/
theorem paper_lemma4_1_expected_reported_posterior_under_gaussian_test
    (baseMean weight skill : ℝ) (testVariance : NNReal) :
    (∫ test,
        lg21ObservedAccessReportedPosterior baseMean weight test
          ∂gaussianReal skill testVariance) =
      lg21ObservedAccessReportedPosterior baseMean weight skill := by
  exact
    lg21_gaussian_expected_affine_test_payoff
      skill testVariance ((1 - weight) * baseMean) weight

/-!
## Requirement-policy closure

The source suppresses the requirement-policy index because Lemma 4.1 has the
same all-information outcome in all three regimes.  The following endpoint
bundles the two strategic arguments above with the third, mandated regime,
where taking and reporting are fixed by `Z = Y = X` and only estimator
consistency remains.
-/

theorem paper_lemma4_1_all_three_requirement_protocols
    {RequiredTest : Type*} [MeasurableSpace RequiredTest]
    {Eoptional : LG21OptionalSequentialEquilibriumData ℝ PUnit ℝ}
    {Erequired :
      LG21ReportRequiredSequentialEquilibriumData ℝ PUnit RequiredTest}
    {Emandated :
      LG21RequiredGivenAccessSequentialEquilibriumData PUnit RequiredTest}
    (hOptionalEq : lg21OptionalSequentialEquilibrium Eoptional)
    (optionalScoreLaw : GaussianScaleLaw)
    (optionalTestVariance : NNReal)
    (hOptionalVariance : optionalTestVariance ≠ 0)
    (hOptionalTestLaw :
      ∀ skill,
        Eoptional.testLaw skill PUnit.unit =
          gaussianReal skill optionalTestVariance)
    (optionalIntercept optionalSlope : ℝ)
    (hOptionalSlope : 0 < optionalSlope)
    (hOptionalReported :
      ∀ score,
        Eoptional.reportedPayoff PUnit.unit score =
          optionalIntercept + optionalSlope * score)
    (hOptionalNoReportConsistency :
      (∀ skill,
        Eoptional.takeDecision skill PUnit.unit = true) →
        ∀ cutoff : ℝ,
          (∀ score, score < cutoff →
            Eoptional.reportDecision PUnit.unit score = false) →
          ¬ (∀ score,
            Eoptional.reportDecision PUnit.unit score = true) →
          Eoptional.noReportPayoff PUnit.unit =
            optionalIntercept + optionalSlope *
              standardGaussianLowerTailMean optionalScoreLaw cutoff)
    (hRequiredEq : lg21ReportRequiredSequentialEquilibrium Erequired)
    (requiredSkillLaw : GaussianScaleLaw)
    (requiredWeight : ℝ) (hRequiredWeight : 0 < requiredWeight)
    (hRequiredWeight_lt_one : requiredWeight < 1)
    (hRequiredTakeExpected :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff
            Erequired skill PUnit.unit =
          lg21ObservedAccessReportedPosterior
            requiredSkillLaw.mean requiredWeight skill)
    (hRequiredCutoffConsistency :
      ¬ (∀ skill,
        Erequired.takeDecision skill PUnit.unit = true) →
        ∃ takingCutoff : ℝ,
          (∀ skill, skill < takingCutoff →
            Erequired.takeDecision skill PUnit.unit = false) ∧
          Erequired.noReportPayoff PUnit.unit =
            standardGaussianLowerTailMean
              requiredSkillLaw takingCutoff)
    (hMandatedEq :
      lg21RequiredGivenAccessSequentialEquilibrium Emandated) :
    ((∀ skill, Eoptional.takeDecision skill PUnit.unit = true) ∧
        ∀ score,
          Eoptional.reportDecision PUnit.unit score = true) ∧
      (∀ skill,
        Erequired.takeDecision skill PUnit.unit = true) ∧
      Emandated.estimationConsistent := by
  refine ⟨?_, ?_, hMandatedEq⟩
  · exact
      paper_lemma4_1_arbitrary_optional_sequential_equilibrium_all_take_and_report
        hOptionalEq optionalScoreLaw optionalTestVariance
        hOptionalVariance hOptionalTestLaw optionalIntercept optionalSlope
        hOptionalSlope hOptionalReported hOptionalNoReportConsistency
  · exact
      paper_lemma4_1_arbitrary_report_required_sequential_equilibrium_all_take
        hRequiredEq PUnit.unit requiredSkillLaw requiredWeight
        hRequiredWeight hRequiredWeight_lt_one hRequiredTakeExpected
        hRequiredCutoffConsistency

/-! ## Exact continuous observed-test mixture -/

/-- Normalize the restriction of a measure to an event. -/
def lg21NormalizedRestriction
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (event : Set Outcome) : Measure Outcome :=
  (law event)⁻¹ • law.restrict event

/-- Event formula for the normalized restriction. -/
theorem lg21NormalizedRestriction_apply
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) {event target : Set Outcome}
    (htarget : MeasurableSet target) :
    lg21NormalizedRestriction law event target =
      (law event)⁻¹ * law (target ∩ event) := by
  rw [lg21NormalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply htarget]

/-- A normalized restriction of finite positive mass is a probability law. -/
theorem lg21NormalizedRestriction_isProbability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) (event : Set Outcome)
    (hpositive : law event ≠ 0) (hfinite : law event ≠ ⊤) :
    IsProbabilityMeasure (lg21NormalizedRestriction law event) := by
  change IsProbabilityMeasure (ProbabilityTheory.cond law event)
  exact cond_isProbabilityMeasure_of_finite hpositive hfinite

/--
The source parameters of the upper-tail observed-score law in the proof of
Lemma 4.1.  Positive posterior variance is part of the Gaussian model, and
positive mass above the finite taking cutoff makes the displayed normalized
restriction an actual conditional probability law.  The optional test has
independent positive Gaussian noise conditional on latent skill.
-/
structure LG21ObservedAccessUpperTailGaussianModel where
  posteriorMean : ℝ
  posteriorVariance : NNReal
  posteriorVariance_pos : 0 < (posteriorVariance : ℝ)
  takingCutoff : ℝ
  upperTailMass_pos :
    0 < gaussianReal posteriorMean posteriorVariance (Set.Ioi takingCutoff)
  testNoiseVariance : NNReal
  testNoiseVariance_pos : 0 < (testNoiseVariance : ℝ)

/-- Posterior skill law conditional on the source's upper-tail taking event. -/
def lg21ObservedAccessUpperTailSkillLaw
    (model : LG21ObservedAccessUpperTailGaussianModel) : Measure ℝ :=
  lg21NormalizedRestriction
    (gaussianReal model.posteriorMean model.posteriorVariance)
    (Set.Ioi model.takingCutoff)

/-- The normalized upper-tail posterior is a probability law when nonempty. -/
theorem lg21ObservedAccessUpperTailSkillLaw_isProbability
    (model : LG21ObservedAccessUpperTailGaussianModel) :
    IsProbabilityMeasure (lg21ObservedAccessUpperTailSkillLaw model) := by
  exact
    lg21NormalizedRestriction_isProbability
      (gaussianReal model.posteriorMean model.posteriorVariance)
      (Set.Ioi model.takingCutoff) model.upperTailMass_pos.ne'
      (measure_ne_top _ _)

/-- The source conditional test law `theta_K | q = N(q, sigma_K^2)`. -/
def lg21ObservedAccessGaussianTestGivenSkill
    (model : LG21ObservedAccessUpperTailGaussianModel) : Kernel ℝ ℝ :=
  gaussianLocationKernel id measurable_id model.testNoiseVariance

/-- The source conditional test law is a Markov kernel. -/
theorem lg21ObservedAccessGaussianTestGivenSkill_isMarkov
    (model : LG21ObservedAccessUpperTailGaussianModel) :
    IsMarkovKernel (lg21ObservedAccessGaussianTestGivenSkill model) := by
  unfold lg21ObservedAccessGaussianTestGivenSkill
  exact gaussianLocationKernel_isMarkov id measurable_id model.testNoiseVariance

/-- Pointwise Gaussian form of the source conditional test law. -/
theorem lg21ObservedAccessGaussianTestGivenSkill_apply
    (model : LG21ObservedAccessUpperTailGaussianModel) (skill : ℝ) :
    lg21ObservedAccessGaussianTestGivenSkill model skill =
      gaussianReal skill model.testNoiseVariance := by
  unfold lg21ObservedAccessGaussianTestGivenSkill
  simpa using
    gaussianLocationKernel_apply id measurable_id model.testNoiseVariance skill

/--
Exact measure form of the source's observed test-score mixture: first draw
skill from the upper-truncated posterior skill law, then draw the noisy test
from its skill-indexed conditional kernel.
-/
def lg21ObservedAccessTestLawOfUpperTailTakers
    (model : LG21ObservedAccessUpperTailGaussianModel) : Measure ℝ :=
  Measure.bind
    (lg21ObservedAccessUpperTailSkillLaw model)
    (lg21ObservedAccessGaussianTestGivenSkill model)

/-- The observed-test mixture is itself a probability law. -/
theorem lg21ObservedAccessTestLawOfUpperTailTakers_isProbability
    (model : LG21ObservedAccessUpperTailGaussianModel) :
    IsProbabilityMeasure (lg21ObservedAccessTestLawOfUpperTailTakers model) := by
  letI : IsProbabilityMeasure
      (lg21ObservedAccessUpperTailSkillLaw model) :=
    lg21ObservedAccessUpperTailSkillLaw_isProbability model
  letI : IsMarkovKernel (lg21ObservedAccessGaussianTestGivenSkill model) :=
    lg21ObservedAccessGaussianTestGivenSkill_isMarkov model
  change IsProbabilityMeasure
    (Measure.bind
      (lg21ObservedAccessUpperTailSkillLaw model)
      (lg21ObservedAccessGaussianTestGivenSkill model))
  infer_instance

/-- The mixture law evaluated on an arbitrary measurable test-score event. -/
theorem paper_lemma4_1_observed_test_law_upper_truncated_mixture_apply
    (model : LG21ObservedAccessUpperTailGaussianModel)
    {testEvent : Set ℝ} (htestEvent : MeasurableSet testEvent) :
    lg21ObservedAccessTestLawOfUpperTailTakers model testEvent =
      ∫⁻ skill,
        gaussianReal skill model.testNoiseVariance testEvent
          ∂lg21ObservedAccessUpperTailSkillLaw model := by
  rw [lg21ObservedAccessTestLawOfUpperTailTakers,
    Measure.bind_apply htestEvent
      (Kernel.aemeasurable (lg21ObservedAccessGaussianTestGivenSkill model))]
  simp_rw [lg21ObservedAccessGaussianTestGivenSkill_apply]

/--
Gaussian specialization of the preceding identity.  The right side is the
source's integral of `N(skill, testVariance)` against the explicitly
parameterized upper-truncated `N(posteriorMean, posteriorVariance)` law.
-/
theorem paper_lemma4_1_observed_test_law_gaussian_upper_truncated_mixture_apply
    (model : LG21ObservedAccessUpperTailGaussianModel)
    {testEvent : Set ℝ} (htestEvent : MeasurableSet testEvent) :
    lg21ObservedAccessTestLawOfUpperTailTakers model testEvent =
      ∫⁻ skill,
        gaussianReal skill model.testNoiseVariance testEvent
          ∂lg21ObservedAccessUpperTailSkillLaw model :=
  paper_lemma4_1_observed_test_law_upper_truncated_mixture_apply model htestEvent

/-! ## Null affine ties for nondegenerate Gaussian laws -/

/-- A positive-slope affine payoff has exactly one tie point. -/
theorem lg21_affine_payoff_tie_set_eq_singleton
    (intercept threshold : ℝ) {slope : ℝ} (hslope : 0 < slope) :
    {value : ℝ | intercept + slope * value = threshold} =
      {affineCutoff intercept slope threshold} := by
  ext value
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro heq
    apply le_antisymm
    · exact
        (affine_le_threshold_iff_le_cutoff hslope).1 heq.le
    · exact
        (threshold_le_affine_iff_cutoff_le hslope).1 heq.ge
  · intro heq
    subst value
    apply le_antisymm
    · exact (affine_le_threshold_iff_le_cutoff hslope).2 le_rfl
    · exact (threshold_le_affine_iff_cutoff_le hslope).2 le_rfl

/-- The unique affine tie is null under every nondegenerate Gaussian law. -/
theorem lg21_gaussian_affine_payoff_tie_null
    (mean : ℝ) {variance : NNReal} (hvariance : variance ≠ 0)
    (intercept threshold : ℝ) {slope : ℝ} (hslope : 0 < slope) :
    gaussianReal mean variance
        {value : ℝ | intercept + slope * value = threshold} = 0 := by
  letI : NoAtoms (gaussianReal mean variance) :=
    noAtoms_gaussianReal hvariance
  rw [lg21_affine_payoff_tie_set_eq_singleton
    intercept threshold hslope, measure_singleton]

end

end LG21TestOptionalPolicies
