import LG21TestOptionalPolicies.SequentialEquilibrium
import LG21TestOptionalPolicies.ContinuousPopulation

/-!
# Hidden-access source model for LG21 Theorem 3.1

This module is deliberately narrower than a whole-paper closeout.  It gives
the hidden-access, optional-reporting part of Theorem 3.1 a source-timed
surface: an arbitrary equilibrium chooses whether to take before a Gaussian
test draw and whether to report after the draw.  The theorem below derives the
cutoff, all-taking, and positive-withholding conclusions from that equilibrium;
it does not receive a cutoff or an opaque `estimationConsistent : Prop` as an
input.

The remaining source-model boundary is visible in
`noReportPBO_of_strict_cutoff`: it is the conditional-expectation calculation
for the hidden-access no-report information set.  Its hypotheses describe the
actual strategy on both strict sides of an already-derived cutoff, rather than
assuming a cutoff strategy.  Deriving that field from a single regular
conditional probability construction is still required for a full source
bridge.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
Source primitives for the hidden-access optional-reporting part of Theorem
3.1.  The Gaussian population supplies the source's unit-mass, independent
access/skill/noise model.  `pboFamily` is tied coordinatewise to that
population, while `scoreLaw` is the Gaussian conditional raw-score law at a
fixed non-test feature profile used in the hidden-access no-report pool.

`baseOnlyPBO` is intentionally retained as the posterior value for the
no-access branch.  The source states that conditional expectation but does not
give a formal regular-conditional-probability construction for arbitrary base
profiles; the exact way it enters the no-report posterior is therefore exposed
below rather than hidden in a generic consistency proposition.
-/
structure LG21HiddenAccessTheorem31GaussianModel
    (Feature Base : Type*) [Fintype Feature] [DecidableEq Feature] where
  population : LG21ContinuousGaussianPopulation Feature
  pboFamily : Base → GaussianOffsetSignalFamily Feature
  observedBase : Base → Feature → ℝ
  testFeature : Feature
  /-- Conditional share of students with access at a fixed base profile. -/
  accessFraction : Base → ℝ
  accessFraction_eq_population :
    ∀ base,
      accessFraction base =
        (population.accessLaw ({true} : Set Bool)).toReal
  accessFraction_pos : ∀ base, 0 < accessFraction base
  accessFraction_lt_one : ∀ base, accessFraction base < 1
  /-- Bayesian estimate for the no-access component before observing a test. -/
  baseOnlyPBO : Base → ℝ
  /-- Gaussian raw-score law conditional on the fixed non-test profile. -/
  scoreLaw : Base → GaussianScaleLaw
  /-- Conditional raw test-score variance after latent skill is known. -/
  testVariance : Base → NNReal
  testVariance_ne_zero : ∀ base, testVariance base ≠ 0
  /-- The posterior family uses the population's Gaussian prior. -/
  pbo_priorMean :
    ∀ base, (pboFamily base).priorMean = population.priorMean
  pbo_priorVariance :
    ∀ base, (pboFamily base).priorVar = (population.priorVariance : ℝ)
  /-- The source noise variables are centered. -/
  pbo_noiseMean :
    ∀ base feature, (pboFamily base).noiseMean feature = 0
  /-- The posterior family uses the population noise variance at every coordinate. -/
  pbo_noiseVariance :
    ∀ base feature,
      (pboFamily base).noiseVar feature =
        (population.noiseVariance feature : ℝ)
  /-- The test's conditional variance is the population variance of feature `K`. -/
  testVariance_eq_population :
    ∀ base, testVariance base = population.noiseVariance testFeature

namespace LG21HiddenAccessTheorem31GaussianModel

/-- The source-timed conditional raw test law `theta_K | q, base`. -/
def rawTestLaw
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (skill : ℝ) (base : Base) : Measure ℝ :=
  gaussianReal skill (model.testVariance base)

/-- The reported Bayesian posterior at a fixed base profile and raw score. -/
def reportedPBO
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (base : Base) (score : ℝ) : ℝ :=
  (model.pboFamily base).posteriorMean
    (Function.update (model.observedBase base) model.testFeature score)

/-- The source's corrected hidden-access no-report posterior at a cutoff. -/
def noReportPBOAtCutoff
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (base : Base) (cutoff : ℝ) : ℝ :=
  lg21OptionalNoReportMixtureEstimate
    (model.accessFraction base) (model.baseOnlyPBO base) (model.scoreLaw base)
    (fun lowerCutoff =>
      model.reportedPBO base
        (standardGaussianLowerTailMean (model.scoreLaw base) lowerCutoff))
    cutoff

/-- The positive slope of the reported PBO as a function of the raw score. -/
theorem reportedPBO_slope_pos
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (base : Base) :
    0 < (model.pboFamily base).centeredFamily.signalWeight model.testFeature :=
  (model.pboFamily base).centeredFamily.signalWeight_pos model.testFeature

/-- The reported PBO is affine in the raw test score at a fixed base profile. -/
theorem reportedPBO_eq_affine
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (base : Base) (score : ℝ) :
    model.reportedPBO base score =
      model.reportedPBO base 0 +
        (model.pboFamily base).centeredFamily.signalWeight model.testFeature * score := by
  exact
    (model.pboFamily base).posteriorMean_update_eq_base_add_weight_mul
      (model.observedBase base) model.testFeature score

end LG21HiddenAccessTheorem31GaussianModel

/--
An arbitrary supplied, source-timed equilibrium compatible with the hidden
access Gaussian model.  The three semantic fields below are deliberately
concrete:

* raw tests have the source conditional Gaussian law;
* reporting payoff is the actual Bayesian posterior formula;
* the no-report payoff equals the source conditional PBO mixture once the
  equilibrium itself has forced the strict cutoff sides.

None supplies a threshold, an all-taking conclusion, or a generic
`estimationConsistent : Prop` witness.
-/
structure LG21HiddenAccessOptionalPBOEquilibrium
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base) where
  testLaw : ℝ → Base → Measure ℝ
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : ℝ → Base → Bool
  reportDecision : Base → ℝ → Bool
  reportedPayoff : Base → ℝ → ℝ
  noReportPayoff : Base → ℝ
  continuationPayoff_integrable :
    ∀ skill base,
      Integrable
        (fun score =>
          if reportDecision base score then
            reportedPayoff base score
          else
            noReportPayoff base)
        (testLaw skill base)
  /-- Definition 1's ex-ante taking best response at the source decision time. -/
  take_best_response :
    ∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill => takeDecision skill base = true)
        (fun skill =>
          ∫ score,
            if reportDecision base score then
              reportedPayoff base score
            else
              noReportPayoff base
            ∂testLaw skill base)
        (fun _skill => noReportPayoff base)
  /-- Definition 1's ex-post reporting best response after observing a score. -/
  report_best_response :
    ∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun score => reportDecision base score = true)
        (reportedPayoff base) (fun _score => noReportPayoff base)
  raw_test_law :
    ∀ skill base,
      testLaw skill base =
        model.rawTestLaw skill base
  reported_payoff_is_pbo :
    ∀ base score,
      reportedPayoff base score = model.reportedPBO base score
  /-- Source's weak preference convention is resolved by reporting at equality. -/
  report_at_indifference :
    ∀ base score,
      reportedPayoff base score = noReportPayoff base →
        reportDecision base score = true
  /--
  The remaining hidden-access conditional-PBO calculation.  Strict cutoff
  sides and all taking are derived from `isEquilibrium`; this field does not
  assume a cutoff rule or any strategic conclusion.  All taking is required
  because the no-report pool otherwise also contains non-takers.
  -/
  noReportPBO_of_strict_cutoff :
    ∀ base cutoff,
      (∀ score, score < cutoff → reportDecision base score = false) →
        (∀ score, cutoff < score → reportDecision base score = true) →
          (∀ skill, takeDecision skill base = true) →
            noReportPayoff base = model.noReportPBOAtCutoff base cutoff

namespace LG21HiddenAccessOptionalPBOEquilibrium

/--
The legacy sequential record is used only as a proof adapter.  Its old
`estimationConsistent : Prop` slot is definitionally `True`; the source-model
content instead lives in the explicit PBO fields of
`LG21HiddenAccessOptionalPBOEquilibrium`.
-/
def toSequentialData
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    {model : LG21HiddenAccessTheorem31GaussianModel Feature Base}
    (E : LG21HiddenAccessOptionalPBOEquilibrium model) :
    LG21OptionalSequentialEquilibriumData ℝ Base ℝ where
  testLaw := E.testLaw
  testLaw_isProbability := E.testLaw_isProbability
  takeDecision := E.takeDecision
  reportDecision := E.reportDecision
  reportedPayoff := E.reportedPayoff
  noReportPayoff := E.noReportPayoff
  continuationPayoff_integrable := E.continuationPayoff_integrable
  estimationConsistent := True

/-- The explicit source-timed best responses induce the reusable sequential equilibrium adapter. -/
theorem toSequentialEquilibrium
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    {model : LG21HiddenAccessTheorem31GaussianModel Feature Base}
    (E : LG21HiddenAccessOptionalPBOEquilibrium model) :
    lg21OptionalSequentialEquilibrium E.toSequentialData :=
  ⟨E.take_best_response, E.report_best_response, trivial⟩

/--
Source-timed hidden-access Theorem 3.1 bridge for optional reporting.  The
cutoff is derived from an arbitrary supplied sequential equilibrium and the
visible tie convention.  The theorem then derives all taking from the
conditional Gaussian test law and positive withholding mass from the
conditional Gaussian score law.

The no-report equality in the conclusion is the model's explicit conditional
PBO obligation evaluated only after the cutoff has been derived.  This keeps
the residual regular-conditional-probability work visible to later repair
agents.
-/
theorem paper_theorem3_1_hidden_access_optional_source_timed_bridge
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (E : LG21HiddenAccessOptionalPBOEquilibrium model) :
    ∀ base,
      ∃ cutoff : ℝ,
        (0 < model.accessFraction base ∧ model.accessFraction base < 1) ∧
          (∀ score,
            E.reportDecision base score = true ↔ cutoff ≤ score) ∧
            E.noReportPayoff base = model.noReportPBOAtCutoff base cutoff ∧
              (∀ skill, E.takeDecision skill base = true) ∧
                0 < (model.scoreLaw base).toMeasure
                  {score | E.reportDecision base score = false} := by
  intro base
  let intercept : ℝ := model.reportedPBO base 0
  let slope : ℝ :=
    (model.pboFamily base).centeredFamily.signalWeight model.testFeature
  have hslope : 0 < slope := by
    simpa [slope] using model.reportedPBO_slope_pos base
  have hreported :
      ∀ score,
        E.reportedPayoff base score = intercept + slope * score := by
    intro score
    rw [E.reported_payoff_is_pbo base score]
    simpa [intercept, slope] using model.reportedPBO_eq_affine base score
  have hcutoff :
      ∀ score,
        E.reportDecision base score = true ↔
          affineCutoff intercept slope (E.noReportPayoff base) ≤ score :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_exact_cutoff_of_tiebreak
      E.toSequentialEquilibrium base intercept slope hslope hreported
      (fun score h => E.report_at_indifference base score h)
  let cutoff : ℝ := affineCutoff intercept slope (E.noReportPayoff base)
  have hbelow :
      ∀ score, score < cutoff → E.reportDecision base score = false := by
    intro score hscore
    have hnot : E.reportDecision base score ≠ true := by
      intro hreport
      exact (not_le_of_gt hscore) ((hcutoff score).1 hreport)
    cases hdecision : E.reportDecision base score
    · rfl
    · exact False.elim (hnot hdecision)
  have habove :
      ∀ score, cutoff < score → E.reportDecision base score = true := by
    intro score hscore
    exact (hcutoff score).2 hscore.le
  have htakes : ∀ skill, E.takeDecision skill base = true := by
    exact
      paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
        E.toSequentialEquilibrium base (model.testVariance base)
        (model.testVariance_ne_zero base)
        (fun skill => by
          simpa [LG21HiddenAccessTheorem31GaussianModel.rawTestLaw] using
            E.raw_test_law skill base)
        intercept slope hslope hreported
  have hnoReport :
      E.noReportPayoff base = model.noReportPBOAtCutoff base cutoff :=
    E.noReportPBO_of_strict_cutoff base cutoff hbelow habove htakes
  have hwithhold :
      0 < gaussianReal (model.scoreLaw base).mean
        (model.scoreLaw base).varianceNNReal
          {score | E.reportDecision base score = false} :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass_gaussian
      E.toSequentialEquilibrium base (model.scoreLaw base).mean
      (model.scoreLaw base).varianceNNReal
      (model.scoreLaw base).varianceNNReal_ne_zero
      intercept slope hslope hreported
  refine ⟨cutoff, ?_, ?_, hnoReport, htakes, ?_⟩
  · exact ⟨model.accessFraction_pos base, model.accessFraction_lt_one base⟩
  · intro score
    simpa [cutoff] using hcutoff score
  · simpa [GaussianScaleLaw.toMeasure] using hwithhold

/--
When a non-test profile exists, the bridge gives the paper's headline
strategic-withholding witness together with positive access share.  The
withholding mass is measured under the model's source conditional score law.
-/
theorem paper_theorem3_1_hidden_access_optional_some_strategic_withholding
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature] [Nonempty Base]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (E : LG21HiddenAccessOptionalPBOEquilibrium model) :
    ∃ base,
      0 < model.accessFraction base ∧
        0 < (model.scoreLaw base).toMeasure
          {score | E.reportDecision base score = false} := by
  let base : Base := Classical.choice inferInstance
  rcases paper_theorem3_1_hidden_access_optional_source_timed_bridge model E base with
    ⟨_cutoff, hshare, _hcutoff, _hpbo, _htakes, hwithhold⟩
  exact ⟨base, hshare.1, hwithhold⟩

end LG21HiddenAccessOptionalPBOEquilibrium

end

end LG21TestOptionalPolicies
