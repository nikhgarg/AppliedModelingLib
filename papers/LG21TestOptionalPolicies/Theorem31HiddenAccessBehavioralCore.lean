import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceModel

/-!
# Hidden-access behavioral core for LG21 Theorem 3.1

This module separates the part of the optional-reporting argument that follows
directly from Definition 1's two decision-time best-response inequalities from
the still-open population/PBO calculation.

In particular, the theorem below does *not* assume or conclude a no-report
mixture formula, a fixed-point witness, a cutoff action rule, or an opaque
estimation-consistency proposition.  Its inputs are the concrete behavioral
clauses, the literal conditional Gaussian test law, and the reported-score PBO
formula.  Thus it is a valid source-model component, but not a full
formalization of Theorem 3.1: identifying the no-report payoff with the
conditional mean on the actual unobserved-access action event remains a
separate measure-theoretic obligation.

The source's pointwise ``if and only if'' convention at the single
indifference score is also deliberately absent.  Weak best response determines
the two strict sides; an exact cutoff requires an explicit tie convention, or
an almost-everywhere formulation under the relevant source score law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
The behavioral core of hidden-access optional reporting.

For every fixed public base profile, an arbitrary source-timed profile that
satisfies Definition 1's concrete taking and reporting best-response clauses,
uses the literal conditional Gaussian test law, and gives reported scores their
Gaussian PBO payoff has:

* the two strict sides of a finite score cutoff;
* all latent types taking the test; and
* positive conditional probability of withholding for every latent type.

The last conclusion is conditional on a latent type's Gaussian test draw.  It
is intentionally not promoted to a population-level selected-action mass,
which would require the unresolved measurable action/population bridge.
-/
theorem lg21_theorem31_hiddenAccess_optional_behavioral_core
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (testLaw : ℝ → Base → Measure ℝ)
    (testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (reportedPayoff : Base → ℝ → ℝ)
    (noReportPayoff : Base → ℝ)
    (continuationPayoff_integrable :
      ∀ skill base,
        Integrable
          (fun score =>
            if reportDecision base score then
              reportedPayoff base score
            else
              noReportPayoff base)
          (testLaw skill base))
    (take_best_response :
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
          (fun _skill => noReportPayoff base))
    (report_best_response :
      ∀ base,
        NoProfitableBinaryChoiceDeviation
          (fun score => reportDecision base score = true)
          (reportedPayoff base) (fun _score => noReportPayoff base))
    (raw_test_law :
      ∀ skill base,
        testLaw skill base = model.rawTestLaw skill base)
    (reported_payoff_is_pbo :
      ∀ base score,
        reportedPayoff base score = model.reportedPBO base score) :
    ∀ base,
      ∃ cutoff : ℝ,
        (∀ score,
          reportDecision base score = true → cutoff ≤ score) ∧
          (∀ score,
            cutoff < score → reportDecision base score = true) ∧
            (∀ skill, takeDecision skill base = true) ∧
              (∀ skill,
                0 < testLaw skill base
                  {score | reportDecision base score = false}) := by
  let E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ := {
    testLaw := testLaw
    testLaw_isProbability := testLaw_isProbability
    takeDecision := takeDecision
    reportDecision := reportDecision
    reportedPayoff := reportedPayoff
    noReportPayoff := noReportPayoff
    continuationPayoff_integrable := continuationPayoff_integrable
    estimationConsistent := True
  }
  have hEq : lg21OptionalSequentialEquilibrium E := by
    refine ⟨?_, ?_, trivial⟩
    · intro base
      simpa [E, lg21OptionalSequentialTakeExpectedPayoff,
        lg21OptionalSequentialContinuationPayoff] using take_best_response base
    · intro base
      simpa [E] using report_best_response base
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
    change reportedPayoff base score = intercept + slope * score
    rw [reported_payoff_is_pbo base score]
    simpa [intercept, slope] using model.reportedPBO_eq_affine base score
  let cutoff : ℝ := affineCutoff intercept slope (E.noReportPayoff base)
  have hstrict :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope hreported
  have htestLawAt :
      ∀ skill, E.testLaw skill base = gaussianReal skill (model.testVariance base) := by
    intro skill
    change testLaw skill base = gaussianReal skill (model.testVariance base)
    simpa [LG21HiddenAccessTheorem31GaussianModel.rawTestLaw] using
      raw_test_law skill base
  have htakes : ∀ skill, E.takeDecision skill base = true := by
    exact
      paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
        hEq base (model.testVariance base) (model.testVariance_ne_zero base)
        htestLawAt intercept slope hslope hreported
  have hwithholds :
      ∀ skill,
        0 < E.testLaw skill base
          {score | E.reportDecision base score = false} := by
    intro skill
    rw [htestLawAt skill]
    exact
      paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass_gaussian
        hEq base skill (model.testVariance base)
        (model.testVariance_ne_zero base) intercept slope hslope hreported
  refine ⟨cutoff, ?_, ?_, ?_, ?_⟩
  · intro score hreport
    exact hstrict.1 score hreport
  · intro score hscore
    exact hstrict.2 score hscore
  · intro skill
    exact htakes skill
  · intro skill
    exact hwithholds skill

/--
The corresponding report-required behavioral core at the source's actual
decision time.  The reported test score is noisy after the student decides
whether to take; hence the relevant taking payoff is its conditional
expectation, not the score itself and not a diagonal `test = skill` surrogate.

This proves only the strict sides of the latent-skill cutoff.  Turning those
sides into a positive population mass of nontakers, and identifying the
no-take payoff with a selected conditional PBO, still requires the literal
base-conditioned population/action bridge.
-/
theorem lg21_theorem31_hiddenAccess_reportRequired_behavioral_core
    {Feature Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (model : LG21HiddenAccessTheorem31GaussianModel Feature Base)
    (testLaw : ℝ → Base → Measure ℝ)
    (testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : ℝ → Base → Bool)
    (reportedPayoff : Base → ℝ → ℝ)
    (noTakePayoff : Base → ℝ)
    (reportedPayoff_integrable :
      ∀ skill base, Integrable (reportedPayoff base) (testLaw skill base))
    (take_best_response :
      ∀ base,
        NoProfitableBinaryChoiceDeviation
          (fun skill => takeDecision skill base = true)
          (fun skill => ∫ score, reportedPayoff base score ∂testLaw skill base)
          (fun _skill => noTakePayoff base))
    (raw_test_law :
      ∀ skill base,
        testLaw skill base = model.rawTestLaw skill base)
    (reported_payoff_is_pbo :
      ∀ base score,
        reportedPayoff base score = model.reportedPBO base score) :
    ∀ base,
      ∃ cutoff : ℝ,
        (∀ skill,
          takeDecision skill base = true → cutoff ≤ skill) ∧
          (∀ skill,
            cutoff < skill → takeDecision skill base = true) := by
  let E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ := {
    testLaw := testLaw
    testLaw_isProbability := testLaw_isProbability
    takeDecision := takeDecision
    reportedPayoff := reportedPayoff
    noReportPayoff := noTakePayoff
    reportedPayoff_integrable := reportedPayoff_integrable
    estimationConsistent := True
  }
  have hEq : lg21ReportRequiredSequentialEquilibrium E := by
    refine ⟨?_, trivial⟩
    intro base
    simpa [E, lg21ReportRequiredSequentialTakeExpectedPayoff] using
      take_best_response base
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
    change reportedPayoff base score = intercept + slope * score
    rw [reported_payoff_is_pbo base score]
    simpa [intercept, slope] using model.reportedPBO_eq_affine base score
  have htestLawAt :
      ∀ skill, E.testLaw skill base = gaussianReal skill (model.testVariance base) := by
    intro skill
    change testLaw skill base = gaussianReal skill (model.testVariance base)
    simpa [LG21HiddenAccessTheorem31GaussianModel.rawTestLaw] using
      raw_test_law skill base
  have htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill := by
    intro skill
    change
      (∫ score, E.reportedPayoff base score ∂E.testLaw skill base) =
        intercept + slope * skill
    rw [htestLawAt skill]
    calc
      (∫ score, E.reportedPayoff base score
          ∂gaussianReal skill (model.testVariance base)) =
        ∫ score, intercept + slope * score
          ∂gaussianReal skill (model.testVariance base) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with score
            exact hreported score
      _ = intercept + slope * skill :=
        lg21_gaussian_expected_affine_test_payoff
          skill (model.testVariance base) intercept slope
  let cutoff : ℝ := affineCutoff intercept slope (E.noReportPayoff base)
  have hstrict :=
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope htakePayoff
  refine ⟨cutoff, ?_, ?_⟩
  · intro skill htakes
    exact hstrict.1 skill htakes
  · intro skill hskill
    exact hstrict.2 skill hskill

end

end LG21TestOptionalPolicies
