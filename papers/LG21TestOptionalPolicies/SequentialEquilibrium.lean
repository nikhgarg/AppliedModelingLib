import LG21TestOptionalPolicies.MainTheorems
import AppliedModelingLib.GameTheory.Choice.BinaryAE
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Source-timed sequential equilibria for LG21

Definition 1 has two decision times.  A student chooses whether to take the
test from latent skill and the base profile, before the test noise is drawn;
after seeing the realized test score, a student in the optional-reporting
regime chooses whether to report.  The static `LG21SourceEquilibriumData`
surface is useful for many finite reductions, but it puts both decisions in a
single realized information record.  In the report-required regime that can
incorrectly force an ex-ante taking decision to agree with a score-dependent
decision at every realized score.

This file gives the source-timed interface directly.  The payoff from taking
is a genuine integral over the conditional test law.  It then proves the
arbitrary-supplied-equilibrium cutoff conclusions that are valid under the
paper's weak-best-response convention:

* on either strict side of the unique affine indifference point, the decision
  is forced;
* under a continuous type law the decision is the cutoff rule almost
  everywhere;
* exact pointwise `if and only if` requires the explicit convention that the
  student chooses the test action at indifference.

The last distinction isolates the source's measure-zero tie convention from
the substantive equilibrium argument.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## Sequential source games -/

/--
Optional reporting with the source's decision timing.  `testLaw skill base`
is drawn only after `takeDecision skill base`; `reportDecision base test` is
then evaluated after the score is observed.  The same no-report payoff applies
to not taking and to taking but withholding, because hidden access makes those
information sets observationally identical.
-/
structure LG21OptionalSequentialEquilibriumData
    (Skill Base Test : Type*) [MeasurableSpace Test] where
  testLaw : Skill → Base → Measure Test
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : Skill → Base → Bool
  reportDecision : Base → Test → Bool
  reportedPayoff : Base → Test → ℝ
  noReportPayoff : Base → ℝ
  continuationPayoff_integrable :
    ∀ skill base,
      Integrable
        (fun test ↦
          if reportDecision base test then
            reportedPayoff base test
          else
            noReportPayoff base)
        (testLaw skill base)
  estimationConsistent : Prop

/-- Realized continuation payoff after an optional test is drawn. -/
def lg21OptionalSequentialContinuationPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (base : Base) (test : Test) : ℝ :=
  if E.reportDecision base test then
    E.reportedPayoff base test
  else
    E.noReportPayoff base

/-- Ex-ante payoff from taking, integrating over the not-yet-observed test. -/
def lg21OptionalSequentialTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  ∫ test,
    lg21OptionalSequentialContinuationPayoff E base test
      ∂E.testLaw skill base

/--
Sequential Definition 1 for optional reporting: the taking decision is an
ex-ante binary best response, the reporting decision is an ex-post binary
best response, and the estimator is consistent with both decisions.
-/
def lg21OptionalSequentialEquilibrium
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test) : Prop :=
  (∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill ↦ E.takeDecision skill base = true)
        (fun skill ↦ lg21OptionalSequentialTakeExpectedPayoff E skill base)
        (fun _skill ↦ E.noReportPayoff base)) ∧
    (∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun test ↦ E.reportDecision base test = true)
        (E.reportedPayoff base)
        (fun _test ↦ E.noReportPayoff base)) ∧
      E.estimationConsistent

/-- Report-required timing: taking is chosen before the Gaussian test draw. -/
structure LG21ReportRequiredSequentialEquilibriumData
    (Skill Base Test : Type*) [MeasurableSpace Test] where
  testLaw : Skill → Base → Measure Test
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : Skill → Base → Bool
  reportedPayoff : Base → Test → ℝ
  noReportPayoff : Base → ℝ
  reportedPayoff_integrable :
    ∀ skill base, Integrable (reportedPayoff base) (testLaw skill base)
  estimationConsistent : Prop

/-- Expected school estimate when the student takes and must report. -/
def lg21ReportRequiredSequentialTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  ∫ test, E.reportedPayoff base test ∂E.testLaw skill base

/--
Sequential Definition 1 for reporting required after taking.  There is no
score-contingent reporting decision: taking automatically entails reporting.
-/
def lg21ReportRequiredSequentialEquilibrium
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test) : Prop :=
  (∀ base,
      NoProfitableBinaryChoiceDeviation
        (fun skill ↦ E.takeDecision skill base = true)
        (fun skill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
        (fun _skill ↦ E.noReportPayoff base)) ∧
    E.estimationConsistent

/--
When access is observed and taking/reporting is required given access, no
student decision remains; equilibrium is exactly estimator consistency.
-/
structure LG21RequiredGivenAccessSequentialEquilibriumData
    (Base Test : Type*) where
  reportedPayoff : Base → Test → ℝ
  estimationConsistent : Prop

def lg21RequiredGivenAccessSequentialEquilibrium
    {Base Test : Type*}
    (E : LG21RequiredGivenAccessSequentialEquilibriumData Base Test) : Prop :=
  E.estimationConsistent

/-- The three source requirement protocols, represented at their true timing. -/
inductive LG21SequentialRequirementProtocol where
  | optionalReporting
  | reportRequiredAfterTaking
  | reportRequiredGivenAccess
deriving DecidableEq

/-! ## Projection lemmas from arbitrary supplied equilibria -/

theorem lg21OptionalSequentialEquilibrium_take_bestResponse
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21OptionalSequentialEquilibriumData Skill Base Test}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base) :
    NoProfitableBinaryChoiceDeviation
      (fun skill ↦ E.takeDecision skill base = true)
      (fun skill ↦ lg21OptionalSequentialTakeExpectedPayoff E skill base)
      (fun _skill ↦ E.noReportPayoff base) :=
  hEq.1 base

theorem lg21OptionalSequentialEquilibrium_report_bestResponse
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21OptionalSequentialEquilibriumData Skill Base Test}
    (hEq : lg21OptionalSequentialEquilibrium E) (base : Base) :
    NoProfitableBinaryChoiceDeviation
      (fun test ↦ E.reportDecision base test = true)
      (E.reportedPayoff base)
      (fun _test ↦ E.noReportPayoff base) :=
  hEq.2.1 base

theorem lg21ReportRequiredSequentialEquilibrium_take_bestResponse
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E) (base : Base) :
    NoProfitableBinaryChoiceDeviation
      (fun skill ↦ E.takeDecision skill base = true)
      (fun skill ↦
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
      (fun _skill ↦ E.noReportPayoff base) :=
  hEq.1 base

/-! ## Optional reporting: every supplied equilibrium has an affine cutoff -/

/--
Weak best response fixes the reporting decision on both strict sides of the
unique affine indifference point.  At the single tie the source's weak
preference definition permits either action.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score) :
    (∀ score,
        E.reportDecision base score = true →
          affineCutoff intercept slope (E.noReportPayoff base) ≤ score) ∧
      (∀ score,
        affineCutoff intercept slope (E.noReportPayoff base) < score →
          E.reportDecision base score = true) := by
  have hbest :=
    lg21OptionalSequentialEquilibrium_report_bestResponse hEq base
  constructor
  · intro score hreport
    have hle := hbest.1 score hreport
    rw [hreported score] at hle
    exact
      (paper_reporting_affine_estimate_threshold_iff_cutoff hslope).1 hle
  · intro score hstrict
    by_contra hnotReport
    have hle := hbest.2 score hnotReport
    rw [hreported score] at hle
    have hscore_le :
        score ≤ affineCutoff intercept slope (E.noReportPayoff base) :=
      (affine_le_threshold_iff_le_cutoff hslope).1 hle
    exact (not_le_of_gt hstrict) hscore_le

/--
For a continuous score law (expressed by a null payoff-tie set), every
arbitrary supplied optional-reporting equilibrium is the source cutoff rule
almost everywhere.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_ae_cutoff
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (htie :
      scoreLaw
          {score |
            E.reportedPayoff base score = E.noReportPayoff base} = 0) :
    ∀ᵐ score ∂scoreLaw,
      E.reportDecision base score =
        decide
          (affineCutoff intercept slope (E.noReportPayoff base) ≤ score) := by
  have hbest :=
    lg21OptionalSequentialEquilibrium_report_bestResponse hEq base
  have hbestAE :
      NoProfitableBinaryChoiceDeviationAE scoreLaw
        (fun score ↦ E.reportDecision base score = true)
        (E.reportedPayoff base)
        (fun _score ↦ E.noReportPayoff base) :=
    noProfitableBinaryChoiceDeviationAE_of_pointwise hbest
  apply
    bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
      (E.reportDecision base) hbestAE
  · intro score
    rw [hreported score]
    exact paper_reporting_affine_estimate_threshold_iff_cutoff hslope
  · exact htie

/--
Exact source wording follows once the tie convention is explicit: report at
indifference.  No additional threshold-shape premise is assumed.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_exact_cutoff_of_tiebreak
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (htie :
      ∀ score,
        E.reportedPayoff base score = E.noReportPayoff base →
          E.reportDecision base score = true) :
    ∀ score,
      E.reportDecision base score = true ↔
        affineCutoff intercept slope (E.noReportPayoff base) ≤ score := by
  have hbest :=
    lg21OptionalSequentialEquilibrium_report_bestResponse hEq base
  apply
    choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak
      hbest
  · intro score
    rw [hreported score]
    exact paper_reporting_affine_estimate_threshold_iff_cutoff hslope
  · exact htie

/--
The strict-side theorem alone rules out both extreme reporting profiles in
every supplied equilibrium: real scores exist strictly below and strictly
above the finite affine cutoff.  No tie convention is needed.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_nonextreme_reporting
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score) :
    (∃ score, E.reportDecision base score = true) ∧
      ∃ score, E.reportDecision base score = false := by
  let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
  have hstrict :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope hreported
  constructor
  · refine ⟨cutoff + 1, hstrict.2 (cutoff + 1) ?_⟩
    linarith
  · have hnot : E.reportDecision base (cutoff - 1) ≠ true := by
      intro hreport
      have hcutoff := hstrict.1 (cutoff - 1) hreport
      dsimp [cutoff] at hcutoff
      linarith
    have hfalse : E.reportDecision base (cutoff - 1) = false := by
      cases hdecision : E.reportDecision base (cutoff - 1)
      · rfl
      · exact False.elim (hnot hdecision)
    exact ⟨cutoff - 1, hfalse⟩

/--
If the continuous score law gives positive mass to the strict lower side of
the cutoff, withholding has positive probability in every supplied
equilibrium.  For the source Gaussian law, this support premise is the usual
positive lower-tail fact.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (hbelow :
      0 < scoreLaw
        (Set.Iio (affineCutoff intercept slope (E.noReportPayoff base)))) :
    0 < scoreLaw {score | E.reportDecision base score = false} := by
  have hstrict :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope hreported
  apply lt_of_lt_of_le hbelow
  apply measure_mono
  intro score hscore
  have hnot : E.reportDecision base score ≠ true := by
    intro hreport
    exact (not_le_of_gt hscore) (hstrict.1 score hreport)
  cases hdecision : E.reportDecision base score
  · exact hdecision
  · exact False.elim (hnot hdecision)

/-- Positive upper-tail score mass gives positive mass of reporters. -/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_reporting_mass
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (habove :
      0 < scoreLaw
        (Set.Ioi (affineCutoff intercept slope (E.noReportPayoff base)))) :
    0 < scoreLaw {score | E.reportDecision base score = true} := by
  have hstrict :=
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope hreported
  apply lt_of_lt_of_le habove
  apply measure_mono
  intro score hscore
  exact hstrict.2 score hscore

/-- Every Gaussian strict lower tail has positive mass. -/
theorem lg21_gaussianReal_Iio_pos
    (mean cutoff : ℝ) {variance : NNReal} (hvariance : variance ≠ 0) :
    0 < gaussianReal mean variance (Set.Iio cutoff) := by
  have hinterval :
      0 < gaussianReal mean variance (Set.Ioo (cutoff - 1) cutoff) :=
    gaussianReal_Ioo_pos mean hvariance (by linarith)
  exact lt_of_lt_of_le hinterval (measure_mono Set.Ioo_subset_Iio_self)

/--
In the nondegenerate Gaussian source score law, every arbitrary optional
equilibrium therefore has a positive-mass withholding set below its affine
reporting cutoff.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass_gaussian
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreMean : ℝ) (scoreVariance : NNReal)
    (hvariance : scoreVariance ≠ 0)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score) :
    0 < gaussianReal scoreMean scoreVariance
      {score | E.reportDecision base score = false} := by
  apply
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_withholding_mass
      hEq base (gaussianReal scoreMean scoreVariance)
      intercept slope hslope hreported
  exact
    lg21_gaussianReal_Iio_pos scoreMean
      (affineCutoff intercept slope (E.noReportPayoff base)) hvariance

/--
The same Gaussian support argument gives positive reporter mass, so neither
extreme reporting profile is an equilibrium even in the continuum model.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_reporting_mass_gaussian
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreMean : ℝ) (scoreVariance : NNReal)
    (hvariance : scoreVariance ≠ 0)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score) :
    0 < gaussianReal scoreMean scoreVariance
      {score | E.reportDecision base score = true} := by
  apply
    paper_theorem3_1_arbitrary_optional_sequential_equilibrium_positive_reporting_mass
      hEq base (gaussianReal scoreMean scoreVariance)
      intercept slope hslope hreported
  let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
  have hinterval :
      0 < gaussianReal scoreMean scoreVariance
        (Set.Ioo cutoff (cutoff + 1)) :=
    gaussianReal_Ioo_pos scoreMean hvariance (by linarith)
  exact lt_of_lt_of_le hinterval (measure_mono Set.Ioo_subset_Ioi_self)

/-! ## Ex-ante taking: positive strict continuation value forces all taking -/

/--
If the set of realized scores at which reporting gives a strict gain has
positive conditional probability, taking has strictly larger expected payoff
than the observationally identical no-take action.
-/
theorem lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (hEq : lg21OptionalSequentialEquilibrium E)
    (skill : Skill) (base : Base)
    (hpositive :
      0 < E.testLaw skill base
        {test |
          E.reportDecision base test = true ∧
            E.noReportPayoff base < E.reportedPayoff base test}) :
    E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E skill base := by
  letI : IsProbabilityMeasure (E.testLaw skill base) :=
    E.testLaw_isProbability skill base
  let gain : Test → ℝ := fun test ↦
    lg21OptionalSequentialContinuationPayoff E base test -
      E.noReportPayoff base
  have hgain_nonneg : ∀ test, 0 ≤ gain test := by
    intro test
    by_cases hreport : E.reportDecision base test = true
    · have hle :=
        (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).1
          test hreport
      simpa [gain, lg21OptionalSequentialContinuationPayoff, hreport]
        using sub_nonneg.mpr hle
    · have hreport_false : E.reportDecision base test = false := by
        cases hdecision : E.reportDecision base test
        · rfl
        · exact False.elim (hreport hdecision)
      simp [gain, lg21OptionalSequentialContinuationPayoff, hreport_false]
  have hgain_integrable : Integrable gain (E.testLaw skill base) := by
    exact
      (E.continuationPayoff_integrable skill base).sub
        (integrable_const (E.noReportPayoff base))
  have hsupport_pos :
      0 < E.testLaw skill base (Function.support gain) := by
    apply lt_of_lt_of_le hpositive
    apply measure_mono
    intro test htest
    change gain test ≠ 0
    rcases htest with ⟨hreport, hstrict⟩
    simp [gain, lg21OptionalSequentialContinuationPayoff, hreport,
      sub_ne_zero.mpr (ne_of_gt hstrict)]
  have hintegral_pos : 0 < ∫ test, gain test ∂E.testLaw skill base :=
    (integral_pos_iff_support_of_nonneg
      hgain_nonneg hgain_integrable).2 hsupport_pos
  have hgain_identity :
      (∫ test, gain test ∂E.testLaw skill base) =
        lg21OptionalSequentialTakeExpectedPayoff E skill base -
          E.noReportPayoff base := by
    have hcontinuation :
        Integrable
          (fun test => lg21OptionalSequentialContinuationPayoff E base test)
          (E.testLaw skill base) := by
      simpa [lg21OptionalSequentialContinuationPayoff] using
        E.continuationPayoff_integrable skill base
    calc
      (∫ test, gain test ∂E.testLaw skill base) =
          (∫ test, lg21OptionalSequentialContinuationPayoff E base test
            ∂E.testLaw skill base) -
            (∫ _test, E.noReportPayoff base ∂E.testLaw skill base) := by
              exact integral_sub hcontinuation
                (integrable_const (E.noReportPayoff base))
      _ = lg21OptionalSequentialTakeExpectedPayoff E skill base -
            E.noReportPayoff base := by
              simp [lg21OptionalSequentialTakeExpectedPayoff]
  rw [hgain_identity] at hintegral_pos
  linarith

/-- The preceding expected-gain argument only needs the report-stage
best-response implication itself.  This source-facing form avoids routing a
literal action proof through an opaque equilibrium-consistency wrapper. -/
theorem lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain_of_reportBR
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (skill : Skill) (base : Base)
    (hreportBR : ∀ test,
      E.reportDecision base test = true ->
        E.noReportPayoff base ≤ E.reportedPayoff base test)
    (hpositive :
      0 < E.testLaw skill base
        {test |
          E.reportDecision base test = true ∧
            E.noReportPayoff base < E.reportedPayoff base test}) :
    E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E skill base := by
  letI : IsProbabilityMeasure (E.testLaw skill base) :=
    E.testLaw_isProbability skill base
  let gain : Test → ℝ := fun test ↦
    lg21OptionalSequentialContinuationPayoff E base test -
      E.noReportPayoff base
  have hgain_nonneg : ∀ test, 0 ≤ gain test := by
    intro test
    by_cases hreport : E.reportDecision base test = true
    · have hle := hreportBR test hreport
      simpa [gain, lg21OptionalSequentialContinuationPayoff, hreport]
        using sub_nonneg.mpr hle
    · have hreport_false : E.reportDecision base test = false := by
        cases hdecision : E.reportDecision base test
        · rfl
        · exact False.elim (hreport hdecision)
      simp [gain, lg21OptionalSequentialContinuationPayoff, hreport_false]
  have hgain_integrable : Integrable gain (E.testLaw skill base) := by
    exact (E.continuationPayoff_integrable skill base).sub
      (integrable_const (E.noReportPayoff base))
  have hsupport_pos :
      0 < E.testLaw skill base (Function.support gain) := by
    apply lt_of_lt_of_le hpositive
    apply measure_mono
    intro test htest
    change gain test ≠ 0
    rcases htest with ⟨hreport, hstrict⟩
    simp [gain, lg21OptionalSequentialContinuationPayoff, hreport,
      sub_ne_zero.mpr (ne_of_gt hstrict)]
  have hintegral_pos : 0 < ∫ test, gain test ∂E.testLaw skill base :=
    (integral_pos_iff_support_of_nonneg
      hgain_nonneg hgain_integrable).2 hsupport_pos
  have hgain_identity :
      (∫ test, gain test ∂E.testLaw skill base) =
        lg21OptionalSequentialTakeExpectedPayoff E skill base -
          E.noReportPayoff base := by
    have hcontinuation :
        Integrable
          (fun test => lg21OptionalSequentialContinuationPayoff E base test)
          (E.testLaw skill base) := by
      simpa [lg21OptionalSequentialContinuationPayoff] using
        E.continuationPayoff_integrable skill base
    calc
      (∫ test, gain test ∂E.testLaw skill base) =
          (∫ test, lg21OptionalSequentialContinuationPayoff E base test
            ∂E.testLaw skill base) -
            (∫ _test, E.noReportPayoff base ∂E.testLaw skill base) := by
              exact integral_sub hcontinuation
                (integrable_const (E.noReportPayoff base))
      _ = lg21OptionalSequentialTakeExpectedPayoff E skill base -
            E.noReportPayoff base := by
              simp [lg21OptionalSequentialTakeExpectedPayoff]
  rw [hgain_identity] at hintegral_pos
  linarith

/--
Consequently, every arbitrary supplied optional-reporting equilibrium has all
students take whenever every latent type has positive probability of a
strictly profitable report realization.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21OptionalSequentialEquilibriumData Skill Base Test}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (hpositive :
      ∀ skill base,
        0 < E.testLaw skill base
          {test |
            E.reportDecision base test = true ∧
              E.noReportPayoff base < E.reportedPayoff base test}) :
    ∀ skill base, E.takeDecision skill base = true := by
  intro skill base
  by_contra hnotTake
  have hle :=
    (lg21OptionalSequentialEquilibrium_take_bestResponse hEq base).2
      skill hnotTake
  have hstrict :=
    lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
      E hEq skill base (hpositive skill base)
  linarith

/--
Equivalent source-facing all-take premise: every type's conditional test law
puts positive mass on scores whose reported posterior strictly exceeds the
no-report estimate.  Ex-post best response forces reporting on that set, so
the preceding theorem applies.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_of_positive_gain_mass
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21OptionalSequentialEquilibriumData Skill Base Test}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (hstrictMass :
      ∀ skill base,
        0 < E.testLaw skill base
          {test | E.noReportPayoff base < E.reportedPayoff base test}) :
    ∀ skill base, E.takeDecision skill base = true := by
  apply paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take hEq
  intro skill base
  apply lt_of_lt_of_le (hstrictMass skill base)
  apply measure_mono
  intro test hstrict
  refine ⟨?_, hstrict⟩
  by_contra hnotReport
  have hle :=
    (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).2
      test hnotReport
  exact (not_le_of_gt hstrict) hle

/-- Every nonempty open interval has positive nondegenerate Gaussian mass. -/
theorem lg21_gaussianReal_Ioi_pos
    (mean cutoff : ℝ) {variance : NNReal} (hvariance : variance ≠ 0) :
    0 < gaussianReal mean variance (Set.Ioi cutoff) := by
  have hinterval :
      0 < gaussianReal mean variance (Set.Ioo cutoff (cutoff + 1)) :=
    gaussianReal_Ioo_pos mean hvariance (by linarith)
  exact lt_of_lt_of_le hinterval (measure_mono Set.Ioo_subset_Ioi_self)

/--
Gaussian source specialization of the all-take argument.  A positive-slope
affine reported estimate exceeds the no-report estimate on a nonempty upper
tail, and every nondegenerate conditional Gaussian test law gives that tail
positive mass for every latent type.
-/
theorem paper_theorem3_1_arbitrary_optional_sequential_equilibrium_all_take_gaussian
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (testVariance : NNReal) (hvariance : testVariance ≠ 0)
    (htestLaw :
      ∀ skill, E.testLaw skill base = gaussianReal skill testVariance)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score) :
    ∀ skill, E.takeDecision skill base = true := by
  have hstrictMass :
      ∀ skill,
        0 < E.testLaw skill base
          {score | E.noReportPayoff base < E.reportedPayoff base score} := by
    intro skill
    let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
    have htail :
        0 < gaussianReal skill testVariance (Set.Ioi cutoff) :=
      lg21_gaussianReal_Ioi_pos skill cutoff hvariance
    rw [htestLaw skill]
    apply lt_of_lt_of_le htail
    apply measure_mono
    intro score hscore
    change E.noReportPayoff base < E.reportedPayoff base score
    rw [hreported score]
    have hindifferent :
        intercept + slope * cutoff = E.noReportPayoff base := by
      dsimp [cutoff]
      apply le_antisymm
      · exact (affine_le_threshold_iff_le_cutoff hslope).2 le_rfl
      · exact (threshold_le_affine_iff_cutoff_le hslope).2 le_rfl
    rw [← hindifferent]
    exact affine_strictMono intercept hslope hscore
  intro skill
  have hpositive :
      0 < E.testLaw skill base
        {score |
          E.reportDecision base score = true ∧
            E.noReportPayoff base < E.reportedPayoff base score} := by
    apply lt_of_lt_of_le (hstrictMass skill)
    apply measure_mono
    intro score hstrict
    refine ⟨?_, hstrict⟩
    by_contra hnotReport
    have hle :=
      (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).2
        score hnotReport
    exact (not_le_of_gt hstrict) hle
  by_contra hnotTake
  have hle :=
    (lg21OptionalSequentialEquilibrium_take_bestResponse hEq base).2
      skill hnotTake
  have hstrictExpected :=
    lg21OptionalSequentialTakeExpectedPayoff_gt_noReport_of_positive_strict_gain
      E hEq skill base hpositive
  exact (not_le_of_gt hstrictExpected) hle

/-! ## Report required: noisy tests and arbitrary supplied equilibria -/

/-- The expectation of a positive-slope affine payoff under a Gaussian test. -/
theorem lg21_gaussian_expected_affine_test_payoff
    (mean : ℝ) (variance : NNReal) (intercept slope : ℝ) :
    (∫ test,
        (intercept + slope * test)
          ∂gaussianReal mean variance) =
      intercept + slope * mean := by
  have hid : Integrable (fun test : ℝ ↦ test) (gaussianReal mean variance) :=
    (memLp_id_gaussianReal' (p := 1) (by norm_num)).integrable le_rfl
  rw [integral_add (integrable_const intercept) (hid.const_mul slope)]
  rw [integral_const_mul, integral_id_gaussianReal]
  simp

/--
Thus the report-required taking payoff is affine in latent skill even though
the realized test has nondegenerate Gaussian noise.  This is the source timing
step that a realized-information static game cannot express.
-/
theorem lg21_report_required_gaussian_expected_posterior_affine_in_skill
    (skill : ℝ) (testVariance : NNReal)
    (baseTerm testWeight : ℝ) :
    (∫ test,
        (baseTerm + testWeight * test)
          ∂gaussianReal skill testVariance) =
      baseTerm + testWeight * skill :=
  lg21_gaussian_expected_affine_test_payoff
    skill testVariance baseTerm testWeight

/--
Weak best response again forces the taking decision on the two strict sides
of its affine indifference point, for an arbitrary supplied sequential
equilibrium and without identifying the realized test with latent skill.
-/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_strict_cutoff
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill) :
    (∀ skill,
        E.takeDecision skill base = true →
          affineCutoff intercept slope (E.noReportPayoff base) ≤ skill) ∧
      (∀ skill,
        affineCutoff intercept slope (E.noReportPayoff base) < skill →
          E.takeDecision skill base = true) := by
  have hbest :=
    lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base
  constructor
  · intro skill htakes
    have hle := hbest.1 skill htakes
    change
      E.noReportPayoff base ≤
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base at hle
    rw [htakePayoff skill] at hle
    exact
      (paper_reporting_affine_estimate_threshold_iff_cutoff hslope).1 hle
  · intro skill hstrict
    by_contra hnotTake
    have hle := hbest.2 skill hnotTake
    change
      lg21ReportRequiredSequentialTakeExpectedPayoff E skill base ≤
        E.noReportPayoff base at hle
    rw [htakePayoff skill] at hle
    have hskill_le :
        skill ≤ affineCutoff intercept slope (E.noReportPayoff base) :=
      (affine_le_threshold_iff_le_cutoff hslope).1 hle
    exact (not_le_of_gt hstrict) hskill_le

/--
Under a continuous latent-skill law, every arbitrary supplied
report-required equilibrium is the finite skill-cutoff rule almost everywhere.
-/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_ae_cutoff
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill)
    (htie :
      skillLaw
          {skill |
            lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
              E.noReportPayoff base} = 0) :
    ∀ᵐ skill ∂skillLaw,
      E.takeDecision skill base =
        decide
          (affineCutoff intercept slope (E.noReportPayoff base) ≤ skill) := by
  have hbest :=
    lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base
  have hbestAE :
      NoProfitableBinaryChoiceDeviationAE skillLaw
        (fun skill ↦ E.takeDecision skill base = true)
        (fun skill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
        (fun _skill ↦ E.noReportPayoff base) :=
    noProfitableBinaryChoiceDeviationAE_of_pointwise hbest
  apply
    bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
      (fun skill ↦ E.takeDecision skill base) hbestAE
  · intro skill
    rw [htakePayoff skill]
    exact paper_reporting_affine_estimate_threshold_iff_cutoff hslope
  · exact htie

/-- Exact pointwise skill cutoff under the explicit take-at-indifference rule. -/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_exact_cutoff_of_tiebreak
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill)
    (htie :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
            E.noReportPayoff base →
          E.takeDecision skill base = true) :
    ∀ skill,
      E.takeDecision skill base = true ↔
        affineCutoff intercept slope (E.noReportPayoff base) ≤ skill := by
  have hbest :=
    lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base
  apply
    choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak
      hbest
  · intro skill
    rw [htakePayoff skill]
    exact paper_reporting_affine_estimate_threshold_iff_cutoff hslope
  · exact htie

/--
The report-required taking profile is nonextreme in every supplied equilibrium
whenever its ex-ante Gaussian payoff is positive-slope affine in skill.
-/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_nonextreme_taking
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill) :
    (∃ skill, E.takeDecision skill base = true) ∧
      ∃ skill, E.takeDecision skill base = false := by
  let cutoff := affineCutoff intercept slope (E.noReportPayoff base)
  have hstrict :=
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope htakePayoff
  constructor
  · refine ⟨cutoff + 1, hstrict.2 (cutoff + 1) ?_⟩
    linarith
  · have hnot : E.takeDecision (cutoff - 1) base ≠ true := by
      intro htakes
      have hcutoff := hstrict.1 (cutoff - 1) htakes
      dsimp [cutoff] at hcutoff
      linarith
    have hfalse : E.takeDecision (cutoff - 1) base = false := by
      cases hdecision : E.takeDecision (cutoff - 1) base
      · rfl
      · exact False.elim (hnot hdecision)
    exact ⟨cutoff - 1, hfalse⟩

/-- Positive lower-tail skill mass gives positive mass of non-takers. -/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_withholding_mass
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill)
    (hbelow :
      0 < skillLaw
        (Set.Iio (affineCutoff intercept slope (E.noReportPayoff base)))) :
    0 < skillLaw {skill | E.takeDecision skill base = false} := by
  have hstrict :=
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope htakePayoff
  apply lt_of_lt_of_le hbelow
  apply measure_mono
  intro skill hskill
  have hnot : E.takeDecision skill base ≠ true := by
    intro htakes
    exact (not_le_of_gt hskill) (hstrict.1 skill htakes)
  cases hdecision : E.takeDecision skill base
  · exact hdecision
  · exact False.elim (hnot hdecision)

/-- Positive upper-tail skill mass gives positive mass of takers. -/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_taking_mass
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : Measure ℝ) (intercept slope : ℝ)
    (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill)
    (habove :
      0 < skillLaw
        (Set.Ioi (affineCutoff intercept slope (E.noReportPayoff base)))) :
    0 < skillLaw {skill | E.takeDecision skill base = true} := by
  have hstrict :=
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_strict_cutoff
      hEq base intercept slope hslope htakePayoff
  apply lt_of_lt_of_le habove
  apply measure_mono
  intro skill hskill
  exact hstrict.2 skill hskill

/--
Gaussian latent skill gives the report-required cutoff a positive-mass set of
non-takers in every arbitrary supplied equilibrium.
-/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_withholding_mass_gaussian
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillMean : ℝ) (skillVariance : NNReal)
    (hvariance : skillVariance ≠ 0)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill) :
    0 < gaussianReal skillMean skillVariance
      {skill | E.takeDecision skill base = false} := by
  apply
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_withholding_mass
      hEq base (gaussianReal skillMean skillVariance)
      intercept slope hslope htakePayoff
  exact
    lg21_gaussianReal_Iio_pos skillMean
      (affineCutoff intercept slope (E.noReportPayoff base)) hvariance

/-- Gaussian upper-tail support gives positive mass of takers as well. -/
theorem paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_taking_mass_gaussian
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillMean : ℝ) (skillVariance : NNReal)
    (hvariance : skillVariance ≠ 0)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (htakePayoff :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          intercept + slope * skill) :
    0 < gaussianReal skillMean skillVariance
      {skill | E.takeDecision skill base = true} := by
  apply
    paper_theorem3_1_arbitrary_report_required_sequential_equilibrium_positive_taking_mass
      hEq base (gaussianReal skillMean skillVariance)
      intercept slope hslope htakePayoff
  exact
    lg21_gaussianReal_Ioi_pos skillMean
      (affineCutoff intercept slope (E.noReportPayoff base)) hvariance

end

end LG21TestOptionalPolicies
