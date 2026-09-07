import LG21TestOptionalPolicies.ObservedAccessContinuous
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

/-!
# Positive-mass observed-access repair for LG21 Lemma 4.1

The source's Definition 1 is pointwise, but the user-approved repair treats
measure-zero action differences as irrelevant.  This file therefore proves the
strongest conclusion compatible with that convention: under the literal
Gaussian/PBO payoff model, a positive-mass set of access students cannot keep
the score or decline the test in an a.e. best response.

The PBO condition is intentionally stated only when the relevant observation
branch has positive mass.  No finite value, belief, or conditional expectation
is supplied for a zero-mass branch.  Thus these results do not manufacture an
off-path completion.  The caller must still derive the displayed
positive-branch conditional-mean identity from the source population.

## Review boundary

This is proof support, not source credit for Lemma 4.1.  In particular, the
literal finite product Gaussian population must still supply the conditional
Gaussian/disintegration and PBO identities used by `hpositiveBranchPBO`.
Until that bridge is proved and audited on the paper-facing surface, these
theorems establish only a conditional a.e. positive-mass repair.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## Generic Gaussian affine-response support -/

/-- A finite positive-slope affine payoff has a single Gaussian-null tie. -/
theorem lg21_gaussian_affine_tie_null
    (law : GaussianScaleLaw) (intercept slope outside : ℝ)
    (hslope : 0 < slope) :
    law.toMeasure {value | intercept + slope * value = outside} = 0 := by
  have hset :
      {value | intercept + slope * value = outside} =
        ({affineCutoff intercept slope outside} : Set ℝ) := by
    ext value
    constructor
    · intro hvalue
      change intercept + slope * value = outside at hvalue
      rw [Set.mem_singleton_iff]
      unfold affineCutoff
      apply (eq_div_iff (ne_of_gt hslope)).2
      nlinarith [hvalue]
    · intro hvalue
      rw [Set.mem_singleton_iff] at hvalue
      change intercept + slope * value = outside
      subst value
      unfold affineCutoff
      field_simp [ne_of_gt hslope]
      linarith
  rw [hset]
  exact law.toMeasure_singleton_eq_zero _

/--
An a.e. binary best response to a finite positive-slope affine payoff is the
corresponding cutoff rule almost everywhere under a nondegenerate Gaussian.
-/
theorem lg21_gaussian_affine_best_response_ae_cutoff
    (law : GaussianScaleLaw) (decision : ℝ → Bool)
    (intercept slope outside : ℝ) (hslope : 0 < slope)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE law.toMeasure
        (fun value => decision value = true)
        (fun value => intercept + slope * value)
        (fun _value => outside)) :
    ∀ᵐ value ∂law.toMeasure,
      decision value =
        decide (affineCutoff intercept slope outside ≤ value) := by
  apply
    bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
      decision hbest
  · intro value
    exact threshold_le_affine_iff_cutoff_le hslope
  · exact lg21_gaussian_affine_tie_null law intercept slope outside hslope

/-! ## Optional reporting -/

/--
Positive-mass optional nonreporting is unstable under the observed-access PBO
model.  The only source-model bridge assumed here is the conditional identity
for the *actual positive-mass no-report branch*: once the a.e. best response
identifies it as a lower score tail, its PBO estimate is the reported posterior
evaluated at that tail's Gaussian conditional mean.

No value is requested for a zero-mass no-report branch.
-/
theorem paper_lemma4_1_optional_pbo_no_positive_mass_nonreport
    (scoreLaw : GaussianScaleLaw) (reportDecision : ℝ → Bool)
    (intercept slope noReportEstimate : ℝ) (hslope : 0 < slope)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE scoreLaw.toMeasure
        (fun score => reportDecision score = true)
        (fun score => intercept + slope * score)
        (fun _score => noReportEstimate))
    (hpositiveBranchPBO :
      ∀ cutoff : ℝ,
        (∀ᵐ score ∂scoreLaw.toMeasure,
          reportDecision score = decide (cutoff ≤ score)) →
        0 < scoreLaw.toMeasure {score | reportDecision score = false} →
        noReportEstimate =
          intercept + slope *
            standardGaussianLowerTailMean scoreLaw cutoff) :
    ¬ 0 < scoreLaw.toMeasure {score | reportDecision score = false} := by
  intro hpositive
  let cutoff := affineCutoff intercept slope noReportEstimate
  have hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score) := by
    exact lg21_gaussian_affine_best_response_ae_cutoff
      scoreLaw reportDecision intercept slope noReportEstimate hslope hbest
  have hpbo :
      noReportEstimate =
        intercept + slope *
          standardGaussianLowerTailMean scoreLaw cutoff :=
    hpositiveBranchPBO cutoff hcutoff hpositive
  let lowerMean := standardGaussianLowerTailMean scoreLaw cutoff
  have hlower_lt_cutoff : lowerMean < cutoff := by
    exact standardGaussianLowerTailMean_lt_threshold scoreLaw cutoff
  have hinterval_positive :
      0 < scoreLaw.toMeasure (Set.Ioo lowerMean cutoff) :=
    scoreLaw.toMeasure_Ioo_pos hlower_lt_cutoff
  have hresponseAE :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision score = decide (cutoff ≤ score) ∧
          (reportDecision score ≠ true →
            intercept + slope * score ≤ noReportEstimate) := by
    exact hcutoff.and hbest.2
  exact
    ae_property_contradicts_positive_failure_mass
      scoreLaw.toMeasure
      (fun score =>
        reportDecision score = decide (cutoff ≤ score) ∧
          (reportDecision score ≠ true →
            intercept + slope * score ≤ noReportEstimate))
      (fun score => score ∈ Set.Ioo lowerMean cutoff)
      hresponseAE
      (by
        intro score hscore hresponse
        have hdecision_false : reportDecision score = false := by
          simpa [not_le_of_gt hscore.2] using hresponse.1
        have hnotReport : reportDecision score ≠ true := by
          simp [hdecision_false]
        have hpayoff_le := hresponse.2 hnotReport
        have hpayoff_gt : noReportEstimate < intercept + slope * score := by
          rw [hpbo]
          exact affine_strictMono intercept hslope hscore.1
        exact (not_le_of_gt hpayoff_gt) hpayoff_le)
      hinterval_positive

/--
Source-timed optional-reporting form of the positive-mass conclusion.  The
best-response premise is projected directly from Definition 1's ex-post
reporting decision.  The remaining `hpositiveBranchPBO` premise is the one
source-population obligation: it must derive the PBO conditional mean of the
observed positive-mass no-report branch, rather than naming an arbitrary
off-path estimate.
-/
theorem paper_lemma4_1_optional_source_timed_pbo_no_positive_mass_nonreport
    {Skill Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData Skill Base ℝ}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (base : Base) (scoreLaw : GaussianScaleLaw)
    (intercept slope : ℝ) (hslope : 0 < slope)
    (hreported :
      ∀ score, E.reportedPayoff base score = intercept + slope * score)
    (hpositiveBranchPBO :
      ∀ cutoff : ℝ,
        (∀ᵐ score ∂scoreLaw.toMeasure,
          E.reportDecision base score = decide (cutoff ≤ score)) →
        0 < scoreLaw.toMeasure
          {score | E.reportDecision base score = false} →
        E.noReportPayoff base =
          intercept + slope *
            standardGaussianLowerTailMean scoreLaw cutoff) :
    ¬ 0 < scoreLaw.toMeasure
      {score | E.reportDecision base score = false} := by
  apply paper_lemma4_1_optional_pbo_no_positive_mass_nonreport
    scoreLaw (E.reportDecision base) intercept slope (E.noReportPayoff base)
    hslope
  · exact noProfitableBinaryChoiceDeviationAE_of_pointwise
      (μ := scoreLaw.toMeasure)
      (by
        have hsource :=
          lg21OptionalSequentialEquilibrium_report_bestResponse hEq base
        constructor
        · intro score hreport
          simpa [hreported score] using hsource.1 score hreport
        · intro score hnotReport
          simpa [hreported score] using hsource.2 score hnotReport)
  · intro cutoff hcutoff hpositive
    apply hpositiveBranchPBO cutoff hcutoff hpositive

/--
Action feasibility closes the optional protocol at the approved a.e. level:
if a population has zero mass of no-report actions, it also has zero mass of
no-take actions.  This is the measure-level form of `Y = 0 -> X = 0`; it does
not assign a payoff to any zero-mass action.
-/
theorem paper_lemma4_1_optional_all_take_ae_of_all_report_ae
    {Student : Type*} [MeasurableSpace Student]
    (populationLaw : Measure Student)
    (takeDecision reportDecision : Student → Bool)
    (hnoTake_implies_noReport :
      ∀ student,
        takeDecision student = false → reportDecision student = false)
    (hnoReport_zero :
      populationLaw {student | reportDecision student = false} = 0) :
    populationLaw {student | takeDecision student = false} = 0 := by
  apply measure_mono_null
  · intro student hnoTake
    exact hnoTake_implies_noReport student hnoTake
  · exact hnoReport_zero

/-! ## Reporting required after taking -/

/--
Positive-mass non-taking is unstable under the actual Definition 1
expected-estimate objective.  The take payoff is the Gaussian expectation of
the observed-access PBO posterior, hence the displayed positive-slope affine
function of latent skill.  The source bridge is needed only for a positive-mass
no-take branch, where PBO identifies its estimate with the Gaussian lower-tail
conditional mean.  In particular, this theorem does *not* use the source
proof's later probability-of-a-better-score behavioral reinterpretation.
-/
theorem paper_lemma4_1_report_required_pbo_no_positive_mass_no_take
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool)
    (weight noTakeEstimate : ℝ)
    (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE skillLaw.toMeasure
        (fun skill => takeDecision skill = true)
        (fun skill =>
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill)
        (fun _skill => noTakeEstimate))
    (hpositiveBranchPBO :
      ∀ cutoff : ℝ,
        (∀ᵐ skill ∂skillLaw.toMeasure,
          takeDecision skill = decide (cutoff ≤ skill)) →
        0 < skillLaw.toMeasure {skill | takeDecision skill = false} →
        noTakeEstimate = standardGaussianLowerTailMean skillLaw cutoff) :
    ¬ 0 < skillLaw.toMeasure {skill | takeDecision skill = false} := by
  intro hpositive
  let intercept := (1 - weight) * skillLaw.mean
  let cutoff := affineCutoff intercept weight noTakeEstimate
  have htakePayoff :
      ∀ skill,
        lg21ObservedAccessReportedPosterior skillLaw.mean weight skill =
          intercept + weight * skill := by
    intro skill
    simp only [lg21ObservedAccessReportedPosterior, intercept]
  have hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        takeDecision skill = decide (cutoff ≤ skill) := by
    have hbest' :
        NoProfitableBinaryChoiceDeviationAE skillLaw.toMeasure
          (fun skill => takeDecision skill = true)
          (fun skill => intercept + weight * skill)
          (fun _skill => noTakeEstimate) := by
      simpa only [htakePayoff] using hbest
    exact lg21_gaussian_affine_best_response_ae_cutoff
      skillLaw takeDecision intercept weight noTakeEstimate hweight hbest'
  have hpbo : noTakeEstimate = standardGaussianLowerTailMean skillLaw cutoff :=
    hpositiveBranchPBO cutoff hcutoff hpositive
  let indifferentScore :=
    lg21ObservedAccessIndifferentTestScore
      skillLaw.mean weight noTakeEstimate
  have hnoTake_lt_mean : noTakeEstimate < skillLaw.mean := by
    rw [hpbo]
    exact lg21_standardGaussianLowerTailMean_lt_parent_mean skillLaw cutoff
  have hindifferent_lt_noTake : indifferentScore < noTakeEstimate := by
    exact lg21ObservedAccessIndifferentTestScore_lt_noTakeEstimate
      skillLaw.mean noTakeEstimate hweight hweight_lt_one hnoTake_lt_mean
  have hnoTake_lt_cutoff : noTakeEstimate < cutoff := by
    rw [hpbo]
    exact standardGaussianLowerTailMean_lt_threshold skillLaw cutoff
  have hindifferent_eq_cutoff : indifferentScore = cutoff := by
    simp only [indifferentScore, cutoff,
      lg21ObservedAccessIndifferentTestScore, intercept]
  rw [hindifferent_eq_cutoff] at hindifferent_lt_noTake
  linarith

/--
Source-timed report-required form of the positive-mass conclusion.  Its
take-payoff identity is the actual Definition 1 expectation over the test
law.  Therefore no probability-of-a-better-score convention is used or
silently imported from the source proof.
-/
theorem paper_lemma4_1_report_required_source_timed_pbo_no_positive_mass_no_take
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : GaussianScaleLaw)
    (weight : ℝ) (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (htakeExpected :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill)
    (hpositiveBranchPBO :
      ∀ cutoff : ℝ,
        (∀ᵐ skill ∂skillLaw.toMeasure,
          E.takeDecision skill base = decide (cutoff ≤ skill)) →
        0 < skillLaw.toMeasure
          {skill | E.takeDecision skill base = false} →
        E.noReportPayoff base =
          standardGaussianLowerTailMean skillLaw cutoff) :
    ¬ 0 < skillLaw.toMeasure
      {skill | E.takeDecision skill base = false} := by
  apply paper_lemma4_1_report_required_pbo_no_positive_mass_no_take
    skillLaw (E.takeDecision · base) weight (E.noReportPayoff base)
    hweight hweight_lt_one
  · have hbest :=
      lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base
    have hbestAE :=
      noProfitableBinaryChoiceDeviationAE_of_pointwise
        (μ := skillLaw.toMeasure) hbest
    simpa only [htakeExpected] using hbestAE
  · intro cutoff hcutoff hpositive
    apply hpositiveBranchPBO cutoff hcutoff hpositive

end

end LG21TestOptionalPolicies
