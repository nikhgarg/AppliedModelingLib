import LG21TestOptionalPolicies.ReportRequiredPositiveMassPBOBridge
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Selection-aware PBO support for LG21 report-required testing

The report-required part of the source proof first selects reporters by a
latent-skill threshold `q > cutoff`.  Therefore the Bayesian posterior after a
reported score must be the posterior conditional on that same selection event;
it is not the unselected Gaussian affine posterior used by the legacy route.

This file proves the resulting mathematical implication.  It deliberately
does **not** assert that a source equilibrium supplies the selected-posterior
identity, the threshold rule, or an everywhere-defined conditional version.
Those are source-model bridge obligations.  The final theorem makes each one
an explicit argument, so it can be used only after a literal population and
sequential action-law construction has discharged them.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory
open Set

/-! ## Generic strict conditional-mean support -/

/-- An almost-everywhere strict inequality integrates strictly under a probability law. -/
private theorem lg21_integral_lt_integral_of_ae_lt_probability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    {f g : Outcome -> ℝ}
    (hf : Integrable f law) (hg : Integrable g law)
    (hlt : ∀ᵐ outcome ∂law, f outcome < g outcome) :
    (∫ outcome, f outcome ∂law) < ∫ outcome, g outcome ∂law := by
  have hdiff_int : Integrable (fun outcome => g outcome - f outcome) law :=
    hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[law] fun outcome => g outcome - f outcome := by
    filter_upwards [hlt] with outcome hltOutcome
    exact sub_nonneg.mpr (le_of_lt hltOutcome)
  have hsupport_ae :
      ∀ᵐ outcome ∂law,
        outcome ∈ Function.support (fun outcome => g outcome - f outcome) := by
    filter_upwards [hlt] with outcome hltOutcome
    change g outcome - f outcome ≠ 0
    exact ne_of_gt (sub_pos.mpr hltOutcome)
  have hsupport_pos : 0 < law (Function.support fun outcome => g outcome - f outcome) := by
    apply (pos_iff_ne_zero).2
    intro hzero
    have hcompl : law (Function.support (fun outcome => g outcome - f outcome))ᶜ = 0 :=
      mem_ae_iff.mp hsupport_ae
    have huniv : law Set.univ = 0 := by
      rw [← Set.union_compl_self (Function.support fun outcome => g outcome - f outcome)]
      exact measure_union_null hzero hcompl
    rw [IsProbabilityMeasure.measure_univ] at huniv
    norm_num at huniv
  have hpos : 0 < ∫ outcome, g outcome - f outcome ∂law :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2 hsupport_pos
  have hsub :
      (∫ outcome, g outcome - f outcome ∂law) =
        (∫ outcome, g outcome ∂law) - ∫ outcome, f outcome ∂law :=
    integral_sub hg hf
  linarith

/-! ## Threshold-selected reporter posterior -/

/--
The reporter posterior under a threshold selection rule.  For a fixed score,
the school first has an unselected posterior on latent skill and then learns
that a reporter satisfied `cutoff < skill`.
-/
def lg21ReportRequiredUpperTailSelectedPosterior
    {Score : Type*} (unselectedPosterior : Score -> Measure ℝ)
    (cutoff : ℝ) (score : Score) : Measure ℝ :=
  lg21NormalizedRestriction (unselectedPosterior score) (Set.Ioi cutoff)

/--
The selected posterior is concentrated above the taking cutoff.  This follows
from the displayed normalized restriction itself; it is not an affine-posterior
assumption.
-/
theorem lg21_report_required_upper_tail_selected_posterior_ae_above_cutoff
    {Score : Type*} (unselectedPosterior : Score -> Measure ℝ)
    (cutoff : ℝ) (score : Score)
    (hfinite : unselectedPosterior score (Set.Ioi cutoff) ≠ ⊤) :
    ∀ᵐ skill ∂
      lg21ReportRequiredUpperTailSelectedPosterior unselectedPosterior cutoff score,
      cutoff < skill := by
  unfold lg21ReportRequiredUpperTailSelectedPosterior lg21NormalizedRestriction
  refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
  · exact ENNReal.inv_ne_zero.mpr hfinite
  · refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    exact ae_of_all _ fun skill hskill => hskill

/--
The mean of a positive-mass threshold-selected reporter posterior is strictly
above the threshold.  This is the selection-aware replacement for treating the
reporter posterior as the unselected affine Gaussian posterior.
-/
theorem lg21_report_required_upper_tail_selected_posterior_mean_gt_cutoff
    {Score : Type*} (unselectedPosterior : Score -> Measure ℝ)
    (cutoff : ℝ) (score : Score)
    (hpositive : 0 < unselectedPosterior score (Set.Ioi cutoff))
    (hfinite : unselectedPosterior score (Set.Ioi cutoff) ≠ ⊤)
    (hintegrable :
      Integrable (fun skill : ℝ => skill)
        (lg21ReportRequiredUpperTailSelectedPosterior
          unselectedPosterior cutoff score)) :
    cutoff < ∫ skill,
      skill ∂lg21ReportRequiredUpperTailSelectedPosterior
        unselectedPosterior cutoff score := by
  let posterior :=
    lg21ReportRequiredUpperTailSelectedPosterior unselectedPosterior cutoff score
  letI : IsProbabilityMeasure posterior :=
    lg21NormalizedRestriction_isProbability
      (unselectedPosterior score) (Set.Ioi cutoff) (ne_of_gt hpositive) hfinite
  have habove : ∀ᵐ skill ∂posterior, cutoff < skill := by
    simpa [posterior] using
      (lg21_report_required_upper_tail_selected_posterior_ae_above_cutoff
        unselectedPosterior cutoff score hfinite)
  have hstrict :=
    lg21_integral_lt_integral_of_ae_lt_probability posterior
      (f := fun _skill : ℝ => cutoff) (g := fun skill : ℝ => skill)
      (integrable_const cutoff) (by simpa [posterior] using hintegrable) habove
  simpa [posterior] using hstrict

/-- A selected reporter posterior mean lies above any no-take estimate below the cutoff. -/
theorem lg21_report_required_upper_tail_selected_posterior_mean_gt_no_take
    {Score : Type*} (unselectedPosterior : Score -> Measure ℝ)
    (cutoff noTakeEstimate : ℝ) (score : Score)
    (hnoTake_lt_cutoff : noTakeEstimate < cutoff)
    (hpositive : 0 < unselectedPosterior score (Set.Ioi cutoff))
    (hfinite : unselectedPosterior score (Set.Ioi cutoff) ≠ ⊤)
    (hintegrable :
      Integrable (fun skill : ℝ => skill)
        (lg21ReportRequiredUpperTailSelectedPosterior
          unselectedPosterior cutoff score)) :
    noTakeEstimate < ∫ skill,
      skill ∂lg21ReportRequiredUpperTailSelectedPosterior
        unselectedPosterior cutoff score :=
  lt_trans hnoTake_lt_cutoff
    (lg21_report_required_upper_tail_selected_posterior_mean_gt_cutoff
      unselectedPosterior cutoff score hpositive hfinite hintegrable)

/--
If every realized test score is evaluated by the actual threshold-selected
posterior, the ex-ante expected reported estimate strictly beats any no-take
estimate below that threshold.  The test law is kept arbitrary and explicit;
in particular this does not replace noisy tests by `test = skill`.
-/
theorem lg21_report_required_expected_selected_posterior_gt_no_take
    {Test : Type*} [MeasurableSpace Test]
    (testLaw : Measure Test) [IsProbabilityMeasure testLaw]
    (unselectedPosterior : Test -> Measure ℝ)
    (cutoff noTakeEstimate : ℝ) (reportedPBO : Test -> ℝ)
    (hnoTake_lt_cutoff : noTakeEstimate < cutoff)
    (hpositive : ∀ test, 0 < unselectedPosterior test (Set.Ioi cutoff))
    (hfinite : ∀ test, unselectedPosterior test (Set.Ioi cutoff) ≠ ⊤)
    (hintegrable : ∀ test,
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction (unselectedPosterior test) (Set.Ioi cutoff)))
    (hreportedPBO : ∀ test,
      reportedPBO test = ∫ skill,
        skill ∂lg21NormalizedRestriction
          (unselectedPosterior test) (Set.Ioi cutoff))
    (hreportedPBO_integrable : Integrable reportedPBO testLaw) :
    noTakeEstimate < ∫ test, reportedPBO test ∂testLaw := by
  have hpoint : ∀ test, noTakeEstimate < reportedPBO test := by
    intro test
    rw [hreportedPBO test]
    exact lg21_report_required_upper_tail_selected_posterior_mean_gt_no_take
      unselectedPosterior cutoff noTakeEstimate test hnoTake_lt_cutoff
      (hpositive test) (hfinite test) (by
        simpa [lg21ReportRequiredUpperTailSelectedPosterior] using hintegrable test)
  have hstrict :=
    lg21_integral_lt_integral_of_ae_lt_probability testLaw
      (f := fun _test : Test => noTakeEstimate) (g := reportedPBO)
      (integrable_const noTakeEstimate) hreportedPBO_integrable
      (Filter.Eventually.of_forall hpoint)
  simpa using hstrict

/-! ## Corrected report-required positive-mass consequence -/

/--
Selection-aware positive-mass repair for the report-required part of Lemma
4.1.  The no-take PBO is the literal lower-tail conditional mean, while a
taker's reported PBO is the mean of the posterior further conditioned on the
threshold-selected reporter population.  Thus every possible test realization
has expected reported value above the no-take value, contradicting a no-take
best response.

This is still conditional support, not PaperInterface source credit.  A source
bridge must derive the a.e. taking threshold and the selected-posterior
conditionalization from the literal joint Gaussian law, preserving the
earlier taking action in the selected event.  The `forall test` form is an
explicit canonical-posterior version requirement; an a.e. RCD route must also
prove its scope transfers to each deviator's noisy test law.
-/
theorem paper_lemma4_1_report_required_selection_aware_actual_pbo_no_positive_mass_no_take
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : GaussianScaleLaw)
    (cutoff : ℝ)
    (hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        E.takeDecision skill base = decide (cutoff ≤ skill))
    (hnoTakeMeasurable :
      MeasurableSet {skill | E.takeDecision skill base = false})
    (hnoTakePBO :
      ∀ hpositive :
        0 < skillLaw.toMeasure {skill | E.takeDecision skill base = false},
        LG21ReportRequiredActualNoTakePBOModel
          skillLaw (E.takeDecision · base) (E.noReportPayoff base)
          hnoTakeMeasurable hpositive)
    (unselectedPosterior : Test -> Measure ℝ)
    (reportedPBO : Test -> ℝ)
    (hselectedMassPositive :
      ∀ test, 0 < unselectedPosterior test (Set.Ioi cutoff))
    (hselectedMassFinite :
      ∀ test, unselectedPosterior test (Set.Ioi cutoff) ≠ ⊤)
    (hselectedSkillIntegrable : ∀ test,
      Integrable (fun skill : ℝ => skill)
        (lg21NormalizedRestriction (unselectedPosterior test) (Set.Ioi cutoff)))
    (hreportedPBO : ∀ test,
      reportedPBO test = ∫ skill,
        skill ∂lg21NormalizedRestriction
          (unselectedPosterior test) (Set.Ioi cutoff))
    (hreportedPBO_integrable : ∀ skill,
      Integrable reportedPBO (E.testLaw skill base))
    (htakeExpected : ∀ skill,
      lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
        ∫ test, reportedPBO test ∂E.testLaw skill base) :
    ¬ 0 < skillLaw.toMeasure {skill | E.takeDecision skill base = false} := by
  intro hpositive
  have hnoTake_lt_cutoff : E.noReportPayoff base < cutoff :=
    lg21_report_required_actual_pbo_positive_branch
      skillLaw (E.takeDecision · base) (E.noReportPayoff base) cutoff
      hcutoff hnoTakeMeasurable hpositive (hnoTakePBO hpositive)
  have htake_beats_no_take : ∀ skill,
      E.noReportPayoff base <
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base := by
    intro skill
    letI : IsProbabilityMeasure (E.testLaw skill base) :=
      E.testLaw_isProbability skill base
    rw [htakeExpected skill]
    exact lg21_report_required_expected_selected_posterior_gt_no_take
      (E.testLaw skill base) unselectedPosterior cutoff (E.noReportPayoff base)
      reportedPBO hnoTake_lt_cutoff hselectedMassPositive hselectedMassFinite
      hselectedSkillIntegrable hreportedPBO (hreportedPBO_integrable skill)
  have hallTake : ∀ skill, E.takeDecision skill base = true := by
    intro skill
    by_contra hnotTake
    have hbest :=
      (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base).2
        skill hnotTake
    change
      lg21ReportRequiredSequentialTakeExpectedPayoff E skill base <=
        E.noReportPayoff base at hbest
    exact (not_le_of_gt (htake_beats_no_take skill)) hbest
  have hnoTakeEvent :
      {skill | E.takeDecision skill base = false} = (∅ : Set ℝ) := by
    ext skill
    simp [hallTake skill]
  simpa [hnoTakeEvent] using hpositive

end

end LG21TestOptionalPolicies
