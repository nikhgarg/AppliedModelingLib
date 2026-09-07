import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium
import LG21TestOptionalPolicies.PositiveReporterStrictGain

/-!
# Positive-reporter closure for hidden-access Theorem 3.1

This module closes the attained-positive-reporter part of the hidden-access
argument without assigning a value to an empty reporting branch.  The source
PBO is required only on the literal selected reporter law.  The remaining
input is a fibrewise disintegration certificate: at a base with both takers
and reporters, it identifies the actual taker population with the selected
Gaussian law and transports the a.e. reporting best response to each
individual's Gaussian score law.

The certificate deliberately does not cover bases with zero reporter mass.
Those require the paper's separate positive-mass candidate-PBO refinement.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LG21HiddenAccessLiteralSourceEquilibriumAE

/-- The a.e. source carrier projected to sequential payoff data.  This is a
data projection only: it does not upgrade the carrier's a.e. best responses
to a pointwise equilibrium. -/
def toOptionalSequentialData
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    LG21OptionalSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ where
  testLaw := E.testLaw
  testLaw_isProbability := E.testLaw_isProbability
  takeDecision := E.takeDecision
  reportDecision := E.reportDecision
  reportedPayoff := E.reportedPayoff
  noReportPayoff := E.noReportPayoff
  continuationPayoff_integrable := E.continuationPayoff_integrable
  estimationConsistent := True

end LG21HiddenAccessLiteralSourceEquilibriumAE

/--
The exact local evidence needed to use an attained reporter branch in the
hidden-access model.  `selected` is the literal set of latent types who take
at this fixed public base.  The PBO identity is only under its positive
reporter law; the final field is the separately proved localization of the
source a.e. reporting best response to an individual Gaussian score draw.

This carrier contains no cutoff, no unselected posterior, and no value on a
zero-reporter branch.
-/
structure LG21PositiveReporterSelectedGaussianFibre
    {Base : Type*}
    (E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ) (base : Base)
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ) : Prop where
  selected_measurable : MeasurableSet selected
  selected_eq_actual_takers : ∀ skill,
    skill ∈ selected ↔ E.takeDecision skill base = true
  selected_positive : 0 < gaussianReal priorMean priorVariance.toNNReal selected
  report_measurable : MeasurableSet {score | E.reportDecision base score = true}
  priorVariance_pos : 0 < priorVariance
  noiseVariance_pos : 0 < noiseVariance
  testLaw_eq_gaussian : ∀ skill,
    E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal
  reporter_positive :
    0 < normalizedSelectedBase
      (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected)
      {score | E.reportDecision base score = true}
  reported_pbo :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    E.reportedPayoff base =ᵐ[
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected))
        {score | E.reportDecision base score = true}]
      fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score
  report_best_response_on_reporter_law :
    ∀ᵐ score ∂lg21NormalizedRestriction
      (normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected))
      {score | E.reportDecision base score = true},
      E.noReportPayoff base ≤ E.reportedPayoff base score
  report_best_response_under_each_testLaw : ∀ skill,
    ∀ᵐ score ∂E.testLaw skill base,
      E.reportDecision base score = true ->
        E.noReportPayoff base ≤ E.reportedPayoff base score

/--
The expected-gain lemma in the source carrier needs only an a.e. score-stage
best response under the particular test law.  This is the a.e. counterpart of
the pointwise sequential-equilibrium helper and is what a literal source-law
disintegration supplies.
-/
theorem lg21_optional_testExpectedPayoff_gt_noReport_of_ae_score_bestResponse
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (skill : Skill) (base : Base)
    (hbest : ∀ᵐ test ∂E.testLaw skill base,
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
  let gain : Test -> ℝ := fun test =>
    lg21OptionalSequentialContinuationPayoff E base test -
      E.noReportPayoff base
  have hgain_nonneg : ∀ᵐ test ∂E.testLaw skill base, 0 ≤ gain test := by
    filter_upwards [hbest] with test hbest
    by_cases hreport : E.reportDecision base test = true
    · simpa [gain, lg21OptionalSequentialContinuationPayoff, hreport] using
        sub_nonneg.mpr (hbest hreport)
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
    (integral_pos_iff_support_of_nonneg_ae hgain_nonneg hgain_integrable).2
      hsupport_pos
  have hgain_identity :
      (∫ test, gain test ∂E.testLaw skill base) =
        lg21OptionalSequentialTakeExpectedPayoff E skill base -
          E.noReportPayoff base := by
    have hcontinuation :
        Integrable (fun test => lg21OptionalSequentialContinuationPayoff E base test)
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

namespace LG21PositiveReporterSelectedGaussianFibre

/-- A literal positive reporter fibre gives every latent skill a strict
source-timed expected gain from testing. -/
theorem strictExpectedGain
    {Base : Type*}
    {E : LG21OptionalSequentialEquilibriumData ℝ Base ℝ}
    {base : Base} {priorMean priorVariance noiseVariance : ℝ}
    {selected : Set ℝ}
    (H : LG21PositiveReporterSelectedGaussianFibre E base
      priorMean priorVariance noiseVariance selected) (skill : ℝ) :
    E.noReportPayoff base <
      lg21OptionalSequentialTakeExpectedPayoff E skill base := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hstrictGain :
      0 < gaussianReal skill noiseVariance.toNNReal
        {score | E.reportDecision base score = true ∧
          E.noReportPayoff base < E.reportedPayoff base score} := by
    exact lg21_positive_reporter_selectedGaussian_strict_test_gain
      priorMean priorVariance noiseVariance selected (E.reportDecision base)
      H.priorVariance_pos H.noiseVariance_pos H.selected_measurable
      H.selected_positive H.report_measurable H.reporter_positive
      (E.reportedPayoff base) (E.noReportPayoff base) H.reported_pbo
      H.report_best_response_on_reporter_law skill
  apply lg21_optional_testExpectedPayoff_gt_noReport_of_ae_score_bestResponse
    E skill base (H.report_best_response_under_each_testLaw skill)
  rw [H.testLaw_eq_gaussian skill]
  exact hstrictGain

end LG21PositiveReporterSelectedGaussianFibre

/--
The remaining global source-law obligation for the attained-reporter route.
For each a.e. literal access/no-take profile, it asks for the positive
selected reporter fibre above.  It says exactly which disintegration and
best-response localization still have to be proved; no null-branch PBO or
cutoff is supplied here.
-/
def LG21HiddenAccessPositiveReporterFibreClosure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  ∀ᵐ profile ∂lg21HiddenAccessAccessLatentBaseLaw M testFeature,
    E.takeDecision profile.1 profile.2 = false ->
      ∃ (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ),
        LG21PositiveReporterSelectedGaussianFibre E.toOptionalSequentialData
          profile.2 priorMean priorVariance noiseVariance selected

/--
Once the literal positive-reporter fibre closure is discharged, the source's
a.e. pre-score best response eliminates all actual access/no-take mass.  This
is intentionally a closure theorem, not a claim that the displayed fibre
certificate follows from a name or an off-path conditional distribution.
-/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent_measure_zero_of_positiveReporterFibreClosure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hclosure : LG21HiddenAccessPositiveReporterFibreClosure E) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  apply E.activeNoTakeEvent_measure_zero_of_globalStrictGain
  filter_upwards [hclosure] with profile hclosure hnoTake
  rcases hclosure hnoTake with
    ⟨priorMean, priorVariance, noiseVariance, selected, H⟩
  simpa only [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData,
    lg21OptionalSequentialTakeExpectedPayoff,
    lg21OptionalSequentialContinuationPayoff] using
    H.strictExpectedGain profile.1

end

end LG21TestOptionalPolicies
