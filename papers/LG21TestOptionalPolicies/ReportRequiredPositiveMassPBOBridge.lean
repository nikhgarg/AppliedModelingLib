import LG21TestOptionalPolicies.ObservedAccessPositiveMass
import LG21TestOptionalPolicies.ContinuousPopulation

/-!
# Actual positive-mass PBO bridge for LG21's report-required protocol

This support module makes a candidate no-take PBO in the report-required
branch an actual conditional expectation under a Gaussian cohort law.  It
deliberately does not give a payoff or belief to a zero-mass branch.

The remaining source-facing work is to connect a fixed base-feature cohort of
the paper's joint population to `skillLaw` and to show that the paper-facing
PBO field is this conditional expectation.  Once those connections are made,
the result below supplies the positive-mass premise used by the a.e. Lemma 4.1
route without an opaque lower-tail-mean certificate.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/--
The Bayesian-optimal estimate for an actual positive-mass no-take cohort:
the expectation of latent skill under the normalized restriction of the
cohort's Gaussian law to a measurable no-take action event.
-/
def lg21ReportRequiredActualNoTakePBO
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool)
    (_hmeasurable : MeasurableSet {skill | takeDecision skill = false})
    (_hpositive : 0 < skillLaw.toMeasure {skill | takeDecision skill = false}) : ℝ :=
  ∫ skill,
    skill ∂lg21NormalizedRestriction skillLaw.toMeasure
      {skill | takeDecision skill = false}

/-- The corresponding literal positive-mass lower-tail conditional mean. -/
def lg21GaussianLowerTailConditionalMean
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ)
    (_hpositive : 0 < skillLaw.toMeasure (Set.Iio cutoff)) : ℝ :=
  ∫ skill,
    skill ∂lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)

/-! ## Measure-level action/cutoff identification -/

/--
If an a.e. best response is a cutoff rule, its no-take cohort is the lower
tail up to the Gaussian population law.  This is an equality of events under
the actual law, not a pointwise completion on null types.
-/
theorem lg21_report_required_no_take_event_ae_eq_lower_tail
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool) (cutoff : ℝ)
    (hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        takeDecision skill = decide (cutoff ≤ skill)) :
    {skill | takeDecision skill = false} =ᵐ[skillLaw.toMeasure]
      Set.Iio cutoff := by
  filter_upwards [hcutoff] with skill hskill
  apply propext
  change (takeDecision skill = false) ↔ skill < cutoff
  rw [hskill]
  simp

/--
The literal no-take PBO agrees with the literal lower-tail conditional mean
whenever the actual action rule is a cutoff almost everywhere.
-/
theorem lg21_report_required_actual_no_take_pbo_eq_lower_tail
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool) (cutoff : ℝ)
    (hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        takeDecision skill = decide (cutoff ≤ skill))
    (hmeasurable : MeasurableSet {skill | takeDecision skill = false})
    (hpositive : 0 < skillLaw.toMeasure {skill | takeDecision skill = false}) :
    lg21ReportRequiredActualNoTakePBO skillLaw takeDecision hmeasurable hpositive =
      lg21GaussianLowerTailConditionalMean skillLaw cutoff
        (by
          rw [← measure_congr
            (lg21_report_required_no_take_event_ae_eq_lower_tail
              skillLaw takeDecision cutoff hcutoff)]
          exact hpositive) := by
  have hsets := lg21_report_required_no_take_event_ae_eq_lower_tail
    skillLaw takeDecision cutoff hcutoff
  unfold lg21ReportRequiredActualNoTakePBO
    lg21GaussianLowerTailConditionalMean
  simp only [lg21NormalizedRestriction]
  rw [measure_congr hsets, Measure.restrict_congr_set hsets]

/-! ## Strict lower-tail mean inequality -/

/-- Almost-everywhere strict inequalities integrate strictly under a probability law. -/
private theorem lg21_integral_lt_integral_of_ae_lt_of_probability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    {f g : Outcome → ℝ}
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

/-- A Gaussian skill coordinate is integrable under its literal cohort law. -/
theorem lg21_gaussian_skill_integrable (skillLaw : GaussianScaleLaw) :
    Integrable (fun skill : ℝ => skill) skillLaw.toMeasure := by
  change Integrable (fun skill : ℝ => skill)
    (gaussianReal skillLaw.mean skillLaw.varianceNNReal)
  apply integrable_of_mem_interior_integrableExpSet
  simp

/--
The normalized restriction of a Gaussian cohort to a positive-mass lower tail
is a probability measure.
-/
theorem lg21_lower_tail_normalized_restriction_is_probability
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ)
    (hpositive : 0 < skillLaw.toMeasure (Set.Iio cutoff)) :
    IsProbabilityMeasure
      (lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)) := by
  apply lg21NormalizedRestriction_isProbability
  · exact ne_of_gt hpositive
  · exact measure_ne_top _ _

/--
The skill coordinate remains integrable after conditioning the Gaussian cohort
on a positive-mass lower tail.
-/
theorem lg21_gaussian_skill_integrable_lower_tail_normalized
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ)
    (hpositive : 0 < skillLaw.toMeasure (Set.Iio cutoff)) :
    Integrable (fun skill : ℝ => skill)
      (lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)) := by
  unfold lg21NormalizedRestriction
  apply (lg21_gaussian_skill_integrable skillLaw).restrict.smul_measure
  exact ENNReal.inv_ne_top.mpr (ne_of_gt hpositive)

/--
An actual Gaussian lower-tail conditional mean lies strictly below its finite
cutoff.  The proof is measure-theoretic: the conditional law is concentrated
strictly below the cutoff and has total mass one.
-/
theorem lg21_gaussian_lower_tail_conditional_mean_lt_cutoff
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ)
    (hpositive : 0 < skillLaw.toMeasure (Set.Iio cutoff)) :
    lg21GaussianLowerTailConditionalMean skillLaw cutoff hpositive < cutoff := by
  let ν := lg21NormalizedRestriction skillLaw.toMeasure (Set.Iio cutoff)
  letI : IsProbabilityMeasure ν :=
    lg21_lower_tail_normalized_restriction_is_probability
      skillLaw cutoff hpositive
  have hskill_int : Integrable (fun skill : ℝ => skill) ν := by
    simpa [ν] using
      lg21_gaussian_skill_integrable_lower_tail_normalized
        skillLaw cutoff hpositive
  have hconst_int : Integrable (fun _skill : ℝ => cutoff) ν :=
    integrable_const cutoff
  have htail_ae : ∀ᵐ skill ∂ν, skill < cutoff := by
    dsimp [ν, lg21NormalizedRestriction]
    refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
    · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
    · refine (ae_restrict_iff' measurableSet_Iio).2 ?_
      exact ae_of_all _ fun skill hskill => hskill
  have hconst : (∫ _skill, cutoff ∂ν) = cutoff := by
    simp
  change (∫ skill, skill ∂ν) < cutoff
  rw [← hconst]
  exact lg21_integral_lt_integral_of_ae_lt_of_probability
    ν hskill_int hconst_int htail_ae

/--
The actual Gaussian lower-tail conditional mean also lies strictly below the
parent cohort mean.  This is proved from the literal measure, rather than by
identifying the integral with a pre-supplied Mills-ratio expression: split the
Gaussian cohort into its lower and upper tails, compare their conditional
means, and recombine their integrals.
-/
theorem lg21_gaussian_lower_tail_conditional_mean_lt_parent_mean
    (skillLaw : GaussianScaleLaw) (cutoff : ℝ)
    (hpositive : 0 < skillLaw.toMeasure (Set.Iio cutoff)) :
    lg21GaussianLowerTailConditionalMean skillLaw cutoff hpositive < skillLaw.mean := by
  let μ := skillLaw.toMeasure
  let lower : Set ℝ := Set.Iio cutoff
  let upper : Set ℝ := Set.Ici cutoff
  let lowerLaw := lg21NormalizedRestriction μ lower
  let upperLaw := lg21NormalizedRestriction μ upper
  let lowerMass := μ lower
  let upperMass := μ upper
  let lowerMean := ∫ skill, skill ∂lowerLaw
  let upperMean := ∫ skill, skill ∂upperLaw
  have hupperPositive : 0 < μ upper := by
    have hinterior : 0 < μ (Set.Ioo cutoff (cutoff + 1)) := by
      dsimp [μ]
      exact skillLaw.toMeasure_Ioo_pos (by linarith)
    apply lt_of_lt_of_le hinterior
    apply measure_mono
    intro skill hskill
    exact le_of_lt hskill.1
  letI : IsProbabilityMeasure lowerLaw := by
    dsimp [lowerLaw, μ, lower]
    exact lg21NormalizedRestriction_isProbability
      skillLaw.toMeasure (Set.Iio cutoff) (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure upperLaw := by
    dsimp [upperLaw]
    exact lg21NormalizedRestriction_isProbability
      μ upper (ne_of_gt hupperPositive) (measure_ne_top _ _)
  have hskillInt : Integrable (fun skill : ℝ => skill) μ := by
    dsimp [μ]
    exact lg21_gaussian_skill_integrable skillLaw
  have hLowerInt : Integrable (fun skill : ℝ => skill) lowerLaw := by
    dsimp [lowerLaw, lower, μ]
    apply hskillInt.restrict.smul_measure
    exact ENNReal.inv_ne_top.mpr (ne_of_gt hpositive)
  have hUpperInt : Integrable (fun skill : ℝ => skill) upperLaw := by
    dsimp [upperLaw]
    apply hskillInt.restrict.smul_measure
    exact ENNReal.inv_ne_top.mpr (ne_of_gt hupperPositive)
  have hLowerLt : lowerMean < cutoff := by
    dsimp [lowerMean, lowerLaw, lower, μ]
    exact lg21_gaussian_lower_tail_conditional_mean_lt_cutoff
      skillLaw cutoff hpositive
  have hUpperGe : cutoff ≤ upperMean := by
    have hconstInt : Integrable (fun _skill : ℝ => cutoff) upperLaw :=
      integrable_const cutoff
    have hsupport : (fun _skill : ℝ => cutoff) ≤ᵐ[upperLaw] fun skill => skill := by
      dsimp [upperLaw, lg21NormalizedRestriction]
      refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
      · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
      · refine (ae_restrict_iff' measurableSet_Ici).2 ?_
        exact ae_of_all _ fun skill hskill => hskill
    have h := integral_mono_ae hconstInt hUpperInt hsupport
    simpa [upperMean] using h
  have hMeanOrder : lowerMean < upperMean :=
    lt_of_lt_of_le hLowerLt hUpperGe
  have hscaleLower : lowerMass • lowerLaw = μ.restrict lower := by
    dsimp [lowerMass, lowerLaw, lg21NormalizedRestriction]
    rw [smul_smul, ENNReal.mul_inv_cancel (ne_of_gt hpositive)
      (measure_ne_top _ _), one_smul]
  have hscaleUpper : upperMass • upperLaw = μ.restrict upper := by
    dsimp [upperMass, upperLaw, lg21NormalizedRestriction]
    rw [smul_smul, ENNReal.mul_inv_cancel (ne_of_gt hupperPositive)
      (measure_ne_top _ _), one_smul]
  have hLowerIntegral :
      (∫ skill, skill ∂μ.restrict lower) = lowerMass.toReal * lowerMean := by
    rw [← hscaleLower, integral_smul_measure]
    simp [lowerMean, smul_eq_mul]
  have hUpperIntegral :
      (∫ skill, skill ∂μ.restrict upper) = upperMass.toReal * upperMean := by
    rw [← hscaleUpper, integral_smul_measure]
    simp [upperMean, smul_eq_mul]
  have hcompl : lowerᶜ = upper := by
    dsimp [lower, upper]
    ext skill
    simp
  have hdecomp : μ.restrict lower + μ.restrict upper = μ := by
    rw [← hcompl]
    exact Measure.restrict_add_restrict_compl measurableSet_Iio
  have hGlobalIntegral :
      (∫ skill, skill ∂μ) =
        lowerMass.toReal * lowerMean + upperMass.toReal * upperMean := by
    rw [← hdecomp, integral_add_measure hskillInt.restrict hskillInt.restrict,
      hLowerIntegral, hUpperIntegral]
  have hMass : lowerMass + upperMass = 1 := by
    have h := congrArg (fun law : Measure ℝ => law Set.univ) hdecomp
    simpa [Measure.add_apply, Measure.restrict_apply_univ,
      IsProbabilityMeasure.measure_univ] using h
  have hMassReal : lowerMass.toReal + upperMass.toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hMass]
    norm_num
  have hUpperMassRealPos : 0 < upperMass.toReal :=
    ENNReal.toReal_pos (ne_of_gt hupperPositive) (measure_ne_top _ _)
  have hGlobalMean : (∫ skill, skill ∂μ) = skillLaw.mean := by
    dsimp [μ, GaussianScaleLaw.toMeasure]
    exact integral_id_gaussianReal
  have hLowerParent : lowerMean < skillLaw.mean := by
    rw [← hGlobalMean, hGlobalIntegral]
    have hmixture :
        lowerMass.toReal * lowerMean + upperMass.toReal * upperMean =
          lowerMean + upperMass.toReal * (upperMean - lowerMean) := by
      calc
        lowerMass.toReal * lowerMean + upperMass.toReal * upperMean =
            (lowerMass.toReal + upperMass.toReal) * lowerMean +
              upperMass.toReal * (upperMean - lowerMean) := by
          ring
        _ = lowerMean + upperMass.toReal * (upperMean - lowerMean) := by
          rw [hMassReal]
          ring
    rw [hmixture]
    have hgap : 0 < upperMass.toReal * (upperMean - lowerMean) :=
      mul_pos hUpperMassRealPos (sub_pos.mpr hMeanOrder)
    linarith
  simpa [lg21GaussianLowerTailConditionalMean, μ, lower, lowerLaw, lowerMean]
    using hLowerParent

/-! ## Direct actual-PBO positive-mass consequence -/

/--
The report-required positive-mass PBO identity in the form a source model must
derive: a Bayesian-optimal no-take estimate is the conditional expectation of
skill over the actual no-take cohort.  This definition names the target
identity; it does not derive the cohort/action carrier from the paper.
-/
def LG21ReportRequiredActualNoTakePBOModel
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool)
    (noTakeEstimate : ℝ)
    (hmeasurable : MeasurableSet {skill | takeDecision skill = false})
    (hpositive : 0 < skillLaw.toMeasure {skill | takeDecision skill = false}) : Prop :=
  noTakeEstimate =
    lg21ReportRequiredActualNoTakePBO skillLaw takeDecision hmeasurable hpositive

/--
An a.e. Gaussian cutoff and the literal conditional-expectation PBO identity
give the source PBO equality required by the report-required Lemma 4.1 route,
but only when the no-take branch has positive mass.
-/
theorem lg21_report_required_actual_pbo_positive_branch
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool)
    (noTakeEstimate cutoff : ℝ)
    (hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        takeDecision skill = decide (cutoff ≤ skill))
    (hmeasurable : MeasurableSet {skill | takeDecision skill = false})
    (hpositive : 0 < skillLaw.toMeasure {skill | takeDecision skill = false})
    (hpbo : LG21ReportRequiredActualNoTakePBOModel
      skillLaw takeDecision noTakeEstimate hmeasurable hpositive) :
    noTakeEstimate < cutoff := by
  rw [hpbo, lg21_report_required_actual_no_take_pbo_eq_lower_tail
    skillLaw takeDecision cutoff hcutoff hmeasurable hpositive]
  have htailPositive : 0 < skillLaw.toMeasure (Set.Iio cutoff) := by
    rw [← measure_congr
      (lg21_report_required_no_take_event_ae_eq_lower_tail
        skillLaw takeDecision cutoff hcutoff)]
    exact hpositive
  exact lg21_gaussian_lower_tail_conditional_mean_lt_cutoff
    skillLaw cutoff htailPositive

/--
Under the actual conditional-expectation PBO semantics, an a.e. best-response
cutoff cannot leave a positive-mass no-take cohort.  Unlike the legacy route,
this theorem does not posit a lower-tail mean formula: both needed strict
inequalities are derived from the normalized Gaussian population law.
-/
theorem paper_lemma4_1_report_required_actual_pbo_no_positive_mass_no_take
    (skillLaw : GaussianScaleLaw) (takeDecision : ℝ → Bool)
    (weight noTakeEstimate : ℝ)
    (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE skillLaw.toMeasure
        (fun skill => takeDecision skill = true)
        (fun skill =>
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill)
        (fun _skill => noTakeEstimate))
    (hmeasurable : MeasurableSet {skill | takeDecision skill = false})
    (hpbo :
      ∀ hpositive : 0 < skillLaw.toMeasure {skill | takeDecision skill = false},
        LG21ReportRequiredActualNoTakePBOModel
          skillLaw takeDecision noTakeEstimate hmeasurable hpositive) :
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
  have hbestAffine :
      NoProfitableBinaryChoiceDeviationAE skillLaw.toMeasure
        (fun skill => takeDecision skill = true)
        (fun skill => intercept + weight * skill)
        (fun _skill => noTakeEstimate) := by
    simpa only [htakePayoff] using hbest
  have hcutoff :
      ∀ᵐ skill ∂skillLaw.toMeasure,
        takeDecision skill = decide (cutoff ≤ skill) :=
    lg21_gaussian_affine_best_response_ae_cutoff
      skillLaw takeDecision intercept weight noTakeEstimate hweight hbestAffine
  have htailPositive : 0 < skillLaw.toMeasure (Set.Iio cutoff) := by
    rw [← measure_congr
      (lg21_report_required_no_take_event_ae_eq_lower_tail
        skillLaw takeDecision cutoff hcutoff)]
    exact hpositive
  have hnoTake_lt_cutoff : noTakeEstimate < cutoff :=
    lg21_report_required_actual_pbo_positive_branch
      skillLaw takeDecision noTakeEstimate cutoff hcutoff hmeasurable hpositive
      (hpbo hpositive)
  have hnoTake_lt_mean : noTakeEstimate < skillLaw.mean := by
    rw [hpbo hpositive,
      lg21_report_required_actual_no_take_pbo_eq_lower_tail
        skillLaw takeDecision cutoff hcutoff hmeasurable hpositive]
    exact lg21_gaussian_lower_tail_conditional_mean_lt_parent_mean
      skillLaw cutoff htailPositive
  let indifferentScore :=
    lg21ObservedAccessIndifferentTestScore
      skillLaw.mean weight noTakeEstimate
  have hindifferent_lt_noTake : indifferentScore < noTakeEstimate := by
    exact lg21ObservedAccessIndifferentTestScore_lt_noTakeEstimate
      skillLaw.mean noTakeEstimate hweight hweight_lt_one hnoTake_lt_mean
  have hindifferent_eq_cutoff : indifferentScore = cutoff := by
    simp only [indifferentScore, cutoff,
      lg21ObservedAccessIndifferentTestScore, intercept]
  rw [hindifferent_eq_cutoff] at hindifferent_lt_noTake
  linarith

/--
Source-timed report-required form of the actual-PBO positive-mass theorem.
The taking payoff is the Definition 1 expected estimate, while the no-take
PBO is explicitly a conditional expectation on its positive-mass action
event.  No probability-of-a-better-result objective is used.
-/
theorem paper_lemma4_1_report_required_source_timed_actual_pbo_no_positive_mass_no_take
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (base : Base) (skillLaw : GaussianScaleLaw)
    (weight : ℝ) (hweight : 0 < weight) (hweight_lt_one : weight < 1)
    (htakeExpected :
      ∀ skill,
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base =
          lg21ObservedAccessReportedPosterior skillLaw.mean weight skill)
    (hnoTakeMeasurable :
      MeasurableSet {skill | E.takeDecision skill base = false})
    (hpbo :
      ∀ hpositive :
        0 < skillLaw.toMeasure {skill | E.takeDecision skill base = false},
        LG21ReportRequiredActualNoTakePBOModel
          skillLaw (E.takeDecision · base) (E.noReportPayoff base)
          hnoTakeMeasurable hpositive) :
    ¬ 0 < skillLaw.toMeasure {skill | E.takeDecision skill base = false} := by
  apply paper_lemma4_1_report_required_actual_pbo_no_positive_mass_no_take
    skillLaw (E.takeDecision · base) weight (E.noReportPayoff base)
    hweight hweight_lt_one
  · have hbest :=
      lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base
    have hbestAE :=
      noProfitableBinaryChoiceDeviationAE_of_pointwise
        (μ := skillLaw.toMeasure) hbest
    simpa only [htakeExpected] using hbestAE
  · intro hpositive
    exact hpbo hpositive

end

end LG21TestOptionalPolicies
