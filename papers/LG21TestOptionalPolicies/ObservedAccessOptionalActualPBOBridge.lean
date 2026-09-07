import LG21TestOptionalPolicies.ObservedAccessSourceConditionalKernel
import LG21TestOptionalPolicies.RawGaussianOptionalPositiveBranch

/-!
# Actual-PBO support for the all-taking observed-access reporting subgame

This file proves a deliberately narrow support result for the reporting stage
of LG21's optional protocol.  It does **not** formalize the full optional
action model: in that model the no-report pool can also contain people who did
not take the test.  Accordingly, every theorem below requires the supplied
carrier to be the access-pinned, all-taking subpopulation, and concerns only
the subsequent score/report decision.

The proof uses a literal normalized action-event law.  Its only strategic
input is an a.e. binary no-deviation certificate.  The equality identifying
the no-report estimate with the conditional skill mean is stated explicitly,
then transported through the kernel tower identity and an explicit
posterior-affine identity.  There is no supplied lower-tail PBO formula.

## Non-credit boundary

The source population has not yet been shown to instantiate the raw kernel
identities, the all-taking condition, the Gaussian conditional score law, or
the Definition-1 PBO interpretation used below.  The imported kernel model
now pins its population carrier to the raw `Z = 1` population, but this module
does not derive any of those fields from the literal LG21 source population.
It is therefore proof support only and must not be cited as paper-facing
credit for Lemma 4.1.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

namespace LG21ObservedAccessSourceConditionalKernel

variable {Ω Base : Type*} [MeasurableSpace Ω] [MeasurableSpace Base]

/--
The all-taking requirement for the restricted score-only reporting subgame.

The imported source-kernel model separately records that `M.populationLaw` is
the normalized raw `Z = 1` carrier.  This is only a supplied all-taking fact
about an auxiliary Boolean `take`; it does not yet identify that Boolean with
the source's pre-score action `Y`, impose its timing/measurability, or connect
the post-score report decision to the observed source action `X`.  A
source-facing bridge must prove those links before it can replace the full
`X = 0` pool by a score-selected no-report law.
-/
def OptionalReportingAllTakingCarrier
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (take : Ω → Bool) : Prop :=
  ∀ᵐ ω ∂M.populationLaw, take ω = true

/--
The candidate conditional-PBO identification needed for a positive-mass
no-report action.  The right side is the latent-skill mean in the normalized
action-selected cohort, not an off-path numerical completion.  This definition
does not claim that the supplied actions or carrier have yet been derived from
Definition 1.
-/
def OptionalReportingNoReportPBOInterpretation
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (reportDecision : Base → ℝ → Bool) (base : Base)
    (noReportEstimate : ℝ) : Prop :=
  noReportEstimate =
    ∫ skill, skill ∂M.noReportSkillLaw reportDecision base

/--
Transport a supplied action-selected PBO identification through the
conditional-kernel tower.

This is a restricted-subgame bridge.  The access/all-taking carrier,
measurability, and good-base hypotheses are deliberately explicit even though
the displayed integral algebra only needs the final three equalities.  They
are necessary ingredients for a future source bridge, but are not by
themselves evidence that the auxiliary actions equal the source's sequential
`Y`/`X` actions.
-/
theorem optionalReporting_actualAffinePBO_receipt
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (take : Ω → Bool)
    (reportDecision : Base → ℝ → Bool) (base : Base)
    (scoreLaw : GaussianScaleLaw) (intercept slope noReportEstimate : ℝ)
    (hallTake : OptionalReportingAllTakingCarrier M take)
    (hgoodBase : M.sourceGoodBase base)
    (hnoReportMeasurable :
      MeasurableSet {score | reportDecision base score = false})
    (hscoreLaw : M.scoreGivenBase base = scoreLaw.toMeasure)
    (hintegrable :
      Integrable (fun pair : ℝ × ℝ => pair.2)
        (M.noReportScoreSkillLaw reportDecision base))
    (hposteriorAffine :
      ∀ᵐ score ∂M.noReportScoreLaw reportDecision base,
        M.posteriorSkillMean base score = intercept + slope * score)
    (hnoReportPBO :
      OptionalReportingNoReportPBOInterpretation M reportDecision base
        noReportEstimate)
    (hpositive :
      0 < M.scoreGivenBase base {score | reportDecision base score = false}) :
    M.populationLaw =
        lg21NormalizedRestriction M.rawPopulationLaw {ω | M.access ω = true} ∧
      OptionalReportingAllTakingCarrier M take ∧
      M.sourceGoodBase base ∧
      MeasurableSet {score | reportDecision base score = false} ∧
      noReportEstimate =
        lg21OptionalPositiveNoReportPBO scoreLaw (reportDecision base)
          (fun score => intercept + slope * score)
          hnoReportMeasurable
          (by simpa [hscoreLaw] using hpositive) := by
  refine ⟨M.populationLaw_eq_access_conditioned, hallTake, hgoodBase,
    hnoReportMeasurable, ?_⟩
  rw [hnoReportPBO]
  rw [M.noReportSkillMean_eq_posterior_tower reportDecision base hintegrable]
  rw [MeasureTheory.integral_congr_ae hposteriorAffine]
  simp only [lg21OptionalPositiveNoReportPBO,
    noReportScoreLaw, hscoreLaw]

/--
In the all-taking, access-pinned score/reporting subgame, a positive-mass
no-report branch contradicts an a.e. best response when its PBO is the actual
normalized conditional skill mean and the score posterior is a positive-slope
affine function.

This theorem is intentionally *not* a full optional-protocol conclusion.  It
cannot be applied until the source carrier has excluded non-takers and all
fixed-base hypotheses have been derived from the raw population on an
almost-everywhere set of bases.
-/
theorem optionalReporting_scoreOnly_no_positive_mass_nonreport
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base)
    (take : Ω → Bool)
    (reportDecision : Base → ℝ → Bool) (base : Base)
    (scoreLaw : GaussianScaleLaw) (intercept slope noReportEstimate : ℝ)
    (hslope : 0 < slope)
    (hallTake : OptionalReportingAllTakingCarrier M take)
    (hgoodBase : M.sourceGoodBase base)
    (hnoReportMeasurable :
      MeasurableSet {score | reportDecision base score = false})
    (hscoreLaw : M.scoreGivenBase base = scoreLaw.toMeasure)
    (hintegrable :
      Integrable (fun pair : ℝ × ℝ => pair.2)
        (M.noReportScoreSkillLaw reportDecision base))
    (hposteriorAffine :
      ∀ᵐ score ∂M.noReportScoreLaw reportDecision base,
        M.posteriorSkillMean base score = intercept + slope * score)
    (hnoReportPBO :
      OptionalReportingNoReportPBOInterpretation M reportDecision base
        noReportEstimate)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE (M.scoreGivenBase base)
        (fun score => reportDecision base score = true)
        (fun score => intercept + slope * score)
        (fun _score => noReportEstimate)) :
    ¬ 0 < M.scoreGivenBase base {score | reportDecision base score = false} := by
  intro hpositive
  have hpositiveGaussian :
      0 < scoreLaw.toMeasure {score | reportDecision base score = false} := by
    simpa [hscoreLaw] using hpositive
  have hbestGaussian :
      NoProfitableBinaryChoiceDeviationAE scoreLaw.toMeasure
        (fun score => reportDecision base score = true)
        (fun score => intercept + slope * score)
        (fun _score => noReportEstimate) := by
    simpa [hscoreLaw] using hbest
  let cutoff := affineCutoff intercept slope noReportEstimate
  have hcutoff :
      ∀ᵐ score ∂scoreLaw.toMeasure,
        reportDecision base score = decide (cutoff ≤ score) := by
    exact lg21_gaussian_affine_best_response_ae_cutoff
      scoreLaw (reportDecision base) intercept slope noReportEstimate
      hslope hbestGaussian
  have hactualPBO :
      noReportEstimate =
        lg21OptionalPositiveNoReportPBO scoreLaw (reportDecision base)
          (fun score => intercept + slope * score) hnoReportMeasurable
          hpositiveGaussian := by
    have hreceipt := optionalReporting_actualAffinePBO_receipt
      M take reportDecision base scoreLaw intercept slope noReportEstimate
      hallTake hgoodBase hnoReportMeasurable hscoreLaw hintegrable
      hposteriorAffine hnoReportPBO hpositive
    exact hreceipt.2.2.2.2
  have hstrict :
      lg21OptionalPositiveNoReportPBO scoreLaw (reportDecision base)
          (fun score => intercept + slope * score) hnoReportMeasurable
          hpositiveGaussian <
        intercept + slope * cutoff := by
    exact lg21OptionalPositiveNoReportPBO_lt_affineAtCutoff_of_cutoff_ae
      scoreLaw (reportDecision base) intercept slope cutoff hslope
      hnoReportMeasurable hpositiveGaussian hcutoff
  have hcutoffValue : intercept + slope * cutoff = noReportEstimate := by
    dsimp [cutoff]
    unfold affineCutoff
    field_simp [ne_of_gt hslope]
    ring
  linarith

end LG21ObservedAccessSourceConditionalKernel

end

end LG21TestOptionalPolicies
