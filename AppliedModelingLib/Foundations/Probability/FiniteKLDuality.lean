import AppliedModelingLib.Foundations.Probability.FiniteKLConvex
import AppliedModelingLib.Foundations.Probability.FiniteMixture
import AppliedModelingLib.Foundations.Probability.ExponentialTilt
import AppliedModelingLib.Foundations.Optimization.EntropyRegularized

/-!
# Finite KL-ball duality helpers

This module collects the finite-simplex convexity facts that turn a strict KL
slack into a feasible improving mixture.  They are the elementary primal
ingredient in source-faithful constrained-to-regularized duality proofs.

## Main declarations

- `finiteKLDivergence_binaryMixturePMF_le`
- `exists_binaryMixtureWeight_of_strict_kl_slack`
- `finiteKL_constrainedUtilityMax_active_of_not_global`
- `finiteKL_constrainedUtilityMax_score_gt_reference_of_pos_radius`
- `exists_pos_exponentialTilt_pmfExp_eq_of_referenceMean_lt`
- `finiteKL_constrainedUtilityMax_is_regularized_of_pos_radius`
- `IsFiniteKLExtendedRegularizedUtilityMax`
- `finiteKL_constrainedUtilityMax_is_extended_regularized`
-/

namespace AppliedModelingLib

open scoped BigOperators

noncomputable section

/-- Finite KL divergence is convex under a binary PMF mixture in its first
argument.  The scalar is represented as an `NNReal` because this is the
probability parameter used by `binaryMixturePMF`. -/
theorem finiteKLDivergence_binaryMixturePMF_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (mixWeight : NNReal) (hmixWeight : mixWeight ≤ 1)
    (selected unselected reference : PMF Outcome) :
    finiteKLDivergence
      (binaryMixturePMF mixWeight hmixWeight selected unselected) reference ≤
        (mixWeight : ℝ) * finiteKLDivergence selected reference +
          (1 - (mixWeight : ℝ)) * finiteKLDivergence unselected reference := by
  let selectedMass : Outcome → ℝ := fun outcome => (selected outcome).toReal
  let unselectedMass : Outcome → ℝ := fun outcome => (unselected outcome).toReal
  have hselected_nonneg : ∀ outcome, 0 ≤ selectedMass outcome := by
    intro outcome
    exact ENNReal.toReal_nonneg
  have hunselected_nonneg : ∀ outcome, 0 ≤ unselectedMass outcome := by
    intro outcome
    exact ENNReal.toReal_nonneg
  have hmix_nonneg : 0 ≤ (mixWeight : ℝ) := by positivity
  have hcomplement_nonneg : 0 ≤ 1 - (mixWeight : ℝ) := by
    exact sub_nonneg.mpr (by exact_mod_cast hmixWeight)
  have hweights : (mixWeight : ℝ) + (1 - (mixWeight : ℝ)) = 1 := by ring
  have hconvex := finiteKLDivergenceMass_convexOn_nonneg reference
  have hbound := hconvex.2 hselected_nonneg hunselected_nonneg
    hmix_nonneg hcomplement_nonneg hweights
  have hmass :
      ((mixWeight : ℝ) • selectedMass + (1 - (mixWeight : ℝ)) • unselectedMass) =
        fun outcome =>
          (binaryMixturePMF mixWeight hmixWeight selected unselected outcome).toReal := by
    funext outcome
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, selectedMass, unselectedMass,
      binaryMixturePMF_apply_toReal]
  rw [hmass] at hbound
  simpa only [finiteKLDivergenceMass_pmf] using hbound

/--
If a policy has strict KL slack, then mixing it with any other finite policy
by a sufficiently small positive probability remains in the same KL ball.
The explicit weight avoids an unproved continuity or optimizer certificate.
-/
theorem exists_binaryMixtureWeight_of_strict_kl_slack
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate better : PMF Outcome) {radius : ℝ}
    (hslack : finiteKLDivergence candidate reference < radius) :
    ∃ mixWeight : NNReal, ∃ hmixWeight : mixWeight ≤ 1, 0 < mixWeight ∧
      finiteKLDivergence
        (binaryMixturePMF mixWeight hmixWeight better candidate) reference ≤ radius := by
  let candidateKL : ℝ := finiteKLDivergence candidate reference
  let betterKL : ℝ := finiteKLDivergence better reference
  let slack : ℝ := radius - candidateKL
  let scale : ℝ := |betterKL - candidateKL| + 1
  let weight : ℝ := min ((1 : ℝ) / 2) (slack / (2 * scale))
  have hslack_pos : 0 < slack := by
    dsimp [slack, candidateKL]
    linarith
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    positivity
  have hquot_pos : 0 < slack / (2 * scale) := by positivity
  have hhalf_pos : 0 < (1 : ℝ) / 2 := by norm_num
  have hweight_pos : 0 < weight := by
    dsimp [weight]
    exact lt_min hhalf_pos hquot_pos
  have hweight_nonneg : 0 ≤ weight := hweight_pos.le
  have hweight_le_half : weight ≤ (1 : ℝ) / 2 := by
    exact min_le_left _ _
  have hweight_le_quot : weight ≤ slack / (2 * scale) := by
    exact min_le_right _ _
  have hweight_le_one : weight ≤ 1 := by linarith
  let mixWeight : NNReal := ⟨weight, hweight_nonneg⟩
  have hmixWeight_pos : 0 < mixWeight := by
    change 0 < weight
    exact hweight_pos
  have hmixWeight_le_one : mixWeight ≤ 1 := by
    change weight ≤ 1
    exact hweight_le_one
  have hweight_scale : weight * scale ≤ slack / 2 := by
    have htwo_scale_pos : 0 < 2 * scale := by positivity
    calc
      weight * scale ≤ (slack / (2 * scale)) * scale :=
        mul_le_mul_of_nonneg_right hweight_le_quot hscale_pos.le
      _ = slack / 2 := by
        field_simp [ne_of_gt hscale_pos]
  have hdelta_le_abs : betterKL - candidateKL ≤ |betterKL - candidateKL| :=
    le_abs_self _
  have habs_le_scale : |betterKL - candidateKL| ≤ scale := by
    dsimp [scale]
    linarith [abs_nonneg (betterKL - candidateKL)]
  have hweight_delta_le : weight * (betterKL - candidateKL) ≤ slack / 2 := by
    calc
      weight * (betterKL - candidateKL) ≤ weight * |betterKL - candidateKL| :=
        mul_le_mul_of_nonneg_left hdelta_le_abs hweight_nonneg
      _ ≤ weight * scale :=
        mul_le_mul_of_nonneg_left habs_le_scale hweight_nonneg
      _ ≤ slack / 2 := hweight_scale
  have hconvex := finiteKLDivergence_binaryMixturePMF_le
    mixWeight hmixWeight_le_one better candidate reference
  have havg_lt_radius :
      (mixWeight : ℝ) * betterKL + (1 - (mixWeight : ℝ)) * candidateKL < radius := by
    change weight * betterKL + (1 - weight) * candidateKL < radius
    dsimp [slack] at hweight_delta_le
    nlinarith
  refine ⟨mixWeight, hmixWeight_le_one, hmixWeight_pos, ?_⟩
  have hconvex' :
      finiteKLDivergence
        (binaryMixturePMF mixWeight hmixWeight_le_one better candidate) reference ≤
        (mixWeight : ℝ) * betterKL +
          (1 - (mixWeight : ℝ)) * candidateKL := by
    simpa only [candidateKL, betterKL] using hconvex
  exact hconvex'.trans havg_lt_radius.le

/--
A constrained expected-utility maximizer that is not already a global
expected-utility maximizer must use its entire finite KL budget.  Otherwise a
sufficiently small mixture with a strictly better policy remains feasible and
improves the objective.
-/
theorem finiteKL_constrainedUtilityMax_active_of_not_global
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ) (radius : ℝ)
    (hcandidate : finiteKLDivergence candidate reference ≤ radius)
    (hmax : ∀ other : PMF Outcome,
      finiteKLDivergence other reference ≤ radius →
        pmfExp other utility ≤ pmfExp candidate utility)
    (hbetter : ∃ better : PMF Outcome,
      pmfExp candidate utility < pmfExp better utility) :
    finiteKLDivergence candidate reference = radius := by
  apply le_antisymm hcandidate
  by_contra hnot
  have hslack : finiteKLDivergence candidate reference < radius :=
    lt_of_not_ge hnot
  obtain ⟨better, hbetter_score⟩ := hbetter
  obtain ⟨mixWeight, hmixWeight_le_one, hmixWeight_pos, hmix_feasible⟩ :=
    exists_binaryMixtureWeight_of_strict_kl_slack reference candidate better hslack
  have hmax_mix := hmax
    (binaryMixturePMF mixWeight hmixWeight_le_one better candidate) hmix_feasible
  rw [pmfExp_binaryMixturePMF] at hmax_mix
  have hmixWeight_pos_real : 0 < (mixWeight : ℝ) := by exact_mod_cast hmixWeight_pos
  have himprove :
      pmfExp candidate utility <
        (mixWeight : ℝ) * pmfExp better utility +
          (1 - (mixWeight : ℝ)) * pmfExp candidate utility := by
    have hdelta_pos :
        0 < (mixWeight : ℝ) *
          (pmfExp better utility - pmfExp candidate utility) :=
      mul_pos hmixWeight_pos_real (sub_pos.mpr hbetter_score)
    nlinarith
  exact (not_lt_of_ge hmax_mix) himprove

/--
At a positive finite KL radius, a constrained utility maximizer that is not
globally utility-optimal has strictly larger utility than the reference PMF.
The proof treats the reference policy itself as a strict-slack feasible point.
-/
theorem finiteKL_constrainedUtilityMax_score_gt_reference_of_pos_radius
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ) {radius : ℝ}
    (hradius : 0 < radius)
    (hmax : ∀ other : PMF Outcome,
      finiteKLDivergence other reference ≤ radius →
        pmfExp other utility ≤ pmfExp candidate utility)
    (hbetter : ∃ better : PMF Outcome,
      pmfExp candidate utility < pmfExp better utility) :
    pmfExp reference utility < pmfExp candidate utility := by
  have href_feasible : finiteKLDivergence reference reference ≤ radius := by
    rw [finiteKLDivergence_self]
    exact hradius.le
  have href_le := hmax reference href_feasible
  apply lt_of_le_of_ne href_le
  intro heq
  obtain ⟨better, hbetter_score⟩ := hbetter
  obtain ⟨mixWeight, hmixWeight_le_one, hmixWeight_pos, hmix_feasible⟩ :=
    exists_binaryMixtureWeight_of_strict_kl_slack reference reference better (by
      rw [finiteKLDivergence_self]
      exact hradius)
  have hmax_mix := hmax
    (binaryMixturePMF mixWeight hmixWeight_le_one better reference) hmix_feasible
  rw [pmfExp_binaryMixturePMF] at hmax_mix
  have hmixWeight_pos_real : 0 < (mixWeight : ℝ) := by exact_mod_cast hmixWeight_pos
  have hbetter_reference : pmfExp reference utility < pmfExp better utility := by
    rw [heq]
    exact hbetter_score
  have himprove :
      pmfExp candidate utility <
        (mixWeight : ℝ) * pmfExp better utility +
          (1 - (mixWeight : ℝ)) * pmfExp reference utility := by
    rw [← heq]
    have hdelta_pos :
        0 < (mixWeight : ℝ) *
          (pmfExp better utility - pmfExp reference utility) :=
      mul_pos hmixWeight_pos_real (sub_pos.mpr hbetter_reference)
    nlinarith
  exact (not_lt_of_ge hmax_mix) himprove

/--
Every target utility strictly between a full-support reference policy's mean
and an available larger atom is attained by a positive exponential tilt.  The
proof solves the shifted finite log-MGF stationarity equation directly, so no
unproved multiplier or inverse-gradient certificate is introduced.
-/
theorem exists_pos_exponentialTilt_pmfExp_eq_of_referenceMean_lt
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (target : ℝ)
    (hreference : PMFFullSupport reference)
    (hmean : pmfExp reference utility < target)
    (hhigh : ∃ outcome : Outcome, target < utility outcome) :
    ∃ inverseTemperature : ℝ, 0 < inverseTemperature ∧
      pmfExp (exponentialTilt reference utility inverseTemperature) utility = target := by
  have hlow : ∃ outcome : Outcome, utility outcome < target := by
    by_contra hnone
    push Not at hnone
    have hneg_bound : pmfExp reference (fun outcome => -utility outcome) ≤ -target :=
      pmfExp_le_of_forall_le reference (fun outcome => -utility outcome) (-target)
        (fun outcome => neg_le_neg (hnone outcome))
    rw [pmfExp_neg] at hneg_bound
    linarith
  obtain ⟨low, hlow_score⟩ := hlow
  obtain ⟨high, hhigh_score⟩ := hhigh
  have hshift_mean : 0 ≤ pmfExp reference (fun outcome => target - utility outcome) := by
    rw [pmfExp_sub, pmfExp_const]
    linarith
  obtain ⟨dual, hdual_nonpos, hstationary⟩ :=
    Probability.exists_nonpos_weighted_exp_score_sum_eq_zero_of_pmfExp_nonneg_pos_neg_atoms
      reference (fun outcome => target - utility outcome) hshift_mean
      (aPos := low) (aNeg := high)
      (hreference low) (sub_pos.mpr hlow_score)
      (hreference high) (sub_neg.mpr hhigh_score)
  have hdual_ne_zero : dual ≠ 0 := by
    intro hzero
    subst dual
    have hshift_zero : pmfExp reference (fun outcome => target - utility outcome) = 0 := by
      simpa [pmfExp] using hstationary
    rw [pmfExp_sub, pmfExp_const] at hshift_zero
    linarith
  have hdual_neg : dual < 0 := lt_of_le_of_ne hdual_nonpos hdual_ne_zero
  let inverseTemperature : ℝ := -dual
  have hinverseTemperature : 0 < inverseTemperature := by
    dsimp [inverseTemperature]
    exact neg_pos.mpr hdual_neg
  have hexp_factor : ∀ outcome : Outcome,
      Real.exp (dual * (target - utility outcome)) =
        Real.exp (dual * target) *
          Real.exp (inverseTemperature * utility outcome) := by
    intro outcome
    rw [show dual * (target - utility outcome) =
      dual * target + inverseTemperature * utility outcome by
        dsimp [inverseTemperature]
        ring, Real.exp_add]
  have hfactor :
      (∑ outcome : Outcome,
        (reference outcome).toReal *
          ((target - utility outcome) * Real.exp (dual * (target - utility outcome)))) =
        Real.exp (dual * target) *
          (∑ outcome : Outcome,
            (reference outcome).toReal *
              ((target - utility outcome) *
                Real.exp (inverseTemperature * utility outcome))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun outcome _ => ?_
    rw [hexp_factor]
    ring
  have hshift_weighted_zero :
      (∑ outcome : Outcome,
        (reference outcome).toReal *
          ((target - utility outcome) *
            Real.exp (inverseTemperature * utility outcome))) = 0 := by
    have hproduct_zero :
        Real.exp (dual * target) *
          (∑ outcome : Outcome,
            (reference outcome).toReal *
              ((target - utility outcome) *
                Real.exp (inverseTemperature * utility outcome))) = 0 := by
      rw [← hfactor]
      exact hstationary
    exact (mul_eq_zero.mp hproduct_zero).resolve_left (Real.exp_ne_zero _)
  have hweighted_expand :
      (∑ outcome : Outcome,
        (reference outcome).toReal *
          ((target - utility outcome) *
            Real.exp (inverseTemperature * utility outcome))) =
        target * Probability.finiteMGF reference utility inverseTemperature -
          ∑ outcome : Outcome,
            (reference outcome).toReal *
              (utility outcome * Real.exp (inverseTemperature * utility outcome)) := by
    unfold Probability.finiteMGF
    calc
      ∑ outcome : Outcome,
          (reference outcome).toReal *
            ((target - utility outcome) *
              Real.exp (inverseTemperature * utility outcome)) =
          ∑ outcome : Outcome,
            (target * ((reference outcome).toReal *
              Real.exp (inverseTemperature * utility outcome)) -
              (reference outcome).toReal *
                (utility outcome * Real.exp (inverseTemperature * utility outcome))) := by
              refine Finset.sum_congr rfl fun outcome _ => ?_
              ring
      _ =
          ∑ outcome : Outcome,
            target * ((reference outcome).toReal *
              Real.exp (inverseTemperature * utility outcome)) -
          ∑ outcome : Outcome,
            (reference outcome).toReal *
              (utility outcome * Real.exp (inverseTemperature * utility outcome)) := by
              rw [Finset.sum_sub_distrib]
      _ =
          target * ∑ outcome : Outcome,
            (reference outcome).toReal *
              Real.exp (inverseTemperature * utility outcome) -
          ∑ outcome : Outcome,
            (reference outcome).toReal *
              (utility outcome * Real.exp (inverseTemperature * utility outcome)) := by
              rw [Finset.mul_sum]
  have hnumerator :
      (∑ outcome : Outcome,
        (reference outcome).toReal *
          (utility outcome * Real.exp (inverseTemperature * utility outcome))) =
        target * Probability.finiteMGF reference utility inverseTemperature := by
    rw [hweighted_expand] at hshift_weighted_zero
    linarith
  refine ⟨inverseTemperature, hinverseTemperature, ?_⟩
  rw [pmfExp_exponentialTilt, hnumerator]
  field_simp [(Probability.finiteMGF_pos reference utility inverseTemperature).ne']

/--
For a strictly positive finite KL radius, every constrained expected-utility
maximizer is also a maximizer of an ordinary finite KL-regularized objective
for some nonnegative penalty.  The proof is finite and explicit: a
non-global constrained optimum is active, its score is matched by a positive
Gibbs tilt, and the two active optimizers coincide by the KL three-point
identity.  The zero-radius `λ = ∞` boundary is intentionally separate.
-/
theorem finiteKL_constrainedUtilityMax_is_regularized_of_pos_radius
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ) {radius : ℝ}
    (hreference : PMFFullSupport reference) (hradius : 0 < radius)
    (hcandidate : finiteKLDivergence candidate reference ≤ radius)
    (hmax : ∀ other : PMF Outcome,
      finiteKLDivergence other reference ≤ radius →
        pmfExp other utility ≤ pmfExp candidate utility) :
    ∃ klWeight : ℝ, 0 ≤ klWeight ∧ ∀ other : PMF Outcome,
      pmfExp other utility - klWeight * finiteKLDivergence other reference ≤
        pmfExp candidate utility - klWeight * finiteKLDivergence candidate reference := by
  by_cases hglobal : ∀ other : PMF Outcome,
      pmfExp other utility ≤ pmfExp candidate utility
  · refine ⟨0, le_rfl, ?_⟩
    intro other
    simpa using hglobal other
  push Not at hglobal
  obtain ⟨better, hbetter⟩ := hglobal
  have hactive : finiteKLDivergence candidate reference = radius :=
    finiteKL_constrainedUtilityMax_active_of_not_global
      reference candidate utility radius hcandidate hmax ⟨better, hbetter⟩
  have hmean_lt : pmfExp reference utility < pmfExp candidate utility :=
    finiteKL_constrainedUtilityMax_score_gt_reference_of_pos_radius
      reference candidate utility hradius hmax ⟨better, hbetter⟩
  have hhigh : ∃ outcome : Outcome, pmfExp candidate utility < utility outcome := by
    by_contra hnone
    push Not at hnone
    have hbetter_le : pmfExp better utility ≤ pmfExp candidate utility :=
      pmfExp_le_of_forall_le better utility (pmfExp candidate utility) hnone
    exact (not_lt_of_ge hbetter_le) hbetter
  obtain ⟨inverseTemperature, hinverseTemperature, htilt_score⟩ :=
    exists_pos_exponentialTilt_pmfExp_eq_of_referenceMean_lt
      reference utility (pmfExp candidate utility) hreference hmean_lt hhigh
  let tilt : PMF Outcome := exponentialTilt reference utility inverseTemperature
  have htilt_score' : pmfExp tilt utility = pmfExp candidate utility := by
    dsimp [tilt]
    exact htilt_score
  have hthree := finiteKLDivergence_exponentialTilt_three_point
    reference candidate utility inverseTemperature hreference
  have hcandidate_to_tilt_nonneg : 0 ≤ finiteKLDivergence candidate tilt := by
    dsimp [tilt]
    exact finiteKLDivergence_nonneg candidate
      (exponentialTilt reference utility inverseTemperature)
      (exponentialTilt_fullSupport reference utility inverseTemperature hreference)
  have htilt_kl_le : finiteKLDivergence tilt reference ≤
      finiteKLDivergence candidate reference := by
    dsimp [tilt] at hcandidate_to_tilt_nonneg ⊢
    rw [htilt_score] at hthree
    nlinarith
  have htilt_feasible : finiteKLDivergence tilt reference ≤ radius :=
    htilt_kl_le.trans_eq hactive
  have htilt_max : ∀ other : PMF Outcome,
      finiteKLDivergence other reference ≤ radius →
        pmfExp other utility ≤ pmfExp tilt utility := by
    intro other hother
    rw [htilt_score']
    exact hmax other hother
  have htilt_better : ∃ better : PMF Outcome,
      pmfExp tilt utility < pmfExp better utility := by
    refine ⟨better, ?_⟩
    rw [htilt_score']
    exact hbetter
  have htilt_active : finiteKLDivergence tilt reference = radius :=
    finiteKL_constrainedUtilityMax_active_of_not_global
      reference tilt utility radius htilt_feasible htilt_max htilt_better
  have hcandidate_tilt_kl_zero : finiteKLDivergence candidate tilt = 0 := by
    dsimp [tilt] at hthree ⊢
    rw [htilt_score, hactive, htilt_active] at hthree
    nlinarith
  have hcandidate_eq_tilt : candidate = tilt := by
    apply (finiteKLDivergence_eq_zero_iff candidate tilt ?_).mp
    · exact hcandidate_tilt_kl_zero
    · dsimp [tilt]
      exact exponentialTilt_fullSupport reference utility inverseTemperature hreference
  subst candidate
  refine ⟨inverseTemperature⁻¹, (inv_nonneg.mpr hinverseTemperature.le), ?_⟩
  intro other
  exact exponentialTilt_regularizedUtility_globalMax
    reference utility inverseTemperature hreference hinverseTemperature other

/--
Finite extended-weight interpretation of KL-regularized utility maximization.
At a finite nonnegative weight this is the ordinary regularized objective.  At
the source's `λ = ∞` boundary it means exactly the reference PMF, which is the
singleton zero-radius KL ball under full support.
-/
def IsFiniteKLExtendedRegularizedUtilityMax
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (klWeight : WithTop ℝ) : Prop :=
  (∃ finiteWeight : ℝ, klWeight = (finiteWeight : WithTop ℝ) ∧ 0 ≤ finiteWeight ∧
    ∀ other : PMF Outcome,
      pmfExp other utility - finiteWeight * finiteKLDivergence other reference ≤
        pmfExp candidate utility - finiteWeight * finiteKLDivergence candidate reference) ∨
  (klWeight = ⊤ ∧ candidate = reference)

/--
An extended KL-regularized utility maximizer is optimal in the constrained
problem at the KL radius it attains.  The finite-weight branch is the usual
penalty comparison.  In the infinite-weight branch the candidate is the
reference policy, and full support makes the attained zero-radius KL ball a
singleton.
-/
theorem finiteKL_extendedRegularizedUtilityMax_is_constrainedAt_attainedKL
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ)
    (klWeight : WithTop ℝ) (hreference : PMFFullSupport reference)
    (hregularized :
      IsFiniteKLExtendedRegularizedUtilityMax reference candidate utility klWeight) :
    finiteKLDivergence candidate reference ≤
        finiteKLDivergence candidate reference ∧
      ∀ other : PMF Outcome,
        finiteKLDivergence other reference ≤
            finiteKLDivergence candidate reference →
          pmfExp other utility ≤ pmfExp candidate utility := by
  constructor
  · exact le_rfl
  · intro other hother
    rcases hregularized with
      ⟨finiteWeight, _hweight, hfiniteWeight_nonneg, hmax⟩ |
        ⟨_hweight_top, hcandidate_reference⟩
    · have hregularized_other := hmax other
      have hpenalty := mul_le_mul_of_nonneg_left hother hfiniteWeight_nonneg
      linarith
    · subst candidate
      have hother_zero : finiteKLDivergence other reference ≤ 0 := by
        simpa using hother
      have hother_reference :=
        (finiteKLDivergence_le_zero_iff_eq other reference hreference).mp hother_zero
      subst other
      exact le_rfl

/--
Full finite constrained-to-regularized correspondence for expected utility.
Positive KL radii are handled by the explicit finite Gibbs-duality theorem;
the zero-radius branch uses the source's extended `λ = ∞` convention and the
fact that a full-support reference has a singleton zero KL ball.
-/
theorem finiteKL_constrainedUtilityMax_is_extended_regularized
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference candidate : PMF Outcome) (utility : Outcome → ℝ) (radius : ℝ)
    (hreference : PMFFullSupport reference)
    (hcandidate : finiteKLDivergence candidate reference ≤ radius)
    (hmax : ∀ other : PMF Outcome,
      finiteKLDivergence other reference ≤ radius →
        pmfExp other utility ≤ pmfExp candidate utility) :
    ∃ klWeight : WithTop ℝ,
      IsFiniteKLExtendedRegularizedUtilityMax reference candidate utility klWeight := by
  have hradius_nonneg : 0 ≤ radius :=
    (finiteKLDivergence_nonneg candidate reference hreference).trans hcandidate
  rcases eq_or_lt_of_le hradius_nonneg with hradius_zero | hradius_pos
  · subst radius
    have hcandidate_eq_reference : candidate = reference :=
      (finiteKLDivergence_le_zero_iff_eq candidate reference hreference).mp hcandidate
    exact ⟨⊤, Or.inr ⟨rfl, hcandidate_eq_reference⟩⟩
  · obtain ⟨finiteWeight, hfiniteWeight_nonneg, hfinite⟩ :=
      finiteKL_constrainedUtilityMax_is_regularized_of_pos_radius
        reference candidate utility hreference hradius_pos hcandidate hmax
    exact ⟨(finiteWeight : WithTop ℝ),
      Or.inl ⟨finiteWeight, rfl, hfiniteWeight_nonneg, hfinite⟩⟩

end

end AppliedModelingLib
