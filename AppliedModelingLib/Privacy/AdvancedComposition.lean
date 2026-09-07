import AppliedModelingLib.Foundations.Probability.FiniteAdaptiveMGF
import AppliedModelingLib.Privacy.KL

/-!
# Finite adaptive advanced composition for pure max-KL stability

This file proves the privacy-loss supermartingale form of advanced
composition for finite, history-dependent mechanisms.  The history is an
arbitrary finite transcript, so the theorem does not assume that rounds are
independent or chosen nonadaptively.
-/

namespace AppliedModelingLib.Privacy

noncomputable section

variable {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]

/-- The one-step log privacy loss of two finite outcome laws. -/
abbrev adaptivePrivacyLoss
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome) :=
  fun round history outcome =>
    logLikelihoodRatio (first round history) (second round history) outcome

/-- The advanced-composition budget obtained from the finite privacy-loss
supermartingale.  The leading `sqrt 2` is the standard DRV10 constant. -/
noncomputable def advancedPureMaxKLBudget
    (epsilon deltaPrime : ℝ) (rounds : ℕ) : ℝ :=
  epsilon * Real.sqrt (2 * (rounds : ℝ) * Real.log (1 / deltaPrime)) +
    (rounds : ℝ) * (2 * epsilon ^ 2)

/-- On a positive-probability atom, exponentiating the log privacy loss
recovers the exact likelihood ratio.  At a zero atom the inequality remains
valid. -/
theorem MaxKLClose.pointwise_le_exp_logLikelihoodRatio_mul
    {epsilon : ℝ} {first second : PMF Outcome}
    (h : MaxKLClose epsilon 0 first second) (outcome : Outcome) :
    (first outcome).toReal ≤
      Real.exp (logLikelihoodRatio first second outcome) * (second outcome).toReal := by
  by_cases hfirstZero : (first outcome).toReal = 0
  · rw [hfirstZero]
    exact mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  · have hfirstPos : 0 < (first outcome).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hfirstZero)
    have hsecondPos : 0 < (second outcome).toReal := by
      by_contra hsecondPos
      have hsecondZero : (second outcome).toReal = 0 :=
        le_antisymm (le_of_not_gt hsecondPos) ENNReal.toReal_nonneg
      have hforward := h.pointwise outcome
      rw [hsecondZero] at hforward
      simp only [mul_zero] at hforward
      exact (not_lt_of_ge hforward) hfirstPos
    unfold logLikelihoodRatio
    rw [Real.exp_sub, Real.exp_log hfirstPos, Real.exp_log hsecondPos]
    field_simp [hsecondPos.ne']
    norm_num

/-- The atom-mass comparison along a fully adaptive trace is controlled by
the sum of its one-step log privacy losses. -/
theorem finiteAdaptiveTraceLaw_pointwise_le_exp_scoreSum_mul
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon : ℝ)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    ∀ rounds (trace : Fin rounds → Outcome),
      (finiteAdaptiveTraceLaw first rounds trace).toReal ≤
        Real.exp (finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) *
          (finiteAdaptiveTraceLaw second rounds trace).toReal := by
  intro rounds
  induction rounds with
  | zero =>
      intro trace
      have htrace : trace = Fin.elim0 := Subsingleton.elim _ _
      subst trace
      simp [finiteAdaptiveTraceLaw, finiteAdaptiveScoreSum]
  | succ rounds ih =>
      intro trace
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveTraceLaw_snoc_apply_toReal,
            finiteAdaptiveTraceLaw_snoc_apply_toReal,
            finiteAdaptiveScoreSum_snoc]
          have hstep := MaxKLClose.pointwise_le_exp_logLikelihoodRatio_mul
            (hclose rounds history) outcome
          calc
            (finiteAdaptiveTraceLaw first rounds history).toReal *
                (first rounds history outcome).toReal ≤
                (Real.exp (finiteAdaptiveScoreSum (adaptivePrivacyLoss first second)
                  rounds history) *
                  (finiteAdaptiveTraceLaw second rounds history).toReal) *
                  (first rounds history outcome).toReal :=
              mul_le_mul_of_nonneg_right (ih history) ENNReal.toReal_nonneg
            _ ≤ (Real.exp (finiteAdaptiveScoreSum (adaptivePrivacyLoss first second)
                  rounds history) *
                  (finiteAdaptiveTraceLaw second rounds history).toReal) *
                  (Real.exp (logLikelihoodRatio (first rounds history)
                    (second rounds history) outcome) *
                    (second rounds history outcome).toReal) :=
              mul_le_mul_of_nonneg_left hstep
                (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)
            _ = Real.exp
                (finiteAdaptiveScoreSum (adaptivePrivacyLoss first second)
                  rounds history +
                  logLikelihoodRatio (first rounds history)
                    (second rounds history) outcome) *
                ((finiteAdaptiveTraceLaw second rounds history).toReal *
                  (second rounds history outcome).toReal) := by
              rw [Real.exp_add]
              ring

/-- Equal history-conditioned transitions generate equal adaptive trace laws. -/
theorem finiteAdaptiveTraceLaw_eq_of_forall_eq
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (htransition : ∀ round history, first round history = second round history) :
    ∀ rounds, finiteAdaptiveTraceLaw first rounds = finiteAdaptiveTraceLaw second rounds := by
  intro rounds
  induction rounds with
  | zero => rfl
  | succ rounds ih =>
      apply PMF.ext
      intro trace
      cases trace using Fin.snocCases with
      | snoc history outcome =>
          rw [finiteAdaptiveTraceLaw_snoc_apply, finiteAdaptiveTraceLaw_snoc_apply,
            ih, htransition]

/-- The finite privacy-loss sum has the adaptive Hoeffding tail implied by
pure max-KL stability.  The `2 * epsilon^2` drift is the BNS16 KL convention. -/
theorem pmfProb_adaptivePrivacyLoss_ge_drift_add_le_exp
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon step threshold : ℝ) (rounds : ℕ)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hstep : 0 ≤ step)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    pmfProb (finiteAdaptiveTraceLaw first rounds)
        (fun trace => (rounds : ℝ) * (2 * epsilon ^ 2) + threshold ≤
          finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) ≤
      Real.exp (-step * threshold +
        (rounds : ℝ) * (epsilon ^ 2 * step ^ 2 / 2)) := by
  apply pmfProb_finiteAdaptiveScoreSum_ge_drift_add_le_exp
    first (adaptivePrivacyLoss first second) (2 * epsilon ^ 2) epsilon step threshold rounds
    hepsilonNonneg hstep
  · intro round history
    have hkl := (hclose round history).toKLClose hepsilonNonneg hepsilonOne
    exact hkl.2
  · intro round history outcome
    exact (hclose round history).logLikelihoodRatio_abs_le hepsilonNonneg outcome

/-- Optimized adaptive privacy-loss tail. -/
theorem pmfProb_adaptivePrivacyLoss_ge_drift_add_le_hoeffding
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon threshold : ℝ) (rounds : ℕ)
    (hepsilonPos : 0 < epsilon) (hthreshold : 0 ≤ threshold)
    (hrounds : 0 < rounds) (hepsilonOne : epsilon ≤ 1)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    pmfProb (finiteAdaptiveTraceLaw first rounds)
        (fun trace => (rounds : ℝ) * (2 * epsilon ^ 2) + threshold ≤
          finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) ≤
      Real.exp (-threshold ^ 2 /
        (2 * (rounds : ℝ) * epsilon ^ 2)) := by
  apply pmfProb_finiteAdaptiveScoreSum_ge_drift_add_le_hoeffding
    first (adaptivePrivacyLoss first second) (2 * epsilon ^ 2) epsilon threshold rounds
    hepsilonPos hthreshold hrounds
  · intro round history
    have hkl := (hclose round history).toKLClose hepsilonPos.le hepsilonOne
    exact hkl.2
  · intro round history outcome
    exact (hclose round history).logLikelihoodRatio_abs_le hepsilonPos.le outcome

/-- At confidence `deltaPrime`, the privacy-loss threshold has the standard
`epsilon * sqrt (2 * rounds * log (1 / deltaPrime))` form. -/
theorem pmfProb_adaptivePrivacyLoss_ge_advancedPureMaxKLBudget_le
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon deltaPrime : ℝ) (rounds : ℕ)
    (hepsilonPos : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdeltaPos : 0 < deltaPrime) (hdeltaOne : deltaPrime ≤ 1)
    (hrounds : 0 < rounds)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    pmfProb (finiteAdaptiveTraceLaw first rounds)
        (fun trace => advancedPureMaxKLBudget epsilon deltaPrime rounds ≤
          finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) ≤
      deltaPrime := by
  let deviation := epsilon * Real.sqrt
    (2 * (rounds : ℝ) * Real.log (1 / deltaPrime))
  have hroundsReal : 0 < (rounds : ℝ) := by exact_mod_cast hrounds
  have hinverseAtLeastOne : 1 ≤ 1 / deltaPrime := by
    apply (le_div_iff₀ hdeltaPos).2
    nlinarith
  have hlogNonneg : 0 ≤ Real.log (1 / deltaPrime) :=
    Real.log_nonneg hinverseAtLeastOne
  have hradicandNonneg : 0 ≤ 2 * (rounds : ℝ) * Real.log (1 / deltaPrime) := by
    positivity
  have hdeviationNonneg : 0 ≤ deviation := by
    dsimp [deviation]
    positivity
  have htail := pmfProb_adaptivePrivacyLoss_ge_drift_add_le_hoeffding
    first second epsilon deviation rounds hepsilonPos hdeviationNonneg hrounds hepsilonOne hclose
  have hexponent : -deviation ^ 2 /
      (2 * (rounds : ℝ) * epsilon ^ 2) = -Real.log (1 / deltaPrime) := by
    dsimp [deviation]
    rw [mul_pow, Real.sq_sqrt hradicandNonneg]
    field_simp [hepsilonPos.ne']
  have htail' : pmfProb (finiteAdaptiveTraceLaw first rounds)
      (fun trace => advancedPureMaxKLBudget epsilon deltaPrime rounds ≤
        finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) ≤
      Real.exp (-deviation ^ 2 /
        (2 * (rounds : ℝ) * epsilon ^ 2)) := by
    simpa [advancedPureMaxKLBudget, deviation, add_comm] using htail
  calc
    pmfProb (finiteAdaptiveTraceLaw first rounds)
        (fun trace => advancedPureMaxKLBudget epsilon deltaPrime rounds ≤
          finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) ≤
        Real.exp (-deviation ^ 2 /
          (2 * (rounds : ℝ) * epsilon ^ 2)) := htail'
    _ = Real.exp (-Real.log (1 / deltaPrime)) := by rw [hexponent]
    _ = deltaPrime := by
      rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / deltaPrime)]
      field_simp [hdeltaPos.ne']

/-- One directed advanced-composition event inequality for a fully adaptive
finite transcript. -/
theorem finiteAdaptiveTraceLaw_advancedApproxDomination
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon deltaPrime : ℝ) (rounds : ℕ)
    (hepsilonPos : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdeltaPos : 0 < deltaPrime) (hdeltaOne : deltaPrime ≤ 1)
    (hrounds : 0 < rounds)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    ApproxDomination (advancedPureMaxKLBudget epsilon deltaPrime rounds) deltaPrime
      (finiteAdaptiveTraceLaw first rounds) (finiteAdaptiveTraceLaw second rounds) := by
  let bad : Finset (Fin rounds → Outcome) := Finset.univ.filter fun trace =>
    advancedPureMaxKLBudget epsilon deltaPrime rounds ≤
      finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace
  have hbadTail := pmfProb_adaptivePrivacyLoss_ge_advancedPureMaxKLBudget_le
    first second epsilon deltaPrime rounds hepsilonPos hepsilonOne hdeltaPos hdeltaOne
      hrounds hclose
  have hbad : eventProbability (finiteAdaptiveTraceLaw first rounds) bad ≤ deltaPrime := by
    simpa [eventProbability, bad] using hbadTail
  apply ApproxDomination.of_pointwise_outside_bad
    (finiteAdaptiveTraceLaw first rounds) (finiteAdaptiveTraceLaw second rounds) bad hbad
  intro trace houtside
  have hnotLarge : ¬ advancedPureMaxKLBudget epsilon deltaPrime rounds ≤
      finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace := by
    simpa [bad] using houtside
  have hscoreLt : finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace <
      advancedPureMaxKLBudget epsilon deltaPrime rounds := lt_of_not_ge hnotLarge
  calc
    (finiteAdaptiveTraceLaw first rounds trace).toReal ≤
        Real.exp (finiteAdaptiveScoreSum (adaptivePrivacyLoss first second) rounds trace) *
          (finiteAdaptiveTraceLaw second rounds trace).toReal :=
      finiteAdaptiveTraceLaw_pointwise_le_exp_scoreSum_mul first second epsilon hclose rounds trace
    _ ≤ Real.exp (advancedPureMaxKLBudget epsilon deltaPrime rounds) *
          (finiteAdaptiveTraceLaw second rounds trace).toReal :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hscoreLt.le) ENNReal.toReal_nonneg

/-- Standard finite adaptive advanced composition for pure two-sided max-KL
stability. -/
theorem finiteAdaptiveTraceLaw_advancedMaxKLClose
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon deltaPrime : ℝ) (rounds : ℕ)
    (hepsilonPos : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdeltaPos : 0 < deltaPrime) (hdeltaOne : deltaPrime ≤ 1)
    (hrounds : 0 < rounds)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    MaxKLClose (advancedPureMaxKLBudget epsilon deltaPrime rounds) deltaPrime
      (finiteAdaptiveTraceLaw first rounds) (finiteAdaptiveTraceLaw second rounds) := by
  constructor
  · exact finiteAdaptiveTraceLaw_advancedApproxDomination first second epsilon deltaPrime rounds
      hepsilonPos hepsilonOne hdeltaPos hdeltaOne hrounds hclose
  · exact finiteAdaptiveTraceLaw_advancedApproxDomination second first epsilon deltaPrime rounds
      hepsilonPos hepsilonOne hdeltaPos hdeltaOne hrounds
      (fun round history => (hclose round history).symm)

/-- The same advanced-composition conclusion, including the degenerate
zero-privacy and zero-round cases stated in the source theorem. -/
theorem finiteAdaptiveTraceLaw_advancedMaxKLClose_full
    (first second : ∀ round, (Fin round → Outcome) → PMF Outcome)
    (epsilon deltaPrime : ℝ) (rounds : ℕ)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdeltaPos : 0 < deltaPrime) (hdeltaOne : deltaPrime ≤ 1)
    (hclose : ∀ round history,
      MaxKLClose epsilon 0 (first round history) (second round history)) :
    MaxKLClose (advancedPureMaxKLBudget epsilon deltaPrime rounds) deltaPrime
      (finiteAdaptiveTraceLaw first rounds) (finiteAdaptiveTraceLaw second rounds) := by
  by_cases hroundsZero : rounds = 0
  · subst rounds
    simpa [advancedPureMaxKLBudget, finiteAdaptiveTraceLaw] using
      (MaxKLClose.refl (PMF.pure Fin.elim0 : PMF (Fin 0 → Outcome))
        (by norm_num) hdeltaPos.le)
  by_cases hepsilonZero : epsilon = 0
  · have htransition : ∀ round history, first round history = second round history := by
      intro round history
      apply PMF.ext
      intro outcome
      apply (ENNReal.toReal_eq_toReal_iff'
        ((first round history).apply_ne_top outcome)
        ((second round history).apply_ne_top outcome)).mp
      apply le_antisymm
      · simpa [hepsilonZero] using (hclose round history).pointwise outcome
      · simpa [hepsilonZero] using (hclose round history).symm.pointwise outcome
    have htrace := finiteAdaptiveTraceLaw_eq_of_forall_eq first second htransition rounds
    have hbudget : advancedPureMaxKLBudget epsilon deltaPrime rounds = 0 := by
      simp [advancedPureMaxKLBudget, hepsilonZero]
    rw [htrace, hbudget]
    exact MaxKLClose.refl _ (by norm_num) hdeltaPos.le
  · have hroundsPos : 0 < rounds := Nat.pos_of_ne_zero hroundsZero
    have hepsilonPos : 0 < epsilon :=
      lt_of_le_of_ne hepsilonNonneg (Ne.symm hepsilonZero)
    exact finiteAdaptiveTraceLaw_advancedMaxKLClose first second epsilon deltaPrime rounds
      hepsilonPos hepsilonOne hdeltaPos hdeltaOne hroundsPos hclose

end

end AppliedModelingLib.Privacy
