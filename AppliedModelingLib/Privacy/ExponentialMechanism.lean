import AppliedModelingLib.Privacy.Finite
import AppliedModelingLib.Foundations.Probability.ExponentialTilt
import AppliedModelingLib.Foundations.Optimization.EntropyRegularized

/-!
# Finite exponential-mechanism privacy

This module proves the finite-domain privacy guarantee for sampling from a
Gibbs distribution whose score has bounded one-dataset variation.  It is the
common mechanism underlying finite private optimization and the exponential
selection monitor in adaptive-data-analysis arguments.
-/

open scoped BigOperators

namespace AppliedModelingLib

open Probability

/-! ## Finite utility -/

/-- Sampling a finite candidate from probability proportional to
`exp (eta * score)` loses at most `log |F| / eta` in expected score. -/
theorem exponentialTilt_expectedScore_ge_score_sub_log_card_div
    {Candidate : Type*} [Fintype Candidate] [DecidableEq Candidate] [Nonempty Candidate]
    (score : Candidate → ℝ) (eta : ℝ) (heta : 0 < eta) :
    ∀ candidate, score candidate - Real.log (Fintype.card Candidate : ℝ) / eta ≤
      pmfExp (exponentialTilt (uniformPMF Candidate) score eta) score := by
  have hreference : PMFFullSupport (uniformPMF Candidate) := by
    intro candidate
    rw [uniformPMF_apply_toReal]
    positivity
  intro candidate
  have hobjective := exponentialTiltObjective_le_at_exponentialTilt
    (uniformPMF Candidate) (PMF.pure candidate) score eta hreference
  have hpureKL := finiteKLDivergence_uniform_le_log_card (PMF.pure candidate)
  have htiltKL := finiteKLDivergence_nonneg
    (exponentialTilt (uniformPMF Candidate) score eta) (uniformPMF Candidate)
    hreference
  have hmain : eta * score candidate - Real.log (Fintype.card Candidate : ℝ) ≤
      eta * pmfExp (exponentialTilt (uniformPMF Candidate) score eta) score := by
    unfold exponentialTiltObjective at hobjective
    rw [pmfExp_pure] at hobjective
    nlinarith
  rw [show score candidate - Real.log (Fintype.card Candidate : ℝ) / eta =
      (eta * score candidate - Real.log (Fintype.card Candidate : ℝ)) / eta by
        field_simp [heta.ne']]
  apply (div_le_iff₀ heta).2
  nlinarith [hmain]

/-! ## Partition-function comparison -/

/-- Raising every score by at most `offset` raises its finite exponential
partition function by at most the corresponding exponential factor. -/
theorem finiteMGF_le_exp_mul_of_forall_le
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (first second : Outcome → ℝ)
    (inverseTemperature offset : ℝ)
    (hinverseTemperature : 0 ≤ inverseTemperature)
    (hscore : ∀ outcome, first outcome ≤ second outcome + offset) :
    finiteMGF reference first inverseTemperature ≤
      Real.exp (inverseTemperature * offset) *
        finiteMGF reference second inverseTemperature := by
  unfold finiteMGF
  calc
    ∑ outcome : Outcome,
        (reference outcome).toReal * Real.exp (inverseTemperature * first outcome) ≤
      ∑ outcome : Outcome,
        (reference outcome).toReal *
          Real.exp (inverseTemperature * (second outcome + offset)) := by
        apply Finset.sum_le_sum
        intro outcome _
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (hscore outcome) hinverseTemperature))
          ENNReal.toReal_nonneg
    _ = Real.exp (inverseTemperature * offset) *
        ∑ outcome : Outcome,
          (reference outcome).toReal * Real.exp (inverseTemperature * second outcome) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro outcome _
        rw [show inverseTemperature * (second outcome + offset) =
          inverseTemperature * second outcome + inverseTemperature * offset by ring,
          Real.exp_add]
        ring

/-! ## Pure max-KL guarantee -/

namespace Privacy

/-- A finite exponential mechanism is pure max-KL stable when its score moves
by at most `sensitivity` in either direction and `2 * eta * sensitivity` fits
the supplied privacy budget. -/
theorem exponentialTilt_maxKLClose_of_score_sensitivity
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (firstScore secondScore : Outcome → ℝ)
    (eta sensitivity epsilon : ℝ)
    (hreference : PMFFullSupport reference)
    (heta : 0 ≤ eta)
    (hfirstSecond : ∀ outcome,
      |firstScore outcome - secondScore outcome| ≤ sensitivity)
    (hbudget : 2 * eta * sensitivity ≤ epsilon) :
    MaxKLClose epsilon 0
      (exponentialTilt reference firstScore eta)
      (exponentialTilt reference secondScore eta) := by
  have hfirstUpper : ∀ outcome, firstScore outcome ≤ secondScore outcome + sensitivity := by
    intro outcome
    have h := (abs_le.mp (hfirstSecond outcome)).2
    linarith
  have hsecondUpper : ∀ outcome, secondScore outcome ≤ firstScore outcome + sensitivity := by
    intro outcome
    have h := (abs_le.mp (hfirstSecond outcome)).1
    linarith
  have hpartitionFirst :
      finiteMGF reference firstScore eta ≤
        Real.exp (eta * sensitivity) * finiteMGF reference secondScore eta :=
    finiteMGF_le_exp_mul_of_forall_le reference firstScore secondScore eta sensitivity
      heta hfirstUpper
  have hpartitionSecond :
      finiteMGF reference secondScore eta ≤
        Real.exp (eta * sensitivity) * finiteMGF reference firstScore eta :=
    finiteMGF_le_exp_mul_of_forall_le reference secondScore firstScore eta sensitivity
      heta hsecondUpper
  have hbudgetExp : Real.exp (2 * eta * sensitivity) ≤ Real.exp epsilon :=
    Real.exp_le_exp.mpr hbudget
  constructor <;>
    apply ApproxDomination.of_pointwise_outside_bad _ _ ∅
  · simp [eventProbability]
  · intro outcome houtside
    rw [exponentialTilt_apply_toReal, exponentialTilt_apply_toReal]
    have hnum :
        Real.exp (eta * firstScore outcome) ≤
          Real.exp (eta * sensitivity) * Real.exp (eta * secondScore outcome) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hdiff := hfirstUpper outcome
      nlinarith
    have hden :
        finiteMGF reference secondScore eta ≤
          Real.exp (eta * sensitivity) * finiteMGF reference firstScore eta :=
      hpartitionSecond
    have hrefPos : 0 < (reference outcome).toReal := hreference outcome
    have hfirstPos : 0 < finiteMGF reference firstScore eta :=
      finiteMGF_pos reference firstScore eta
    have hsecondPos : 0 < finiteMGF reference secondScore eta :=
      finiteMGF_pos reference secondScore eta
    calc
      (reference outcome).toReal * Real.exp (eta * firstScore outcome) /
          finiteMGF reference firstScore eta ≤
        (reference outcome).toReal *
          (Real.exp (eta * sensitivity) * Real.exp (eta * secondScore outcome)) /
          finiteMGF reference firstScore eta := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnum ENNReal.toReal_nonneg) hfirstPos.le
      _ ≤ Real.exp (2 * eta * sensitivity) *
          ((reference outcome).toReal * Real.exp (eta * secondScore outcome) /
            finiteMGF reference secondScore eta) := by
          apply (div_le_iff₀ hfirstPos).2
          rw [show Real.exp (2 * eta * sensitivity) *
              ((reference outcome).toReal * Real.exp (eta * secondScore outcome) /
                finiteMGF reference secondScore eta) *
                finiteMGF reference firstScore eta =
              (Real.exp (2 * eta * sensitivity) *
                (reference outcome).toReal * Real.exp (eta * secondScore outcome) *
                finiteMGF reference firstScore eta) /
                finiteMGF reference secondScore eta by field_simp]
          apply (le_div_iff₀ hsecondPos).2
          have hfactor : 0 ≤ (reference outcome).toReal *
              Real.exp (eta * secondScore outcome) * Real.exp (eta * sensitivity) := by
            positivity
          have hmult := mul_le_mul_of_nonneg_left hden hfactor
          rw [show Real.exp (2 * eta * sensitivity) =
            Real.exp (eta * sensitivity) * Real.exp (eta * sensitivity) by
              rw [← Real.exp_add]
              congr 1
              ring]
          convert hmult using 1 <;> ring
      _ ≤ Real.exp epsilon *
          ((reference outcome).toReal * Real.exp (eta * secondScore outcome) /
            finiteMGF reference secondScore eta) := by
          exact mul_le_mul_of_nonneg_right hbudgetExp
            (div_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hsecondPos.le)
  · simp [eventProbability]
  · intro outcome houtside
    rw [exponentialTilt_apply_toReal, exponentialTilt_apply_toReal]
    have hnum :
        Real.exp (eta * secondScore outcome) ≤
          Real.exp (eta * sensitivity) * Real.exp (eta * firstScore outcome) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hdiff := hsecondUpper outcome
      nlinarith
    have hrefPos : 0 < (reference outcome).toReal := hreference outcome
    have hfirstPos : 0 < finiteMGF reference firstScore eta :=
      finiteMGF_pos reference firstScore eta
    have hsecondPos : 0 < finiteMGF reference secondScore eta :=
      finiteMGF_pos reference secondScore eta
    calc
      (reference outcome).toReal * Real.exp (eta * secondScore outcome) /
          finiteMGF reference secondScore eta ≤
        (reference outcome).toReal *
          (Real.exp (eta * sensitivity) * Real.exp (eta * firstScore outcome)) /
          finiteMGF reference secondScore eta := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnum ENNReal.toReal_nonneg) hsecondPos.le
      _ ≤ Real.exp (2 * eta * sensitivity) *
          ((reference outcome).toReal * Real.exp (eta * firstScore outcome) /
            finiteMGF reference firstScore eta) := by
          apply (div_le_iff₀ hsecondPos).2
          rw [show Real.exp (2 * eta * sensitivity) *
              ((reference outcome).toReal * Real.exp (eta * firstScore outcome) /
                finiteMGF reference firstScore eta) *
                finiteMGF reference secondScore eta =
              (Real.exp (2 * eta * sensitivity) *
                (reference outcome).toReal * Real.exp (eta * firstScore outcome) *
                finiteMGF reference secondScore eta) /
                finiteMGF reference firstScore eta by field_simp]
          apply (le_div_iff₀ hfirstPos).2
          have hfactor : 0 ≤ (reference outcome).toReal *
              Real.exp (eta * firstScore outcome) * Real.exp (eta * sensitivity) := by
            positivity
          have hmult := mul_le_mul_of_nonneg_left hpartitionFirst hfactor
          rw [show Real.exp (2 * eta * sensitivity) =
            Real.exp (eta * sensitivity) * Real.exp (eta * sensitivity) by
              rw [← Real.exp_add]
              congr 1
              ring]
          convert hmult using 1 <;> ring
      _ ≤ Real.exp epsilon *
          ((reference outcome).toReal * Real.exp (eta * firstScore outcome) /
            finiteMGF reference firstScore eta) := by
          exact mul_le_mul_of_nonneg_right hbudgetExp
            (div_nonneg (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) hfirstPos.le)

/-- Dataset-indexed form of the finite exponential-mechanism guarantee. -/
theorem exponentialTilt_maxKLStable_of_score_sensitivity
    {Dataset Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (adjacent : Dataset → Dataset → Prop)
    (reference : PMF Outcome) (score : Dataset → Outcome → ℝ)
    (eta sensitivity epsilon : ℝ)
    (hreference : PMFFullSupport reference)
    (heta : 0 ≤ eta)
    (hscore : ∀ first second outcome, adjacent first second →
      |score first outcome - score second outcome| ≤ sensitivity)
    (hbudget : 2 * eta * sensitivity ≤ epsilon) :
    MaxKLStable adjacent (fun dataset => exponentialTilt reference (score dataset) eta)
      epsilon 0 := by
  intro first second hadjacent
  exact (exponentialTilt_maxKLClose_of_score_sensitivity reference
    (score first) (score second) eta sensitivity epsilon hreference heta
    (fun outcome => hscore first second outcome hadjacent) hbudget).1

end Privacy

end AppliedModelingLib
