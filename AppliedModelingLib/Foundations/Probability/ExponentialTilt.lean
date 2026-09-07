import Mathlib.Analysis.SpecialFunctions.Exp
import AppliedModelingLib.Foundations.Probability.FiniteKL
import AppliedModelingLib.Foundations.Probability.FiniteSupportMGF

/-!
# Finite exponential tilting

This module supplies the policy-optimization-facing exponential tilt of a
finite PMF.  Its partition function reuses the existing `finiteMGF` rather
than introducing another normalization abstraction.  The older
`finiteExponentialTilt` in the large-deviation layer remains a specialized
change-of-measure construction; this API keeps optimization dependencies
narrow and states its support and log-ratio facts directly.

## Main declarations

- `exponentialTilt`
- `exponentialTilt_apply_toReal`
- `continuous_exponentialTilt_apply_toReal`
- `continuous_finiteKLDivergence_exponentialTilt`
- `pmfExp_exponentialTilt`
- `exponentialTilt_fullSupport`
- `exponentialTilt_zero`
- `exponentialTilt_log_ratio`
- `exponentialTilt_add_constant`
-/

open scoped BigOperators

namespace AppliedModelingLib

/--
Tilt a finite reference PMF by a real-valued utility at a real inverse-temperature.
The normalizing partition function is `finiteMGF reference utility inverseTemperature`.
-/
noncomputable def exponentialTilt {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ) :
    PMF Outcome :=
  PMF.ofFintype
    (fun outcome : Outcome =>
      ENNReal.ofReal
        ((reference outcome).toReal * Real.exp (inverseTemperature * utility outcome) /
          Probability.finiteMGF reference utility inverseTemperature))
    (by
      classical
      have hterm_nonneg : ∀ outcome : Outcome,
          0 ≤ (reference outcome).toReal * Real.exp (inverseTemperature * utility outcome) /
            Probability.finiteMGF reference utility inverseTemperature := by
        intro outcome
        exact div_nonneg
          (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
          (Probability.finiteMGF_pos reference utility inverseTemperature).le
      have hsum_real :
          (∑ outcome : Outcome,
              (reference outcome).toReal *
                Real.exp (inverseTemperature * utility outcome) /
                Probability.finiteMGF reference utility inverseTemperature) = 1 := by
        rw [← Finset.sum_div]
        field_simp [(Probability.finiteMGF_pos reference utility inverseTemperature).ne']
        rfl
      calc
        (∑ outcome : Outcome,
            ENNReal.ofReal
              ((reference outcome).toReal *
                Real.exp (inverseTemperature * utility outcome) /
                  Probability.finiteMGF reference utility inverseTemperature)) =
            ENNReal.ofReal
              (∑ outcome : Outcome,
                (reference outcome).toReal *
                  Real.exp (inverseTemperature * utility outcome) /
                    Probability.finiteMGF reference utility inverseTemperature) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg
                (s := (Finset.univ : Finset Outcome))
                (f := fun outcome : Outcome =>
                  (reference outcome).toReal *
                    Real.exp (inverseTemperature * utility outcome) /
                    Probability.finiteMGF reference utility inverseTemperature)
                (by intro outcome _; exact hterm_nonneg outcome)
        _ = 1 := by rw [hsum_real]; norm_num)

/-- The real mass formula for a finite exponential tilt. -/
@[simp] theorem exponentialTilt_apply_toReal
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (outcome : Outcome) :
    (exponentialTilt reference utility inverseTemperature outcome).toReal =
      (reference outcome).toReal * Real.exp (inverseTemperature * utility outcome) /
        Probability.finiteMGF reference utility inverseTemperature := by
  unfold exponentialTilt
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg
      (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    (Probability.finiteMGF_pos reference utility inverseTemperature).le)

/-- Each real atom mass of a finite exponential tilt varies continuously with
the inverse temperature.  The finite MGF denominator is strictly positive at
every real parameter, so this is an ordinary quotient-continuity statement. -/
theorem continuous_exponentialTilt_apply_toReal
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (outcome : Outcome) :
    Continuous (fun inverseTemperature : ℝ =>
      (exponentialTilt reference utility inverseTemperature outcome).toReal) := by
  rw [show (fun inverseTemperature : ℝ =>
      (exponentialTilt reference utility inverseTemperature outcome).toReal) =
      (fun inverseTemperature : ℝ =>
        (reference outcome).toReal * Real.exp (inverseTemperature * utility outcome) /
          Probability.finiteMGF reference utility inverseTemperature) by
        funext inverseTemperature
        exact exponentialTilt_apply_toReal reference utility inverseTemperature outcome]
  apply Continuous.div
  · exact continuous_const.mul
      (Real.continuous_exp.comp (continuous_id.mul continuous_const))
  · exact Probability.finiteMGF_continuous reference utility
  · intro inverseTemperature
    exact (Probability.finiteMGF_pos reference utility inverseTemperature).ne'

/-- The finite KL divergence of the exponential-tilt path from its reference
PMF is continuous in inverse temperature.  This is the compact finite
one-dimensional object used to match active KL budgets to Gibbs policies. -/
theorem continuous_finiteKLDivergence_exponentialTilt
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) :
    Continuous (fun inverseTemperature : ℝ =>
      finiteKLDivergence (exponentialTilt reference utility inverseTemperature) reference) := by
  unfold finiteKLDivergence
  apply continuous_finset_sum
  intro outcome _
  have hmass := continuous_exponentialTilt_apply_toReal reference utility outcome
  simpa only [mul_sub] using
    ((Real.continuous_mul_log.comp hmass).sub
      (hmass.mul continuous_const))

/-- The utility expectation under an exponential tilt is the normalized
exponentially weighted utility sum.  This is the finite score-matching
identity used to turn a stationary log-MGF equation into a Gibbs policy with
a prescribed expected score. -/
theorem pmfExp_exponentialTilt
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ) :
    pmfExp (exponentialTilt reference utility inverseTemperature) utility =
      (∑ outcome : Outcome,
        (reference outcome).toReal *
          (utility outcome * Real.exp (inverseTemperature * utility outcome))) /
        Probability.finiteMGF reference utility inverseTemperature := by
  unfold pmfExp
  calc
    ∑ outcome : Outcome,
        (exponentialTilt reference utility inverseTemperature outcome).toReal * utility outcome =
        ∑ outcome : Outcome,
          ((reference outcome).toReal *
            Real.exp (inverseTemperature * utility outcome) /
              Probability.finiteMGF reference utility inverseTemperature) * utility outcome := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            rw [exponentialTilt_apply_toReal]
    _ =
        ∑ outcome : Outcome,
          ((reference outcome).toReal *
            (utility outcome * Real.exp (inverseTemperature * utility outcome))) /
              Probability.finiteMGF reference utility inverseTemperature := by
            refine Finset.sum_congr rfl fun outcome _ => ?_
            ring
    _ =
        (∑ outcome : Outcome,
          (reference outcome).toReal *
            (utility outcome * Real.exp (inverseTemperature * utility outcome))) /
          Probability.finiteMGF reference utility inverseTemperature := by
            rw [Finset.sum_div]

/-- Exponential tilting preserves full support of the reference PMF. -/
theorem exponentialTilt_fullSupport
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (hreference : PMFFullSupport reference) :
    PMFFullSupport (exponentialTilt reference utility inverseTemperature) := by
  intro outcome
  rw [exponentialTilt_apply_toReal]
  exact div_pos
    (mul_pos (hreference outcome) (Real.exp_pos _))
    (Probability.finiteMGF_pos reference utility inverseTemperature)

/-- Tilting at inverse temperature zero leaves a finite PMF unchanged. -/
theorem exponentialTilt_zero
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) :
    exponentialTilt reference utility 0 = reference := by
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((exponentialTilt reference utility 0).apply_ne_top outcome)
    (reference.apply_ne_top outcome)).mp
  rw [exponentialTilt_apply_toReal, Probability.finiteMGF_zero]
  simp

/-- Shifting a score by a constant factors its finite moment-generating function. -/
theorem finiteMGF_add_constant
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ)
    (constant inverseTemperature : ℝ) :
    Probability.finiteMGF reference (fun outcome => utility outcome + constant) inverseTemperature =
      Real.exp (inverseTemperature * constant) *
        Probability.finiteMGF reference utility inverseTemperature := by
  simpa [sub_eq_add_neg] using
    Probability.finiteMGF_sub_const reference utility (-constant) inverseTemperature

/-- Adding a response-independent constant to utility does not change its exponential tilt. -/
theorem exponentialTilt_add_constant
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ)
    (constant inverseTemperature : ℝ) :
    exponentialTilt reference (fun outcome => utility outcome + constant) inverseTemperature =
      exponentialTilt reference utility inverseTemperature := by
  apply PMF.ext
  intro outcome
  apply (ENNReal.toReal_eq_toReal_iff'
    ((exponentialTilt reference (fun outcome => utility outcome + constant)
      inverseTemperature).apply_ne_top outcome)
    ((exponentialTilt reference utility inverseTemperature).apply_ne_top outcome)).mp
  rw [exponentialTilt_apply_toReal, exponentialTilt_apply_toReal,
    finiteMGF_add_constant]
  rw [show inverseTemperature * (utility outcome + constant) =
    inverseTemperature * utility outcome + inverseTemperature * constant by ring,
    Real.exp_add]
  field_simp [Probability.finiteMGF_pos reference utility inverseTemperature |>.ne',
    (Real.exp_pos (inverseTemperature * constant)).ne']

/-- The tilt/reference log ratio is utility minus the log partition function. -/
theorem exponentialTilt_log_ratio
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    (hreference : PMFFullSupport reference) (outcome : Outcome) :
    Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal -
        Real.log (reference outcome).toReal =
      inverseTemperature * utility outcome -
        Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
  rw [exponentialTilt_apply_toReal]
  have hreference_pos : 0 < (reference outcome).toReal := hreference outcome
  have hexp_pos : 0 < Real.exp (inverseTemperature * utility outcome) := Real.exp_pos _
  have hpartition_pos : 0 < Probability.finiteMGF reference utility inverseTemperature :=
    Probability.finiteMGF_pos reference utility inverseTemperature
  rw [Real.log_div
    (mul_ne_zero hreference_pos.ne' hexp_pos.ne') hpartition_pos.ne']
  rw [Real.log_mul hreference_pos.ne' hexp_pos.ne', Real.log_exp]
  ring

/-- The pointwise log-ratio identity for an exponential tilt.  Unlike
`exponentialTilt_log_ratio`, this form needs positivity only at the displayed
outcome, so it applies naturally to PMFs with zeros outside their support. -/
theorem exponentialTilt_log_ratio_of_pos
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (reference : PMF Outcome) (utility : Outcome → ℝ) (inverseTemperature : ℝ)
    {outcome : Outcome} (houtcome : 0 < (reference outcome).toReal) :
    Real.log (exponentialTilt reference utility inverseTemperature outcome).toReal -
        Real.log (reference outcome).toReal =
      inverseTemperature * utility outcome -
        Real.log (Probability.finiteMGF reference utility inverseTemperature) := by
  rw [exponentialTilt_apply_toReal]
  have hexp_pos : 0 < Real.exp (inverseTemperature * utility outcome) := Real.exp_pos _
  have hpartition_pos : 0 < Probability.finiteMGF reference utility inverseTemperature :=
    Probability.finiteMGF_pos reference utility inverseTemperature
  rw [Real.log_div
    (mul_ne_zero houtcome.ne' hexp_pos.ne') hpartition_pos.ne']
  rw [Real.log_mul houtcome.ne' hexp_pos.ne', Real.log_exp]
  ring

end AppliedModelingLib
