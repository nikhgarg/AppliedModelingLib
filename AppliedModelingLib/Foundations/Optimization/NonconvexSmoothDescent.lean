import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex

/-!
# One-step inexact smooth descent

This module gives the deterministic algebra behind finite-time nonconvex SGD:
a smooth objective is updated with an exact sampled gradient plus an
approximation error.  The result keeps the sampling fluctuation and the
approximation error separate, so probability layers can later take conditional
expectations without obscuring the optimization argument.
-/

namespace AppliedModelingLib
namespace Optimization

open scoped InnerProductSpace

variable {Parameter : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
  [CompleteSpace Parameter]

/--
One inexact gradient step for a smooth, possibly nonconvex objective.  The
sampled exact gradient and the inner-solver error appear as separate terms.
This is the deterministic inequality used before taking conditional
expectations in finite-time nonconvex SGD bounds.
-/
theorem inexactSmoothDescentStep
    (objective : Parameter → ℝ) (gradient : Parameter → Parameter) (smoothness : ℝ)
    (hgradient : ∀ first second,
      ‖gradient first - gradient second‖ ≤ smoothness * ‖first - second‖)
    (hgradientAt : ∀ parameter, HasGradientAt objective (gradient parameter) parameter)
    {point sampledGradient approximationError : Parameter} {step : ℝ}
    (hsmoothness : 0 ≤ smoothness) (hstep : 0 ≤ step)
    (hstepSmooth : smoothness * step ≤ 1) :
    objective (point - step • (sampledGradient + approximationError)) ≤
      objective point - step / 2 * ‖gradient point‖ ^ 2 +
        step * (1 - smoothness * step) *
          ⟪gradient point, gradient point - sampledGradient⟫_ℝ +
        step * (1 + smoothness * step) / 2 * ‖approximationError‖ ^ 2 +
        smoothness * step ^ 2 * ‖sampledGradient - gradient point‖ ^ 2 := by
  have hmodel := smooth_upper_model_bound objective gradient smoothness hgradient hgradientAt
    point (point - step • (sampledGradient + approximationError))
  have hdisplacement :
      point - step • (sampledGradient + approximationError) - point =
        -(step • (sampledGradient + approximationError)) := by
    abel
  rw [hdisplacement, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hstep] at hmodel
  have hmodel' :
      objective (point - step • (sampledGradient + approximationError)) ≤
        objective point - step * ⟪gradient point, sampledGradient + approximationError⟫_ℝ +
          smoothness / 2 * step ^ 2 * ‖sampledGradient + approximationError‖ ^ 2 := by
    nlinarith [hmodel]
  have hfirstSquare :
      0 ≤ (1 - smoothness * step) * ‖gradient point + approximationError‖ ^ 2 := by
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hsecondSquare :
      0 ≤ (smoothness * step) *
        ‖(sampledGradient - gradient point) - approximationError‖ ^ 2 := by
    exact mul_nonneg (mul_nonneg hsmoothness hstep) (sq_nonneg _)
  have hidentity :
      (objective point - step / 2 * ‖gradient point‖ ^ 2 +
          step * (1 - smoothness * step) *
            ⟪gradient point, gradient point - sampledGradient⟫_ℝ +
          step * (1 + smoothness * step) / 2 * ‖approximationError‖ ^ 2 +
          smoothness * step ^ 2 * ‖sampledGradient - gradient point‖ ^ 2) -
        (objective point - step *
            ⟪gradient point, sampledGradient + approximationError⟫_ℝ +
          smoothness / 2 * step ^ 2 * ‖sampledGradient + approximationError‖ ^ 2) =
        step / 2 *
          ((1 - smoothness * step) * ‖gradient point + approximationError‖ ^ 2 +
            (smoothness * step) *
              ‖(sampledGradient - gradient point) - approximationError‖ ^ 2) := by
    simp only [inner_add_right, inner_sub_right, inner_sub_left, real_inner_comm,
      real_inner_self_eq_norm_sq,
      norm_add_sq_real, norm_sub_sq_real]
    ring
  calc
    objective (point - step • (sampledGradient + approximationError)) ≤
        objective point - step * ⟪gradient point, sampledGradient + approximationError⟫_ℝ +
          smoothness / 2 * step ^ 2 * ‖sampledGradient + approximationError‖ ^ 2 := hmodel'
    _ ≤ objective point - step / 2 * ‖gradient point‖ ^ 2 +
          step * (1 - smoothness * step) *
            ⟪gradient point, gradient point - sampledGradient⟫_ℝ +
          step * (1 + smoothness * step) / 2 * ‖approximationError‖ ^ 2 +
          smoothness * step ^ 2 * ‖sampledGradient - gradient point‖ ^ 2 := by
      have hsquares : 0 ≤
          (1 - smoothness * step) * ‖gradient point + approximationError‖ ^ 2 +
            (smoothness * step) *
              ‖(sampledGradient - gradient point) - approximationError‖ ^ 2 :=
        add_nonneg hfirstSquare hsecondSquare
      have hgap : 0 ≤
          (objective point - step / 2 * ‖gradient point‖ ^ 2 +
              step * (1 - smoothness * step) *
                ⟪gradient point, gradient point - sampledGradient⟫_ℝ +
              step * (1 + smoothness * step) / 2 * ‖approximationError‖ ^ 2 +
              smoothness * step ^ 2 * ‖sampledGradient - gradient point‖ ^ 2) -
            (objective point - step *
                ⟪gradient point, sampledGradient + approximationError⟫_ℝ +
              smoothness / 2 * step ^ 2 * ‖sampledGradient + approximationError‖ ^ 2) := by
        rw [hidentity]
        exact mul_nonneg (div_nonneg hstep (by norm_num)) hsquares
      linarith

/--
Telescoping finite-horizon consequence of an expected smooth-descent
recurrence.  `potential t` may already be an expectation; this lemma makes no
probability construction of its own.  It is the paper-independent summation
step used after a stochastic analysis has established one such inequality per
round.

The error and variance terms are intentionally separate: inexact inner solves
typically contribute `step * error`, whereas unbiased stochastic gradients
contribute `smoothness * step^2 * variance`.
-/
theorem finiteHorizon_gradientSum_le_of_expectedDescent
    (potential gradientSq : ℕ → ℝ) (horizon : ℕ)
    (step error smoothness variance lowerBound : ℝ)
    (hstep : 0 < step) (hlowerBound : lowerBound ≤ potential horizon)
    (hdescent : ∀ time, time < horizon →
      potential (time + 1) ≤ potential time - step / 2 * gradientSq time +
        step * error + smoothness * step ^ 2 * variance) :
    (∑ time ∈ Finset.range horizon, gradientSq time) ≤
      2 / step * (potential 0 - lowerBound) +
        2 * (horizon : ℝ) * error +
        2 * (horizon : ℝ) * smoothness * step * variance := by
  have htelescoping :
      (∑ time ∈ Finset.range horizon, (potential time - potential (time + 1))) =
        potential 0 - potential horizon := by
    calc
      (∑ time ∈ Finset.range horizon, (potential time - potential (time + 1))) =
          -(∑ time ∈ Finset.range horizon, (potential (time + 1) - potential time)) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro time _
            ring
      _ = -(potential horizon - potential 0) := by rw [Finset.sum_range_sub]
      _ = potential 0 - potential horizon := by ring
  have hperTime : ∀ time, time < horizon →
      step / 2 * gradientSq time ≤
        potential time - potential (time + 1) +
          (step * error + smoothness * step ^ 2 * variance) := by
    intro time htime
    linarith [hdescent time htime]
  have hsum :
      step / 2 * (∑ time ∈ Finset.range horizon, gradientSq time) ≤
        (potential 0 - potential horizon) +
          (horizon : ℝ) * (step * error + smoothness * step ^ 2 * variance) := by
    calc
      step / 2 * (∑ time ∈ Finset.range horizon, gradientSq time) =
          ∑ time ∈ Finset.range horizon, step / 2 * gradientSq time := by
            rw [Finset.mul_sum]
      _ ≤ ∑ time ∈ Finset.range horizon,
          (potential time - potential (time + 1) +
            (step * error + smoothness * step ^ 2 * variance)) := by
            apply Finset.sum_le_sum
            intro time htime
            exact hperTime time (Finset.mem_range.mp htime)
      _ = (potential 0 - potential horizon) +
          (horizon : ℝ) * (step * error + smoothness * step ^ 2 * variance) := by
            rw [Finset.sum_add_distrib, htelescoping]
            simp
            ring
  have hsumLower :
      step / 2 * (∑ time ∈ Finset.range horizon, gradientSq time) ≤
        (potential 0 - lowerBound) +
          (horizon : ℝ) * (step * error + smoothness * step ^ 2 * variance) := by
    nlinarith [hsum, hlowerBound]
  have hstepHalf : 0 < step / 2 := by positivity
  have hrewrite :
      2 / step * (potential 0 - lowerBound) +
          2 * (horizon : ℝ) * error +
          2 * (horizon : ℝ) * smoothness * step * variance =
        ((potential 0 - lowerBound) +
          (horizon : ℝ) * (step * error + smoothness * step ^ 2 * variance)) /
          (step / 2) := by
    field_simp
    ring
  rw [hrewrite]
  apply (le_div_iff₀ hstepHalf).mpr
  rw [mul_comm]
  exact hsumLower

end Optimization
end AppliedModelingLib
