import AppliedModelingLib.Foundations.Probability.PoissonMoments

/-!
# Exponential generating functions of Poisson counts

This module records the probability generating function of a Poisson count,
in a form suitable for compound-Poisson input calculations.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/-- The probability generating function of a Poisson count. -/
theorem integral_pow_poissonMeasure (mean : ℝ≥0) (q : ℝ) :
    ∫ n : ℕ, q ^ n ∂poissonMeasure mean =
      Real.exp ((mean : ℝ) * (q - 1)) := by
  rw [integral_poissonMeasure]
  calc
    ∑' n : ℕ, (Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ n /
        (n.factorial : ℝ)) • q ^ n =
        Real.exp (-(mean : ℝ)) *
          ∑' n : ℕ, ((mean : ℝ) * q) ^ n / (n.factorial : ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [smul_eq_mul]
      rw [mul_pow]
      ring
    _ = Real.exp (-(mean : ℝ)) * Real.exp ((mean : ℝ) * q) := by
      rw [(NormedSpace.expSeries_div_hasSum_exp ((mean : ℝ) * q)).tsum_eq,
        ← Real.exp_eq_exp_ℝ]
    _ = Real.exp ((mean : ℝ) * (q - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Every real power of a Poisson count is integrable. -/
theorem integrable_pow_poissonMeasure (mean : ℝ≥0) (q : ℝ) :
    Integrable (fun n : ℕ => q ^ n) (poissonMeasure mean) := by
  by_contra h
  have hzero : ∫ n : ℕ, q ^ n ∂poissonMeasure mean = 0 :=
    integral_undef h
  rw [integral_pow_poissonMeasure] at hzero
  exact (Real.exp_pos _).ne' hzero

end

end AppliedModelingLib.Probability.PoissonProcess
