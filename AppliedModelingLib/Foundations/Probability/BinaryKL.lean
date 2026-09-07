import AppliedModelingLib.Foundations.Math.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Binary Kullback--Leibler divergence

Elementary real-analysis identities for the KL divergence of two Bernoulli
laws.  The declarations are probability-model independent: they use the
source's displayed two-coordinate formula directly, and are reusable wherever
binary error rates are represented as real numbers in `(0,1)`.
-/

namespace AppliedModelingLib
namespace Probability

/-- The binary relative entropy `KL(p || q)` in the source's real formula. -/
noncomputable def binaryKLDivergence (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/--
At a one-half reference probability, binary KL is the negative logarithm of
the familiar AdaBoost/Hellinger factor.
-/
theorem binaryKLDivergence_half_eq_neg_log_two_sqrt
    {error : ℝ} (herror : 0 < error ∧ error < 1) :
    binaryKLDivergence (1 / 2) error =
      -Real.log (2 * Real.sqrt (error * (1 - error))) := by
  have hcomplement_pos : 0 < 1 - error := sub_pos.mpr herror.2
  have hproduct_pos : 0 < error * (1 - error) :=
    mul_pos herror.1 hcomplement_pos
  have hsqrt_pos : 0 < Real.sqrt (error * (1 - error)) :=
    Real.sqrt_pos.mpr hproduct_pos
  have hhalf_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hlog_half : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  unfold binaryKLDivergence
  rw [show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [Real.log_div hhalf_ne herror.1.ne',
    Real.log_div hhalf_ne hcomplement_pos.ne']
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hsqrt_pos.ne',
    Real.log_sqrt hproduct_pos.le]
  rw [hlog_half, Real.log_mul herror.1.ne' hcomplement_pos.ne']
  ring

/--
The exact exponential form of the one-round AdaBoost error factor in terms of
binary KL.
-/
theorem two_mul_sqrt_error_mul_one_sub_eq_exp_neg_binaryKL_half
    {error : ℝ} (herror : 0 < error ∧ error < 1) :
    2 * Real.sqrt (error * (1 - error)) =
      Real.exp (-binaryKLDivergence (1 / 2) error) := by
  have hcomplement_pos : 0 < 1 - error := sub_pos.mpr herror.2
  have hfactor_pos : 0 < 2 * Real.sqrt (error * (1 - error)) := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr (mul_pos herror.1 hcomplement_pos))
  rw [binaryKLDivergence_half_eq_neg_log_two_sqrt herror]
  rw [neg_neg, Real.exp_log hfactor_pos]

/-- The centered binary-KL closed form used in the Chernoff calculation. -/
theorem binaryKLDivergence_half_half_sub_eq_neg_half_log_one_sub_four_sq
    {gamma : ℝ} (hgamma_lower : -(1 / 2 : ℝ) < gamma)
    (hgamma_upper : gamma < 1 / 2) :
    binaryKLDivergence (1 / 2) (1 / 2 - gamma) =
      -Real.log (1 - 4 * gamma ^ 2) / 2 := by
  have herror_pos : 0 < 1 / 2 - gamma := by linarith
  have herror_lt_one : 1 / 2 - gamma < 1 := by linarith
  have hcomplement_pos : 0 < 1 - (1 / 2 - gamma) := by linarith
  have hproduct_pos : 0 < (1 / 2 - gamma) * (1 - (1 / 2 - gamma)) :=
    mul_pos herror_pos hcomplement_pos
  have hkl := binaryKLDivergence_half_eq_neg_log_two_sqrt
    (error := 1 / 2 - gamma) ⟨herror_pos, herror_lt_one⟩
  have hsquare :
      (2 * Real.sqrt ((1 / 2 - gamma) * (1 - (1 / 2 - gamma)))) ^ 2 =
        1 - 4 * gamma ^ 2 := by
    have hsqrt_sq := Real.sq_sqrt hproduct_pos.le
    nlinarith
  have hfactor_pos : 0 <
      2 * Real.sqrt ((1 / 2 - gamma) * (1 - (1 / 2 - gamma))) := by
    exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hproduct_pos)
  have hlog_factor :
      Real.log (2 * Real.sqrt ((1 / 2 - gamma) * (1 - (1 / 2 - gamma)))) =
        Real.log (1 - 4 * gamma ^ 2) / 2 := by
    have hlog_sq := Real.log_pow
      (2 * Real.sqrt ((1 / 2 - gamma) * (1 - (1 / 2 - gamma)))) 2
    rw [hsquare] at hlog_sq
    linarith
  rw [hkl, hlog_factor]
  ring

/--
The binary Pinsker lower bound in the centered form used by AdaBoost: if the
error is `1/2 - gamma`, then `KL(1/2 || 1/2-gamma) ≥ 2 gamma²`.
-/
theorem two_mul_sq_le_binaryKLDivergence_half_half_sub
    {gamma : ℝ} (hgamma_lower : -(1 / 2 : ℝ) < gamma)
    (hgamma_upper : gamma < 1 / 2) :
    2 * gamma ^ 2 ≤ binaryKLDivergence (1 / 2) (1 / 2 - gamma) := by
  have herror_pos : 0 < 1 / 2 - gamma := by linarith
  have herror_lt_one : 1 / 2 - gamma < 1 := by linarith
  have hfour_sq_nonneg : 0 ≤ 4 * gamma ^ 2 := by positivity
  have hfour_sq_lt_one : 4 * gamma ^ 2 < 1 := by
    nlinarith [sq_nonneg (gamma - 1 / 2), sq_nonneg (gamma + 1 / 2)]
  have hlog_bound := AppliedModelingLib.Math.le_neg_log_one_sub
    hfour_sq_nonneg hfour_sq_lt_one
  have hkl := binaryKLDivergence_half_half_sub_eq_neg_half_log_one_sub_four_sq
    hgamma_lower hgamma_upper
  rw [hkl]
  linarith

/--
The equal-edge exponent identity in AdaBoost Eq. (22), with the iteration
count kept as a natural number and the source's real exponent made explicit.
-/
theorem exp_neg_nat_mul_binaryKLDivergence_half_half_sub_eq_rpow
    {gamma : ℝ} (hgamma_lower : -(1 / 2 : ℝ) < gamma)
    (hgamma_upper : gamma < 1 / 2) (rounds : ℕ) :
    Real.exp (-(rounds : ℝ) * binaryKLDivergence (1 / 2) (1 / 2 - gamma)) =
      (1 - 4 * gamma ^ 2) ^ ((rounds : ℝ) / 2) := by
  have hbase_pos : 0 < 1 - 4 * gamma ^ 2 := by
    nlinarith [sq_nonneg (gamma - 1 / 2), sq_nonneg (gamma + 1 / 2)]
  have hkl := binaryKLDivergence_half_half_sub_eq_neg_half_log_one_sub_four_sq
    hgamma_lower hgamma_upper
  calc
    Real.exp (-(rounds : ℝ) * binaryKLDivergence (1 / 2) (1 / 2 - gamma)) =
        Real.exp (Real.log (1 - 4 * gamma ^ 2) * ((rounds : ℝ) / 2)) := by
          rw [hkl]
          congr 1
          ring
    _ = (1 - 4 * gamma ^ 2) ^ ((rounds : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hbase_pos]

end Probability
end AppliedModelingLib
