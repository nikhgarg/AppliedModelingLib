import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Fractional Square-Root Monotonicity

Reusable scalar algebra for access-barrier and precision-comparison proofs.

## Main declarations

- `sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one`
- `sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho`
- `sqrt_self_div_add_const_le_of_le`
-/

namespace AppliedModelingLib

open Set

/--
The precision-to-posterior-scale map `x ↦ sqrt (x / (a + x))` is monotone on
nonnegative `x` when the prior precision `a` is positive.
-/
theorem sqrt_self_div_add_const_le_of_le
    {a x y : ℝ}
    (ha : 0 < a) (hx : 0 ≤ x) (hxy : x ≤ y) :
    Real.sqrt (x / (a + x)) ≤ Real.sqrt (y / (a + y)) := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hdenx : 0 < a + x := by linarith
  have hdeny : 0 < a + y := by linarith
  have hfrac : x / (a + x) ≤ y / (a + y) := by
    rw [div_le_div_iff₀ hdenx hdeny]
    nlinarith
  exact Real.sqrt_le_sqrt hfrac

/--
If `0 ≤ rho < 1`, then
`x ↦ sqrt ((a*x + b*rho) / (a*x + b))` is strictly increasing on nonnegative
`x`, for positive `a` and `b`.
-/
theorem sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one
    {a b rho x y : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1)
    (hx_nonneg : 0 ≤ x) (hxy : x < y) :
    Real.sqrt ((a * x + b * rho) / (a * x + b)) <
      Real.sqrt ((a * y + b * rho) / (a * y + b)) := by
  have hy_nonneg : 0 ≤ y := le_trans hx_nonneg hxy.le
  have hdenx_pos : 0 < a * x + b := by nlinarith [mul_nonneg ha.le hx_nonneg]
  have hdeny_pos : 0 < a * y + b := by nlinarith [mul_nonneg ha.le hy_nonneg]
  have hnumx_nonneg : 0 ≤ a * x + b * rho := by
    nlinarith [mul_nonneg ha.le hx_nonneg, mul_nonneg hb.le hrho_nonneg]
  have hfracx_nonneg : 0 ≤ (a * x + b * rho) / (a * x + b) :=
    div_nonneg hnumx_nonneg hdenx_pos.le
  have hfrac_lt :
      (a * x + b * rho) / (a * x + b) <
        (a * y + b * rho) / (a * y + b) := by
    rw [div_lt_div_iff₀ hdenx_pos hdeny_pos]
    have hdiff :
        (a * y + b * rho) * (a * x + b) -
            (a * x + b * rho) * (a * y + b) =
          a * b * (1 - rho) * (y - x) := by
      ring
    have hprod_pos : 0 < a * b * (1 - rho) * (y - x) := by
      exact mul_pos (mul_pos (mul_pos ha hb) (sub_pos.mpr hrho_lt_one))
        (sub_pos.mpr hxy)
    nlinarith
  exact (Real.sqrt_lt_sqrt_iff hfracx_nonneg).mpr hfrac_lt

/--
If `1 < rho`, then
`x ↦ sqrt ((a*x*rho + b) / (a*x + b))` is strictly increasing on nonnegative
`x`, for positive `a` and `b`.
-/
theorem sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho
    {a b rho x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hone_lt_rho : 1 < rho)
    (hx_nonneg : 0 ≤ x) (hxy : x < y) :
    Real.sqrt ((a * x * rho + b) / (a * x + b)) <
      Real.sqrt ((a * y * rho + b) / (a * y + b)) := by
  have hy_nonneg : 0 ≤ y := le_trans hx_nonneg hxy.le
  have hrho_pos : 0 < rho := lt_trans zero_lt_one hone_lt_rho
  have hdenx_pos : 0 < a * x + b := by nlinarith [mul_nonneg ha.le hx_nonneg]
  have hdeny_pos : 0 < a * y + b := by nlinarith [mul_nonneg ha.le hy_nonneg]
  have hnumx_nonneg : 0 ≤ a * x * rho + b := by
    nlinarith [mul_nonneg (mul_nonneg ha.le hx_nonneg) hrho_pos.le, hb.le]
  have hfracx_nonneg : 0 ≤ (a * x * rho + b) / (a * x + b) :=
    div_nonneg hnumx_nonneg hdenx_pos.le
  have hfrac_lt :
      (a * x * rho + b) / (a * x + b) <
        (a * y * rho + b) / (a * y + b) := by
    rw [div_lt_div_iff₀ hdenx_pos hdeny_pos]
    have hdiff :
        (a * y * rho + b) * (a * x + b) -
            (a * x * rho + b) * (a * y + b) =
          a * b * (rho - 1) * (y - x) := by
      ring
    have hprod_pos : 0 < a * b * (rho - 1) * (y - x) := by
      exact mul_pos (mul_pos (mul_pos ha hb) (sub_pos.mpr hone_lt_rho))
        (sub_pos.mpr hxy)
    nlinarith
  exact (Real.sqrt_lt_sqrt_iff hfracx_nonneg).mpr hfrac_lt

/--
Strict-monotone-on form of
`sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one`.
-/
theorem strictMonoOn_sqrt_fractionalLinear_const_mul_of_rho_lt_one
    {a b rho : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    StrictMonoOn
      (fun x : ℝ => Real.sqrt ((a * x + b * rho) / (a * x + b)))
      (Ici 0) := by
  intro x hx y _hy hxy
  exact sqrt_fractionalLinear_const_mul_lt_of_rho_lt_one
    ha hb hrho_nonneg hrho_lt_one hx hxy

/--
Strict-monotone-on form of
`sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho`.
-/
theorem strictMonoOn_sqrt_fractionalLinear_mul_const_of_one_lt_rho
    {a b rho : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hone_lt_rho : 1 < rho) :
    StrictMonoOn
      (fun x : ℝ => Real.sqrt ((a * x * rho + b) / (a * x + b)))
      (Ici 0) := by
  intro x hx y _hy hxy
  exact sqrt_fractionalLinear_mul_const_lt_of_one_lt_rho
    ha hb hone_lt_rho hx hxy

end AppliedModelingLib
