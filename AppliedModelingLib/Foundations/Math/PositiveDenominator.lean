import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

namespace AppliedModelingLib
namespace PositiveDenominator

/-- Clear two positive denominators in a non-strict ratio comparison. -/
theorem div_le_div_of_cross_mul_le
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d ≤ c * b) :
    a / b ≤ c / d := by
  apply le_of_mul_le_mul_right (a := b * d)
  · calc
      a / b * (b * d) = a * d := by
        field_simp [ne_of_gt hb]
      _ ≤ c * b := hcross
      _ = c / d * (b * d) := by
        field_simp [ne_of_gt hd]
  · exact mul_pos hb hd

/-- Clear two positive denominators in a strict ratio comparison. -/
theorem div_lt_div_of_cross_mul_lt
    {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hcross : a * d < c * b) :
    a / b < c / d := by
  apply lt_of_mul_lt_mul_right (a := b * d)
  · calc
      a / b * (b * d) = a * d := by
        field_simp [ne_of_gt hb]
      _ < c * b := hcross
      _ = c / d * (b * d) := by
        field_simp [ne_of_gt hd]
  · exact le_of_lt (mul_pos hb hd)

/--
Clear two positive denominators in the product sign for a difference of
normalized masses.
-/
theorem sub_div_mul_nonneg_of_cross_sub_mul_nonneg
    {a b c d g : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hcross : 0 ≤ (a * d - c * b) * g) :
    0 ≤ (a / b - c / d) * g := by
  have hden_nonneg : 0 ≤ b * d := le_of_lt (mul_pos hb hd)
  have hrewrite :
      (a / b - c / d) * g = ((a * d - c * b) * g) / (b * d) := by
    field_simp [ne_of_gt hb, ne_of_gt hd]
  rw [hrewrite]
  exact div_nonneg hcross hden_nonneg

end PositiveDenominator
end AppliedModelingLib
