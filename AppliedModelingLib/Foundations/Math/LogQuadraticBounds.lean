import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# Quadratic bounds for the logarithm

Elementary second-order lower bounds on the logarithmic loss near one.
-/

namespace AppliedModelingLib.Math

open Set

/-- On `[0, 1)`, the negative logarithmic loss dominates its quadratic
Taylor polynomial. -/
theorem add_half_sq_le_neg_log_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
  let f : ℝ → ℝ := fun y => -Real.log (1 - y) - y - y ^ 2 / 2
  let f' : ℝ → ℝ := fun y => y ^ 2 / (1 - y)
  have hderiv : ∀ y < 1, HasDerivAt f (f' y) y := by
    intro y hy
    have hlog : HasDerivAt (fun z : ℝ => Real.log (1 - z))
        (-(1 - y)⁻¹) y := by
      convert ((hasDerivAt_id y).const_sub 1).log
        (ne_of_gt (sub_pos.mpr hy)) using 1
      all_goals simp only [id_eq]
      all_goals ring_nf
    have hquad : HasDerivAt (fun z : ℝ => z ^ 2 / 2) y y := by
      convert (hasDerivAt_pow 2 y).div_const (2 : ℝ) using 1
      all_goals ring_nf
    have hraw := hlog.neg.sub (hasDerivAt_id y) |>.sub hquad
    have hvalue : -(-(1 - y)⁻¹) - 1 - y = y ^ 2 / (1 - y) := by
      field_simp [ne_of_gt (sub_pos.mpr hy)]
      ring
    rw [hvalue] at hraw
    simpa [f, f'] using hraw
  have hcont : ContinuousOn f (Icc 0 x) := by
    intro y hy
    exact (hderiv y (lt_of_le_of_lt hy.2 hx1)).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc 0 x)
      hcont ?_ ?_
    · intro y hy
      have hy' : y < 1 := by
        rw [interior_Icc] at hy
        exact lt_of_lt_of_le hy.2 hx1.le
      exact (hderiv y hy').hasDerivWithinAt
    · intro y hy
      have hy' : y < 1 := by
        rw [interior_Icc] at hy
        exact lt_of_lt_of_le hy.2 hx1.le
      exact div_nonneg (sq_nonneg y) (by linarith)
  have hfx : f 0 ≤ f x := hmono (by simp [hx0]) (by simp [hx0]) hx0
  dsimp [f] at hfx
  norm_num at hfx
  linarith

end AppliedModelingLib.Math
