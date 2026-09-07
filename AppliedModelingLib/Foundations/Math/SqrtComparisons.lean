import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

namespace AppliedModelingLib

open Set
open scoped Topology

/-!
# Square-Root Comparison Lemmas

Reusable real-analysis facts for paper proofs whose closed-form thresholds
contain expressions of the form `sqrt (a * s ^ 2 + c + d / s ^ 2)`.

## Main declarations

- `sqrtQuadraticInv_hasDerivAt`
- `sqrtQuadraticInvSubSelf_antitoneOn_Ioi`
- `scaledSqrtQuadraticInvSubLinear_decreases`
-/

/-- Derivative of `a * x ^ 2 + c + d / x ^ 2` away from zero. -/
theorem sqrtQuadraticInv_hasDerivAt
    {a c d s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun x : ℝ => a * x ^ 2 + c + d / x ^ 2)
      (2 * a * s - 2 * d / s ^ 3) s := by
  have h1 : HasDerivAt (fun x : ℝ => a * x ^ 2 + c) (2 * a * s) s := by
    have hp := (hasDerivAt_pow 2 s).const_mul a
    have hp' : HasDerivAt (fun x : ℝ => a * x ^ 2)
        (a * (2 * s ^ (2 - 1))) s := hp
    convert hp'.const_add c using 1 <;> ring_nf
  have h2 : HasDerivAt (fun x : ℝ => d / x ^ 2) (-2 * d / s ^ 3) s := by
    have hp : HasDerivAt (fun x : ℝ => x ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have hinv := hp.inv (pow_ne_zero 2 hs)
    have hmul := hinv.const_mul d
    convert hmul using 1
    · field_simp [hs]
  have hsum := h1.add h2
  convert hsum using 1
  · ring

/--
For `0 < a ≤ 1` and `0 ≤ c,d`, the map
`s ↦ sqrt (a * s^2 + c + d/s^2) - s` is antitone on positive `s`.
-/
theorem sqrtQuadraticInvSubSelf_antitoneOn_Ioi
    {a c d : ℝ} (ha_pos : 0 < a) (ha_le_one : a ≤ 1)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d) :
    AntitoneOn (fun s : ℝ => Real.sqrt (a * s ^ 2 + c + d / s ^ 2) - s)
      (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro s hs
    have hs_pos : 0 < s := hs
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_ne_zero hs_ne
    have hinside_pos : 0 < a * s ^ 2 + c + d / s ^ 2 := by
      have ha_term_pos : 0 < a * s ^ 2 := mul_pos ha_pos hs_sq_pos
      have hd_term_nonneg : 0 ≤ d / s ^ 2 :=
        div_nonneg hd_nonneg hs_sq_pos.le
      linarith
    exact ((sqrtQuadraticInv_hasDerivAt (a := a) (c := c) (d := d) hs_ne).sqrt
      (ne_of_gt hinside_pos)).sub (hasDerivAt_id s) |>.continuousAt.continuousWithinAt
  · intro s hs
    have hs_pos : 0 < s := by
      simpa using (interior_subset hs)
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_ne_zero hs_ne
    have hinside_pos : 0 < a * s ^ 2 + c + d / s ^ 2 := by
      have ha_term_pos : 0 < a * s ^ 2 := mul_pos ha_pos hs_sq_pos
      have hd_term_nonneg : 0 ≤ d / s ^ 2 :=
        div_nonneg hd_nonneg hs_sq_pos.le
      linarith
    exact (((sqrtQuadraticInv_hasDerivAt (a := a) (c := c) (d := d) hs_ne).sqrt
      (ne_of_gt hinside_pos)).sub (hasDerivAt_id s)).differentiableAt.differentiableWithinAt
  · intro s hs
    have hs_pos : 0 < s := by
      simpa using (interior_subset hs)
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    have hs_sq_pos : 0 < s ^ 2 := sq_pos_of_ne_zero hs_ne
    have hinside_pos : 0 < a * s ^ 2 + c + d / s ^ 2 := by
      have ha_term_pos : 0 < a * s ^ 2 := mul_pos ha_pos hs_sq_pos
      have hd_term_nonneg : 0 ≤ d / s ^ 2 :=
        div_nonneg hd_nonneg hs_sq_pos.le
      linarith
    have hderiv :
        deriv (fun s : ℝ => Real.sqrt (a * s ^ 2 + c + d / s ^ 2) - s) s =
          (2 * a * s - 2 * d / s ^ 3) /
              (2 * Real.sqrt (a * s ^ 2 + c + d / s ^ 2)) -
            1 := by
      exact (((sqrtQuadraticInv_hasDerivAt (a := a) (c := c) (d := d) hs_ne).sqrt
        (ne_of_gt hinside_pos)).sub (hasDerivAt_id s)).deriv
    rw [hderiv]
    have hsqrt_pos :
        0 < Real.sqrt (a * s ^ 2 + c + d / s ^ 2) :=
      Real.sqrt_pos.mpr hinside_pos
    have hnum_le :
        2 * a * s - 2 * d / s ^ 3 ≤
          2 * Real.sqrt (a * s ^ 2 + c + d / s ^ 2) := by
      have hd_div_nonneg : 0 ≤ 2 * d / s ^ 3 := by
        have hs_cube_pos : 0 < s ^ 3 := by positivity
        exact div_nonneg (mul_nonneg (by norm_num) hd_nonneg) hs_cube_pos.le
      have hleft_le : 2 * a * s - 2 * d / s ^ 3 ≤ 2 * a * s := by
        linarith
      have ha_s_le : a * s ≤ Real.sqrt (a * s ^ 2 + c + d / s ^ 2) := by
        apply Real.le_sqrt_of_sq_le
        have hd_div_nonneg' : 0 ≤ d / s ^ 2 :=
          div_nonneg hd_nonneg hs_sq_pos.le
        nlinarith [mul_nonneg (sub_nonneg.mpr ha_le_one)
          (mul_nonneg ha_pos.le (sq_nonneg s))]
      nlinarith
    have hden_pos : 0 < 2 * Real.sqrt (a * s ^ 2 + c + d / s ^ 2) := by
      positivity
    rw [sub_nonpos]
    exact (div_le_one hden_pos).mpr hnum_le

/--
If `0 < a ≤ 1`, `c,d ≥ 0`, and the linear penalty slope is strictly larger
than the square-root multiplier, then
`k * sqrt(a*s^2 + c + d/s^2) - slope*s` strictly decreases as `s` increases.
-/
theorem scaledSqrtQuadraticInvSubLinear_decreases
    {a c d k slope sLow sHigh : ℝ}
    (ha_pos : 0 < a) (ha_le_one : a ≤ 1)
    (hc_nonneg : 0 ≤ c) (hd_nonneg : 0 ≤ d)
    (hk_pos : 0 < k) (hk_lt_slope : k < slope)
    (hsLow_pos : 0 < sLow) (hs : sLow < sHigh) :
    k * Real.sqrt (a * sHigh ^ 2 + c + d / sHigh ^ 2) - sHigh * slope <
      k * Real.sqrt (a * sLow ^ 2 + c + d / sLow ^ 2) - sLow * slope := by
  have hsHigh_pos : 0 < sHigh := lt_trans hsLow_pos hs
  have hanti :=
    sqrtQuadraticInvSubSelf_antitoneOn_Ioi
      ha_pos ha_le_one hc_nonneg hd_nonneg
      (show sLow ∈ Set.Ioi 0 by simpa)
      (show sHigh ∈ Set.Ioi 0 by simpa)
      hs.le
  have hdiff_le :
      Real.sqrt (a * sHigh ^ 2 + c + d / sHigh ^ 2) -
          Real.sqrt (a * sLow ^ 2 + c + d / sLow ^ 2) ≤
        sHigh - sLow := by
    linarith
  have hs_gap_pos : 0 < sHigh - sLow := sub_pos.mpr hs
  have hscaled_le :
      k * (Real.sqrt (a * sHigh ^ 2 + c + d / sHigh ^ 2) -
          Real.sqrt (a * sLow ^ 2 + c + d / sLow ^ 2)) ≤
        k * (sHigh - sLow) :=
    mul_le_mul_of_nonneg_left hdiff_le hk_pos.le
  have hscaled_lt :
      k * (sHigh - sLow) < slope * (sHigh - sLow) :=
    mul_lt_mul_of_pos_right hk_lt_slope hs_gap_pos
  nlinarith

end AppliedModelingLib
