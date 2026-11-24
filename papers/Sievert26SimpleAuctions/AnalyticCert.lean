import Sievert26SimpleAuctions.Abstract

/-! Real-analysis lemmas behind the integer certificate. -/
set_option linter.deprecated false
open Finset MeasureTheory

namespace Sievert26SimpleAuctions
namespace UB

/-! ### elementary bounds for `exp (-x)` -/

theorem exp_neg_le_quad (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hx
  rw [Real.exp_neg]
  have hp : 0 < 1 + x + x ^ 2 / 2 := by positivity
  have hq : 0 < Real.exp x := Real.exp_pos x
  rw [inv_le_iff_one_le_mul₀ hq]
  have h2 : 0 ≤ 1 - x + x ^ 2 / 2 := by nlinarith [sq_nonneg (1 - x)]
  nlinarith [mul_le_mul_of_nonneg_left h1 h2, sq_nonneg (x ^ 2)]

theorem cubic_le_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 ≤ Real.exp (-x) := by
  have hd : ∀ y, HasDerivAt (fun y => Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6))
      (-Real.exp (-y) - (-1 + y - y ^ 2 / 2)) y := by
    intro y
    have h1 : HasDerivAt (fun y => Real.exp (-y)) (Real.exp (-y) * (-1)) y :=
      ((hasDerivAt_id' y).fun_neg).exp
    have h2 : HasDerivAt (fun y : ℝ => 1 - y + y ^ 2 / 2 - y ^ 3 / 6)
        (-1 + (2 * y) / 2 - (3 * y ^ 2) / 6) y := by
      have a1 := (hasDerivAt_id' y).const_sub 1
      have a2 := ((hasDerivAt_pow 2 y).div_const 2)
      have a3 := ((hasDerivAt_pow 3 y).div_const 6)
      have a4 := (a1.fun_add a2).fun_sub a3
      convert a4 using 1
      norm_num
    convert h1.fun_sub h2 using 1
    ring
  have hmono : MonotoneOn (fun y => Real.exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hd y).deriv]
    have := exp_neg_le_quad y (le_of_lt hy)
    linarith
  have h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at h
  linarith

theorem psi_le_half (z : ℝ) (hz : 0 < z) : psi z ≤ z / 2 := by
  unfold psi
  have h := exp_neg_le_quad z hz.le
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hz]
  nlinarith

theorem psi_le_one (z : ℝ) (hz : 0 < z) : psi z ≤ 1 := by
  unfold psi
  have : Real.exp (-z) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have : 0 ≤ (1 - Real.exp (-z)) / z := div_nonneg (by linarith) hz.le
  linarith

theorem psi_eq (al v : ℝ) (hal : 0 < al) (hv : 0 < v) :
    psi (al / v) = 1 - v / al + v / al * Real.exp (-(al / v)) := by
  unfold psi; field_simp; ring

/-- `v ↦ ψ(α/v)` lies below its chord -/
theorem psi_chord (al a b v pa pb : ℝ) (hal : 0 < al) (ha : 0 < a) (hab : a < b)
    (hva : a ≤ v) (hvb : v ≤ b) (hpa : psi (al / a) ≤ pa) (hpb : psi (al / b) ≤ pb) :
    psi (al / v) ≤ ((b - v) * pa + (v - a) * pb) / (b - a) := by
  have hb : 0 < b := ha.trans hab
  have hv : 0 < v := lt_of_lt_of_le ha hva
  have hba : 0 < b - a := sub_pos.mpr hab
  rw [psi_eq al a hal ha] at hpa
  rw [psi_eq al b hal hb] at hpb
  rw [psi_eq al v hal hv]
  -- weights
  set p := (b - v) * a / ((b - a) * v) with hp
  set q := (v - a) * b / ((b - a) * v) with hq
  have hp0 : 0 ≤ p := div_nonneg (mul_nonneg (by linarith) ha.le) (by positivity)
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg (by linarith) hb.le) (by positivity)
  have hpq : p + q = 1 := by rw [hp, hq]; field_simp; ring
  have h := convexOn_exp.2 (Set.mem_univ (-(al / a))) (Set.mem_univ (-(al / b))) hp0 hq0 hpq
  simp only [smul_eq_mul] at h
  have e : p * -(al / a) + q * -(al / b) = -(al / v) := by
    rw [hp, hq]; field_simp; ring
  rw [e] at h
  have h2 := mul_le_mul_of_nonneg_left h (div_pos hv hal).le
  have e2 : v / al * (p * Real.exp (-(al / a)) + q * Real.exp (-(al / b))) =
      ((b - v) * (a / al * Real.exp (-(al / a))) + (v - a) * (b / al * Real.exp (-(al / b))))
        / (b - a) := by
    rw [hp, hq]; field_simp
  rw [e2] at h2
  have e3 : 1 - v / al = ((b - v) * (1 - a / al) + (v - a) * (1 - b / al)) / (b - a) := by
    field_simp; ring
  rw [e3]
  calc _ ≤ ((b - v) * (1 - a / al) + (v - a) * (1 - b / al)) / (b - a) +
        ((b - v) * (a / al * Real.exp (-(al / a))) + (v - a) * (b / al * Real.exp (-(al / b))))
        / (b - a) := by linarith
    _ = ((b - v) * (1 - a / al + a / al * Real.exp (-(al / a)))
        + (v - a) * (1 - b / al + b / al * Real.exp (-(al / b)))) / (b - a) := by ring
    _ ≤ _ := by
        refine div_le_div_of_nonneg_right ?_ hba.le
        exact add_le_add (mul_le_mul_of_nonneg_left hpa (by linarith))
          (mul_le_mul_of_nonneg_left hpb (by linarith))

section cell
variable {n : ℕ} (a s : Fin n → ℝ)

theorem Rf_ii (al x y : ℝ) (hal : 0 < al) (hx : 0 < x) (hxy : x ≤ y) :
    IntervalIntegrable (Rf a s al) volume x y := by
  refine ((Rf_contOn a s al hal).mono ?_).intervalIntegrable
  rw [Set.uIcc_of_le hxy]
  intro t ht
  exact lt_of_lt_of_le hx ht.1

/-- integral of the remainder over one cell -/
theorem cell_integral (al x y pa pb wa wb La Lb : ℝ) (hal : 0 < al) (hx : 0 < x) (hxy : x < y)
    (hpa : psi (al / x) ≤ pa) (hpb : psi (al / y) ≤ pb)
    (hw : ∀ v, x ≤ v → v ≤ y → ((y - v) * wa + (v - x) * wb) / (y - x) ≤ wf a s v)
    (hLa0 : 0 ≤ La) (hLb0 : 0 ≤ Lb) (hLa : pa - wa ≤ La) (hLb : pb - wb ≤ Lb) :
    ∫ v in x..y, Rf a s al v ≤
      (y - x) * (2 * La * y + La * x + Lb * y + 2 * Lb * x) / (6 * x * y) := by
  have hy : 0 < y := hx.trans hxy
  have hyx : 0 < y - x := sub_pos.mpr hxy
  set q : ℝ → ℝ := fun v =>
    ((y - v) * La + (v - x) * Lb) * ((y - v) / x + (v - x) / y) / (y - x) ^ 2 with hq
  have hpt : ∀ v ∈ Set.Icc x y, Rf a s al v ≤ q v := by
    intro v hv
    have hv0 : 0 < v := lt_of_lt_of_le hx hv.1
    have h1 := psi_chord al x y v pa pb hal hx hxy hv.1 hv.2 hpa hpb
    have h2 := hw v hv.1 hv.2
    have hyv : 0 ≤ y - v := by linarith [hv.2]
    have hvx : 0 ≤ v - x := by linarith [hv.1]
    have hl : psi (al / v) - wf a s v ≤ ((y - v) * La + (v - x) * Lb) / (y - x) := by
      have : ((y - v) * pa + (v - x) * pb) / (y - x) - ((y - v) * wa + (v - x) * wb) / (y - x) =
          ((y - v) * (pa - wa) + (v - x) * (pb - wb)) / (y - x) := by ring
      have h3 : ((y - v) * (pa - wa) + (v - x) * (pb - wb)) / (y - x) ≤
          ((y - v) * La + (v - x) * Lb) / (y - x) := by
        refine div_le_div_of_nonneg_right ?_ hyx.le
        exact add_le_add (mul_le_mul_of_nonneg_left hLa hyv) (mul_le_mul_of_nonneg_left hLb hvx)
      linarith
    have hl0 : 0 ≤ ((y - v) * La + (v - x) * Lb) / (y - x) :=
      div_nonneg (add_nonneg (mul_nonneg hyv hLa0) (mul_nonneg hvx hLb0)) hyx.le
    have hm : max (psi (al / v) - wf a s v) 0 ≤ ((y - v) * La + (v - x) * Lb) / (y - x) :=
      max_le hl hl0
    have hinv : 1 / v ≤ ((y - v) / x + (v - x) / y) / (y - x) := by
      rw [le_div_iff₀ hyx, div_mul_eq_mul_div, one_mul, div_le_iff₀ hv0]
      have : ((y - v) / x + (v - x) / y) * v - (y - x) = (y - x) * ((y - v) * (v - x)) / (x * y) := by
        field_simp; ring
      have h4 : 0 ≤ (y - x) * ((y - v) * (v - x)) / (x * y) := by positivity
      linarith
    unfold Rf
    calc max (psi (al / v) - wf a s v) 0 / v = max (psi (al / v) - wf a s v) 0 * (1 / v) := by ring
      _ ≤ ((y - v) * La + (v - x) * Lb) / (y - x) * (((y - v) / x + (v - x) / y) / (y - x)) :=
          mul_le_mul hm hinv (by positivity) hl0
      _ = q v := by rw [hq]; field_simp
  have hqc : Continuous q := by rw [hq]; fun_prop
  refine (intervalIntegral.integral_mono_on hxy.le (Rf_ii a s al x y hal hx hxy.le)
    (hqc.intervalIntegrable _ _) hpt).trans (le_of_eq ?_)
  -- explicit antiderivative
  set F : ℝ → ℝ := fun v => (-(La / x) * (y - v) ^ 3 / 3 + Lb / y * (v - x) ^ 3 / 3
    + (La / y + Lb / x) * (-(v ^ 3) / 3 + (x + y) * v ^ 2 / 2 - x * y * v)) / (y - x) ^ 2 with hF
  have hder : ∀ v ∈ Set.uIcc x y, HasDerivAt F (q v) v := by
    intro v _
    have d1 : HasDerivAt (fun v => (y - v) ^ 3) (3 * (y - v) ^ 2 * (-1)) v := by
      have := ((hasDerivAt_id' v).const_sub y).fun_pow 3
      simpa using this
    have d2 : HasDerivAt (fun v => (v - x) ^ 3) (3 * (v - x) ^ 2) v := by
      have := ((hasDerivAt_id' v).sub_const x).fun_pow 3
      simpa using this
    have d3 : HasDerivAt (fun v : ℝ => v ^ 3) (3 * v ^ 2) v := by
      simpa using hasDerivAt_pow 3 v
    have d4 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * v) v := by
      simpa using hasDerivAt_pow 2 v
    have d5 := ((d1.const_mul (-(La / x))).div_const 3).fun_add ((d2.const_mul (Lb / y)).div_const 3)
    have d6 := (((d3.fun_neg.div_const 3).fun_add ((d4.const_mul (x + y)).div_const 2)).fun_sub
      ((hasDerivAt_id' v).const_mul (x * y))).const_mul (La / y + Lb / x)
    have d7 := (d5.fun_add d6).div_const ((y - x) ^ 2)
    convert d7 using 1
    rw [hq]
    dsimp only
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hqc.intervalIntegrable _ _), hF]
  dsimp only
  field_simp
  ring

/-- `What t / t` is antitone -/
theorem avg_antitone (ha : ∀ i, 0 ≤ a i) (hs : ∀ i, 0 < s i) (t b : ℝ) (ht : 0 < t) (htb : t ≤ b) :
    What a s b / b ≤ What a s t / t := by
  have hb : 0 < b := lt_of_lt_of_le ht htb
  have h := What_secant a s ha hs t b hb ht.le htb
  rw [le_div_iff₀ ht]
  calc What a s b / b * t = t / b * What a s b := by ring
    _ ≤ _ := h

end cell

/-! ### the tangent property -/

theorem tan_cell_aux (y x z m E : ℝ) (hy : 0 < y) (hx : 0 < x) (hxz : x < z)
    (hE : ∀ u, 0 < u → E * (1 - y * (u - m)) ≤ Real.exp (-(y * u))) :
    y * ∫ u in x..z, Real.exp (-(y * u)) / u ≤
      (-(Real.exp (-(y * z)) / z) + E * ((1 + y * m) / z + y * Real.log z)) -
      (-(Real.exp (-(y * x)) / x) + E * ((1 + y * m) / x + y * Real.log x)) := by
  have hne : ∀ u ∈ Set.Icc x z, u ≠ 0 := fun u hu => (lt_of_lt_of_le hx hu.1).ne'
  have hne2 : ∀ u ∈ Set.Icc x z, u ^ 2 ≠ 0 := fun u hu => pow_ne_zero 2 (hne u hu)
  have c0 : ContinuousOn (fun u : ℝ => u) (Set.Icc x z) := continuousOn_id
  have c1 : ContinuousOn (fun u : ℝ => Real.exp (-(y * u))) (Set.Icc x z) :=
    Continuous.continuousOn (by fun_prop)
  have c2 : ContinuousOn (fun u : ℝ => u ^ 2) (Set.Icc x z) := Continuous.continuousOn (by fun_prop)
  have c3 : ContinuousOn (fun u : ℝ => E * (1 - y * (u - m))) (Set.Icc x z) :=
    Continuous.continuousOn (by fun_prop)
  have c4 : ContinuousOn (fun u : ℝ => Real.exp (-(y * u)) / u) (Set.Icc x z) := c1.div c0 hne
  have hcont : ContinuousOn (fun u : ℝ => y * (Real.exp (-(y * u)) / u)
      + Real.exp (-(y * u)) / u ^ 2 - E * (1 - y * (u - m)) / u ^ 2) (Set.Icc x z) :=
    ((continuousOn_const.mul c4).add (c1.div c2 hne2)).sub (c3.div c2 hne2)
  have hii : IntervalIntegrable (fun u : ℝ => y * (Real.exp (-(y * u)) / u)
      + Real.exp (-(y * u)) / u ^ 2 - E * (1 - y * (u - m)) / u ^ 2) volume x z := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxz.le]; exact hcont
  have hder : ∀ u ∈ Set.uIcc x z, HasDerivAt
      (fun u => -(Real.exp (-(y * u)) / u) + E * ((1 + y * m) / u + y * Real.log u))
      (y * (Real.exp (-(y * u)) / u)
      + Real.exp (-(y * u)) / u ^ 2 - E * (1 - y * (u - m)) / u ^ 2) u := by
    intro u hu
    rw [Set.uIcc_of_le hxz.le] at hu
    have hu0 : u ≠ 0 := hne u hu
    have d1 : HasDerivAt (fun u => Real.exp (-(y * u))) (Real.exp (-(y * u)) * (-(y * 1))) u :=
      (((hasDerivAt_id' u).const_mul y).fun_neg).exp
    have d2 := (d1.fun_div (hasDerivAt_id' u) hu0).fun_neg
    have d3 : HasDerivAt (fun u : ℝ => (1 + y * m) / u) (-(1 + y * m) / u ^ 2) u := by
      have h1 := (hasDerivAt_inv hu0).const_mul (1 + y * m)
      have e1 : (1 + y * m) * -(u ^ 2)⁻¹ = -(1 + y * m) / u ^ 2 := by ring
      rw [e1] at h1
      exact h1
    have d4 := (Real.hasDerivAt_log hu0).const_mul y
    have d5 := d2.fun_add ((d3.fun_add d4).const_mul E)
    have e : -((Real.exp (-(y * u)) * -(y * 1) * u - Real.exp (-(y * u)) * 1) / u ^ 2) +
        E * (-(1 + y * m) / u ^ 2 + y * u⁻¹) = y * (Real.exp (-(y * u)) / u)
      + Real.exp (-(y * u)) / u ^ 2 - E * (1 - y * (u - m)) / u ^ 2 := by
      field_simp
      ring
    rw [e] at d5
    exact d5
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hii
  rw [← hint, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hxz.le ?_ hii ?_
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hxz.le]
    exact continuousOn_const.mul c4
  · intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hx hu.1
    have h2 := div_le_div_of_nonneg_right (hE u hu0) (sq_nonneg u)
    linarith

/-- one cell of the exponential integral -/
theorem tan_cell (y x z : ℝ) (hy : 0 < y) (hx : 0 < x) (hxz : x < z) :
    y * ∫ u in x..z, Real.exp (-(y * u)) / u ≤
      Real.exp (-(y * x)) / x - Real.exp (-(y * z)) / z
        - (1 / x - 1 / z) * Real.exp (-(y * ((x + z) / 2))) := by
  have hz : 0 < z := hx.trans hxz
  have key := tan_cell_aux y x z ((x + z) / 2) (Real.exp (-(y * ((x + z) / 2)))) hy hx hxz (by
    intro u _
    have h1 := Real.add_one_le_exp (-(y * (u - (x + z) / 2)))
    have e : Real.exp (-(y * u)) =
        Real.exp (-(y * ((x + z) / 2))) * Real.exp (-(y * (u - (x + z) / 2))) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le)
  have hlog : Real.log z - Real.log x ≤ (x + z) / 2 * (1 / x - 1 / z) := by
    rw [← Real.log_div hz.ne' hx.ne']
    have hzx : 1 ≤ z / x := by rw [le_div_iff₀ hx]; linarith
    have hL0 : 0 ≤ Real.log (z / x) := Real.log_nonneg hzx
    have hs := Real.self_le_sinh_iff.mpr hL0
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (div_pos hz hx)] at hs
    refine hs.trans (le_of_eq ?_)
    field_simp; ring
  have h3 := mul_le_mul_of_nonneg_left hlog (mul_pos (Real.exp_pos (-(y * ((x + z) / 2)))) hy).le
  have e2 : ∀ A B E m lz lx : ℝ, (-A + E * ((1 + y * m) / z + y * lz)) -
      (-B + E * ((1 + y * m) / x + y * lx)) =
      B - A - (1 / x - 1 / z) * E + (E * y * (lz - lx) - E * y * (m * (1 / x - 1 / z))) := by
    intro A B E m lz lx; ring
  rw [e2] at key
  linarith

/-- monotonicity in the upper limit -/
theorem tan_tail (y x z : ℝ) (hy : 0 < y) (hx : 0 < x) (hxz : x ≤ z) :
    y * ∫ u in x..z, Real.exp (-(y * u)) / u ≤ Real.exp (-(y * x)) / x - Real.exp (-(y * z)) / z := by
  rcases eq_or_lt_of_le hxz with h | h
  · rw [h]; simp
  · refine (tan_cell y x z hy hx h).trans ?_
    have h1 : 0 ≤ 1 / x - 1 / z := by
      rw [sub_nonneg]; exact one_div_le_one_div_of_le hx hxz
    have := mul_nonneg h1 (Real.exp_pos (-(y * ((x + z) / 2)))).le
    linarith

end UB
end Sievert26SimpleAuctions
