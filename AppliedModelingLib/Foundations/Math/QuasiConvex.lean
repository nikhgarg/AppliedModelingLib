import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

namespace AppliedModelingLib

open Set

/-- Strict quasi-convexity on positive real arguments. -/
def StrictQuasiConvexOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    f (θ * x + (1 - θ) * y) < max (f x) (f y)

/-- Strict quasi-concavity on positive real arguments. -/
def StrictQuasiConcaveOnPositive (f : ℝ → ℝ) : Prop :=
  ∀ x y θ : ℝ, 0 < x → 0 < y → x ≠ y → 0 < θ → θ < 1 →
    min (f x) (f y) < f (θ * x + (1 - θ) * y)

/--
A reusable single-crossing derivative criterion for strict quasi-convexity on
positive reals.  The proxy `g` need not be the derivative itself; it only has
to have the same weak sign as the derivative and be strictly increasing.
-/
theorem strictQuasiConvexOnPositive_of_deriv_proxy_strictMono
    {f g : ℝ → ℝ}
    (hcont :
      ∀ a b : ℝ, 0 < a → a < b → ContinuousOn f (Icc a b))
    (hdiff :
      ∀ t : ℝ, 0 < t → DifferentiableAt ℝ f t)
    (hg : StrictMonoOn g (Ioi 0))
    (hderiv_nonneg_to_proxy_nonneg :
      ∀ t : ℝ, 0 < t → 0 ≤ deriv f t → 0 ≤ g t)
    (hderiv_nonpos_to_proxy_nonpos :
      ∀ t : ℝ, 0 < t → deriv f t ≤ 0 → g t ≤ 0) :
    StrictQuasiConvexOnPositive f := by
  have ordered :
      ∀ a b θ : ℝ, 0 < a → 0 < b → a < b → 0 < θ → θ < 1 →
        f (θ * a + (1 - θ) * b) < max (f a) (f b) := by
    intro a b θ ha _hb hab hθ_pos hθ_lt_one
    let z : ℝ := θ * a + (1 - θ) * b
    have hone_minus_pos : 0 < 1 - θ := by linarith
    have ha_lt_z : a < z := by
      dsimp [z]
      nlinarith [mul_pos hone_minus_pos (sub_pos.mpr hab)]
    have hz_lt_b : z < b := by
      dsimp [z]
      nlinarith [mul_pos hθ_pos (sub_pos.mpr hab)]
    have hz_pos : 0 < z := lt_trans ha ha_lt_z
    by_contra hnot
    have hmax_le : max (f a) (f b) ≤ f z := le_of_not_gt hnot
    have hfa_le_fz : f a ≤ f z := (le_max_left _ _).trans hmax_le
    have hfb_le_fz : f b ≤ f z := (le_max_right _ _).trans hmax_le
    have hdiff_left : DifferentiableOn ℝ f (Ioo a z) := by
      intro t ht
      exact (hdiff t (lt_trans ha ht.1)).differentiableWithinAt
    rcases exists_deriv_eq_slope f ha_lt_z
        (hcont a z ha ha_lt_z) hdiff_left with
      ⟨c, hc_mem, hc_deriv⟩
    have hslope_left_nonneg : 0 ≤ (f z - f a) / (z - a) := by
      exact div_nonneg (sub_nonneg.mpr hfa_le_fz)
        (le_of_lt (sub_pos.mpr ha_lt_z))
    have hc_deriv_nonneg : 0 ≤ deriv f c := by
      rw [hc_deriv]
      exact hslope_left_nonneg
    have hc_pos : 0 < c := lt_trans ha hc_mem.1
    have hc_proxy_nonneg : 0 ≤ g c :=
      hderiv_nonneg_to_proxy_nonneg c hc_pos hc_deriv_nonneg
    have hdiff_right : DifferentiableOn ℝ f (Ioo z b) := by
      intro t ht
      exact (hdiff t (lt_trans hz_pos ht.1)).differentiableWithinAt
    rcases exists_deriv_eq_slope f hz_lt_b
        (hcont z b hz_pos hz_lt_b) hdiff_right with
      ⟨d, hd_mem, hd_deriv⟩
    have hslope_right_nonpos : (f b - f z) / (b - z) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hfb_le_fz)
        (le_of_lt (sub_pos.mpr hz_lt_b))
    have hd_deriv_nonpos : deriv f d ≤ 0 := by
      rw [hd_deriv]
      exact hslope_right_nonpos
    have hd_pos : 0 < d := lt_trans hz_pos hd_mem.1
    have hd_proxy_nonpos : g d ≤ 0 :=
      hderiv_nonpos_to_proxy_nonpos d hd_pos hd_deriv_nonpos
    have hcd : c < d := lt_trans hc_mem.2 hd_mem.1
    have hproxy_lt : g c < g d := hg hc_pos hd_pos hcd
    linarith
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  by_cases hxy_lt : x < y
  · exact ordered x y θ hx hy hxy_lt hθ_pos hθ_lt_one
  · have hyx_lt : y < x :=
      lt_of_le_of_ne (le_of_not_gt hxy_lt) (Ne.symm hxy)
    have hone_minus_pos : 0 < 1 - θ := by linarith
    have hone_minus_lt_one : 1 - θ < 1 := by linarith
    have hswap :=
      ordered y x (1 - θ) hy hx hyx_lt hone_minus_pos hone_minus_lt_one
    simpa [mul_comm, add_comm, add_left_comm, max_comm] using hswap

/-- Negating a strictly quasi-convex function gives a strictly quasi-concave function. -/
theorem strictQuasiConcaveOnPositive_of_neg_strictQuasiConvex
    {f : ℝ → ℝ}
    (hf : StrictQuasiConvexOnPositive (fun x => -f x)) :
    StrictQuasiConcaveOnPositive f := by
  intro x y θ hx hy hxy hθ_pos hθ_lt_one
  have h := hf x y θ hx hy hxy hθ_pos hθ_lt_one
  rw [max_neg_neg] at h
  linarith

/--
Pointwise form of strict quasi-convexity: a positive point strictly between two
positive endpoints has value below the larger endpoint value.
-/
theorem StrictQuasiConvexOnPositive.lt_of_between
    {f : ℝ → ℝ} (hf : StrictQuasiConvexOnPositive f)
    {x z y : ℝ} (hx : 0 < x) (hxz : x < z) (hzy : z < y) :
    f z < max (f x) (f y) := by
  let θ : ℝ := (y - z) / (y - x)
  have hy_pos : 0 < y := lt_trans (lt_trans hx hxz) hzy
  have hxy : x ≠ y := ne_of_lt (lt_trans hxz hzy)
  have hden_pos : 0 < y - x := by linarith
  have hθ_pos : 0 < θ := by
    exact div_pos (sub_pos.mpr hzy) hden_pos
  have hθ_lt_one : θ < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hz_eq : θ * x + (1 - θ) * y = z := by
    dsimp [θ]
    field_simp [ne_of_gt hden_pos]
    ring_nf
  simpa [hz_eq] using hf x y θ hx hy_pos hxy hθ_pos hθ_lt_one

/--
Pointwise form of strict quasi-concavity: a positive point strictly between two
positive endpoints has value above the smaller endpoint value.
-/
theorem StrictQuasiConcaveOnPositive.lt_between
    {f : ℝ → ℝ} (hf : StrictQuasiConcaveOnPositive f)
    {x z y : ℝ} (hx : 0 < x) (hxz : x < z) (hzy : z < y) :
    min (f x) (f y) < f z := by
  let θ : ℝ := (y - z) / (y - x)
  have hy_pos : 0 < y := lt_trans (lt_trans hx hxz) hzy
  have hxy : x ≠ y := ne_of_lt (lt_trans hxz hzy)
  have hden_pos : 0 < y - x := by linarith
  have hθ_pos : 0 < θ := by
    exact div_pos (sub_pos.mpr hzy) hden_pos
  have hθ_lt_one : θ < 1 := by
    rw [div_lt_one hden_pos]
    linarith
  have hz_eq : θ * x + (1 - θ) * y = z := by
    dsimp [θ]
    field_simp [ne_of_gt hden_pos]
    ring_nf
  simpa [hz_eq] using hf x y θ hx hy_pos hxy hθ_pos hθ_lt_one

end AppliedModelingLib
