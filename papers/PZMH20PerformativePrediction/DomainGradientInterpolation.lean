import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex
import PZMH20PerformativePrediction.LocalToGlobalLipschitz

/-!
# Gradient interpolation on convex parameter domains

The four-point argument below uses only feasible function values. It is the
quadratic-remainder argument of Wachsmuth and Wachsmuth, Lemma 2.1,
"A simple proof of the Baillon--Haddad theorem on open subsets of Hilbert
spaces", arXiv:2204.00282v1 (2022), https://arxiv.org/abs/2204.00282v1.
The Lean proof is an independent implementation using Mathlib inner-product
identities. Unlike a whole-space descent step, each test point's feasibility
is explicit.
-/

namespace PZMH20PerformativePrediction.DomainGradient

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Four feasible Taylor comparisons bound a gradient increment tested against
an arbitrary vector. The two auxiliary points are symmetric about the midpoint
of the original pair. -/
theorem gradient_increment_inner_le_of_quadratic_remainder
    (f : E → ℝ) (g : E → E) (domain : Set E) (L : ℝ)
    (hrem : ∀ x ∈ domain, ∀ y ∈ domain,
      |f y - f x - ⟪g x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2)
    (x y w : E) (hx : x ∈ domain) (hy : y ∈ domain)
    (hleft : x - (1 / 2 : ℝ) • (w - (y - x)) ∈ domain)
    (hright : y + (1 / 2 : ℝ) • (w - (y - x)) ∈ domain) :
    ⟪g y - g x, w⟫_ℝ ≤ L / 2 * (‖y - x‖ ^ 2 + ‖w‖ ^ 2) := by
  let d : E := (1 / 2 : ℝ) • (w - (y - x))
  have h₁ := (abs_le.mp (hrem y hy (x - d) hleft)).2
  have h₂ := (abs_le.mp (hrem x hx (y + d) hright)).2
  have h₃ := (abs_le.mp (hrem y hy (y + d) hright)).1
  have h₄ := (abs_le.mp (hrem x hx (x - d) hleft)).1
  have hxy : x - d - y = -(y - x + d) := by abel
  have hyx : y + d - x = y - x + d := by abel
  have hxx : x - d - x = -d := by abel
  have hyy : y + d - y = d := by abel
  rw [hxy, norm_neg, inner_neg_right] at h₁
  rw [hyx] at h₂
  rw [hyy] at h₃
  rw [hxx, norm_neg, inner_neg_right] at h₄
  have hfour : ⟪g y - g x, y - x + (2 : ℝ) • d⟫_ℝ ≤
      L * (‖y - x + d‖ ^ 2 + ‖d‖ ^ 2) := by
    simp only [inner_sub_left, inner_add_right, real_inner_smul_right] at *
    linarith
  have hw : y - x + (2 : ℝ) • d = w := by dsimp [d]; module
  have hplus : y - x + d = (1 / 2 : ℝ) • ((y - x) + w) := by
    dsimp [d]; module
  rw [hw, hplus] at hfour
  dsimp [d] at hfour
  rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    mul_pow, mul_pow, norm_add_sq_real (y - x) w, norm_sub_sq_real w (y - x),
    real_inner_comm w (y - x)] at hfour
  nlinarith

/-- A local Lipschitz estimate follows whenever the gradient-scaled test
vector makes the two midpoint perturbations feasible. -/
theorem norm_gradient_increment_le_of_feasible_test
    (f : E → ℝ) (g : E → E) (domain : Set E) {L : ℝ} (hL : 0 < L)
    (hrem : ∀ x ∈ domain, ∀ y ∈ domain,
      |f y - f x - ⟪g x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2)
    (x y : E) (hx : x ∈ domain) (hy : y ∈ domain)
    (hleft : x - (1 / 2 : ℝ) • ((L⁻¹ • (g y - g x)) - (y - x)) ∈ domain)
    (hright : y + (1 / 2 : ℝ) • ((L⁻¹ • (g y - g x)) - (y - x)) ∈ domain) :
    ‖g y - g x‖ ≤ L * ‖y - x‖ := by
  have h := gradient_increment_inner_le_of_quadratic_remainder
    f g domain L hrem x y (L⁻¹ • (g y - g x)) hx hy hleft hright
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL), mul_pow] at h
  have hmul := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2 * L)
  have hLne := ne_of_gt hL
  field_simp at hmul
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL.le (norm_nonneg _))).mp
  nlinarith only [hmul]

/-- The quadratic-remainder bound gives its sharp gradient Lipschitz constant
for pairs that lie one common positive radius inside the domain and are no
farther apart than that radius. No preliminary gradient-Lipschitz assumption
is required. -/
theorem norm_gradient_increment_le_on_inner_offset
    (f : E → ℝ) (g : E → E) (domain : Set E) {L ρ : ℝ}
    (hL : 0 < L) (hρ : 0 < ρ)
    (hrem : ∀ x ∈ domain, ∀ y ∈ domain,
      |f y - f x - ⟪g x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2)
    (x y : E)
    (hx : ∀ v : E, ‖v‖ ≤ ρ → x + v ∈ domain)
    (hy : ∀ v : E, ‖v‖ ≤ ρ → y + v ∈ domain)
    (hxy : ‖y - x‖ ≤ ρ) :
    ‖g y - g x‖ ≤ L * ‖y - x‖ := by
  have hxmem : x ∈ domain := by simpa using hx 0 (by simpa using hρ.le)
  have hymem : y ∈ domain := by simpa using hy 0 (by simpa using hρ.le)
  have htest (w : E) (hw : ‖w‖ ≤ ρ) :
      x - (1 / 2 : ℝ) • (w - (y - x)) ∈ domain ∧
      y + (1 / 2 : ℝ) • (w - (y - x)) ∈ domain := by
    have hd : ‖(1 / 2 : ℝ) • (w - (y - x))‖ ≤ ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      calc
        (1 / 2 : ℝ) * ‖w - (y - x)‖ ≤
            (1 / 2 : ℝ) * (‖w‖ + ‖y - x‖) := by gcongr; exact norm_sub_le _ _
        _ ≤ ρ := by linarith
    exact ⟨by
      simpa only [sub_eq_add_neg] using
        hx (-((1 / 2 : ℝ) • (w - (y - x)))) (by simpa only [norm_neg] using hd), hy _ hd⟩
  have hcoarse : ‖g y - g x‖ ≤ L * ρ := by
    by_cases hzero : ‖g y - g x‖ = 0
    · rw [hzero]; positivity
    have hpos : 0 < ‖g y - g x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    let w : E := (ρ / ‖g y - g x‖) • (g y - g x)
    have hw : ‖w‖ = ρ := by
      dsimp [w]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ hpos)]
      exact div_mul_cancel₀ ρ hzero
    have h := gradient_increment_inner_le_of_quadratic_remainder
      f g domain L hrem x y w hxmem hymem (htest w hw.le).1 (htest w hw.le).2
    rw [hw] at h
    have hinner : ⟪g y - g x, w⟫_ℝ = ρ * ‖g y - g x‖ := by
      dsimp [w]
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hinner] at h
    have hsquare : ‖y - x‖ ^ 2 ≤ ρ ^ 2 := by nlinarith [norm_nonneg (y - x)]
    nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hsquare)]
  have hscaled : ‖L⁻¹ • (g y - g x)‖ ≤ ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
    calc
      L⁻¹ * ‖g y - g x‖ ≤ L⁻¹ * (L * ρ) := by gcongr
      _ = ρ := by field_simp
  exact norm_gradient_increment_le_of_feasible_test f g domain hL hrem x y
    hxmem hymem (htest _ hscaled).1 (htest _ hscaled).2

/-- On an open convex domain, a two-sided quadratic Taylor remainder controls
the full gradient increment with the same constant. -/
theorem norm_gradient_increment_le_on_open
    (f : E → ℝ) (g : E → E) (domain : Set E) (hopen : IsOpen domain)
    (hconvex : Convex ℝ domain) {L : ℝ} (hL : 0 < L)
    (hrem : ∀ x ∈ domain, ∀ y ∈ domain,
      |f y - f x - ⟪g x, y - x⟫_ℝ| ≤ L / 2 * ‖y - x‖ ^ 2)
    (x y : E) (hx : x ∈ domain) (hy : y ∈ domain) :
    ‖g y - g x‖ ≤ L * ‖y - x‖ := by
  obtain ⟨ρ, hρ, hxρ, hyρ⟩ := exists_common_innerOffset_of_isOpen domain hopen hx hy
  exact norm_image_sub_le_of_uniform_local_on_convex g (innerOffset domain ρ)
    (convex_innerOffset domain ρ hconvex) hρ
    (fun first hfirst second hsecond hdist =>
      norm_gradient_increment_le_on_inner_offset f g domain hL hρ hrem
        second first hsecond hfirst hdist) y hyρ x hxρ

/-- Subtracting a quadratic shifts the Taylor remainder by exactly its
quadratic displacement term. -/
theorem quadratic_shift_remainder (f : E → ℝ) (g : E → E) (a : ℝ) (x y : E) :
    (f y - a / 2 * ‖y‖ ^ 2) - (f x - a / 2 * ‖x‖ ^ 2) -
        ⟪g x - a • x, y - x⟫_ℝ =
      f y - f x - ⟪g x, y - x⟫_ℝ - a / 2 * ‖y - x‖ ^ 2 := by
  rw [inner_sub_left, real_inner_smul_left, inner_sub_right x,
    real_inner_self_eq_norm_sq, norm_sub_sq_real, real_inner_comm y x]
  ring

/-- Strong convexity and a smooth upper model center the Taylor remainder
between opposite quadratic bounds. -/
theorem abs_quadratic_shift_remainder_le
    (f : E → ℝ) (g : E → E) (domain : Set E) (β γ : ℝ)
    (hlower : ∀ x ∈ domain, ∀ y ∈ domain,
      f x + ⟪g x, y - x⟫_ℝ + γ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hupper : ∀ x ∈ domain, ∀ y ∈ domain,
      f y ≤ f x + ⟪g x, y - x⟫_ℝ + β / 2 * ‖y - x‖ ^ 2)
    (x y : E) (hx : x ∈ domain) (hy : y ∈ domain) :
    |(f y - ((β + γ) / 2) / 2 * ‖y‖ ^ 2) -
        (f x - ((β + γ) / 2) / 2 * ‖x‖ ^ 2) -
        ⟪g x - ((β + γ) / 2) • x, y - x⟫_ℝ| ≤
      ((β - γ) / 2) / 2 * ‖y - x‖ ^ 2 := by
  rw [quadratic_shift_remainder]
  exact abs_le.mpr ⟨by linarith [hlower x hx y hy], by linarith [hupper x hx y hy]⟩

/-- Sharp smooth--strong gradient interpolation on an open convex domain.
The argument needs only the two quadratic models, not a Hessian or any
off-domain extension of the loss. -/
theorem gradient_interpolation_on_open_of_quadratic_models
    (f : E → ℝ) (g : E → E) (domain : Set E) (hopen : IsOpen domain)
    (hconvex : Convex ℝ domain) {β γ : ℝ} (hgap : γ < β)
    (hlower : ∀ x ∈ domain, ∀ y ∈ domain,
      f x + ⟪g x, y - x⟫_ℝ + γ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hupper : ∀ x ∈ domain, ∀ y ∈ domain,
      f y ≤ f x + ⟪g x, y - x⟫_ℝ + β / 2 * ‖y - x‖ ^ 2)
    (x y : E) (hx : x ∈ domain) (hy : y ∈ domain) :
    β * γ * ‖y - x‖ ^ 2 + ‖g y - g x‖ ^ 2 ≤
      (β + γ) * ⟪g y - g x, y - x⟫_ℝ := by
  have hbound := norm_gradient_increment_le_on_open
    (fun v => f v - ((β + γ) / 2) / 2 * ‖v‖ ^ 2)
    (fun v => g v - ((β + γ) / 2) • v) domain hopen hconvex
    (by linarith : 0 < (β - γ) / 2)
    (fun u hu v hv => abs_quadratic_shift_remainder_le f g domain β γ
      hlower hupper u v hu hv) x y hx hy
  have hsub : (g y - ((β + γ) / 2) • y) - (g x - ((β + γ) / 2) • x) =
      (g y - g x) - ((β + γ) / 2) • (y - x) := by module
  rw [hsub] at hbound
  have hnonneg : 0 ≤ ((β - γ) / 2) * ‖y - x‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  have hsquare := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr hbound
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs] at hsquare
  nlinarith only [hsquare]

/-- Continuity extends the open-domain interpolation inequality to the
boundary of a closed convex set with nonempty interior. Applying this theorem
in the affine direction space also treats lower-dimensional feasible sets. -/
theorem gradient_interpolation_on_closed_of_quadratic_models
    (f : E → ℝ) (g : E → E) (domain : Set E) (hclosed : IsClosed domain)
    (hconvex : Convex ℝ domain) (hinterior : (interior domain).Nonempty)
    (hg : ContinuousOn g domain) {β γ : ℝ} (hgap : γ < β)
    (hlower : ∀ x ∈ domain, ∀ y ∈ domain,
      f x + ⟪g x, y - x⟫_ℝ + γ / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hupper : ∀ x ∈ domain, ∀ y ∈ domain,
      f y ≤ f x + ⟪g x, y - x⟫_ℝ + β / 2 * ‖y - x‖ ^ 2)
    (x y : E) (hx : x ∈ domain) (hy : y ∈ domain) :
    β * γ * ‖y - x‖ ^ 2 + ‖g y - g x‖ ^ 2 ≤
      (β + γ) * ⟪g y - g x, y - x⟫_ℝ := by
  have hclosure : closure (interior domain) = domain := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior, hclosed.closure_eq]
  have hprodClosure : closure (interior domain ×ˢ interior domain) = domain ×ˢ domain := by
    rw [closure_prod_eq, hclosure]
  have hgfirst : ContinuousOn (fun p : E × E => g p.1) (domain ×ˢ domain) :=
    hg.comp continuousOn_fst (fun _ hp => hp.1)
  have hgsecond : ContinuousOn (fun p : E × E => g p.2) (domain ×ˢ domain) :=
    hg.comp continuousOn_snd (fun _ hp => hp.2)
  have hdisplacement : ContinuousOn (fun p : E × E => p.2 - p.1) (domain ×ˢ domain) :=
    continuousOn_snd.sub continuousOn_fst
  apply le_on_closure
    (f := fun p : E × E => β * γ * ‖p.2 - p.1‖ ^ 2 + ‖g p.2 - g p.1‖ ^ 2)
    (g := fun p : E × E => (β + γ) * ⟪g p.2 - g p.1, p.2 - p.1⟫_ℝ)
    (s := interior domain ×ˢ interior domain) ?_ ?_ ?_
    (show (x, y) ∈ closure (interior domain ×ˢ interior domain) by
      rw [hprodClosure]; exact ⟨hx, hy⟩)
  · intro p hp
    exact gradient_interpolation_on_open_of_quadratic_models f g (interior domain)
      isOpen_interior hconvex.interior hgap
      (fun u hu v hv => hlower u (interior_subset hu) v (interior_subset hv))
      (fun u hu v hv => hupper u (interior_subset hu) v (interior_subset hv))
      p.1 p.2 hp.1 hp.2
  · rw [hprodClosure]
    exact (continuousOn_const.mul (hdisplacement.norm.pow 2)).add
      ((hgsecond.sub hgfirst).norm.pow 2)
  · rw [hprodClosure]
    exact continuousOn_const.mul ((hgsecond.sub hgfirst).inner hdisplacement)

end PZMH20PerformativePrediction.DomainGradient
