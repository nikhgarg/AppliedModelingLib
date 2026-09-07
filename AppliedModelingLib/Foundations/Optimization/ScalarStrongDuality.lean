/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the repository LICENSE.
Authors: Daniel Lyng

This file adapts the scalar-duality development from
https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Optimization/Constrained/Duality.lean
to AppliedModelingLib's Lean/Mathlib 4.30 environment.  The upstream revision is
Apache-2.0.  The adaptation changes module names, makes the scalar Slater
predicate local, and will retain only the reusable scalar strong-duality
surface needed here; no upstream repository is imported as a dependency.
-/

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.ContinuousOn

/-!
# Strong duality for scalar-constrained convex programs

For a compact convex feasible set, a continuous concave objective, and one
continuous convex inequality constraint, a strict Slater point gives equality
between the primal supremum and the nonnegative-multiplier Lagrange dual
infimum.  The theorem is generic in the ambient real topological module and
is intended to support finite linear programs and transport models as well as
economic optimization problems.

## External formalization credit

This is a Lean/Mathlib 4.30 compatibility adaptation of Daniel Lyng's
Apache-2.0 Econlib source at
[`Econlib/Optimization/Constrained/Duality.lean`](https://github.com/danlyng/Econlib/blob/003655ccf010cdf44c4f67d6675167b54ce0e9df/Econlib/Optimization/Constrained/Duality.lean),
revision
[`003655ccf010cdf44c4f67d6675167b54ce0e9df`](https://github.com/danlyng/Econlib/commit/003655ccf010cdf44c4f67d6675167b54ce0e9df).
Econlib is Apache-2.0 licensed.  The upstream code was inspected without
`sorry` or additional axioms; the original copyright notice and this
modification notice are retained as required by that license.
-/

@[expose] public section

open Pointwise Set

namespace AppliedModelingLib
namespace Optimization

section ScalarDuality

variable {E : Type*} [TopologicalSpace E]

/-- Feasible points in `X` satisfying the scalar inequality `g x ≤ 0`. -/
def scalarFeasible (X : Set E) (g : E → ℝ) : Set E :=
  {x ∈ X | g x ≤ 0}

/-- A scalar Lagrangian with nonnegative multiplier convention. -/
noncomputable def scalarLagrangian (f g : E → ℝ) (x : E) (multiplier : ℝ) : ℝ :=
  f x - multiplier * g x

/-- Primal supremum of the objective over scalar-feasible points. -/
noncomputable def scalarPrimalValue (X : Set E) (f g : E → ℝ) : ℝ :=
  sSup (f '' scalarFeasible X g)

/-- Dual objective at a fixed scalar multiplier. -/
noncomputable def scalarDualObjective (X : Set E) (f g : E → ℝ)
    (multiplier : ℝ) : ℝ :=
  sSup ((fun x => scalarLagrangian f g x multiplier) '' X)

/-- Infimum dual value over nonnegative scalar multipliers. -/
noncomputable def scalarDualValue (X : Set E) (f g : E → ℝ) : ℝ :=
  sInf (scalarDualObjective X f g '' Ici 0)

/-- Scalar Slater data: convexity and a strictly feasible point. -/
structure IsScalarSlater [AddCommGroup E] [Module ℝ E]
    (X : Set E) (g : E → ℝ) : Prop where
  convex_X : Convex ℝ X
  convex_g : ConvexOn ℝ X g
  strict_feasible : ∃ x ∈ X, g x < 0

/-- The Lagrangian image is bounded above on a compact continuous domain. -/
private lemma scalarLagrangian_image_bddAbove
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    (multiplier : ℝ) :
    BddAbove ((fun x => scalarLagrangian f g x multiplier) '' X) := by
  have hcont : ContinuousOn (fun x => scalarLagrangian f g x multiplier) X := by
    unfold scalarLagrangian
    exact hf_cont.sub ((continuousOn_const (c := multiplier)).mul hg_cont)
  exact (hcompact.image_of_continuousOn hcont).bddAbove

/-- A feasible point is below every nonnegative-multiplier dual objective. -/
private lemma scalarFeasible_le_scalarDualObjective
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    {multiplier : ℝ} (hmultiplier : 0 ≤ multiplier)
    {x : E} (hx : x ∈ scalarFeasible X g) :
    f x ≤ scalarDualObjective X f g multiplier := by
  obtain ⟨hxX, hgx⟩ := hx
  have hfx_le : f x ≤ scalarLagrangian f g x multiplier := by
    unfold scalarLagrangian
    have : multiplier * g x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmultiplier hgx
    linarith
  have hmem : scalarLagrangian f g x multiplier ∈
      (fun x => scalarLagrangian f g x multiplier) '' X :=
    ⟨x, hxX, rfl⟩
  have hbdd := scalarLagrangian_image_bddAbove hcompact hf_cont hg_cont multiplier
  exact hfx_le.trans (le_csSup hbdd hmem)

/-- Weak duality for a compact continuous scalar-constrained maximization problem. -/
theorem scalarPrimalValue_le_scalarDualValue
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X)
    (hfeas_ne : (scalarFeasible X g).Nonempty) :
    scalarPrimalValue X f g ≤ scalarDualValue X f g := by
  have hfeas_img_ne : (f '' scalarFeasible X g).Nonempty := hfeas_ne.image f
  have hdual_img_ne : (scalarDualObjective X f g '' Ici 0).Nonempty :=
    ⟨scalarDualObjective X f g 0, 0, self_mem_Ici, rfl⟩
  refine le_csInf hdual_img_ne ?_
  rintro y ⟨multiplier, hmultiplier, rfl⟩
  refine csSup_le hfeas_img_ne ?_
  rintro value ⟨x, hx, rfl⟩
  exact scalarFeasible_le_scalarDualObjective hcompact hf_cont hg_cont hmultiplier hx

omit [TopologicalSpace E] in
/-- A point of `X` gives a lower bound for its fixed-multiplier dual objective. -/
lemma scalarLagrangian_le_scalarDualObjective
    {X : Set E} {f g : E → ℝ} {multiplier : ℝ}
    (hbdd : BddAbove ((fun x => scalarLagrangian f g x multiplier) '' X))
    {x : E} (hx : x ∈ X) :
    scalarLagrangian f g x multiplier ≤ scalarDualObjective X f g multiplier :=
  le_csSup hbdd ⟨x, hx, rfl⟩

omit [TopologicalSpace E] in
/-- A uniform Lagrangian upper bound bounds its fixed-multiplier dual objective. -/
lemma scalarDualObjective_le
    {X : Set E} {f g : E → ℝ} {multiplier bound : ℝ}
    (hX_ne : X.Nonempty)
    (hbound : ∀ x ∈ X, scalarLagrangian f g x multiplier ≤ bound) :
    scalarDualObjective X f g multiplier ≤ bound :=
  csSup_le (hX_ne.image _) (by
    rintro value ⟨x, hx, rfl⟩
    exact hbound x hx)

omit [TopologicalSpace E] in
/-- Any nonnegative multiplier upper-bounds the scalar dual infimum. -/
lemma scalarDualValue_le
    {X : Set E} {f g : E → ℝ}
    (hbdd : BddBelow (scalarDualObjective X f g '' Ici 0))
    {multiplier : ℝ} (hmultiplier : 0 ≤ multiplier) :
    scalarDualValue X f g ≤ scalarDualObjective X f g multiplier :=
  csInf_le hbdd ⟨multiplier, hmultiplier, rfl⟩

omit [TopologicalSpace E] in
/-- A common lower bound for all nonnegative multipliers lower-bounds the dual value. -/
lemma le_scalarDualValue
    {X : Set E} {f g : E → ℝ} {bound : ℝ}
    (hbound : ∀ multiplier, 0 ≤ multiplier →
      bound ≤ scalarDualObjective X f g multiplier) :
    bound ≤ scalarDualValue X f g :=
  le_csInf ⟨scalarDualObjective X f g 0, 0, self_mem_Ici, rfl⟩
    (by
      rintro value ⟨multiplier, hmultiplier, rfl⟩
      exact hbound multiplier hmultiplier)

end ScalarDuality
end Optimization
end AppliedModelingLib

namespace AppliedModelingLib
namespace Optimization

section ScalarStrongDuality

variable {E : Type*} [TopologicalSpace E]

/-- The achievable hypograph for one scalar inequality-constrained program. -/
private def scalarAchievableSet (X : Set E) (f g : E → ℝ) : Set (ℝ × ℝ) :=
  {point | ∃ x ∈ X, g x ≤ point.1 ∧ point.2 ≤ f x}

omit [TopologicalSpace E] in
private lemma scalarAchievableSet_convex [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f g : E → ℝ}
    (hX_convex : Convex ℝ X)
    (hf_concave : ConcaveOn ℝ X f)
    (hg_convex : ConvexOn ℝ X g) :
    Convex ℝ (scalarAchievableSet X f g) := by
  rintro ⟨u₁, v₁⟩ ⟨x₁, hx₁X, hgu₁, hvf₁⟩ ⟨u₂, v₂⟩ ⟨x₂, hx₂X, hgu₂, hvf₂⟩
  intro a b ha hb hab
  simp only at hgu₁ hvf₁ hgu₂ hvf₂
  refine ⟨a • x₁ + b • x₂, hX_convex hx₁X hx₂X ha hb hab, ?_, ?_⟩
  · have hconv := hg_convex.2 hx₁X hx₂X ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have ha1 : a • g x₁ ≤ a * u₁ := by
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hgu₁ ha
    have hb1 : b • g x₂ ≤ b * u₂ := by
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hgu₂ hb
    linarith
  · have hconv := hf_concave.2 hx₁X hx₂X ha hb hab
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    have ha1 : a * v₁ ≤ a • f x₁ := by
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hvf₁ ha
    have hb1 : b * v₂ ≤ b • f x₂ := by
      rw [smul_eq_mul]
      exact mul_le_mul_of_nonneg_left hvf₂ hb
    linarith

omit [TopologicalSpace E] in
private lemma scalarAchievableSet_eq_image_add
    (X : Set E) (f g : E → ℝ) :
    scalarAchievableSet X f g =
      (fun x => (g x, f x)) '' X + (Ici (0 : ℝ)) ×ˢ (Iic (0 : ℝ)) := by
  ext ⟨u, v⟩
  constructor
  · rintro ⟨x, hxX, hgu, hvf⟩
    refine ⟨(g x, f x), ⟨x, hxX, rfl⟩, (u - g x, v - f x), ?_, ?_⟩
    · exact ⟨sub_nonneg.mpr hgu, sub_nonpos.mpr hvf⟩
    · simp [add_sub_cancel]
  · rintro ⟨⟨u₀, v₀⟩, ⟨x, hxX, hxeq⟩, ⟨a, b⟩, hab_mem, hsum⟩
    obtain ⟨ha, hb⟩ := hab_mem
    simp only at ha hb
    rw [Prod.mk.injEq] at hxeq
    obtain ⟨hgx, hfx⟩ := hxeq
    have hu : u₀ + a = u := (Prod.mk.injEq _ _ _ _).mp hsum |>.1
    have hv : v₀ + b = v := (Prod.mk.injEq _ _ _ _).mp hsum |>.2
    refine ⟨x, hxX, ?_, ?_⟩
    · rw [← hu, ← hgx]
      linarith [mem_Ici.mp ha]
    · rw [← hv, ← hfx]
      linarith [mem_Iic.mp hb]

private lemma scalarAchievableSet_isClosed
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hg_cont : ContinuousOn g X) :
    IsClosed (scalarAchievableSet X f g) := by
  rw [scalarAchievableSet_eq_image_add]
  have himg_compact : IsCompact ((fun x => (g x, f x)) '' X) :=
    hcompact.image_of_continuousOn (hg_cont.prodMk hf_cont)
  have hcone_closed : IsClosed ((Ici (0 : ℝ)) ×ˢ (Iic (0 : ℝ))) :=
    isClosed_Ici.prod isClosed_Iic
  exact hcone_closed.add_left_of_isCompact himg_compact

omit [TopologicalSpace E] in
private lemma scalar_image_mem_achievableSet
    {X : Set E} {f g : E → ℝ} {x : E} (hx : x ∈ X) :
    (g x, f x) ∈ scalarAchievableSet X f g :=
  ⟨x, hx, le_rfl, le_rfl⟩

private lemma scalar_not_mem_achievableSet_of_gt_primalValue
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (_hfeas_ne : (scalarFeasible X g).Nonempty)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (0, scalarPrimalValue X f g + epsilon) ∉ scalarAchievableSet X f g := by
  rintro ⟨x, hxX, hgx, hVepsilon_le_fx⟩
  have hx_feas : x ∈ scalarFeasible X g := ⟨hxX, hgx⟩
  have hmem : f x ∈ f '' scalarFeasible X g := ⟨x, hx_feas, rfl⟩
  have hsub : f '' scalarFeasible X g ⊆ f '' X := Set.image_mono (fun _ h => h.1)
  have hbdd_X : BddAbove (f '' X) := (hcompact.image_of_continuousOn hf_cont).bddAbove
  have hbdd : BddAbove (f '' scalarFeasible X g) := hbdd_X.mono hsub
  have hle : f x ≤ scalarPrimalValue X f g := le_csSup hbdd hmem
  linarith

private lemma scalar_prod_apply_eq (linear : (ℝ × ℝ) →L[ℝ] ℝ) (first second : ℝ) :
    linear (first, second) = first * linear (1, 0) + second * linear (0, 1) := by
  have hsplit : (first, second) = first • ((1, 0) : ℝ × ℝ) + second • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  rw [hsplit, linear.map_add, linear.map_smul, linear.map_smul]
  simp [smul_eq_mul]

omit [TopologicalSpace E] in
private lemma scalarAchievableSet_comprehensive
    {X : Set E} {f g : E → ℝ} {first first' second second' : ℝ}
    (hpoint : (first, second) ∈ scalarAchievableSet X f g)
    (hfirst : first ≤ first') (hsecond : second' ≤ second) :
    (first', second') ∈ scalarAchievableSet X f g := by
  obtain ⟨x, hxX, hgfirst, hsecondf⟩ := hpoint
  exact ⟨x, hxX, hgfirst.trans hfirst, hsecond.trans hsecondf⟩

end ScalarStrongDuality
end Optimization
end AppliedModelingLib

namespace AppliedModelingLib
namespace Optimization

section ScalarStrongDualityTheorem

variable {E : Type*} [TopologicalSpace E]

/--
Strong duality for a compact scalar-constrained convex maximization problem.
The conclusion identifies the primal supremum with the infimum of the
nonnegative-multiplier scalar Lagrange dual.
-/
theorem scalarStrongDuality_of_isScalarSlater [AddCommGroup E] [Module ℝ E]
    {X : Set E} {f g : E → ℝ}
    (hcompact : IsCompact X)
    (hf_cont : ContinuousOn f X)
    (hf_concave : ConcaveOn ℝ X f)
    (hg_cont : ContinuousOn g X)
    (hg_convex : ConvexOn ℝ X g)
    (hslater : IsScalarSlater X g) :
    scalarPrimalValue X f g = scalarDualValue X f g := by
  obtain ⟨x₀, hx₀X, hg_x₀⟩ := hslater.strict_feasible
  have hfeas_ne : (scalarFeasible X g).Nonempty :=
    ⟨x₀, hx₀X, hg_x₀.le⟩
  have hweak := scalarPrimalValue_le_scalarDualValue hcompact hf_cont hg_cont hfeas_ne
  refine le_antisymm hweak ?_
  set primal := scalarPrimalValue X f g with hprimal_def
  by_contra hlt
  push Not at hlt
  set epsilon := (scalarDualValue X f g - primal) / 2 with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by
    have : 0 < scalarDualValue X f g - primal := sub_pos.mpr hlt
    positivity
  have hprimal_epsilon_lt : primal + epsilon < scalarDualValue X f g := by
    rw [hepsilon_def]
    linarith
  have hachievable_convex :=
    scalarAchievableSet_convex hslater.convex_X hf_concave hg_convex
  have hachievable_closed := scalarAchievableSet_isClosed hcompact hf_cont hg_cont
  have hachievable_excluded :=
    scalar_not_mem_achievableSet_of_gt_primalValue hcompact hf_cont hfeas_ne hepsilon_pos
  obtain ⟨linear, constant, hlinear_point, hlinear_set⟩ :=
    geometric_hahn_banach_point_closed hachievable_convex hachievable_closed hachievable_excluded
  set firstCoefficient := linear (1, 0) with hfirstCoefficient_def
  set secondCoefficient := linear (0, 1) with hsecondCoefficient_def
  have hlinear_decomp : ∀ first second : ℝ,
      linear (first, second) = first * firstCoefficient + second * secondCoefficient :=
    fun first second => scalar_prod_apply_eq linear first second
  have hseparate_point : (primal + epsilon) * secondCoefficient < constant := by
    have h := hlinear_point
    rw [hlinear_decomp] at h
    linarith
  have hseparate_set : ∀ point ∈ scalarAchievableSet X f g,
      constant < point.1 * firstCoefficient + point.2 * secondCoefficient := by
    intro point hpoint
    have h := hlinear_set point hpoint
    rw [hlinear_decomp] at h
    linarith
  have hx₀_mem : (g x₀, f x₀) ∈ scalarAchievableSet X f g :=
    scalar_image_mem_achievableSet hx₀X
  have hfirst_nonneg : 0 ≤ firstCoefficient := by
    by_contra hfirst_neg
    push Not at hfirst_neg
    have hfirst_ne : firstCoefficient ≠ 0 := ne_of_lt hfirst_neg
    set offset : ℝ := constant - firstCoefficient * g x₀ - f x₀ * secondCoefficient
      with hoffset_def
    set shift : ℝ := (|offset| + 1) * (-1 / firstCoefficient) with hshift_def
    have hinv_pos : 0 < -1 / firstCoefficient := by
      rw [neg_div]
      exact neg_pos.mpr (div_neg_of_pos_of_neg one_pos hfirst_neg)
    have hshift_pos : 0 < shift := by
      apply mul_pos _ hinv_pos
      linarith [abs_nonneg offset]
    have hmem : (g x₀ + shift, f x₀) ∈ scalarAchievableSet X f g := by
      refine scalarAchievableSet_comprehensive hx₀_mem ?_ le_rfl
      linarith
    have hsep : constant <
        (g x₀ + shift) * firstCoefficient + f x₀ * secondCoefficient :=
      hseparate_set (g x₀ + shift, f x₀) hmem
    have hfirst_shift : firstCoefficient * shift = -(|offset| + 1) := by
      rw [hshift_def]
      field_simp
    have hexpand : (g x₀ + shift) * firstCoefficient + f x₀ * secondCoefficient =
        firstCoefficient * g x₀ + firstCoefficient * shift + f x₀ * secondCoefficient := by
      ring
    rw [hexpand, hfirst_shift] at hsep
    have hoffset_lt : offset < -(|offset| + 1) := by
      rw [hoffset_def]
      linarith
    linarith [abs_nonneg offset, neg_abs_le offset]
  have hsecond_nonpos : secondCoefficient ≤ 0 := by
    by_contra hsecond_pos
    push Not at hsecond_pos
    have hsecond_ne : secondCoefficient ≠ 0 := ne_of_gt hsecond_pos
    set offset : ℝ := constant - g x₀ * firstCoefficient - secondCoefficient * f x₀
      with hoffset_def
    set shift : ℝ := (|offset| + 1) / secondCoefficient with hshift_def
    have hshift_pos : 0 < shift := by
      apply div_pos _ hsecond_pos
      linarith [abs_nonneg offset]
    have hmem : (g x₀, f x₀ - shift) ∈ scalarAchievableSet X f g := by
      refine scalarAchievableSet_comprehensive hx₀_mem le_rfl ?_
      linarith
    have hsep : constant <
        g x₀ * firstCoefficient + (f x₀ - shift) * secondCoefficient :=
      hseparate_set (g x₀, f x₀ - shift) hmem
    have hsecond_shift : secondCoefficient * shift = |offset| + 1 := by
      rw [hshift_def]
      field_simp
    have hexpand : g x₀ * firstCoefficient + (f x₀ - shift) * secondCoefficient =
        g x₀ * firstCoefficient + secondCoefficient * f x₀ - secondCoefficient * shift := by
      ring
    rw [hexpand, hsecond_shift] at hsep
    have hoffset_lt : offset < -(|offset| + 1) := by
      rw [hoffset_def]
      linarith
    linarith [abs_nonneg offset, neg_abs_le offset]
  have hsecond_neg : secondCoefficient < 0 := by
    rcases lt_or_eq_of_le hsecond_nonpos with hsecond_lt | hsecond_eq
    · exact hsecond_lt
    · exfalso
      have hprimal_epsilon_mul : (primal + epsilon) * secondCoefficient = 0 := by
        rw [hsecond_eq]
        ring
      have hconstant_pos : 0 < constant := by
        linarith
      have hmem_sep := hseparate_set (g x₀, f x₀) hx₀_mem
      have hfx₀_second : f x₀ * secondCoefficient = 0 := by
        rw [hsecond_eq]
        ring
      have hfirst_gx₀_le : firstCoefficient * g x₀ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfirst_nonneg hg_x₀.le
      nlinarith [hmem_sep, hfirst_gx₀_le, hfx₀_second]
  set multiplier : ℝ := -firstCoefficient / secondCoefficient with hmultiplier_def
  have hmultiplier_nonneg : 0 ≤ multiplier := by
    rw [hmultiplier_def]
    exact div_nonneg_of_nonpos (neg_nonpos_of_nonneg hfirst_nonneg) hsecond_neg.le
  have hdual_bound : ∀ x ∈ X,
      scalarLagrangian f g x multiplier ≤ constant / secondCoefficient := by
    intro x hxX
    have hmem := hseparate_set (g x, f x) (scalar_image_mem_achievableSet hxX)
    unfold scalarLagrangian
    rw [hmultiplier_def]
    have hsecond_ne : secondCoefficient ≠ 0 := ne_of_lt hsecond_neg
    have hdiv : (g x * firstCoefficient + f x * secondCoefficient) / secondCoefficient <
        constant / secondCoefficient :=
      div_lt_div_of_neg_of_lt hsecond_neg hmem
    have heq : (g x * firstCoefficient + f x * secondCoefficient) / secondCoefficient =
        f x + firstCoefficient * g x / secondCoefficient := by
      field_simp
      ring
    rw [heq] at hdiv
    have hsub : f x - -firstCoefficient / secondCoefficient * g x =
        f x + firstCoefficient * g x / secondCoefficient := by
      field_simp
      ring
    linarith
  have hX_ne : X.Nonempty := ⟨x₀, hx₀X⟩
  have hdualObjective_le : scalarDualObjective X f g multiplier ≤ constant / secondCoefficient :=
    scalarDualObjective_le hX_ne hdual_bound
  have hconstant_div : constant / secondCoefficient < primal + epsilon := by
    have hsecond_ne : secondCoefficient ≠ 0 := ne_of_lt hsecond_neg
    have hstep : constant / secondCoefficient <
        (primal + epsilon) * secondCoefficient / secondCoefficient :=
      div_lt_div_of_neg_of_lt hsecond_neg hseparate_point
    rwa [mul_div_assoc, div_self hsecond_ne, mul_one] at hstep
  have hdualValue_le : scalarDualValue X f g ≤ scalarDualObjective X f g multiplier := by
    unfold scalarDualValue
    have hmem : scalarDualObjective X f g multiplier ∈ scalarDualObjective X f g '' Ici 0 :=
      ⟨multiplier, hmultiplier_nonneg, rfl⟩
    refine csInf_le ?_ hmem
    refine ⟨f x₀, ?_⟩
    rintro value ⟨candidateMultiplier, hcandidateMultiplier, rfl⟩
    exact scalarFeasible_le_scalarDualObjective hcompact hf_cont hg_cont hcandidateMultiplier
      ⟨hx₀X, hg_x₀.le⟩
  linarith

/--
Strong duality for a compact convex frontier of attainable `(cost, payoff)`
pairs.  The first coordinate is constrained by `cost ≤ radius`, and the
second coordinate is maximized.  This is the finite-dimensional frontier form
of the Slater step in constrained transport and distributionally robust
optimization: applications must establish compactness and convexity of their
actual attainable-pair set, rather than assume a duality conclusion.
-/
theorem scalarStrongDuality_costPayoffFrontier
    (frontier : Set (ℝ × ℝ)) (radius : ℝ)
    (hcompact : IsCompact frontier) (hconvex : Convex ℝ frontier)
    (hstrict : ∃ point ∈ frontier, point.1 < radius) :
    scalarPrimalValue frontier Prod.snd (fun point => point.1 - radius) =
      scalarDualValue frontier Prod.snd (fun point => point.1 - radius) := by
  apply scalarStrongDuality_of_isScalarSlater hcompact
  · exact continuous_snd.continuousOn
  · refine ⟨hconvex, ?_⟩
    intro first hfirst second hsecond a b ha hb hab
    change a * first.2 + b * second.2 ≤ a * first.2 + b * second.2
    exact le_rfl
  · exact (continuous_fst.sub continuous_const).continuousOn
  · refine ⟨hconvex, ?_⟩
    intro first hfirst second hsecond a b ha hb hab
    change a * first.1 + b * second.1 - radius ≤
      a * (first.1 - radius) + b * (second.1 - radius)
    have hradius : (a + b) * radius = radius := by rw [hab]; ring
    exact le_of_eq (by
      calc
        a * first.1 + b * second.1 - radius =
            a * first.1 + b * second.1 - (a + b) * radius := by rw [hradius]
        _ = a * (first.1 - radius) + b * (second.1 - radius) := by ring)
  · exact {
      convex_X := hconvex
      convex_g := by
        refine ⟨hconvex, ?_⟩
        intro first hfirst second hsecond a b ha hb hab
        change a * first.1 + b * second.1 - radius ≤
          a * (first.1 - radius) + b * (second.1 - radius)
        have hradius : (a + b) * radius = radius := by rw [hab]; ring
        exact le_of_eq (by
          calc
            a * first.1 + b * second.1 - radius =
                a * first.1 + b * second.1 - (a + b) * radius := by rw [hradius]
            _ = a * (first.1 - radius) + b * (second.1 - radius) := by ring)
      strict_feasible := by
        obtain ⟨point, hpoint, hcost⟩ := hstrict
        exact ⟨point, hpoint, sub_neg.mpr hcost⟩ }

end ScalarStrongDualityTheorem
end Optimization
end AppliedModelingLib
