import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# First-order smooth maps under composition

This module packages the elementary first-order data needed to propagate both
a global Lipschitz bound and a Lipschitz derivative bound through a
composition.  It is useful for finite-dimensional neural-network calculations,
but is stated for arbitrary real normed vector spaces.

The calculus chain rule and continuous-linear-map operator bound come from the
pinned Mathlib API (`HasFDerivAt.comp` and
`ContinuousLinearMap.opNorm_comp_le`); this module supplies only the resulting
quantitative composition inequality.
-/

namespace AppliedModelingLib.Optimization

open Function

variable {E F G : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]

noncomputable section

/--
The forward prefix formed by a finite family of maps between consecutively
indexed real normed spaces.  This deliberately records only the composition
itself, without value or derivative bounds.
-/
def prefixMap {depth : ℕ} {Space : Fin (depth + 1) → Type*}
    [(level : Fin (depth + 1)) → NormedAddCommGroup (Space level)]
    [(level : Fin (depth + 1)) → NormedSpace ℝ (Space level)]
    (layer : ∀ level : Fin depth, Space level.castSucc → Space level.succ) :
    (level : Fin (depth + 1)) → Space 0 → Space level :=
  Fin.induction id fun level previous => layer level ∘ previous

/--
The ordered derivative product of `prefixMap`.  At level zero this is the
identity; each succeeding layer derivative is composed on the left.
-/
def prefixDeriv {depth : ℕ} {Space : Fin (depth + 1) → Type*}
    [(level : Fin (depth + 1)) → NormedAddCommGroup (Space level)]
    [(level : Fin (depth + 1)) → NormedSpace ℝ (Space level)]
    (layer : ∀ level : Fin depth, Space level.castSucc → Space level.succ)
    (deriv : ∀ level : Fin depth,
      Space level.castSucc → Space level.castSucc →L[ℝ] Space level.succ) :
    (level : Fin (depth + 1)) → Space 0 → (Space 0 →L[ℝ] Space level) :=
  Fin.induction (fun _ => ContinuousLinearMap.id ℝ (Space 0)) fun level previous point =>
    (deriv level (prefixMap layer level.castSucc point)).comp (previous point)

/--
Differentiable layers give the derivative of every finite forward prefix as
the ordered composition of the layer derivatives.  No global Lipschitz or
derivative-Lipschitz bound is required.
-/
theorem hasFDerivAt_prefixMap
    {depth : ℕ} {Space : Fin (depth + 1) → Type*}
    [(level : Fin (depth + 1)) → NormedAddCommGroup (Space level)]
    [(level : Fin (depth + 1)) → NormedSpace ℝ (Space level)]
    (layer : ∀ level : Fin depth, Space level.castSucc → Space level.succ)
    (deriv : ∀ level : Fin depth,
      Space level.castSucc → Space level.castSucc →L[ℝ] Space level.succ)
    (hlayer : ∀ level point, HasFDerivAt (layer level) (deriv level point) point)
    (level : Fin (depth + 1)) (point : Space 0) :
    HasFDerivAt (prefixMap layer level) (prefixDeriv layer deriv level point) point := by
  induction level using Fin.induction with
  | zero =>
      simpa [prefixMap, prefixDeriv] using (hasFDerivAt_id (𝕜 := ℝ) point)
  | succ level inductionHypothesis =>
      simpa [prefixMap, prefixDeriv, Function.comp_apply] using
        (hlayer level (prefixMap layer level.castSucc point)).comp point inductionHypothesis

/-- A differentiable map with explicit global value, derivative, and derivative-Lipschitz bounds. -/
structure FirstOrderSmoothMap (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  toFun : E → F
  deriv : E → E →L[ℝ] F
  valueLipschitz : ℝ
  derivBound : ℝ
  derivSmoothness : ℝ
  valueLipschitz_nonneg : 0 ≤ valueLipschitz
  derivBound_nonneg : 0 ≤ derivBound
  derivSmoothness_nonneg : 0 ≤ derivSmoothness
  hasFDerivAt : ∀ point, HasFDerivAt toFun (deriv point) point
  value_lipschitz : ∀ first second,
    ‖toFun first - toFun second‖ ≤ valueLipschitz * ‖first - second‖
  deriv_bound : ∀ point, ‖deriv point‖ ≤ derivBound
  deriv_lipschitz : ∀ first second,
    ‖deriv first - deriv second‖ ≤ derivSmoothness * ‖first - second‖

namespace FirstOrderSmoothMap

/-- Identity map with the uniform source-friendly bounds `1`, `1`, and `0`. -/
def identity : FirstOrderSmoothMap E E where
  toFun := id
  deriv := fun _ => ContinuousLinearMap.id ℝ E
  valueLipschitz := 1
  derivBound := 1
  derivSmoothness := 0
  valueLipschitz_nonneg := zero_le_one
  derivBound_nonneg := zero_le_one
  derivSmoothness_nonneg := le_rfl
  hasFDerivAt := hasFDerivAt_id
  value_lipschitz := by simp
  deriv_bound := fun _ => ContinuousLinearMap.norm_id_le
  deriv_lipschitz := by simp

/-- Differentiability plus a global value-Lipschitz bound controls the operator norm of the derivative. -/
theorem deriv_bound_le_valueLipschitz (map : FirstOrderSmoothMap E F) (point : E) :
    ‖map.deriv point‖ ≤ map.valueLipschitz := by
  let constant : NNReal := ⟨map.valueLipschitz, map.valueLipschitz_nonneg⟩
  have hLipschitz : LipschitzWith constant map.toFun := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [NNReal.coe_mk, dist_eq_norm] using map.value_lipschitz first second
  simpa only [constant] using (map.hasFDerivAt point).le_of_lipschitz hLipschitz

/-- Replace any explicit derivative bound by the sharp bound derived from the value-Lipschitz field. -/
def normalizeDerivBound (map : FirstOrderSmoothMap E F) : FirstOrderSmoothMap E F where
  toFun := map.toFun
  deriv := map.deriv
  valueLipschitz := map.valueLipschitz
  derivBound := map.valueLipschitz
  derivSmoothness := map.derivSmoothness
  valueLipschitz_nonneg := map.valueLipschitz_nonneg
  derivBound_nonneg := map.valueLipschitz_nonneg
  derivSmoothness_nonneg := map.derivSmoothness_nonneg
  hasFDerivAt := map.hasFDerivAt
  value_lipschitz := map.value_lipschitz
  deriv_bound := map.deriv_bound_le_valueLipschitz
  deriv_lipschitz := map.deriv_lipschitz

/-- A continuous linear map has constant derivative and zero derivative smoothness. -/
def ofContinuousLinearMap (linear : E →L[ℝ] F) : FirstOrderSmoothMap E F where
  toFun := linear
  deriv := fun _ => linear
  valueLipschitz := ‖linear‖
  derivBound := ‖linear‖
  derivSmoothness := 0
  valueLipschitz_nonneg := norm_nonneg _
  derivBound_nonneg := norm_nonneg _
  derivSmoothness_nonneg := le_rfl
  hasFDerivAt := fun _ => linear.hasFDerivAt
  value_lipschitz := by
    intro first second
    simpa only [map_sub] using linear.le_opNorm (first - second)
  deriv_bound := fun _ => le_rfl
  deriv_lipschitz := by simp

/-- Composition preserves explicit first-order smoothness bounds. -/
def comp (outer : FirstOrderSmoothMap F G) (inner : FirstOrderSmoothMap E F) :
    FirstOrderSmoothMap E G where
  toFun := outer.toFun ∘ inner.toFun
  deriv := fun point => (outer.deriv (inner.toFun point)).comp (inner.deriv point)
  valueLipschitz := outer.valueLipschitz * inner.valueLipschitz
  derivBound := outer.derivBound * inner.derivBound
  derivSmoothness :=
    outer.derivSmoothness * inner.valueLipschitz * inner.derivBound +
      outer.derivBound * inner.derivSmoothness
  valueLipschitz_nonneg := mul_nonneg outer.valueLipschitz_nonneg inner.valueLipschitz_nonneg
  derivBound_nonneg := mul_nonneg outer.derivBound_nonneg inner.derivBound_nonneg
  derivSmoothness_nonneg := by
    exact add_nonneg
      (mul_nonneg (mul_nonneg outer.derivSmoothness_nonneg inner.valueLipschitz_nonneg)
        inner.derivBound_nonneg)
      (mul_nonneg outer.derivBound_nonneg inner.derivSmoothness_nonneg)
  hasFDerivAt := by
    intro point
    simpa only [Function.comp_apply] using
      (outer.hasFDerivAt (inner.toFun point)).comp point (inner.hasFDerivAt point)
  value_lipschitz := by
    intro first second
    calc
      ‖(outer.toFun ∘ inner.toFun) first - (outer.toFun ∘ inner.toFun) second‖ =
          ‖outer.toFun (inner.toFun first) - outer.toFun (inner.toFun second)‖ := rfl
      _ ≤ outer.valueLipschitz * ‖inner.toFun first - inner.toFun second‖ :=
        outer.value_lipschitz _ _
      _ ≤ outer.valueLipschitz * (inner.valueLipschitz * ‖first - second‖) :=
        mul_le_mul_of_nonneg_left (inner.value_lipschitz first second)
          outer.valueLipschitz_nonneg
      _ = (outer.valueLipschitz * inner.valueLipschitz) * ‖first - second‖ := by ring
  deriv_bound := by
    intro point
    calc
      ‖(outer.deriv (inner.toFun point)).comp (inner.deriv point)‖ ≤
          ‖outer.deriv (inner.toFun point)‖ * ‖inner.deriv point‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ outer.derivBound * inner.derivBound :=
        mul_le_mul (outer.deriv_bound _) (inner.deriv_bound _) (norm_nonneg _)
          outer.derivBound_nonneg
  deriv_lipschitz := by
    intro first second
    let firstOuter := outer.deriv (inner.toFun first)
    let secondOuter := outer.deriv (inner.toFun second)
    let firstInner := inner.deriv first
    let secondInner := inner.deriv second
    have hdecomposition :
        firstOuter.comp firstInner - secondOuter.comp secondInner =
          (firstOuter - secondOuter).comp firstInner +
            secondOuter.comp (firstInner - secondInner) := by
      ext direction
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.add_apply, map_sub]
      abel
    have houter_difference :
        ‖firstOuter - secondOuter‖ ≤
          outer.derivSmoothness *
            (inner.valueLipschitz * ‖first - second‖) := by
      exact (outer.deriv_lipschitz (inner.toFun first) (inner.toFun second)).trans
        (mul_le_mul_of_nonneg_left (inner.value_lipschitz first second)
          outer.derivSmoothness_nonneg)
    have hfirst_term :
        ‖(firstOuter - secondOuter).comp firstInner‖ ≤
          (outer.derivSmoothness *
              (inner.valueLipschitz * ‖first - second‖)) * inner.derivBound := by
      calc
        ‖(firstOuter - secondOuter).comp firstInner‖ ≤
            ‖firstOuter - secondOuter‖ * ‖firstInner‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (outer.derivSmoothness *
              (inner.valueLipschitz * ‖first - second‖)) * inner.derivBound :=
          mul_le_mul houter_difference (inner.deriv_bound first) (norm_nonneg _)
            (mul_nonneg outer.derivSmoothness_nonneg
              (mul_nonneg inner.valueLipschitz_nonneg (norm_nonneg _)))
    have hsecond_term :
        ‖secondOuter.comp (firstInner - secondInner)‖ ≤
          outer.derivBound * (inner.derivSmoothness * ‖first - second‖) := by
      calc
        ‖secondOuter.comp (firstInner - secondInner)‖ ≤
            ‖secondOuter‖ * ‖firstInner - secondInner‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ outer.derivBound * (inner.derivSmoothness * ‖first - second‖) :=
          mul_le_mul (outer.deriv_bound (inner.toFun second))
            (inner.deriv_lipschitz first second) (norm_nonneg _) outer.derivBound_nonneg
    change ‖firstOuter.comp firstInner - secondOuter.comp secondInner‖ ≤ _
    rw [hdecomposition]
    calc
      ‖(firstOuter - secondOuter).comp firstInner +
          secondOuter.comp (firstInner - secondInner)‖ ≤
          ‖(firstOuter - secondOuter).comp firstInner‖ +
            ‖secondOuter.comp (firstInner - secondInner)‖ := norm_add_le _ _
      _ ≤ (outer.derivSmoothness *
              (inner.valueLipschitz * ‖first - second‖)) * inner.derivBound +
            outer.derivBound * (inner.derivSmoothness * ‖first - second‖) :=
        add_le_add hfirst_term hsecond_term
      _ = (outer.derivSmoothness * inner.valueLipschitz * inner.derivBound +
            outer.derivBound * inner.derivSmoothness) * ‖first - second‖ := by ring

end FirstOrderSmoothMap
end
end AppliedModelingLib.Optimization
