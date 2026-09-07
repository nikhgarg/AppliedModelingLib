import AppliedModelingLib.Foundations.Optimization.StrongConcaveArgmax

/-!
# Stability of strongly concave argmax selections in normed spaces

This module is the dual-space counterpart of `StrongConcaveArgmax`.  It keeps
the derivative in the continuous dual rather than identifying it with a vector
through a Hilbert-space Riesz map.  Thus its optimizer-stability theorem uses
only a real normed-space geometry, exactly the setting of source statements
that formulate smoothness with a norm and its dual norm.

The proof uses Mathlib's operator-norm estimate
[`ContinuousLinearMap.le_opNorm`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Normed/Operator/NormedSpace.html#ContinuousLinearMap.le_opNorm)
from
[`Mathlib/Analysis/Normed/Operator/NormedSpace.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Normed/Operator/NormedSpace.lean),
at the repository-pinned Apache-2.0 Mathlib revision.  No external proof or
code is copied or ported.

As in the Hilbert version, an attained maximizer and its feasible-direction
first-order condition are explicit.  Strong concavity alone does not establish
them on an arbitrary feasible state domain.

For the unrestricted state-space specialization, the bridge from a pointwise
maximum and a Fréchet derivative to first-order optimality uses Mathlib's
[`IsLocalMax.hasFDerivAt_eq_zero`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/LocalExtr/Basic.html#IsLocalMax.hasFDerivAt_eq_zero)
from the repository-pinned Apache-2.0
[`LocalExtr/Basic`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Analysis/Calculus/LocalExtr/Basic.lean)
module.  No upstream proof or code is copied or ported.

For a proper convex feasible domain, the corresponding directional bridge
uses Mathlib's
[`Convex.segment_subset`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html#Convex.segment_subset),
[`HasDerivAt.tendsto_slope_zero_right`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/Deriv/Slope.html#HasDerivAt.tendsto_slope_zero_right),
and [`le_of_tendsto`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Order/OrderClosed.html#le_of_tendsto),
all at the repository-pinned Apache-2.0 Mathlib revision
[`5450b53`](https://github.com/leanprover-community/mathlib4/tree/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No external proof text or code is copied or ported.
-/

namespace AppliedModelingLib
namespace Optimization

variable {Parameter State : Type*}
variable [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
variable [NormedAddCommGroup State] [NormedSpace ℝ State]

/-- A first-order strong-concavity inequality whose state derivative is a dual vector. -/
def StrongConcaveInStateFirstOrderDual
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (modulus : ℝ) : Prop :=
  ∀ parameter base candidate,
    objective parameter candidate ≤ objective parameter base +
      stateDerivative parameter base (candidate - base) -
        modulus / 2 * ‖candidate - base‖ ^ 2

/-- The strong-concavity first-order inequality restricted to a feasible state domain. -/
def StrongConcaveInStateFirstOrderDualOn (domain : Set State)
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (modulus : ℝ) : Prop :=
  ∀ parameter base candidate, base ∈ domain → candidate ∈ domain →
    objective parameter candidate ≤ objective parameter base +
      stateDerivative parameter base (candidate - base) -
        modulus / 2 * ‖candidate - base‖ ^ 2

/-- First-order optimality of a selected maximizer, expressed in the continuous dual. -/
def HasStateFirstOrderMaximizerConditionDual
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State) : Prop :=
  ∀ parameter candidate,
    stateDerivative parameter (select parameter) (candidate - select parameter) ≤ 0

/-- Pointwise maximization restricted to a feasible state domain. -/
def IsPointwiseStateMaximizerOn (domain : Set State)
    (objective : Parameter → State → ℝ) (select : Parameter → State) : Prop :=
  ∀ parameter candidate, candidate ∈ domain →
    objective parameter candidate ≤ objective parameter (select parameter)

/-- Feasible-direction first-order optimality on a state domain. -/
def HasStateFirstOrderMaximizerConditionDualOn (domain : Set State)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State) : Prop :=
  ∀ parameter candidate, candidate ∈ domain →
    stateDerivative parameter (select parameter) (candidate - select parameter) ≤ 0

/-- The selected-point comparison needed by the smooth-envelope proof. -/
def PointwiseStateSelectionDominant
    (objective : Parameter → State → ℝ) (select : Parameter → State) : Prop :=
  ∀ parameter other,
    objective parameter (select other) ≤ objective parameter (select parameter)

/--
On an unrestricted normed state space, an attained pointwise maximizer has the
feasible-direction first-order condition whenever its state derivative exists.

For a proper feasible subset, this theorem is intentionally not applicable:
one instead needs a convex-domain or tangent-cone bridge.
-/
theorem pointwiseStateMaximizer_firstOrder_dual_of_hasFDerivAt
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hderivativeAt : ∀ parameter,
      HasFDerivAt (fun state => objective parameter state)
        (stateDerivative parameter (select parameter)) (select parameter)) :
    HasStateFirstOrderMaximizerConditionDual stateDerivative select := by
  intro parameter candidate
  have hlocal : IsLocalMax (objective parameter) (select parameter) :=
    Filter.Eventually.of_forall (fun state => hmax parameter state)
  have hzero := hlocal.hasFDerivAt_eq_zero (hderivativeAt parameter)
  rw [hzero]
  simp

omit [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter] in
/--
An attained pointwise maximum on a convex feasible domain satisfies the
feasible-direction first-order condition when its ambient Fréchet derivative
exists at the selected state.

This is the constrained-domain counterpart of
`pointwiseStateMaximizer_firstOrder_dual_of_hasFDerivAt`; it uses right-hand
derivatives along the feasible segment from the selected state to a candidate.
-/
theorem pointwiseStateMaximizerOn_firstOrder_dual_of_convex_of_hasFDerivAt
    (domain : Set State)
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State)
    (hconvex : Convex ℝ domain)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hmax : IsPointwiseStateMaximizerOn domain objective select)
    (hderivativeAt : ∀ parameter,
      HasFDerivAt (fun state => objective parameter state)
        (stateDerivative parameter (select parameter)) (select parameter)) :
    HasStateFirstOrderMaximizerConditionDualOn domain stateDerivative select := by
  intro parameter candidate hcandidate
  let base := select parameter
  let displacement := candidate - base
  let line : ℝ → State := fun t => t • displacement + base
  let value : ℝ → ℝ := fun t => objective parameter (line t)
  have hline : HasDerivAt line displacement 0 := by
    dsimp [line]
    simpa using ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const displacement).add_const base
  have hvalue : HasDerivAt value (stateDerivative parameter base displacement) 0 := by
    have houter : HasFDerivAt (fun state => objective parameter state)
        (stateDerivative parameter base) (line 0) := by
      simpa [line, base] using hderivativeAt parameter
    have hcomp := houter.comp 0 hline
    simpa only [value, line, Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one] using hcomp.hasDerivAt
  have hvalueMax (t : ℝ) (htpos : 0 < t) (htlt : t < 1) : value t ≤ value 0 := by
    have hsegment : line t ∈ domain := by
      apply hconvex.segment_subset (hselect parameter) hcandidate
      rw [segment_eq_image_lineMap]
      refine ⟨t, ⟨le_of_lt htpos, le_of_lt htlt⟩, ?_⟩
      simp [line, displacement, base, AffineMap.lineMap_apply]
    simpa [value, line, base] using hmax parameter (line t) hsegment
  have hlt : ∀ᶠ (t : ℝ) in nhdsWithin 0 (Set.Ioi 0), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  apply le_of_tendsto hvalue.tendsto_slope_zero_right
  filter_upwards [eventually_mem_nhdsWithin, hlt] with t htpos htlt
  exact smul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr htpos.le)
    (sub_nonpos.mpr (by simpa [value] using hvalueMax t htpos htlt))

/-- A pointwise maximum on a domain controls every pair of selected states. -/
theorem IsPointwiseStateMaximizerOn.selectionDominant
    (domain : Set State) (objective : Parameter → State → ℝ) (select : Parameter → State)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hmax : IsPointwiseStateMaximizerOn domain objective select) :
    PointwiseStateSelectionDominant objective select := by
  intro parameter other
  exact hmax parameter (select other) (hselect other)

/-- A cross-Lipschitz bound for state derivatives in the parameter coordinate. -/
def StateDerivativeCrossLipschitz
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (constant : ℝ) : Prop :=
  ∀ first second state,
    ‖stateDerivative first state - stateDerivative second state‖ ≤
      constant * ‖first - second‖

/-- State-derivative parameter-coordinate smoothness on a feasible state domain. -/
def StateDerivativeCrossLipschitzOn (domain : Set State)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (constant : ℝ) : Prop :=
  ∀ first second state, state ∈ domain →
    ‖stateDerivative first state - stateDerivative second state‖ ≤
      constant * ‖first - second‖

/--
An attained strongly-concave pointwise maximizer is Lipschitz in the parameter
when its state derivative is cross-Lipschitz.  This is the arbitrary-real-norm
form of the standard optimizer-map estimate.
-/
theorem pointwiseStateMaximizer_lipschitz_dual
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State) {modulus crossConstant : ℝ}
    (hmodulus : 0 < modulus)
    (hstrong : StrongConcaveInStateFirstOrderDual objective stateDerivative modulus)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionDual stateDerivative select)
    (hcross : StateDerivativeCrossLipschitz stateDerivative crossConstant)
    (first second : Parameter) :
    ‖select first - select second‖ ≤
      (crossConstant / modulus) * ‖first - second‖ := by
  let firstState : State := select first
  let secondState : State := select second
  let displacement : State := secondState - firstState
  have hmaxSecond : objective second firstState ≤ objective second secondState :=
    hmax second firstState
  have hstrongSecond := hstrong second firstState secondState
  have hstrongLinear :
      modulus / 2 * ‖displacement‖ ^ 2 ≤
        stateDerivative second firstState displacement := by
    dsimp [displacement] at hstrongSecond ⊢
    linarith
  have hstrongAtSecond := hstrong second secondState firstState
  have hfirstOrderSecond :
      stateDerivative second secondState (firstState - secondState) ≤ 0 :=
    hfirstOrder second firstState
  have hquadraticGap :
      modulus / 2 * ‖displacement‖ ^ 2 ≤
        objective second secondState - objective second firstState := by
    dsimp [displacement] at hstrongAtSecond ⊢
    have hnorm : ‖firstState - secondState‖ = ‖secondState - firstState‖ :=
      norm_sub_rev _ _
    rw [hnorm] at hstrongAtSecond
    linarith
  have hfirstOrderFirst :
      stateDerivative first firstState displacement ≤ 0 := by
    dsimp [firstState, displacement]
    exact hfirstOrder first secondState
  have hstrongCore :
      modulus * ‖displacement‖ ^ 2 ≤
        (stateDerivative second firstState - stateDerivative first firstState) displacement := by
    rw [ContinuousLinearMap.sub_apply]
    linarith [hquadraticGap]
  have happly :
      (stateDerivative second firstState - stateDerivative first firstState) displacement ≤
        ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ := by
    calc
      (stateDerivative second firstState - stateDerivative first firstState) displacement ≤
          |(stateDerivative second firstState - stateDerivative first firstState) displacement| :=
        le_abs_self _
      _ = ‖(stateDerivative second firstState - stateDerivative first firstState) displacement‖ := by
        simp only [Real.norm_eq_abs]
      _ ≤ ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ :=
        (stateDerivative second firstState - stateDerivative first firstState).le_opNorm displacement
  have hgradient :
      ‖stateDerivative second firstState - stateDerivative first firstState‖ ≤
        crossConstant * ‖first - second‖ := by
    simpa [norm_sub_rev] using hcross second first firstState
  have hdisplacement_nonneg : 0 ≤ ‖displacement‖ := norm_nonneg _
  have hgradientBound :
      ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    mul_le_mul_of_nonneg_right hgradient hdisplacement_nonneg
  have hquadratic :
      modulus * ‖displacement‖ ^ 2 ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    hstrongCore.trans (happly.trans hgradientBound)
  by_cases hzero : ‖displacement‖ = 0
  · have hstate : firstState = secondState := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
    have hcross_nonneg : 0 ≤ crossConstant * ‖first - second‖ :=
      (norm_nonneg _).trans hgradient
    have hright : 0 ≤ (crossConstant / modulus) * ‖first - second‖ := by
      rw [show (crossConstant / modulus) * ‖first - second‖ =
          (crossConstant * ‖first - second‖) / modulus by field_simp]
      exact div_nonneg hcross_nonneg hmodulus.le
    simpa only [firstState, secondState, hstate, sub_self, norm_zero] using hright
  · have hdisplacement_pos : 0 < ‖displacement‖ := lt_of_le_of_ne hdisplacement_nonneg
      (Ne.symm hzero)
    have hlinear : modulus * ‖displacement‖ ≤ crossConstant * ‖first - second‖ := by
      nlinarith [hquadratic]
    have htarget : ‖displacement‖ ≤
        (crossConstant / modulus) * ‖first - second‖ := by
      rw [show (crossConstant / modulus) * ‖first - second‖ =
          (crossConstant * ‖first - second‖) / modulus by field_simp]
      exact (le_div_iff₀ hmodulus).mpr (by simpa [mul_comm] using hlinear)
    simpa only [firstState, secondState, displacement, norm_sub_rev] using htarget

/--
An attained strongly-concave pointwise maximizer is Lipschitz in its parameter
on a feasible domain.  The strong-concavity inequality, maximization, and
first-order condition are used only at feasible selected states and feasible
candidates, so this is the domain-faithful version of
`pointwiseStateMaximizer_lipschitz_dual`.
-/
theorem pointwiseStateMaximizerOn_lipschitz_dual
    (domain : Set State)
    (objective : Parameter → State → ℝ)
    (stateDerivative : Parameter → State → State →L[ℝ] ℝ)
    (select : Parameter → State) {modulus crossConstant : ℝ}
    (hmodulus : 0 < modulus)
    (hselect : ∀ parameter, select parameter ∈ domain)
    (hstrong : StrongConcaveInStateFirstOrderDualOn domain objective stateDerivative modulus)
    (hmax : IsPointwiseStateMaximizerOn domain objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionDualOn domain stateDerivative select)
    (hcross : StateDerivativeCrossLipschitzOn domain stateDerivative crossConstant)
    (first second : Parameter) :
    ‖select first - select second‖ ≤
      (crossConstant / modulus) * ‖first - second‖ := by
  let firstState : State := select first
  let secondState : State := select second
  let displacement : State := secondState - firstState
  have hmaxSecond : objective second firstState ≤ objective second secondState :=
    hmax second firstState (hselect first)
  have hstrongSecond := hstrong second firstState secondState (hselect first) (hselect second)
  have hstrongLinear :
      modulus / 2 * ‖displacement‖ ^ 2 ≤
        stateDerivative second firstState displacement := by
    dsimp [displacement] at hstrongSecond ⊢
    linarith
  have hstrongAtSecond := hstrong second secondState firstState (hselect second) (hselect first)
  have hfirstOrderSecond :
      stateDerivative second secondState (firstState - secondState) ≤ 0 :=
    hfirstOrder second firstState (hselect first)
  have hquadraticGap :
      modulus / 2 * ‖displacement‖ ^ 2 ≤
        objective second secondState - objective second firstState := by
    dsimp [displacement] at hstrongAtSecond ⊢
    have hnorm : ‖firstState - secondState‖ = ‖secondState - firstState‖ :=
      norm_sub_rev _ _
    rw [hnorm] at hstrongAtSecond
    linarith
  have hfirstOrderFirst :
      stateDerivative first firstState displacement ≤ 0 := by
    dsimp [firstState, displacement]
    exact hfirstOrder first secondState (hselect second)
  have hstrongCore :
      modulus * ‖displacement‖ ^ 2 ≤
        (stateDerivative second firstState - stateDerivative first firstState) displacement := by
    rw [ContinuousLinearMap.sub_apply]
    linarith [hquadraticGap]
  have happly :
      (stateDerivative second firstState - stateDerivative first firstState) displacement ≤
        ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ := by
    calc
      (stateDerivative second firstState - stateDerivative first firstState) displacement ≤
          |(stateDerivative second firstState - stateDerivative first firstState) displacement| :=
        le_abs_self _
      _ = ‖(stateDerivative second firstState - stateDerivative first firstState) displacement‖ := by
        simp only [Real.norm_eq_abs]
      _ ≤ ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ :=
        (stateDerivative second firstState - stateDerivative first firstState).le_opNorm displacement
  have hgradient :
      ‖stateDerivative second firstState - stateDerivative first firstState‖ ≤
        crossConstant * ‖first - second‖ := by
    simpa [norm_sub_rev] using hcross second first firstState (hselect first)
  have hdisplacement_nonneg : 0 ≤ ‖displacement‖ := norm_nonneg _
  have hgradientBound :
      ‖stateDerivative second firstState - stateDerivative first firstState‖ *
          ‖displacement‖ ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    mul_le_mul_of_nonneg_right hgradient hdisplacement_nonneg
  have hquadratic :
      modulus * ‖displacement‖ ^ 2 ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    hstrongCore.trans (happly.trans hgradientBound)
  by_cases hzero : ‖displacement‖ = 0
  · have hstate : firstState = secondState := by
      exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
    have hcross_nonneg : 0 ≤ crossConstant * ‖first - second‖ :=
      (norm_nonneg _).trans hgradient
    have hright : 0 ≤ (crossConstant / modulus) * ‖first - second‖ := by
      rw [show (crossConstant / modulus) * ‖first - second‖ =
          (crossConstant * ‖first - second‖) / modulus by field_simp]
      exact div_nonneg hcross_nonneg hmodulus.le
    simpa only [firstState, secondState, hstate, sub_self, norm_zero] using hright
  · have hdisplacement_pos : 0 < ‖displacement‖ := lt_of_le_of_ne hdisplacement_nonneg
      (Ne.symm hzero)
    have hlinear : modulus * ‖displacement‖ ≤ crossConstant * ‖first - second‖ := by
      nlinarith [hquadratic]
    have htarget : ‖displacement‖ ≤
        (crossConstant / modulus) * ‖first - second‖ := by
      rw [show (crossConstant / modulus) * ‖first - second‖ =
          (crossConstant * ‖first - second‖) / modulus by field_simp]
      exact (le_div_iff₀ hmodulus).mpr (by simpa [mul_comm] using hlinear)
    simpa only [firstState, secondState, displacement, norm_sub_rev] using htarget

end Optimization
end AppliedModelingLib
