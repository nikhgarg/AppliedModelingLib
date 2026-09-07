import AppliedModelingLib.Foundations.Optimization.SmoothStrongConvex

/-!
# Stability of strongly concave argmax selections

This module formalizes the first-order core of the standard argmax-stability
argument.  It separates three logically distinct facts that are often bundled
informally: an attained pointwise maximizer, its feasible-direction first-order
condition, and a strong-concavity first-order inequality.  Under a cross
Lipschitz bound on the state gradient, the selected maximizer is Lipschitz in
the parameter.

The approximate-maximizer distance estimate directly uses Mathlib's
`sq_le_sq₀` from
[`Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/5450b53e5ddc75d46418fabb605edbf36bd0beb6/Mathlib/Algebra/Order/GroupWithZero/Unbundled/Basic.lean)
at the repository-pinned Apache-2.0 Mathlib revision
[`5450b53e5ddc75d46418fabb605edbf36bd0beb6`](https://github.com/leanprover-community/mathlib4/commit/5450b53e5ddc75d46418fabb605edbf36bd0beb6).
No upstream proof or code is copied or ported.

The explicit first-order-maximizer hypothesis is intentional.  Differentiable
strong concavity by itself does not supply it on an arbitrary nonconvex
feasible domain; a convex-domain theorem can discharge this premise in a
later layer.
-/

namespace AppliedModelingLib
namespace Optimization

open scoped InnerProductSpace

variable {Parameter State : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [NormedAddCommGroup State] [InnerProductSpace ℝ State]

/-- A first-order strong-concavity inequality in the state coordinate. -/
def StrongConcaveInStateFirstOrder
    (objective : Parameter → State → ℝ) (stateGradient : Parameter → State → State)
    (modulus : ℝ) : Prop :=
  ∀ parameter base candidate,
    objective parameter candidate ≤ objective parameter base +
      ⟪stateGradient parameter base, candidate - base⟫_ℝ -
        modulus / 2 * ‖candidate - base‖ ^ 2

/-- A first-order strong-concavity inequality restricted to feasible states. -/
def StrongConcaveInStateFirstOrderOn (domain : Set State)
    (objective : Parameter → State → ℝ) (stateGradient : Parameter → State → State)
    (modulus : ℝ) : Prop :=
  ∀ parameter base candidate, base ∈ domain → candidate ∈ domain →
    objective parameter candidate ≤ objective parameter base +
      ⟪stateGradient parameter base, candidate - base⟫_ℝ -
        modulus / 2 * ‖candidate - base‖ ^ 2

/-- A selector attains the pointwise maximum on the represented state domain. -/
def IsPointwiseStateMaximizer (objective : Parameter → State → ℝ)
    (select : Parameter → State) : Prop :=
  ∀ parameter candidate, objective parameter candidate ≤ objective parameter (select parameter)

/-- First-order optimality of a selected pointwise maximizer in every feasible direction. -/
def HasStateFirstOrderMaximizerCondition
    (stateGradient : Parameter → State → State) (select : Parameter → State) : Prop :=
  ∀ parameter candidate,
    ⟪stateGradient parameter (select parameter), candidate - select parameter⟫_ℝ ≤ 0

/-- First-order optimality in every feasible direction of a state domain. -/
def HasStateFirstOrderMaximizerConditionOn (domain : Set State)
    (stateGradient : Parameter → State → State) (select : Parameter → State) : Prop :=
  ∀ parameter candidate, candidate ∈ domain →
    ⟪stateGradient parameter (select parameter), candidate - select parameter⟫_ℝ ≤ 0

/-- A cross-Lipschitz bound for the state gradient in the parameter coordinate. -/
def StateGradientCrossLipschitz
    (stateGradient : Parameter → State → State) (constant : ℝ) : Prop :=
  ∀ first second state,
    ‖stateGradient first state - stateGradient second state‖ ≤
      constant * ‖first - second‖

/--
An `error`-approximate state maximizer lies within squared distance
`2 * error / modulus` of a selected first-order maximizer of a strongly
concave objective.  This is the standard objective-gap-to-distance estimate
used when an inner maximization is solved only approximately.

The result uses the selected maximizer's feasible-direction first-order
condition explicitly; neither attainment nor that condition is inferred from
strong concavity alone.
-/
theorem sq_norm_sub_le_two_mul_div_of_approximateStateMaximizer
    (objective : Parameter → State → ℝ) (stateGradient : Parameter → State → State)
    (select : Parameter → State) {modulus error : ℝ}
    (hmodulus : 0 < modulus)
    (hstrong : StrongConcaveInStateFirstOrder objective stateGradient modulus)
    (hfirstOrder : HasStateFirstOrderMaximizerCondition stateGradient select)
    (parameter : Parameter) (candidate : State)
    (happroximate : objective parameter (select parameter) - objective parameter candidate ≤ error) :
    ‖candidate - select parameter‖ ^ 2 ≤ 2 * error / modulus := by
  have hstrongCandidate := hstrong parameter (select parameter) candidate
  have hfirstOrderCandidate := hfirstOrder parameter candidate
  have hgap : modulus / 2 * ‖candidate - select parameter‖ ^ 2 ≤ error := by
    linarith
  rw [show 2 * error / modulus = error / (modulus / 2) by
    field_simp [ne_of_gt hmodulus]]
  exact (le_div_iff₀ (by positivity : 0 < modulus / 2)).mpr (by
    simpa [mul_comm] using hgap)

/--
On a feasible state domain, an approximate maximizer has the same
strong-concavity distance bound when both the selected and approximate states
are feasible.  This is the constrained counterpart of
`sq_norm_sub_le_two_mul_div_of_approximateStateMaximizer`.
-/
theorem sq_norm_sub_le_two_mul_div_of_approximateStateMaximizerOn
    (domain : Set State) (objective : Parameter → State → ℝ)
    (stateGradient : Parameter → State → State) (select : Parameter → State)
    {modulus error : ℝ}
    (hmodulus : 0 < modulus) (hselect : ∀ parameter, select parameter ∈ domain)
    (hstrong : StrongConcaveInStateFirstOrderOn domain objective stateGradient modulus)
    (hfirstOrder : HasStateFirstOrderMaximizerConditionOn domain stateGradient select)
    (parameter : Parameter) (candidate : State) (hcandidate : candidate ∈ domain)
    (happroximate : objective parameter (select parameter) - objective parameter candidate ≤ error) :
    ‖candidate - select parameter‖ ^ 2 ≤ 2 * error / modulus := by
  have hstrongCandidate := hstrong parameter (select parameter) candidate
    (hselect parameter) hcandidate
  have hfirstOrderCandidate := hfirstOrder parameter candidate hcandidate
  have hgap : modulus / 2 * ‖candidate - select parameter‖ ^ 2 ≤ error := by
    linarith
  rw [show 2 * error / modulus = error / (modulus / 2) by
    field_simp [ne_of_gt hmodulus]]
  exact (le_div_iff₀ (by positivity : 0 < modulus / 2)).mpr (by
    simpa [mul_comm] using hgap)

/--
An attained strongly concave pointwise maximizer is Lipschitz in the parameter
when its state gradient is cross-Lipschitz.  This is the Euclidean/Hilbert
version of the optimizer-map inequality used in smooth DRO surrogates.
-/
theorem pointwiseStateMaximizer_lipschitz
    (objective : Parameter → State → ℝ) (stateGradient : Parameter → State → State)
    (select : Parameter → State) {modulus crossConstant : ℝ}
    (hmodulus : 0 < modulus)
    (hstrong : StrongConcaveInStateFirstOrder objective stateGradient modulus)
    (hmax : IsPointwiseStateMaximizer objective select)
    (hfirstOrder : HasStateFirstOrderMaximizerCondition stateGradient select)
    (hcross : StateGradientCrossLipschitz stateGradient crossConstant)
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
        ⟪stateGradient second firstState, displacement⟫_ℝ := by
    dsimp [displacement] at hstrongSecond ⊢
    linarith
  have hstrongAtSecond := hstrong second secondState firstState
  have hfirstOrderSecond :
      ⟪stateGradient second secondState, firstState - secondState⟫_ℝ ≤ 0 :=
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
      ⟪stateGradient first firstState, displacement⟫_ℝ ≤ 0 := by
    dsimp [firstState, displacement]
    exact hfirstOrder first secondState
  have hstrongCore :
      modulus * ‖displacement‖ ^ 2 ≤
        ⟪stateGradient second firstState - stateGradient first firstState,
          displacement⟫_ℝ := by
    rw [inner_sub_left]
    linarith [hquadraticGap]
  have hinner :
      ⟪stateGradient second firstState - stateGradient first firstState,
          displacement⟫_ℝ ≤
        ‖stateGradient second firstState - stateGradient first firstState‖ *
          ‖displacement‖ :=
    real_inner_le_norm _ _
  have hgradient :
      ‖stateGradient second firstState - stateGradient first firstState‖ ≤
        crossConstant * ‖first - second‖ := by
    simpa [norm_sub_rev] using hcross second first firstState
  have hdisplacement_nonneg : 0 ≤ ‖displacement‖ := norm_nonneg _
  have hgradientBound :
      ‖stateGradient second firstState - stateGradient first firstState‖ *
          ‖displacement‖ ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    mul_le_mul_of_nonneg_right hgradient hdisplacement_nonneg
  have hquadratic :
      modulus * ‖displacement‖ ^ 2 ≤
        (crossConstant * ‖first - second‖) * ‖displacement‖ :=
    hstrongCore.trans (hinner.trans hgradientBound)
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
