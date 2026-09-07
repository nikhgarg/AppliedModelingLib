import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Finite follow-the-regularized-leader algebra

This module proves the finite-horizon algebra shared by FTRL analyses.  It
separates two genuine ingredients:

* **be the leader**: each next action minimizes the regularizer plus every
  loss observed so far; and
* **stability**: the current and next FTRL actions have controlled one-step
  loss difference.

The first ingredient is proved here from the literal prefix minimizers.  The
second is deliberately an explicit premise: applications derive it from their
own regularizer's curvature and first-order conditions rather than hiding an
oracle or differentiability assumption in the summation algebra.
-/

open scoped BigOperators InnerProductSpace

namespace AppliedModelingLib

/-- The FTRL objective after the first `prefix` losses: a regularizer plus
the corresponding finite prefix sum. -/
def finiteFTRLObjective {Decision : Type*}
    (regularizer : Decision → ℝ) (loss : ℕ → Decision → ℝ)
    (prefixLength : ℕ) (decision : Decision) : ℝ :=
  regularizer decision + ∑ round ∈ Finset.range prefixLength, loss round decision

/-- If each `action prefix` minimizes the literal FTRL prefix objective, then
the shifted action sequence satisfies the finite be-the-leader inequality.
The action at zero is the regularizer-only leader, and loss `t` is charged to
the action selected after observing that loss. -/
theorem finiteFTRL_be_the_leader
    {Decision : Type*} (feasible : Set Decision)
    (regularizer : Decision → ℝ) (loss : ℕ → Decision → ℝ)
    (action : ℕ → Decision)
    (haction : ∀ prefixLength, action prefixLength ∈ feasible)
    (hminimizes : ∀ prefixLength,
      IsMinOn (finiteFTRLObjective regularizer loss prefixLength) feasible (action prefixLength))
    (comparator : Decision) (hcomparator : comparator ∈ feasible) :
    ∀ horizon,
      regularizer (action 0) +
          ∑ round ∈ Finset.range horizon, loss round (action (round + 1)) ≤
        regularizer comparator +
          ∑ round ∈ Finset.range horizon, loss round comparator := by
  intro horizon
  induction horizon generalizing comparator with
  | zero =>
      simpa [finiteFTRLObjective] using hminimizes 0 hcomparator
  | succ horizon ih =>
      have hprefix := ih (action (horizon + 1)) (haction (horizon + 1))
      have hleader :
          regularizer (action (horizon + 1)) +
              (∑ round ∈ Finset.range horizon, loss round (action (horizon + 1))) +
                loss horizon (action (horizon + 1)) ≤
            regularizer comparator +
              (∑ round ∈ Finset.range horizon, loss round comparator) + loss horizon comparator := by
        simpa [finiteFTRLObjective, Finset.sum_range_succ, add_assoc] using
          hminimizes (horizon + 1) hcomparator
      simp only [Finset.sum_range_succ]
      linarith

/-- Be-the-leader plus a per-round stability bound gives finite FTRL regret.
This is exact finite-sum algebra; the regularizer range and curvature enter
only through the two displayed, independently checkable inputs. -/
theorem finiteFTRL_regret_of_be_the_leader_and_stability
    {Decision : Type*} (regularizer : Decision → ℝ) (loss : ℕ → Decision → ℝ)
    (action : ℕ → Decision) (comparator : Decision) (stability : ℕ → ℝ)
    (hleader : ∀ horizon,
      regularizer (action 0) +
          ∑ round ∈ Finset.range horizon, loss round (action (round + 1)) ≤
        regularizer comparator +
          ∑ round ∈ Finset.range horizon, loss round comparator)
    (hstability : ∀ round,
      loss round (action round) - loss round (action (round + 1)) ≤ stability round) :
    ∀ horizon,
      (∑ round ∈ Finset.range horizon, loss round (action round)) -
          ∑ round ∈ Finset.range horizon, loss round comparator ≤
        regularizer comparator - regularizer (action 0) +
          ∑ round ∈ Finset.range horizon, stability round := by
  intro horizon
  have hshifted := hleader horizon
  have hstabilitySum :
      ∑ round ∈ Finset.range horizon,
        (loss round (action round) - loss round (action (round + 1))) ≤
        ∑ round ∈ Finset.range horizon, stability round := by
    apply Finset.sum_le_sum
    intro round _
    exact hstability round
  have hdecomposition :
      ∑ round ∈ Finset.range horizon, loss round (action round) =
        (∑ round ∈ Finset.range horizon,
          (loss round (action round) - loss round (action (round + 1)))) +
          ∑ round ∈ Finset.range horizon, loss round (action (round + 1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro round _
    ring
  rw [hdecomposition]
  linarith

/-- A literal prefix-minimizer FTRL trajectory and a stability certificate
therefore imply the standard finite regret decomposition. -/
theorem finiteFTRL_regret_of_prefix_minimizers_and_stability
    {Decision : Type*} (feasible : Set Decision)
    (regularizer : Decision → ℝ) (loss : ℕ → Decision → ℝ)
    (action : ℕ → Decision) (comparator : Decision) (stability : ℕ → ℝ)
    (haction : ∀ prefixLength, action prefixLength ∈ feasible)
    (hminimizes : ∀ prefixLength,
      IsMinOn (finiteFTRLObjective regularizer loss prefixLength) feasible (action prefixLength))
    (hcomparator : comparator ∈ feasible)
    (hstability : ∀ round,
      loss round (action round) - loss round (action (round + 1)) ≤ stability round) :
    ∀ horizon,
      (∑ round ∈ Finset.range horizon, loss round (action round)) -
          ∑ round ∈ Finset.range horizon, loss round comparator ≤
        regularizer comparator - regularizer (action 0) +
          ∑ round ∈ Finset.range horizon, stability round := by
  apply finiteFTRL_regret_of_be_the_leader_and_stability regularizer loss action comparator stability
    (finiteFTRL_be_the_leader feasible regularizer loss action haction hminimizes comparator hcomparator)
    hstability

/-- A one-step linear FTRL stability estimate from the two constrained
first-order inequalities and strong monotonicity of the regularizer gradient.
It is stated in a real Hilbert space so applications may use their natural
coordinate geometry.  In particular, the conclusion is the loss difference
between the current FTRL action and the action after the new linear loss. -/
theorem finiteFTRL_linear_stability_of_firstOrder_and_strongMonotone
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (regularizerGradient : Value → Value)
    (current next cumulativeGradient instantaneousGradient : Value)
    (learningRate modulus : ℝ)
    (hlearningRate : 0 ≤ learningRate) (hmodulus : 0 < modulus)
    (hstrongMonotone :
      modulus * ‖current - next‖ ^ 2 ≤
        ⟪regularizerGradient current - regularizerGradient next, current - next⟫_ℝ)
    (hcurrentFirstOrder :
      0 ≤ ⟪regularizerGradient current + learningRate • cumulativeGradient,
        next - current⟫_ℝ)
    (hnextFirstOrder :
      0 ≤ ⟪regularizerGradient next + learningRate •
        (cumulativeGradient + instantaneousGradient), current - next⟫_ℝ) :
    ⟪instantaneousGradient, current - next⟫_ℝ ≤
      learningRate / modulus * ‖instantaneousGradient‖ ^ 2 := by
  have hcurrent :
      ⟪regularizerGradient current + learningRate • cumulativeGradient,
        current - next⟫_ℝ ≤ 0 := by
    rw [show next - current = -(current - next) by abel, inner_neg_right] at hcurrentFirstOrder
    linarith
  have hvariational :
      modulus * ‖current - next‖ ^ 2 ≤
        learningRate * ⟪instantaneousGradient, current - next⟫_ℝ := by
    rw [inner_sub_left] at hstrongMonotone
    rw [inner_add_left, real_inner_smul_left] at hcurrent
    rw [inner_add_left, real_inner_smul_left, inner_add_left] at hnextFirstOrder
    nlinarith
  have hinnerNorm :
      ⟪instantaneousGradient, current - next⟫_ℝ ≤
        ‖instantaneousGradient‖ * ‖current - next‖ :=
    real_inner_le_norm _ _
  by_cases hzero : current - next = 0
  · rw [hzero]
    rw [inner_zero_right]
    exact mul_nonneg (div_nonneg hlearningRate hmodulus.le) (sq_nonneg _)
  · have hdistancePositive : 0 < ‖current - next‖ := norm_pos_iff.mpr hzero
    have hvariationalNorm :
        modulus * ‖current - next‖ ^ 2 ≤
          learningRate * (‖instantaneousGradient‖ * ‖current - next‖) :=
      hvariational.trans
        (mul_le_mul_of_nonneg_left hinnerNorm hlearningRate)
    have hdistance :
        ‖current - next‖ ≤ learningRate / modulus * ‖instantaneousGradient‖ := by
      have hcancel :
          modulus * ‖current - next‖ ≤ learningRate * ‖instantaneousGradient‖ := by
        apply le_of_mul_le_mul_right _ hdistancePositive
        convert hvariationalNorm using 1 <;> ring
      rw [show learningRate / modulus * ‖instantaneousGradient‖ =
        (learningRate * ‖instantaneousGradient‖) / modulus by ring]
      apply (le_div_iff₀ hmodulus).mpr
      nlinarith [hcancel]
    calc
      ⟪instantaneousGradient, current - next⟫_ℝ ≤
          ‖instantaneousGradient‖ * ‖current - next‖ := hinnerNorm
      _ ≤ ‖instantaneousGradient‖ *
          (learningRate / modulus * ‖instantaneousGradient‖) :=
        mul_le_mul_of_nonneg_left hdistance (norm_nonneg _)
      _ = learningRate / modulus * ‖instantaneousGradient‖ ^ 2 := by ring

/-- An approximate minimizer is close to an exact constrained minimizer when
the objective has a displayed strong-convex lower model and the exact point
satisfies its variational first-order inequality.  Keeping all three
premises explicit makes this usable for inexact FTRL or ERM routines without
silently assuming an unconstrained interior optimum. -/
theorem finiteFTRL_approximateMinimizer_norm_sq_le_of_strongLower
    {Value : Type*} [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]
    (objective : Value → ℝ) (gradient : Value → Value)
    (exact approximate : Value) (modulus approximationError : ℝ)
    (hmodulus : 0 < modulus) (herror : 0 ≤ approximationError)
    (hfirstOrder : 0 ≤ ⟪gradient exact, approximate - exact⟫_ℝ)
    (hstrongLower :
      objective approximate ≥ objective exact +
        ⟪gradient exact, approximate - exact⟫_ℝ +
          modulus / 2 * ‖approximate - exact‖ ^ 2)
    (happroximate : objective approximate ≤ objective exact + approximationError) :
    ‖approximate - exact‖ ^ 2 ≤ 2 * approximationError / modulus := by
  have hquadratic : modulus / 2 * ‖approximate - exact‖ ^ 2 ≤ approximationError := by
    nlinarith
  apply (le_div_iff₀ hmodulus).mpr
  nlinarith

end AppliedModelingLib
