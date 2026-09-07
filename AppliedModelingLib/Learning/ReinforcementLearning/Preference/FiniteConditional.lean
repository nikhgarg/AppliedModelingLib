import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms

/-!
# Finite joint laws and conditional policies

This module records the algebra behind empirical Markovization.  A joint
state-action mass factors as a state occupancy times a conditional action
policy.  If both a target and an empirical joint law admit such
factorizations, then the target-occupancy-weighted conditional-policy error is
at most twice their joint-mass `L1` error.  The statement remains valid at
zero-mass states because the conditional policy there may be any probability
vector.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace PreferenceRL

noncomputable section

/-- A finite joint mass together with a normalized conditional factorization. -/
structure FiniteJointPolicyFactorization (State Action : Type*)
    [Fintype Action] where
  jointMass : State → Action → ℝ
  stateMass : State → ℝ
  policy : State → Action → ℝ
  policy_nonneg : ∀ state action, 0 ≤ policy state action
  policy_sum_one : ∀ state, ∑ action, policy state action = 1
  jointMass_eq : ∀ state action,
    jointMass state action = stateMass state * policy state action

/-- State marginal error is bounded by the sum of joint-coordinate errors. -/
theorem abs_stateMass_sub_le_sum_abs_jointMass_sub
    {State Action : Type*} [Fintype Action]
    (target empirical : FiniteJointPolicyFactorization State Action)
    (state : State) :
    |target.stateMass state - empirical.stateMass state| ≤
      ∑ action, |target.jointMass state action - empirical.jointMass state action| := by
  have hstate : target.stateMass state - empirical.stateMass state =
      ∑ action, (target.jointMass state action - empirical.jointMass state action) := by
    rw [Finset.sum_sub_distrib]
    simp_rw [target.jointMass_eq, empirical.jointMass_eq]
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      target.policy_sum_one, empirical.policy_sum_one, mul_one, mul_one]
  rw [hstate]
  exact Finset.abs_sum_le_sum_abs _ _

/--
At one state, target-occupancy-weighted conditional-policy `L1` error is at
most the state-marginal error plus the joint-mass `L1` error.
-/
theorem stateMass_mul_policyL1_le_marginalError_add_jointError
    {State Action : Type*} [Fintype Action]
    (target empirical : FiniteJointPolicyFactorization State Action)
    (state : State) (htargetStateMass : 0 ≤ target.stateMass state) :
    target.stateMass state *
        (∑ action, |empirical.policy state action - target.policy state action|) ≤
      |target.stateMass state - empirical.stateMass state| +
        ∑ action,
          |empirical.jointMass state action - target.jointMass state action| := by
  rw [Finset.mul_sum]
  calc
    (∑ action,
        target.stateMass state *
          |empirical.policy state action - target.policy state action|) =
        ∑ action,
          |target.stateMass state *
            (empirical.policy state action - target.policy state action)| := by
      apply Finset.sum_congr rfl
      intro action _
      rw [abs_mul, abs_of_nonneg htargetStateMass]
    _ ≤ ∑ action,
        (|target.stateMass state - empirical.stateMass state| *
            empirical.policy state action +
          |empirical.jointMass state action - target.jointMass state action|) := by
      apply Finset.sum_le_sum
      intro action _
      have hidentity :
          target.stateMass state *
              (empirical.policy state action - target.policy state action) =
            (target.stateMass state - empirical.stateMass state) *
                empirical.policy state action +
              (empirical.jointMass state action - target.jointMass state action) := by
        rw [target.jointMass_eq, empirical.jointMass_eq]
        ring
      rw [hidentity]
      calc
        |(target.stateMass state - empirical.stateMass state) *
              empirical.policy state action +
            (empirical.jointMass state action - target.jointMass state action)| ≤
            |(target.stateMass state - empirical.stateMass state) *
                empirical.policy state action| +
              |empirical.jointMass state action - target.jointMass state action| :=
          abs_add_le _ _
        _ = |target.stateMass state - empirical.stateMass state| *
              empirical.policy state action +
              |empirical.jointMass state action - target.jointMass state action| := by
          rw [abs_mul, abs_of_nonneg (empirical.policy_nonneg state action)]
    _ = |target.stateMass state - empirical.stateMass state| +
        ∑ action,
          |empirical.jointMass state action - target.jointMass state action| := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        empirical.policy_sum_one, mul_one]

/--
Global empirical-conditional stability: weighted policy error is at most twice
the joint-mass `L1` error.
-/
theorem weightedPolicyL1_le_two_mul_jointMassL1
    {State Action : Type*} [Fintype State] [Fintype Action]
    (target empirical : FiniteJointPolicyFactorization State Action)
    (htargetStateMass : ∀ state, 0 ≤ target.stateMass state) :
    (∑ state, target.stateMass state *
        ∑ action, |empirical.policy state action - target.policy state action|) ≤
      2 * ∑ state, ∑ action,
        |empirical.jointMass state action - target.jointMass state action| := by
  calc
    (∑ state, target.stateMass state *
        ∑ action, |empirical.policy state action - target.policy state action|) ≤
        ∑ state,
          (|target.stateMass state - empirical.stateMass state| +
            ∑ action,
              |empirical.jointMass state action - target.jointMass state action|) := by
      apply Finset.sum_le_sum
      intro state _
      exact stateMass_mul_policyL1_le_marginalError_add_jointError
        target empirical state (htargetStateMass state)
    _ ≤ ∑ state,
        ((∑ action,
            |target.jointMass state action - empirical.jointMass state action|) +
          ∑ action,
            |empirical.jointMass state action - target.jointMass state action|) := by
      apply Finset.sum_le_sum
      intro state _
      exact add_le_add
        (abs_stateMass_sub_le_sum_abs_jointMass_sub target empirical state) le_rfl
    _ = 2 * ∑ state, ∑ action,
        |empirical.jointMass state action - target.jointMass state action| := by
      simp_rw [abs_sub_comm (target.jointMass _ _) (empirical.jointMass _ _)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _
      ring

/--
A bounded score difference is controlled by policy `L1` distance.  This is the
one-state inequality used inside the performance-difference expansion.
-/
theorem abs_sum_policyDifference_mul_score_le_policyL1
    {Action : Type*} [Fintype Action]
    (first second : Action → ℝ) (score : Action → ℝ)
    (hscore : ∀ action, |score action| ≤ 1) :
    |∑ action, (first action - second action) * score action| ≤
      ∑ action, |first action - second action| := by
  calc
    |∑ action, (first action - second action) * score action| ≤
        ∑ action, |(first action - second action) * score action| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ action, |first action - second action| := by
      apply Finset.sum_le_sum
      intro action _
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (hscore action)

/--
Finite performance-difference bound.  Once a payoff difference is written as
the target occupancy weighted sum of conditional-policy differences against
scores in `[-1,1]`, its absolute value is controlled by the corresponding
weighted policy `L1` error.
-/
theorem abs_stagewisePerformanceDifference_le_weightedPolicyL1
    {Stage State Action : Type*}
    [Fintype Stage] [Fintype State] [Fintype Action]
    (target empirical : Stage → FiniteJointPolicyFactorization State Action)
    (score : Stage → State → Action → ℝ)
    (difference : ℝ)
    (htargetStateMass : ∀ stage state, 0 ≤ (target stage).stateMass state)
    (hscore : ∀ stage state action, |score stage state action| ≤ 1)
    (hdecomposition : difference =
      ∑ stage, ∑ state, (target stage).stateMass state *
        ∑ action,
          ((empirical stage).policy state action -
            (target stage).policy state action) * score stage state action) :
    |difference| ≤
      ∑ stage, ∑ state, (target stage).stateMass state *
        ∑ action,
          |(empirical stage).policy state action -
            (target stage).policy state action| := by
  rw [hdecomposition]
  calc
    |∑ stage, ∑ state, (target stage).stateMass state *
        ∑ action,
          ((empirical stage).policy state action -
            (target stage).policy state action) * score stage state action| ≤
        ∑ stage, |∑ state, (target stage).stateMass state *
          ∑ action,
            ((empirical stage).policy state action -
              (target stage).policy state action) * score stage state action| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ stage, ∑ state,
        |(target stage).stateMass state *
          ∑ action,
            ((empirical stage).policy state action -
              (target stage).policy state action) * score stage state action| := by
      apply Finset.sum_le_sum
      intro stage _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ stage, ∑ state, (target stage).stateMass state *
        ∑ action,
          |(empirical stage).policy state action -
            (target stage).policy state action| := by
      apply Finset.sum_le_sum
      intro stage _
      apply Finset.sum_le_sum
      intro state _
      rw [abs_mul, abs_of_nonneg (htargetStateMass stage state)]
      exact mul_le_mul_of_nonneg_left
        (abs_sum_policyDifference_mul_score_le_policyL1
          ((empirical stage).policy state) ((target stage).policy state)
          (score stage state) (hscore stage state))
        (htargetStateMass stage state)

/--
Joint-law form of the stagewise performance-difference bound: empirical
conditionalization costs at most twice the summed stagewise joint-mass `L1`
error.
-/
theorem abs_stagewisePerformanceDifference_le_two_mul_jointMassL1
    {Stage State Action : Type*}
    [Fintype Stage] [Fintype State] [Fintype Action]
    (target empirical : Stage → FiniteJointPolicyFactorization State Action)
    (score : Stage → State → Action → ℝ)
    (difference : ℝ)
    (htargetStateMass : ∀ stage state, 0 ≤ (target stage).stateMass state)
    (hscore : ∀ stage state action, |score stage state action| ≤ 1)
    (hdecomposition : difference =
      ∑ stage, ∑ state, (target stage).stateMass state *
        ∑ action,
          ((empirical stage).policy state action -
            (target stage).policy state action) * score stage state action) :
    |difference| ≤
      2 * ∑ stage, ∑ state, ∑ action,
        |(empirical stage).jointMass state action -
          (target stage).jointMass state action| := by
  calc
    |difference| ≤
        ∑ stage, ∑ state, (target stage).stateMass state *
          ∑ action,
            |(empirical stage).policy state action -
              (target stage).policy state action| :=
      abs_stagewisePerformanceDifference_le_weightedPolicyL1
        target empirical score difference htargetStateMass hscore hdecomposition
    _ ≤ ∑ stage, 2 * ∑ state, ∑ action,
        |(empirical stage).jointMass state action -
          (target stage).jointMass state action| := by
      apply Finset.sum_le_sum
      intro stage _
      exact weightedPolicyL1_le_two_mul_jointMassL1
        (target stage) (empirical stage) (htargetStateMass stage)
    _ = 2 * ∑ stage, ∑ state, ∑ action,
        |(empirical stage).jointMass state action -
          (target stage).jointMass state action| := by
      rw [Finset.mul_sum]

end

end PreferenceRL
end AppliedModelingLib
