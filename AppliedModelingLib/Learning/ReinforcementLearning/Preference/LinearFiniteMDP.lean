import AppliedModelingLib.Learning.ReinforcementLearning.Preference.LinearTransition
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import Mathlib.Tactic

/-!
# Finite linear Markov decision processes

This module records the finite form of a stage-indexed linear MDP.  Transition
probabilities and rewards share a known state-action feature map; the unknown
transition basis is a finite vector of signed masses over successor states.

The exact linear identities are independent of norm assumptions.  Bounds on
the Bellman parameter use an explicit variation quantity
`sum next, l2 (transitionBasis time next)`.  This is the finite hypothesis
actually needed to control integration against an arbitrary bounded value
function and avoids conflating a signed measure's total mass with its total
variation.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace PreferenceRL

open FiniteDimensionalNorms

noncomputable section

/-- A finite, stage-indexed linear representation of both transition and reward. -/
structure FiniteLinearMDPRepresentation
    (State Action Feature : Type*) [Fintype State] [Fintype Feature] where
  transition : StageIndexedTransitionModel State Action
  reward : StageIndexedReward State Action
  feature : ℕ → State → Action → Feature → ℝ
  transitionBasis : ℕ → State → Feature → ℝ
  rewardParameter : ℕ → Feature → ℝ
  transition_linear : ∀ time state action nextState,
    (transition time state action nextState).toReal =
      dot (feature time state action) (transitionBasis time nextState)
  reward_linear : ∀ time state action,
    reward time state action =
      dot (feature time state action) (rewardParameter time)

/-- The parameter obtained by integrating a next-state value against the
signed transition basis. -/
def FiniteLinearMDPRepresentation.nextValueParameter
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ) : Feature → ℝ :=
  linearTransitionRewardParameter (model.transitionBasis time) nextValue

/-- The Bellman action-value parameter: reward parameter plus integrated
continuation-value parameter. -/
def FiniteLinearMDPRepresentation.actionValueParameter
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ) : Feature → ℝ :=
  fun coordinate ↦
    model.rewardParameter time coordinate +
      model.nextValueParameter time nextValue coordinate

/-- Assumption-3 transition linearity turns every expected continuation value
into a dot product with the induced finite parameter. -/
theorem FiniteLinearMDPRepresentation.expectedNextValue_eq_dot
    {State Action Feature : Type*}
    [Fintype State] [DecidableEq State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ) (state : State) (action : Action) :
    pmfExp (model.transition time state action) nextValue =
      dot (model.feature time state action)
        (model.nextValueParameter time nextValue) := by
  exact pmfExp_eq_dot_linearTransitionRewardParameter
    (model.transition time) (model.feature time)
    (model.transitionBasis time) nextValue
    (model.transition_linear time) state action

/-- In a finite linear MDP, the one-step Bellman action value is linear in the
same state-action feature. -/
theorem FiniteLinearMDPRepresentation.reward_add_expectedNextValue_eq_dot
    {State Action Feature : Type*}
    [Fintype State] [DecidableEq State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ) (state : State) (action : Action) :
    model.reward time state action +
        pmfExp (model.transition time state action) nextValue =
      dot (model.feature time state action)
        (model.actionValueParameter time nextValue) := by
  rw [model.reward_linear, model.expectedNextValue_eq_dot]
  unfold FiniteLinearMDPRepresentation.actionValueParameter
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- The finite total-variation-style size of a stage's signed transition
basis. -/
def FiniteLinearMDPRepresentation.transitionVariation
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) : ℝ :=
  ∑ nextState : State, l2 (model.transitionBasis time nextState)

theorem FiniteLinearMDPRepresentation.transitionVariation_nonneg
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) :
    0 ≤ model.transitionVariation time := by
  unfold FiniteLinearMDPRepresentation.transitionVariation
  exact Finset.sum_nonneg fun _ _ ↦ Real.sqrt_nonneg _

/-- A bounded continuation value and a variation bound on the signed
transition basis control the induced Bellman parameter. -/
theorem FiniteLinearMDPRepresentation.nextValueParameter_l2_le
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ)
    (valueRadius variationRadius : ℝ)
    (hvalueRadius : 0 ≤ valueRadius)
    (hvalue : ∀ nextState, |nextValue nextState| ≤ valueRadius)
    (hvariation : model.transitionVariation time ≤ variationRadius) :
    l2 (model.nextValueParameter time nextValue) ≤
      valueRadius * variationRadius := by
  classical
  have hsum :
      l2 (model.nextValueParameter time nextValue) ≤
        ∑ nextState : State,
          l2 (fun coordinate ↦
            nextValue nextState * model.transitionBasis time nextState coordinate) := by
    simpa [FiniteLinearMDPRepresentation.nextValueParameter,
      linearTransitionRewardParameter] using
      (normL2_finset_sum_le (Finset.univ : Finset State)
        (fun nextState coordinate ↦
          nextValue nextState * model.transitionBasis time nextState coordinate))
  calc
    l2 (model.nextValueParameter time nextValue) ≤
        ∑ nextState : State,
          l2 (fun coordinate ↦
            nextValue nextState * model.transitionBasis time nextState coordinate) := hsum
    _ = ∑ nextState : State,
          |nextValue nextState| * l2 (model.transitionBasis time nextState) := by
      apply Finset.sum_congr rfl
      intro nextState _
      exact normL2_smul _ _
    _ ≤ ∑ nextState : State,
          valueRadius * l2 (model.transitionBasis time nextState) := by
      apply Finset.sum_le_sum
      intro nextState _
      exact mul_le_mul_of_nonneg_right (hvalue nextState) (Real.sqrt_nonneg _)
    _ = valueRadius * model.transitionVariation time := by
      simp [FiniteLinearMDPRepresentation.transitionVariation, Finset.mul_sum]
    _ ≤ valueRadius * variationRadius :=
      mul_le_mul_of_nonneg_left hvariation hvalueRadius

/-- Reward-parameter and transition-variation bounds give the standard linear
Bellman-parameter radius. -/
theorem FiniteLinearMDPRepresentation.actionValueParameter_l2_le
    {State Action Feature : Type*} [Fintype State] [Fintype Feature]
    (model : FiniteLinearMDPRepresentation State Action Feature)
    (time : ℕ) (nextValue : State → ℝ)
    (rewardRadius valueRadius variationRadius : ℝ)
    (hvalueRadius : 0 ≤ valueRadius)
    (hreward : l2 (model.rewardParameter time) ≤ rewardRadius)
    (hvalue : ∀ nextState, |nextValue nextState| ≤ valueRadius)
    (hvariation : model.transitionVariation time ≤ variationRadius) :
    l2 (model.actionValueParameter time nextValue) ≤
      rewardRadius + valueRadius * variationRadius := by
  calc
    l2 (model.actionValueParameter time nextValue) ≤
        l2 (model.rewardParameter time) +
          l2 (model.nextValueParameter time nextValue) := by
      simpa [FiniteLinearMDPRepresentation.actionValueParameter] using
        (normL2_add_le (model.rewardParameter time)
          (model.nextValueParameter time nextValue))
    _ ≤ rewardRadius + valueRadius * variationRadius :=
      add_le_add hreward
        (model.nextValueParameter_l2_le time nextValue valueRadius variationRadius
          hvalueRadius hvalue hvariation)

end

end PreferenceRL
end AppliedModelingLib
