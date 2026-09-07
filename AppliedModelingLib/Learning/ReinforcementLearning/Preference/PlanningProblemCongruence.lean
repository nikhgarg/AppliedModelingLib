import AppliedModelingLib.Learning.ReinforcementLearning.Preference.LinearLeastSquaresPlanning

/-!
# Observational congruence for finite least-squares planners

Two planning records may store different totalized data functions while
agreeing on every row in their finite index set.  The planner cannot observe
the off-index differences.  This file packages that fact for covariance,
regression, bonuses, and the full backward recursion.
-/

namespace AppliedModelingLib
namespace PreferenceRL

open AppliedModelingLib.FiniteDimensionalNorms

noncomputable section

/-- Equality of every field and data row that a finite planning problem can
actually read. -/
structure LinearPlanningProblem.SameObservations
    {Index State Action Coordinate : Type*}
    (first second : LinearPlanningProblem Index State Action Coordinate) : Prop where
  indices : first.data.indices = second.data.indices
  feature : first.feature = second.feature
  ridge : first.ridge = second.ridge
  bonusScale : first.bonusScale = second.bonusScale
  state : ∀ index ∈ first.data.indices, ∀ time,
    first.data.state index time = second.data.state index time
  action : ∀ index ∈ first.data.indices, ∀ time,
    first.data.action index time = second.data.action index time
  nextState : ∀ index ∈ first.data.indices, ∀ time,
    first.data.nextState index time = second.data.nextState index time

theorem LinearPlanningProblem.SameObservations.sampleFeature_eq
    {Index State Action Coordinate : Type*}
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (time : ℕ) (index : Index) (hindex : index ∈ first.data.indices) :
    first.sampleFeature time index = second.sampleFeature time index := by
  unfold LinearPlanningProblem.sampleFeature
  rw [h.feature, h.state index hindex time, h.action index hindex time]

theorem LinearPlanningProblem.SameObservations.covariance_eq
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second) (time : ℕ) :
    first.covariance time = second.covariance time := by
  unfold LinearPlanningProblem.covariance regularizedGram
  rw [h.ridge, ← h.indices]
  congr 1
  apply Finset.sum_congr rfl
  intro index hindex
  rw [h.sampleFeature_eq time index hindex]

theorem LinearPlanningProblem.SameObservations.regressionSignal_eq
    {Index State Action Coordinate : Type*}
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second) (time : ℕ) (nextValue : State → ℝ) :
    first.regressionSignal time nextValue = second.regressionSignal time nextValue := by
  unfold LinearPlanningProblem.regressionSignal
  rw [← h.indices]
  apply Finset.sum_congr rfl
  intro index hindex
  rw [h.nextState index hindex time, h.sampleFeature_eq time index hindex]

theorem LinearPlanningProblem.SameObservations.weight_eq
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second) (time : ℕ) (nextValue : State → ℝ) :
    first.weight time nextValue = second.weight time nextValue := by
  unfold LinearPlanningProblem.weight
  rw [h.covariance_eq time, h.regressionSignal_eq time nextValue]

theorem LinearPlanningProblem.SameObservations.widthSq_eq
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (time : ℕ) (state : State) (action : Action) :
    first.widthSq time state action = second.widthSq time state action := by
  unfold LinearPlanningProblem.widthSq
  rw [h.feature, h.covariance_eq time]

theorem LinearPlanningProblem.SameObservations.explorationBonus_eq
    {Index State Action Coordinate : Type*}
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (remaining time : ℕ) (state : State) (action : Action) :
    first.explorationBonus remaining time state action =
      second.explorationBonus remaining time state action := by
  unfold LinearPlanningProblem.explorationBonus
  rw [h.bonusScale, h.widthSq_eq time state action]

/-- The complete optimistic backward recursion only depends on the rows in the
finite dataset index set. -/
theorem LinearPlanningProblem.SameObservations.linearUCBExplorationResult_eq
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second) (horizon : ℕ) :
    ∀ remaining time,
      linearUCBExplorationResult first horizon remaining time =
        linearUCBExplorationResult second horizon remaining time := by
  intro remaining
  induction remaining with
  | zero => intro time; rfl
  | succ remaining ih =>
      intro time
      simp only [linearUCBExplorationResult]
      rw [ih (time + 1)]
      rw [h.weight_eq time]
      simp_rw [h.explorationBonus_eq (remaining + 1) time]
      rw [h.feature]

theorem LinearPlanningProblem.SameObservations.linearUCBExplorationValue_eq
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (horizon remaining time : ℕ) :
    linearUCBExplorationValue first horizon remaining time =
      linearUCBExplorationValue second horizon remaining time := by
  funext state
  unfold linearUCBExplorationValue
  rw [h.linearUCBExplorationResult_eq horizon remaining time]

theorem LinearPlanningProblem.SameObservations.linearUCBExplorationQ_eq
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (horizon remaining time : ℕ) :
    linearUCBExplorationQ first horizon remaining time =
      linearUCBExplorationQ second horizon remaining time := by
  funext state action
  unfold linearUCBExplorationQ
  rw [h.linearUCBExplorationResult_eq horizon remaining time]

theorem LinearPlanningProblem.SameObservations.linearUCBExplorationAction_eq
    {Index State Action Coordinate : Type*}
    [Fintype Action] [Nonempty Action]
    [Fintype Coordinate] [DecidableEq Coordinate]
    {first second : LinearPlanningProblem Index State Action Coordinate}
    (h : first.SameObservations second)
    (horizon remaining time : ℕ) :
    linearUCBExplorationAction first horizon remaining time =
      linearUCBExplorationAction second horizon remaining time := by
  funext state
  unfold linearUCBExplorationAction
  rw [h.linearUCBExplorationQ_eq horizon remaining time]

end

end PreferenceRL
end AppliedModelingLib
