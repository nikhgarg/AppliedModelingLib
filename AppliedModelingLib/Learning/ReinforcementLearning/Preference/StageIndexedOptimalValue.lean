import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedPerformanceDifference
import Mathlib.Tactic

/-!
# Optimal values for finite stage-indexed MDPs

This module supplies the finite-action Bellman optimum for transition and
reward primitives that vary with absolute time.  It complements the fixed-
policy recursion in `StageIndexedOccupancy`.
-/

namespace AppliedModelingLib
namespace PreferenceRL

open AppliedModelingLib

noncomputable section

/-- Finite-horizon optimal value for a stage-indexed transition and reward. -/
def stageIndexedOptimalValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) : ℕ → ℕ → State → ℝ
  | _, 0, _ => 0
  | time, remaining + 1, state =>
      (Finset.univ : Finset Action).sup' Finset.univ_nonempty fun action =>
        reward time state action +
          pmfExp (transition time state action)
            (stageIndexedOptimalValue transition reward (time + 1) remaining)

@[simp] theorem stageIndexedOptimalValue_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (time : ℕ) (state : State) :
    stageIndexedOptimalValue transition reward time 0 state = 0 := by
  rfl

theorem stageIndexedOptimalActionValue_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (time remaining : ℕ) (state : State) (action : Action) :
    reward time state action +
        pmfExp (transition time state action)
          (stageIndexedOptimalValue transition reward (time + 1) remaining) ≤
      stageIndexedOptimalValue transition reward time (remaining + 1) state := by
  unfold stageIndexedOptimalValue
  exact Finset.le_sup' (s := (Finset.univ : Finset Action))
    (f := fun action => reward time state action +
      pmfExp (transition time state action)
        (stageIndexedOptimalValue transition reward (time + 1) remaining)) (by simp)

/-- Every randomized stage-indexed policy is bounded by the Bellman optimum. -/
theorem stageIndexedStateValue_le_optimalValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) :
    ∀ time remaining state,
      stageIndexedStateValue transition reward policy time remaining state ≤
        stageIndexedOptimalValue transition reward time remaining state := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state
      change 0 ≤ 0
      norm_num
  | succ remaining ih =>
      intro state
      rw [stageIndexedStateValue_succ]
      apply FiniteMDP.pmfExp_le_const
      intro action
      calc
        reward time state action +
            pmfExp (transition time state action)
              (stageIndexedStateValue transition reward policy (time + 1) remaining) ≤
          reward time state action +
            pmfExp (transition time state action)
              (stageIndexedOptimalValue transition reward (time + 1) remaining) := by
            exact add_le_add (le_refl _)
              (FiniteMarkovKernel.pmfExp_mono (transition time state action)
                (fun nextState => ih (time + 1) nextState))
        _ ≤ stageIndexedOptimalValue transition reward time (remaining + 1) state :=
          stageIndexedOptimalActionValue_le transition reward time remaining state action

/-- A candidate that is super-Bellman for a reference reward dominates the
optimal value of any reward bounded by a nonnegative multiple of the reference
reward.  This packages both reward monotonicity and positive scaling without
requiring a policy optimizer. -/
theorem stageIndexedOptimalValue_le_scale_candidate
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action]
    (transition : StageIndexedTransitionModel State Action)
    (targetReward referenceReward : StageIndexedReward State Action)
    (candidate : ℕ → ℕ → State → ℝ) (scale : ℝ)
    (hscale : 0 ≤ scale)
    (hreward : ∀ time state action,
      targetReward time state action ≤ scale * referenceReward time state action)
    (hterminal : ∀ time state, 0 ≤ scale * candidate time 0 state)
    (hsuper : ∀ time remaining state action,
      referenceReward time state action +
          pmfExp (transition time state action) (candidate (time + 1) remaining) ≤
        candidate time (remaining + 1) state) :
    ∀ time remaining state,
      stageIndexedOptimalValue transition targetReward time remaining state ≤
        scale * candidate time remaining state := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state
      simpa using hterminal time state
  | succ remaining ih =>
      intro state
      unfold stageIndexedOptimalValue
      apply Finset.sup'_le
      intro action _haction
      calc
        targetReward time state action +
            pmfExp (transition time state action)
              (stageIndexedOptimalValue transition targetReward (time + 1) remaining) ≤
          scale * referenceReward time state action +
            pmfExp (transition time state action)
              (fun nextState => scale * candidate (time + 1) remaining nextState) := by
            exact add_le_add (hreward time state action)
              (FiniteMarkovKernel.pmfExp_mono (transition time state action)
                (ih (time + 1)))
        _ = scale * (referenceReward time state action +
            pmfExp (transition time state action)
              (candidate (time + 1) remaining)) := by
            rw [pmfExp_const_mul]
            ring
        _ ≤ scale * candidate time (remaining + 1) state :=
          mul_le_mul_of_nonneg_left (hsuper time remaining state action) hscale

/-- Diagonal finite-horizon version of
`stageIndexedOptimalValue_le_scale_candidate`.  A finite-horizon dynamic
program only visits pairs `(time, remaining)` with constant sum, so a
paper-local Bellman certificate need only be supplied on that diagonal. -/
theorem stageIndexedOptimalValue_le_scale_candidate_of_elapsed
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [Nonempty Action]
    (transition : StageIndexedTransitionModel State Action)
    (targetReward referenceReward : StageIndexedReward State Action)
    (candidate : ℕ → ℕ → State → ℝ) (scale : ℝ) (horizon : ℕ)
    (hscale : 0 ≤ scale)
    (hreward : ∀ time state action,
      targetReward time state action ≤ scale * referenceReward time state action)
    (hterminal : ∀ time state, 0 ≤ scale * candidate time 0 state)
    (hsuper : ∀ time remaining state action,
      time + remaining + 1 = horizon →
      referenceReward time state action +
          pmfExp (transition time state action) (candidate (time + 1) remaining) ≤
        candidate time (remaining + 1) state) :
    ∀ time remaining, time + remaining = horizon → ∀ state,
      stageIndexedOptimalValue transition targetReward time remaining state ≤
        scale * candidate time remaining state := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro _hdiag state
      simpa using hterminal time state
  | succ remaining ih =>
      intro hdiag state
      unfold stageIndexedOptimalValue
      apply Finset.sup'_le
      intro action _haction
      have hnext : time + 1 + remaining = horizon := by omega
      have hbellman : time + remaining + 1 = horizon := by omega
      calc
        targetReward time state action +
            pmfExp (transition time state action)
              (stageIndexedOptimalValue transition targetReward (time + 1) remaining) ≤
          scale * referenceReward time state action +
            pmfExp (transition time state action)
              (fun nextState => scale * candidate (time + 1) remaining nextState) := by
            exact add_le_add (hreward time state action)
              (FiniteMarkovKernel.pmfExp_mono (transition time state action)
                (ih (time + 1) hnext))
        _ = scale * (referenceReward time state action +
            pmfExp (transition time state action)
              (candidate (time + 1) remaining)) := by
            rw [pmfExp_const_mul]
            ring
        _ ≤ scale * candidate time (remaining + 1) state :=
          mul_le_mul_of_nonneg_left
            (hsuper time remaining state action hbellman) hscale

end

end PreferenceRL
end AppliedModelingLib
