import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedVisitation
import Mathlib.Tactic

/-!
# Occupancy accounting for stage-indexed finite-horizon rewards

This module makes explicit the finite-PMF rollout identity used when a
finite-horizon exploration algorithm is run against a synthetic reward.  A
policy value is the sum, over source stages, of the immediate expected reward
under the corresponding state law.  The initial stage need not be zero, which
is essential for backward-induction and prefix-rollout algorithms.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- Separate the first term of a finite real-valued range sum without changing
the source-stage indexing of its tail. -/
theorem sum_range_succ_eq_head_add_shift (f : ℕ → ℝ) (horizon : ℕ) :
    f 0 + ∑ elapsed ∈ Finset.range horizon, f (elapsed + 1) =
      ∑ elapsed ∈ Finset.range (horizon + 1), f elapsed := by
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
      ring

/--
The state law after a specified number of elapsed transitions when a
stage-indexed policy starts at an arbitrary absolute source stage.
-/
noncomputable def stageIndexedStateLawFrom
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) (startTime : ℕ) :
    ℕ → PMF State
  | 0 => initial
  | elapsed + 1 =>
      stageIndexedAdvanceStateLaw transition policy
        (stageIndexedStateLawFrom transition policy initial startTime elapsed)
        (startTime + elapsed)

@[simp] theorem stageIndexedStateLawFrom_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) (startTime : ℕ) :
    stageIndexedStateLawFrom transition policy initial startTime 0 = initial :=
  rfl

@[simp] theorem stageIndexedStateLawFrom_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (startTime elapsed : ℕ) :
    stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1) =
      stageIndexedAdvanceStateLaw transition policy
        (stageIndexedStateLawFrom transition policy initial startTime elapsed)
        (startTime + elapsed) :=
  rfl

/-- The zero-start instance of the absolute-time rollout agrees with the
ordinary stage-indexed state law. -/
theorem stageIndexedStateLaw_eq_stateIndexedStateLawFrom_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) :
    ∀ time,
      stageIndexedStateLaw transition policy initial time =
        stageIndexedStateLawFrom transition policy initial 0 time
  | 0 => rfl
  | time + 1 => by
      rw [stageIndexedStateLaw_succ, stageIndexedStateLawFrom_succ,
        stageIndexedStateLaw_eq_stateIndexedStateLawFrom_zero]
      simp

/--
Removing the first source stage is the same rollout as advancing the initial
law once and starting one absolute stage later.
-/
theorem stageIndexedStateLawFrom_succ_eq_advanced
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (startTime elapsed : ℕ) :
    stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1) =
      stageIndexedStateLawFrom transition policy
        (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1) elapsed := by
  induction elapsed with
  | zero => rfl
  | succ elapsed ih =>
      calc
        stageIndexedStateLawFrom transition policy initial startTime (Nat.succ elapsed + 1) =
            stageIndexedAdvanceStateLaw transition policy
              (stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1))
              (startTime + (elapsed + 1)) := by rfl
        _ = stageIndexedAdvanceStateLaw transition policy
              (stageIndexedStateLawFrom transition policy
                (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
                elapsed)
              ((startTime + 1) + elapsed) := by
              rw [ih]
              congr 1
              omega
        _ = stageIndexedStateLawFrom transition policy
              (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
              (elapsed + 1) := by rfl

/--
Finite-horizon policy value is the sum of its immediate expected rewards under
the actual state law at every elapsed stage.
-/
theorem stageIndexedPolicyValue_eq_sum_stateLawFrom
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedPolicyValue transition reward policy initial startTime horizon =
        ∑ elapsed ∈ Finset.range horizon,
          pmfExp (stageIndexedStateLawFrom transition policy initial startTime elapsed)
            (fun state => pmfExp (policy (startTime + elapsed) state)
              (fun action => reward (startTime + elapsed) state action)) := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp
  | succ horizon ih =>
      rw [stageIndexedPolicyValue_succ]
      rw [ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)]
      have htail :
          (∑ elapsed ∈ Finset.range horizon,
            pmfExp (stageIndexedStateLawFrom transition policy
              (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1) elapsed)
              (fun state => pmfExp (policy ((startTime + 1) + elapsed) state)
                (fun action => reward ((startTime + 1) + elapsed) state action))) =
          ∑ elapsed ∈ Finset.range horizon,
            pmfExp (stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1))
              (fun state => pmfExp (policy (startTime + (elapsed + 1)) state)
                (fun action => reward (startTime + (elapsed + 1)) state action)) := by
        apply Finset.sum_congr rfl
        intro elapsed _
        have htime : (startTime + 1) + elapsed = startTime + (elapsed + 1) := by omega
        rw [← stageIndexedStateLawFrom_succ_eq_advanced]
        simp [htime]
      rw [htail]
      simpa only [stageIndexedStateLawFrom_zero, Nat.zero_add] using
        (sum_range_succ_eq_head_add_shift
          (fun elapsed =>
            pmfExp (stageIndexedStateLawFrom transition policy initial startTime elapsed)
              (fun state => pmfExp (policy (startTime + elapsed) state)
                (fun action => reward (startTime + elapsed) state action))) horizon)

end PreferenceRL

end AppliedModelingLib
