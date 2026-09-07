import AppliedModelingLib.Learning.ReinforcementLearning.Preference.ApproximateDynamicProgramming
import Mathlib.Tactic

/-!
# Stage-indexed approximate dynamic programming for finite MDPs

Finite-horizon policy-search algorithms construct an action rule backwards:
the action selected at a state may depend on the stage even when the MDP's
transition and reward primitives are stationary.  This file supplies the
corresponding Bellman-error accumulation theorem for transition-dependent
finite-MDP rewards.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A deterministic finite-horizon action rule may vary with the absolute stage. -/
abbrev StageIndexedDeterministicPolicy (State Action : Type*) :=
  ℕ → State → Action

/-- Extend a finite-horizon action table by a harmless fallback beyond its horizon. -/
def finiteHorizonStageActionRule {State Action : Type*} (horizon : ℕ)
    (choose : Fin horizon → State → Action) (fallback : Action) :
    StageIndexedDeterministicPolicy State Action :=
  fun time state => if htime : time < horizon then choose ⟨time, htime⟩ state else fallback

@[simp]
theorem finiteHorizonStageActionRule_apply_of_lt {State Action : Type*} (horizon : ℕ)
    (choose : Fin horizon → State → Action) (fallback : Action)
    (time : ℕ) (htime : time < horizon) (state : State) :
    finiteHorizonStageActionRule horizon choose fallback time state = choose ⟨time, htime⟩ state := by
  simp [finiteHorizonStageActionRule, htime]

/--
The value obtained by following a stage-indexed deterministic rule for a
specified number of remaining stages. The reward is the MDP's original
transition-dependent reward, through `FiniteMDP.actionValue`.
-/
noncomputable def stageIndexedHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (startTime : ℕ) : ℕ → State → ℝ
  | 0 => fun _ => 0
  | remaining + 1 => fun state =>
      M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
        state (choose startTime state)

@[simp]
theorem stageIndexedHorizonValue_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (startTime : ℕ) (state : State) :
    stageIndexedHorizonValue M choose startTime 0 state = 0 :=
  rfl

@[simp]
theorem stageIndexedHorizonValue_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (startTime remaining : ℕ) (state : State) :
    stageIndexedHorizonValue M choose startTime (remaining + 1) state =
      M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
        state (choose startTime state) :=
  rfl

/--
At every stage and state, the selected action is Bellman-optimal up to the
displayed additive error relative to the already constructed continuation.
-/
def StageIndexedApproximatelyGreedy
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (error : ℝ) : Prop :=
  ∀ startTime remaining state,
    M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) state ≤
      M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
        state (choose startTime state) + error

/--
Stage-indexed approximate Bellman choices accumulate at most one local error
per remaining stage against the finite-MDP optimal value.
-/
theorem optimalValue_le_stageIndexedHorizonValue_add_of_approximatelyGreedy
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (error : ℝ) (hgreedy : StageIndexedApproximatelyGreedy M choose error) :
    ∀ startTime remaining state,
      M.optimalValue remaining state ≤
        stageIndexedHorizonValue M choose startTime remaining state + (remaining : ℝ) * error := by
  intro startTime remaining
  induction remaining generalizing startTime with
  | zero =>
      intro state
      simp
  | succ remaining ih =>
      intro state
      calc
        M.optimalValue (remaining + 1) state = M.optimalStep (M.optimalValue remaining) state := by
          rfl
        _ ≤ M.optimalStep
            (fun nextState =>
              stageIndexedHorizonValue M choose (startTime + 1) remaining nextState +
                (remaining : ℝ) * error)
            state :=
          optimalStep_mono M (fun nextState => ih (startTime + 1) nextState) state
        _ = M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) state +
              (remaining : ℝ) * error := by
          exact optimalStep_add_constant M
            (stageIndexedHorizonValue M choose (startTime + 1) remaining)
            ((remaining : ℝ) * error) state
        _ ≤ M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
              state (choose startTime state) + error + (remaining : ℝ) * error := by
          linarith [hgreedy startTime remaining state]
        _ = stageIndexedHorizonValue M choose startTime (remaining + 1) state +
              ((remaining + 1 : ℕ) : ℝ) * error := by
          rw [stageIndexedHorizonValue_succ]
          push_cast
          ring

/--
The bounded-horizon variant only requires Bellman guarantees on stages reached
before the finite horizon.  This is the form used by backward policy search.
-/
theorem optimalValue_le_stageIndexedHorizonValue_add_of_approximatelyGreedy_upTo
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (error : ℝ) (horizon : ℕ)
    (hgreedy : ∀ startTime remaining,
      startTime + remaining < horizon →
        M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) ≤
          fun state => M.actionValue
            (stageIndexedHorizonValue M choose (startTime + 1) remaining)
            state (choose startTime state) + error) :
    ∀ startTime remaining, startTime + remaining ≤ horizon → ∀ state,
      M.optimalValue remaining state ≤
        stageIndexedHorizonValue M choose startTime remaining state + (remaining : ℝ) * error := by
  intro startTime remaining
  induction remaining generalizing startTime with
  | zero =>
      intro _ state
      simp
  | succ remaining ih =>
      intro hbound state
      have hstrict : startTime + remaining < horizon := by omega
      have hnext : startTime + 1 + remaining ≤ horizon := by omega
      calc
        M.optimalValue (remaining + 1) state = M.optimalStep (M.optimalValue remaining) state := by
          rfl
        _ ≤ M.optimalStep
            (fun nextState =>
              stageIndexedHorizonValue M choose (startTime + 1) remaining nextState +
                (remaining : ℝ) * error)
            state :=
          optimalStep_mono M (fun nextState => ih (startTime + 1) hnext nextState) state
        _ = M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) state +
              (remaining : ℝ) * error := by
          exact optimalStep_add_constant M
            (stageIndexedHorizonValue M choose (startTime + 1) remaining)
            ((remaining : ℝ) * error) state
        _ ≤ M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
              state (choose startTime state) + error + (remaining : ℝ) * error := by
          linarith [hgreedy startTime remaining hstrict state]
        _ = stageIndexedHorizonValue M choose startTime (remaining + 1) state +
              ((remaining + 1 : ℕ) : ℝ) * error := by
          rw [stageIndexedHorizonValue_succ]
          push_cast
          ring

/--
Backward finite-horizon policy search only needs a Bellman guarantee at the
one continuation length associated with each absolute stage.  This theorem is
therefore sharper than the uniformly bounded-horizon variant: a call at time
`startTime` is compared against the continuation with exactly enough remaining
stages to reach the specified horizon.
-/
theorem optimalValue_le_stageIndexedHorizonValue_add_of_backwardApproximatelyGreedy
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : StageIndexedDeterministicPolicy State Action)
    (error : ℝ) (horizon : ℕ)
    (hgreedy : ∀ startTime remaining,
      startTime + remaining + 1 = horizon →
        M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) ≤
          fun state => M.actionValue
            (stageIndexedHorizonValue M choose (startTime + 1) remaining)
            state (choose startTime state) + error) :
    ∀ startTime remaining, startTime + remaining = horizon → ∀ state,
      M.optimalValue remaining state ≤
        stageIndexedHorizonValue M choose startTime remaining state + (remaining : ℝ) * error := by
  intro startTime remaining
  induction remaining generalizing startTime with
  | zero =>
      intro _ state
      simp
  | succ remaining ih =>
      intro htime state
      have hnext : (startTime + 1) + remaining = horizon := by
        omega
      have hlocal : startTime + remaining + 1 = horizon := by
        omega
      calc
        M.optimalValue (remaining + 1) state = M.optimalStep (M.optimalValue remaining) state := by
          rfl
        _ ≤ M.optimalStep
            (fun nextState =>
              stageIndexedHorizonValue M choose (startTime + 1) remaining nextState +
                (remaining : ℝ) * error)
            state :=
          optimalStep_mono M (fun nextState => ih (startTime + 1) hnext nextState) state
        _ = M.optimalStep (stageIndexedHorizonValue M choose (startTime + 1) remaining) state +
              (remaining : ℝ) * error := by
          exact optimalStep_add_constant M
            (stageIndexedHorizonValue M choose (startTime + 1) remaining)
            ((remaining : ℝ) * error) state
        _ ≤ M.actionValue (stageIndexedHorizonValue M choose (startTime + 1) remaining)
              state (choose startTime state) + error + (remaining : ℝ) * error := by
          linarith [hgreedy startTime remaining hlocal state]
        _ = stageIndexedHorizonValue M choose startTime (remaining + 1) state +
              ((remaining + 1 : ℕ) : ℝ) * error := by
          rw [stageIndexedHorizonValue_succ]
          push_cast
          ring

/-- Choosing local error `constant * epsilon / horizon` gives total loss `epsilon`. -/
theorem stageIndexed_horizon_accumulated_scaled_error
    (horizon : ℕ) (horizonPositive : 0 < horizon)
    (constant epsilon : ℝ) (hconstant : 0 < constant) :
    (horizon : ℝ) * ((constant * epsilon / (horizon : ℝ)) / constant) = epsilon := by
  have hhorizon : (horizon : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast horizonPositive)
  have hconstant' : constant ≠ 0 := ne_of_gt hconstant
  field_simp [hhorizon, hconstant']

end PreferenceRL

end AppliedModelingLib
