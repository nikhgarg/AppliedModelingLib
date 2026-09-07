import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import AppliedModelingLib.Foundations.Probability.PMFKernel
import Mathlib.Tactic

/-!
# Finite-horizon transition simulation for preference-based RL

This module isolates the finite-state, stationary specialization of the
simulation argument used when a preference-RL procedure plans in an estimated
transition model.  Rewards are shared and depend only on the current
state-action pair, so transition error enters through the estimated
continuation value exactly as in the simulation lemma.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- A finite transition model with a shared state-action reward. -/
abbrev StationaryTransitionModel (State Action : Type*) :=
  State → PMFKernel Action State

/-- A randomized stationary policy for the finite transition model. -/
abbrev StationaryPolicy (State Action : Type*) :=
  PMFKernel State Action

/-- One Bellman step with a state-action reward and a continuation value. -/
noncomputable def stationaryBellmanStep
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (continuation : State → ℝ) (state : State) : ℝ :=
  pmfExp (policy state) fun action =>
    reward state action + pmfExp (transition state action) continuation

/-- Finite-horizon value with zero terminal continuation value. -/
noncomputable def stationaryHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action) :
    ℕ → State → ℝ
  | 0 => fun _ => 0
  | remaining + 1 => fun state =>
      stationaryBellmanStep transition reward policy
        (stationaryHorizonValue transition reward policy remaining) state

@[simp] theorem stationaryHorizonValue_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (state : State) :
    stationaryHorizonValue transition reward policy 0 state = 0 :=
  rfl

@[simp] theorem stationaryHorizonValue_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (remaining : ℕ) (state : State) :
    stationaryHorizonValue transition reward policy (remaining + 1) state =
      stationaryBellmanStep transition reward policy
        (stationaryHorizonValue transition reward policy remaining) state :=
  rfl

/-- The stationary Bellman step is monotone in its continuation value. -/
theorem stationaryBellmanStep_mono
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    {first second : State → ℝ} (hcontinuation : ∀ state, first state ≤ second state)
    (state : State) :
    stationaryBellmanStep transition reward policy first state ≤
      stationaryBellmanStep transition reward policy second state := by
  unfold stationaryBellmanStep
  apply FiniteMarkovKernel.pmfExp_mono
  intro action
  exact add_le_add_right
    (FiniteMarkovKernel.pmfExp_mono (transition state action) hcontinuation) _

/-- Adding a constant continuation value adds the same constant after one step. -/
theorem stationaryBellmanStep_add_constant
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (continuation : State → ℝ) (constant : ℝ) (state : State) :
    stationaryBellmanStep transition reward policy
        (fun nextState => continuation nextState + constant) state =
      stationaryBellmanStep transition reward policy continuation state + constant := by
  unfold stationaryBellmanStep
  calc
    pmfExp (policy state) (fun action => reward state action +
        pmfExp (transition state action) (fun nextState => continuation nextState + constant)) =
      pmfExp (policy state) (fun action => reward state action +
        (pmfExp (transition state action) continuation + constant)) := by
          apply pmfExp_congr
          intro action
          rw [pmfExp_add, pmfExp_const]
    _ = pmfExp (policy state) (fun action =>
        (reward state action + pmfExp (transition state action) continuation) + constant) := by
          apply pmfExp_congr
          intro action
          ring
    _ = pmfExp (policy state) (fun action =>
        reward state action + pmfExp (transition state action) continuation) +
        pmfExp (policy state) (fun _ => constant) := by
          rw [pmfExp_add]
    _ = stationaryBellmanStep transition reward policy continuation state + constant := by
          rw [pmfExp_const]
          rfl

/-- A uniform actionwise transition-residual bound lifts through the policy mixture. -/
theorem stationaryBellmanStep_sub_le_of_uniformTransitionResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (continuation : State → ℝ) (error : ℝ)
    (hresidual : ∀ state action,
      pmfExp (firstTransition state action) continuation -
          pmfExp (secondTransition state action) continuation ≤ error)
    (state : State) :
    stationaryBellmanStep firstTransition reward policy continuation state -
        stationaryBellmanStep secondTransition reward policy continuation state ≤ error := by
  unfold stationaryBellmanStep
  rw [← pmfExp_sub]
  calc
    pmfExp (policy state) (fun action =>
        (reward state action + pmfExp (firstTransition state action) continuation) -
          (reward state action + pmfExp (secondTransition state action) continuation)) =
      pmfExp (policy state) (fun action =>
        pmfExp (firstTransition state action) continuation -
          pmfExp (secondTransition state action) continuation) := by
          apply pmfExp_congr
          intro action
          ring
    _ ≤ error :=
      FiniteMDP.pmfExp_le_const (policy state) fun action => hresidual state action

/--
The stationary finite-horizon simulation inequality with an explicit residual
schedule.  At remaining horizon `k`, the local discrepancy is evaluated on
the estimated model's `k`-step continuation value.
-/
theorem stationarySimulation_difference_le_of_transitionResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (error : ℕ → ℝ)
    (hresidual : ∀ remaining state action,
      pmfExp (firstTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining) -
        pmfExp (secondTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining) ≤ error remaining) :
    ∀ horizon state,
      stationaryHorizonValue firstTransition reward policy horizon state -
          stationaryHorizonValue secondTransition reward policy horizon state ≤
        ∑ remaining ∈ Finset.range horizon, error remaining := by
  intro horizon
  induction horizon with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      calc
        stationaryHorizonValue firstTransition reward policy (horizon + 1) state -
            stationaryHorizonValue secondTransition reward policy (horizon + 1) state =
          stationaryBellmanStep firstTransition reward policy
              (stationaryHorizonValue firstTransition reward policy horizon) state -
            stationaryBellmanStep secondTransition reward policy
              (stationaryHorizonValue secondTransition reward policy horizon) state := by
                rfl
        _ ≤ stationaryBellmanStep firstTransition reward policy
              (fun nextState =>
                stationaryHorizonValue secondTransition reward policy horizon nextState +
                  ∑ remaining ∈ Finset.range horizon, error remaining) state -
            stationaryBellmanStep secondTransition reward policy
              (stationaryHorizonValue secondTransition reward policy horizon) state := by
                exact sub_le_sub_right
                  (stationaryBellmanStep_mono firstTransition reward policy
                    (fun nextState => by linarith [ih nextState]) state) _
        _ = (stationaryBellmanStep firstTransition reward policy
              (stationaryHorizonValue secondTransition reward policy horizon) state -
            stationaryBellmanStep secondTransition reward policy
              (stationaryHorizonValue secondTransition reward policy horizon) state) +
              ∑ remaining ∈ Finset.range horizon, error remaining := by
                rw [stationaryBellmanStep_add_constant]
                ring
        _ ≤ error horizon + ∑ remaining ∈ Finset.range horizon, error remaining := by
                linarith [
                  stationaryBellmanStep_sub_le_of_uniformTransitionResidual
                    firstTransition secondTransition reward policy
                    (stationaryHorizonValue secondTransition reward policy horizon)
                    (error horizon) (hresidual horizon) state]
        _ = ∑ remaining ∈ Finset.range (horizon + 1), error remaining := by
                rw [Finset.sum_range_succ]
                ring

/-- The horizon value is nonnegative when all state-action rewards are nonnegative. -/
theorem stationaryHorizonValue_nonneg_of_reward_nonneg
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (hreward : ∀ state action, 0 ≤ reward state action) :
    ∀ horizon state, 0 ≤ stationaryHorizonValue transition reward policy horizon state := by
  intro horizon
  induction horizon with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      unfold stationaryHorizonValue stationaryBellmanStep
      apply pmfExp_nonneg_of_forall_nonneg
      intro action
      apply add_nonneg (hreward state action)
      apply pmfExp_nonneg_of_forall_nonneg
      intro nextState
      exact ih nextState

/-- Unit-bounded state-action rewards give a horizon-length upper bound on value. -/
theorem stationaryHorizonValue_le_horizon_of_reward_le_one
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (hreward : ∀ state action, reward state action ≤ 1) :
    ∀ horizon state,
      stationaryHorizonValue transition reward policy horizon state ≤ (horizon : ℝ) := by
  intro horizon
  induction horizon with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      unfold stationaryHorizonValue stationaryBellmanStep
      apply FiniteMDP.pmfExp_le_const
      intro action
      calc
        reward state action +
            pmfExp (transition state action)
              (stationaryHorizonValue transition reward policy horizon) ≤
          1 + (horizon : ℝ) := by
            exact add_le_add (hreward state action)
              (FiniteMDP.pmfExp_le_const (transition state action) fun nextState => ih nextState)
        _ = ((horizon + 1 : ℕ) : ℝ) := by
            push_cast
            ring

/--
The finite-PMF ℓ¹ specialization of the stationary simulation inequality.
The continuation bound may vary with the remaining horizon; this keeps the
finite-horizon value envelope explicit instead of replacing it by a hidden
global constant.
-/
theorem stationarySimulation_difference_le_of_L1
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : StationaryPolicy State Action)
    (continuationBound : ℕ → ℝ) (transitionError : ℝ)
    (hcontinuation : ∀ remaining state,
      |stationaryHorizonValue secondTransition reward policy remaining state| ≤
        continuationBound remaining)
    (htransition : ∀ state action,
      pmfL1Error (firstTransition state action) (secondTransition state action) ≤
        transitionError) :
    ∀ horizon state,
      stationaryHorizonValue firstTransition reward policy horizon state -
          stationaryHorizonValue secondTransition reward policy horizon state ≤
        ∑ remaining ∈ Finset.range horizon,
          continuationBound remaining * transitionError := by
  apply stationarySimulation_difference_le_of_transitionResidual
    firstTransition secondTransition reward policy
    (fun remaining => continuationBound remaining * transitionError)
  intro remaining state action
  have hbound_nonneg : 0 ≤ continuationBound remaining := by
    linarith [abs_nonneg (stationaryHorizonValue secondTransition reward policy remaining state),
      hcontinuation remaining state]
  calc
    pmfExp (firstTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining) -
        pmfExp (secondTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining) ≤
      |pmfExp (firstTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining) -
        pmfExp (secondTransition state action)
          (stationaryHorizonValue secondTransition reward policy remaining)| :=
        le_abs_self _
    _ ≤ continuationBound remaining *
        pmfL1Error (firstTransition state action) (secondTransition state action) :=
      abs_pmfExp_sub_le_bound_mul_pmfL1Error
        (firstTransition state action) (secondTransition state action)
        (stationaryHorizonValue secondTransition reward policy remaining)
        (continuationBound remaining) (hcontinuation remaining)
    _ ≤ continuationBound remaining * transitionError :=
      mul_le_mul_of_nonneg_left (htransition state action) hbound_nonneg

/-!
## Time-indexed policies

The transition kernel and state-action reward remain stationary, as in
Wu--Sun's model, but a policy may depend on the stage.  Keeping that stage
explicit is the finite discrete counterpart of the time-indexed values in
Lemma D.2.
-/

/-- A randomized policy whose action law may depend on the current stage. -/
abbrev TimeIndexedPolicy (State Action : Type*) :=
  StageIndexedPolicy State Action

/-- One Bellman step at a specified stage for a time-indexed policy. -/
noncomputable def timeIndexedBellmanStep
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time : ℕ) (continuation : State → ℝ) (state : State) : ℝ :=
  pmfExp (policy time state) fun action =>
    reward state action + pmfExp (transition state action) continuation

/--
The value with `remaining` stages left, starting at the stated absolute time.
The terminal continuation is zero.
-/
noncomputable def timeIndexedHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (startTime : ℕ) : ℕ → State → ℝ
  | 0 => fun _ => 0
  | remaining + 1 => fun state =>
      timeIndexedBellmanStep transition reward policy startTime
        (timeIndexedHorizonValue transition reward policy (startTime + 1) remaining) state

@[simp] theorem timeIndexedHorizonValue_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (startTime : ℕ) (state : State) :
    timeIndexedHorizonValue transition reward policy startTime 0 state = 0 :=
  rfl

@[simp] theorem timeIndexedHorizonValue_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (startTime remaining : ℕ) (state : State) :
    timeIndexedHorizonValue transition reward policy startTime (remaining + 1) state =
      timeIndexedBellmanStep transition reward policy startTime
        (timeIndexedHorizonValue transition reward policy (startTime + 1) remaining) state :=
  rfl

/-- The time-indexed Bellman step is monotone in its continuation value. -/
theorem timeIndexedBellmanStep_mono
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time : ℕ) {first second : State → ℝ}
    (hcontinuation : ∀ state, first state ≤ second state) (state : State) :
    timeIndexedBellmanStep transition reward policy time first state ≤
      timeIndexedBellmanStep transition reward policy time second state := by
  unfold timeIndexedBellmanStep
  apply FiniteMarkovKernel.pmfExp_mono
  intro action
  exact add_le_add_right
    (FiniteMarkovKernel.pmfExp_mono (transition state action) hcontinuation) _

/-- Adding a constant to a time-indexed continuation adds that constant after one step. -/
theorem timeIndexedBellmanStep_add_constant
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time : ℕ) (continuation : State → ℝ) (constant : ℝ) (state : State) :
    timeIndexedBellmanStep transition reward policy time
        (fun nextState => continuation nextState + constant) state =
      timeIndexedBellmanStep transition reward policy time continuation state + constant := by
  unfold timeIndexedBellmanStep
  calc
    pmfExp (policy time state) (fun action => reward state action +
        pmfExp (transition state action) (fun nextState => continuation nextState + constant)) =
      pmfExp (policy time state) (fun action => reward state action +
        (pmfExp (transition state action) continuation + constant)) := by
          apply pmfExp_congr
          intro action
          rw [pmfExp_add, pmfExp_const]
    _ = pmfExp (policy time state) (fun action =>
        (reward state action + pmfExp (transition state action) continuation) + constant) := by
          apply pmfExp_congr
          intro action
          ring
    _ = pmfExp (policy time state) (fun action =>
        reward state action + pmfExp (transition state action) continuation) +
        pmfExp (policy time state) (fun _ => constant) := by
          rw [pmfExp_add]
    _ = timeIndexedBellmanStep transition reward policy time continuation state + constant := by
          rw [pmfExp_const]
          rfl

/-- A uniform actionwise residual lifts through the stage-specific policy mixture. -/
theorem timeIndexedBellmanStep_sub_le_of_uniformTransitionResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time : ℕ) (continuation : State → ℝ) (error : ℝ)
    (hresidual : ∀ state action,
      pmfExp (firstTransition state action) continuation -
          pmfExp (secondTransition state action) continuation ≤ error)
    (state : State) :
    timeIndexedBellmanStep firstTransition reward policy time continuation state -
        timeIndexedBellmanStep secondTransition reward policy time continuation state ≤ error := by
  unfold timeIndexedBellmanStep
  rw [← pmfExp_sub]
  calc
    pmfExp (policy time state) (fun action =>
        (reward state action + pmfExp (firstTransition state action) continuation) -
          (reward state action + pmfExp (secondTransition state action) continuation)) =
      pmfExp (policy time state) (fun action =>
        pmfExp (firstTransition state action) continuation -
          pmfExp (secondTransition state action) continuation) := by
          apply pmfExp_congr
          intro action
          ring
    _ ≤ error :=
      FiniteMDP.pmfExp_le_const (policy time state) fun action => hresidual state action

/--
The recursive stage-indexed accumulation of one-step simulation residuals.
At `(startTime, remaining + 1)`, it records the current residual with
`remaining` continuation stages and then advances one stage.
-/
def timeIndexedResidualTotal (error : ℕ → ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | startTime, remaining + 1 =>
      error startTime remaining + timeIndexedResidualTotal error (startTime + 1) remaining

@[simp] theorem timeIndexedResidualTotal_zero (error : ℕ → ℕ → ℝ) (startTime : ℕ) :
    timeIndexedResidualTotal error startTime 0 = 0 :=
  rfl

@[simp] theorem timeIndexedResidualTotal_succ (error : ℕ → ℕ → ℝ)
    (startTime remaining : ℕ) :
    timeIndexedResidualTotal error startTime (remaining + 1) =
      error startTime remaining + timeIndexedResidualTotal error (startTime + 1) remaining :=
  rfl

/-- The next-state law after one stage of a policy rollout. -/
noncomputable def timeIndexedAdvanceStateLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) (initial : PMF State) (time : ℕ) : PMF State :=
  initial.bind fun state =>
    (policy time state).bind fun action => transition state action

/--
The one-step discrepancy in the estimated continuation value at a state-action
pair.  This is the inner expression in Wu--Sun Lemma D.2.
-/
noncomputable def timeIndexedLocalTransitionResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) (action : Action) : ℝ :=
  pmfExp (firstTransition state action)
      (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) -
    pmfExp (secondTransition state action)
      (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining)

/--
The true-transition, policy-rollout accumulation of local simulation
residuals.  Its recursive initial law is exactly the next-state law of the
first transition model, so this is the finite-PMF occupancy form rather than
a uniform state-action relaxation.
-/
noncomputable def timeIndexedOccupancyResidualTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      (pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action =>
          timeIndexedLocalTransitionResidual firstTransition secondTransition reward policy
            startTime remaining state action) +
        timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining

@[simp] theorem timeIndexedOccupancyResidualTotal_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (initial : PMF State) (startTime : ℕ) :
    timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
      initial startTime 0 = 0 :=
  rfl

@[simp] theorem timeIndexedOccupancyResidualTotal_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (initial : PMF State) (startTime remaining : ℕ) :
    timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
      initial startTime (remaining + 1) =
      pmfExp initial (fun state =>
        pmfExp (policy startTime state) fun action =>
          timeIndexedLocalTransitionResidual firstTransition secondTransition reward policy
            startTime remaining state action)
      + timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining := by
  simp [timeIndexedOccupancyResidualTotal]

/--
Separating a Bellman-step difference into its estimated-continuation transition
residual and the propagated continuation-value difference.
-/
theorem timeIndexedBellmanStep_sub_decompose
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (time : ℕ) (firstContinuation secondContinuation : State → ℝ) (state : State) :
    timeIndexedBellmanStep firstTransition reward policy time firstContinuation state -
        timeIndexedBellmanStep secondTransition reward policy time secondContinuation state =
      pmfExp (policy time state) (fun action =>
        pmfExp (firstTransition state action) secondContinuation -
          pmfExp (secondTransition state action) secondContinuation) +
        pmfExp (policy time state) (fun action =>
          pmfExp (firstTransition state action)
            (fun nextState => firstContinuation nextState - secondContinuation nextState)) := by
  unfold timeIndexedBellmanStep
  rw [← pmfExp_sub]
  calc
    pmfExp (policy time state) (fun action =>
        (reward state action + pmfExp (firstTransition state action) firstContinuation) -
          (reward state action + pmfExp (secondTransition state action) secondContinuation)) =
      pmfExp (policy time state) (fun action =>
        (pmfExp (firstTransition state action) secondContinuation -
          pmfExp (secondTransition state action) secondContinuation) +
          pmfExp (firstTransition state action)
            (fun nextState => firstContinuation nextState - secondContinuation nextState)) := by
          apply pmfExp_congr
          intro action
          rw [pmfExp_sub]
          ring
    _ = pmfExp (policy time state) (fun action =>
        pmfExp (firstTransition state action) secondContinuation -
          pmfExp (secondTransition state action) secondContinuation) +
        pmfExp (policy time state) (fun action =>
          pmfExp (firstTransition state action)
            (fun nextState => firstContinuation nextState - secondContinuation nextState)) := by
          rw [pmfExp_add]

/--
Finite-PMF occupancy simulation inequality: averaging the value difference
under an initial law is bounded by the recursively accumulated local residuals
along the first transition model's policy rollout.  This is the discrete
counterpart of the first inequality in Wu--Sun Lemma D.2.
-/
theorem timeIndexedExpectedSimulation_difference_le_of_occupancyResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      pmfExp initial (timeIndexedHorizonValue firstTransition reward policy startTime horizon) -
          pmfExp initial (timeIndexedHorizonValue secondTransition reward policy startTime horizon) ≤
        timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
          initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp [timeIndexedHorizonValue, timeIndexedOccupancyResidualTotal]
  | succ horizon ih =>
      calc
        pmfExp initial
            (timeIndexedHorizonValue firstTransition reward policy startTime (horizon + 1)) -
          pmfExp initial
            (timeIndexedHorizonValue secondTransition reward policy startTime (horizon + 1)) =
          pmfExp initial (fun state =>
            timeIndexedBellmanStep firstTransition reward policy startTime
                (timeIndexedHorizonValue firstTransition reward policy (startTime + 1) horizon) state -
              timeIndexedBellmanStep secondTransition reward policy startTime
                (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state) := by
                rw [← pmfExp_sub]
                rfl
        _ = pmfExp initial (fun state =>
            pmfExp (policy startTime state) (fun action =>
              timeIndexedLocalTransitionResidual firstTransition secondTransition reward policy
                startTime horizon state action) +
              pmfExp (policy startTime state) (fun action =>
                pmfExp (firstTransition state action) (fun nextState =>
                  timeIndexedHorizonValue firstTransition reward policy (startTime + 1) horizon nextState -
                    timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon nextState))) := by
                apply pmfExp_congr
                intro state
                exact timeIndexedBellmanStep_sub_decompose
                  firstTransition secondTransition reward policy startTime
                  (timeIndexedHorizonValue firstTransition reward policy (startTime + 1) horizon)
                  (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state
        _ = (pmfExp initial (fun state =>
            pmfExp (policy startTime state) (fun action =>
              timeIndexedLocalTransitionResidual firstTransition secondTransition reward policy
                startTime horizon state action)) +
            pmfExp (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (fun nextState =>
              timeIndexedHorizonValue firstTransition reward policy (startTime + 1) horizon nextState -
                timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon nextState)) := by
                rw [pmfExp_add]
                unfold timeIndexedAdvanceStateLaw
                rw [pmfExp_bind]
                congr 1
                apply pmfExp_congr
                intro state
                rw [pmfExp_bind]
        _ ≤ (pmfExp initial (fun state =>
            pmfExp (policy startTime state) (fun action =>
              timeIndexedLocalTransitionResidual firstTransition secondTransition reward policy
                startTime horizon state action)) +
            timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
              (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1) horizon) := by
                rw [pmfExp_sub]
                linarith [
                  ih (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)]
        _ = timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
              initial startTime (horizon + 1) := by
                rw [timeIndexedOccupancyResidualTotal_succ]

/--
The occupancy-weighted finite-PMF ℓ¹ transition-error total.  The value bound
is indexed by the current stage and remaining continuation horizon, while the
state-action expectation follows the first transition model's rollout.
-/
noncomputable def timeIndexedOccupancyL1Total
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) (continuationBound : ℕ → ℕ → ℝ)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      (pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action =>
          continuationBound startTime remaining *
            pmfL1Error (firstTransition state action) (secondTransition state action)) +
        timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining

@[simp] theorem timeIndexedOccupancyL1Total_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) (continuationBound : ℕ → ℕ → ℝ)
    (initial : PMF State) (startTime remaining : ℕ) :
    timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
      initial startTime (remaining + 1) =
      (pmfExp initial (fun state =>
        pmfExp (policy startTime state) fun action =>
          continuationBound startTime remaining *
            pmfL1Error (firstTransition state action) (secondTransition state action)) +
        timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining) := by
  simp [timeIndexedOccupancyL1Total]

/--
The occupancy residual total is bounded by its finite-PMF ℓ¹ counterpart when
the estimated continuation values satisfy the supplied stage-indexed bound.
-/
theorem timeIndexedOccupancyResidualTotal_le_occupancyL1Total
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (continuationBound : ℕ → ℕ → ℝ)
    (hcontinuation : ∀ time remaining state,
      |timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state| ≤
        continuationBound time remaining) :
    ∀ (initial : PMF State) startTime horizon,
      timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
        initial startTime horizon ≤
      timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
        initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp [timeIndexedOccupancyResidualTotal, timeIndexedOccupancyL1Total]
  | succ horizon ih =>
      rw [timeIndexedOccupancyResidualTotal_succ, timeIndexedOccupancyL1Total_succ]
      apply add_le_add
      · apply FiniteMarkovKernel.pmfExp_mono
        intro state
        apply FiniteMarkovKernel.pmfExp_mono
        intro action
        unfold timeIndexedLocalTransitionResidual
        calc
          pmfExp (firstTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) -
            pmfExp (secondTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) ≤
            |pmfExp (firstTransition state action)
                (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) -
              pmfExp (secondTransition state action)
                (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon)| :=
              le_abs_self _
          _ ≤ continuationBound startTime horizon *
              pmfL1Error (firstTransition state action) (secondTransition state action) :=
            abs_pmfExp_sub_le_bound_mul_pmfL1Error
              (firstTransition state action) (secondTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon)
              (continuationBound startTime horizon) (hcontinuation startTime horizon)
      · exact ih (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)

/--
The finite-PMF occupancy-weighted simulation bound.  It follows the first
transition model's policy rollout and is therefore the discrete ℓ¹ analogue of
the two inequalities in Wu--Sun Lemma D.2.
-/
theorem timeIndexedExpectedSimulation_difference_le_of_occupancyL1
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (continuationBound : ℕ → ℕ → ℝ)
    (hcontinuation : ∀ time remaining state,
      |timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state| ≤
        continuationBound time remaining)
    (initial : PMF State) (startTime horizon : ℕ) :
    pmfExp initial (timeIndexedHorizonValue firstTransition reward policy startTime horizon) -
        pmfExp initial (timeIndexedHorizonValue secondTransition reward policy startTime horizon) ≤
      timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
        initial startTime horizon := by
  calc
    pmfExp initial (timeIndexedHorizonValue firstTransition reward policy startTime horizon) -
        pmfExp initial (timeIndexedHorizonValue secondTransition reward policy startTime horizon) ≤
      timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
        initial startTime horizon :=
      timeIndexedExpectedSimulation_difference_le_of_occupancyResidual
        firstTransition secondTransition reward policy initial startTime horizon
    _ ≤ timeIndexedOccupancyL1Total firstTransition secondTransition policy continuationBound
        initial startTime horizon :=
      timeIndexedOccupancyResidualTotal_le_occupancyL1Total
        firstTransition secondTransition reward policy continuationBound hcontinuation
        initial startTime horizon

/--
The occupancy-weighted total-variation transition-error accumulation.  The
multiplier is the span of the estimated continuation value, matching the
standard total-variation convention rather than the looser absolute-value
ℓ¹ bound.
-/
noncomputable def timeIndexedOccupancyTVTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action)
    (lower upper : ℕ → ℕ → ℝ)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      (pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action =>
          (upper startTime remaining - lower startTime remaining) *
            pmfTotalVariation (firstTransition state action) (secondTransition state action)) +
        timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining

@[simp] theorem timeIndexedOccupancyTVTotal_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) (lower upper : ℕ → ℕ → ℝ)
    (initial : PMF State) (startTime remaining : ℕ) :
    timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
      initial startTime (remaining + 1) =
      (pmfExp initial (fun state =>
        pmfExp (policy startTime state) fun action =>
          (upper startTime remaining - lower startTime remaining) *
            pmfTotalVariation (firstTransition state action) (secondTransition state action)) +
        timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          remaining) := by
  simp [timeIndexedOccupancyTVTotal]

/--
An occupancy-weighted total-variation accumulation is nonnegative whenever
each supplied continuation span is nonnegative.
-/
theorem timeIndexedOccupancyTVTotal_nonneg
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) (lower upper : ℕ → ℕ → ℝ)
    (hspan : ∀ time remaining, 0 ≤ upper time remaining - lower time remaining) :
    ∀ (initial : PMF State) startTime horizon,
      0 ≤ timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
        initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp [timeIndexedOccupancyTVTotal]
  | succ horizon ih =>
      rw [timeIndexedOccupancyTVTotal_succ]
      apply add_nonneg
      · apply pmfExp_nonneg_of_forall_nonneg
        intro state
        apply pmfExp_nonneg_of_forall_nonneg
        intro action
        exact mul_nonneg (hspan startTime horizon) (by
          rw [pmfTotalVariation_eq_half_pmfL1Error]
          exact div_nonneg (pmfL1Error_nonneg _ _) (by norm_num))
      · exact ih (timeIndexedAdvanceStateLaw firstTransition policy initial startTime)
          (startTime + 1)

/--
Replacing the remaining-horizon continuation span by the full horizon gives
the coarser finite total-variation accumulation used in simulation bounds.
-/
theorem timeIndexedOccupancyTVTotal_remainingSpan_le_horizon_mul_unit
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (policy : TimeIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      timeIndexedOccupancyTVTotal firstTransition secondTransition policy
          (fun _ _ => 0) (fun _ remaining => (remaining : ℝ)) initial startTime horizon ≤
        (horizon : ℝ) *
          timeIndexedOccupancyTVTotal firstTransition secondTransition policy
            (fun _ _ => 0) (fun _ _ => 1) initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp [timeIndexedOccupancyTVTotal]
  | succ horizon ih =>
      rw [timeIndexedOccupancyTVTotal_succ, timeIndexedOccupancyTVTotal_succ]
      have hcurrent :
          pmfExp initial (fun state =>
            pmfExp (policy startTime state) fun action =>
              ((horizon : ℝ) - 0) *
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) =
            (horizon : ℝ) * pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) := by
        simp only [sub_zero]
        calc
          pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                (horizon : ℝ) * pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) =
              pmfExp initial (fun state => (horizon : ℝ) *
                pmfExp (policy startTime state) fun action =>
                  pmfTotalVariation (firstTransition state action)
                    (secondTransition state action)) := by
              apply pmfExp_congr
              intro state
              exact pmfExp_const_mul (policy startTime state) (horizon : ℝ) _
          _ = (horizon : ℝ) * pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) :=
            pmfExp_const_mul initial (horizon : ℝ) _
      have htail := ih
        (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
      have hunit_nonneg :
          0 ≤ timeIndexedOccupancyTVTotal firstTransition secondTransition policy
            (fun _ _ => 0) (fun _ _ => 1)
            (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
            horizon :=
        timeIndexedOccupancyTVTotal_nonneg firstTransition secondTransition policy
          (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => by norm_num)
          (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
          horizon
      have hfirst_nonneg :
          0 ≤ pmfExp initial (fun state =>
            pmfExp (policy startTime state) fun action =>
              pmfTotalVariation (firstTransition state action)
                (secondTransition state action)) := by
        apply pmfExp_nonneg_of_forall_nonneg
        intro state
        apply pmfExp_nonneg_of_forall_nonneg
        intro action
        rw [pmfTotalVariation_eq_half_pmfL1Error]
        exact div_nonneg (pmfL1Error_nonneg _ _) (by norm_num)
      calc
        pmfExp initial (fun state =>
            pmfExp (policy startTime state) fun action =>
              ((horizon : ℝ) - 0) *
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) +
            timeIndexedOccupancyTVTotal firstTransition secondTransition policy
              (fun _ _ => 0) (fun _ remaining => (remaining : ℝ))
              (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
              horizon ≤
            (horizon : ℝ) * pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) +
              (horizon : ℝ) * timeIndexedOccupancyTVTotal
                firstTransition secondTransition policy (fun _ _ => 0) (fun _ _ => 1)
                (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
                horizon := by
              rw [hcurrent]
              exact add_le_add_right htail _
        _ = (horizon : ℝ) *
            (pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) +
              timeIndexedOccupancyTVTotal firstTransition secondTransition policy
                (fun _ _ => 0) (fun _ _ => 1)
                (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
                horizon) := by ring
        _ ≤ ((horizon + 1 : ℕ) : ℝ) *
            (pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) +
              timeIndexedOccupancyTVTotal firstTransition secondTransition policy
                (fun _ _ => 0) (fun _ _ => 1)
                (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
                horizon) := by
              push_cast
              nlinarith
        _ = ((horizon + 1 : ℕ) : ℝ) *
            (pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                (1 - 0) * pmfTotalVariation (firstTransition state action)
                  (secondTransition state action)) +
              timeIndexedOccupancyTVTotal firstTransition secondTransition policy
                (fun _ _ => 0) (fun _ _ => 1)
                (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)
                horizon) := by norm_num

/--
The true-rollout residual total is bounded by the corresponding
occupancy-weighted total-variation total when the estimated continuation lies
in the supplied stage-indexed interval.
-/
theorem timeIndexedOccupancyResidualTotal_le_occupancyTVTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (lower upper : ℕ → ℕ → ℝ)
    (hspan : ∀ time remaining, lower time remaining ≤ upper time remaining)
    (hcontinuationLower : ∀ time remaining state,
      lower time remaining ≤
        timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state)
    (hcontinuationUpper : ∀ time remaining state,
      timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state ≤
        upper time remaining) :
    ∀ (initial : PMF State) startTime horizon,
      timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
        initial startTime horizon ≤
      timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
        initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp [timeIndexedOccupancyResidualTotal, timeIndexedOccupancyTVTotal]
  | succ horizon ih =>
      rw [timeIndexedOccupancyResidualTotal_succ, timeIndexedOccupancyTVTotal_succ]
      apply add_le_add
      · apply FiniteMarkovKernel.pmfExp_mono
        intro state
        apply FiniteMarkovKernel.pmfExp_mono
        intro action
        unfold timeIndexedLocalTransitionResidual
        calc
          pmfExp (firstTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) -
            pmfExp (secondTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) ≤
            |pmfExp (firstTransition state action)
                (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) -
              pmfExp (secondTransition state action)
                (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon)| :=
              le_abs_self _
          _ ≤ (upper startTime horizon - lower startTime horizon) *
              pmfTotalVariation (firstTransition state action) (secondTransition state action) :=
            abs_pmfExp_sub_le_span_mul_pmfTotalVariation
              (firstTransition state action) (secondTransition state action)
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon)
              (lower startTime horizon) (upper startTime horizon)
              (hspan startTime horizon) (hcontinuationLower startTime horizon)
              (hcontinuationUpper startTime horizon)
      · exact ih (timeIndexedAdvanceStateLaw firstTransition policy initial startTime) (startTime + 1)

/--
Finite-PMF total-variation form of the occupancy simulation inequality.  It
follows the first transition model's rollout, with the standard span-times-TV
one-step estimate used in Wu--Sun Lemma D.2.
-/
theorem timeIndexedExpectedSimulation_difference_le_of_occupancyTV
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (lower upper : ℕ → ℕ → ℝ)
    (hspan : ∀ time remaining, lower time remaining ≤ upper time remaining)
    (hcontinuationLower : ∀ time remaining state,
      lower time remaining ≤
        timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state)
    (hcontinuationUpper : ∀ time remaining state,
      timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state ≤
        upper time remaining)
    (initial : PMF State) (startTime horizon : ℕ) :
    pmfExp initial (timeIndexedHorizonValue firstTransition reward policy startTime horizon) -
        pmfExp initial (timeIndexedHorizonValue secondTransition reward policy startTime horizon) ≤
      timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
        initial startTime horizon := by
  calc
    pmfExp initial (timeIndexedHorizonValue firstTransition reward policy startTime horizon) -
        pmfExp initial (timeIndexedHorizonValue secondTransition reward policy startTime horizon) ≤
      timeIndexedOccupancyResidualTotal firstTransition secondTransition reward policy
        initial startTime horizon :=
      timeIndexedExpectedSimulation_difference_le_of_occupancyResidual
        firstTransition secondTransition reward policy initial startTime horizon
    _ ≤ timeIndexedOccupancyTVTotal firstTransition secondTransition policy lower upper
        initial startTime horizon :=
      timeIndexedOccupancyResidualTotal_le_occupancyTVTotal
        firstTransition secondTransition reward policy lower upper hspan
        hcontinuationLower hcontinuationUpper initial startTime horizon

/--
A finite, time-indexed simulation inequality for a stationary transition model
and a possibly nonstationary policy.  This is the pointwise, uniform-residual
specialization of the stage-indexed telescoping used in Wu--Sun Lemma D.2; it
does not identify the source's occupancy-weighted `dTV` convention.
-/
theorem timeIndexedSimulation_difference_le_of_transitionResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (error : ℕ → ℕ → ℝ)
    (hresidual : ∀ time remaining state action,
      pmfExp (firstTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) -
        pmfExp (secondTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) ≤
        error time remaining) :
    ∀ startTime horizon state,
      timeIndexedHorizonValue firstTransition reward policy startTime horizon state -
          timeIndexedHorizonValue secondTransition reward policy startTime horizon state ≤
        timeIndexedResidualTotal error startTime horizon := by
  intro startTime horizon
  induction horizon generalizing startTime with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      calc
        timeIndexedHorizonValue firstTransition reward policy startTime (horizon + 1) state -
            timeIndexedHorizonValue secondTransition reward policy startTime (horizon + 1) state =
          timeIndexedBellmanStep firstTransition reward policy startTime
              (timeIndexedHorizonValue firstTransition reward policy (startTime + 1) horizon) state -
            timeIndexedBellmanStep secondTransition reward policy startTime
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state := by
                rfl
        _ ≤ timeIndexedBellmanStep firstTransition reward policy startTime
              (fun nextState =>
                timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon nextState +
                  timeIndexedResidualTotal error (startTime + 1) horizon) state -
            timeIndexedBellmanStep secondTransition reward policy startTime
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state := by
                exact sub_le_sub_right
                  (timeIndexedBellmanStep_mono firstTransition reward policy startTime
                    (fun nextState => by linarith [ih (startTime + 1) nextState]) state) _
        _ = (timeIndexedBellmanStep firstTransition reward policy startTime
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state -
            timeIndexedBellmanStep secondTransition reward policy startTime
              (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon) state) +
              timeIndexedResidualTotal error (startTime + 1) horizon := by
                rw [timeIndexedBellmanStep_add_constant]
                ring
        _ ≤ error startTime horizon + timeIndexedResidualTotal error (startTime + 1) horizon := by
                linarith [
                  timeIndexedBellmanStep_sub_le_of_uniformTransitionResidual
                    firstTransition secondTransition reward policy startTime
                    (timeIndexedHorizonValue secondTransition reward policy (startTime + 1) horizon)
                    (error startTime horizon) (hresidual startTime horizon) state]
        _ = timeIndexedResidualTotal error startTime (horizon + 1) := by
                rfl

/-- The time-indexed horizon value is nonnegative for nonnegative rewards. -/
theorem timeIndexedHorizonValue_nonneg_of_reward_nonneg
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (hreward : ∀ state action, 0 ≤ reward state action) :
    ∀ startTime horizon state,
      0 ≤ timeIndexedHorizonValue transition reward policy startTime horizon state := by
  intro startTime horizon
  induction horizon generalizing startTime with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      unfold timeIndexedHorizonValue timeIndexedBellmanStep
      apply pmfExp_nonneg_of_forall_nonneg
      intro action
      apply add_nonneg (hreward state action)
      apply pmfExp_nonneg_of_forall_nonneg
      intro nextState
      exact ih (startTime + 1) nextState

/-- Unit-bounded rewards give a remaining-horizon bound, at every start time. -/
theorem timeIndexedHorizonValue_le_horizon_of_reward_le_one
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (hreward : ∀ state action, reward state action ≤ 1) :
    ∀ startTime horizon state,
      timeIndexedHorizonValue transition reward policy startTime horizon state ≤ (horizon : ℝ) := by
  intro startTime horizon
  induction horizon generalizing startTime with
  | zero =>
      intro state
      simp
  | succ horizon ih =>
      intro state
      unfold timeIndexedHorizonValue timeIndexedBellmanStep
      apply FiniteMDP.pmfExp_le_const
      intro action
      calc
        reward state action +
            pmfExp (transition state action)
              (timeIndexedHorizonValue transition reward policy (startTime + 1) horizon) ≤
          1 + (horizon : ℝ) := by
            exact add_le_add (hreward state action)
              (FiniteMDP.pmfExp_le_const (transition state action)
                fun nextState => ih (startTime + 1) nextState)
        _ = ((horizon + 1 : ℕ) : ℝ) := by
            push_cast
            ring

/--
Finite-PMF ℓ¹ version of the time-indexed simulation inequality.  Its error
schedule remains explicit in both absolute time and remaining horizon.
-/
theorem timeIndexedSimulation_difference_le_of_L1
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (firstTransition secondTransition : StationaryTransitionModel State Action)
    (reward : State → Action → ℝ) (policy : TimeIndexedPolicy State Action)
    (continuationBound transitionError : ℕ → ℕ → ℝ)
    (hcontinuation : ∀ time remaining state,
      |timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state| ≤
        continuationBound time remaining)
    (htransition : ∀ time remaining state action,
      pmfL1Error (firstTransition state action) (secondTransition state action) ≤
        transitionError time remaining) :
    ∀ startTime horizon state,
      timeIndexedHorizonValue firstTransition reward policy startTime horizon state -
          timeIndexedHorizonValue secondTransition reward policy startTime horizon state ≤
        timeIndexedResidualTotal
          (fun time remaining => continuationBound time remaining * transitionError time remaining)
          startTime horizon := by
  apply timeIndexedSimulation_difference_le_of_transitionResidual
    firstTransition secondTransition reward policy
    (fun time remaining => continuationBound time remaining * transitionError time remaining)
  intro time remaining state action
  have hbound_nonneg : 0 ≤ continuationBound time remaining := by
    linarith [
      abs_nonneg (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining state),
      hcontinuation time remaining state]
  calc
    pmfExp (firstTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) -
        pmfExp (secondTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) ≤
      |pmfExp (firstTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining) -
        pmfExp (secondTransition state action)
          (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining)| :=
        le_abs_self _
    _ ≤ continuationBound time remaining *
        pmfL1Error (firstTransition state action) (secondTransition state action) :=
      abs_pmfExp_sub_le_bound_mul_pmfL1Error
        (firstTransition state action) (secondTransition state action)
        (timeIndexedHorizonValue secondTransition reward policy (time + 1) remaining)
        (continuationBound time remaining) (hcontinuation time remaining)
    _ ≤ continuationBound time remaining * transitionError time remaining :=
      mul_le_mul_of_nonneg_left (htransition time remaining state action) hbound_nonneg

end PreferenceRL

end AppliedModelingLib
