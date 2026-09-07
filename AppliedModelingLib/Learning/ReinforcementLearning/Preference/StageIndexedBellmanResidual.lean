import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedPerformanceDifference
import Mathlib.Tactic

/-!
# Stage-indexed Bellman residuals

This module gives the finite-PMF telescoping identity behind regret
decompositions for adaptive planning algorithms.  A candidate value function
need not be a true value function: its difference from a policy's realized
value is exactly the policy-occupancy total of its one-step Bellman residuals.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- One policy Bellman step applied to an arbitrary stage-indexed candidate value. -/
noncomputable def stageIndexedPolicyBellmanStep
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (time remaining : ℕ) (state : State) : ℝ :=
  pmfExp (policy time state) (fun action =>
    reward time state action +
      pmfExp (transition time state action) (candidate (time + 1) remaining))

/-- The amount by which an arbitrary candidate misses its policy Bellman equation. -/
noncomputable def stageIndexedBellmanResidual
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (time remaining : ℕ) (state : State) : ℝ :=
  candidate time (remaining + 1) state -
    stageIndexedPolicyBellmanStep transition reward policy candidate time remaining state

/-- A finite candidate that is below its policy Bellman step on one terminal
diagonal is bounded by that policy's finite-horizon value on the same
diagonal.  This is the backward comparison principle for a source proof that
controls a plan only at its remaining-horizon stages. -/
theorem candidate_le_stageIndexedStateValue_of_subBellman_of_terminalTime
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ) (terminalTime : ℕ)
    (hterminal : ∀ time state, candidate time 0 state ≤ 0)
    (hsub : ∀ time remaining state, time + (remaining + 1) = terminalTime →
      candidate time (remaining + 1) state ≤
        stageIndexedPolicyBellmanStep transition reward policy candidate time remaining state) :
    ∀ time remaining state, time + remaining = terminalTime →
      candidate time remaining state ≤
        stageIndexedStateValue transition reward policy time remaining state := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state _
      simpa [stageIndexedStateValue, stageIndexedPolicyValue] using hterminal time state
  | succ remaining ih =>
      intro state htime
      rw [stageIndexedStateValue_succ]
      calc
        candidate time (remaining + 1) state ≤
            stageIndexedPolicyBellmanStep transition reward policy candidate time remaining state :=
          hsub time remaining state (by omega)
        _ ≤ pmfExp (policy time state) (fun action =>
            reward time state action +
              pmfExp (transition time state action)
                (stageIndexedStateValue transition reward policy (time + 1) remaining)) := by
          unfold stageIndexedPolicyBellmanStep
          apply FiniteMarkovKernel.pmfExp_mono
          intro action
          apply add_le_add (le_refl _)
          apply FiniteMarkovKernel.pmfExp_mono
          intro next
          exact ih (time + 1) next (by omega)

/-- The policy-occupancy total of Bellman residuals over a finite horizon. -/
noncomputable def stageIndexedBellmanResidualTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      pmfExp initial
        (stageIndexedBellmanResidual transition reward policy candidate startTime remaining) +
      stageIndexedBellmanResidualTotal transition reward policy candidate
        (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1) remaining

/-- The true-policy occupancy total of an arbitrary stage/remaining-state
cost.  This has the same rollout recursion as `stageIndexedBellmanResidualTotal`,
but keeps the integrand explicit so pointwise residual estimates can be
aggregated without redoing the state-law induction. -/
noncomputable def stageIndexedOccupancyCostTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (cost : ℕ → ℕ → State → ℝ)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      pmfExp initial (cost startTime remaining) +
      stageIndexedOccupancyCostTotal transition policy cost
        (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1) remaining

/-- Evaluating a stage-indexed action reward is the same as accumulating its
action expectation under the policy's state occupancy.  This separates a
pointwise action-cost envelope from its finite source-boundary visit-mass
aggregation. -/
theorem stageIndexedPolicyValue_eq_occupancyCostTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedPolicyValue transition reward policy initial startTime horizon =
        stageIndexedOccupancyCostTotal transition policy
          (fun time _remaining state => pmfExp (policy time state) (fun action =>
            reward time state action))
          initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => rfl
  | succ remaining ih =>
      simp only [stageIndexedPolicyValue, stageIndexedOccupancyCostTotal]
      rw [ih]

/-- A pointwise Bellman-residual bound lifts to the corresponding total under
the policy's true state law. -/
theorem stageIndexedBellmanResidualTotal_le_stageIndexedOccupancyCostTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ) (cost : ℕ → ℕ → State → ℝ)
    (hcost : ∀ time remaining state,
      stageIndexedBellmanResidual transition reward policy candidate time remaining state ≤
        cost time remaining state) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime horizon ≤
        stageIndexedOccupancyCostTotal transition policy cost initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedBellmanResidualTotal, stageIndexedOccupancyCostTotal]
  | succ horizon ih =>
      apply add_le_add
      · exact pmfExp_le_pmfExp_of_forall_le initial _ _ (hcost startTime horizon)
      · exact ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)

/-- The same occupancy lift when a finite-horizon candidate is controlled
only on the diagonal reached by a fixed terminal time.  Backward plans often
provide estimates precisely in this form: at source time `time`, there are
`remaining + 1` stages through the common terminal boundary. -/
theorem stageIndexedBellmanResidualTotal_le_stageIndexedOccupancyCostTotal_of_terminalTime
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ) (cost : ℕ → ℕ → State → ℝ) (terminalTime : ℕ)
    (hcost : ∀ time remaining state, time + (remaining + 1) = terminalTime →
      stageIndexedBellmanResidual transition reward policy candidate time remaining state ≤
        cost time remaining state) :
    ∀ (initial : PMF State) (startTime horizon : ℕ), startTime + horizon = terminalTime →
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime horizon ≤
        stageIndexedOccupancyCostTotal transition policy cost initial startTime horizon := by
  intro initial startTime horizon hterminal
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedBellmanResidualTotal, stageIndexedOccupancyCostTotal]
  | succ horizon ih =>
      apply add_le_add
      · exact pmfExp_le_pmfExp_of_forall_le initial _ _
          (fun state => hcost startTime horizon state (by omega))
      · apply ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
        omega

/-- A constant per-stage occupancy cost sums to that constant times the
horizon, independently of the transition model and policy. -/
theorem stageIndexedOccupancyCostTotal_const
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (cost : ℝ) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedOccupancyCostTotal transition policy (fun _ _ _ => cost) initial startTime horizon =
        (horizon : ℝ) * cost := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedOccupancyCostTotal]
  | succ horizon ih =>
      rw [stageIndexedOccupancyCostTotal, pmfExp_const,
        ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)]
      push_cast
      ring

/-- A state-action cost occupancy total expands into the finite sum of the
true state-action laws at each elapsed stage.  This is the action-level form
needed when a Bellman-residual bound is indexed by the selected action rather
than only by the current state. -/
theorem stageIndexedOccupancyCostTotal_eq_sum_stateActionLawFrom
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (actionCost : ℕ → ℕ → State → Action → ℝ) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedOccupancyCostTotal transition policy
        (fun time remaining state =>
          pmfExp (policy time state) (fun action => actionCost time remaining state action))
        initial startTime horizon =
      ∑ elapsed ∈ Finset.range horizon,
        pmfExp
          (stageIndexedStateActionLaw policy
            (stageIndexedStateLawFrom transition policy initial startTime elapsed)
            (startTime + elapsed))
          (fun stateAction =>
            actionCost (startTime + elapsed) (horizon - (elapsed + 1))
              stateAction.1 stateAction.2) := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedOccupancyCostTotal]
  | succ horizon ih =>
      rw [stageIndexedOccupancyCostTotal,
        ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)]
      have hhead :
          pmfExp initial (fun state =>
            pmfExp (policy startTime state) (fun action =>
              actionCost startTime horizon state action)) =
            pmfExp
              (stageIndexedStateActionLaw policy
                (stageIndexedStateLawFrom transition policy initial startTime 0) startTime)
              (fun stateAction => actionCost startTime horizon stateAction.1 stateAction.2) := by
        rw [stageIndexedStateLawFrom_zero]
        unfold stageIndexedStateActionLaw
        rw [pmfExp_bind]
        simp only [pmfExp_map]
      have htail :
          (∑ elapsed ∈ Finset.range horizon,
            pmfExp
              (stageIndexedStateActionLaw policy
                (stageIndexedStateLawFrom transition policy
                  (stageIndexedAdvanceStateLaw transition policy initial startTime)
                  (startTime + 1) elapsed)
                ((startTime + 1) + elapsed))
              (fun stateAction =>
                actionCost ((startTime + 1) + elapsed) (horizon - (elapsed + 1))
                  stateAction.1 stateAction.2)) =
          ∑ elapsed ∈ Finset.range horizon,
            pmfExp
              (stageIndexedStateActionLaw policy
                (stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1))
                (startTime + (elapsed + 1)))
              (fun stateAction =>
                actionCost (startTime + (elapsed + 1))
                  ((horizon + 1) - ((elapsed + 1) + 1))
                  stateAction.1 stateAction.2) := by
        apply Finset.sum_congr rfl
        intro elapsed _
        rw [← stageIndexedStateLawFrom_succ_eq_advanced]
        have htime : (startTime + 1) + elapsed = startTime + (elapsed + 1) := by omega
        have hremaining : horizon - (elapsed + 1) =
            (horizon + 1) - ((elapsed + 1) + 1) := by omega
        rw [htime, hremaining]
      rw [hhead, htail]
      simpa only [Nat.succ_eq_add_one] using
        (sum_range_succ_eq_head_add_shift
          (fun elapsed =>
            pmfExp
              (stageIndexedStateActionLaw policy
                (stageIndexedStateLawFrom transition policy initial startTime elapsed)
                (startTime + elapsed))
              (fun stateAction =>
                actionCost (startTime + elapsed) ((horizon + 1) - (elapsed + 1))
                  stateAction.1 stateAction.2)) horizon)

/-- The finite-state expansion of an action-indexed occupancy total.  This is
the atomwise form of `stageIndexedOccupancyCostTotal_eq_sum_stateActionLawFrom`,
useful when a proof must retain an elapsed-stage-dependent action cost through
a subsequent finite aggregation. -/
theorem stageIndexedOccupancyCostTotal_eq_sum_stateActionLawFrom_finite
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (actionCost : ℕ → ℕ → State → Action → ℝ) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedOccupancyCostTotal transition policy
        (fun time remaining state =>
          pmfExp (policy time state) (fun action => actionCost time remaining state action))
        initial startTime horizon =
      ∑ elapsed ∈ Finset.range horizon, ∑ stateAction : State × Action,
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLawFrom transition policy initial startTime elapsed)
          (startTime + elapsed) stateAction).toReal *
          actionCost (startTime + elapsed) (horizon - (elapsed + 1))
            stateAction.1 stateAction.2 := by
  intro initial startTime horizon
  rw [stageIndexedOccupancyCostTotal_eq_sum_stateActionLawFrom
    transition policy actionCost initial startTime horizon]
  apply Finset.sum_congr rfl
  intro elapsed _
  rfl

/-- Expected candidate value after one true policy step. -/
theorem pmfExp_stageIndexedPolicyBellmanStep_eq_reward_add_advancedCandidate
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (initial : PMF State) (time remaining : ℕ) :
    pmfExp initial
      (stageIndexedPolicyBellmanStep transition reward policy candidate time remaining) =
      pmfExp initial (fun state =>
        pmfExp (policy time state) (fun action => reward time state action)) +
    pmfExp (stageIndexedAdvanceStateLaw transition policy initial time)
        (candidate (time + 1) remaining) := by
  unfold stageIndexedPolicyBellmanStep
  calc
    pmfExp initial (fun state =>
        pmfExp (policy time state) (fun action =>
          reward time state action +
            pmfExp (transition time state action) (candidate (time + 1) remaining))) =
        pmfExp initial (fun state =>
          pmfExp (policy time state) (fun action => reward time state action) +
          pmfExp (policy time state) (fun action =>
            pmfExp (transition time state action) (candidate (time + 1) remaining))) := by
          apply pmfExp_congr
          intro state
          rw [pmfExp_add]
    _ =
        pmfExp initial (fun state =>
          pmfExp (policy time state) (fun action => reward time state action)) +
        pmfExp (stageIndexedAdvanceStateLaw transition policy initial time)
          (candidate (time + 1) remaining) := by
          rw [pmfExp_add]
          unfold stageIndexedAdvanceStateLaw
          congr 1
          symm
          rw [pmfExp_bind]
          apply pmfExp_congr
          intro state
          rw [pmfExp_bind]

/-- Expected residual is candidate value minus its expected policy Bellman step. -/
theorem pmfExp_stageIndexedBellmanResidual_eq_candidate_sub_BellmanStep
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (initial : PMF State) (time remaining : ℕ) :
    pmfExp initial
      (stageIndexedBellmanResidual transition reward policy candidate time remaining) =
      pmfExp initial (candidate time (remaining + 1)) -
        pmfExp initial
          (stageIndexedPolicyBellmanStep transition reward policy candidate time remaining) := by
  unfold stageIndexedBellmanResidual
  rw [pmfExp_sub]

/--
Bellman-residual telescoping under the policy's true state law.

The candidate value only needs a zero terminal boundary.  This is the exact
finite form used when an optimistic planning value is compared with the value
of the policy selected from that planning value.
-/
theorem pmfExp_candidate_sub_stageIndexedPolicyValue_eq_BellmanResidualTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (candidate_terminal : ∀ time state, candidate time 0 state = 0) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      pmfExp initial (candidate startTime horizon) -
        stageIndexedPolicyValue transition reward policy initial startTime horizon =
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      have hterminal : candidate startTime 0 = fun _ => 0 := by
        funext state
        exact candidate_terminal startTime state
      simp [stageIndexedBellmanResidualTotal, hterminal]
  | succ horizon ih =>
      have hpolicyStep :
          stageIndexedPolicyValue transition reward policy initial startTime (horizon + 1) =
            pmfExp initial (fun state =>
              pmfExp (policy startTime state) (fun action => reward startTime state action)) +
            stageIndexedPolicyValue transition reward policy
              (stageIndexedAdvanceStateLaw transition policy initial startTime)
              (startTime + 1) horizon := by
        rw [stageIndexedPolicyValue_succ]
      have hcandidateStep :=
        pmfExp_stageIndexedPolicyBellmanStep_eq_reward_add_advancedCandidate transition reward
          policy candidate initial startTime horizon
      have hresidual :=
        pmfExp_stageIndexedBellmanResidual_eq_candidate_sub_BellmanStep transition reward policy
          candidate initial startTime horizon
      calc
        pmfExp initial (candidate startTime (horizon + 1)) -
            stageIndexedPolicyValue transition reward policy initial startTime (horizon + 1) =
            (pmfExp initial (candidate startTime (horizon + 1)) -
              pmfExp initial
                (stageIndexedPolicyBellmanStep transition reward policy candidate startTime horizon)) +
              (pmfExp (stageIndexedAdvanceStateLaw transition policy initial startTime)
                (candidate (startTime + 1) horizon) -
              stageIndexedPolicyValue transition reward policy
                (stageIndexedAdvanceStateLaw transition policy initial startTime)
                (startTime + 1) horizon) := by
              rw [hpolicyStep, hcandidateStep]
              ring
        _ =
            pmfExp initial
              (stageIndexedBellmanResidual transition reward policy candidate startTime horizon) +
              stageIndexedBellmanResidualTotal transition reward policy candidate
                (stageIndexedAdvanceStateLaw transition policy initial startTime)
                (startTime + 1) horizon := by
              rw [← hresidual,
                ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)]
        _ =
            stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime
              (horizon + 1) := by
              rfl

/--
An optimistic candidate converts the Bellman-residual identity into a regret
upper bound.  The benchmark can be the optimal value at the initial stage;
the theorem intentionally does not assume how the candidate's optimism was
established.
-/
theorem pmfExp_benchmark_sub_stageIndexedPolicyValue_le_BellmanResidualTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (candidate_terminal : ∀ time state, candidate time 0 state = 0)
    (initial : PMF State) (startTime horizon : ℕ) (benchmark : State → ℝ)
    (benchmark_le_candidate : ∀ state, benchmark state ≤ candidate startTime horizon state) :
    pmfExp initial benchmark -
        stageIndexedPolicyValue transition reward policy initial startTime horizon ≤
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime horizon := by
  calc
    pmfExp initial benchmark -
        stageIndexedPolicyValue transition reward policy initial startTime horizon ≤
      pmfExp initial (candidate startTime horizon) -
        stageIndexedPolicyValue transition reward policy initial startTime horizon := by
          exact sub_le_sub_right
            (FiniteMarkovKernel.pmfExp_mono initial benchmark_le_candidate) _
    _ = stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime horizon :=
      pmfExp_candidate_sub_stageIndexedPolicyValue_eq_BellmanResidualTotal transition reward policy
        candidate candidate_terminal initial startTime horizon

/-- A pointwise upper envelope on one-step Bellman residuals bounds their
entire occupancy total by the policy value of that envelope.  This is the
stage-indexed finite-horizon form of the deterministic half of a standard
optimistic-regret decomposition. -/
theorem stageIndexedBellmanResidualTotal_le_policyValue_of_pointwise
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward envelope : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (hresidual : ∀ time remaining state,
      stageIndexedBellmanResidual transition reward policy candidate time remaining state ≤
        pmfExp (policy time state) (envelope time state)) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime
          horizon ≤
        stageIndexedPolicyValue transition envelope policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedBellmanResidualTotal]
  | succ horizon ih =>
      rw [stageIndexedPolicyValue_succ]
      change
        pmfExp initial
            (stageIndexedBellmanResidual transition reward policy candidate startTime horizon) +
          stageIndexedBellmanResidualTotal transition reward policy candidate
            (stageIndexedAdvanceStateLaw transition policy initial startTime)
            (startTime + 1) horizon ≤ _
      exact add_le_add
        (FiniteMarkovKernel.pmfExp_mono initial
          (fun state ↦ hresidual startTime horizon state))
        (ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1))

/-- Diagonal finite-horizon version of
`stageIndexedBellmanResidualTotal_le_policyValue_of_pointwise`.  Only the
residuals actually visited from `startTime` with `horizon` stages remaining
must satisfy the envelope. -/
theorem stageIndexedBellmanResidualTotal_le_policyValue_of_elapsed
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward envelope : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      (∀ elapsed, elapsed < horizon → ∀ state,
        stageIndexedBellmanResidual transition reward policy candidate
            (startTime + elapsed) (horizon - (elapsed + 1)) state ≤
          pmfExp (policy (startTime + elapsed) state)
            (envelope (startTime + elapsed) state)) →
      stageIndexedBellmanResidualTotal transition reward policy candidate initial startTime
          horizon ≤
        stageIndexedPolicyValue transition envelope policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      intro _hresidual
      simp [stageIndexedBellmanResidualTotal]
  | succ horizon ih =>
      intro hresidual
      rw [stageIndexedPolicyValue_succ]
      change
        pmfExp initial
            (stageIndexedBellmanResidual transition reward policy candidate startTime horizon) +
          stageIndexedBellmanResidualTotal transition reward policy candidate
            (stageIndexedAdvanceStateLaw transition policy initial startTime)
            (startTime + 1) horizon ≤ _
      apply add_le_add
      · apply FiniteMarkovKernel.pmfExp_mono initial
        intro state
        simpa using hresidual 0 (by omega) state
      · apply ih
        intro elapsed helapsed state
        have hsource := hresidual (elapsed + 1) (by omega) state
        have htime : startTime + 1 + elapsed = startTime + (elapsed + 1) := by omega
        have hremaining : horizon + 1 - (elapsed + 1 + 1) =
            horizon - (elapsed + 1) := by omega
        simpa [htime, hremaining] using hsource

/-- Diagonal pointwise nonnegativity propagates to the complete finite-horizon
Bellman-residual total. -/
theorem stageIndexedBellmanResidualTotal_nonneg_of_elapsed
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      (∀ elapsed, elapsed < horizon → ∀ state,
        0 ≤ stageIndexedBellmanResidual transition reward policy candidate
          (startTime + elapsed) (horizon - (elapsed + 1)) state) →
      0 ≤ stageIndexedBellmanResidualTotal transition reward policy candidate initial
        startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      intro _hresidual
      simp [stageIndexedBellmanResidualTotal]
  | succ horizon ih =>
      intro hresidual
      change 0 ≤
        pmfExp initial
            (stageIndexedBellmanResidual transition reward policy candidate startTime
              horizon) +
          stageIndexedBellmanResidualTotal transition reward policy candidate
            (stageIndexedAdvanceStateLaw transition policy initial startTime)
            (startTime + 1) horizon
      apply add_nonneg
      · apply pmfExp_nonneg_of_forall_nonneg
        intro state
        simpa using hresidual 0 (by omega) state
      · apply ih
        intro elapsed helapsed state
        have hsource := hresidual (elapsed + 1) (by omega) state
        have htime : startTime + 1 + elapsed = startTime + (elapsed + 1) := by omega
        have hremaining : horizon + 1 - (elapsed + 1 + 1) =
            horizon - (elapsed + 1) := by omega
        simpa [htime, hremaining] using hsource

end PreferenceRL

end AppliedModelingLib
