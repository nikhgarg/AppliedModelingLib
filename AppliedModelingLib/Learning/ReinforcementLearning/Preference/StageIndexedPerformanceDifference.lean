import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedRewardOccupancy
import AppliedModelingLib.Foundations.Probability.MDP
import Mathlib.Tactic

/-!
# Stage-indexed performance differences

The finite-PMF form of the performance-difference identity used in Zhan et
al. (2024), Lemma 10.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- The finite-horizon value of a policy when the current state is fixed. -/
noncomputable def stageIndexedStateValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) : ℝ :=
  stageIndexedPolicyValue transition reward policy (PMF.pure state) time remaining

/-- A policy value under any finite initial law is the expectation of its state values. -/
theorem stageIndexedPolicyValue_eq_pmfExp_stateValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) time remaining,
      stageIndexedPolicyValue transition reward policy initial time remaining =
        pmfExp initial (stageIndexedStateValue transition reward policy time remaining) := by
  intro initial time remaining
  induction remaining generalizing initial time with
  | zero =>
      change 0 = pmfExp initial (fun _ => 0)
      simp
  | succ remaining ih =>
      have hstate : ∀ state,
          stageIndexedStateValue transition reward policy time (remaining + 1) state =
            pmfExp (policy time state) (fun action =>
              reward time state action +
                pmfExp (transition time state action)
                  (stageIndexedStateValue transition reward policy (time + 1) remaining)) := by
        intro state
        unfold stageIndexedStateValue
        rw [stageIndexedPolicyValue_succ, ih]
        simp only [FiniteMDP.pmfExp_pure, stageIndexedAdvanceStateLaw, PMF.pure_bind]
        rw [pmfExp_bind, ← pmfExp_add]
        rfl
      rw [stageIndexedPolicyValue_succ, ih]
      calc
        (pmfExp initial (fun state =>
            pmfExp (policy time state) (fun action => reward time state action)) +
          pmfExp
            (stageIndexedAdvanceStateLaw transition policy initial time)
            (stageIndexedStateValue transition reward policy (time + 1) remaining)) =
            pmfExp initial (fun state =>
              pmfExp (policy time state) (fun action => reward time state action) +
                pmfExp (policy time state) (fun action =>
                  pmfExp (transition time state action)
                    (stageIndexedStateValue transition reward policy (time + 1) remaining))) := by
              unfold stageIndexedAdvanceStateLaw
              rw [pmfExp_bind]
              rw [← pmfExp_add]
              apply pmfExp_congr
              intro state
              rw [pmfExp_bind]
        _ = pmfExp initial
            (stageIndexedStateValue transition reward policy time (remaining + 1)) := by
              apply pmfExp_congr
              intro state
              rw [← pmfExp_add]
              exact (hstate state).symm

/-- A nonnegative scalar bounded by a stage-indexed state value has square
bounded by the horizon times the corresponding squared-reward state value.
This packages the finite Jensen--Cauchy step at the state-value interface. -/
theorem sq_le_horizon_mul_stageIndexedStateValue_sq_reward_of_nonneg_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (time horizon : ℕ) (state : State) (value : ℝ)
    (hvalue_nonneg : 0 ≤ value)
    (hvalue_le : value ≤ stageIndexedStateValue transition reward policy time horizon state) :
    value ^ 2 ≤ (horizon : ℝ) *
      stageIndexedStateValue transition
        (fun localTime localState localAction =>
          (reward localTime localState localAction) ^ 2)
        policy time horizon state := by
  unfold stageIndexedStateValue at hvalue_le ⊢
  have hsq_mono : value ^ 2 ≤
      (stageIndexedPolicyValue transition reward policy (PMF.pure state) time horizon) ^ 2 := by
    nlinarith
  calc
    value ^ 2 ≤
        (stageIndexedPolicyValue transition reward policy (PMF.pure state) time horizon) ^ 2 :=
      hsq_mono
    _ ≤ (horizon : ℝ) * stageIndexedPolicyValue transition
        (fun localTime localState localAction =>
          (reward localTime localState localAction) ^ 2)
        policy (PMF.pure state) time horizon :=
      stageIndexedPolicyValue_sq_le_horizon_mul_sq_reward
        transition reward policy (PMF.pure state) time horizon

/-- Summing the squared continuation value over every state law of one
finite rollout costs at most two horizon factors times the occupancy value of
the squared reward.  This is the reusable finite tail-sum form of the
Jensen--Cauchy calculation behind cumulative-width arguments. -/
theorem stageIndexedCumulativeTailStateValue_sq_le_horizon_sq_mul_policyValue_sq_reward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      ∑ elapsed ∈ Finset.range horizon,
        pmfExp (stageIndexedStateLawFrom transition policy initial startTime elapsed)
          (fun state =>
            (stageIndexedStateValue transition reward policy (startTime + elapsed)
              (horizon - elapsed) state) ^ 2) ≤
        (horizon : ℝ) ^ 2 * stageIndexedPolicyValue transition
          (fun time state action => (reward time state action) ^ 2)
          policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp
  | succ remaining ih =>
      let squaredReward : StageIndexedReward State Action := fun time state action =>
        (reward time state action) ^ 2
      let nextInitial := stageIndexedAdvanceStateLaw transition policy initial startTime
      have hpoint : ∀ state,
          (stageIndexedStateValue transition reward policy startTime (remaining + 1) state) ^ 2 ≤
            ((remaining + 1 : ℕ) : ℝ) *
              stageIndexedStateValue transition squaredReward policy startTime (remaining + 1) state := by
        intro state
        exact stageIndexedPolicyValue_sq_le_horizon_mul_sq_reward transition reward policy
          (PMF.pure state) startTime (remaining + 1)
      have hfirst :
          pmfExp initial (fun state =>
            (stageIndexedStateValue transition reward policy startTime (remaining + 1) state) ^ 2) ≤
            ((remaining + 1 : ℕ) : ℝ) *
              stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) := by
        calc
          _ ≤ pmfExp initial (fun state => ((remaining + 1 : ℕ) : ℝ) *
              stageIndexedStateValue transition squaredReward policy startTime (remaining + 1) state) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro state
            exact hpoint state
          _ = ((remaining + 1 : ℕ) : ℝ) *
              pmfExp initial (stageIndexedStateValue transition squaredReward policy startTime (remaining + 1)) := by
            calc
              _ = pmfExp initial (fun state =>
                  stageIndexedStateValue transition squaredReward policy startTime (remaining + 1) state *
                    ((remaining + 1 : ℕ) : ℝ)) := by
                apply pmfExp_congr
                intro state
                ring
              _ = pmfExp initial
                  (stageIndexedStateValue transition squaredReward policy startTime (remaining + 1)) *
                    ((remaining + 1 : ℕ) : ℝ) :=
                pmfExp_mul_const initial _ _
              _ = _ := by ring
          _ = _ := by
            rw [← stageIndexedPolicyValue_eq_pmfExp_stateValue]
      have htail := ih nextInitial (startTime + 1)
      have htailRewrite :
          ∑ elapsed ∈ Finset.range remaining,
            pmfExp (stageIndexedStateLawFrom transition policy initial startTime (elapsed + 1))
              (fun state =>
                (stageIndexedStateValue transition reward policy
                  (startTime + (elapsed + 1)) ((remaining + 1) - (elapsed + 1)) state) ^ 2) =
          ∑ elapsed ∈ Finset.range remaining,
            pmfExp (stageIndexedStateLawFrom transition policy nextInitial (startTime + 1) elapsed)
              (fun state =>
                (stageIndexedStateValue transition reward policy
                  ((startTime + 1) + elapsed) (remaining - elapsed) state) ^ 2) := by
        apply Finset.sum_congr rfl
        intro elapsed _
        rw [stageIndexedStateLawFrom_succ_eq_advanced]
        apply pmfExp_congr
        intro state
        have hremaining : (remaining + 1) - (elapsed + 1) = remaining - elapsed := by omega
        have htime : startTime + (elapsed + 1) = (startTime + 1) + elapsed := by omega
        rw [hremaining, htime]
      have htotalSq_nonneg : 0 ≤ stageIndexedPolicyValue transition squaredReward policy
          initial startTime (remaining + 1) := by
        exact stageIndexedPolicyValue_nonneg transition squaredReward policy (fun _ _ _ => sq_nonneg _)
          initial startTime (remaining + 1)
      have hnextSq_nonneg : 0 ≤ stageIndexedPolicyValue transition squaredReward policy
          nextInitial (startTime + 1) remaining := by
        exact stageIndexedPolicyValue_nonneg transition squaredReward policy (fun _ _ _ => sq_nonneg _)
          nextInitial (startTime + 1) remaining
      have hnextSq_le_total :
          stageIndexedPolicyValue transition squaredReward policy nextInitial (startTime + 1) remaining ≤
            stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) := by
        rw [stageIndexedPolicyValue_succ]
        apply le_add_of_nonneg_left
        apply pmfExp_nonneg_of_forall_nonneg
        intro state
        apply pmfExp_nonneg_of_forall_nonneg
        intro action
        exact sq_nonneg _
      rw [← sum_range_succ_eq_head_add_shift]
      rw [htailRewrite]
      calc
        _ ≤ ((remaining + 1 : ℕ) : ℝ) *
              stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) +
            (remaining : ℝ) ^ 2 *
              stageIndexedPolicyValue transition squaredReward policy nextInitial (startTime + 1) remaining :=
          add_le_add hfirst htail
        _ ≤ ((remaining + 1 : ℕ) : ℝ) *
              stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) +
            (remaining : ℝ) ^ 2 *
              stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) := by
          gcongr
        _ ≤ ((remaining + 1 : ℕ) : ℝ) ^ 2 *
              stageIndexedPolicyValue transition squaredReward policy initial startTime (remaining + 1) := by
          have hcast : ((remaining + 1 : ℕ) : ℝ) = (remaining : ℝ) + 1 := by norm_num
          rw [hcast]
          nlinarith

/-- A fixed-state continuation value is monotone under reward domination on
the stages it can still reach. -/
theorem stageIndexedStateValue_mono_reward_of_elapsed
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (lower upper : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action)
    (time horizon : ℕ) (state : State)
    (hreward : ∀ elapsed, elapsed < horizon → ∀ localState localAction,
      lower (time + elapsed) localState localAction ≤
        upper (time + elapsed) localState localAction) :
    stageIndexedStateValue transition lower policy time horizon state ≤
      stageIndexedStateValue transition upper policy time horizon state := by
  unfold stageIndexedStateValue
  exact stageIndexedPolicyValue_mono_reward_of_elapsed transition lower upper policy
    (PMF.pure state) time horizon hreward

/-- Bellman form of a fixed-state value in the stage-indexed model. -/
theorem stageIndexedStateValue_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) :
    stageIndexedStateValue transition reward policy time (remaining + 1) state =
      pmfExp (policy time state) (fun action =>
        reward time state action +
          pmfExp (transition time state action)
            (stageIndexedStateValue transition reward policy (time + 1) remaining)) := by
  unfold stageIndexedStateValue
  rw [stageIndexedPolicyValue_succ,
    stageIndexedPolicyValue_eq_pmfExp_stateValue]
  simp only [FiniteMDP.pmfExp_pure, stageIndexedAdvanceStateLaw, PMF.pure_bind]
  rw [pmfExp_bind, ← pmfExp_add]
  rfl

/-- The action value obtained by taking one action and then following a reference policy. -/
noncomputable def stageIndexedActionValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (reference : StageIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) (action : Action) : ℝ :=
  reward time state action +
    pmfExp (transition time state action)
      (stageIndexedStateValue transition reward reference (time + 1) remaining)

/-- A reference policy's state value is its action-value expectation. -/
theorem stageIndexedStateValue_succ_eq_actionValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (reference : StageIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) :
    stageIndexedStateValue transition reward reference time (remaining + 1) state =
      pmfExp (reference time state)
        (stageIndexedActionValue transition reward reference time remaining state) := by
  rw [stageIndexedStateValue_succ]
  rfl

/-- The stagewise advantage of an evaluation policy over a reference policy. -/
noncomputable def stageIndexedPolicyAdvantage
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action)
    (time remaining : ℕ) (state : State) : ℝ :=
  pmfExp (evaluation time state)
      (stageIndexedActionValue transition reward reference time remaining state) -
    pmfExp (reference time state)
      (stageIndexedActionValue transition reward reference time remaining state)

/-- The occupancy-weighted stagewise-advantage total in the performance-difference identity. -/
noncomputable def stageIndexedPerformanceDifference
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      pmfExp initial
        (stageIndexedPolicyAdvantage transition reward reference evaluation startTime remaining) +
      stageIndexedPerformanceDifference transition reward reference evaluation
        (stageIndexedAdvanceStateLaw transition evaluation initial startTime) (startTime + 1)
        remaining

/--
The finite-PMF performance-difference identity: changing from the reference
policy to the evaluation policy changes value by the evaluation-occupancy
total of the reference action-value advantage.

This is the exact finite-state/action counterpart of Zhan et al. (2024),
Lemma 10.  The recursive right-hand side is the finite-PMF expansion of the
paper's sum of expectations under the evaluation-policy trajectory law.
-/
theorem stageIndexedPolicyValue_sub_eq_performanceDifference
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      stageIndexedPolicyValue transition reward evaluation initial startTime horizon -
        stageIndexedPolicyValue transition reward reference initial startTime horizon =
          stageIndexedPerformanceDifference transition reward reference evaluation
            initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedPerformanceDifference]
  | succ horizon ih =>
      have hrefAdvance :
          stageIndexedPolicyValue transition reward reference
              (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
              (startTime + 1) horizon =
            pmfExp initial (fun state =>
              pmfExp (evaluation startTime state) (fun action =>
                pmfExp (transition startTime state action)
                  (stageIndexedStateValue transition reward reference
                    (startTime + 1) horizon))) := by
        rw [stageIndexedPolicyValue_eq_pmfExp_stateValue]
        unfold stageIndexedAdvanceStateLaw
        rw [pmfExp_bind]
        apply pmfExp_congr
        intro state
        rw [pmfExp_bind]
      have hrefCurrent :
          stageIndexedPolicyValue transition reward reference initial startTime (horizon + 1) =
            pmfExp initial (fun state =>
              pmfExp (reference startTime state)
                (stageIndexedActionValue transition reward reference startTime horizon state)) := by
        rw [stageIndexedPolicyValue_eq_pmfExp_stateValue]
        apply pmfExp_congr
        intro state
        rw [stageIndexedStateValue_succ_eq_actionValue]
      have hevaluationWithReference :
          pmfExp initial (fun state =>
              pmfExp (evaluation startTime state) (fun action =>
                reward startTime state action)) +
            stageIndexedPolicyValue transition reward reference
              (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
              (startTime + 1) horizon =
            pmfExp initial (fun state =>
              pmfExp (evaluation startTime state)
                (stageIndexedActionValue transition reward reference startTime horizon state)) := by
        rw [hrefAdvance, ← pmfExp_add]
        apply pmfExp_congr
        intro state
        unfold stageIndexedActionValue
        rw [pmfExp_add]
      have hadvantage :
          pmfExp initial
              (stageIndexedPolicyAdvantage transition reward reference evaluation startTime horizon) =
            pmfExp initial (fun state =>
              (pmfExp (evaluation startTime state)
                (stageIndexedActionValue transition reward reference startTime horizon state) -
              pmfExp (reference startTime state)
                (stageIndexedActionValue transition reward reference startTime horizon state))) := by
        unfold stageIndexedPolicyAdvantage
        rw [pmfExp_sub]
      calc
        stageIndexedPolicyValue transition reward evaluation initial startTime (horizon + 1) -
            stageIndexedPolicyValue transition reward reference initial startTime (horizon + 1) =
            (pmfExp initial (fun state =>
                pmfExp (evaluation startTime state) (fun action => reward startTime state action)) +
              stageIndexedPolicyValue transition reward evaluation
                (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
                (startTime + 1) horizon) -
              stageIndexedPolicyValue transition reward reference initial startTime (horizon + 1) := by
              congr 1
        _ =
            (pmfExp initial (fun state =>
                pmfExp (evaluation startTime state) (fun action => reward startTime state action)) +
              stageIndexedPolicyValue transition reward evaluation
                (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
                (startTime + 1) horizon) -
              pmfExp initial (fun state =>
                pmfExp (reference startTime state)
                  (stageIndexedActionValue transition reward reference startTime horizon state)) := by
              rw [hrefCurrent]
        _ =
            (pmfExp initial (fun state =>
                pmfExp (evaluation startTime state)
                  (stageIndexedActionValue transition reward reference startTime horizon state)) -
              pmfExp initial (fun state =>
                pmfExp (reference startTime state)
                  (stageIndexedActionValue transition reward reference startTime horizon state))) +
              (stageIndexedPolicyValue transition reward evaluation
                (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
                (startTime + 1) horizon -
              stageIndexedPolicyValue transition reward reference
                (stageIndexedAdvanceStateLaw transition evaluation initial startTime)
                (startTime + 1) horizon) := by
              rw [← hevaluationWithReference]
              ring
        _ =
            stageIndexedPerformanceDifference transition reward reference evaluation
              initial startTime (horizon + 1) := by
              rw [← pmfExp_sub, ← hadvantage,
                ih (stageIndexedAdvanceStateLaw transition evaluation initial startTime) (startTime + 1)]
              rfl

/--
The performance-difference recurrence as an explicit finite sum over the
evaluation-policy state laws.  This is the occupancy form needed when a
policy-search proof bounds its local action loss only on a high-reach subset
of states.
-/
theorem stageIndexedPerformanceDifference_eq_sum_stateLawFrom
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      stageIndexedPerformanceDifference transition reward reference evaluation
          initial startTime horizon =
        ∑ elapsed ∈ Finset.range horizon,
          pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
            (stageIndexedPolicyAdvantage transition reward reference evaluation
              (startTime + elapsed) (horizon - elapsed - 1)) := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp [stageIndexedPerformanceDifference]
  | succ horizon ih =>
      change
        pmfExp initial
            (stageIndexedPolicyAdvantage transition reward reference evaluation startTime horizon) +
          stageIndexedPerformanceDifference transition reward reference evaluation
            (stageIndexedAdvanceStateLaw transition evaluation initial startTime) (startTime + 1)
            horizon = _
      rw [ih (stageIndexedAdvanceStateLaw transition evaluation initial startTime) (startTime + 1)]
      have htail :
          (∑ elapsed ∈ Finset.range horizon,
            pmfExp (stageIndexedStateLawFrom transition evaluation
              (stageIndexedAdvanceStateLaw transition evaluation initial startTime) (startTime + 1)
              elapsed)
              (stageIndexedPolicyAdvantage transition reward reference evaluation
                ((startTime + 1) + elapsed) (horizon - elapsed - 1))) =
          ∑ elapsed ∈ Finset.range horizon,
            pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime (elapsed + 1))
              (stageIndexedPolicyAdvantage transition reward reference evaluation
                (startTime + (elapsed + 1)) ((horizon + 1) - (elapsed + 1) - 1)) := by
        apply Finset.sum_congr rfl
        intro elapsed _
        have htime : (startTime + 1) + elapsed = startTime + (elapsed + 1) := by omega
        have hremaining : horizon - elapsed - 1 =
            (horizon + 1) - (elapsed + 1) - 1 := by omega
        rw [← stageIndexedStateLawFrom_succ_eq_advanced]
        simp [htime, hremaining]
      rw [htail]
      have hfirst :
          pmfExp initial
              (stageIndexedPolicyAdvantage transition reward reference evaluation startTime horizon) =
            pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime 0)
              (stageIndexedPolicyAdvantage transition reward reference evaluation
                (startTime + 0) ((horizon + 1) - 0 - 1)) := by
        simp
      rw [hfirst]
      simpa only [stageIndexedStateLawFrom_zero, Nat.zero_add] using
        (sum_range_succ_eq_head_add_shift
          (fun elapsed =>
            pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
              (stageIndexedPolicyAdvantage transition reward reference evaluation
                (startTime + elapsed) ((horizon + 1) - elapsed - 1))) horizon)

/-- A policy has zero continuation value after the only stage on which its
reward may be nonzero. -/
theorem stageIndexedStateValue_eq_zero_after_singleStageReward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) (targetTime : ℕ)
    (hzero : ∀ time, time ≠ targetTime → ∀ state action, reward time state action = 0) :
    ∀ time remaining, targetTime < time → ∀ state,
      stageIndexedStateValue transition reward policy time remaining state = 0 := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro _ state
      rfl
  | succ remaining ih =>
      intro htime state
      rw [stageIndexedStateValue_succ]
      have hintegrand : (fun action =>
          reward time state action +
            pmfExp (transition time state action)
              (stageIndexedStateValue transition reward policy (time + 1) remaining)) =
          (fun _action => 0) := by
        funext action
        rw [hzero time (by omega) state action]
        have htail : ∀ nextState,
            stageIndexedStateValue transition reward policy (time + 1) remaining nextState = 0 :=
          ih (time + 1) (by omega)
        have htailExp : pmfExp (transition time state action)
            (stageIndexedStateValue transition reward policy (time + 1) remaining) = 0 := by
          calc
            pmfExp (transition time state action)
                (stageIndexedStateValue transition reward policy (time + 1) remaining) =
              pmfExp (transition time state action) (fun _nextState => 0) := by
                apply pmfExp_congr
                exact htail
            _ = 0 := by simp
        rw [htailExp]
        ring
      rw [hintegrand]
      simp

/-- Uniformly bounded stage rewards give the expected linear-in-horizon
envelope for every finite-horizon state value. -/
theorem abs_stageIndexedStateValue_le_card_mul_of_uniformRewardBound
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) (bound : ℝ)
    (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ time state action, |reward time state action| ≤ bound) :
    ∀ time remaining state,
      |stageIndexedStateValue transition reward policy time remaining state| ≤
        (remaining : ℝ) * bound := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state
      simp [stageIndexedStateValue]
  | succ remaining ih =>
      intro state
      rw [stageIndexedStateValue_succ]
      apply abs_pmfExp_le_of_forall_abs_le
      intro action
      calc
        |reward time state action +
            pmfExp (transition time state action)
              (stageIndexedStateValue transition reward policy (time + 1) remaining)| ≤
            |reward time state action| +
              |pmfExp (transition time state action)
                (stageIndexedStateValue transition reward policy (time + 1) remaining)| :=
          abs_add_le _ _
        _ ≤ bound + (remaining : ℝ) * bound := by
          exact add_le_add (hbound time state action)
            (abs_pmfExp_le_of_forall_abs_le _ _ ((remaining : ℝ) * bound)
              (ih (time + 1)))
        _ = ((remaining + 1 : ℕ) : ℝ) * bound := by
          push_cast
          ring

/-- Uniformly bounded stage rewards give the expected one-step-plus-
continuation action-value envelope. -/
theorem abs_stageIndexedActionValue_le_card_mul_of_uniformRewardBound
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) (bound : ℝ)
    (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ time state action, |reward time state action| ≤ bound)
    (time remaining : ℕ) (state : State) (action : Action) :
    |stageIndexedActionValue transition reward policy time remaining state action| ≤
      ((remaining + 1 : ℕ) : ℝ) * bound := by
  unfold stageIndexedActionValue
  calc
    |reward time state action +
        pmfExp (transition time state action)
          (stageIndexedStateValue transition reward policy (time + 1) remaining)| ≤
      |reward time state action| +
        |pmfExp (transition time state action)
          (stageIndexedStateValue transition reward policy (time + 1) remaining)| :=
      abs_add_le _ _
    _ ≤ bound + (remaining : ℝ) * bound := by
      exact add_le_add (hbound time state action)
        (abs_pmfExp_le_of_forall_abs_le _ _ ((remaining : ℝ) * bound)
          (abs_stageIndexedStateValue_le_card_mul_of_uniformRewardBound
            transition reward policy bound hboundNonneg hbound (time + 1) remaining))
    _ = ((remaining + 1 : ℕ) : ℝ) * bound := by
      push_cast
      ring

/-- A reward supported at one stage gives every state value the same absolute
envelope as its one-stage rewards. -/
theorem abs_stageIndexedStateValue_le_of_singleStageReward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) (targetTime : ℕ) (bound : ℝ)
    (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ state action, |reward targetTime state action| ≤ bound)
    (hzero : ∀ time, time ≠ targetTime → ∀ state action, reward time state action = 0) :
    ∀ time remaining state,
      |stageIndexedStateValue transition reward policy time remaining state| ≤ bound := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state
      change |(0 : ℝ)| ≤ bound
      simpa using hboundNonneg
  | succ remaining ih =>
      intro state
      rw [stageIndexedStateValue_succ]
      apply abs_pmfExp_le_of_forall_abs_le
      intro action
      by_cases htime : time = targetTime
      · subst time
        have htail : ∀ nextState,
            stageIndexedStateValue transition reward policy (targetTime + 1) remaining
              nextState = 0 :=
          stageIndexedStateValue_eq_zero_after_singleStageReward transition reward policy
            targetTime hzero (targetTime + 1) remaining (by omega)
        have htailExp : pmfExp (transition targetTime state action)
            (stageIndexedStateValue transition reward policy (targetTime + 1) remaining) = 0 := by
          calc
            pmfExp (transition targetTime state action)
                (stageIndexedStateValue transition reward policy (targetTime + 1) remaining) =
              pmfExp (transition targetTime state action) (fun _nextState => 0) := by
                apply pmfExp_congr
                exact htail
            _ = 0 := by simp
        rw [htailExp, add_zero]
        exact hbound state action
      · rw [hzero time htime state action, zero_add]
        exact abs_pmfExp_le_of_forall_abs_le _ _ bound (ih (time + 1))

/-- A reward supported at one stage gives every reference-policy action value
the same absolute envelope as its one-stage rewards. -/
theorem abs_stageIndexedActionValue_le_of_singleStageReward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) (targetTime : ℕ) (bound : ℝ)
    (hboundNonneg : 0 ≤ bound)
    (hbound : ∀ state action, |reward targetTime state action| ≤ bound)
    (hzero : ∀ time, time ≠ targetTime → ∀ state action, reward time state action = 0)
    (time remaining : ℕ) (state : State) (action : Action) :
    |stageIndexedActionValue transition reward policy time remaining state action| ≤ bound := by
  unfold stageIndexedActionValue
  by_cases htime : time = targetTime
  · subst time
    have htail : ∀ nextState,
        stageIndexedStateValue transition reward policy (targetTime + 1) remaining nextState = 0 :=
      stageIndexedStateValue_eq_zero_after_singleStageReward transition reward policy
        targetTime hzero (targetTime + 1) remaining (by omega)
    have htailExp : pmfExp (transition targetTime state action)
        (stageIndexedStateValue transition reward policy (targetTime + 1) remaining) = 0 := by
      calc
        pmfExp (transition targetTime state action)
            (stageIndexedStateValue transition reward policy (targetTime + 1) remaining) =
          pmfExp (transition targetTime state action) (fun _nextState => 0) := by
            apply pmfExp_congr
            exact htail
        _ = 0 := by simp
    rw [htailExp, add_zero]
    exact hbound state action
  · rw [hzero time htime state action, zero_add]
    exact abs_pmfExp_le_of_forall_abs_le _ _ bound
      (abs_stageIndexedStateValue_le_of_singleStageReward transition reward policy
        targetTime bound hboundNonneg hbound hzero (time + 1) remaining)

/-- A uniform finite-horizon policy `L1` error controls value error whenever
the reference-policy action values admit a uniform absolute envelope. -/
theorem abs_stageIndexedPolicyValue_sub_le_of_uniformPolicyL1Error
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (firstPolicy secondPolicy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (actionValueBound policyError : ℝ)
    (hactionValueBoundNonneg : 0 ≤ actionValueBound)
    (hactionValueBound : ∀ elapsed, elapsed < horizon → ∀ state action,
      |stageIndexedActionValue transition reward secondPolicy
          (startTime + elapsed) (horizon - elapsed - 1) state action| ≤ actionValueBound)
    (hpolicyError : ∀ elapsed, elapsed < horizon → ∀ state,
      pmfL1Error (firstPolicy (startTime + elapsed) state)
        (secondPolicy (startTime + elapsed) state) ≤ policyError) :
    |stageIndexedPolicyValue transition reward firstPolicy initial startTime horizon -
        stageIndexedPolicyValue transition reward secondPolicy initial startTime horizon| ≤
      (horizon : ℝ) * actionValueBound * policyError := by
  rw [stageIndexedPolicyValue_sub_eq_performanceDifference,
    stageIndexedPerformanceDifference_eq_sum_stateLawFrom]
  calc
    |∑ elapsed ∈ Finset.range horizon,
        pmfExp (stageIndexedStateLawFrom transition firstPolicy initial startTime elapsed)
          (stageIndexedPolicyAdvantage transition reward secondPolicy firstPolicy
            (startTime + elapsed) (horizon - elapsed - 1))| ≤
      ∑ elapsed ∈ Finset.range horizon,
        |pmfExp (stageIndexedStateLawFrom transition firstPolicy initial startTime elapsed)
          (stageIndexedPolicyAdvantage transition reward secondPolicy firstPolicy
            (startTime + elapsed) (horizon - elapsed - 1))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _elapsed ∈ Finset.range horizon, actionValueBound * policyError := by
      apply Finset.sum_le_sum
      intro elapsed helapsed
      have helapsed' : elapsed < horizon := Finset.mem_range.mp helapsed
      apply abs_pmfExp_le_of_forall_abs_le
      intro state
      unfold stageIndexedPolicyAdvantage
      exact (abs_pmfExp_sub_le_bound_mul_pmfL1Error
        (firstPolicy (startTime + elapsed) state)
        (secondPolicy (startTime + elapsed) state)
        (stageIndexedActionValue transition reward secondPolicy
          (startTime + elapsed) (horizon - elapsed - 1) state)
        actionValueBound (hactionValueBound elapsed helapsed' state)).trans
          (mul_le_mul_of_nonneg_left
            (hpolicyError elapsed helapsed' state) hactionValueBoundNonneg)
    _ = (horizon : ℝ) * actionValueBound * policyError := by
      simp [Finset.card_range]
      ring

/--
An evaluation policy's value loss is controlled by local action advantages on
a designated good-state region plus the evaluation-rollout mass of its
complement.  The uniform `1` on exceptional states applies when total
continuation values are normalized to `[0,1]`.
-/
theorem stageIndexedPolicyValue_sub_le_of_goodStateAdvantageBound
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (good : ℕ → State → Prop) [∀ time state, Decidable (good time state)]
    (localError badProbability : ℝ)
    (hlocalNonneg : 0 ≤ localError)
    (hgood : ∀ elapsed state, elapsed < horizon → good (startTime + elapsed) state →
      stageIndexedPolicyAdvantage transition reward reference evaluation
        (startTime + elapsed) (horizon - elapsed - 1) state ≤ localError)
    (hglobal : ∀ elapsed state, elapsed < horizon →
      stageIndexedPolicyAdvantage transition reward reference evaluation
        (startTime + elapsed) (horizon - elapsed - 1) state ≤ 1)
    (hbad : ∀ elapsed, elapsed < horizon →
      pmfProb (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
        (fun state => ¬ good (startTime + elapsed) state) ≤ badProbability) :
    stageIndexedPolicyValue transition reward evaluation initial startTime horizon -
      stageIndexedPolicyValue transition reward reference initial startTime horizon ≤
        (horizon : ℝ) * (localError + badProbability) := by
  classical
  rw [stageIndexedPolicyValue_sub_eq_performanceDifference]
  rw [stageIndexedPerformanceDifference_eq_sum_stateLawFrom]
  calc
    ∑ elapsed ∈ Finset.range horizon,
        pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
          (stageIndexedPolicyAdvantage transition reward reference evaluation
            (startTime + elapsed) (horizon - elapsed - 1)) ≤
      ∑ _elapsed ∈ Finset.range horizon, (localError + badProbability) := by
        refine Finset.sum_le_sum (s := Finset.range horizon) ?_
        intro elapsed helapsed
        have hstage : elapsed < horizon := Finset.mem_range.mp helapsed
        have hpoint : ∀ state,
            stageIndexedPolicyAdvantage transition reward reference evaluation
              (startTime + elapsed) (horizon - elapsed - 1) state ≤
              localError +
                (if ¬ good (startTime + elapsed) state then (1 : ℝ) else 0) := by
          intro state
          by_cases hbadState : ¬ good (startTime + elapsed) state
          · simp [hbadState]
            linarith [hglobal elapsed state hstage]
          · have hgoodState : good (startTime + elapsed) state := by
              exact Classical.not_not.mp hbadState
            simp [hbadState]
            exact hgood elapsed state hstage hgoodState
        calc
          pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
              (stageIndexedPolicyAdvantage transition reward reference evaluation
                (startTime + elapsed) (horizon - elapsed - 1)) ≤
            pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
              (fun state => localError +
                if ¬ good (startTime + elapsed) state then (1 : ℝ) else 0) :=
              pmfExp_le_pmfExp_of_forall_le _ _ _ hpoint
          _ = localError +
              pmfProb (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
                (fun state => ¬ good (startTime + elapsed) state) := by
              rw [pmfExp_add, pmfExp_const]
              rfl
          _ ≤ localError + badProbability :=
            by simpa [add_comm] using add_le_add_left (hbad elapsed hstage) localError
    _ = (horizon : ℝ) * (localError + badProbability) := by
      simp [Finset.card_range]
      ring

/--
Stage-dependent version of `stageIndexedPolicyValue_sub_le_of_goodStateAdvantageBound`.
It retains the exact sum of bad-state masses, which is useful when a
finite-horizon analysis uses disjoint state layers and controls their *total*
rather than a uniform per-stage exceptional probability.
-/
theorem stageIndexedPolicyValue_sub_le_of_goodStateAdvantageBounds
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action)
    (reference evaluation : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (good : ℕ → State → Prop) [∀ time state, Decidable (good time state)]
    (localError badProbability : ℕ → ℝ)
    (hlocalNonneg : ∀ elapsed, elapsed < horizon → 0 ≤ localError elapsed)
    (hgood : ∀ elapsed state, elapsed < horizon → good (startTime + elapsed) state →
      stageIndexedPolicyAdvantage transition reward reference evaluation
        (startTime + elapsed) (horizon - elapsed - 1) state ≤ localError elapsed)
    (hglobal : ∀ elapsed state, elapsed < horizon →
      stageIndexedPolicyAdvantage transition reward reference evaluation
        (startTime + elapsed) (horizon - elapsed - 1) state ≤ 1)
    (hbad : ∀ elapsed, elapsed < horizon →
      pmfProb (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
        (fun state => ¬ good (startTime + elapsed) state) ≤ badProbability elapsed) :
    stageIndexedPolicyValue transition reward evaluation initial startTime horizon -
      stageIndexedPolicyValue transition reward reference initial startTime horizon ≤
        ∑ elapsed ∈ Finset.range horizon, (localError elapsed + badProbability elapsed) := by
  classical
  rw [stageIndexedPolicyValue_sub_eq_performanceDifference]
  rw [stageIndexedPerformanceDifference_eq_sum_stateLawFrom]
  apply Finset.sum_le_sum
  intro elapsed helapsed
  have hstage : elapsed < horizon := Finset.mem_range.mp helapsed
  have hpoint : ∀ state,
      stageIndexedPolicyAdvantage transition reward reference evaluation
        (startTime + elapsed) (horizon - elapsed - 1) state ≤
        localError elapsed +
          (if ¬ good (startTime + elapsed) state then (1 : ℝ) else 0) := by
    intro state
    by_cases hbadState : ¬ good (startTime + elapsed) state
    · simp [hbadState]
      linarith [hglobal elapsed state hstage, hlocalNonneg elapsed hstage]
    · have hgoodState : good (startTime + elapsed) state := by
        exact Classical.not_not.mp hbadState
      simp [hbadState]
      exact hgood elapsed state hstage hgoodState
  calc
    pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
        (stageIndexedPolicyAdvantage transition reward reference evaluation
          (startTime + elapsed) (horizon - elapsed - 1)) ≤
      pmfExp (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
        (fun state => localError elapsed +
          if ¬ good (startTime + elapsed) state then (1 : ℝ) else 0) :=
        pmfExp_le_pmfExp_of_forall_le _ _ _ hpoint
    _ = localError elapsed +
        pmfProb (stageIndexedStateLawFrom transition evaluation initial startTime elapsed)
          (fun state => ¬ good (startTime + elapsed) state) := by
        rw [pmfExp_add, pmfExp_const]
        rfl
    _ ≤ localError elapsed + badProbability elapsed :=
      by simpa [add_comm] using
        add_le_add_left (hbad elapsed hstage) (localError elapsed)

end PreferenceRL

end AppliedModelingLib
