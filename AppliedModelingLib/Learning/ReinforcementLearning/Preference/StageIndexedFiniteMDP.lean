import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedPerformanceDifference
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedBellmanResidual
import AppliedModelingLib.Foundations.Probability.MDP

/-!
# Finite MDPs as stage-indexed expected-reward models

`FiniteMDP` allows a reward to depend on the realized successor state, while
the stage-indexed preference-RL interface records its expected one-step reward
separately.  This file proves that the two finite-horizon value recursions
agree exactly.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A time-homogeneous finite MDP viewed as a stage-indexed transition model. -/
noncomputable def finiteMDPStageIndexedTransition
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) : StageIndexedTransitionModel State Action :=
  fun _ => mdp.transition

/-- The stage-indexed reward is the true MDP's expected successor-dependent reward. -/
noncomputable def finiteMDPExpectedStageReward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) : StageIndexedReward State Action :=
  fun _ state action => pmfExp (mdp.transition state action) (mdp.reward state action)

/-- A finite-horizon value recursion for a policy indexed by absolute time. -/
noncomputable def finiteMDPTimeIndexedHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) (policy : StageIndexedPolicy State Action) :
    ℕ → ℕ → State → ℝ
  | _, 0, _ => 0
  | time, remaining + 1, state =>
      FiniteMDP.policyValueStep mdp (policy time)
        (finiteMDPTimeIndexedHorizonValue mdp policy (time + 1) remaining) state

/--
The stage-indexed value of the expected-reward conversion equals the original
successor-dependent-reward MDP value for every absolute start time.
-/
theorem stageIndexedStateValue_finiteMDPExpectedReward_eq_timeIndexedHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) (policy : StageIndexedPolicy State Action) :
    ∀ time remaining state,
      stageIndexedStateValue (finiteMDPStageIndexedTransition mdp)
        (finiteMDPExpectedStageReward mdp) policy time remaining state =
        finiteMDPTimeIndexedHorizonValue mdp policy time remaining state := by
  intro time remaining
  induction remaining generalizing time with
  | zero =>
      intro state
      simp [stageIndexedStateValue, finiteMDPTimeIndexedHorizonValue]
  | succ remaining ih =>
      intro state
      rw [stageIndexedStateValue_succ]
      unfold finiteMDPStageIndexedTransition finiteMDPExpectedStageReward
      unfold finiteMDPTimeIndexedHorizonValue FiniteMDP.policyValueStep FiniteMDP.actionValue
      apply pmfExp_congr
      intro action
      have hnext :
          pmfExp (mdp.transition state action)
            (stageIndexedStateValue (fun _ : ℕ => mdp.transition)
              (fun _ state action =>
                pmfExp (mdp.transition state action) (mdp.reward state action))
              policy (time + 1) remaining) =
            pmfExp (mdp.transition state action)
              (finiteMDPTimeIndexedHorizonValue mdp policy (time + 1) remaining) := by
            apply pmfExp_congr
            intro next
            simpa [finiteMDPStageIndexedTransition, finiteMDPExpectedStageReward] using
              ih (time + 1) next
      rw [hnext, ← pmfExp_add]

/-- The same conversion holds from an arbitrary finite initial-state law. -/
theorem stageIndexedPolicyValue_finiteMDPExpectedReward_eq_pmfExp_timeIndexedHorizonValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (time remaining : ℕ) :
    stageIndexedPolicyValue (finiteMDPStageIndexedTransition mdp)
      (finiteMDPExpectedStageReward mdp) policy initial time remaining =
      pmfExp initial (finiteMDPTimeIndexedHorizonValue mdp policy time remaining) := by
  rw [stageIndexedPolicyValue_eq_pmfExp_stateValue]
  apply pmfExp_congr
  intro state
  exact stageIndexedStateValue_finiteMDPExpectedReward_eq_timeIndexedHorizonValue mdp policy
    time remaining state

/--
The Bellman-residual regret bound specialized to an MDP with
successor-dependent rewards.  It is the finite true-occupancy form of the
standard regret decomposition used in EULER's appendix.
-/
theorem pmfExp_benchmark_sub_timeIndexedHorizonValue_le_finiteMDPBellmanResidualTotal
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (mdp : FiniteMDP State Action) (policy : StageIndexedPolicy State Action)
    (candidate : ℕ → ℕ → State → ℝ)
    (candidate_terminal : ∀ time state, candidate time 0 state = 0)
    (initial : PMF State) (startTime horizon : ℕ) (benchmark : State → ℝ)
    (benchmark_le_candidate : ∀ state, benchmark state ≤ candidate startTime horizon state) :
    pmfExp initial benchmark -
        pmfExp initial (finiteMDPTimeIndexedHorizonValue mdp policy startTime horizon) ≤
      stageIndexedBellmanResidualTotal (finiteMDPStageIndexedTransition mdp)
        (finiteMDPExpectedStageReward mdp) policy candidate initial startTime horizon := by
  rw [← stageIndexedPolicyValue_finiteMDPExpectedReward_eq_pmfExp_timeIndexedHorizonValue
    mdp policy initial startTime horizon]
  exact pmfExp_benchmark_sub_stageIndexedPolicyValue_le_BellmanResidualTotal
    (finiteMDPStageIndexedTransition mdp) (finiteMDPExpectedStageReward mdp) policy candidate
    candidate_terminal initial startTime horizon benchmark benchmark_le_candidate

end PreferenceRL

end AppliedModelingLib
