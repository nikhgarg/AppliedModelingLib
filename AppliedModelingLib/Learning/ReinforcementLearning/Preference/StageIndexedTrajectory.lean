import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedRewardOccupancy

/-!
# Finite trajectories for stage-indexed MDPs

This module constructs the literal finite trajectory law of a stage-indexed
Markov policy and transition model.  Its main interface identifies every
trajectory coordinate with the corresponding state--action visitation law.
That equality is the source-to-model bridge needed when a trajectory-level
preference theorem is combined with stagewise reward-free exploration bounds.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- A length-`horizon` trajectory containing the state--action pair at every
reward-bearing stage. -/
abbrev StageIndexedTrajectory (State Action : Type*) (horizon : ℕ) :=
  Fin horizon → State × Action

/-- The recursive rollout state after `step` actions.  It retains the current
state together with all preceding reward-bearing state--action pairs. -/
noncomputable def stageIndexedTrajectoryPrefixLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) :
    (step : ℕ) → PMF (State × StageIndexedTrajectory State Action step)
  | 0 => initial.map fun state => (state, fun time => Fin.elim0 time)
  | step + 1 =>
      (stageIndexedTrajectoryPrefixLaw initial transition policy step).bind fun current =>
        (policy step current.1).bind fun action =>
          (transition step current.1 action).map fun nextState =>
            (nextState, Fin.snoc current.2 (current.1, action))

/-- Forget the post-horizon state from the recursive rollout.  The resulting
law is the source trajectory `(s₁,a₁,…,s_H,a_H)`. -/
noncomputable def stageIndexedTrajectoryLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (horizon : ℕ) :
    PMF (StageIndexedTrajectory State Action horizon) :=
  (stageIndexedTrajectoryPrefixLaw initial transition policy horizon).map Prod.snd

/-- The current-state marginal of the recursive trajectory law is exactly the
stage-indexed state law. -/
theorem stageIndexedTrajectoryPrefixLaw_map_fst
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) :
    ∀ step,
      (stageIndexedTrajectoryPrefixLaw initial transition policy step).map Prod.fst =
        stageIndexedStateLaw transition policy initial step := by
  intro step
  induction step with
  | zero =>
      rw [stageIndexedTrajectoryPrefixLaw, PMF.map_comp]
      simpa only [Function.comp_apply] using PMF.map_id initial
  | succ step ih =>
      rw [stageIndexedTrajectoryPrefixLaw, PMF.map_bind]
      simp_rw [PMF.map_bind, PMF.map_comp]
      have hcomp : ∀ (current : State × StageIndexedTrajectory State Action step)
          (action : Action),
          Prod.fst ∘ (fun nextState : State =>
            (nextState, @Fin.snoc step (fun _ => State × Action)
              current.2 (current.1, action))) = (id : State → State) := by
        intro current action
        funext nextState
        rfl
      simp_rw [hcomp, PMF.map_id]
      change (stageIndexedTrajectoryPrefixLaw initial transition policy step).bind
          ((fun state => (policy step state).bind fun action =>
            transition step state action) ∘ Prod.fst) = _
      rw [← PMF.bind_map, ih]
      rfl

/-- Every stored coordinate of the recursive prefix has the true visitation
marginal at that stage. -/
theorem stageIndexedTrajectoryPrefixLaw_coordinate
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) :
    ∀ (step : ℕ) (time : Fin step),
      (stageIndexedTrajectoryPrefixLaw initial transition policy step).map
          (fun current => current.2 time) =
        stageIndexedTrueStateActionRollout initial transition policy time.1 := by
  intro step
  induction step with
  | zero =>
      intro time
      exact Fin.elim0 time
  | succ step ih =>
      intro time
      refine Fin.lastCases ?_ ?_ time
      · rw [stageIndexedTrajectoryPrefixLaw, PMF.map_bind]
        simp_rw [PMF.map_bind, PMF.map_comp]
        have hcomp : ∀ (current : State × StageIndexedTrajectory State Action step)
            (action : Action),
            (fun stored : State × StageIndexedTrajectory State Action (step + 1) =>
              stored.2 (Fin.last step)) ∘ (fun nextState =>
              (nextState, @Fin.snoc step (fun _ => State × Action)
                current.2 (current.1, action))) =
                Function.const State (current.1, action) := by
          intro current action
          funext nextState
          simp
        simp_rw [hcomp, PMF.map_const]
        change (stageIndexedTrajectoryPrefixLaw initial transition policy step).bind
            (fun current => (policy step current.1).bind
              (PMF.pure ∘ fun action => (current.1, action))) = _
        simp_rw [PMF.bind_pure_comp]
        change (stageIndexedTrajectoryPrefixLaw initial transition policy step).bind
            ((fun state => (policy step state).map fun action => (state, action)) ∘
              Prod.fst) = _
        rw [← PMF.bind_map,
          stageIndexedTrajectoryPrefixLaw_map_fst initial transition policy step]
        rfl
      · intro time
        rw [stageIndexedTrajectoryPrefixLaw, PMF.map_bind]
        simp_rw [PMF.map_bind, PMF.map_comp]
        have hcomp : ∀ (current : State × StageIndexedTrajectory State Action step)
            (action : Action),
            (fun stored : State × StageIndexedTrajectory State Action (step + 1) =>
              stored.2 time.castSucc) ∘ (fun nextState =>
              (nextState, @Fin.snoc step (fun _ => State × Action)
                current.2 (current.1, action))) =
                Function.const State (current.2 time) := by
          intro current action
          funext nextState
          simp
        simp_rw [hcomp, PMF.map_const, PMF.bind_const]
        change (stageIndexedTrajectoryPrefixLaw initial transition policy step).bind
            (PMF.pure ∘ fun current => current.2 time) = _
        rw [PMF.bind_pure_comp]
        simpa using ih time

/-- Every coordinate of the complete trajectory has exactly the corresponding
true state--action visitation law. -/
theorem stageIndexedTrajectoryLaw_coordinate
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (horizon : ℕ) (time : Fin horizon) :
    (stageIndexedTrajectoryLaw initial transition policy horizon).map
        (fun trajectory => trajectory time) =
      stageIndexedTrueStateActionRollout initial transition policy time.1 := by
  unfold stageIndexedTrajectoryLaw
  rw [PMF.map_comp]
  simpa only [Function.comp_apply] using
    stageIndexedTrajectoryPrefixLaw_coordinate initial transition policy horizon time

/-- For every positive horizon, the initial state stored in a trajectory has
exactly the supplied initial law, independently of the policy and transition
kernel used later in the rollout. -/
theorem stageIndexedTrajectoryPrefixLaw_map_initialState
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (horizon : ℕ)
    (hhorizon : 0 < horizon) :
    (stageIndexedTrajectoryPrefixLaw initial transition policy horizon).map
        (fun rollout ↦ (rollout.2 ⟨0, hhorizon⟩).1) = initial := by
  let time : Fin horizon := ⟨0, hhorizon⟩
  calc
    (stageIndexedTrajectoryPrefixLaw initial transition policy horizon).map
        (fun rollout ↦ (rollout.2 time).1) =
      ((stageIndexedTrajectoryPrefixLaw initial transition policy horizon).map
        (fun rollout ↦ rollout.2 time)).map Prod.fst := by
          rw [PMF.map_comp]
          rfl
    _ = (stageIndexedTrueStateActionRollout initial transition policy 0).map Prod.fst := by
      rw [stageIndexedTrajectoryPrefixLaw_coordinate initial transition policy horizon time]
    _ = initial := by
      unfold stageIndexedTrueStateActionRollout stageIndexedStateActionLaw
      simp [PMF.map_bind, PMF.map_comp]

/-- The expected sum of arbitrary stage rewards on the retained rollout is
exactly the corresponding finite-horizon policy value.  Keeping the terminal
state in the outcome does not change reward accounting. -/
theorem stageIndexedTrajectoryPrefixLaw_reward_sum_eq_policyValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (reward : StageIndexedReward State Action) (horizon : ℕ) :
    pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy horizon)
        (fun rollout ↦ ∑ time : Fin horizon,
          reward time.1 (rollout.2 time).1 (rollout.2 time).2) =
      stageIndexedPolicyValue transition reward policy initial 0 horizon := by
  classical
  have hstateLaw : ∀ elapsed,
      stageIndexedStateLawFrom transition policy initial 0 elapsed =
        stageIndexedStateLaw transition policy initial elapsed := by
    intro elapsed
    induction elapsed with
    | zero => rfl
    | succ elapsed ih =>
        rw [stageIndexedStateLawFrom_succ, stageIndexedStateLaw_succ, ih]
        simp
  rw [pmfExp_univ_sum]
  rw [stageIndexedPolicyValue_eq_sum_stateLawFrom]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro time _htime
  calc
    pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy horizon)
        (fun rollout ↦ reward time.1 (rollout.2 time).1 (rollout.2 time).2) =
      pmfExp
        ((stageIndexedTrajectoryPrefixLaw initial transition policy horizon).map
          (fun rollout ↦ rollout.2 time))
        (fun stateAction ↦ reward time.1 stateAction.1 stateAction.2) := by
          rw [pmfExp_map]
    _ = pmfExp
        (stageIndexedTrueStateActionRollout initial transition policy time.1)
        (fun stateAction ↦ reward time.1 stateAction.1 stateAction.2) := by
          rw [stageIndexedTrajectoryPrefixLaw_coordinate]
    _ = pmfExp
        (stageIndexedStateLawFrom transition policy initial 0 time.1)
        (fun state ↦ pmfExp (policy (0 + time.1) state)
          (fun action ↦ reward (0 + time.1) state action)) := by
          rw [hstateLaw]
          simp only [Nat.zero_add]
          unfold stageIndexedTrueStateActionRollout stageIndexedStateActionLaw
          rw [pmfExp_bind]
          apply pmfExp_congr
          intro state
          rw [pmfExp_map]

/-- The successor state paired with a stored state--action coordinate.  The
post-horizon state retained by `stageIndexedTrajectoryPrefixLaw` supplies the
successor of the final stored coordinate. -/
def stageIndexedTrajectoryPrefixNextState
    {State Action : Type*} {step : ℕ}
    (rollout : State × StageIndexedTrajectory State Action step)
    (time : Fin step) : State :=
  if hnext : time.1 + 1 < step then
    (rollout.2 ⟨time.1 + 1, hnext⟩).1
  else
    rollout.1

@[simp] theorem stageIndexedTrajectoryPrefixNextState_snoc_castSucc
    {State Action : Type*} {step : ℕ}
    (current : State × StageIndexedTrajectory State Action step)
    (action : Action) (nextState : State) (time : Fin step) :
    stageIndexedTrajectoryPrefixNextState
        (nextState, Fin.snoc current.2 (current.1, action)) time.castSucc =
      stageIndexedTrajectoryPrefixNextState current time := by
  unfold stageIndexedTrajectoryPrefixNextState
  change
    (if hnext : time.1 + 1 < step + 1 then
        ((@Fin.snoc step (fun _ ↦ State × Action)
          current.2 (current.1, action))
          ⟨time.1 + 1, hnext⟩).1
      else nextState) =
      if hnext : time.1 + 1 < step then
        (current.2 ⟨time.1 + 1, hnext⟩).1
      else current.1
  have hnew : time.1 + 1 < step + 1 := by omega
  rw [dif_pos hnew]
  by_cases hnext : time.1 + 1 < step
  · rw [dif_pos hnext]
    have hindex :
        (⟨time.1 + 1, hnew⟩ : Fin (step + 1)) =
          (⟨time.1 + 1, hnext⟩ : Fin step).castSucc := by
      apply Fin.ext
      rfl
    rw [hindex, Fin.snoc_castSucc]
  · rw [dif_neg hnext]
    have heq : time.1 + 1 = step := by omega
    have hindex : (⟨time.1 + 1, hnew⟩ : Fin (step + 1)) = Fin.last step := by
      apply Fin.ext
      exact heq
    rw [hindex, Fin.snoc_last]

/-- A predictable scalar weight times the one-step transition residual is
centered under the literal finite rollout law.  This is the finite-PMF
martingale-difference identity used by adaptive least-squares analyses: the
weight may depend on the current state and action, but not on the freshly
sampled successor state. -/
theorem stageIndexedTrajectoryPrefixLaw_weightedTransitionResidual_eq_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (weight : State → Action → ℝ) (value : State → ℝ) :
    ∀ (step : ℕ) (time : Fin step),
      pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
          (fun rollout ↦
            let stateAction := rollout.2 time
            weight stateAction.1 stateAction.2 *
              (value (stageIndexedTrajectoryPrefixNextState rollout time) -
                pmfExp (transition time.1 stateAction.1 stateAction.2) value)) = 0 := by
  intro step
  induction step with
  | zero =>
      intro time
      exact Fin.elim0 time
  | succ step ih =>
      intro time
      refine Fin.lastCases ?_ ?_ time
      · rw [stageIndexedTrajectoryPrefixLaw, pmfExp_bind]
        calc
          pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
              (fun current ↦
                pmfExp
                  ((policy step current.1).bind fun action ↦
                    (transition step current.1 action).map fun nextState ↦
                      (nextState, Fin.snoc current.2 (current.1, action)))
                  (fun rollout ↦
                    let stateAction := rollout.2 (Fin.last step)
                    weight stateAction.1 stateAction.2 *
                      (value
                          (stageIndexedTrajectoryPrefixNextState rollout (Fin.last step)) -
                        pmfExp
                          (transition (Fin.last step).1 stateAction.1 stateAction.2)
                          value))) =
              pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
                (fun _current ↦ 0) := by
                apply pmfExp_congr
                intro current
                rw [pmfExp_bind]
                calc
                  pmfExp (policy step current.1)
                      (fun action ↦
                        pmfExp
                          ((transition step current.1 action).map fun nextState ↦
                            (nextState, Fin.snoc current.2 (current.1, action)))
                          (fun rollout ↦
                            let stateAction := rollout.2 (Fin.last step)
                            weight stateAction.1 stateAction.2 *
                              (value (stageIndexedTrajectoryPrefixNextState rollout
                                  (Fin.last step)) -
                                pmfExp
                                  (transition (Fin.last step).1 stateAction.1 stateAction.2)
                                  value))) =
                      pmfExp (policy step current.1) (fun _action ↦ 0) := by
                        apply pmfExp_congr
                        intro action
                        rw [pmfExp_map]
                        simp [stageIndexedTrajectoryPrefixNextState,
                          pmfExp_const_mul, pmfExp_sub]
                  _ = 0 := by simp
          _ = 0 := by simp
      · intro time
        rw [stageIndexedTrajectoryPrefixLaw, pmfExp_bind]
        calc
          pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
              (fun current ↦
                pmfExp
                  ((policy step current.1).bind fun action ↦
                    (transition step current.1 action).map fun nextState ↦
                      (nextState, Fin.snoc current.2 (current.1, action)))
                  (fun rollout ↦
                    let stateAction := rollout.2 time.castSucc
                    weight stateAction.1 stateAction.2 *
                      (value (stageIndexedTrajectoryPrefixNextState rollout time.castSucc) -
                        pmfExp (transition time.1 stateAction.1 stateAction.2) value))) =
              pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
                (fun current ↦
                  let stateAction := current.2 time
                  weight stateAction.1 stateAction.2 *
                    (value (stageIndexedTrajectoryPrefixNextState current time) -
                      pmfExp (transition time.1 stateAction.1 stateAction.2) value)) := by
                apply pmfExp_congr
                intro current
                rw [pmfExp_bind]
                calc
                  pmfExp (policy step current.1)
                      (fun action ↦
                        pmfExp
                          ((transition step current.1 action).map fun nextState ↦
                            (nextState, Fin.snoc current.2 (current.1, action)))
                          (fun rollout ↦
                            let stateAction := rollout.2 time.castSucc
                            weight stateAction.1 stateAction.2 *
                              (value
                                  (stageIndexedTrajectoryPrefixNextState rollout
                                    time.castSucc) -
                                pmfExp
                                  (transition time.1 stateAction.1 stateAction.2)
                                  value))) =
                      pmfExp (policy step current.1)
                        (fun _action ↦
                          weight (current.2 time).1 (current.2 time).2 *
                            (value (stageIndexedTrajectoryPrefixNextState current time) -
                              pmfExp
                                (transition time.1 (current.2 time).1
                                  (current.2 time).2) value)) := by
                        apply pmfExp_congr
                        intro action
                        rw [pmfExp_map]
                        simpa using pmfExp_const
                          (transition step current.1 action)
                          (weight (current.2 time).1 (current.2 time).2 *
                            (value (stageIndexedTrajectoryPrefixNextState current time) -
                              pmfExp
                                (transition time.1 (current.2 time).1
                                  (current.2 time).2) value))
                  _ =
                      weight (current.2 time).1 (current.2 time).2 *
                        (value (stageIndexedTrajectoryPrefixNextState current time) -
                          pmfExp
                            (transition time.1 (current.2 time).1
                              (current.2 time).2) value) := by simp
          _ = 0 := ih time

/-- The policy-to-trajectory-law interface induced by a finite stage-indexed
MDP rollout. -/
noncomputable def stageIndexedPolicyTrajectoryLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (horizon : ℕ) :
    PolicyTrajectoryLaw (StageIndexedPolicy State Action)
      (StageIndexedTrajectory State Action horizon) :=
  fun policy => stageIndexedTrajectoryLaw initial transition policy horizon

/-- The expected sum of a scalar stage reward along the literal trajectory is
exactly its occupancy/visitation expression. -/
theorem stageIndexedTrajectoryExpectedScore_eq_visitationScore
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (score : StageIndexedReward State Action) (horizon : ℕ) :
    pmfExp (stageIndexedTrajectoryLaw initial transition policy horizon)
        (fun trajectory => ∑ time : Fin horizon,
          score time.1 (trajectory time).1 (trajectory time).2) =
      stageIndexedVisitationScore transition policy initial score horizon := by
  rw [pmfExp_univ_sum]
  unfold stageIndexedVisitationScore
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro time htime
  have htimeLt : time < horizon := Finset.mem_range.mp htime
  rw [dif_pos htimeLt]
  let stage : Fin horizon := ⟨time, htimeLt⟩
  calc
    pmfExp (stageIndexedTrajectoryLaw initial transition policy horizon)
        (fun trajectory => score stage.1 (trajectory stage).1 (trajectory stage).2) =
      pmfExp
        ((stageIndexedTrajectoryLaw initial transition policy horizon).map
          (fun trajectory => trajectory stage))
        (fun stateAction => score stage.1 stateAction.1 stateAction.2) := by
          rw [pmfExp_map]
    _ = pmfExp (stageIndexedTrueStateActionRollout initial transition policy stage.1)
        (fun stateAction => score stage.1 stateAction.1 stateAction.2) := by
          rw [stageIndexedTrajectoryLaw_coordinate]
    _ = pmfExp
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw transition policy initial time) time)
        (fun stateAction => score time stateAction.1 stateAction.2) := by
          rfl

end PreferenceRL

end AppliedModelingLib
