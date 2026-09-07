import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedTrajectory
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.AdaptiveConcentration

/-!
# Concentration identities for stage-indexed trajectories

The current state--action feature inside a rollout is predictable immediately
before its successor state is sampled, even though it is not known at the
start of the episode.  This module conditions at that internal transition and
proves the exact one-step Hoeffding exponential bound without replacing the
realized feature square by a worst-case episode-level envelope.
-/

namespace AppliedModelingLib
namespace PreferenceRL

noncomputable section

/-- A predictable scalar weight times a bounded next-state Bellman residual,
with its realized quadratic compensation, has exponential moment at most one
under the literal finite rollout law. -/
theorem stageIndexedTrajectoryPrefixLaw_exp_weightedTransitionResidual_le_one
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (initial : PMF State) (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (weight : State → Action → ℝ) (value : State → ℝ) (valueBound : ℝ)
    (hvalueBound : 0 ≤ valueBound)
    (hvalue : ∀ state, value state ∈ Set.Icc 0 valueBound) :
    ∀ (step : ℕ) (time : Fin step),
      pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
          (fun rollout ↦
            let stateAction := rollout.2 time
            let scalar := weight stateAction.1 stateAction.2
            Real.exp
              (scalar *
                  (value (stageIndexedTrajectoryPrefixNextState rollout time) -
                    pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                valueBound ^ 2 * scalar ^ 2 / 2)) ≤ 1 := by
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
                    let scalar := weight stateAction.1 stateAction.2
                    Real.exp
                      (scalar *
                          (value (stageIndexedTrajectoryPrefixNextState rollout
                            (Fin.last step)) -
                            pmfExp
                              (transition (Fin.last step).1 stateAction.1 stateAction.2)
                              value) -
                        valueBound ^ 2 * scalar ^ 2 / 2))) ≤
            pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
              (fun _current ↦ 1) := by
                apply pmfExp_le_pmfExp_of_forall_le
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
                            let scalar := weight stateAction.1 stateAction.2
                            Real.exp
                              (scalar *
                                  (value (stageIndexedTrajectoryPrefixNextState rollout
                                    (Fin.last step)) -
                                    pmfExp
                                      (transition (Fin.last step).1 stateAction.1
                                        stateAction.2) value) -
                                valueBound ^ 2 * scalar ^ 2 / 2))) ≤
                    pmfExp (policy step current.1) (fun _action ↦ 1) := by
                      apply pmfExp_le_pmfExp_of_forall_le
                      intro action
                      rw [pmfExp_map]
                      let mean := pmfExp (transition step current.1 action) value
                      let scalar := weight current.1 action
                      have hmeanLower : 0 ≤ mean :=
                        pmfExp_nonneg_of_forall_nonneg _ _ fun state ↦ (hvalue state).1
                      have hmeanUpper : mean ≤ valueBound :=
                        pmfExp_le_of_forall_le _ _ _ fun state ↦ (hvalue state).2
                      have hcenter :
                          pmfExp (transition step current.1 action)
                            (fun nextState ↦ value nextState - mean) = 0 := by
                        rw [pmfExp_sub, pmfExp_const]
                        dsimp [mean]
                        ring
                      have hresidual : ∀ nextState,
                          |value nextState - mean| ≤ valueBound := by
                        intro nextState
                        rw [abs_le]
                        constructor <;> linarith [
                          (hvalue nextState).1, (hvalue nextState).2]
                      have hmgf := pmfExp_exp_mul_le_exp_half_bound_sq_mul_sq
                        (transition step current.1 action)
                        (fun nextState ↦ value nextState - mean)
                        valueBound scalar hvalueBound hcenter hresidual
                      have hfactor :
                          (fun nextState ↦
                            Real.exp
                              (scalar * (value nextState - mean) -
                                valueBound ^ 2 * scalar ^ 2 / 2)) =
                            fun nextState ↦
                              Real.exp (-valueBound ^ 2 * scalar ^ 2 / 2) *
                                Real.exp (scalar * (value nextState - mean)) := by
                        funext nextState
                        rw [← Real.exp_add]
                        congr 1
                        ring
                      simp only [Fin.snoc_last, Fin.val_last,
                        stageIndexedTrajectoryPrefixNextState]
                      simp only [lt_self_iff_false, ↓reduceDIte]
                      change pmfExp (transition step current.1 action)
                          (fun nextState ↦ Real.exp
                            (scalar * (value nextState - mean) -
                              valueBound ^ 2 * scalar ^ 2 / 2)) ≤ 1
                      rw [hfactor, pmfExp_const_mul]
                      calc
                        Real.exp (-valueBound ^ 2 * scalar ^ 2 / 2) *
                            pmfExp (transition step current.1 action)
                              (fun nextState ↦ Real.exp
                                (scalar * (value nextState - mean))) ≤
                          Real.exp (-valueBound ^ 2 * scalar ^ 2 / 2) *
                            Real.exp (valueBound ^ 2 * scalar ^ 2 / 2) := by
                              gcongr
                        _ = 1 := by
                          rw [← Real.exp_add]
                          ring_nf
                          simp
                  _ = 1 := by simp
          _ = 1 := by simp
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
                    let scalar := weight stateAction.1 stateAction.2
                    Real.exp
                      (scalar *
                          (value (stageIndexedTrajectoryPrefixNextState rollout
                            time.castSucc) -
                            pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                        valueBound ^ 2 * scalar ^ 2 / 2))) =
            pmfExp (stageIndexedTrajectoryPrefixLaw initial transition policy step)
              (fun current ↦
                let stateAction := current.2 time
                let scalar := weight stateAction.1 stateAction.2
                Real.exp
                  (scalar *
                      (value (stageIndexedTrajectoryPrefixNextState current time) -
                        pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                    valueBound ^ 2 * scalar ^ 2 / 2)) := by
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
                            let scalar := weight stateAction.1 stateAction.2
                            Real.exp
                              (scalar *
                                  (value (stageIndexedTrajectoryPrefixNextState rollout
                                    time.castSucc) -
                                    pmfExp (transition time.1 stateAction.1 stateAction.2)
                                      value) -
                                valueBound ^ 2 * scalar ^ 2 / 2))) =
                    pmfExp (policy step current.1)
                      (fun _action ↦
                        let stateAction := current.2 time
                        let scalar := weight stateAction.1 stateAction.2
                        Real.exp
                          (scalar *
                              (value (stageIndexedTrajectoryPrefixNextState current time) -
                                pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                            valueBound ^ 2 * scalar ^ 2 / 2)) := by
                      apply pmfExp_congr
                      intro action
                      rw [pmfExp_map]
                      simpa using pmfExp_const
                        (transition step current.1 action)
                        (let stateAction := current.2 time
                         let scalar := weight stateAction.1 stateAction.2
                         Real.exp
                           (scalar *
                               (value (stageIndexedTrajectoryPrefixNextState current time) -
                                 pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                             valueBound ^ 2 * scalar ^ 2 / 2))
                  _ =
                      (let stateAction := current.2 time
                       let scalar := weight stateAction.1 stateAction.2
                       Real.exp
                         (scalar *
                             (value (stageIndexedTrajectoryPrefixNextState current time) -
                               pmfExp (transition time.1 stateAction.1 stateAction.2) value) -
                           valueBound ^ 2 * scalar ^ 2 / 2)) := by simp
          _ ≤ 1 := ih time

end

end PreferenceRL
end AppliedModelingLib
