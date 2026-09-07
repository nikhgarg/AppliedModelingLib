import AppliedModelingLib.Learning.ReinforcementLearning.Preference.StageIndexedOccupancy
import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic

/-!
# Stage-indexed finite visitation stability

Finite-PMF rollout laws and their ℓ¹ stability under a learned, time-indexed
transition model.  The main bound is the discrete induction used in Zhan et
al. (2024), Lemma 5: an initial-law error and one expected transition error per
stage yield a linearly growing visitation error.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The state law at each stage of a finite stage-indexed rollout. -/
noncomputable def stageIndexedStateLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) : ℕ → PMF State
  | 0 => initial
  | time + 1 =>
      stageIndexedAdvanceStateLaw transition policy
        (stageIndexedStateLaw transition policy initial time) time

@[simp] theorem stageIndexedStateLaw_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) :
    stageIndexedStateLaw transition policy initial 0 = initial :=
  rfl

@[simp] theorem stageIndexedStateLaw_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) (time : ℕ) :
    stageIndexedStateLaw transition policy initial (time + 1) =
      stageIndexedAdvanceStateLaw transition policy
        (stageIndexedStateLaw transition policy initial time) time :=
  rfl

/-- The state-action visitation law induced by a state law and a policy at one stage. -/
noncomputable def stageIndexedStateActionLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (policy : StageIndexedPolicy State Action) (stateLaw : PMF State) (time : ℕ) :
    PMF (State × Action) :=
  stateLaw.bind fun state => (policy time state).map fun action => (state, action)

/-- Advancing a state law is binding its state-action visitation law through the transition. -/
theorem stageIndexedAdvanceStateLaw_eq_stateActionLaw_bind
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (stateLaw : PMF State) (time : ℕ) :
    stageIndexedAdvanceStateLaw transition policy stateLaw time =
      (stageIndexedStateActionLaw policy stateLaw time).bind fun stateAction =>
        transition time stateAction.1 stateAction.2 := by
  unfold stageIndexedAdvanceStateLaw stageIndexedStateActionLaw
  rw [PMF.bind_bind]
  congr 1
  funext state
  rw [PMF.bind_map]
  rfl

/-- The next-stage expectation is the current state-action expectation of
the transition-conditional score.  This is the finite rollout identity used
when a confidence correction retains a true-transition second moment rather
than replacing it by a uniform range. -/
theorem pmfExp_stageIndexedStateLaw_succ_eq_stateAction_transition
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (time : ℕ) (score : State → ℝ) :
    pmfExp (stageIndexedStateLaw transition policy initial (time + 1)) score =
      pmfExp
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw transition policy initial time) time)
        (fun stateAction => pmfExp (transition time stateAction.1 stateAction.2) score) := by
  rw [stageIndexedStateLaw_succ, stageIndexedAdvanceStateLaw_eq_stateActionLaw_bind,
    pmfExp_bind]

/-- Atomwise stage occupancy followed by the transition kernel sums to the
next-stage expectation.  This is the expanded finite form of
`pmfExp_stageIndexedStateLaw_succ_eq_stateAction_transition`. -/
theorem sum_stageIndexedStateActionLaw_mul_pmfExp_transition_eq_pmfExp_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (time : ℕ) (score : State → ℝ) :
    (∑ stateAction : State × Action,
      (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw transition policy initial time) time stateAction).toReal *
        pmfExp (transition time stateAction.1 stateAction.2) score) =
      pmfExp (stageIndexedStateLaw transition policy initial (time + 1)) score := by
  change pmfExp
      (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw transition policy initial time) time)
      (fun stateAction => pmfExp (transition time stateAction.1 stateAction.2) score) = _
  exact (pmfExp_stageIndexedStateLaw_succ_eq_stateAction_transition
    transition policy initial time score).symm

/-- A nonnegative terminal-zero score loses no mass when a transition score is
shifted one stage forward.  The left side is the source form with a
state-action occupancy and a true-transition expectation; the right side is
the corresponding state-law score surface. -/
theorem sum_stageIndexedStateAction_transition_score_le_sum_state_score
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (horizon : ℕ) (score : ℕ → State → ℝ)
    (hnonneg : ∀ remaining state, 0 ≤ score remaining state)
    (hterminal : ∀ state, score 0 state = 0) :
    (∑ time ∈ Finset.range horizon, ∑ stateAction : State × Action,
      (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw transition policy initial time) time stateAction).toReal *
        pmfExp (transition time stateAction.1 stateAction.2)
          (score (horizon - time - 1))) ≤
      ∑ time ∈ Finset.range horizon,
        pmfExp (stageIndexedStateLaw transition policy initial time)
          (score (horizon - time)) := by
  classical
  let shifted : ℕ → ℝ := fun time =>
    pmfExp (stageIndexedStateLaw transition policy initial time) (score (horizon - time))
  have hstep : ∀ time,
      (∑ stateAction : State × Action,
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw transition policy initial time) time stateAction).toReal *
          pmfExp (transition time stateAction.1 stateAction.2)
            (score (horizon - time - 1))) = shifted (time + 1) := by
    intro time
    have hremaining : horizon - time - 1 = horizon - (time + 1) := by omega
    rw [hremaining, sum_stageIndexedStateActionLaw_mul_pmfExp_transition_eq_pmfExp_succ]
  have hshifted_nonneg : 0 ≤ shifted 0 := by
    dsimp only [shifted]
    exact pmfExp_nonneg_of_forall_nonneg _ _ (hnonneg horizon)
  have hshifted_terminal : shifted horizon = 0 := by
    dsimp only [shifted]
    have hremaining : horizon - horizon = 0 := by omega
    rw [hremaining]
    calc
      pmfExp (stageIndexedStateLaw transition policy initial horizon) (score 0) =
          pmfExp (stageIndexedStateLaw transition policy initial horizon) (fun _ => 0) := by
            apply pmfExp_congr
            intro state
            exact hterminal state
      _ = 0 := by simp
  have hsplit : ∀ length : ℕ,
      shifted 0 + ∑ time ∈ Finset.range length, shifted (time + 1) =
        ∑ time ∈ Finset.range (length + 1), shifted time := by
    intro length
    induction length with
    | zero => simp
    | succ length ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
        ring
  cases horizon with
  | zero => simp
  | succ length =>
      calc
        (∑ time ∈ Finset.range (length + 1), ∑ stateAction : State × Action,
          (stageIndexedStateActionLaw policy
            (stageIndexedStateLaw transition policy initial time) time stateAction).toReal *
            pmfExp (transition time stateAction.1 stateAction.2)
              (score (length + 1 - time - 1))) =
            ∑ time ∈ Finset.range (length + 1), shifted (time + 1) := by
              apply Finset.sum_congr rfl
              intro time _
              exact hstep time
        _ = ∑ time ∈ Finset.range length, shifted (time + 1) := by
              rw [Finset.sum_range_succ]
              simp only [hshifted_terminal, add_zero]
        _ ≤ shifted 0 + ∑ time ∈ Finset.range length, shifted (time + 1) :=
              le_add_of_nonneg_left hshifted_nonneg
        _ = ∑ time ∈ Finset.range (length + 1), shifted time := hsplit length
        _ = ∑ time ∈ Finset.range (length + 1),
            pmfExp (stageIndexedStateLaw transition policy initial time)
              (score (length + 1 - time)) := by rfl

/-- A common action kernel cannot increase a state-law ℓ¹ discrepancy. -/
theorem stageIndexedStateActionLaw_l1_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (policy : StageIndexedPolicy State Action)
    (firstStateLaw secondStateLaw : PMF State) (time : ℕ) :
    pmfL1Error (stageIndexedStateActionLaw policy firstStateLaw time)
      (stageIndexedStateActionLaw policy secondStateLaw time) ≤
      pmfL1Error firstStateLaw secondStateLaw := by
  exact pmfL1Error_bind_sameKernel_le firstStateLaw secondStateLaw
    (fun state => (policy time state).map fun action => (state, action))

/-- The true state-action rollout law corresponding to a stage-indexed policy. -/
noncomputable def stageIndexedTrueStateActionRollout
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State) (trueTransition : StageIndexedTransitionModel State Action) :
    StateActionRolloutLaw (StageIndexedPolicy State Action) ℕ State Action :=
  fun policy time =>
    stageIndexedStateActionLaw policy
      (stageIndexedStateLaw trueTransition policy trueInitial time) time

/--
One-step state-law error is at most the previous visitation error plus the
true-rollout expected transition error.  This is the finite-PMF mixture step
in the proof of Zhan et al.'s Lemma 5.
-/
theorem stageIndexedAdvanceStateLaw_l1_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition estimatedTransition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (estimatedStateLaw : PMF State) (time : ℕ) :
    pmfL1Error
        (stageIndexedAdvanceStateLaw trueTransition policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time)
        (stageIndexedAdvanceStateLaw estimatedTransition policy estimatedStateLaw time) ≤
      pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time) estimatedStateLaw +
        expectedTransitionL1Error trueTransition estimatedTransition
          (stageIndexedTrueStateActionRollout trueInitial trueTransition)
          policy time := by
  have hstateAction :
      pmfL1Error (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw trueTransition policy trueInitial time) time)
        (stageIndexedStateActionLaw policy estimatedStateLaw time) ≤
        pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time) estimatedStateLaw :=
    stageIndexedStateActionLaw_l1_le policy
      (stageIndexedStateLaw trueTransition policy trueInitial time) estimatedStateLaw time
  have hrollout :
      pmfExp (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw trueTransition policy trueInitial time) time) (fun stateAction =>
        pmfL1Error (trueTransition time stateAction.1 stateAction.2)
          (estimatedTransition time stateAction.1 stateAction.2)) =
      expectedTransitionL1Error trueTransition estimatedTransition
        (stageIndexedTrueStateActionRollout trueInitial trueTransition)
        policy time := by
    unfold expectedTransitionL1Error stageIndexedTrueStateActionRollout
    apply pmfExp_congr
    intro stateAction
    exact pmfL1Error_comm _ _
  calc
    pmfL1Error
        (stageIndexedAdvanceStateLaw trueTransition policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time)
        (stageIndexedAdvanceStateLaw estimatedTransition policy estimatedStateLaw time) =
      pmfL1Error
        ((stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time).bind fun stateAction =>
          trueTransition time stateAction.1 stateAction.2)
        ((stageIndexedStateActionLaw policy estimatedStateLaw time).bind fun stateAction =>
          estimatedTransition time stateAction.1 stateAction.2) := by
        rw [stageIndexedAdvanceStateLaw_eq_stateActionLaw_bind,
          stageIndexedAdvanceStateLaw_eq_stateActionLaw_bind]
    _ ≤ pmfL1Error (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time)
          (stageIndexedStateActionLaw policy estimatedStateLaw time) +
        pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time) (fun stateAction =>
          pmfL1Error (trueTransition time stateAction.1 stateAction.2)
            (estimatedTransition time stateAction.1 stateAction.2)) :=
      pmfL1Error_bind_le _ _ _ _
    _ ≤ pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time) estimatedStateLaw +
        pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time) (fun stateAction =>
          pmfL1Error (trueTransition time stateAction.1 stateAction.2)
            (estimatedTransition time stateAction.1 stateAction.2)) := by
      exact add_le_add_left hstateAction _
    _ = pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time)
          estimatedStateLaw +
        expectedTransitionL1Error trueTransition estimatedTransition
          (stageIndexedTrueStateActionRollout trueInitial trueTransition)
          policy time := by
      rw [hrollout]

/--
Definition 1's error envelope yields the stage-indexed state-visitation bound
used in Zhan et al. (2024), Lemma 5.  Time zero here corresponds to the
paper's first visitation distribution, hence the factor `time + 1`.
-/
theorem rewardFreeOracle_stateVisitationError_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : StageIndexedTransitionModel State Action)
    {tolerance : ℝ}
    (certificate : RewardFreeTransitionOracleCertificate
      (StageIndexedPolicy State Action) ℕ State Action
      trueInitial trueTransition
      (stageIndexedTrueStateActionRollout trueInitial trueTransition) tolerance)
    (policy : StageIndexedPolicy State Action) :
    ∀ time : ℕ,
      pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time)
        (stageIndexedStateLaw certificate.estimatedTransition policy
          certificate.estimatedInitial time) ≤
        ((time + 1 : ℕ) : ℝ) * tolerance := by
  intro time
  induction time with
  | zero =>
      calc
        pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial 0)
            (stageIndexedStateLaw certificate.estimatedTransition policy
              certificate.estimatedInitial 0) =
            pmfL1Error trueInitial certificate.estimatedInitial := by rfl
        _ = pmfL1Error certificate.estimatedInitial trueInitial :=
          pmfL1Error_comm _ _
        _ ≤ tolerance := certificate.initial_error_bound
        _ = ((0 + 1 : ℕ) : ℝ) * tolerance := by norm_num
  | succ time ih =>
      calc
        pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial (time + 1))
            (stageIndexedStateLaw certificate.estimatedTransition policy
              certificate.estimatedInitial (time + 1)) =
            pmfL1Error
              (stageIndexedAdvanceStateLaw trueTransition policy
                (stageIndexedStateLaw trueTransition policy trueInitial time) time)
              (stageIndexedAdvanceStateLaw certificate.estimatedTransition policy
                (stageIndexedStateLaw certificate.estimatedTransition policy
                  certificate.estimatedInitial time) time) := by rfl
        _ ≤ pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time)
              (stageIndexedStateLaw certificate.estimatedTransition policy
                certificate.estimatedInitial time) +
            expectedTransitionL1Error trueTransition certificate.estimatedTransition
              (stageIndexedTrueStateActionRollout trueInitial trueTransition)
              policy time :=
          stageIndexedAdvanceStateLaw_l1_le trueInitial trueTransition
            certificate.estimatedTransition policy _ time
        _ ≤ ((time + 1 : ℕ) : ℝ) * tolerance + tolerance := by
          exact add_le_add ih (certificate.rollout_error_bound policy time)
        _ = ((time + 1 + 1 : ℕ) : ℝ) * tolerance := by
          push_cast
          ring

/--
The corresponding state-action visitation statement of Zhan et al.'s Lemma 5.
The true rollout is compared with the same policy rolled out in the estimated
model, and the bound grows by one oracle tolerance per source stage.
-/
theorem rewardFreeOracle_visitationError_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : StageIndexedTransitionModel State Action)
    {tolerance : ℝ}
    (certificate : RewardFreeTransitionOracleCertificate
      (StageIndexedPolicy State Action) ℕ State Action
      trueInitial trueTransition
      (stageIndexedTrueStateActionRollout trueInitial trueTransition) tolerance)
    (policy : StageIndexedPolicy State Action) (time : ℕ) :
    pmfL1Error
        (stageIndexedTrueStateActionRollout trueInitial trueTransition policy time)
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) ≤
      ((time + 1 : ℕ) : ℝ) * tolerance := by
  calc
    pmfL1Error
        (stageIndexedTrueStateActionRollout trueInitial trueTransition policy time)
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) =
      pmfL1Error
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time)
        (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) := by
        rfl
    _ ≤ pmfL1Error (stageIndexedStateLaw trueTransition policy trueInitial time)
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) :=
      stageIndexedStateActionLaw_l1_le policy _ _ time
    _ ≤ ((time + 1 : ℕ) : ℝ) * tolerance :=
      rewardFreeOracle_stateVisitationError_le trueInitial trueTransition certificate policy time

/-- The cumulative expected score of a stage-indexed rollout. -/
noncomputable def stageIndexedVisitationScore
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State)
    (score : StageIndexedReward State Action) (horizon : ℕ) : ℝ :=
  ∑ time ∈ Finset.range horizon,
    pmfExp (stageIndexedStateActionLaw policy
      (stageIndexedStateLaw transition policy initial time) time) fun stateAction =>
      score time stateAction.1 stateAction.2

/--
The bounded scalar-score consequence of Zhan et al.'s Lemmas 5--6.  It keeps
the exact sum of stagewise visitation errors rather than silently replacing it
with a coarser horizon polynomial.  A vector inner product `φ_h(s,a)ᵀ v_h`
instantiates `score` after separately supplying its norm-derived bound.
-/
theorem rewardFreeOracle_boundedVisitationScoreError_le
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (trueInitial : PMF State)
    (trueTransition : StageIndexedTransitionModel State Action)
    {tolerance : ℝ}
    (certificate : RewardFreeTransitionOracleCertificate
      (StageIndexedPolicy State Action) ℕ State Action
      trueInitial trueTransition
      (stageIndexedTrueStateActionRollout trueInitial trueTransition) tolerance)
    (policy : StageIndexedPolicy State Action)
    (score : StageIndexedReward State Action) (bound : ℝ)
    (hbound : 0 ≤ bound)
    (hscore : ∀ time state action, |score time state action| ≤ bound)
    (horizon : ℕ) :
    |stageIndexedVisitationScore trueTransition policy trueInitial score horizon -
      stageIndexedVisitationScore certificate.estimatedTransition policy
        certificate.estimatedInitial score horizon| ≤
      ∑ time ∈ Finset.range horizon,
        bound * ((time + 1 : ℕ) : ℝ) * tolerance := by
  unfold stageIndexedVisitationScore
  calc
    |(∑ time ∈ Finset.range horizon,
      (pmfExp (stageIndexedStateActionLaw policy
        (stageIndexedStateLaw trueTransition policy trueInitial time) time) fun stateAction =>
        score time stateAction.1 stateAction.2)) -
      (∑ time ∈ Finset.range horizon,
        (pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) fun stateAction =>
          score time stateAction.1 stateAction.2))| =
        |(∑ time ∈ Finset.range horizon,
          ((pmfExp (stageIndexedStateActionLaw policy
            (stageIndexedStateLaw trueTransition policy trueInitial time) time) fun stateAction =>
            score time stateAction.1 stateAction.2) -
          pmfExp (stageIndexedStateActionLaw policy
            (stageIndexedStateLaw certificate.estimatedTransition policy
              certificate.estimatedInitial time) time) fun stateAction =>
            score time stateAction.1 stateAction.2))| := by
          rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ time ∈ Finset.range horizon,
        |((pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time) fun stateAction =>
          score time stateAction.1 stateAction.2) -
        pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) fun stateAction =>
          score time stateAction.1 stateAction.2)| :=
      Finset.abs_sum_le_sum_abs _ (Finset.range horizon)
    _ ≤ ∑ time ∈ Finset.range horizon,
        bound * ((time + 1 : ℕ) : ℝ) * tolerance := by
      apply Finset.sum_le_sum
      intro time htime
      calc
        |(pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw trueTransition policy trueInitial time) time) fun stateAction =>
          score time stateAction.1 stateAction.2) -
        pmfExp (stageIndexedStateActionLaw policy
          (stageIndexedStateLaw certificate.estimatedTransition policy
            certificate.estimatedInitial time) time) fun stateAction =>
          score time stateAction.1 stateAction.2| ≤
          bound * pmfL1Error
            (stageIndexedTrueStateActionRollout trueInitial trueTransition policy time)
            (stageIndexedStateActionLaw policy
              (stageIndexedStateLaw certificate.estimatedTransition policy
                certificate.estimatedInitial time) time) := by
          exact abs_pmfExp_sub_le_bound_mul_pmfL1Error _ _ _ bound
            (fun stateAction => hscore time stateAction.1 stateAction.2)
        _ ≤ bound * (((time + 1 : ℕ) : ℝ) * tolerance) := by
          exact mul_le_mul_of_nonneg_left
            (rewardFreeOracle_visitationError_le trueInitial trueTransition
              certificate policy time) hbound
        _ = bound * ((time + 1 : ℕ) : ℝ) * tolerance := by ring

end PreferenceRL

end AppliedModelingLib
