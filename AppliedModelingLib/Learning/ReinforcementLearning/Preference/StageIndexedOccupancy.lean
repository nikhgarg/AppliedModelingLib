import AppliedModelingLib.Foundations.Probability.PMFKernel
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Tactic

/-!
# Stage-indexed policy values and occupancy features

Finite-horizon preference-RL papers often use a transition kernel, reward, and
policy that each vary by stage.  This module gives the finite-PMF policy value
and the occupancy-feature linearity identity in that setting.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- A finite transition law indexed by an absolute stage. -/
abbrev StageIndexedTransitionModel (State Action : Type*) :=
  ℕ → State → PMFKernel Action State

/-- A randomized policy whose action law may vary by absolute stage. -/
abbrev StageIndexedPolicy (State Action : Type*) :=
  ℕ → PMFKernel State Action

/-- A state-action reward function indexed by an absolute stage. -/
abbrev StageIndexedReward (State Action : Type*) :=
  ℕ → State → Action → ℝ

/-- The next-state law after one stage under the stage-indexed model and policy. -/
noncomputable def stageIndexedAdvanceStateLaw
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action) (initial : PMF State) (time : ℕ) : PMF State :=
  initial.bind fun state =>
    (policy time state).bind fun action => transition time state action

/--
Expected return of a stage-indexed policy from an initial state law with the
given number of stages remaining.
-/
noncomputable def stageIndexedPolicyValue
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime : ℕ) : ℕ → ℝ
  | 0 => 0
  | remaining + 1 =>
      (pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action => reward startTime state action) +
        stageIndexedPolicyValue transition reward policy
          (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
          remaining

@[simp] theorem stageIndexedPolicyValue_zero
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime : ℕ) :
    stageIndexedPolicyValue transition reward policy initial startTime 0 = 0 :=
  rfl

@[simp] theorem stageIndexedPolicyValue_succ
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime remaining : ℕ) :
    stageIndexedPolicyValue transition reward policy initial startTime (remaining + 1) =
      (pmfExp initial (fun state =>
        pmfExp (policy startTime state) fun action => reward startTime state action) +
        stageIndexedPolicyValue transition reward policy
          (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
          remaining) := by
  simp [stageIndexedPolicyValue]

/-- Pointwise reward domination propagates through a fixed finite-horizon
stage-indexed policy value.  This is the monotonicity bridge used when a
paper's clipped one-step confidence cost is replaced by a coordinate-only
large/small occupancy envelope. -/
theorem stageIndexedPolicyValue_mono_reward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (lower upper : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action)
    (hreward : ∀ time state action, lower time state action ≤ upper time state action) :
    ∀ (initial : PMF State) startTime horizon,
      stageIndexedPolicyValue transition lower policy initial startTime horizon ≤
        stageIndexedPolicyValue transition upper policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp
  | succ remaining ih =>
      rw [stageIndexedPolicyValue_succ, stageIndexedPolicyValue_succ]
      apply add_le_add
      · refine pmfExp_le_pmfExp_of_forall_le initial _ _ ?_
        intro state
        refine pmfExp_le_pmfExp_of_forall_le (policy startTime state) _ _ ?_
        intro action
        exact hreward startTime state action
      · exact ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)

/-- Finite-horizon reward monotonicity needs pointwise domination only on the
stages actually reached from the specified start time.  This diagonal form
avoids imposing an artificial condition on a paper's terminal extension. -/
theorem stageIndexedPolicyValue_mono_reward_of_elapsed
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (lower upper : StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) (startTime horizon : ℕ),
      (∀ elapsed, elapsed < horizon → ∀ state action,
        lower (startTime + elapsed) state action ≤ upper (startTime + elapsed) state action) →
      stageIndexedPolicyValue transition lower policy initial startTime horizon ≤
        stageIndexedPolicyValue transition upper policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => intro _; simp
  | succ remaining ih =>
      intro hreward
      rw [stageIndexedPolicyValue_succ, stageIndexedPolicyValue_succ]
      apply add_le_add
      · refine pmfExp_le_pmfExp_of_forall_le initial _ _ ?_
        intro state
        refine pmfExp_le_pmfExp_of_forall_le (policy startTime state) _ _ ?_
        intro action
        simpa only [Nat.add_zero] using hreward 0 (by omega) state action
      · apply ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
        intro elapsed helapsed state action
        have hlt : elapsed + 1 < remaining + 1 := by omega
        have hpoint := hreward (elapsed + 1) hlt state action
        simpa only [Nat.add_assoc, Nat.add_comm 1 elapsed, Nat.add_left_comm] using hpoint

/-- A nonnegative stage reward has nonnegative finite-horizon policy value. -/
theorem stageIndexedPolicyValue_nonneg
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (hreward : ∀ time state action, 0 ≤ reward time state action) :
    ∀ (initial : PMF State) startTime horizon,
      0 ≤ stageIndexedPolicyValue transition reward policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp
  | succ remaining ih =>
      rw [stageIndexedPolicyValue_succ]
      apply add_nonneg
      · apply pmfExp_nonneg_of_forall_nonneg
        intro state
        apply pmfExp_nonneg_of_forall_nonneg
        intro action
        exact hreward startTime state action
      · exact ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)

/-- Squaring a finite-horizon policy value costs at most one factor of the
remaining horizon times the policy value of squared rewards.
This is the finite Jensen--Cauchy step used to turn a pointwise width
recurrence into a cumulative squared-width bound. -/
theorem stageIndexedPolicyValue_sq_le_horizon_mul_sq_reward
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      (stageIndexedPolicyValue transition reward policy initial startTime horizon) ^ 2 ≤
        (horizon : ℝ) * stageIndexedPolicyValue transition
          (fun time state action => (reward time state action) ^ 2)
          policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero => simp
  | succ remaining ih =>
      rw [stageIndexedPolicyValue_succ, stageIndexedPolicyValue_succ]
      let current : ℝ := pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action => reward startTime state action
      let currentSq : ℝ := pmfExp initial fun state =>
        pmfExp (policy startTime state) fun action => (reward startTime state action) ^ 2
      let nextInitial := stageIndexedAdvanceStateLaw transition policy initial startTime
      let next : ℝ := stageIndexedPolicyValue transition reward policy
        nextInitial (startTime + 1) remaining
      let nextSq : ℝ := stageIndexedPolicyValue transition
        (fun time state action => (reward time state action) ^ 2)
        policy nextInitial (startTime + 1) remaining
      have hcurrent_sq : current ^ 2 ≤ currentSq := by
        dsimp only [current, currentSq]
        calc
          (pmfExp initial fun state =>
              pmfExp (policy startTime state) fun action => reward startTime state action) ^ 2 ≤
              pmfExp initial (fun state =>
                (pmfExp (policy startTime state) fun action =>
                  reward startTime state action) ^ 2) :=
            pmfExp_sq_le_pmfExp_sq initial _
          _ ≤ pmfExp initial (fun state =>
                pmfExp (policy startTime state) fun action =>
                  (reward startTime state action) ^ 2) := by
            apply pmfExp_le_pmfExp_of_forall_le
            intro state
            exact pmfExp_sq_le_pmfExp_sq (policy startTime state) _
      have hnext_sq : next ^ 2 ≤ (remaining : ℝ) * nextSq := by
        dsimp only [next, nextSq, nextInitial]
        exact ih (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
      change (current + next) ^ 2 ≤ ((remaining + 1 : ℕ) : ℝ) * (currentSq + nextSq)
      rw [Nat.cast_add, Nat.cast_one]
      by_cases hremaining : remaining = 0
      · subst remaining
        simp [next, nextSq] at hcurrent_sq ⊢
        nlinarith
      · have hremaining_pos : 0 < (remaining : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hremaining
        have hkey :
            (remaining : ℝ) * (current + next) ^ 2 ≤
              (remaining : ℝ) * ((remaining : ℝ) + 1) * (currentSq + nextSq) := by
          have hcurrent_scaled :
              (remaining : ℝ) * ((remaining : ℝ) + 1) * current ^ 2 ≤
                (remaining : ℝ) * ((remaining : ℝ) + 1) * currentSq :=
            mul_le_mul_of_nonneg_left hcurrent_sq (by positivity)
          have hnext_scaled :
              ((remaining : ℝ) + 1) * next ^ 2 ≤
                (remaining : ℝ) * ((remaining : ℝ) + 1) * nextSq :=
            calc
              ((remaining : ℝ) + 1) * next ^ 2 ≤
                  ((remaining : ℝ) + 1) * ((remaining : ℝ) * nextSq) :=
                mul_le_mul_of_nonneg_left hnext_sq (by positivity)
              _ = _ := by ring
          nlinarith [sq_nonneg ((remaining : ℝ) * current - next)]
        nlinarith

/-- The occupancy-weighted total of a stage-indexed scalar feature. -/
noncomputable def stageIndexedOccupancyFeatureMass
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (feature : StageIndexedReward State Action) : ℝ :=
  stageIndexedPolicyValue transition feature policy initial startTime horizon

/-- Scaling a stage-indexed reward scales its policy value. -/
theorem stageIndexedPolicyValue_scale
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (reward : StageIndexedReward State Action) (policy : StageIndexedPolicy State Action)
    (parameter : ℝ) :
    ∀ (initial : PMF State) startTime horizon,
      stageIndexedPolicyValue transition
          (fun time state action => parameter * reward time state action)
          policy initial startTime horizon =
        parameter * stageIndexedPolicyValue transition reward policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp
  | succ horizon ih =>
      rw [stageIndexedPolicyValue_succ]
      have hcurrent :
          pmfExp initial (fun state =>
            pmfExp (policy startTime state) fun action =>
              parameter * reward startTime state action) =
            parameter * pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action => reward startTime state action) := by
        calc
          pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                parameter * reward startTime state action) =
            pmfExp initial (fun state =>
              parameter * pmfExp (policy startTime state)
                (fun action => reward startTime state action)) := by
              apply pmfExp_congr
              intro state
              exact pmfExp_const_mul (policy startTime state) parameter
                (fun action => reward startTime state action)
          _ = parameter * pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action => reward startTime state action) :=
            pmfExp_const_mul initial parameter _
      rw [hcurrent, ih,
        stageIndexedPolicyValue_succ transition reward policy initial startTime horizon]
      ring

/-- Finite sums of stage-indexed rewards commute with policy evaluation. -/
theorem stageIndexedPolicyValue_sum
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Fintype Feature]
    (transition : StageIndexedTransitionModel State Action)
    (reward : Feature → StageIndexedReward State Action)
    (policy : StageIndexedPolicy State Action) :
    ∀ (initial : PMF State) startTime horizon,
      stageIndexedPolicyValue transition
          (fun time state action => ∑ coordinate : Feature, reward coordinate time state action)
          policy initial startTime horizon =
        ∑ coordinate : Feature,
          stageIndexedPolicyValue transition (reward coordinate) policy initial startTime horizon := by
  intro initial startTime horizon
  induction horizon generalizing initial startTime with
  | zero =>
      simp
  | succ horizon ih =>
      rw [stageIndexedPolicyValue_succ]
      have hcurrent :
          pmfExp initial (fun state =>
            pmfExp (policy startTime state) fun action =>
              ∑ coordinate : Feature, reward coordinate startTime state action) =
            ∑ coordinate : Feature,
              pmfExp initial (fun state =>
                pmfExp (policy startTime state)
                  (fun action => reward coordinate startTime state action)) := by
        calc
          pmfExp initial (fun state =>
              pmfExp (policy startTime state) fun action =>
                ∑ coordinate : Feature, reward coordinate startTime state action) =
            pmfExp initial (fun state =>
              ∑ coordinate : Feature,
                pmfExp (policy startTime state)
                  (fun action => reward coordinate startTime state action)) := by
              apply pmfExp_congr
              intro state
              exact pmfExp_univ_sum (policy startTime state)
                (fun coordinate action => reward coordinate startTime state action)
          _ = ∑ coordinate : Feature,
              pmfExp initial (fun state =>
                pmfExp (policy startTime state)
                  (fun action => reward coordinate startTime state action)) :=
            pmfExp_univ_sum initial _
      have hsumSucc :
          (∑ coordinate : Feature,
            stageIndexedPolicyValue transition (reward coordinate) policy
              initial startTime (horizon + 1)) =
            ∑ coordinate : Feature,
              (pmfExp initial (fun state =>
                pmfExp (policy startTime state)
                  (fun action => reward coordinate startTime state action)) +
                stageIndexedPolicyValue transition (reward coordinate) policy
                  (stageIndexedAdvanceStateLaw transition policy initial startTime) (startTime + 1)
                  horizon) := by
        apply Finset.sum_congr rfl
        intro coordinate _
        exact stageIndexedPolicyValue_succ transition (reward coordinate) policy
          initial startTime horizon
      rw [hcurrent, ih, hsumSucc, Finset.sum_add_distrib]

/--
Stage-indexed linear reward evaluation is the parameter-weighted sum of the
occupancy feature masses.  A block coordinate `(h, j)` instantiates the
time-specific feature vectors in Zhan et al.'s Assumption 1.
-/
theorem stageIndexedPolicyValue_linear
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Fintype Feature]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (feature : Feature → StageIndexedReward State Action) (parameter : Feature → ℝ) :
    stageIndexedPolicyValue transition
        (fun time state action => ∑ coordinate : Feature,
          parameter coordinate * feature coordinate time state action)
        policy initial startTime horizon =
      ∑ coordinate : Feature, parameter coordinate *
        stageIndexedOccupancyFeatureMass transition policy initial startTime horizon
          (feature coordinate) := by
  calc
    stageIndexedPolicyValue transition
        (fun time state action => ∑ coordinate : Feature,
          parameter coordinate * feature coordinate time state action)
        policy initial startTime horizon =
      ∑ coordinate : Feature,
        stageIndexedPolicyValue transition
          (fun time state action => parameter coordinate *
            feature coordinate time state action)
          policy initial startTime horizon :=
      stageIndexedPolicyValue_sum transition
        (fun coordinate time state action => parameter coordinate *
          feature coordinate time state action)
        policy initial startTime horizon
    _ = ∑ coordinate : Feature, parameter coordinate *
        stageIndexedPolicyValue transition (feature coordinate)
          policy initial startTime horizon := by
      apply Finset.sum_congr rfl
      intro coordinate _
      exact stageIndexedPolicyValue_scale transition (feature coordinate) policy
        (parameter coordinate) initial startTime horizon
    _ = ∑ coordinate : Feature, parameter coordinate *
        stageIndexedOccupancyFeatureMass transition policy initial startTime horizon
          (feature coordinate) :=
      rfl

/--
The occupancy contribution of one coordinate whose reward parameter may vary
by stage.
-/
noncomputable def stageIndexedParameterFeatureContribution
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (feature : ℕ → State → Action → Feature → ℝ)
    (parameter : ℕ → Feature → ℝ) (coordinate : Feature) : ℝ :=
  stageIndexedOccupancyFeatureMass transition policy initial startTime horizon
    (fun time state action => parameter time coordinate * feature time state action coordinate)

/--
Linear policy value for a genuinely stage-indexed feature map and parameter.
This is the finite-PMF form of a reward specification
`r_h(s,a) = Σ_j θ_h,j φ_h,j(s,a)`.
-/
theorem stageIndexedPolicyValue_timeLinear
    {State Action Feature : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Fintype Feature]
    (transition : StageIndexedTransitionModel State Action)
    (policy : StageIndexedPolicy State Action)
    (initial : PMF State) (startTime horizon : ℕ)
    (feature : ℕ → State → Action → Feature → ℝ)
    (parameter : ℕ → Feature → ℝ) :
    stageIndexedPolicyValue transition
        (fun time state action => ∑ coordinate : Feature,
          parameter time coordinate * feature time state action coordinate)
        policy initial startTime horizon =
      ∑ coordinate : Feature,
        stageIndexedParameterFeatureContribution transition policy initial startTime horizon
          feature parameter coordinate := by
  calc
    stageIndexedPolicyValue transition
        (fun time state action => ∑ coordinate : Feature,
          parameter time coordinate * feature time state action coordinate)
        policy initial startTime horizon =
      ∑ coordinate : Feature,
        stageIndexedPolicyValue transition
          (fun time state action =>
            parameter time coordinate * feature time state action coordinate)
          policy initial startTime horizon :=
      stageIndexedPolicyValue_sum transition
        (fun coordinate time state action =>
          parameter time coordinate * feature time state action coordinate)
        policy initial startTime horizon
    _ = ∑ coordinate : Feature,
        stageIndexedParameterFeatureContribution transition policy initial startTime horizon
          feature parameter coordinate :=
      rfl

end PreferenceRL

end AppliedModelingLib
