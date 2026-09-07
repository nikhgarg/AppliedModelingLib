import AppliedModelingLib.Learning.ReinforcementLearning.Preference.Trajectory
import Mathlib.Tactic

/-!
# Approximate preference-based dynamic programming

This module contains the deterministic finite-horizon argument behind
preference-based policy search: a locally approximate Bellman action incurs at
most its local error on each remaining step.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/--
A selected arm is an approximate preference winner when its centered preference
gap against every competing arm is at least `-error`.
-/
def ApproximatePreferenceWinner {Arm : Type*}
    (preferenceGap : Arm → Arm → ℝ) (selected : Arm) (error : ℝ) : Prop :=
  ∀ competitor, -error ≤ preferenceGap selected competitor

/--
Under a calibrated, antisymmetric preference gap, an approximate preference
winner is approximately value-optimal against every competitor.
-/
theorem approximatePreferenceWinner_value_le {Arm : Type*}
    {value : Arm → ℝ} {preferenceGap : Arm → Arm → ℝ}
    (calibration : PreferenceValueCalibration Arm value preferenceGap)
    (hantisymmetric : ∀ first second,
      preferenceGap second first = -preferenceGap first second)
    {selected : Arm} {error : ℝ}
  (hwinner : ApproximatePreferenceWinner preferenceGap selected error)
    (competitor : Arm) :
    value competitor ≤ value selected + error / calibration.constant := by
  by_cases hvalue : value competitor ≤ value selected
  · have hnonneg : 0 ≤ error / calibration.constant := by
      have hself : preferenceGap selected selected = 0 := by
        linarith [hantisymmetric selected selected]
      have herror : 0 ≤ error := by
        linarith [hwinner selected]
      exact div_nonneg herror (le_of_lt calibration.constant_pos)
    linarith
  · have hgapValue : 0 < value competitor - value selected := by linarith
    have hcalibration := calibration.lower_bound competitor selected hgapValue
    have hgapBound : preferenceGap competitor selected ≤ error := by
      rw [hantisymmetric selected competitor]
      linarith [hwinner competitor]
    have hdiff : value competitor - value selected ≤ error / calibration.constant := by
      apply (le_div_iff₀ calibration.constant_pos).mpr
      have : calibration.constant * (value competitor - value selected) ≤ error :=
        hcalibration.trans hgapBound
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    linarith

/-- A deterministic action rule is Bellman-optimal up to an additive error. -/
def ApproximatelyGreedy {State Action : Type*}
    [Fintype State] [DecidableEq State] [Fintype Action] [DecidableEq Action]
    [Nonempty Action]
    (M : FiniteMDP State Action) (choose : State → Action)
    (continuation : State → ℝ) (error : ℝ) : Prop :=
  ∀ state,
    M.optimalStep continuation state ≤ M.actionValue continuation state (choose state) + error

/-- The finite Bellman maximum is monotone in its continuation value. -/
theorem optimalStep_mono
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) {first second : State → ℝ}
    (hcontinuation : ∀ state, first state ≤ second state) (state : State) :
    M.optimalStep first state ≤ M.optimalStep second state := by
  obtain ⟨action, haction⟩ := FiniteMDP.exists_action_optimalStep M first state
  rw [haction]
  exact (M.actionValue_mono hcontinuation state action).trans
    (FiniteMDP.actionValue_le_optimalStep M second state action)

/-- Adding a constant to a continuation value adds the same constant to every action value. -/
theorem actionValue_add_constant
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (continuation : State → ℝ) (constant : ℝ)
    (state : State) (action : Action) :
    M.actionValue (fun nextState => continuation nextState + constant) state action =
      M.actionValue continuation state action + constant := by
  unfold FiniteMDP.actionValue
  calc
    pmfExp (M.transition state action)
        (fun nextState => M.reward state action nextState +
          (continuation nextState + constant)) =
      pmfExp (M.transition state action)
        (fun nextState => (M.reward state action nextState + continuation nextState) + constant) := by
          apply pmfExp_congr
          intro nextState
          ring
    _ = pmfExp (M.transition state action)
          (fun nextState => M.reward state action nextState + continuation nextState) +
        pmfExp (M.transition state action) (fun _ => constant) := by
          rw [pmfExp_add]
    _ = pmfExp (M.transition state action)
          (fun nextState => M.reward state action nextState + continuation nextState) + constant := by
          rw [pmfExp_const]

/-- Adding a constant to a continuation value adds it to the Bellman maximum. -/
theorem optimalStep_add_constant
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (continuation : State → ℝ) (constant : ℝ)
    (state : State) :
    M.optimalStep (fun nextState => continuation nextState + constant) state =
      M.optimalStep continuation state + constant := by
  apply le_antisymm
  · obtain ⟨action, haction⟩ := FiniteMDP.exists_action_optimalStep M
      (fun nextState => continuation nextState + constant) state
    rw [haction, actionValue_add_constant]
    have hbound := FiniteMDP.actionValue_le_optimalStep M continuation state action
    linarith
  · obtain ⟨action, haction⟩ := FiniteMDP.exists_action_optimalStep M continuation state
    rw [haction]
    have hbound := FiniteMDP.actionValue_le_optimalStep M
      (fun nextState => continuation nextState + constant) state action
    rw [actionValue_add_constant] at hbound
    linarith

/--
If the same deterministic action rule is approximately greedy at every
remaining horizon, its finite-horizon value loses at most one local error per
step relative to the Bellman optimum.
-/
theorem optimalValue_le_horizonValue_add_of_approximatelyGreedy
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : State → Action) (error : ℝ)
    (hgreedy : ∀ remaining,
      ApproximatelyGreedy M choose
        (M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining) error) :
    ∀ remaining state,
      M.optimalValue remaining state ≤
        M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining state +
          (remaining : ℝ) * error := by
  intro remaining
  induction remaining with
  | zero =>
      intro state
      simp
  | succ remaining ih =>
      intro state
      calc
        M.optimalValue (remaining + 1) state =
            M.optimalStep (M.optimalValue remaining) state := by
              rfl
        _ ≤ M.optimalStep
              (fun nextState =>
                M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining nextState +
                  (remaining : ℝ) * error)
              state :=
          optimalStep_mono M (fun nextState => ih nextState) state
        _ = M.optimalStep
              (M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining)
              state + (remaining : ℝ) * error := by
          rw [optimalStep_add_constant]
        _ ≤ M.actionValue
              (M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining)
              state (choose state) + error + (remaining : ℝ) * error := by
          linarith [hgreedy remaining state]
        _ = M.horizonValue (FiniteMDP.deterministicPolicy choose) (remaining + 1) state +
              ((remaining + 1 : ℕ) : ℝ) * error := by
          rw [FiniteMDP.horizonValue_succ, FiniteMDP.policyValueStep_deterministic]
          push_cast
          ring

/--
The bounded-horizon form of approximate dynamic programming. Only local
greediness checks for strictly fewer than `horizon` remaining steps are needed.
-/
theorem optimalValue_le_horizonValue_add_of_approximatelyGreedy_upTo
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] [Nonempty Action]
    (M : FiniteMDP State Action) (choose : State → Action) (error : ℝ)
    (horizon : ℕ)
    (hgreedy : ∀ remaining, remaining < horizon →
      ApproximatelyGreedy M choose
        (M.horizonValue (FiniteMDP.deterministicPolicy choose) remaining) error)
    (state : State) :
    M.optimalValue horizon state ≤
      M.horizonValue (FiniteMDP.deterministicPolicy choose) horizon state +
        (horizon : ℝ) * error := by
  revert hgreedy state
  induction horizon with
  | zero =>
      intro _ state
      simp
  | succ horizon ih =>
      intro hgreedy state
      calc
        M.optimalValue (horizon + 1) state =
            M.optimalStep (M.optimalValue horizon) state := by
              rfl
        _ ≤ M.optimalStep
              (fun nextState =>
                M.horizonValue (FiniteMDP.deterministicPolicy choose) horizon nextState +
                  (horizon : ℝ) * error)
              state :=
          optimalStep_mono M
            (fun nextState => ih (fun remaining hremaining =>
              hgreedy remaining (Nat.lt_trans hremaining (Nat.lt_succ_self horizon))) nextState)
            state
        _ = M.optimalStep
              (M.horizonValue (FiniteMDP.deterministicPolicy choose) horizon)
              state + (horizon : ℝ) * error := by
          rw [optimalStep_add_constant]
        _ ≤ M.actionValue
              (M.horizonValue (FiniteMDP.deterministicPolicy choose) horizon)
              state (choose state) + error + (horizon : ℝ) * error := by
          linarith [hgreedy horizon (Nat.lt_succ_self horizon) state]
        _ = M.horizonValue (FiniteMDP.deterministicPolicy choose) (horizon + 1) state +
              ((horizon + 1 : ℕ) : ℝ) * error := by
          rw [FiniteMDP.horizonValue_succ, FiniteMDP.policyValueStep_deterministic]
          push_cast
          ring

/--
Choosing local error `constant * epsilon / horizon` makes the accumulated
`horizon * (localError / constant)` loss exactly `epsilon`.
-/
theorem horizon_accumulated_scaled_error
    (horizon : ℕ) (horizonPositive : 0 < horizon)
    (constant epsilon : ℝ) (hconstant : 0 < constant) :
    (horizon : ℝ) * ((constant * epsilon / (horizon : ℝ)) / constant) = epsilon := by
  have hhorizon : (horizon : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast horizonPositive)
  have hconstant' : constant ≠ 0 := ne_of_gt hconstant
  field_simp [hhorizon, hconstant']

end PreferenceRL

end AppliedModelingLib
