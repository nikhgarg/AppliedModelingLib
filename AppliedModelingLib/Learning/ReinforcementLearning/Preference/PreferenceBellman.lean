import AppliedModelingLib.Foundations.Probability.MDP

/-!
# Bellman surrogates for preference learning

Preference-to-reward reductions ultimately plan with a surrogate scalar reward.
This module names the corresponding one-step Bellman evaluation without
identifying it with a human preference label.
-/

namespace AppliedModelingLib

namespace PreferenceRL

/-- The Bellman one-step value of a policy under a learned scalar surrogate MDP. -/
noncomputable def preferenceBellmanStep
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    (continuation : State → ℝ) (state : State) : ℝ :=
  M.policyValueStep policy continuation state

/-- Preference Bellman evaluation is monotone in the surrogate continuation value. -/
theorem preferenceBellmanStep_mono
    {State Action : Type*} [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action]
    (M : FiniteMDP State Action) (policy : FiniteMDP.Policy State Action)
    {first second : State → ℝ} (hcontinuation : ∀ state, first state ≤ second state)
    (state : State) :
    preferenceBellmanStep M policy first state ≤
      preferenceBellmanStep M policy second state :=
  FiniteMDP.policyValueStep_mono M policy hcontinuation state

end PreferenceRL

end AppliedModelingLib
