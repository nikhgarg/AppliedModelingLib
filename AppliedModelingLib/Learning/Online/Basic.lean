import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import AppliedModelingLib.Foundations.Probability.PMFKernel

/-!
# Finite full-information online learning

Paper-independent definitions for a finite-action, finite-horizon,
full-information online learning problem.  Loss sequences are deterministic
paths: no probability-space assumptions are hidden in the regret API.

## Main declarations

- `LossSequence`
- `PlaySequence`
- `expectedLossAt`
- `cumulativeExpectedLoss`
- `cumulativeLoss`
- `RewardSequence` and `lossOfReward`
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- A deterministic loss function for each round of a finite online problem. -/
abbrev LossSequence (Action : Type*) (horizon : ℕ) :=
  Fin horizon → Action → ℝ

/-- A learner's distribution-valued decision at each round. -/
abbrev PlaySequence (Action : Type*) (horizon : ℕ) :=
  PMFKernel (Fin horizon) Action

/-- The expected loss of one distribution-valued decision on one realized loss vector. -/
noncomputable def expectedLossAt {Action : Type*} [Fintype Action] [DecidableEq Action]
    {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon) (round : Fin horizon) : ℝ :=
  pmfExp (plays round) (losses round)

/-- The learner's pathwise cumulative expected loss over the finite horizon. -/
noncomputable def cumulativeExpectedLoss {Action : Type*} [Fintype Action] [DecidableEq Action]
    {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon) : ℝ :=
  ∑ round : Fin horizon, expectedLossAt losses plays round

/-- The pathwise cumulative loss of one fixed action. -/
def cumulativeLoss {Action : Type*} {horizon : ℕ}
    (losses : LossSequence Action horizon) (action : Action) : ℝ :=
  ∑ round : Fin horizon, losses round action

/-- A deterministic reward function for each round of a finite online problem. -/
abbrev RewardSequence (Action : Type*) (horizon : ℕ) :=
  LossSequence Action horizon

/-- Convert a reward-maximization instance to its sign-equivalent loss instance. -/
def lossOfReward {Action : Type*} {horizon : ℕ}
    (rewards : RewardSequence Action horizon) : LossSequence Action horizon :=
  fun round action => -rewards round action

/-- Expected loss is nonnegative when every realized action loss is nonnegative. -/
theorem expectedLossAt_nonneg_of_nonneg {Action : Type*} [Fintype Action] [DecidableEq Action]
    {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon)
    (h_nonneg : ∀ round action, 0 ≤ losses round action) (round : Fin horizon) :
    0 ≤ expectedLossAt losses plays round := by
  unfold expectedLossAt
  exact pmfExp_nonneg_of_forall_nonneg (plays round) (losses round)
    (fun action => h_nonneg round action)

/-- Cumulative expected loss is nonnegative for a nonnegative loss sequence. -/
theorem cumulativeExpectedLoss_nonneg_of_nonneg
    {Action : Type*} [Fintype Action] [DecidableEq Action]
    {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon)
    (h_nonneg : ∀ round action, 0 ≤ losses round action) :
    0 ≤ cumulativeExpectedLoss losses plays := by
  unfold cumulativeExpectedLoss
  exact Finset.sum_nonneg fun round _ =>
    expectedLossAt_nonneg_of_nonneg losses plays h_nonneg round

/-- A fixed action has nonnegative cumulative loss for a nonnegative loss sequence. -/
theorem cumulativeLoss_nonneg_of_nonneg {Action : Type*} {horizon : ℕ}
    (losses : LossSequence Action horizon)
    (h_nonneg : ∀ round action, 0 ≤ losses round action) (action : Action) :
    0 ≤ cumulativeLoss losses action := by
  unfold cumulativeLoss
  exact Finset.sum_nonneg fun round _ => h_nonneg round action

/-- Reward-to-loss conversion negates each fixed action's cumulative objective. -/
theorem cumulativeLoss_lossOfReward_eq_neg {Action : Type*} {horizon : ℕ}
    (rewards : RewardSequence Action horizon) (action : Action) :
    cumulativeLoss (lossOfReward rewards) action = -cumulativeLoss rewards action := by
  unfold cumulativeLoss lossOfReward
  rw [Finset.sum_neg_distrib]

end Online
end Learning
end AppliedModelingLib
