import Mathlib.Data.Finset.Max
import AppliedModelingLib.Learning.Online.Basic

/-!
# External regret for finite online learning

This module defines pathwise external regret against the best fixed action.
It is deliberately independent of any stochastic model for the losses or the
learner: probability enters only through the learner's distribution-valued
action in each realized round.

## Main declarations

- `bestFixedActionLoss`
- `externalRegret`
- `bestFixedActionLoss_le`
-/

namespace AppliedModelingLib
namespace Learning
namespace Online

/-- The smallest cumulative loss attained by a fixed action over the horizon. -/
noncomputable def bestFixedActionLoss {Action : Type*} [Fintype Action] [Nonempty Action]
    {horizon : ℕ} (losses : LossSequence Action horizon) : ℝ :=
  (Finset.univ : Finset Action).inf' Finset.univ_nonempty (cumulativeLoss losses)

/-- Pathwise external regret: learner loss minus the best fixed action's loss. -/
noncomputable def externalRegret {Action : Type*} [Fintype Action] [DecidableEq Action]
    [Nonempty Action] {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon) : ℝ :=
  cumulativeExpectedLoss losses plays - bestFixedActionLoss losses

/-- The best fixed action loss is at most every named fixed action's loss. -/
theorem bestFixedActionLoss_le {Action : Type*} [Fintype Action] [Nonempty Action]
    {horizon : ℕ} (losses : LossSequence Action horizon) (action : Action) :
    bestFixedActionLoss losses ≤ cumulativeLoss losses action := by
  unfold bestFixedActionLoss
  exact Finset.inf'_le _ (Finset.mem_univ action)

/-- External regret unfolds to its learner-minus-comparator interpretation. -/
theorem externalRegret_eq_cumulativeExpectedLoss_sub_bestFixedActionLoss
    {Action : Type*} [Fintype Action] [DecidableEq Action] [Nonempty Action]
    {horizon : ℕ} (losses : LossSequence Action horizon)
    (plays : PlaySequence Action horizon) :
    externalRegret losses plays =
      cumulativeExpectedLoss losses plays - bestFixedActionLoss losses := rfl

end Online
end Learning
end AppliedModelingLib
