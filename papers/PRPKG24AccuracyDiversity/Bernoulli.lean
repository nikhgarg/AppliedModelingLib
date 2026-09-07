import PRPKG24AccuracyDiversity.Basic
import AppliedModelingLib.Foundations.Probability.Bernoulli

open scoped BigOperators

namespace PRPKG24AccuracyDiversity

/--
Expected satisfaction from `q` independent Bernoulli items when the user consumes one item:
`1 - (1 - p)^q`.
-/
noncomputable def bernoulliAtLeastOneValue (p : ℝ) (q : ℕ) : ℝ :=
  1 - (1 - p) ^ q

@[simp] theorem bernoulliAtLeastOneValue_zero (p : ℝ) :
    bernoulliAtLeastOneValue p 0 = 0 := by
  simp [bernoulliAtLeastOneValue]

theorem bernoulliAtLeastOneValue_one (p : ℝ) :
    bernoulliAtLeastOneValue p 1 = p := by
  simp [bernoulliAtLeastOneValue]

/-- Closed form for the one-step Bernoulli satisfaction marginal. -/
theorem bernoulliAtLeastOneValue_succ_sub (p : ℝ) (q : ℕ) :
    bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q =
      p * (1 - p) ^ q := by
  simpa [bernoulliAtLeastOneValue,
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue] using
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue_succ_sub p q

/-- Closed form for the value lost by removing the last Bernoulli recommendation. -/
theorem bernoulliAtLeastOneValue_sub_pred {p : ℝ} {q : ℕ} (hq : 0 < q) :
    bernoulliAtLeastOneValue p q - bernoulliAtLeastOneValue p (q - 1) =
      p * (1 - p) ^ (q - 1) := by
  simpa [bernoulliAtLeastOneValue,
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue] using
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue_sub_pred (p := p) hq

/-- Bernoulli satisfaction has nonnegative marginal values for `0 ≤ p ≤ 1`. -/
theorem bernoulliAtLeastOneValue_succ_sub_nonneg {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    0 ≤ bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q := by
  simpa [bernoulliAtLeastOneValue,
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue] using
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue_succ_sub_nonneg hp0 hp1 q

/-- Bernoulli satisfaction has diminishing one-step marginal values for `0 ≤ p ≤ 1`. -/
theorem bernoulliAtLeastOneValue_diminishing_marginal {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℕ) :
    bernoulliAtLeastOneValue p (q + 2) - bernoulliAtLeastOneValue p (q + 1) ≤
      bernoulliAtLeastOneValue p (q + 1) - bernoulliAtLeastOneValue p q := by
  simpa [bernoulliAtLeastOneValue,
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue] using
    AppliedModelingLib.Probability.Bernoulli.atLeastOneValue_diminishing_marginal hp0 hp1 q

/-- Bernoulli-satisfaction specialization used by the paper's heterogeneous Bernoulli results. -/
structure BernoulliSatisfactionModel (T : ℕ) where
  likelihood : ItemType T → ℝ
  successProb : ItemType T → ℝ

namespace BernoulliSatisfactionModel

/-- Type likelihoods form a probability vector. -/
def LikelihoodsSumToOne {T : ℕ} (B : BernoulliSatisfactionModel T) : Prop := ∑ t, B.likelihood t = 1

/-- All success probabilities lie in `[0,1]`. -/
def SuccessProbabilitiesValid {T : ℕ} (B : BernoulliSatisfactionModel T) : Prop := ∀ t, 0 ≤ B.successProb t ∧ B.successProb t ≤ 1

/-- Convert the Bernoulli satisfaction model into the generic consumption model. -/
noncomputable def toConsumptionModel {T : ℕ} (B : BernoulliSatisfactionModel T) : ConsumptionModel T where
  likelihood := B.likelihood
  valueOfCount := fun t q => bernoulliAtLeastOneValue (B.successProb t) q

/-- Objective for the Bernoulli satisfaction model. -/
noncomputable def objective {T : ℕ}
    (B : BernoulliSatisfactionModel T) (a : CountAllocation T) : ℝ := B.toConsumptionModel.objective a

@[simp] theorem objective_eq_consumption_objective {T : ℕ}
    (B : BernoulliSatisfactionModel T) (a : CountAllocation T) :
    B.objective a = B.toConsumptionModel.objective a := rfl

@[simp] theorem valueOfCount_zero {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) :
    B.toConsumptionModel.valueOfCount t 0 = 0 := by
  simp [toConsumptionModel, bernoulliAtLeastOneValue]

/-- The Bernoulli specialization has nonnegative marginal values when probabilities are valid. -/
theorem toConsumptionModel_has_nonnegative_marginals {T : ℕ}
    (B : BernoulliSatisfactionModel T) (hvalid : B.SuccessProbabilitiesValid) :
    B.toConsumptionModel.HasNonnegativeMarginals := by
  intro t q
  simpa [ConsumptionModel.HasNonnegativeMarginals, AppliedModelingLib.Allocation.HasNonnegativeMarginals,
    AppliedModelingLib.Allocation.marginal, toConsumptionModel] using
      bernoulliAtLeastOneValue_succ_sub_nonneg (hvalid t).1 (hvalid t).2 q

/-- The Bernoulli specialization has diminishing marginal returns when probabilities are valid. -/
theorem toConsumptionModel_has_diminishing_returns {T : ℕ}
    (B : BernoulliSatisfactionModel T) (hvalid : B.SuccessProbabilitiesValid) :
    B.toConsumptionModel.HasDiminishingReturns := by
  intro t q
  simpa [ConsumptionModel.HasDiminishingReturns, AppliedModelingLib.Allocation.HasDiminishingReturns,
    AppliedModelingLib.Allocation.marginal, toConsumptionModel] using
      bernoulliAtLeastOneValue_diminishing_marginal (hvalid t).1 (hvalid t).2 q

end BernoulliSatisfactionModel
end PRPKG24AccuracyDiversity
