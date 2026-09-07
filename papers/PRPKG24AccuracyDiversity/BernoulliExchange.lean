import PRPKG24AccuracyDiversity.Bernoulli
import PRPKG24AccuracyDiversity.Exchange

namespace PRPKG24AccuracyDiversity

namespace BernoulliSatisfactionModel

/-- Weighted forward marginal in the Bernoulli one-consumption model. -/
theorem weightedForwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) (q : ℕ) :
    (B.toConsumptionModel).weightedForwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ q := by
  unfold ConsumptionModel.weightedForwardMarginal ConsumptionModel.marginalValue
    AppliedModelingLib.Allocation.marginal toConsumptionModel
  rw [bernoulliAtLeastOneValue_succ_sub]
  ring

/-- Weighted backward marginal in the Bernoulli one-consumption model. -/
theorem weightedBackwardMarginal_toConsumptionModel {T : ℕ}
    (B : BernoulliSatisfactionModel T) (t : ItemType T) {q : ℕ}
    (hq : 0 < q) :
    (B.toConsumptionModel).weightedBackwardMarginal t q =
      B.likelihood t * B.successProb t * (1 - B.successProb t) ^ (q - 1) := by
  have hne : ¬ q = 0 := ne_of_gt hq
  unfold ConsumptionModel.weightedBackwardMarginal toConsumptionModel
  simp [hne]
  rw [bernoulliAtLeastOneValue_sub_pred (p := B.successProb t) hq]
  ring

/--
Paper-facing first-order condition for the finite Bernoulli specialization:
an optimal allocation has no exchange whose destination marginal exceeds the
source's last-item marginal.
-/
theorem forwardMarginal_le_backwardMarginal_of_optimum {T : ℕ}
    (B : BernoulliSatisfactionModel T) (N : ℕ)
    {a : CountAllocation T} {src dst : ItemType T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : AppliedModelingLib.Allocation.CanMoveOne a src) :
    B.likelihood dst * B.successProb dst *
        (1 - B.successProb dst) ^ (a.count dst) ≤
      B.likelihood src * B.successProb src *
        (1 - B.successProb src) ^ (a.count src - 1) := by
  have h :=
    ConsumptionModel.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (M := B.toConsumptionModel) (N := N) (a := a)
      (src := src) (dst := dst) hopt hne hcan
  rw [weightedForwardMarginal_toConsumptionModel
    (B := B) (t := dst) (q := a.count dst)] at h
  rw [weightedBackwardMarginal_toConsumptionModel
    (B := B) (t := src) (q := a.count src) hcan] at h
  exact h

/--
Finite i.i.d. Bernoulli balance condition.

If all item types have the same likelihood and success probability, every
finite optimum has pairwise counts differing by at most one.
-/
theorem pairwise_count_le_succ_of_symmetric_optimum {T : ℕ}
    (B : BernoulliSatisfactionModel T) (N : ℕ) {a : CountAllocation T}
    (hopt : B.toConsumptionModel.IsOptimalAtTotal N a)
    (hlike : ∀ i j : ItemType T, B.likelihood i = B.likelihood j)
    (hprob : ∀ i j : ItemType T, B.successProb i = B.successProb j)
    (hlike_pos : ∀ i : ItemType T, 0 < B.likelihood i)
    (hprob_pos : ∀ i : ItemType T, 0 < B.successProb i)
    (hprob_lt_one : ∀ i : ItemType T, B.successProb i < 1) :
    ∀ src dst : ItemType T, a.count src ≤ a.count dst + 1 := by
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        B.likelihood B.toConsumptionModel.valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal, ConsumptionModel.IsOptimalAtTotal,
      ConsumptionModel.FeasibleAtTotal, ConsumptionModel.objective, toConsumptionModel] using hopt
  refine
    AppliedModelingLib.Allocation.count_le_succ_of_cross_strict_antitone_forwardMarginal
      (a := a) (weight := B.likelihood)
      (valueOfCount := B.toConsumptionModel.valueOfCount) (N := N) hopt' ?_
  intro src dst q r hqr
  have hcoef_pos : 0 < B.likelihood dst * B.successProb dst :=
    mul_pos (hlike_pos dst) (hprob_pos dst)
  have hbase_pos : 0 < 1 - B.successProb dst := by
    linarith [hprob_lt_one dst]
  have hbase_lt_one : 1 - B.successProb dst < 1 := by
    linarith [hprob_pos dst]
  have hpow_lt :
      (1 - B.successProb dst) ^ r < (1 - B.successProb dst) ^ q :=
    pow_lt_pow_right_of_lt_one₀ hbase_pos hbase_lt_one hqr
  calc
    AppliedModelingLib.Allocation.weightedForwardMarginal
        B.likelihood B.toConsumptionModel.valueOfCount src r
        = B.likelihood src * B.successProb src *
            (1 - B.successProb src) ^ r := by
          unfold AppliedModelingLib.Allocation.weightedForwardMarginal
            AppliedModelingLib.Allocation.marginal toConsumptionModel
          rw [bernoulliAtLeastOneValue_succ_sub]
          ring
    _ = B.likelihood dst * B.successProb dst * (1 - B.successProb dst) ^ r := by
          simp [hlike src dst, hprob src dst]
    _ < B.likelihood dst * B.successProb dst * (1 - B.successProb dst) ^ q :=
          mul_lt_mul_of_pos_left hpow_lt hcoef_pos
    _ = AppliedModelingLib.Allocation.weightedForwardMarginal
        B.likelihood B.toConsumptionModel.valueOfCount dst q := by
          unfold AppliedModelingLib.Allocation.weightedForwardMarginal
            AppliedModelingLib.Allocation.marginal toConsumptionModel
          rw [bernoulliAtLeastOneValue_succ_sub]
          ring

end BernoulliSatisfactionModel
end PRPKG24AccuracyDiversity
