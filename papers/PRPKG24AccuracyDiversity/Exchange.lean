import PRPKG24AccuracyDiversity.Optimization
import AppliedModelingLib.Foundations.Math.FiniteRounding

namespace PRPKG24AccuracyDiversity

namespace ConsumptionModel

/-- Move one recommendation from type `src` to type `dst`. -/
def moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) : CountAllocation T := AppliedModelingLib.Allocation.moveOne a src dst

/-- Weighted forward marginal gain from adding one more item of type `t`. -/
noncomputable def weightedForwardMarginal {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ := M.likelihood t * M.marginalValue t q

/--
Weighted value lost by removing the `q`-th item of type `t`.
The value is set to `0` at `q = 0`; exchange lemmas should also assume `0 < q`.
-/
noncomputable def weightedBackwardMarginal {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else M.likelihood t * (M.valueOfCount t q - M.valueOfCount t (q - 1))

/-- The one-step exchange condition used in finite allocation optimality arguments. -/
def ExchangeCondition {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T) (src dst : ItemType T) : Prop :=
  weightedBackwardMarginal M src (a.count src) ≤ weightedForwardMarginal M dst (a.count dst)

/--
Target proposition for the finite exchange lemma:
if moving one count from `src` to `dst` loses no more than it gains, the objective weakly improves.
-/
def ExchangeImprovementTarget {T : ℕ} (M : ConsumptionModel T) : Prop :=
  ∀ a src dst,
    src ≠ dst →
    AppliedModelingLib.Allocation.CanMoveOne a src →
    ExchangeCondition M a src dst →
    M.objective a ≤ M.objective (moveOne a src dst)

/--
Target proposition for local optimality:
if `a` is optimal at total size `N`, every valid one-step exchange has nonpositive gain.
-/
def NoProfitableExchangeAtOptimumTarget {T : ℕ} (M : ConsumptionModel T) (N : ℕ) : Prop :=
  ∀ a src dst,
    M.IsOptimalAtTotal N a →
    src ≠ dst →
    AppliedModelingLib.Allocation.CanMoveOne a src →
    M.objective (moveOne a src dst) ≤ M.objective a

@[simp] theorem moveOne_eq_allocation_moveOne {T : ℕ}
    (a : CountAllocation T) (src dst : ItemType T) :
    moveOne a src dst = AppliedModelingLib.Allocation.moveOne a src dst := rfl

@[simp] theorem weightedForwardMarginal_apply {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) :
    weightedForwardMarginal M t q = M.likelihood t * M.marginalValue t q := rfl

/-- Moving one item from a positive source to a distinct destination preserves total size. -/
theorem total_moveOne_eq {T : ℕ} (a : CountAllocation T)
    {src dst : ItemType T} (hne : src ≠ dst)
    (hcan : AppliedModelingLib.Allocation.CanMoveOne a src) :
    AppliedModelingLib.Allocation.total (moveOne a src dst) =
      AppliedModelingLib.Allocation.total a := by
  simpa [moveOne] using
    AppliedModelingLib.Allocation.total_moveOne_eq
      (a := a) (src := src) (dst := dst) hne hcan

/--
Exact objective accounting for one valid exchange: the destination gains its
forward marginal and the source loses its backward marginal.
-/
theorem objective_moveOne_eq {T : ℕ} (M : ConsumptionModel T) (a : CountAllocation T)
    {src dst : ItemType T} (hne : src ≠ dst)
    (hcan : AppliedModelingLib.Allocation.CanMoveOne a src) :
    M.objective (moveOne a src dst) =
      M.objective a - M.weightedBackwardMarginal src (a.count src) +
        M.weightedForwardMarginal dst (a.count dst) := by
  simpa [objective, moveOne, weightedBackwardMarginal, weightedForwardMarginal,
    marginalValue, AppliedModelingLib.Allocation.weightedBackwardMarginal,
    AppliedModelingLib.Allocation.weightedForwardMarginal, AppliedModelingLib.Allocation.marginal] using
      AppliedModelingLib.Allocation.objective_moveOne_eq
        (a := a) (weight := M.likelihood) (valueOfCount := M.valueOfCount)
        (src := src) (dst := dst) hne hcan

/-- The finite exchange-improvement target is closed by exact marginal accounting. -/
theorem exchangeImprovementTarget {T : ℕ} (M : ConsumptionModel T) :
    ExchangeImprovementTarget M := by
  intro a src dst hne hcan hcond
  have hcond' :
      AppliedModelingLib.Allocation.ExchangeCondition
        M.likelihood M.valueOfCount a src dst := by
    simpa [ExchangeCondition, weightedBackwardMarginal, weightedForwardMarginal,
      marginalValue, AppliedModelingLib.Allocation.ExchangeCondition,
      AppliedModelingLib.Allocation.weightedBackwardMarginal,
      AppliedModelingLib.Allocation.weightedForwardMarginal,
      AppliedModelingLib.Allocation.marginal] using hcond
  simpa [objective, moveOne] using
    AppliedModelingLib.Allocation.objective_le_objective_moveOne_of_exchangeCondition
      (a := a) (weight := M.likelihood) (valueOfCount := M.valueOfCount)
      (src := src) (dst := dst) hne hcan hcond'

/--
At any finite optimum, moving one item from a positive source to a distinct
destination cannot strictly improve the objective.
-/
theorem noProfitableExchangeAtOptimumTarget {T : ℕ} (M : ConsumptionModel T) (N : ℕ) :
    NoProfitableExchangeAtOptimumTarget M N := by
  intro a src dst hopt hne hcan
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        M.likelihood M.valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal, IsOptimalAtTotal,
      FeasibleAtTotal, objective] using hopt
  simpa [objective, moveOne] using
    AppliedModelingLib.Allocation.objective_moveOne_le_of_isOptimalAtTotal
      (a := a) (weight := M.likelihood) (valueOfCount := M.valueOfCount)
      (N := N) hopt' hne hcan

/--
First-order finite optimality condition: at an optimum, the weighted marginal
gain from adding to `dst` cannot exceed the weighted marginal loss from `src`.
-/
theorem weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) {a : CountAllocation T}
    {src dst : ItemType T}
    (hopt : M.IsOptimalAtTotal N a) (hne : src ≠ dst)
    (hcan : AppliedModelingLib.Allocation.CanMoveOne a src) :
    weightedForwardMarginal M dst (a.count dst) ≤
      weightedBackwardMarginal M src (a.count src) := by
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        M.likelihood M.valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal, IsOptimalAtTotal,
      FeasibleAtTotal, objective] using hopt
  simpa [weightedBackwardMarginal, weightedForwardMarginal, marginalValue,
    AppliedModelingLib.Allocation.weightedBackwardMarginal,
    AppliedModelingLib.Allocation.weightedForwardMarginal,
    AppliedModelingLib.Allocation.marginal] using
      AppliedModelingLib.Allocation.weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
        (a := a) (weight := M.likelihood) (valueOfCount := M.valueOfCount)
        (N := N) (src := src) (dst := dst) hopt' hne hcan

theorem marginalValue_antitone_of_diminishing {T : ℕ}
    (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (t : ItemType T) {q r : ℕ} (hqr : q ≤ r) :
    M.marginalValue t r ≤ M.marginalValue t q := by
  simpa [marginalValue, HasDiminishingReturns] using
    AppliedModelingLib.Allocation.marginal_antitone_of_diminishing
      (valueOfCount := M.valueOfCount) hDR t hqr

theorem weightedForwardMarginal_antitone_of_diminishing {T : ℕ}
    (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (t : ItemType T) {q r : ℕ} (hqr : q ≤ r) :
    M.weightedForwardMarginal t r ≤ M.weightedForwardMarginal t q := by
  simpa [weightedForwardMarginal, marginalValue, HasDiminishingReturns,
    AppliedModelingLib.Allocation.weightedForwardMarginal,
    AppliedModelingLib.Allocation.marginal] using
      AppliedModelingLib.Allocation.weightedForwardMarginal_antitone_of_diminishing
        (weight := M.likelihood) (valueOfCount := M.valueOfCount)
        hDR hlike_nonneg t hqr

theorem weightedBackwardMarginal_eq_weightedForwardMarginal_pred {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) {q : ℕ} (hq : 0 < q) :
    M.weightedBackwardMarginal t q = M.weightedForwardMarginal t (q - 1) := by
  simpa [weightedBackwardMarginal, weightedForwardMarginal, marginalValue,
    AppliedModelingLib.Allocation.weightedBackwardMarginal,
    AppliedModelingLib.Allocation.weightedForwardMarginal,
    AppliedModelingLib.Allocation.marginal] using
      AppliedModelingLib.Allocation.weightedBackwardMarginal_eq_weightedForwardMarginal_pred
        (weight := M.likelihood) (valueOfCount := M.valueOfCount) t hq

theorem weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
    {T : ℕ} (M : ConsumptionModel T) (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (t : ItemType T) {q r : ℕ} (hrq : r + 1 ≤ q) :
    M.weightedBackwardMarginal t q ≤ M.weightedForwardMarginal t r := by
  simpa [weightedBackwardMarginal, weightedForwardMarginal, marginalValue,
    HasDiminishingReturns, AppliedModelingLib.Allocation.weightedBackwardMarginal,
    AppliedModelingLib.Allocation.weightedForwardMarginal,
    AppliedModelingLib.Allocation.marginal] using
      AppliedModelingLib.Allocation.weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
        (weight := M.likelihood) (valueOfCount := M.valueOfCount)
        hDR hlike_nonneg t hrq

def StrictRoundingExchangeCertificateBetween {T : ℕ}
    (M : ConsumptionModel T)
    (lower upper : CountAllocation T) : Prop :=
  ∀ high low,
    0 < lower.count low →
      M.weightedForwardMarginal high (upper.count high) <
        M.weightedBackwardMarginal low (lower.count low)

theorem noRoundingCrossingBetween_of_strictExchangeCertificate {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ)
    {a lower upper : CountAllocation T}
    (hopt : M.IsOptimalAtTotal N a)
    (hDR : M.HasDiminishingReturns)
    (hlike_nonneg : ∀ t, 0 ≤ M.likelihood t)
    (horder : ∀ t, lower.count t ≤ upper.count t)
    (hcert : M.StrictRoundingExchangeCertificateBetween lower upper) :
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
      (fun t : ItemType T => a.count t)
      (fun t : ItemType T => lower.count t)
      (fun t : ItemType T => upper.count t) := by
  have hopt' :
      AppliedModelingLib.Allocation.IsOptimalAtTotal
        M.likelihood M.valueOfCount N a := by
    simpa [AppliedModelingLib.Allocation.IsOptimalAtTotal, IsOptimalAtTotal,
      FeasibleAtTotal, objective] using hopt
  have hcert' :
      AppliedModelingLib.Allocation.StrictRoundingExchangeCertificateBetween
        M.likelihood M.valueOfCount lower upper := by
    intro high low hlow
    simpa [StrictRoundingExchangeCertificateBetween, weightedForwardMarginal,
      weightedBackwardMarginal, marginalValue,
      AppliedModelingLib.Allocation.StrictRoundingExchangeCertificateBetween,
      AppliedModelingLib.Allocation.weightedForwardMarginal,
      AppliedModelingLib.Allocation.weightedBackwardMarginal,
      AppliedModelingLib.Allocation.marginal] using hcert high low hlow
  exact
    AppliedModelingLib.Allocation.noRoundingCrossingBetween_of_strictExchangeCertificate
      (a := a) (lower := lower) (upper := upper)
      (weight := M.likelihood) (valueOfCount := M.valueOfCount)
      (N := N) hopt' hDR hlike_nonneg horder hcert'

end ConsumptionModel
end PRPKG24AccuracyDiversity
