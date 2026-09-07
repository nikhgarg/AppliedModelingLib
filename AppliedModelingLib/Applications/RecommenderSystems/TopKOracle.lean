import AppliedModelingLib.Applications.RecommenderSystems.Allocation
import AppliedModelingLib.Foundations.Probability.OrderStatistics

namespace AppliedModelingLib
namespace Probability
namespace TopKExpectationOracle

/-!
# Top-k Oracles for Count Allocations

This module connects the probability-side `TopKExpectationOracle` abstraction to
finite recommendation count allocations.  It is intentionally generic in the
item/type index, so domain-specific models can keep their own names while using
the same allocation objective and marginal bridges.
-/

variable {τ : Type*}

/-- Value-of-count function induced by fixing a top-`k` expectation oracle. -/
def allocationValueOfCount (O : TopKExpectationOracle τ) (k : ℕ) :
    τ → ℕ → ℝ :=
  fun t q => O.expectedTopSum k t q

/-- Allocation objective induced by a fixed top-`k` expectation oracle. -/
noncomputable def allocationObjective [Fintype τ]
    (O : TopKExpectationOracle τ) (objectiveWeight : τ → ℝ)
    (k : ℕ) (a : Allocation τ) : ℝ :=
  Allocation.objective a objectiveWeight (O.allocationValueOfCount k)

@[simp] theorem allocationValueOfCount_apply
    (O : TopKExpectationOracle τ) (k : ℕ) (t : τ) (q : ℕ) :
    O.allocationValueOfCount k t q = O.expectedTopSum k t q := rfl

@[simp] theorem allocationObjective_apply [Fintype τ]
    (O : TopKExpectationOracle τ) (objectiveWeight : τ → ℝ)
    (k : ℕ) (a : Allocation τ) :
    O.allocationObjective objectiveWeight k a =
      Allocation.objective a objectiveWeight
        (fun t q => O.expectedTopSum k t q) := rfl

@[simp] theorem marginal_allocationValueOfCount
    (O : TopKExpectationOracle τ) (k : ℕ) (t : τ) (q : ℕ) :
    Allocation.marginal (O.allocationValueOfCount k) t q =
      O.marginalTopK k t q := rfl

/--
Nonnegative top-`k` oracle marginals imply nonnegative allocation marginals for
the induced value-of-count function.
-/
theorem allocationValueOfCount_has_nonnegative_marginals
    (O : TopKExpectationOracle τ) (k : ℕ)
    (h : O.HasNonnegativeMarginalsAt k) :
    Allocation.HasNonnegativeMarginals (O.allocationValueOfCount k) := by
  intro t q
  exact h t q

/--
Diminishing top-`k` oracle marginals imply diminishing allocation returns for
the induced value-of-count function.
-/
theorem allocationValueOfCount_has_diminishing_returns
    (O : TopKExpectationOracle τ) (k : ℕ)
    (h : O.HasDiminishingReturnsAt k) :
    Allocation.HasDiminishingReturns (O.allocationValueOfCount k) := by
  intro t q
  exact h t q

end TopKExpectationOracle
end Probability
end AppliedModelingLib
