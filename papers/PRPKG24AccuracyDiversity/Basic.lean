import AppliedModelingLib.Applications.RecommenderSystems.Allocation

open scoped BigOperators
open AppliedModelingLib

namespace PRPKG24AccuracyDiversity

/-- Item types in the recommendation-diversity model. -/
abbrev ItemType (T : ℕ) := Fin T

/-- A count allocation: how many recommended items are drawn from each type. -/
abbrev CountAllocation (T : ℕ) := AppliedModelingLib.Allocation (ItemType T)

/--
Generic finite abstraction of the paper's consumption-constrained objective.

`likelihood t` is the probability that the user prefers type `t`.
`valueOfCount t q` is the expected user value from recommending `q` items of type `t`,
conditional on the user preferring type `t`.

The paper's equation (3) has exactly this form:
`∑_t likelihood t * valueOfCount t (count t)`.
-/
structure ConsumptionModel (T : ℕ) where
  likelihood : ItemType T → ℝ
  valueOfCount : ItemType T → ℕ → ℝ

namespace ConsumptionModel

/-- The finite count-objective induced by a consumption model. -/
noncomputable def objective {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T) : ℝ := AppliedModelingLib.Allocation.objective a M.likelihood M.valueOfCount

/-- `a` is feasible for a slate/recommendation set of size `N`. -/
def FeasibleAtTotal {T : ℕ} (N : ℕ) (a : CountAllocation T) : Prop := AppliedModelingLib.Allocation.HasTotal a N

/-- `a` maximizes the consumption-constrained objective among allocations of size `N`. -/
def IsOptimalAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) (a : CountAllocation T) : Prop :=
  FeasibleAtTotal N a ∧
    ∀ b : CountAllocation T, FeasibleAtTotal N b → M.objective b ≤ M.objective a

/-- Marginal gain from adding one more item of type `t` after already recommending `q`. -/
noncomputable def marginalValue {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ := AppliedModelingLib.Allocation.marginal M.valueOfCount t q

/-- The model has nonnegative marginal values in every type. -/
def HasNonnegativeMarginals {T : ℕ} (M : ConsumptionModel T) : Prop := AppliedModelingLib.Allocation.HasNonnegativeMarginals M.valueOfCount

/-- The model has diminishing returns in every type. -/
def HasDiminishingReturns {T : ℕ} (M : ConsumptionModel T) : Prop := AppliedModelingLib.Allocation.HasDiminishingReturns M.valueOfCount

/-- Linear, no-consumption-constraint value: each additional item has the same value. -/
def linearValueOfCount {T : ℕ}
    (perItemValue : ItemType T → ℝ) : ItemType T → ℕ → ℝ :=
  fun t q => (q : ℝ) * perItemValue t

/-- The linearized objective used as the baseline that ignores consumption constraints. -/
def linearized {T : ℕ}
    (likelihood : ItemType T → ℝ) (perItemValue : ItemType T → ℝ) : ConsumptionModel T where
  likelihood := likelihood
  valueOfCount := linearValueOfCount perItemValue

@[simp] theorem objective_eq_allocation_objective {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T) :
    M.objective a = AppliedModelingLib.Allocation.objective a M.likelihood M.valueOfCount := rfl

@[simp] theorem marginalValue_apply {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) :
    M.marginalValue t q = M.valueOfCount t (q + 1) - M.valueOfCount t q := rfl

@[simp] theorem linearValueOfCount_zero {T : ℕ}
    (perItemValue : ItemType T → ℝ) (t : ItemType T) :
    linearValueOfCount perItemValue t 0 = 0 := by
  simp [linearValueOfCount]

end ConsumptionModel
end PRPKG24AccuracyDiversity
