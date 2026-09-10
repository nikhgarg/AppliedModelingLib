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

/-- Zero-likelihood coordinates do not affect the consumption objective.

This is the supportwise bridge needed when a source population law permits
types of zero probability: two allocations may differ arbitrarily off the
positive-likelihood support while having identical objective value whenever
their counts agree on every nonzero-weight type. -/
theorem objective_eq_of_agree_on_likelihood_support
    {T : ℕ} (M : ConsumptionModel T)
    (a b : CountAllocation T)
    (hcounts : ∀ t, M.likelihood t ≠ 0 → a.count t = b.count t) :
    M.objective a = M.objective b := by
  classical
  unfold objective AppliedModelingLib.Allocation.objective
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases ht : M.likelihood t = 0
  · simp [ht]
  · rw [hcounts t ht]

/-
If one feasible optimizer is modified only on zero-likelihood coordinates,
the modified allocation is an optimizer as well.  This is the optimizer-level
supportwise consequence used when assessing the paper's zero-support case.
It deliberately does not choose a canonical off-support tie-break.
-/
theorem isOptimalAtTotal_of_agree_on_likelihood_support
    {T : ℕ} (M : ConsumptionModel T) (N : ℕ)
    {a b : CountAllocation T}
    (hopt : M.IsOptimalAtTotal N a)
    (hb : FeasibleAtTotal N b)
    (hcounts : ∀ t, M.likelihood t ≠ 0 → a.count t = b.count t) :
    M.IsOptimalAtTotal N b := by
  rcases hopt with ⟨ha, hmax⟩
  have hobj : M.objective a = M.objective b :=
    objective_eq_of_agree_on_likelihood_support M a b hcounts
  refine ⟨hb, ?_⟩
  intro c hc
  calc
    M.objective c ≤ M.objective a := hmax c hc
    _ = M.objective b := hobj

@[simp] theorem marginalValue_apply {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) :
    M.marginalValue t q = M.valueOfCount t (q + 1) - M.valueOfCount t q := rfl

@[simp] theorem linearValueOfCount_zero {T : ℕ}
    (perItemValue : ItemType T → ℝ) (t : ItemType T) :
    linearValueOfCount perItemValue t 0 = 0 := by
  simp [linearValueOfCount]

end ConsumptionModel
end PRPKG24AccuracyDiversity
