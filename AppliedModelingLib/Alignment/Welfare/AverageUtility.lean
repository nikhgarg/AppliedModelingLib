import AppliedModelingLib.Alignment.Welfare.Population

/-!
# Average utility and welfare of finite policies

## Main declarations

- `populationAverageUtility`
- `policyAverageUtility`
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

/-- The utilitarian average utility of one alternative over a user population. -/
noncomputable def populationAverageUtility
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (alternative : Alternative) : ℝ :=
  pmfExp population (fun user => utility user alternative)

/-- The average utility of a randomized alternative policy. -/
noncomputable def policyAverageUtility
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (policy : PMF Alternative) : ℝ :=
  pmfExp policy (populationAverageUtility population utility)

/-- Unit-interval user utilities have nonnegative population average utility. -/
theorem populationAverageUtility_nonneg
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility) (alternative : Alternative) :
    0 ≤ populationAverageUtility population utility alternative := by
  unfold populationAverageUtility
  exact pmfExp_nonneg_of_forall_nonneg population _ fun user =>
    (hutility user alternative).1

/-- Unit-interval user utilities have population average utility at most one. -/
theorem populationAverageUtility_le_one
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (hutility : UnitIntervalUtilityProfile utility) (alternative : Alternative) :
    populationAverageUtility population utility alternative ≤ 1 := by
  unfold populationAverageUtility
  exact pmfExp_le_of_forall_le population _ 1 fun user =>
    (hutility user alternative).2

/-- A policy's average utility is nonnegative for unit-interval user utilities. -/
theorem policyAverageUtility_nonneg
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (policy : PMF Alternative) (hutility : UnitIntervalUtilityProfile utility) :
    0 ≤ policyAverageUtility population utility policy := by
  unfold policyAverageUtility
  exact pmfExp_nonneg_of_forall_nonneg policy _ fun alternative =>
    populationAverageUtility_nonneg population utility hutility alternative

/-- A policy's average utility is at most one for unit-interval user utilities. -/
theorem policyAverageUtility_le_one
    {User Alternative : Type*} [Fintype User] [DecidableEq User]
    [Fintype Alternative] [DecidableEq Alternative]
    (population : PMF User) (utility : FiniteUtilityProfile User Alternative)
    (policy : PMF Alternative) (hutility : UnitIntervalUtilityProfile utility) :
    policyAverageUtility population utility policy ≤ 1 := by
  unfold policyAverageUtility
  exact pmfExp_le_of_forall_le policy _ 1 fun alternative =>
    populationAverageUtility_le_one population utility hutility alternative

end Welfare
end Alignment
end AppliedModelingLib
