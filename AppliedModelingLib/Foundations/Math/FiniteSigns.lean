import AppliedModelingLib.Foundations.Probability.FiniteExpectation

open scoped BigOperators

namespace AppliedModelingLib

/-- A finite sum of nonnegative real terms is nonnegative. -/
theorem sum_univ_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (hf : ∀ a : α, 0 ≤ f a) :
    0 ≤ ∑ a : α, f a := by
  classical
  exact Finset.sum_nonneg (by intro a _; exact hf a)

/--
If one term in a finite sum is strictly positive and all terms are nonnegative,
then the whole sum is strictly positive.
-/
theorem sum_univ_pos_of_pos_of_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) (a₀ : α)
    (hpos : 0 < f a₀) (hnonneg : ∀ a : α, 0 ≤ f a) :
    0 < ∑ a : α, f a := by
  classical
  have hle : f a₀ ≤ ∑ a : α, f a := by
    exact Finset.single_le_sum (fun a _ => hnonneg a) (by simp)
  exact lt_of_lt_of_le hpos hle

end AppliedModelingLib
