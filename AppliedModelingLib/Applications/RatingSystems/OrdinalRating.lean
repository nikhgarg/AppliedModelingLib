import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/--
Posterior mean of the Dirichlet-Categorical model for ordinal ratings.

Given a finite set of ordinal rating categories `K` (e.g., `{1, 2, 3, 4, 5}`),
a function assigning a real value `rating` to each category,
prior pseudo-count parameters `alpha : K → ℝ`, and observed counts `N : K → ℝ`,
the estimated quality is the expected posterior mean.
-/
noncomputable def dirichletCategoricalPosteriorMean
    {K : Type} [Fintype K]
    (rating : K → ℝ)
    (alpha : K → ℝ)
    (N : K → ℝ) : ℝ :=
  (∑ j : K, (alpha j + N j) * rating j) / (∑ j : K, (alpha j + N j))

/--
For ordinal ratings with a finite domain, if the total prior plus observed count
is non-zero, the posterior mean is correctly normalized.
-/
theorem dirichletCategoricalPosteriorMean_eq_weighted_sum
    {K : Type} [Fintype K]
    (rating : K → ℝ)
    (alpha : K → ℝ)
    (N : K → ℝ)
    (h_pos : ∑ j : K, (alpha j + N j) ≠ 0) :
    dirichletCategoricalPosteriorMean rating alpha N =
      ∑ j : K, ((alpha j + N j) / (∑ j : K, (alpha j + N j))) * rating j := by
  unfold dirichletCategoricalPosteriorMean
  have h_div : (∑ j : K, (alpha j + N j) * rating j) / (∑ j : K, (alpha j + N j)) =
    (∑ j : K, (alpha j + N j) * rating j) * (∑ j : K, (alpha j + N j))⁻¹ := by
    exact div_eq_mul_inv _ _
  rw [h_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  have h_div2 : ((alpha x + N x) / ∑ j : K, (alpha j + N j)) * rating x =
    (alpha x + N x) * (∑ j : K, (alpha j + N j))⁻¹ * rating x := by
    exact congrArg (fun a => a * rating x) (div_eq_mul_inv _ _)
  rw [h_div2]
  ring

end Statistics
end AppliedModelingLib
