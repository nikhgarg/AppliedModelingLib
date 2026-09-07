import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace AppliedModelingLib
namespace Statistics

open scoped BigOperators

/-- Mean of a real-valued function over a finite set. -/
noncomputable def finsetMean {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  if s.card = 0 then 0 else (∑ a ∈ s, f a) / (s.card : ℝ)

/-- Variance of a real-valued function over a finite set. -/
noncomputable def finsetVariance {α : Type*} (s : Finset α) (f : α → ℝ) : ℝ :=
  if s.card = 0 then 0 else
    let mu := finsetMean s f
    (∑ a ∈ s, (f a - mu) ^ 2) / (s.card : ℝ)

end Statistics
end AppliedModelingLib
