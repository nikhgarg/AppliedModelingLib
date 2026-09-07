import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

/-!
# Expectations under a finite uniform PMF

The empirical laws used by finite-sample algorithms are often a pushforward of
`PMF.uniformOfFinset`.  This file records its scalar expectation as the
literal finite sample average.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- A finite-PMF expectation under `uniformOfFinset` is the arithmetic mean
over the selected finite set. -/
theorem pmfExp_uniformOfFinset_eq_sum_div_card
    {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    pmfExp (PMF.uniformOfFinset s hs) f =
      (∑ a ∈ s, f a) / (s.card : ℝ) := by
  classical
  have hmass : ((s.card : ENNReal)⁻¹).toReal = (s.card : ℝ)⁻¹ := by
    rw [ENNReal.toReal_inv]
    norm_cast
  unfold pmfExp
  calc
    ∑ a : α, ((PMF.uniformOfFinset s hs a).toReal) * f a =
        ∑ a : α, if a ∈ s then ((s.card : ENNReal)⁻¹).toReal * f a else 0 := by
          apply Finset.sum_congr rfl
          intro a _
          simp only [PMF.uniformOfFinset_apply]
          split_ifs
          · rfl
          · simp
    _ = ∑ a ∈ s, ((s.card : ENNReal)⁻¹).toReal * f a := by
          simpa using
            (Finset.sum_filter (s := (Finset.univ : Finset α)) (p := fun a => a ∈ s)
              (f := fun a => ((s.card : ENNReal)⁻¹).toReal * f a)).symm
    _ = (∑ a ∈ s, f a) / (s.card : ℝ) := by
          rw [hmass, ← Finset.mul_sum]
          ring

end AppliedModelingLib
