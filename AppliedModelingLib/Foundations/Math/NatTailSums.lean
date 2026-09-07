import Mathlib.Tactic

/-!
# Tails of summable natural-indexed series

Small reindexing lemmas for series over a natural-number tail.
-/

namespace AppliedModelingLib

open Filter Topology
/-- A convergent offset-indexed nonnegative series is the sum of the same
series restricted to the corresponding natural-number upper tail. -/
theorem hasSum_nat_Ici_indicator_of_hasSum_shift
    {f : ℕ → ℝ} {offset : ℕ} {total : ℝ}
    (hshift : HasSum (fun n : ℕ => f (n + offset)) total) :
    HasSum (fun n : ℕ => if offset ≤ n then f n else 0) total := by
  let tailIndicator : ℕ → ℝ := fun n => if offset ≤ n then f n else 0
  have hshiftIndicator : HasSum (fun n : ℕ => tailIndicator (n + offset)) total := by
    refine hshift.congr_fun ?_
    intro n
    simp [tailIndicator]
  have hprefix : ∑ state ∈ Finset.range offset, tailIndicator state = 0 := by
    apply Finset.sum_eq_zero
    intro state hstate
    simp [tailIndicator, not_le_of_gt (Finset.mem_range.mp hstate)]
  have hsum := (hasSum_nat_add_iff offset).mp hshiftIndicator
  rw [hprefix, add_zero] at hsum
  exact hsum

end AppliedModelingLib
