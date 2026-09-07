import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic

open scoped BigOperators

/-!
# Finite concavity inequalities

Elementary real-line consequences of concavity used by finite optimization and
likelihood arguments.

## Main declarations

- `concave_increment_diminishes`
- `finset_sum_increment_diminishes`
-/

namespace AppliedModelingLib

/--
For a concave real function, a nonnegative shift can only weakly decrease the
gain from a second nonnegative shift. Equivalently, the two endpoints of the
resulting rectangle satisfy the displayed four-point inequality.
-/
theorem concave_increment_diminishes
    (f : ℝ → ℝ) (hconcave : ConcaveOn ℝ Set.univ f)
    {base shiftLeft shiftRight : ℝ}
    (hshiftLeft : 0 ≤ shiftLeft) (hshiftRight : 0 ≤ shiftRight) :
    f (base + shiftLeft + shiftRight) + f base ≤
      f (base + shiftLeft) + f (base + shiftRight) := by
  by_cases htotal_zero : shiftLeft + shiftRight = 0
  · have hleft_zero : shiftLeft = 0 := by linarith
    have hright_zero : shiftRight = 0 := by linarith
    simp [hleft_zero, hright_zero]
  · have htotal_pos : 0 < shiftLeft + shiftRight :=
      lt_of_le_of_ne (add_nonneg hshiftLeft hshiftRight) (Ne.symm htotal_zero)
    let leftWeight : ℝ := shiftLeft / (shiftLeft + shiftRight)
    let rightWeight : ℝ := shiftRight / (shiftLeft + shiftRight)
    have hleftWeight : 0 ≤ leftWeight := div_nonneg hshiftLeft htotal_pos.le
    have hrightWeight : 0 ≤ rightWeight := div_nonneg hshiftRight htotal_pos.le
    have hweightSum : leftWeight + rightWeight = 1 := by
      dsimp [leftWeight, rightWeight]
      field_simp [htotal_pos.ne']
    have hfirst := hconcave.2
      (show base ∈ Set.univ by simp)
      (show base + shiftLeft + shiftRight ∈ Set.univ by simp)
      hrightWeight hleftWeight (by linarith [hweightSum])
    have hfirstArgument :
        rightWeight • base + leftWeight • (base + shiftLeft + shiftRight) =
          base + shiftLeft := by
      dsimp [leftWeight, rightWeight]
      field_simp [htotal_pos.ne']
      ring
    rw [hfirstArgument] at hfirst
    have hsecond := hconcave.2
      (show base ∈ Set.univ by simp)
      (show base + shiftLeft + shiftRight ∈ Set.univ by simp)
      hleftWeight hrightWeight hweightSum
    have hsecondArgument :
        leftWeight • base + rightWeight • (base + shiftLeft + shiftRight) =
          base + shiftRight := by
      dsimp [leftWeight, rightWeight]
      field_simp [htotal_pos.ne']
      ring
    rw [hsecondArgument] at hsecond
    simp only [smul_eq_mul] at hfirst hsecond
    have hsumTerms := add_le_add hfirst hsecond
    have hrearrange :
        (rightWeight * f base + leftWeight * f (base + shiftLeft + shiftRight)) +
            (leftWeight * f base + rightWeight * f (base + shiftLeft + shiftRight)) =
          f (base + shiftLeft + shiftRight) + f base := by
      calc
        _ = (leftWeight + rightWeight) *
            (f base + f (base + shiftLeft + shiftRight)) := by ring
        _ = f (base + shiftLeft + shiftRight) + f base := by
          rw [hweightSum]
          ring
    rw [hrearrange] at hsumTerms
    linarith

/--
The finite-sum form of `concave_increment_diminishes`. It directly packages
the step in which pointwise diminishing increments are summed over a finite
family of concave likelihood terms.
-/
theorem finset_sum_increment_diminishes
    {Index : Type*} (indices : Finset Index) (term : Index → ℝ → ℝ)
    (hconcave : ∀ index ∈ indices, ConcaveOn ℝ Set.univ (term index))
    (base shiftLeft shiftRight : Index → ℝ)
    (hshiftLeft : ∀ index ∈ indices, 0 ≤ shiftLeft index)
    (hshiftRight : ∀ index ∈ indices, 0 ≤ shiftRight index) :
    (∑ index ∈ indices,
      (term index (base index + shiftLeft index + shiftRight index) -
        term index (base index + shiftLeft index))) ≤
      ∑ index ∈ indices,
        (term index (base index + shiftRight index) - term index (base index)) := by
  refine Finset.sum_le_sum ?_
  intro index hindex
  have hpointwise := concave_increment_diminishes (term index)
    (hconcave index hindex) (base := base index)
    (hshiftLeft index hindex) (hshiftRight index hindex)
  linarith

end AppliedModelingLib
