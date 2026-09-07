import AppliedModelingLib.Foundations.Probability.FiniteSampleVariance
import AppliedModelingLib.Foundations.Probability.FiniteSelfBounding
import Mathlib.Tactic

/-!
# Self-bounding algebra for empirical pairwise variance

This module begins the source-faithful deterministic part of the
Maurer--Pontil variance proof.  It establishes how the scaled pairwise
variance changes under one coordinate replacement.  The self-bounding tail
and the source's squared-drop estimate are subsequent obligations.
-/

namespace AppliedModelingLib

open scoped BigOperators

/-- The source quantity `Z = n V_n` for a finite real sample. -/
noncomputable def finiteSampleScaledPairwiseVariance {n : ℕ}
    (sample : Fin n → ℝ) : ℝ :=
  (n : ℝ) * finiteSamplePairwiseVariance sample

/-- The same source quantity after evaluating a finite-carrier sample through
a bounded real statistic. -/
noncomputable def finiteSampleValueScaledPairwiseVariance
    {α : Type*} {n : ℕ} (statistic : α → ℝ) (sample : Fin n → α) : ℝ :=
  finiteSampleScaledPairwiseVariance (statistic ∘ sample)

/-- The unnormalized pairwise squared-disagreement row at one observation. -/
noncomputable def finiteSamplePairwiseRow {n : ℕ}
    (sample : Fin n → ℝ) (index : Fin n) : ℝ :=
  ∑ other : Fin n, (sample index - sample other) ^ 2

/-- A pairwise-disagreement row is a quadratic polynomial in its observation
and the first two sample power sums. -/
theorem finiteSamplePairwiseRow_eq_quadratic
    {n : ℕ} (sample : Fin n → ℝ) (index : Fin n) :
    finiteSamplePairwiseRow sample index =
      (n : ℝ) * sample index ^ 2 -
        2 * sample index * (∑ other : Fin n, sample other) +
          ∑ other : Fin n, sample other ^ 2 := by
  unfold finiteSamplePairwiseRow
  calc
    (∑ other : Fin n, (sample index - sample other) ^ 2) =
        ∑ other : Fin n,
          (sample index ^ 2 - 2 * sample index * sample other + sample other ^ 2) := by
            apply Finset.sum_congr rfl
            intro other _
            ring
    _ = (∑ _other : Fin n, sample index ^ 2) -
          2 * sample index * (∑ other : Fin n, sample other) +
            ∑ other : Fin n, sample other ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            congr 2
            rw [Finset.mul_sum]
    _ = (n : ℝ) * sample index ^ 2 -
          2 * sample index * (∑ other : Fin n, sample other) +
            ∑ other : Fin n, sample other ^ 2 := by simp

/-- The symmetrized polynomial in Maurer--Pontil's finite corollary. -/
noncomputable def empiricalVarianceTediousKernel (left right : ℝ) : ℝ :=
  left ^ 2 - left * right - left ^ 4 - 3 * left ^ 2 * right ^ 2 +
    4 * left ^ 3 * right

/-- The source's "tedious computation": after symmetrization the kernel is a
product of three nonnegative factors for observations in `[0,1]`. -/
theorem empiricalVarianceTediousKernel_add_swap_nonneg_of_unitInterval
    {left right : ℝ}
    (hleft : 0 ≤ left ∧ left ≤ 1) (hright : 0 ≤ right ∧ right ≤ 1) :
    0 ≤ empiricalVarianceTediousKernel left right +
      empiricalVarianceTediousKernel right left := by
  have hfirst : 0 ≤ left - right + 1 := by linarith [hleft.1, hright.2]
  have hsecond : 0 ≤ right - left + 1 := by linarith [hright.1, hleft.2]
  calc
    empiricalVarianceTediousKernel left right +
        empiricalVarianceTediousKernel right left =
        (left - right + 1) * (right - left + 1) * (right - left) ^ 2 := by
          unfold empiricalVarianceTediousKernel
          ring
    _ ≥ 0 := by positivity

/-- Summing the source's symmetrized kernel proves nonnegativity of its
unsymmetrized double sum. -/
theorem finiteSample_sum_empiricalVarianceTediousKernel_nonneg_of_unitInterval
    {n : ℕ} (sample : Fin n → ℝ)
    (hunit : ∀ index, 0 ≤ sample index ∧ sample index ≤ 1) :
    0 ≤ ∑ left : Fin n, ∑ right : Fin n,
      empiricalVarianceTediousKernel (sample left) (sample right) := by
  have hpoint (left right : Fin n) :
      0 ≤ empiricalVarianceTediousKernel (sample left) (sample right) +
        empiricalVarianceTediousKernel (sample right) (sample left) :=
    empiricalVarianceTediousKernel_add_swap_nonneg_of_unitInterval
      (hunit left) (hunit right)
  have hsym_nonneg :
      0 ≤ ∑ left : Fin n, ∑ right : Fin n,
        (empiricalVarianceTediousKernel (sample left) (sample right) +
          empiricalVarianceTediousKernel (sample right) (sample left)) := by
    exact Finset.sum_nonneg fun left _ =>
      Finset.sum_nonneg fun right _ => hpoint left right
  have hswap :
      (∑ left : Fin n, ∑ right : Fin n,
        empiricalVarianceTediousKernel (sample right) (sample left)) =
        ∑ left : Fin n, ∑ right : Fin n,
          empiricalVarianceTediousKernel (sample left) (sample right) := by
    rw [Finset.sum_comm]
  have htwice :
      (∑ left : Fin n, ∑ right : Fin n,
        (empiricalVarianceTediousKernel (sample left) (sample right) +
          empiricalVarianceTediousKernel (sample right) (sample left))) =
        2 * (∑ left : Fin n, ∑ right : Fin n,
          empiricalVarianceTediousKernel (sample left) (sample right)) := by
    calc
      (∑ left : Fin n, ∑ right : Fin n,
        (empiricalVarianceTediousKernel (sample left) (sample right) +
          empiricalVarianceTediousKernel (sample right) (sample left))) =
          ∑ left : Fin n,
            ((∑ right : Fin n,
              empiricalVarianceTediousKernel (sample left) (sample right)) +
              ∑ right : Fin n,
                empiricalVarianceTediousKernel (sample right) (sample left)) := by
              apply Finset.sum_congr rfl
              intro left _
              rw [Finset.sum_add_distrib]
      _ = (∑ left : Fin n, ∑ right : Fin n,
            empiricalVarianceTediousKernel (sample left) (sample right)) +
          (∑ left : Fin n, ∑ right : Fin n,
            empiricalVarianceTediousKernel (sample right) (sample left)) := by
              rw [Finset.sum_add_distrib]
      _ = 2 * (∑ left : Fin n, ∑ right : Fin n,
            empiricalVarianceTediousKernel (sample left) (sample right)) := by
              rw [hswap]
              ring
  rw [htwice] at hsym_nonneg
  linarith

/-- Expanding the squared pairwise rows into the first four finite power
sums.  This is the finite algebra behind Maurer--Pontil's corollary. -/
theorem finiteSample_sum_pairwiseRows_sq_eq_powerSums
    {n : ℕ} (sample : Fin n → ℝ) :
    (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) =
      (n : ℝ) ^ 2 * (∑ index : Fin n, sample index ^ 4) -
        4 * (n : ℝ) * (∑ index : Fin n, sample index) *
          (∑ index : Fin n, sample index ^ 3) +
        3 * (n : ℝ) * (∑ index : Fin n, sample index ^ 2) ^ 2 := by
  let first : ℝ := ∑ index : Fin n, sample index
  let second : ℝ := ∑ index : Fin n, sample index ^ 2
  let third : ℝ := ∑ index : Fin n, sample index ^ 3
  let fourth : ℝ := ∑ index : Fin n, sample index ^ 4
  have hrow (index : Fin n) :
      finiteSamplePairwiseRow sample index =
        (n : ℝ) * sample index ^ 2 - 2 * sample index * first + second := by
    simpa [first, second] using finiteSamplePairwiseRow_eq_quadratic sample index
  have hexpand (index : Fin n) :
      (finiteSamplePairwiseRow sample index) ^ 2 =
        (n : ℝ) ^ 2 * sample index ^ 4 -
          4 * (n : ℝ) * first * sample index ^ 3 +
          (2 * (n : ℝ) * second + 4 * first ^ 2) * sample index ^ 2 -
          4 * first * second * sample index + second ^ 2 := by
    rw [hrow]
    ring
  have hA : (∑ index : Fin n, (n : ℝ) ^ 2 * sample index ^ 4) =
      (n : ℝ) ^ 2 * fourth := by
    change (∑ index : Fin n, (n : ℝ) ^ 2 * sample index ^ 4) =
      (n : ℝ) ^ 2 * (∑ index : Fin n, sample index ^ 4)
    rw [← Finset.mul_sum]
  have hB : (∑ index : Fin n, 4 * (n : ℝ) * first * sample index ^ 3) =
      4 * (n : ℝ) * first * third := by
    change (∑ index : Fin n, (4 * (n : ℝ) * first) * sample index ^ 3) =
      (4 * (n : ℝ) * first) * (∑ index : Fin n, sample index ^ 3)
    rw [← Finset.mul_sum]
  have hC : (∑ index : Fin n,
      (2 * (n : ℝ) * second + 4 * first ^ 2) * sample index ^ 2) =
      (2 * (n : ℝ) * second + 4 * first ^ 2) * second := by
    change (∑ index : Fin n,
      (2 * (n : ℝ) * second + 4 * first ^ 2) * sample index ^ 2) =
      (2 * (n : ℝ) * second + 4 * first ^ 2) *
        (∑ index : Fin n, sample index ^ 2)
    rw [← Finset.mul_sum]
  have hD : (∑ index : Fin n, 4 * first * second * sample index) =
      4 * first * second * first := by
    change (∑ index : Fin n, (4 * first * second) * sample index) =
      (4 * first * second) * (∑ index : Fin n, sample index)
    rw [← Finset.mul_sum]
  have hE : (∑ _index : Fin n, second ^ 2) = (n : ℝ) * second ^ 2 := by simp
  calc
    (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) =
        ∑ index : Fin n,
          ((n : ℝ) ^ 2 * sample index ^ 4 -
            4 * (n : ℝ) * first * sample index ^ 3 +
            (2 * (n : ℝ) * second + 4 * first ^ 2) * sample index ^ 2 -
            4 * first * second * sample index + second ^ 2) := by
              apply Finset.sum_congr rfl
              intro index _
              exact hexpand index
    _ = (n : ℝ) ^ 2 * fourth - 4 * (n : ℝ) * first * third +
          (2 * (n : ℝ) * second + 4 * first ^ 2) * second -
          4 * first * second * first + (n : ℝ) * second ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [hA, hB, hC, hD, hE]
    _ = (n : ℝ) ^ 2 * (∑ index : Fin n, sample index ^ 4) -
          4 * (n : ℝ) * (∑ index : Fin n, sample index) *
            (∑ index : Fin n, sample index ^ 3) +
          3 * (n : ℝ) * (∑ index : Fin n, sample index ^ 2) ^ 2 := by
          simp [first, second, third, fourth]
          ring

/-- The full double pairwise squared-disagreement sum in terms of the first
two sample power sums. -/
theorem finiteSample_doublePairSqSum_eq_powerSums
    {n : ℕ} (sample : Fin n → ℝ) :
    (∑ left : Fin n, ∑ right : Fin n, (sample left - sample right) ^ 2) =
      2 * (n : ℝ) * (∑ index : Fin n, sample index ^ 2) -
        2 * (∑ index : Fin n, sample index) ^ 2 := by
  let first : ℝ := ∑ index : Fin n, sample index
  let second : ℝ := ∑ index : Fin n, sample index ^ 2
  have hrow (index : Fin n) :
      finiteSamplePairwiseRow sample index =
        (n : ℝ) * sample index ^ 2 - 2 * sample index * first + second := by
    simpa [first, second] using finiteSamplePairwiseRow_eq_quadratic sample index
  have hA : (∑ index : Fin n, (n : ℝ) * sample index ^ 2) =
      (n : ℝ) * second := by
    change (∑ index : Fin n, (n : ℝ) * sample index ^ 2) =
      (n : ℝ) * (∑ index : Fin n, sample index ^ 2)
    rw [← Finset.mul_sum]
  have hB : (∑ index : Fin n, 2 * sample index * first) = 2 * first ^ 2 := by
    calc
      (∑ index : Fin n, 2 * sample index * first) =
          (∑ index : Fin n, 2 * sample index) * first := by
            rw [← Finset.sum_mul]
      _ = 2 * first * first := by
            rw [← Finset.mul_sum]
      _ = 2 * first ^ 2 := by ring
  have hC : (∑ _index : Fin n, second) = (n : ℝ) * second := by simp
  calc
    (∑ left : Fin n, ∑ right : Fin n, (sample left - sample right) ^ 2) =
        ∑ left : Fin n, finiteSamplePairwiseRow sample left := by
          rfl
    _ = ∑ left : Fin n,
          ((n : ℝ) * sample left ^ 2 - 2 * sample left * first + second) := by
            apply Finset.sum_congr rfl
            intro left _
            exact hrow left
    _ = (n : ℝ) * second - 2 * first ^ 2 + (n : ℝ) * second := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hA, hB, hC]
    _ = 2 * (n : ℝ) * (∑ index : Fin n, sample index ^ 2) -
          2 * (∑ index : Fin n, sample index) ^ 2 := by
          simp [first, second]
          ring

/-- The unsymmetrized Maurer--Pontil kernel has an exact finite power-sum
expansion. -/
theorem finiteSample_sum_empiricalVarianceTediousKernel_eq_powerSums
    {n : ℕ} (sample : Fin n → ℝ) :
    (∑ left : Fin n, ∑ right : Fin n,
      empiricalVarianceTediousKernel (sample left) (sample right)) =
      (n : ℝ) * (∑ index : Fin n, sample index ^ 2) -
        (∑ index : Fin n, sample index) ^ 2 -
        (n : ℝ) * (∑ index : Fin n, sample index ^ 4) -
        3 * (∑ index : Fin n, sample index ^ 2) ^ 2 +
        4 * (∑ index : Fin n, sample index) *
          (∑ index : Fin n, sample index ^ 3) := by
  let first : ℝ := ∑ index : Fin n, sample index
  let second : ℝ := ∑ index : Fin n, sample index ^ 2
  let third : ℝ := ∑ index : Fin n, sample index ^ 3
  let fourth : ℝ := ∑ index : Fin n, sample index ^ 4
  have hA : (∑ left : Fin n, ∑ _right : Fin n, sample left ^ 2) =
      (n : ℝ) * second := by
    calc
      (∑ left : Fin n, ∑ _right : Fin n, sample left ^ 2) =
          ∑ left : Fin n, (n : ℝ) * sample left ^ 2 := by
            apply Finset.sum_congr rfl
            intro left _
            simp
      _ = (n : ℝ) * second := by
            change (∑ left : Fin n, (n : ℝ) * sample left ^ 2) =
              (n : ℝ) * (∑ left : Fin n, sample left ^ 2)
            rw [← Finset.mul_sum]
  have hB : (∑ left : Fin n, ∑ right : Fin n, sample left * sample right) =
      first ^ 2 := by
    calc
      (∑ left : Fin n, ∑ right : Fin n, sample left * sample right) =
          ∑ left : Fin n, sample left * first := by
            apply Finset.sum_congr rfl
            intro left _
            change (∑ right : Fin n, sample left * sample right) =
              sample left * (∑ right : Fin n, sample right)
            rw [← Finset.mul_sum]
      _ = first * first := by
            rw [← Finset.sum_mul]
      _ = first ^ 2 := by ring
  have hC : (∑ left : Fin n, ∑ _right : Fin n, sample left ^ 4) =
      (n : ℝ) * fourth := by
    calc
      (∑ left : Fin n, ∑ _right : Fin n, sample left ^ 4) =
          ∑ left : Fin n, (n : ℝ) * sample left ^ 4 := by
            apply Finset.sum_congr rfl
            intro left _
            simp
      _ = (n : ℝ) * fourth := by
            change (∑ left : Fin n, (n : ℝ) * sample left ^ 4) =
              (n : ℝ) * (∑ left : Fin n, sample left ^ 4)
            rw [← Finset.mul_sum]
  have hD : (∑ left : Fin n, ∑ right : Fin n,
      3 * sample left ^ 2 * sample right ^ 2) = 3 * second ^ 2 := by
    calc
      (∑ left : Fin n, ∑ right : Fin n,
        3 * sample left ^ 2 * sample right ^ 2) =
          ∑ left : Fin n, 3 * sample left ^ 2 * second := by
            apply Finset.sum_congr rfl
            intro left _
            change (∑ right : Fin n,
              (3 * sample left ^ 2) * sample right ^ 2) =
              (3 * sample left ^ 2) * (∑ right : Fin n, sample right ^ 2)
            rw [← Finset.mul_sum]
      _ = 3 * second * second := by
            calc
              (∑ left : Fin n, 3 * sample left ^ 2 * second) =
                  (∑ left : Fin n, 3 * sample left ^ 2) * second := by
                    rw [← Finset.sum_mul]
              _ = (3 * second) * second := by
                    congr 1
                    change (∑ left : Fin n, 3 * sample left ^ 2) = 3 * second
                    rw [← Finset.mul_sum]
      _ = 3 * second ^ 2 := by ring
  have hE : (∑ left : Fin n, ∑ right : Fin n,
      4 * sample left ^ 3 * sample right) = 4 * first * third := by
    calc
      (∑ left : Fin n, ∑ right : Fin n,
        4 * sample left ^ 3 * sample right) =
          ∑ left : Fin n, 4 * sample left ^ 3 * first := by
            apply Finset.sum_congr rfl
            intro left _
            change (∑ right : Fin n,
              (4 * sample left ^ 3) * sample right) =
              (4 * sample left ^ 3) * (∑ right : Fin n, sample right)
            rw [← Finset.mul_sum]
      _ = 4 * third * first := by
            calc
              (∑ left : Fin n, 4 * sample left ^ 3 * first) =
                  (∑ left : Fin n, 4 * sample left ^ 3) * first := by
                    rw [← Finset.sum_mul]
              _ = (4 * third) * first := by
                    congr 1
                    change (∑ left : Fin n, 4 * sample left ^ 3) = 4 * third
                    rw [← Finset.mul_sum]
      _ = 4 * first * third := by ring
  unfold empiricalVarianceTediousKernel
  have hinner (left : Fin n) :
      (∑ right : Fin n,
        (sample left ^ 2 - sample left * sample right - sample left ^ 4 -
          3 * sample left ^ 2 * sample right ^ 2 +
            4 * sample left ^ 3 * sample right)) =
        (∑ right : Fin n, sample left ^ 2) -
          (∑ right : Fin n, sample left * sample right) -
          (∑ right : Fin n, sample left ^ 4) -
          (∑ right : Fin n, 3 * sample left ^ 2 * sample right ^ 2) +
          ∑ right : Fin n, 4 * sample left ^ 3 * sample right := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  calc
    (∑ left : Fin n, ∑ right : Fin n,
      (sample left ^ 2 - sample left * sample right - sample left ^ 4 -
        3 * sample left ^ 2 * sample right ^ 2 +
          4 * sample left ^ 3 * sample right)) =
        ∑ left : Fin n,
          ((∑ right : Fin n, sample left ^ 2) -
            (∑ right : Fin n, sample left * sample right) -
            (∑ right : Fin n, sample left ^ 4) -
            (∑ right : Fin n, 3 * sample left ^ 2 * sample right ^ 2) +
            ∑ right : Fin n, 4 * sample left ^ 3 * sample right) := by
              apply Finset.sum_congr rfl
              intro left _
              exact hinner left
    _ = (∑ left : Fin n, ∑ right : Fin n, sample left ^ 2) -
          (∑ left : Fin n, ∑ right : Fin n, sample left * sample right) -
          (∑ left : Fin n, ∑ right : Fin n, sample left ^ 4) -
          (∑ left : Fin n, ∑ right : Fin n, 3 * sample left ^ 2 * sample right ^ 2) +
          ∑ left : Fin n, ∑ right : Fin n, 4 * sample left ^ 3 * sample right := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (n : ℝ) * (∑ index : Fin n, sample index ^ 2) -
          (∑ index : Fin n, sample index) ^ 2 -
          (n : ℝ) * (∑ index : Fin n, sample index ^ 4) -
          3 * (∑ index : Fin n, sample index ^ 2) ^ 2 +
          4 * (∑ index : Fin n, sample index) *
            (∑ index : Fin n, sample index ^ 3) := by
              rw [hA, hB, hC, hD, hE]

/-- Maurer--Pontil's finite corollary: squared pairwise rows are controlled by
one half of the total double-pair energy on a unit-interval sample. -/
theorem finiteSample_sum_pairwiseRows_sq_le_half_card_doublePairSqSum_of_unitInterval
    {n : ℕ} (sample : Fin n → ℝ)
    (hunit : ∀ index, 0 ≤ sample index ∧ sample index ≤ 1) :
    (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) ≤
      ((n : ℝ) / 2) *
        (∑ left : Fin n, ∑ right : Fin n, (sample left - sample right) ^ 2) := by
  have hkernel : 0 ≤ ∑ left : Fin n, ∑ right : Fin n,
      empiricalVarianceTediousKernel (sample left) (sample right) :=
    finiteSample_sum_empiricalVarianceTediousKernel_nonneg_of_unitInterval sample hunit
  have hid :
      (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) -
          ((n : ℝ) / 2) *
            (∑ left : Fin n, ∑ right : Fin n, (sample left - sample right) ^ 2) =
        -(n : ℝ) *
          (∑ left : Fin n, ∑ right : Fin n,
            empiricalVarianceTediousKernel (sample left) (sample right)) := by
    rw [finiteSample_sum_pairwiseRows_sq_eq_powerSums,
      finiteSample_doublePairSqSum_eq_powerSums,
      finiteSample_sum_empiricalVarianceTediousKernel_eq_powerSums]
    ring
  have hcard_nonneg : 0 ≤ (n : ℝ) := by positivity
  nlinarith [hid]

/-- The scaled pairwise variance is its symmetric double-pair energy divided
by `2 (n - 1)`. -/
theorem finiteSampleScaledPairwiseVariance_eq_doublePairSqSum
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n) :
    finiteSampleScaledPairwiseVariance sample =
      (∑ left : Fin n, ∑ right : Fin n, (sample left - sample right) ^ 2) /
        (2 * ((n : ℝ) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by omega) hn)
  unfold finiteSampleScaledPairwiseVariance finiteSamplePairwiseVariance
  rw [finiteSampleOrderedPairSqSum_eq_half_doublePairSqSum]
  field_simp [hn0]

/-- The squared old-row bounds satisfy the exact `a = n/(n-1)` estimate in
the source self-bounding verification for `Z = n V_n`. -/
theorem finiteSample_sum_sq_pairwiseRowBounds_le_scaledPairwiseVariance
    {n : ℕ} (sample : Fin n → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ index, 0 ≤ sample index ∧ sample index ≤ 1) :
    (∑ index : Fin n,
      (finiteSamplePairwiseRow sample index / ((n : ℝ) - 1)) ^ 2) ≤
      ((n : ℝ) / ((n : ℝ) - 1)) *
        finiteSampleScaledPairwiseVariance sample := by
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hgt : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  have hleft :
      (∑ index : Fin n,
        (finiteSamplePairwiseRow sample index / ((n : ℝ) - 1)) ^ 2) =
        (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) /
          (((n : ℝ) - 1) ^ 2) := by
    calc
      (∑ index : Fin n,
        (finiteSamplePairwiseRow sample index / ((n : ℝ) - 1)) ^ 2) =
          ∑ index : Fin n,
            (finiteSamplePairwiseRow sample index) ^ 2 /
              (((n : ℝ) - 1) ^ 2) := by
                apply Finset.sum_congr rfl
                intro index _
                field_simp [hden_pos.ne']
      _ = (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) /
            (((n : ℝ) - 1) ^ 2) := by
              rw [Finset.sum_div]
  rw [hleft, finiteSampleScaledPairwiseVariance_eq_doublePairSqSum sample hn]
  calc
    (∑ index : Fin n, (finiteSamplePairwiseRow sample index) ^ 2) /
        (((n : ℝ) - 1) ^ 2) ≤
        (((n : ℝ) / 2) *
          (∑ left : Fin n, ∑ right : Fin n,
            (sample left - sample right) ^ 2)) /
          (((n : ℝ) - 1) ^ 2) :=
      div_le_div_of_nonneg_right
        (finiteSample_sum_pairwiseRows_sq_le_half_card_doublePairSqSum_of_unitInterval
          sample hunit)
        (sq_nonneg _)
    _ = ((n : ℝ) / ((n : ℝ) - 1)) *
        ((∑ left : Fin n, ∑ right : Fin n,
          (sample left - sample right) ^ 2) /
          (2 * ((n : ℝ) - 1))) := by
      field_simp [hden_pos.ne']

/-- Exact one-coordinate replacement identity for `Z = n V_n`.  The new row
is evaluated on the genuinely updated sample, which is the reading of the
source's `X_{y,k}` notation that keeps its displayed identity correct. -/
theorem finiteSampleScaledPairwiseVariance_sub_update_eq_rowDifference
    {n : ℕ} (sample : Fin n → ℝ) (coordinate : Fin n) (value : ℝ)
    (hn : 2 ≤ n) :
    finiteSampleScaledPairwiseVariance sample -
        finiteSampleScaledPairwiseVariance (Function.update sample coordinate value) =
      ((∑ right : Fin n, (sample coordinate - sample right) ^ 2) -
        ∑ right : Fin n,
          ((Function.update sample coordinate value coordinate) -
            (Function.update sample coordinate value right)) ^ 2) /
        ((n : ℝ) - 1) := by
  rw [finiteSampleScaledPairwiseVariance_eq_doublePairSqSum sample hn,
    finiteSampleScaledPairwiseVariance_eq_doublePairSqSum
      (Function.update sample coordinate value) hn]
  rw [← sub_div,
    finiteDoubleSum_sub_update_eq_two_rowDifference
      (fun left right : ℝ => (left - right) ^ 2)
      (by intro left right; ring) (by intro value; ring)]
  have hden : ((n : ℝ) - 1) ≠ 0 := by
    have hgt : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  field_simp [hden]

/-- Dropping the scaled pairwise variance by one replacement is bounded by
the old coordinate's average pairwise squared disagreement. -/
theorem finiteSampleScaledPairwiseVariance_sub_update_le_oldRow
    {n : ℕ} (sample : Fin n → ℝ) (coordinate : Fin n) (value : ℝ)
    (hn : 2 ≤ n) :
    finiteSampleScaledPairwiseVariance sample -
        finiteSampleScaledPairwiseVariance (Function.update sample coordinate value) ≤
      (∑ right : Fin n, (sample coordinate - sample right) ^ 2) /
        ((n : ℝ) - 1) := by
  rw [finiteSampleScaledPairwiseVariance_sub_update_eq_rowDifference
    sample coordinate value hn]
  have hnew_nonneg : 0 ≤ ∑ right : Fin n,
      ((Function.update sample coordinate value coordinate) -
        (Function.update sample coordinate value right)) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hgt : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  exact div_le_div_of_nonneg_right (sub_le_self _ hnew_nonneg) hden_pos.le

/-- For a unit-interval sample, one coordinate's average pairwise squared
disagreement is at most one.  The self-pair contributes zero, yielding the
source denominator `n - 1`. -/
theorem finiteSample_pairwiseRow_div_le_one_of_unitInterval
    {n : ℕ} (sample : Fin n → ℝ) (coordinate : Fin n) (hn : 2 ≤ n)
    (hunit : ∀ index, 0 ≤ sample index ∧ sample index ≤ 1) :
    (∑ right : Fin n, (sample coordinate - sample right) ^ 2) /
        ((n : ℝ) - 1) ≤ 1 := by
  have hterm (right : Fin n) :
      (sample coordinate - sample right) ^ 2 ≤
        if right = coordinate then 0 else 1 := by
    by_cases hright : right = coordinate
    · subst right
      simp
    · have hlower : -1 ≤ sample coordinate - sample right := by
        linarith [(hunit coordinate).1, (hunit right).2]
      have hupper : sample coordinate - sample right ≤ 1 := by
        linarith [(hunit coordinate).2, (hunit right).1]
      have habs : |sample coordinate - sample right| ≤ 1 :=
        abs_le.mpr ⟨hlower, hupper⟩
      have hsq : (sample coordinate - sample right) ^ 2 ≤ 1 := by
        rw [← sq_abs]
        nlinarith [abs_nonneg (sample coordinate - sample right)]
      simpa [hright] using hsq
  have hsum :
      (∑ right : Fin n, (sample coordinate - sample right) ^ 2) ≤
        ∑ right : Fin n, if right = coordinate then 0 else 1 := by
    apply Finset.sum_le_sum
    intro right _
    exact hterm right
  have hone : (∑ right : Fin n, if right = coordinate then (0 : ℝ) else 1) =
      (n : ℝ) - 1 := by
    calc
      (∑ right : Fin n, if right = coordinate then (0 : ℝ) else 1) =
          (if coordinate = coordinate then 0 else 1) +
            ∑ right ∈ Finset.univ.erase coordinate,
              if right = coordinate then 0 else 1 := by
                rw [← Finset.add_sum_erase _ _ (Finset.mem_univ coordinate)]
      _ = ∑ _right ∈ Finset.univ.erase coordinate, (1 : ℝ) := by
            simp only [if_pos, zero_add]
            apply Finset.sum_congr rfl
            intro right hright
            have hright_ne : right ≠ coordinate := (Finset.mem_erase.mp hright).1
            simp [hright_ne]
      _ = ((Finset.univ.erase coordinate).card : ℝ) := by simp
      _ = (n : ℝ) - 1 := by
            have hcard : (Finset.univ.erase coordinate).card = n - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ coordinate)]
              simp
            rw [hcard, Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num
  have hden_pos : 0 < (n : ℝ) - 1 := by
    have hgt : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
    linarith
  apply (div_le_iff₀ hden_pos).mpr
  rw [← hone]
  simpa using hsum

/-- The scaled pairwise sample variance has the first self-bounding property
on every finite unit-interval carrier. -/
theorem finiteSampleValueScaledPairwiseVariance_replacementDrop_le_one
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (statistic : α → ℝ) (sample : Fin n → α) (coordinate : Fin n)
    (hn : 2 ≤ n) (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1) :
    finiteCoordinateReplacementDrop
      (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate ≤ 1 := by
  rcases exists_replacement_eq_finiteCoordinateReplacementInf
    (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate with
    ⟨value, hvalue⟩
  unfold finiteCoordinateReplacementDrop
  rw [← hvalue]
  have hmapUpdate : statistic ∘ Function.update sample coordinate value =
      Function.update (statistic ∘ sample) coordinate (statistic value) := by
    funext index
    by_cases hindex : index = coordinate
    · subst index
      simp
    · simp [Function.comp_def, hindex]
  unfold finiteSampleValueScaledPairwiseVariance
  rw [hmapUpdate]
  apply le_trans
    (finiteSampleScaledPairwiseVariance_sub_update_le_oldRow
      (statistic ∘ sample) coordinate (statistic value) hn)
  apply finiteSample_pairwiseRow_div_le_one_of_unitInterval
    (statistic ∘ sample) coordinate hn
  intro index
  exact hunit (sample index)

/-- More precisely, each replacement drop is bounded by its old pairwise-row
average.  This is the pointwise input to the source squared-drop estimate. -/
theorem finiteSampleValueScaledPairwiseVariance_replacementDrop_le_pairwiseRowBound
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (statistic : α → ℝ) (sample : Fin n → α) (coordinate : Fin n)
    (hn : 2 ≤ n) :
    finiteCoordinateReplacementDrop
      (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate ≤
      finiteSamplePairwiseRow (statistic ∘ sample) coordinate / ((n : ℝ) - 1) := by
  rcases exists_replacement_eq_finiteCoordinateReplacementInf
    (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate with
    ⟨value, hvalue⟩
  unfold finiteCoordinateReplacementDrop
  rw [← hvalue]
  have hmapUpdate : statistic ∘ Function.update sample coordinate value =
      Function.update (statistic ∘ sample) coordinate (statistic value) := by
    funext index
    by_cases hindex : index = coordinate
    · subst index
      simp
    · simp [Function.comp_def, hindex]
  unfold finiteSampleValueScaledPairwiseVariance
  rw [hmapUpdate]
  simpa [finiteSamplePairwiseRow] using
    (finiteSampleScaledPairwiseVariance_sub_update_le_oldRow
      (statistic ∘ sample) coordinate (statistic value) hn)

/-- The scaled pairwise sample variance satisfies exactly the deterministic
self-bounding conditions used by Maurer--Pontil's variance tail argument. -/
theorem finiteSampleValueScaledPairwiseVariance_isFiniteSelfBounding
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    (statistic : α → ℝ) (hn : 2 ≤ n)
    (hunit : ∀ value, 0 ≤ statistic value ∧ statistic value ≤ 1) :
    FiniteSelfBounding
      (fun sample : Fin n → α => finiteSampleValueScaledPairwiseVariance statistic sample)
      ((n : ℝ) / ((n : ℝ) - 1)) := by
  constructor
  · intro sample coordinate
    exact finiteSampleValueScaledPairwiseVariance_replacementDrop_le_one
      statistic sample coordinate hn hunit
  · intro sample
    have hden_pos : 0 < (n : ℝ) - 1 := by
      have hgt : (1 : ℝ) < (n : ℝ) := by
        exact_mod_cast (show 1 < n from lt_of_lt_of_le (by omega) hn)
      linarith
    have hdrop_sq (coordinate : Fin n) :
        (finiteCoordinateReplacementDrop
          (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate) ^ 2 ≤
          (finiteSamplePairwiseRow (statistic ∘ sample) coordinate /
            ((n : ℝ) - 1)) ^ 2 := by
      have hdrop_nonneg := finiteCoordinateReplacementDrop_nonneg
        (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate
      have hdrop_le :=
        finiteSampleValueScaledPairwiseVariance_replacementDrop_le_pairwiseRowBound
          statistic sample coordinate hn
      have hrow_nonneg : 0 ≤ finiteSamplePairwiseRow (statistic ∘ sample) coordinate := by
        unfold finiteSamplePairwiseRow
        exact Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hrowBound_nonneg :
          0 ≤ finiteSamplePairwiseRow (statistic ∘ sample) coordinate /
            ((n : ℝ) - 1) :=
        div_nonneg hrow_nonneg hden_pos.le
      nlinarith
    calc
      (∑ coordinate : Fin n,
        (finiteCoordinateReplacementDrop
          (finiteSampleValueScaledPairwiseVariance statistic) sample coordinate) ^ 2) ≤
          ∑ coordinate : Fin n,
            (finiteSamplePairwiseRow (statistic ∘ sample) coordinate /
              ((n : ℝ) - 1)) ^ 2 := by
              apply Finset.sum_le_sum
              intro coordinate _
              exact hdrop_sq coordinate
      _ ≤ ((n : ℝ) / ((n : ℝ) - 1)) *
          finiteSampleScaledPairwiseVariance (statistic ∘ sample) :=
        finiteSample_sum_sq_pairwiseRowBounds_le_scaledPairwiseVariance
          (statistic ∘ sample) hn (fun index => hunit (sample index))
      _ = ((n : ℝ) / ((n : ℝ) - 1)) *
          finiteSampleValueScaledPairwiseVariance statistic sample := by
            rfl

end AppliedModelingLib
