import AppliedModelingLib.SocialChoice.Ranking.Mallows
import AppliedModelingLib.SocialChoice.Ranking.Payoff

/-!
# Mallows Payoff Finite Sums

Reusable Mallows finite-sum identities for first-choice value-gap masses and
positive-denominator normal forms.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace SocialChoice
namespace Ranking

noncomputable section

namespace MallowsSpec

variable {n : ℕ} (M : MallowsSpec n)

/--
Unnormalized first-choice fiber gap mass.

This is the Mallows-weight numerator corresponding to
`firstChoiceGapMass M.law value c`.
-/
def firstChoiceGapWeight
    (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  ∑ π : Ranking n,
    if c = firstChoice π then
      mallowsWeight M.q M.center π * valueGap value π
    else
      0

/-- First-choice gap mass reduces to an unnormalized Mallows-weight numerator. -/
theorem firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition
    (value : Candidate n → ℝ) (c : Candidate n) :
    firstChoiceGapMass M.law value c =
      M.firstChoiceGapWeight value c / M.partition := by
  classical
  unfold firstChoiceGapMass pmfExp firstChoiceGapWeight
  calc
    ∑ π : Ranking n, (M.law π).toReal *
        (if c = firstChoice π then valueGap value π else 0)
        = ∑ π : Ranking n,
            (mallowsWeight M.q M.center π / M.partition) *
              (if c = firstChoice π then valueGap value π else 0) := by
          refine Finset.sum_congr rfl ?_
          intro π _
          rw [M.law_apply_toReal]
    _ = ∑ π : Ranking n,
          (if c = firstChoice π then
              mallowsWeight M.q M.center π * valueGap value π
            else
              0) / M.partition := by
          refine Finset.sum_congr rfl ?_
          intro π _
          by_cases h : c = firstChoice π
          · have h' : c = π 0 := by simpa [firstChoice] using h
            simp [h']
            ring
          · have h' : c ≠ π 0 := by simpa [firstChoice] using h
            simp [h']
    _ = (∑ π : Ranking n,
          if c = firstChoice π then
            mallowsWeight M.q M.center π * valueGap value π
          else
            0) / M.partition := by
          rw [Finset.sum_div]

/-- First-choice miss probability with the positive Mallows denominator exposed. -/
theorem firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition
    (c : Candidate n) :
    firstChoiceMissProb M.law c =
      (M.partition - M.firstWeight c) / M.partition := by
  have hprob :
      firstChoiceProb M.law c = M.firstWeight c / M.partition :=
    M.firstChoiceProb_eq_firstWeight_div_partition c
  unfold firstChoiceMissProb
  rw [hprob]
  field_simp [M.partition_ne_zero]

/--
The independent-reranking candidate sum with all positive Mallows denominators
cleared.
-/
theorem firstChoice_miss_gap_sum_eq_weight_sum_div
    (value : Candidate n → ℝ) :
    (∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c) =
      (∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c) /
        (M.partition * M.partition) := by
  classical
  calc
    ∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c
        = ∑ c : Candidate n,
            ((M.partition - M.firstWeight c) *
              M.firstChoiceGapWeight value c) /
              (M.partition * M.partition) := by
          refine Finset.sum_congr rfl ?_
          intro c _
          rw [M.firstChoiceMissProb_eq_partition_sub_firstWeight_div_partition c]
          rw [M.firstChoiceGapMass_eq_firstChoiceGapWeight_div_partition value c]
          field_simp [M.partition_ne_zero]
    _ = (∑ c : Candidate n,
          (M.partition - M.firstWeight c) *
            M.firstChoiceGapWeight value c) /
        (M.partition * M.partition) := by
          rw [Finset.sum_div]

/-- Positive cleared Mallows sum implies positive independent-reranking sum. -/
theorem firstChoice_miss_gap_sum_pos_of_weight_sum_pos
    {value : Candidate n → ℝ}
    (hsum :
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c) :
    0 < ∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c := by
  rw [M.firstChoice_miss_gap_sum_eq_weight_sum_div value]
  exact div_pos hsum (mul_pos M.partition_pos M.partition_pos)

/-- Positivity of the normalized first-choice sum is equivalent to its cleared form. -/
theorem firstChoice_miss_gap_sum_pos_iff_weight_sum_pos
    (value : Candidate n → ℝ) :
    (0 < ∑ c : Candidate n,
      firstChoiceMissProb M.law c * firstChoiceGapMass M.law value c) ↔
      0 < ∑ c : Candidate n,
        (M.partition - M.firstWeight c) *
          M.firstChoiceGapWeight value c := by
  rw [M.firstChoice_miss_gap_sum_eq_weight_sum_div value]
  constructor
  · intro h
    by_contra hnot
    have hsum_nonpos :
        (∑ c : Candidate n,
          (M.partition - M.firstWeight c) *
            M.firstChoiceGapWeight value c) ≤ 0 := le_of_not_gt hnot
    have hden_nonneg : 0 ≤ M.partition * M.partition :=
      le_of_lt (mul_pos M.partition_pos M.partition_pos)
    have hdiv_nonpos :
        (∑ c : Candidate n,
          (M.partition - M.firstWeight c) *
            M.firstChoiceGapWeight value c) /
          (M.partition * M.partition) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hsum_nonpos hden_nonneg
    linarith
  · intro h
    exact div_pos h (mul_pos M.partition_pos M.partition_pos)

end MallowsSpec

end

end Ranking
end SocialChoice
end AppliedModelingLib
