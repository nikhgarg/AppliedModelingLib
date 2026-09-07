import PG24NoisyMatchingMarkets.Theorem3DenseGapProbability
import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs

/-!
# PG24 Theorem 3 exact-cardinality ranked dense blocks

The source dense block has `ceil(C^phi)` iid draws.  The closed rank window
also contains its endpoint, so this file introduces the corresponding
half-open semantic block with exactly that cardinality.
-/

open MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The original colleges represented by the half-open rank interval
`[start, terminal)`. -/
noncomputable def theorem3RankedDenseBlock
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) : Finset (Fin (C + 1)) :=
  (Finset.Ico start terminal).image (theorem3RankedCollege C cutoff)

/-- An exact dense block has the cardinality of its half-open rank interval. -/
theorem theorem3RankedDenseBlock_card
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) :
    (theorem3RankedDenseBlock C cutoff start terminal).card =
      terminal.val - start.val := by
  unfold theorem3RankedDenseBlock
  rw [Finset.card_image_of_injective]
  · exact Fin.card_Ico start terminal
  · exact AppliedModelingLib.FiniteRanking.rankAgentByValue_injective
      (Finset.univ : Finset (Fin (C + 1))) cutoff
      (theorem3_ranked_cutoff_univ_card C)

/-- The `stride` ranks following `start` form an exact-cardinality iid block. -/
theorem theorem3RankedDenseBlock_card_of_start_add_stride_le
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (hterminal : start + stride ≤ C) :
    (theorem3RankedDenseBlock C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩).card = stride := by
  rw [theorem3RankedDenseBlock_card]
  change start + stride - start = stride
  omega

/-- The exact dense block lies in the suffix beginning at its first rank. -/
theorem theorem3RankedDenseBlock_subset_rankedSuffix
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (start terminal : Fin (C + 1)) :
    theorem3RankedDenseBlock C cutoff start terminal ⊆
      theorem3RankedSuffix C cutoff start.val := by
  intro college hcollege
  rcases Finset.mem_image.mp hcollege with ⟨rank, hrank, rfl⟩
  unfold theorem3RankedSuffix
  refine Finset.mem_image.mpr ⟨rank, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ rank, ?_⟩
  exact (Finset.mem_Ico.mp hrank).1

/-- Every cutoff in the exact dense block is below the dense-window ceiling. -/
theorem theorem3RankedDenseBlock_cutoff_le_start_add_of_denseRankWindow
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ) (width : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense :
      theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
        start stride width)
    {college : Fin (C + 1)}
    (hcollege : college ∈ theorem3RankedDenseBlock C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩) :
    cutoff college ≤ theorem3RankedCutoffNat C cutoff start + width := by
  rcases Finset.mem_image.mp hcollege with ⟨rank, hrank, rfl⟩
  have hrank_bounds := Finset.mem_Ico.mp hrank
  rw [← theorem3RankedCutoff_eq_original C cutoff rank]
  rw [← theorem3RankedCutoffNat_eq_rankedCutoff C cutoff
    (Nat.lt_succ_iff.mp rank.isLt)]
  exact (hdense rank.val (by exact_mod_cast hrank_bounds.1)
    (by exact_mod_cast hrank_bounds.2.le)).2

/-- Dense-branch high affordance using the exact `stride`-draw iid block. -/
theorem theorem3_ranked_denseBlock_high_affordance_gt_one_sub
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (width value epsilon : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense :
      theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
        start stride width)
    (hblock :
      1 - epsilon <
        1 - (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
          (theorem3RankedCutoffNat C cutoff start + width - value)) ^ stride) :
    1 - epsilon <
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (theorem3RankedSuffix C cutoff start) value cutoff := by
  apply theorem3_dense_high_affordance_gt_one_sub_of_window
    noiseLaw
    (theorem3RankedSuffix C cutoff start)
    (theorem3RankedDenseBlock C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩)
    cutoff value
    (theorem3RankedCutoffNat C cutoff start + width) epsilon
  · exact theorem3RankedDenseBlock_subset_rankedSuffix C cutoff _ _
  · intro college hcollege
    exact theorem3RankedDenseBlock_cutoff_le_start_add_of_denseRankWindow
      C start stride cutoff width hterminal hdense hcollege
  · rw [theorem3RankedDenseBlock_card_of_start_add_stride_le
      C start stride cutoff hterminal]
    exact hblock

end

end PG24NoisyMatchingMarkets
