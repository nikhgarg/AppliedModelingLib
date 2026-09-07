import PG24NoisyMatchingMarkets.Theorem3LargeGapBridge
import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs

/-!
# PG24 Theorem 3 ranked large-gap probability bridge

The large-gap branch is expressed in canonical ranked-cutoff coordinates and
then transported back to the original college indices before the iid tail
argument is applied.  The remaining inputs are the genuine asymptotic gap and
centering estimates, not a conclusion-shaped cutoff premise.
-/

open Filter Topology MeasureTheory Asymptotics

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
An eventual large separation in canonical ranked-cutoff coordinates is the
same separation between the corresponding original colleges.
-/
theorem theorem3_ranked_cutoff_gap_of_ranked_gap
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {rank : ℕ → ℕ} {gapLower : ℕ → ℝ}
    (hrank_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 + (gapLower C : ℝ) <
        theorem3RankedCutoffNat C (cutoff C) (rank C)) :
    ∀ᶠ C : ℕ in atTop,
      (gapLower C : ℝ) <
        cutoff C (theorem3RankedCollege C (cutoff C)
          ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) -
        cutoff C (theorem3RankedCollege C (cutoff C)
          ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) := by
  filter_upwards [hrank_gap] with C hgap
  rw [theorem3RankedCutoffNat_eq_cutoff_rankedCollege,
    theorem3RankedCutoffNat_eq_cutoff_rankedCollege] at hgap
  linarith

/--
The ranked large-gap branch closes the high side of Theorem 3 directly for
the original coalition.  `gapLower` is written as a real scale so it can be
the telescoped `blocks * width`; its convergence and the centering little-o
relation are explicit mathematical obligations.
-/
theorem theorem3_ranked_fullAffordance_eventually_one_sub_lt_of_large_gap
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    {rank : ℕ → ℕ} {gapLower slack value : ℕ → ℝ}
    (hrank_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 + gapLower C <
        theorem3RankedCutoffNat C (cutoff C) (rank C))
    (hvalue_below_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (theorem3RankedCollege C (cutoff C)
        ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) -
        value C ≤ slack C)
    (hgap_toTop : Tendsto gapLower atTop atTop)
    (hslack_little : slack =o[atTop] gapLower)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1))) (value C) (cutoff C) := by
  apply theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_gap_of_isLittleO
    noiseLaw
    (fun C => theorem3RankedCollege C (cutoff C)
      ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
    (fun C => theorem3RankedCollege C (cutoff C)
      ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
    ?_ hvalue_below_rank hgap_toTop hslack_little epsilon hepsilon
  filter_upwards [hrank_gap] with C hgap
  rw [theorem3RankedCutoffNat_eq_cutoff_rankedCollege,
    theorem3RankedCutoffNat_eq_cutoff_rankedCollege] at hgap
  linarith

end

end PG24NoisyMatchingMarkets
