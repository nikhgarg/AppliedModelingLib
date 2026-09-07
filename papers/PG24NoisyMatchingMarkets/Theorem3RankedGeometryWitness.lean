import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs
import PG24NoisyMatchingMarkets.Theorem3RoundedScaleFit
import PG24NoisyMatchingMarkets.Theorem3SublinearPrefix

/-!
# PG24 Theorem 3 ranked geometry witness

The finite dense-window / large-gap split must choose a large coalition
subset in either branch.  This module proves that choice in canonical ranked
coordinates.  It contains no probabilistic endpoint estimate or market
clearing premise.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- Enlarging a paper-large subset inside the same coalition preserves its
large-subset certificate. -/
theorem coalitionLargeSubset_of_subset
    {College : Type*} [DecidableEq College]
    {coalition small large : Finset College} {epsilon : ℝ}
    (hsmall : CoalitionLargeSubset coalition small epsilon)
    (hsmall_large : small ⊆ large) (hlarge_coalition : large ⊆ coalition) :
    CoalitionLargeSubset coalition large epsilon := by
  refine ⟨hlarge_coalition, hsmall.coalition_card_pos, ?_⟩
  apply lt_of_lt_of_le hsmall.large_ratio
  apply div_le_div_of_nonneg_right ?_ hsmall.coalition_card_pos.le
  exact_mod_cast Finset.card_le_card hsmall_large

/-- Deleting a longer ranked prefix produces a subset of the shorter-prefix
suffix. -/
theorem theorem3RankedSuffix_subset_of_le
    (C : ℕ) (cutoff : Fin (C + 1) → ℝ) {start cut : ℕ}
    (hstart_cut : start ≤ cut) :
    theorem3RankedSuffix C cutoff cut ⊆ theorem3RankedSuffix C cutoff start := by
  intro college hcollege
  rcases Finset.mem_image.mp hcollege with ⟨rank, hrank, rfl⟩
  unfold theorem3RankedSuffix
  refine Finset.mem_image.mpr ⟨rank, ?_, rfl⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ rank, ?_⟩
  exact hstart_cut.trans (Finset.mem_filter.mp hrank).2

/--
The ranked dense-window / large-gap dichotomy chooses a paper-large suffix in
both branches.  In the dense branch the window starts no later than the early
prefix, so its suffix contains the already-large early-prefix suffix.
-/
theorem theorem3_ranked_denseWindow_or_large_gap_with_large_subset
    {C : ℕ} {denseExponent prefixExponent width epsilon : ℝ}
    (cutoff : Fin (C + 1) → ℝ)
    (hC_pos : 0 < C)
    (hfit :
      theorem3DenseWindowCount C denseExponent ≤
        theorem3EarlyPrefixRank C prefixExponent)
    (hearly_large :
      CoalitionLargeSubset
        (Finset.univ : Finset (Fin (C + 1)))
        (theorem3RankedSuffix C cutoff
          (theorem3EarlyPrefixRank C prefixExponent)) epsilon) :
    (∃ start : ℕ,
      start + theorem3DenseWindowCount C denseExponent ≤
          theorem3DenseGapBlockCount C denseExponent prefixExponent *
            theorem3DenseWindowCount C denseExponent ∧
        theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff) start
          (theorem3DenseWindowCount C denseExponent) width ∧
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedSuffix C cutoff start) epsilon) ∨
      (theorem3RankedCutoffNat C cutoff 0 +
          (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
            width <
        theorem3RankedCutoffNat C cutoff
          (theorem3EarlyPrefixRank C prefixExponent) ∧
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedSuffix C cutoff
            (theorem3EarlyPrefixRank C prefixExponent)) epsilon) := by
  rcases theorem3_ranked_denseWindow_or_rounded_large_gap cutoff hC_pos hfit with
    hdense | hgap
  · rcases hdense with ⟨start, hterminal, hdense⟩
    refine Or.inl ⟨start, hterminal, hdense, ?_⟩
    apply coalitionLargeSubset_of_subset hearly_large
    · apply theorem3RankedSuffix_subset_of_le C cutoff
      calc
        start ≤ start + theorem3DenseWindowCount C denseExponent :=
          Nat.le_add_right _ _
        _ ≤ theorem3DenseGapBlockCount C denseExponent prefixExponent *
            theorem3DenseWindowCount C denseExponent := hterminal
        _ ≤ theorem3EarlyPrefixRank C prefixExponent :=
          theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
            C denseExponent prefixExponent
    · exact theorem3RankedSuffix_subset C cutoff start
  · exact Or.inr ⟨hgap, hearly_large⟩

/--
For the beta-only scales used by the repaired coalition route, the finite
ranked dichotomy is eventually well indexed and carries a paper-large suffix
in either branch.  The width is deliberately arbitrary here: its tail and
concentration estimates are separate probabilistic obligations.
-/
theorem theorem3_ranked_denseWindow_or_large_gap_with_large_subset_eventually
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon)
    (width : ℕ → ℝ) :
    ∀ᶠ C : ℕ in Filter.atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        (∃ start : ℕ,
          start + theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) ≤
              theorem3DenseGapBlockCount C
                (theorem3DenseClusterExponent beta)
                (theorem3EarlyCutoffExponent beta) *
                theorem3DenseWindowCount C
                  (theorem3DenseClusterExponent beta) ∧
            theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
              start
              (theorem3DenseWindowCount C
                (theorem3DenseClusterExponent beta))
              (width C) ∧
            CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1)))
              (theorem3RankedSuffix C cutoff start) epsilon) ∨
          (theorem3RankedCutoffNat C cutoff 0 +
              (theorem3DenseGapBlockCount C
                (theorem3DenseClusterExponent beta)
                (theorem3EarlyCutoffExponent beta) : ℝ) * width C <
            theorem3RankedCutoffNat C cutoff
              (theorem3EarlyPrefixRank C
                (theorem3EarlyCutoffExponent beta)) ∧
            CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1)))
              (theorem3RankedSuffix C cutoff
                (theorem3EarlyPrefixRank C
                  (theorem3EarlyCutoffExponent beta))) epsilon) := by
  filter_upwards
    [theorem3DenseClusterCount_eventually_le_earlyPrefixRank hbeta,
      theorem3CoalitionLargeSubset_rankedSuffix_earlyPrefix_eventually
        (theorem3EarlyCutoffExponent_lt_one hbeta) hepsilon,
      Filter.eventually_gt_atTop 0] with C hfit hearly_large hC_pos cutoff
  exact theorem3_ranked_denseWindow_or_large_gap_with_large_subset cutoff
    hC_pos hfit (hearly_large cutoff)

end

end PG24NoisyMatchingMarkets
