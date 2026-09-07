import PG24NoisyMatchingMarkets.Theorem1LargeGapGeometry
import PG24NoisyMatchingMarkets.Theorem3RoundedRanks

/-!
# PG24 Theorem 3 dense-window / large-gap geometry

The extended attenuation proof needs a finite dichotomy for an increasing
cutoff list.  Inside the rounded early prefix, either some consecutive
`C^phi`-sized rank window is dense, or every such window is sparse and the
telescoping argument produces a large cutoff separation.  This file makes
that split explicit without assuming a market-clearing, capacity, probability,
or attenuation conclusion.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The rounded early prefix has the source proof's dense-window / large-gap
dichotomy.  The left branch is a concrete dense rank window.  The right branch
is the telescoped separation from the first cutoff to the rounded early-prefix
rank.  Rounding is supplied by `Theorem3RoundedRanks`; finite telescoping is
supplied by `Theorem1LargeGapGeometry`.
-/
theorem theorem3_denseWindow_or_rounded_large_gap
    {C : ℕ} {denseExponent prefixExponent width : ℝ}
    (cutoff : ℕ → ℝ)
    (hC_pos : 0 < C)
    (hmono : Monotone cutoff)
    (hfit :
      theorem3DenseWindowCount C denseExponent ≤
        theorem3EarlyPrefixRank C prefixExponent) :
    (∃ start : ℕ,
      start + theorem3DenseWindowCount C denseExponent ≤
          theorem3DenseGapBlockCount C denseExponent prefixExponent *
            theorem3DenseWindowCount C denseExponent ∧
        theorem1TailDenseRankWindow cutoff start
          (theorem3DenseWindowCount C denseExponent) width) ∨
      cutoff 0 +
          (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
            width <
        cutoff (theorem3EarlyPrefixRank C prefixExponent) := by
  by_cases hdense :
      ∃ start : ℕ,
        start + theorem3DenseWindowCount C denseExponent ≤
            theorem3DenseGapBlockCount C denseExponent prefixExponent *
              theorem3DenseWindowCount C denseExponent ∧
          theorem1TailDenseRankWindow cutoff start
            (theorem3DenseWindowCount C denseExponent) width
  · exact Or.inl hdense
  · refine Or.inr ?_
    apply theorem1Tail_rank_stride_gap_to_later_rank
      cutoff
      (theorem3DenseWindowCount C denseExponent)
      (theorem3DenseGapBlockCount C denseExponent prefixExponent)
      (theorem3EarlyPrefixRank C prefixExponent)
      width
    · exact
        theorem3DenseGapBlockCount_pos_of_denseWindowCount_le_earlyPrefixRank
          hC_pos hfit
    · intro i hi
      apply
        (theorem1Tail_not_dense_rank_window_iff cutoff i
          (theorem3DenseWindowCount C denseExponent) width hmono).mp
      intro hdense_i
      exact hdense ⟨i, hi, hdense_i⟩
    · exact hmono
    · exact
        theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank
          C denseExponent prefixExponent

end

end PG24NoisyMatchingMarkets
