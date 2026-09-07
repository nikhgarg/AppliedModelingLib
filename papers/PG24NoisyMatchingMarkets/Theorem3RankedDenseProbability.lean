import PG24NoisyMatchingMarkets.Theorem3DenseGapProbability
import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs

/-!
# PG24 Theorem 3 ranked dense-branch probability bridge

This module connects the semantic ranked-cutoff construction to the iid
dense-cluster probability estimates.  Its hypotheses are only the remaining
probabilistic maximum-block estimates; the cutoff window, suffix, cardinality,
and floor/ceiling relations are derived from the arbitrary original cutoff
function.
-/

open MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The high side of a semantic dense ranked window.  Once the iid maximum block
crosses its derived ceiling with high probability, the whole semantic suffix
has high affordance probability.
-/
theorem theorem3_ranked_dense_high_affordance_gt_one_sub
    (C start stride : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (width value epsilon : ℝ)
    (hterminal : start + stride ≤ C)
    (hdense :
      theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
        start stride width)
    (hblock :
      1 - epsilon <
        1 -
          (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
            (theorem3RankedCutoffNat C cutoff start + width - value)) ^
            (theorem3RankedWindow C cutoff
              ⟨start, Nat.lt_succ_of_le
                (le_trans (Nat.le_add_right start stride) hterminal)⟩
              ⟨start + stride, Nat.lt_succ_of_le hterminal⟩).card) :
    1 - epsilon <
      cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (theorem3RankedSuffix C cutoff start) value cutoff := by
  apply theorem3_dense_high_affordance_gt_one_sub_of_window
    noiseLaw
    (theorem3RankedSuffix C cutoff start)
    (theorem3RankedWindow C cutoff
      ⟨start, Nat.lt_succ_of_le
        (le_trans (Nat.le_add_right start stride) hterminal)⟩
      ⟨start + stride, Nat.lt_succ_of_le hterminal⟩)
    cutoff value
    (theorem3RankedCutoffNat C cutoff start + width) epsilon
  · exact theorem3RankedWindow_subset_rankedSuffix C cutoff _ _
  · intro college hcollege
    exact theorem3RankedWindow_cutoff_le_start_add_of_denseRankWindow
      C start stride cutoff width hterminal hdense hcollege
  · exact hblock

/--
The low side of a semantic dense ranked window.  The suffix floor is derived
from canonical cutoff ranking, then the corrected finite geometric/union-bound
estimate controls its affordability probability.
-/
theorem theorem3_ranked_dense_low_affordance_le
    (C start : ℕ) (cutoff : Fin (C + 1) → ℝ)
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (value crossing : ℝ) {m : ℕ}
    (hstart : start ≤ C) (hm : 0 < m)
    (hcrossing :
      crossing = 1 -
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
          (theorem3RankedCutoffNat C cutoff start - value)) ^ m)
    (hcrossing_le_half : crossing ≤ 1 / 2) :
    cutoffAffordanceProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (theorem3RankedSuffix C cutoff start) value cutoff ≤
      ((theorem3RankedSuffix C cutoff start).card : ℝ) *
        (2 * crossing / (m : ℝ)) := by
  apply theorem3_dense_low_affordance_le_card_mul_blockCrossing
    noiseLaw (theorem3RankedSuffix C cutoff start) cutoff
    (theorem3RankedCutoffNat C cutoff start) value crossing hm
  · intro college hcollege
    exact theorem3RankedCutoffNat_le_cutoff_of_mem_rankedSuffix
      C cutoff hstart hcollege
  · exact hcrossing
  · exact hcrossing_le_half

end

end PG24NoisyMatchingMarkets
