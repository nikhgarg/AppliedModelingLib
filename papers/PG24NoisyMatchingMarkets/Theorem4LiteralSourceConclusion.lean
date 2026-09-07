import PG24NoisyMatchingMarkets.Theorem4LiteralSourceActualPmu
import Mathlib.Tactic

/-!
# PG24 Theorem 4 Literal Source Conclusion

This is the source-facing conclusion for finite broader markets.  It fixes the
coalition value law before the error tolerance, quantifies only over literal
source data after the threshold, and reports the large subset on the actual
global-college carrier.
-/

open MeasureTheory
open AppliedModelingLib.Matching

namespace PG24NoisyMatchingMarkets

noncomputable section

universe u v w x

/--
Theorem 4 for literal extended-model source data with one fixed coalition value
law.  The threshold is selected before the arbitrary type, outcome, broader
college carrier, cutoff carrier, and source economy are supplied.
-/
theorem theorem4_literal_source_coalition_amplification_fixed_eta_of_longTailed
    (noiseLaw fixed_eta : Measure ℝ)
    [IsProbabilityMeasure noiseLaw] [IsProbabilityMeasure fixed_eta]
    (hlong : LongTailedSurvival
      (AppliedModelingLib.Probability.upperTailMass noiseLaw))
    {totalSupply : ℝ} (htotalSupply_pos : 0 < totalSupply)
    (htotalSupply_lt_one : totalSupply < 1) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ N : ℕ, ∀ C : ℕ, N ≤ C →
        ∀ (StudentType : Type u) [MeasurableSpace StudentType]
          (Outcome : Type v) [MeasurableSpace Outcome]
          (GlobalCollege : Type w) [Fintype GlobalCollege]
          (Cutoff : Type x)
          (data :
            PG24LiteralSourceStableData C noiseLaw fixed_eta totalSupply
              StudentType Outcome GlobalCollege Cutoff),
          ∃ effectiveSupply : ℝ,
          ∃ indexedLargeSubset : Finset (Fin (C + 1)),
          ∃ actualCoalition : Finset GlobalCollege,
          ∃ actualLargeSubset : Finset GlobalCollege,
          ∃ regularSet : Set ℝ,
            actualCoalition =
                theorem4EmbeddedCoalition data.coalitionEmbedding ∧
              actualLargeSubset =
                theorem4EmbeddedCoalitionSubset data.coalitionEmbedding
                  indexedLargeSubset ∧
              CoalitionLargeSubset actualCoalition actualLargeSubset epsilon ∧
              N < actualCoalition.card ∧
              fixed_eta.real regularSetᶜ ≤ epsilon ∧
              (∀ value ∈ regularSet,
                |data.pMuOnActualSubset value actualLargeSubset -
                    effectiveSupply| < epsilon) := by
  intro epsilon hepsilon_pos
  rcases
      PG24ExtendedCoalitionSourceStableInstance.theorem4_source_native_coalition_amplification_pMu_uniform_of_longTailed
        noiseLaw fixed_eta hlong htotalSupply_pos htotalSupply_lt_one
        epsilon hepsilon_pos with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro C hthreshold StudentType _ Outcome _ GlobalCollege _ Cutoff data
  rcases hN C hthreshold StudentType Outcome GlobalCollege Cutoff
      data.toExtendedCoalitionSourceStableInstance with
    ⟨effectiveSupply, indexedLargeSubset, regularSet, hlarge, hregular, hclose⟩
  refine ⟨effectiveSupply, indexedLargeSubset,
    theorem4EmbeddedCoalition data.coalitionEmbedding,
    theorem4EmbeddedCoalitionSubset data.coalitionEmbedding indexedLargeSubset,
    regularSet, rfl, rfl, ?_, ?_, hregular, ?_⟩
  · exact coalitionLargeSubset_embedded_of_indexed
      data.coalitionEmbedding indexedLargeSubset hlarge
  · exact theorem4EmbeddedCoalition_card_gt_of_threshold_le
      data.coalitionEmbedding hthreshold
  · intro value hvalue
    rw [data.pMuOnActualSubset_embedded_eq_indexed value indexedLargeSubset]
    exact hclose value hvalue

end

end PG24NoisyMatchingMarkets
