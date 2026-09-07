import PG24NoisyMatchingMarkets.Theorem3DenseHighEndpoint

/-!
# PG24 Theorem 3 dense-branch high endpoint on the full coalition

The dense-block calculation first certifies high affordability for its
semantic ranked suffix.  Affordability is monotone under enlarging the active
college set, so this module records the source-required full-coalition
endpoint without adding any ordering or market-clearing premise.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The dense-branch high endpoint holds for the full coalition as well as
the ranked suffix used to witness the dense iid block. -/
theorem theorem3_ranked_dense_high_full_endpoint_eventually
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ (cutoff : Fin (C + 1) → ℝ) (start : ℕ),
        start + theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) ≤ C →
        theorem1TailDenseRankWindow (theorem3RankedCutoffNat C cutoff)
          start (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta))
          (Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)) →
        1 - epsilon <
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1)))
            (theorem3RankedCutoffNat C cutoff start -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (theorem3DenseWindowCount C
                  (theorem3DenseClusterExponent beta) - 1) + epsilon)
            cutoff := by
  filter_upwards [theorem3_ranked_dense_high_endpoint_eventually
    noiseLaw hbeta hvariance hepsilon] with C hendpoint cutoff start
      hterminal hdense
  exact lt_of_lt_of_le (hendpoint cutoff start hterminal hdense)
    (cutoffAffordanceProbability_mono_active
      (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
      (theorem3RankedSuffix_subset C cutoff start))

end

end PG24NoisyMatchingMarkets
