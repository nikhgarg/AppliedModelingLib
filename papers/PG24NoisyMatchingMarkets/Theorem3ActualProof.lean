import PG24NoisyMatchingMarkets.Theorem3RankedGeometryWitness
import PG24NoisyMatchingMarkets.Theorem3DenseLowEndpoint
import PG24NoisyMatchingMarkets.Theorem3DenseHighFullEndpoint
import PG24NoisyMatchingMarkets.Theorem3LargeGapLowEndpoint
import PG24NoisyMatchingMarkets.Theorem3LargeGapHighEndpoint
import PG24NoisyMatchingMarkets.Theorem3IidExpectedMaximumLog

/-!
# PG24 Theorem 3 actual proof assembly

This module joins the canonical ranked cutoff geometry to the proved
probabilistic endpoint estimates.  It deliberately quantifies over arbitrary
finite cutoff vectors: no sorted-coordinate convention, capacity premise, or
endpoint conclusion is an input.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The dense-window branch already provides the complete paper-facing
attenuation witness once its semantic large suffix and valid terminal rank are
known. -/
theorem theorem3_dense_branch_attenuation_eventually
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
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedSuffix C cutoff start) epsilon →
        ∃ threshold : ℝ, ∃ largeSubset : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
            (∀ v : ℝ, v < threshold - epsilon →
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset v cutoff < epsilon) ∧
            (∀ v : ℝ, threshold + epsilon < v →
              1 - epsilon < cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v cutoff) := by
  filter_upwards [theorem3_ranked_dense_low_endpoint_eventually
      noiseLaw hbeta hvariance hepsilon,
    theorem3_ranked_dense_high_full_endpoint_eventually
      noiseLaw hbeta hvariance hepsilon] with C hlow hhigh cutoff start
      hterminal hdense hlarge
  let threshold : ℝ := theorem3RankedCutoffNat C cutoff start -
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
      (theorem3DenseWindowCount C
        (theorem3DenseClusterExponent beta) - 1)
  have hstart : start ≤ C :=
    le_trans (Nat.le_add_right _ _) hterminal
  refine ⟨threshold, theorem3RankedSuffix C cutoff start, hlarge, ?_, ?_⟩
  · intro v hv
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (theorem3RankedSuffix C cutoff start) v cutoff ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (theorem3RankedSuffix C cutoff start) (threshold - epsilon) cutoff :=
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (active := theorem3RankedSuffix C cutoff start) (cutoff := cutoff)
        (le_of_lt hv)
    exact lt_of_le_of_lt hmono
      (by simpa [threshold] using (hlow cutoff start hstart))
  · intro v hv
    have hmono :
        cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) (threshold + epsilon) cutoff ≤
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1))) v cutoff :=
      cutoffAffordanceProbability_mono_value
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (active := (Finset.univ : Finset (Fin (C + 1)))) (cutoff := cutoff)
        (le_of_lt hv)
    exact lt_of_lt_of_le
      (by simpa [threshold] using (hhigh cutoff start hterminal hdense)) hmono

/-- Assembly of the two canonical cutoff-geometry branches, with the analytic
expected-maximum logarithmic estimate made explicit.  The variance-only
theorem below this assembly discharges that estimate from the iid product
coupling, so this is not a paper-facing premise. -/
theorem theorem3_attenuation_in_coalitions_of_iid_beta_of_expectedMaximum_div_log
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hmean : Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C /
          Real.log (C : ℝ))
      atTop (nhds 0))
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        ∃ threshold : ℝ, ∃ largeSubset : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
            (∀ v : ℝ, v < threshold - epsilon →
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset v cutoff < epsilon) ∧
            (∀ v : ℝ, threshold + epsilon < v →
              1 - epsilon < cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v cutoff) := by
  have hgeometry :=
    theorem3_ranked_denseWindow_or_large_gap_with_large_subset_eventually
      hbeta.1 hepsilon
      (fun C : ℕ => Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta))
  have hdense := theorem3_dense_branch_attenuation_eventually
    noiseLaw hbeta hvariance hepsilon
  have hgap_low := theorem3_ranked_largeGap_low_endpoint_eventually
    noiseLaw hbeta hvariance hepsilon
  have hgap_high :=
    theorem3_ranked_largeGap_high_endpoint_uniform_eventually_of_mean_div_log
      noiseLaw hbeta.1 hmean hepsilon
  filter_upwards [hgeometry, hdense, hgap_low, hgap_high,
    eventually_gt_atTop 1] with C hgeometry_C hdense_C hgap_low_C hgap_high_C
      hC_one_lt cutoff
  rcases hgeometry_C cutoff with hdense_geometry | hgap_geometry
  · rcases hdense_geometry with ⟨start, hterminal, hdense_window, hlarge⟩
    have hearly_lt :
        theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta) < C :=
      theorem3EarlyPrefixRank_lt_coalitionSize hC_one_lt
        (theorem3EarlyCutoffExponent_lt_one hbeta.1)
    have hblock_le :
        theorem3DenseGapBlockCount C
            (theorem3DenseClusterExponent beta)
            (theorem3EarlyCutoffExponent beta) *
          theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) ≤
          theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta) :=
      theorem3DenseGapBlockCount_mul_denseWindowCount_le_earlyPrefixRank C
        (theorem3DenseClusterExponent beta)
        (theorem3EarlyCutoffExponent beta)
    have hterminal_C :
        start + theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) ≤ C :=
      hterminal.trans (hblock_le.trans hearly_lt.le)
    exact hdense_C cutoff start hterminal_C hdense_window hlarge
  · rcases hgap_geometry with ⟨hgap, hlarge⟩
    let threshold : ℝ := theorem3RankedCutoffNat C cutoff
      (theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta)) -
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
        Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)
    refine ⟨threshold,
      theorem3RankedSuffix C cutoff
        (theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta)),
      hlarge, ?_, ?_⟩
    · intro v hv
      have hmono :
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem3RankedSuffix C cutoff
                (theorem3EarlyPrefixRank C
                  (theorem3EarlyCutoffExponent beta))) v cutoff ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (theorem3RankedSuffix C cutoff
                (theorem3EarlyPrefixRank C
                  (theorem3EarlyCutoffExponent beta)))
              (threshold - epsilon) cutoff :=
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := theorem3RankedSuffix C cutoff
            (theorem3EarlyPrefixRank C
              (theorem3EarlyCutoffExponent beta)))
          (cutoff := cutoff) (le_of_lt hv)
      exact lt_of_le_of_lt hmono
        (by simpa [threshold] using (hgap_low_C cutoff))
    · intro v hv
      have hthreshold_le_v : threshold ≤ v := by
        have hthreshold_le : threshold ≤ threshold + epsilon :=
          le_add_of_nonneg_right hepsilon.le
        exact hthreshold_le.trans (le_of_lt hv)
      have hmono :
          cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) threshold cutoff ≤
            cutoffAffordanceProbability
              (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
              (Finset.univ : Finset (Fin (C + 1))) v cutoff :=
        cutoffAffordanceProbability_mono_value
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (active := (Finset.univ : Finset (Fin (C + 1))))
          (cutoff := cutoff) hthreshold_le_v
      exact lt_of_lt_of_le
        (by simpa [threshold] using (hgap_high_C cutoff hgap)) hmono

/-- The fully discharged T3 attenuation theorem for arbitrary finite cutoff
vectors.  The iid expected-maximum logarithmic estimate used by the
large-gap branch is a derived theorem of the source beta-max variance
condition, not an additional paper-facing premise. -/
theorem theorem3_attenuation_in_coalitions_of_iid_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        ∃ threshold : ℝ, ∃ largeSubset : Finset (Fin (C + 1)),
          CoalitionLargeSubset
              (Finset.univ : Finset (Fin (C + 1))) largeSubset epsilon ∧
            (∀ v : ℝ, v < threshold - epsilon →
              cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                largeSubset v cutoff < epsilon) ∧
            (∀ v : ℝ, threshold + epsilon < v →
              1 - epsilon < cutoffAffordanceProbability
                (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
                (Finset.univ : Finset (Fin (C + 1))) v cutoff) := by
  exact theorem3_attenuation_in_coalitions_of_iid_beta_of_expectedMaximum_div_log
    noiseLaw hbeta hvariance
    (theorem3_iidExpectedMaximum_div_log_tendsto_zero_of_beta
      noiseLaw hbeta hvariance)
    hepsilon

end

end PG24NoisyMatchingMarkets
