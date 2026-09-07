import PG24NoisyMatchingMarkets.Theorem3LargeGapAsymptotics
import PG24NoisyMatchingMarkets.Theorem3LargeGapScale
import PG24NoisyMatchingMarkets.Theorem3RankedLargeGapProbability
import PG24NoisyMatchingMarkets.Assumptions

/-!
# PG24 Theorem 3 large-gap high endpoint

This module closes the high-affordance endpoint of the large-gap branch.
The finite ranked-gap inequality is transported to original college indices,
and the threshold algebra is discharged at the ranked early-prefix endpoint.
The only analytic input beyond the beta variance condition is the explicit
iid dyadic maximum bridge required by the source's logarithmic maximum lemma.
-/

open Filter Topology MeasureTheory Asymptotics

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
The large-gap high endpoint in the quantifier order required by the finite
ranked geometry: after a cutoff-independent scalar threshold is reached,
every cutoff vector satisfying that finite ranked gap has high full-coalition
affordance at the source threshold.  The expected-maximum hypothesis is the
proved analytic `o(log C)` conclusion, not an affordability assumption.
-/
theorem theorem3_ranked_largeGap_high_endpoint_uniform_eventually_of_mean_div_log
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {beta epsilon : ℝ}
    (hbeta : 0 < beta)
    (hmean : Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C /
          Real.log (C : ℝ))
      atTop (nhds 0))
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        theorem3RankedCutoffNat C cutoff 0 +
            (theorem3DenseGapBlockCount C
              (theorem3DenseClusterExponent beta)
              (theorem3EarlyCutoffExponent beta) : ℝ) *
              Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) <
          theorem3RankedCutoffNat C cutoff
            (theorem3EarlyPrefixRank C
              (theorem3EarlyCutoffExponent beta)) →
        1 - epsilon <
          cutoffAffordanceProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
            (Finset.univ : Finset (Fin (C + 1)))
            (theorem3RankedCutoffNat C cutoff
                (theorem3EarlyPrefixRank C
                  (theorem3EarlyCutoffExponent beta)) -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
              Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta))
            cutoff := by
  let rank : ℕ → ℕ := fun C =>
    theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta)
  let gapLower : ℕ → ℝ := fun C =>
    (theorem3DenseGapBlockCount C
      (theorem3DenseClusterExponent beta)
      (theorem3EarlyCutoffExponent beta) : ℝ) *
      Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)
  let mean : ℕ → ℝ :=
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
  let displacement : ℕ → ℝ := fun C =>
    Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)
  let slack : ℕ → ℝ := fun C => mean C + displacement C
  let value : ∀ C : ℕ, (Fin (C + 1) → ℝ) → ℝ := fun C cutoff =>
    theorem3RankedCutoffNat C cutoff (rank C) - mean C - displacement C
  have hslack_little : slack =o[atTop] gapLower := by
    simpa [slack, mean, displacement, gapLower] using
      (theorem3_mean_add_gapDisplacement_isLittleO_roundedLargeGapScale
        hbeta hmean)
  have hgap_toTop : Tendsto gapLower atTop atTop := by
    simpa [gapLower] using
      (theorem3DenseGapBlockCount_mul_denseWindowScale_tendsto_atTop hbeta)
  have hslack_sub_gap :
      Tendsto (fun C : ℕ => slack C - gapLower C) atTop atBot :=
    theorem3_slack_sub_gap_tendsto_atBot_of_isLittleO hgap_toTop hslack_little
  rcases Filter.eventually_atBot.1
      (AppliedModelingLib.Probability.eventually_one_sub_lt_upperTailMass_atBot
        noiseLaw hepsilon) with ⟨B, htail_B⟩
  have hscalar : ∀ᶠ C : ℕ in atTop, slack C - gapLower C ≤ B :=
    tendsto_atBot.mp hslack_sub_gap B
  filter_upwards [hscalar] with C hscalar_C cutoff hlarge_gap
  let lowCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  let highCollege : Fin (C + 1) := theorem3RankedCollege C cutoff
    ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
  have hsemantic_gap :
      gapLower C < cutoff highCollege - cutoff lowCollege := by
    dsimp [highCollege, lowCollege]
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff (rank C),
      ← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff 0]
    have hgap' : theorem3RankedCutoffNat C cutoff 0 + gapLower C <
        theorem3RankedCutoffNat C cutoff (rank C) := by
      simpa [rank, gapLower] using hlarge_gap
    linarith
  have hvalue_below_high_rank :
      cutoff highCollege - value C cutoff ≤ slack C := by
    dsimp [highCollege]
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C cutoff (rank C)]
    dsimp [value, slack]
    linarith
  have hlow_cutoff_sub_value :
      cutoff lowCollege - value C cutoff ≤ B := by
    calc
      cutoff lowCollege - value C cutoff ≤ slack C - gapLower C := by
        linarith
      _ ≤ B := hscalar_C
  have hsingle_high :
      1 - epsilon <
        singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C cutoff) cutoff lowCollege := by
    rw [singleCollegeAffordanceProbability,
      AppliedModelingLib.Matching.singleCutoffCrossingProbability_iidProduct_eq_upperTailMass]
    exact htail_B _ hlow_cutoff_sub_value
  have hsingle_le :
      singleCollegeAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (value C cutoff) cutoff lowCollege ≤
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1)))
          (value C cutoff) cutoff := by
    simpa only [singleCollegeAffordanceProbability,
      cutoffAffordanceProbability] using
      (AppliedModelingLib.Matching.singleCutoffCrossingProbability_le_cutoffCrossingProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (Finset.univ : Finset (Fin (C + 1))) (by simp)
        (value C cutoff) cutoff)
  simpa [rank, mean, displacement, value] using
    (lt_of_lt_of_le hsingle_high hsingle_le)

/--
For a cutoff sequence in the actual large-gap branch, the source threshold
at the early ranked cutoff minus the expected iid maximum and the shrinking
gap displacement has full-coalition affordance tending to one.

The geometric premise is exactly the finite large-gap alternative on the
canonical cutoff ranking.  It is not a conclusion-shaped affordability or
cutoff-tail premise.  `hdyadic` is the explicit iid two-block maximum
comparison needed to derive the source's `o(log C)` maximum bound.
-/
theorem theorem3_ranked_largeGap_high_endpoint_eventually
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hdyadic : Theorem3MaximumDyadicVarianceBridge
      (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
      maxVariance)
    {cutoff : ∀ C : ℕ, Fin (C + 1) → ℝ}
    (hlarge_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 +
          (theorem3DenseGapBlockCount C
            (theorem3DenseClusterExponent beta)
            (theorem3EarlyCutoffExponent beta) : ℝ) *
            Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) <
        theorem3RankedCutoffNat C (cutoff C)
          (theorem3EarlyPrefixRank C
            (theorem3EarlyCutoffExponent beta)))
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      1 - epsilon <
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedCutoffNat C (cutoff C)
              (theorem3EarlyPrefixRank C
                (theorem3EarlyCutoffExponent beta)) -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
            Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta))
          (cutoff C) := by
  let rank : ℕ → ℕ := fun C =>
    theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta)
  let gapLower : ℕ → ℝ := fun C =>
    (theorem3DenseGapBlockCount C
      (theorem3DenseClusterExponent beta)
      (theorem3EarlyCutoffExponent beta) : ℝ) *
      Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)
  let mean : ℕ → ℝ :=
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
      (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
  let displacement : ℕ → ℝ := fun C =>
    Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)
  let slack : ℕ → ℝ := fun C => mean C + displacement C
  let value : ℕ → ℝ := fun C =>
    theorem3RankedCutoffNat C (cutoff C) (rank C) - mean C - displacement C
  have hmean_log : Tendsto
      (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0) := by
    dsimp [mean]
    exact theorem3_expectedMaximum_div_log_tendsto_zero_of_beta_variance_bound
      hbeta hvariance.2 hdyadic
  have hslack_little : slack =o[atTop] gapLower := by
    simpa [slack, mean, displacement, gapLower] using
      (theorem3_mean_add_gapDisplacement_isLittleO_roundedLargeGapScale
        hbeta.1 hmean_log)
  have hgap_toTop : Tendsto gapLower atTop atTop := by
    simpa [gapLower] using
      (theorem3DenseGapBlockCount_mul_denseWindowScale_tendsto_atTop hbeta.1)
  have hrank_gap : ∀ᶠ C : ℕ in atTop,
      theorem3RankedCutoffNat C (cutoff C) 0 + gapLower C <
        theorem3RankedCutoffNat C (cutoff C) (rank C) := by
    simpa [rank, gapLower] using hlarge_gap
  have hsemantic_gap : ∀ᶠ C : ℕ in atTop,
      gapLower C <
        cutoff C (theorem3RankedCollege C (cutoff C)
          ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) -
        cutoff C (theorem3RankedCollege C (cutoff C)
          ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) :=
    theorem3_ranked_cutoff_gap_of_ranked_gap hrank_gap
  have hvalue_below_high_rank : ∀ᶠ C : ℕ in atTop,
      cutoff C (theorem3RankedCollege C (cutoff C)
        ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩) -
        value C ≤ slack C := by
    filter_upwards with C
    rw [← theorem3RankedCutoffNat_eq_cutoff_rankedCollege C (cutoff C) (rank C)]
    dsimp [value, slack]
    linarith
  have hresult :=
    theorem3_fullAffordance_eventually_one_sub_lt_of_cutoff_gap_of_isLittleO
      noiseLaw
      (fun C => theorem3RankedCollege C (cutoff C)
        ⟨min 0 C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
      (fun C => theorem3RankedCollege C (cutoff C)
        ⟨min (rank C) C, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩)
      hsemantic_gap hvalue_below_high_rank hgap_toTop hslack_little epsilon hepsilon
  simpa [rank, mean, displacement, value] using hresult

end

end PG24NoisyMatchingMarkets
