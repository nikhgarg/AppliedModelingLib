import PG24NoisyMatchingMarkets.Theorem3LargeGapChebyshev
import PG24NoisyMatchingMarkets.Theorem3MaximumTailBridge
import PG24NoisyMatchingMarkets.Theorem3RankedDenseProbability

/-!
# PG24 Theorem 3 large-gap low endpoint

The low side of the large-gap branch uses the maximum over the full coalition.
The corrected finite geometric argument turns that maximum crossing bound into
an affordability bound for the semantic ranked suffix.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- A subset with no more than `m` colleges loses no factor beyond two when a
maximum-of-`m` crossing probability is converted to its union-bound form. -/
theorem theorem3_card_mul_two_div_blockCrossing_le_two
    {College : Type*} [DecidableEq College]
    (active : Finset College) {m : ℕ} {crossing : ℝ}
    (hm : 0 < m) (hcard : active.card ≤ m) (hcrossing_nonneg : 0 ≤ crossing) :
    (active.card : ℝ) * (2 * crossing / (m : ℝ)) ≤ 2 * crossing := by
  have hm_real_pos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hratio : (active.card : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm_real_pos]
    exact_mod_cast hcard
  calc
    (active.card : ℝ) * (2 * crossing / (m : ℝ)) =
        ((active.card : ℝ) / (m : ℝ)) * (2 * crossing) := by
      field_simp [ne_of_gt hm_real_pos]
    _ ≤ 1 * (2 * crossing) :=
      mul_le_mul_of_nonneg_right hratio (by positivity)
    _ = 2 * crossing := by ring

/-- At the threshold minus epsilon selected by the large-gap branch, the
semantic high-ranked suffix has affordability probability below epsilon. -/
theorem theorem3_ranked_largeGap_low_endpoint_eventually
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedSuffix C cutoff
            (theorem3EarlyPrefixRank C
              (theorem3EarlyCutoffExponent beta)))
          (theorem3RankedCutoffNat C cutoff
              (theorem3EarlyPrefixRank C
                (theorem3EarlyCutoffExponent beta)) -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C -
            Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta) - epsilon)
          cutoff < epsilon := by
  have htol_pos : 0 < min (epsilon / 2) (1 / 2 : ℝ) := by
    exact lt_min (by linarith) (by norm_num)
  have hdeviation_small :=
    theorem3_iidMaximum_fullBlock_gapDeviation_eventually_lt
      noiseLaw hbeta hvariance htol_pos
  filter_upwards [hdeviation_small, eventually_gt_atTop 1] with
    C hdeviation_small_C hC_one_lt cutoff
  let rank : ℕ := theorem3EarlyPrefixRank C
    (theorem3EarlyCutoffExponent beta)
  let mean : ℝ := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
    (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C
  let displacement : ℝ := Real.rpow (C : ℝ)
    (theorem3GapDisplacementExponent beta)
  let value : ℝ := theorem3RankedCutoffNat C cutoff rank - mean -
    displacement - epsilon
  let crossing : ℝ := 1 -
    (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
      (theorem3RankedCutoffNat C cutoff rank - value)) ^ (C + 1)
  have hrank_le : rank ≤ C :=
    Nat.le_of_lt (theorem3EarlyPrefixRank_lt_coalitionSize hC_one_lt
      (theorem3EarlyCutoffExponent_lt_one hbeta.1))
  have hdisplacement_pos : 0 < displacement := by
    dsimp [displacement]
    exact Real.rpow_pos_of_pos
      (by exact_mod_cast (show 0 < C by omega)) _
  have hseparation : mean + displacement ≤
      theorem3RankedCutoffNat C cutoff rank - value := by
    dsimp [value]
    linarith
  have hcrossing_le_deviation := theorem3_iidMaximum_upper_crossing_le_deviation
    noiseLaw C (center := mean) (deviation := displacement)
    (threshold := theorem3RankedCutoffNat C cutoff rank - value) hseparation
  have hcrossing_le : crossing ≤
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) mean displacement := by
    simpa [crossing] using hcrossing_le_deviation
  have hcrossing_nonneg : 0 ≤ crossing := by
    have htop_nonneg : 0 ≤
        AppliedModelingLib.Probability.topOrderCrossingProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedCutoffNat C cutoff rank - value) := by
      unfold AppliedModelingLib.Probability.topOrderCrossingProbability
      exact measureReal_nonneg
    have hcrossing_eq : crossing =
        AppliedModelingLib.Probability.topOrderCrossingProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedCutoffNat C cutoff rank - value) := by
      unfold crossing
      rw [AppliedModelingLib.Probability.topOrderCrossingProbability_iidProduct_eq_one_sub_lowerCDFMass_pow]
    rw [hcrossing_eq]
    exact htop_nonneg
  have hcrossing_le_half : crossing ≤ 1 / 2 := by
    exact (show crossing < 1 / 2 from calc
      crossing ≤
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) mean displacement :=
        hcrossing_le
      _ < min (epsilon / 2) (1 / 2 : ℝ) := by
        simpa [mean, displacement] using hdeviation_small_C
      _ ≤ 1 / 2 := min_le_right _ _).le
  have hlow := theorem3_ranked_dense_low_affordance_le
    C rank cutoff noiseLaw value crossing (m := C + 1) hrank_le
    (Nat.succ_pos C) (by simp [crossing]) hcrossing_le_half
  have hsuffix_card : (theorem3RankedSuffix C cutoff rank).card ≤ C + 1 := by
    calc
      (theorem3RankedSuffix C cutoff rank).card ≤
          (Finset.univ : Finset (Fin (C + 1))).card :=
        Finset.card_le_card (theorem3RankedSuffix_subset C cutoff rank)
      _ = C + 1 := by simp
  have htwo_crossing :
      (theorem3RankedSuffix C cutoff rank).card *
          (2 * crossing / ((C + 1 : ℕ) : ℝ)) ≤ 2 * crossing :=
    theorem3_card_mul_two_div_blockCrossing_le_two
      (theorem3RankedSuffix C cutoff rank) (Nat.succ_pos C)
      hsuffix_card hcrossing_nonneg
  have hcrossing_small : 2 * crossing < epsilon := by
    calc
      2 * crossing ≤ 2 *
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (C + 1) => noiseLaw)) mean displacement :=
        mul_le_mul_of_nonneg_left hcrossing_le (by norm_num)
      _ < 2 * (epsilon / 2) :=
        mul_lt_mul_of_pos_left
          (lt_of_lt_of_le
            (by simpa [mean, displacement] using hdeviation_small_C)
            (min_le_left _ _))
          (by norm_num)
      _ = epsilon := by ring
  have hresult :
      cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedSuffix C cutoff rank) value cutoff < epsilon :=
    lt_of_le_of_lt (hlow.trans htwo_crossing) hcrossing_small
  simpa [rank, mean, displacement, value] using hresult

end

end PG24NoisyMatchingMarkets
