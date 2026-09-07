import PG24NoisyMatchingMarkets.Theorem3DenseLowChebyshev
import PG24NoisyMatchingMarkets.Theorem3MaximumTailBridge
import PG24NoisyMatchingMarkets.Theorem3RankedDenseProbability

/-!
# PG24 Theorem 3 dense-branch low endpoint

This is the source low-endpoint calculation for the canonical ranked dense
route.  It combines the exact rounded iid block, the finite geometric
block-to-single-draw estimate, and the coalition union bound.  No endpoint
estimate is assumed as an input.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
At values a fixed positive margin below the dense-block centered threshold,
the affordance probability of every semantic ranked suffix tends to zero.

The proof uses the exact rounded dense block cardinality and is uniform in
the cutoff vector and the suffix start rank (subject only to being in range).
-/
theorem theorem3_ranked_dense_low_endpoint_eventually
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      ∀ (cutoff : Fin (C + 1) → ℝ) (start : ℕ), start ≤ C →
        cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedSuffix C cutoff start)
          (theorem3RankedCutoffNat C cutoff start -
            AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
              (theorem3DenseWindowCount C
                (theorem3DenseClusterExponent beta) - 1) - epsilon)
          cutoff < epsilon := by
  have hdeviation_zero :=
    theorem3_roundedDenseBlock_fixedDeviation_tendsto_zero
      noiseLaw hbeta hvariance hepsilon
  have hdeviation_half : ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin
          (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) - 1 + 1) => noiseLaw))
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
          (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) - 1)) epsilon < 1 / 2 :=
    hdeviation_zero (isOpen_Iio.mem_nhds (by norm_num))
  have hunion_zero :=
    theorem3_roundedDenseBlock_unionBoundDeviation_tendsto_zero
      noiseLaw hbeta hvariance hepsilon
  have hunion_small := hunion_zero (isOpen_Iio.mem_nhds hepsilon)
  filter_upwards [hdeviation_half, hunion_small,
    eventually_gt_atTop 0] with C hdeviation_half_C hunion_small_C hC_pos
      cutoff start hstart
  let m : ℕ := theorem3DenseWindowCount C
    (theorem3DenseClusterExponent beta)
  let mean : ℝ := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
    (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) (m - 1)
  let value : ℝ := theorem3RankedCutoffNat C cutoff start - mean - epsilon
  let crossing : ℝ := 1 -
    (AppliedModelingLib.Probability.lowerCDFMass noiseLaw (mean + epsilon)) ^ m
  have hm_pos_nat : 0 < m := by
    dsimp [m]
    exact theorem3DenseWindowCount_pos hC_pos
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast hm_pos_nat
  have hsize : (m - 1) + 1 = m := by
    dsimp [m]
    exact theorem3DenseWindowCount_sub_one_add_one hC_pos
  have hdeviation_half_m :
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (m - 1 + 1) => noiseLaw)) mean epsilon < 1 / 2 := by
    simpa [m, mean] using hdeviation_half_C
  have hunion_small_m :
      (((C + 1 : ℕ) : ℝ) *
        (2 *
          AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (m - 1 + 1) => noiseLaw)) mean epsilon /
            (m : ℝ))) < epsilon := by
    simpa [m, mean] using hunion_small_C
  have hcrossing_eq :
      crossing = 1 -
        (AppliedModelingLib.Probability.lowerCDFMass noiseLaw
          (theorem3RankedCutoffNat C cutoff start - value)) ^ m := by
    dsimp [crossing, value]
    congr 2
    ring
  have hcrossing_nonneg : 0 ≤ crossing := by
    dsimp [crossing]
    apply sub_nonneg.mpr
    exact pow_le_one₀
      (AppliedModelingLib.Probability.lowerCDFMass_nonneg noiseLaw _)
      (AppliedModelingLib.Probability.lowerCDFMass_le_one noiseLaw _)
  have hcrossing_deviation :
      crossing ≤
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (m - 1 + 1) => noiseLaw)) mean epsilon := by
    have hbridge := theorem3_iidMaximum_upper_crossing_le_deviation
      noiseLaw (m - 1) (center := mean) (deviation := epsilon)
      (threshold := mean + epsilon) (by linarith)
    simpa only [hsize, crossing] using hbridge
  have hcrossing_half : crossing ≤ 1 / 2 :=
    le_of_lt (lt_of_le_of_lt hcrossing_deviation hdeviation_half_m)
  have hsingle_factor_nonneg : 0 ≤ 2 * crossing / (m : ℝ) := by
    exact div_nonneg (mul_nonneg (by norm_num) hcrossing_nonneg) hm_pos.le
  have hsuffix_card_le :
      ((theorem3RankedSuffix C cutoff start).card : ℝ) ≤
        ((C + 1 : ℕ) : ℝ) := by
    have hcard_nat : (theorem3RankedSuffix C cutoff start).card ≤ C + 1 := by
      rw [theorem3RankedSuffix_card]
      omega
    exact_mod_cast hcard_nat
  have hscaled_crossing_le :
      (((C + 1 : ℕ) : ℝ) * (2 * crossing / (m : ℝ))) ≤
        (((C + 1 : ℕ) : ℝ) *
          (2 *
            AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (m - 1 + 1) => noiseLaw)) mean epsilon /
            (m : ℝ))) := by
    apply mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcrossing_deviation (by norm_num)) hm_pos.le)
    exact Nat.cast_nonneg _
  have hlow := theorem3_ranked_dense_low_affordance_le
    C start cutoff noiseLaw value crossing hstart hm_pos_nat hcrossing_eq hcrossing_half
  calc
    cutoffAffordanceProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (theorem3RankedSuffix C cutoff start) value cutoff ≤
        ((theorem3RankedSuffix C cutoff start).card : ℝ) *
          (2 * crossing / (m : ℝ)) := hlow
    _ ≤ ((C + 1 : ℕ) : ℝ) * (2 * crossing / (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hsuffix_card_le hsingle_factor_nonneg
    _ ≤ ((C + 1 : ℕ) : ℝ) *
          (2 *
            AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (m - 1 + 1) => noiseLaw)) mean epsilon /
            (m : ℝ)) := hscaled_crossing_le
    _ < epsilon := hunion_small_m

end

end PG24NoisyMatchingMarkets
