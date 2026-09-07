import PG24NoisyMatchingMarkets.Theorem3ChebyshevRates
import PG24NoisyMatchingMarkets.Theorem3DenseBlockIndex
import PG24NoisyMatchingMarkets.Theorem3DenseLowRate
import Mathlib.Tactic

/-!
# PG24 Theorem 3 rounded dense-block low Chebyshev bound

This module combines the source beta-max variance condition with the exact
ceiling-rounded dense block and the full-coalition factor from the corrected
finite union bound.  It proves a rate for the actual maximum-deviation
probability, without assuming a low endpoint or an attenuation conclusion.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
At any fixed positive deviation, the maximum on the exact rounded dense block
concentrates.  This is the unscaled Chebyshev bridge used to make the finite
geometric reduction applicable.
-/
theorem theorem3_roundedDenseBlock_fixedDeviation_tendsto_zero
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) - 1 + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) - 1)) epsilon)
      atTop (nhds 0) := by
  rcases theorem3DenseClusterBlockIndex_properties hbeta.1 with
    ⟨hblock_atTop, _⟩
  have hmem_at_block := hblock_atTop.eventually hvariance.1
  have hvariance_at_block := hblock_atTop.eventually hvariance.2
  have hvariance_zero :=
    betaMaxConcentratingVariance.tendsto_zero_of_variance_bound
      hbeta hvariance.2
  have hupper_zero : Tendsto
      (fun C : ℕ =>
        maxVariance (theorem3DenseWindowCount C
          (theorem3DenseClusterExponent beta) - 1) / epsilon ^ 2)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (hvariance_zero.comp hblock_atTop).mul_const ((epsilon ^ 2)⁻¹)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero ?_ ?_
  · filter_upwards with C
    exact measureReal_nonneg
  · filter_upwards [hmem_at_block, hvariance_at_block] with C hmem hvariance_bound
    exact (theorem3_iidMaximum_deviation_le_variance_div_sq noiseLaw
      (theorem3DenseWindowCount C
        (theorem3DenseClusterExponent beta) - 1) hmem hepsilon).trans
      (div_le_div_of_nonneg_right hvariance_bound (sq_nonneg epsilon))

/--
The full-coalition factor times the corrected block-to-single-draw bound for
the exact rounded dense block tends to zero at every fixed positive deviation.
-/
theorem theorem3_roundedDenseBlock_unionBoundDeviation_tendsto_zero
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    Tendsto
      (fun C : ℕ =>
        (((C + 1 : ℕ) : ℝ) *
          (2 *
            AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin
                (theorem3DenseWindowCount C
                  (theorem3DenseClusterExponent beta) - 1 + 1) => noiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (theorem3DenseWindowCount C
                  (theorem3DenseClusterExponent beta) - 1))
              epsilon /
              (theorem3DenseWindowCount C
                (theorem3DenseClusterExponent beta) : ℝ))))
      atTop (nhds 0) := by
  rcases hbeta with ⟨hbeta_pos, K, N, hK_nonneg, hK_bound⟩
  let exponent : ℝ := theorem3DenseClusterExponent beta
  let m : ℕ → ℕ := fun C => theorem3DenseWindowCount C exponent
  rcases theorem3DenseClusterBlockIndex_properties hbeta_pos with
    ⟨hblock_atTop, hblock_lower⟩
  have hmem_at_block := hblock_atTop.eventually hvariance.1
  have hvariance_at_block := hblock_atTop.eventually hvariance.2
  have hN_at_block := hblock_atTop.eventually_ge_atTop N
  have hrate_zero : Tendsto
      (fun C : ℕ =>
        (2 * K / epsilon ^ 2) *
          ((((C + 1 : ℕ) : ℝ) * Real.rpow (m C : ℝ) (-beta)) /
            (m C : ℝ)))
      atTop (nhds 0) := by
    simpa [m, exponent] using
      (theorem3DenseCluster_unionBoundRate_tendsto_zero hbeta_pos).const_mul
        (2 * K / epsilon ^ 2)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hrate_zero ?_ ?_
  · filter_upwards with C
    have hdev_nonneg :
        0 ≤ AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (m C - 1 + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (m C - 1)) epsilon :=
      measureReal_nonneg
    exact mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hdev_nonneg) (Nat.cast_nonneg _))
  · filter_upwards [hmem_at_block, hvariance_at_block, hN_at_block,
      eventually_gt_atTop 0] with C hmem hvariance_bound hN hC_pos
    have hC_real_pos : 0 < (C : ℝ) := by
      exact_mod_cast hC_pos
    have hm_pos_nat : 0 < m C := by
      dsimp [m]
      exact theorem3DenseWindowCount_pos hC_pos
    have hm_pos : 0 < (m C : ℝ) := by
      exact_mod_cast hm_pos_nat
    have hsize : (m C - 1) + 1 = m C := by
      dsimp [m]
      exact theorem3DenseWindowCount_sub_one_add_one hC_pos
    have hvariance_K :
        maxVariance (m C - 1) ≤
          K * Real.rpow (m C : ℝ) (-beta) := by
      calc
        maxVariance (m C - 1) ≤
            K * Real.rpow (((m C - 1 + 1 : ℕ) : ℝ)) (-beta) :=
          hK_bound (m C - 1) hN
        _ = K * Real.rpow (m C : ℝ) (-beta) := by rw [hsize]
    have hdeviation_le :
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (m C - 1 + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (m C - 1)) epsilon ≤
          K * Real.rpow (m C : ℝ) (-beta) / epsilon ^ 2 := by
      calc
        AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (m C - 1 + 1) => noiseLaw))
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
              (m C - 1)) epsilon ≤
            ProbabilityTheory.variance
              (fun sample : Fin (m C - 1 + 1) → ℝ =>
                AppliedModelingLib.Probability.upperOrderStatistic sample
                  (AppliedModelingLib.Probability.topSampleRank
                    (n := m C - 1 + 1)))
              (Measure.pi (fun _ : Fin (m C - 1 + 1) => noiseLaw)) /
              epsilon ^ 2 :=
          theorem3_iidMaximum_deviation_le_variance_div_sq
            noiseLaw (m C - 1) hmem hepsilon
        _ ≤ maxVariance (m C - 1) / epsilon ^ 2 :=
          div_le_div_of_nonneg_right hvariance_bound (sq_nonneg epsilon)
        _ ≤ K * Real.rpow (m C : ℝ) (-beta) / epsilon ^ 2 :=
          div_le_div_of_nonneg_right hvariance_K (sq_nonneg epsilon)
    have hfactor_nonneg :
        0 ≤ (((C + 1 : ℕ) : ℝ) * (2 / (m C : ℝ))) := by
      exact mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (by norm_num) hm_pos.le)
    have hscaled := mul_le_mul_of_nonneg_left hdeviation_le hfactor_nonneg
    have hscaled_bound :
        (((C + 1 : ℕ) : ℝ) *
          (2 *
            AppliedModelingLib.Probability.topOrderDeviationProbability
              (Measure.pi (fun _ : Fin (m C - 1 + 1) => noiseLaw))
              (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (m C - 1)) epsilon / (m C : ℝ))) ≤
          (2 * K / epsilon ^ 2) *
            ((((C + 1 : ℕ) : ℝ) * Real.rpow (m C : ℝ) (-beta)) /
              (m C : ℝ)) := by
      convert hscaled using 1 <;> ring
    simpa [m, exponent] using hscaled_bound

end

end PG24NoisyMatchingMarkets
