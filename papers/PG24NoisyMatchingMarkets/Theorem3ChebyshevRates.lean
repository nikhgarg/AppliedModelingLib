import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem3DenseGapExponents
import Mathlib.Tactic

/-!
# PG24 Theorem 3 iid maximum-block Chebyshev rates

This module turns the paper's beta-max variance hypothesis for iid maximum
order statistics into the polynomial deviation estimates used by the
dense-cluster branch.  The input block size is explicit: no cutoff ordering,
coalition conclusion, or probability endpoint estimate is assumed here.
-/

open Filter MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
Chebyshev for the maximum of an iid block, written with the same `n + 1`
indexing as the source beta-max variance premise.
-/
theorem theorem3_iidMaximum_deviation_le_variance_div_sq
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (n : ℕ)
    (hmem :
      MemLp
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)))
    {deviation : ℝ} (hdeviation_pos : 0 < deviation) :
    AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) n)
        deviation ≤
      ProbabilityTheory.variance
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) / deviation ^ 2 := by
  simpa [AppliedModelingLib.Probability.expectedTopOrderStatisticSeq] using
    AppliedModelingLib.Probability.topOrderDeviationProbability_le_variance_div_sq
      (μ := Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) hmem hdeviation_pos

/--
Algebra for a beta-max variance rate divided by a power-scale deviation.
The exponent on the right is the one which must be negative for the
corresponding Chebyshev error to vanish.
-/
theorem theorem3_powerVariance_div_powerDeviation_sq
    {C K beta blockExponent deviationExponent : ℝ}
    (hC_pos : 0 < C) :
    (K * Real.rpow C (-beta * blockExponent)) /
        (Real.rpow C deviationExponent) ^ 2 =
      K * Real.rpow C
        (-beta * blockExponent - 2 * deviationExponent) := by
  have hsq : (Real.rpow C deviationExponent) ^ 2 =
      Real.rpow C (deviationExponent + deviationExponent) := by
    calc
      (Real.rpow C deviationExponent) ^ 2 =
          Real.rpow C deviationExponent * Real.rpow C deviationExponent := by
            ring
      _ = Real.rpow C (deviationExponent + deviationExponent) :=
        (Real.rpow_add hC_pos deviationExponent deviationExponent).symm
  rw [hsq]
  calc
    (K * Real.rpow C (-beta * blockExponent)) /
          Real.rpow C (deviationExponent + deviationExponent) =
        K * (Real.rpow C (-beta * blockExponent) /
          Real.rpow C (deviationExponent + deviationExponent)) := by
            ring
    _ = K * Real.rpow C
          ((-beta * blockExponent) -
            (deviationExponent + deviationExponent)) := by
          exact congrArg (fun x : ℝ => K * x)
            (Real.rpow_sub hC_pos (-beta * blockExponent)
              (deviationExponent + deviationExponent)).symm
    _ = K * Real.rpow C
          (-beta * blockExponent - 2 * deviationExponent) := by ring

/--
Reindex the source iid beta-max variance premise along arbitrary growing
maximum blocks.  If a block has at least `C ^ blockExponent` draws, then its
Chebyshev deviation at radius `C ^ deviationExponent` has the stated rate.

`blockIndex C` denotes one less than the number of iid draws, matching the
source convention that its `n`th law is on `Fin (n + 1)`.
-/
theorem theorem3_iidMaximum_powerDeviation_eventually_le_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta blockExponent deviationExponent : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (blockIndex : ℕ → ℕ)
    (hblock_atTop : Tendsto blockIndex atTop atTop)
    (hblock_lower : ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) blockExponent ≤ ((blockIndex C + 1 : ℕ) : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ C : ℕ in atTop,
        AppliedModelingLib.Probability.topOrderDeviationProbability
            (Measure.pi (fun _ : Fin (blockIndex C + 1) => noiseLaw))
            (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
              (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
              (blockIndex C))
            (Real.rpow (C : ℝ) deviationExponent) ≤
          K * Real.rpow (C : ℝ)
            (-beta * blockExponent - 2 * deviationExponent) := by
  rcases hbeta with ⟨hbeta_pos, K, N, hK_nonneg, hK_bound⟩
  refine ⟨K, hK_nonneg, ?_⟩
  have hmem_at_block := hblock_atTop.eventually hvariance.1
  have hvariance_at_block := hblock_atTop.eventually hvariance.2
  have hN_at_block := hblock_atTop.eventually_ge_atTop N
  filter_upwards [hmem_at_block, hvariance_at_block, hN_at_block,
    hblock_lower, eventually_gt_atTop 0] with C hmem hvariance_bound hN
      hblock_lower_C hC_pos
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hdeviation_pos : 0 < Real.rpow (C : ℝ) deviationExponent :=
    Real.rpow_pos_of_pos hC_real_pos _
  have hchebyshev := theorem3_iidMaximum_deviation_le_variance_div_sq
    noiseLaw (blockIndex C) hmem hdeviation_pos
  have hbeta_bound :
      maxVariance (blockIndex C) ≤
        K * Real.rpow (((blockIndex C + 1 : ℕ) : ℝ)) (-beta) :=
    hK_bound (blockIndex C) hN
  have hblock_base_pos : 0 < Real.rpow (C : ℝ) blockExponent :=
    Real.rpow_pos_of_pos hC_real_pos _
  have hvariance_power :
      Real.rpow (((blockIndex C + 1 : ℕ) : ℝ)) (-beta) ≤
        Real.rpow (C : ℝ) (-beta * blockExponent) := by
    calc
      Real.rpow (((blockIndex C + 1 : ℕ) : ℝ)) (-beta) ≤
          Real.rpow (Real.rpow (C : ℝ) blockExponent) (-beta) :=
        Real.rpow_le_rpow_of_nonpos hblock_base_pos hblock_lower_C (by linarith)
      _ = Real.rpow (C : ℝ) (blockExponent * (-beta)) := by
        exact (Real.rpow_mul (le_of_lt hC_real_pos)
          blockExponent (-beta)).symm
      _ = Real.rpow (C : ℝ) (-beta * blockExponent) := by ring
  have hK_power :
      K * Real.rpow (((blockIndex C + 1 : ℕ) : ℝ)) (-beta) ≤
        K * Real.rpow (C : ℝ) (-beta * blockExponent) :=
    mul_le_mul_of_nonneg_left hvariance_power hK_nonneg
  have hdenom_nonneg : 0 ≤ (Real.rpow (C : ℝ) deviationExponent) ^ 2 :=
    sq_nonneg _
  calc
    AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (blockIndex C + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (blockIndex C))
          (Real.rpow (C : ℝ) deviationExponent) ≤
        ProbabilityTheory.variance
          (fun sample : Fin (blockIndex C + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank
                (n := blockIndex C + 1)))
          (Measure.pi (fun _ : Fin (blockIndex C + 1) => noiseLaw)) /
          (Real.rpow (C : ℝ) deviationExponent) ^ 2 := hchebyshev
    _ ≤ maxVariance (blockIndex C) /
          (Real.rpow (C : ℝ) deviationExponent) ^ 2 :=
      div_le_div_of_nonneg_right hvariance_bound hdenom_nonneg
    _ ≤ (K * Real.rpow (((blockIndex C + 1 : ℕ) : ℝ)) (-beta)) /
          (Real.rpow (C : ℝ) deviationExponent) ^ 2 :=
      div_le_div_of_nonneg_right hbeta_bound hdenom_nonneg
    _ ≤ (K * Real.rpow (C : ℝ) (-beta * blockExponent)) /
          (Real.rpow (C : ℝ) deviationExponent) ^ 2 :=
      div_le_div_of_nonneg_right hK_power hdenom_nonneg
    _ = K * Real.rpow (C : ℝ)
          (-beta * blockExponent - 2 * deviationExponent) :=
      theorem3_powerVariance_div_powerDeviation_sq hC_real_pos

/--
If the displayed power exponent is negative, the preceding iid maximum-block
deviation probability converges to zero.
-/
theorem theorem3_iidMaximum_powerDeviation_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta blockExponent deviationExponent : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (blockIndex : ℕ → ℕ)
    (hblock_atTop : Tendsto blockIndex atTop atTop)
    (hblock_lower : ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) blockExponent ≤ ((blockIndex C + 1 : ℕ) : ℝ))
    (hrate_neg : -beta * blockExponent - 2 * deviationExponent < 0) :
    Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (blockIndex C + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (blockIndex C))
          (Real.rpow (C : ℝ) deviationExponent))
      atTop (nhds 0) := by
  rcases theorem3_iidMaximum_powerDeviation_eventually_le_of_beta
    noiseLaw hbeta hvariance blockIndex hblock_atTop hblock_lower with
      ⟨K, hK_nonneg, hbound⟩
  have hrate_pos : 0 < -(-beta * blockExponent - 2 * deviationExponent) := by
    linarith
  have hpower_zero :
      Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ)
          (-beta * blockExponent - 2 * deviationExponent))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (tendsto_rpow_neg_atTop hrate_pos).comp tendsto_natCast_atTop_atTop
  have hupper_zero :
      Tendsto
        (fun C : ℕ => K * Real.rpow (C : ℝ)
          (-beta * blockExponent - 2 * deviationExponent))
        atTop (nhds 0) := by
    simpa using hpower_zero.const_mul K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
    hupper_zero ?_ hbound
  filter_upwards with C
  exact measureReal_nonneg

/--
The T3 dense-block choice has a negative Chebyshev exponent.  This is the
explicit numerical condition used by both dense endpoint routes; the low
endpoint has one additional inverse-block factor and hence the stronger
`theorem3DenseLowErrorExponent_neg` rate.
-/
theorem theorem3_denseBlock_chebyshev_exponents_neg {beta : ℝ}
    (hbeta : 0 < beta) :
    theorem3DenseHighErrorExponent beta < 0 ∧
      theorem3DenseLowErrorExponent beta < 0 := by
  exact ⟨theorem3DenseHighErrorExponent_neg hbeta,
    theorem3DenseLowErrorExponent_neg hbeta⟩

/--
The generic iid maximum-block rate specialized to T3's dense cluster and
dense-window exponents.
-/
theorem theorem3_iidMaximum_denseBlock_deviation_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (blockIndex : ℕ → ℕ)
    (hblock_atTop : Tendsto blockIndex atTop atTop)
    (hblock_lower : ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem3DenseClusterExponent beta) ≤
        ((blockIndex C + 1 : ℕ) : ℝ)) :
    Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (blockIndex C + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (blockIndex C))
          (Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)))
      atTop (nhds 0) := by
  apply theorem3_iidMaximum_powerDeviation_tendsto_zero_of_beta
    noiseLaw hbeta hvariance blockIndex hblock_atTop hblock_lower
  rw [show -beta * theorem3DenseClusterExponent beta -
      2 * theorem3DenseWindowExponent beta =
        theorem3DenseHighErrorExponent beta by
      unfold theorem3DenseHighErrorExponent
      ring]
  exact theorem3DenseHighErrorExponent_neg hbeta.1

end

end PG24NoisyMatchingMarkets
