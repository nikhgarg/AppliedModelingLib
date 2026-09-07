import PG24NoisyMatchingMarkets.Theorem3ChebyshevRates
import PG24NoisyMatchingMarkets.Theorem3DenseBlockIndex

/-!
# PG24 Theorem 3 rounded dense-block concentration

This specializes the generic iid maximum-block Chebyshev rate to the exact
ceiling-rounded dense block used by the canonical cutoff geometry.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The maximum on the exact rounded dense block concentrates at the
dense-window scale under the paper's beta-max variance condition. -/
theorem theorem3_iidMaximum_roundedDenseBlock_deviation_tendsto_zero
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin
            (theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) - 1 + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
            (theorem3DenseWindowCount C
              (theorem3DenseClusterExponent beta) - 1))
          (Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)))
      atTop (nhds 0) := by
  rcases theorem3DenseClusterBlockIndex_properties hbeta.1 with
    ⟨hblock_atTop, hblock_lower⟩
  exact theorem3_iidMaximum_denseBlock_deviation_tendsto_zero_of_beta
    noiseLaw hbeta hvariance
    (fun C : ℕ => theorem3DenseWindowCount C
      (theorem3DenseClusterExponent beta) - 1)
    hblock_atTop hblock_lower

/-- The rounded dense-block deviation probability is eventually below every
fixed positive tolerance. -/
theorem theorem3_iidMaximum_roundedDenseBlock_deviation_eventually_lt
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin
          (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) - 1 + 1) => noiseLaw))
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
          (theorem3DenseWindowCount C
            (theorem3DenseClusterExponent beta) - 1))
        (Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)) < epsilon :=
  theorem3_iidMaximum_roundedDenseBlock_deviation_tendsto_zero
    noiseLaw hbeta hvariance
    (isOpen_Iio.mem_nhds hepsilon)

end

end PG24NoisyMatchingMarkets
