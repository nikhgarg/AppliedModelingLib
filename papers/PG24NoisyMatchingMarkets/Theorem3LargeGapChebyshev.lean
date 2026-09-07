import PG24NoisyMatchingMarkets.Theorem3ChebyshevRates

/-!
# PG24 Theorem 3 large-gap full-block concentration

The low side of the large-gap branch uses the maximum over the entire
coalition.  Its block size is exactly `C + 1`, so the beta-max Chebyshev rate
specializes without any rounding loss.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The full iid coalition maximum concentrates at the negative-power
large-gap displacement scale. -/
theorem theorem3_iidMaximum_fullBlock_gapDeviation_tendsto_zero
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    Tendsto
      (fun C : ℕ =>
        AppliedModelingLib.Probability.topOrderDeviationProbability
          (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
          (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
            (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C)
          (Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)))
      atTop (nhds 0) := by
  apply theorem3_iidMaximum_powerDeviation_tendsto_zero_of_beta
    noiseLaw (beta := beta) (blockExponent := 1)
    (deviationExponent := theorem3GapDisplacementExponent beta)
    hbeta hvariance (fun C : ℕ => C)
  · exact tendsto_id
  · filter_upwards with C
    calc
      Real.rpow (C : ℝ) (1 : ℝ) = (C : ℝ) := Real.rpow_one _
      _ ≤ ((C + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ C
  · rw [show -beta * (1 : ℝ) -
      2 * theorem3GapDisplacementExponent beta =
        theorem3GapLowErrorExponent beta by
      unfold theorem3GapLowErrorExponent
      ring]
    exact theorem3GapLowErrorExponent_neg hbeta.1

/-- The full-block large-gap deviation probability is eventually below every
positive tolerance. -/
theorem theorem3_iidMaximum_fullBlock_gapDeviation_eventually_lt
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta epsilon : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      AppliedModelingLib.Probability.topOrderDeviationProbability
        (Measure.pi (fun _ : Fin (C + 1) => noiseLaw))
        (AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw)) C)
        (Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)) < epsilon :=
  theorem3_iidMaximum_fullBlock_gapDeviation_tendsto_zero
    noiseLaw hbeta hvariance
    (isOpen_Iio.mem_nhds hepsilon)

end

end PG24NoisyMatchingMarkets
