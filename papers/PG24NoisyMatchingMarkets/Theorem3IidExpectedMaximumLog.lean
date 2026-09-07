import PG24NoisyMatchingMarkets.Assumptions
import PG24NoisyMatchingMarkets.Theorem3MaximumDyadicVarianceBridge

/-!
# PG24 Theorem 3 iid expected-maximum logarithmic bound

The source variance premise supplies finite second moments only eventually.
This module therefore derives eventual, rather than global, monotonicity of
the iid expected maximum before applying the shifted dyadic analytic lemma.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- Once consecutive iid maximum order statistics are in `L²`, their
expectations are monotone in sample size; hence an eventual `L²` premise gives
the eventual monotonicity needed by the logarithmic dyadic argument. -/
theorem theorem3_iidExpectedTop_eventually_monotone_of_eventual_memLp
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (hmem : ∀ᶠ n : ℕ in atTop,
      MemLp
        (fun sample : Fin (n + 1) → ℝ =>
          AppliedModelingLib.Probability.upperOrderStatistic sample
            (AppliedModelingLib.Probability.topSampleRank (n := n + 1))) 2
        (Measure.pi (fun _ : Fin (n + 1) => noiseLaw))) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m →
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n ≤
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) m := by
  rcases Filter.eventually_atTop.1 hmem with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn m hnm
  refine Nat.le_induction (P := fun k _ =>
    AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun j : ℕ => Measure.pi (fun _ : Fin (j + 1) => noiseLaw)) n ≤
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
        (fun j : ℕ => Measure.pi (fun _ : Fin (j + 1) => noiseLaw)) k)
    le_rfl ?_ m hnm
  intro k hnk ih
  exact ih.trans
    (IidMaximumDyadic.iidExpectedTop_succ_mono noiseLaw k
      (hN k (hn.trans hnk))
      (hN (k + 1) (by omega)))

/-- The product-measure dyadic comparison applies eventually under the exact
finite-second-moment and variance clauses of the source beta-max premise. -/
theorem theorem3_iidExpectedTop_doubling_increment_eventually_of_source_variance
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    (maxVariance : ℕ → ℝ)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    ∀ᶠ n : ℕ in atTop,
      AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) (2 * n) -
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n ≤
        2 * Real.sqrt (maxVariance n) := by
  rcases Filter.eventually_atTop.1 hvariance.1 with ⟨Nmem, hmem⟩
  rcases Filter.eventually_atTop.1 hvariance.2 with ⟨Nvariance, hvariance⟩
  filter_upwards [eventually_ge_atTop (max Nmem Nvariance)] with n hn
  have hn_mem : Nmem ≤ n := le_trans (le_max_left _ _) hn
  have hn_variance : Nvariance ≤ n := le_trans (le_max_right _ _) hn
  exact IidMaximumDyadic.iidExpectedTop_two_mul_increment_le
    noiseLaw maxVariance n
    (hmem n hn_mem)
    (hmem (n + n) (by omega))
    (hvariance n hn_variance)

/-- The PG24 beta-max variance condition proves the source logarithmic bound
for iid expected maxima.  Its monotonicity and dyadic increment inputs are
both derived above from the product model, with no global integrability or
bridge assumption. -/
theorem theorem3_iidExpectedMaximum_div_log_tendsto_zero_of_beta
    (noiseLaw : Measure ℝ) [IsProbabilityMeasure noiseLaw]
    {maxVariance : ℕ → ℝ} {beta : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance beta)
    (hvariance : source_assumption_iid_beta_max_variance_bound
      noiseLaw maxVariance) :
    Tendsto
      (fun n : ℕ =>
        AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
          (fun k : ℕ => Measure.pi (fun _ : Fin (k + 1) => noiseLaw)) n /
          Real.log (n : ℝ))
      atTop (nhds 0) := by
  have hmono := theorem3_iidExpectedTop_eventually_monotone_of_eventual_memLp
    noiseLaw hvariance.1
  have hdouble :=
    theorem3_iidExpectedTop_doubling_increment_eventually_of_source_variance
      noiseLaw maxVariance hvariance
  have herror :=
    theorem3_two_mul_sqrt_variance_tendsto_zero_of_beta_variance_bound
      hbeta hvariance.2
  apply theorem3_eventuallyMonotone_doubling_div_log_tendsto_zero hmono
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (maxVariance n) < epsilon :=
    herror (isOpen_Iio.mem_nhds hepsilon)
  filter_upwards [hdouble, hsmall] with n hdouble_n hsmall_n
  exact hdouble_n.trans (le_of_lt hsmall_n)

end

end PG24NoisyMatchingMarkets
