import PG24NoisyMatchingMarkets.Theorem3DenseChebyshev
import PG24NoisyMatchingMarkets.Theorem3MaximumTailBridge
import PG24NoisyMatchingMarkets.Theorem3RankedDenseBlockProbability
import PG24NoisyMatchingMarkets.Theorem3ScaleLimits

/-!
# PG24 Theorem 3 dense-branch high endpoint

This is the actual high-side concentration calculation for a semantic dense
rank block.  The fixed theorem margin eventually dominates the shrinking
dense-window width, and Chebyshev controls the exact rounded iid block.
-/

open Filter Topology MeasureTheory

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The dense branch admits values one fixed epsilon above its natural
cutoff-minus-expected-maximum threshold. -/
theorem theorem3_ranked_dense_high_endpoint_eventually
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
            (theorem3RankedSuffix C cutoff start)
            (theorem3RankedCutoffNat C cutoff start -
              AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
                (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
                (theorem3DenseWindowCount C
                  (theorem3DenseClusterExponent beta) - 1) + epsilon)
            cutoff := by
  have hwidth_small := theorem3DenseWindowWidth_eventually_lt hbeta.1
    (by linarith : 0 < epsilon / 2)
  have hdeviation_small :=
    theorem3_iidMaximum_roundedDenseBlock_deviation_eventually_lt
      noiseLaw hbeta hvariance hepsilon
  filter_upwards [hwidth_small, hdeviation_small,
    eventually_gt_atTop 0] with C hwidth_small_C hdeviation_small_C hC_pos
      cutoff start hterminal hdense
  let stride : ℕ := theorem3DenseWindowCount C
    (theorem3DenseClusterExponent beta)
  let mean : ℝ := AppliedModelingLib.Probability.expectedTopOrderStatisticSeq
    (fun n : ℕ => Measure.pi (fun _ : Fin (n + 1) => noiseLaw))
    (stride - 1)
  let width : ℝ := Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta)
  have hwidth_pos : 0 < width := by
    dsimp [width]
    exact Real.rpow_pos_of_pos (by exact_mod_cast hC_pos) _
  have hmargin : 2 * width < epsilon := by
    dsimp [width]
    calc
      2 * Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) <
          2 * (epsilon / 2) :=
        mul_lt_mul_of_pos_left hwidth_small_C (by norm_num)
      _ = epsilon := by ring
  have hseparation :
      theorem3RankedCutoffNat C cutoff start + width -
          (theorem3RankedCutoffNat C cutoff start - mean + epsilon) <
        mean - width := by
    linarith [hmargin]
  have hblock := theorem3_iidMaximum_high_crossing_gt_one_sub_of_deviation_lt
    noiseLaw (stride - 1) hwidth_pos hseparation (by
      simpa [stride, mean, width] using hdeviation_small_C)
  have hstride : (stride - 1) + 1 = stride := by
    dsimp [stride]
    exact theorem3DenseWindowCount_sub_one_add_one hC_pos
  rw [hstride] at hblock
  exact theorem3_ranked_denseBlock_high_affordance_gt_one_sub
    C start stride cutoff noiseLaw width
    (theorem3RankedCutoffNat C cutoff start - mean + epsilon) epsilon
    (by simpa [stride] using hterminal)
    (by simpa [stride, width] using hdense)
    hblock

end

end PG24NoisyMatchingMarkets
