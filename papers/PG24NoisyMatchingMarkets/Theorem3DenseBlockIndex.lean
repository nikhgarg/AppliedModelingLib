import PG24NoisyMatchingMarkets.Theorem3RoundedRanks

/-!
# PG24 Theorem 3 dense-block indexing

The beta-max variance convention indexes a law on `Fin (n + 1)`, while the
finite dense block has a rounded cardinality.  These lemmas make that
off-by-one translation explicit before it is used in Chebyshev bounds.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The rounded dense block cardinality is at least its real power target. -/
theorem theorem3DenseWindowCount_real_le
    (C : ℕ) (exponent : ℝ) :
    Real.rpow (C : ℝ) exponent ≤
      (theorem3DenseWindowCount C exponent : ℝ) := by
  unfold theorem3DenseWindowCount
  exact Nat.le_ceil _

/-- The index one below a dense-block cardinality tends to infinity whenever
the block exponent is positive. -/
theorem theorem3DenseWindowCount_sub_one_tendsto_atTop
    {exponent : ℝ} (hexponent_pos : 0 < exponent) :
    Tendsto
      (fun C : ℕ => theorem3DenseWindowCount C exponent - 1)
      atTop atTop := by
  have hpow : Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ) exponent) atTop atTop :=
    (tendsto_rpow_atTop hexponent_pos).comp tendsto_natCast_atTop_atTop
  refine tendsto_atTop.2 ?_
  intro target
  filter_upwards [hpow.eventually_ge_atTop (((target + 1 : ℕ) : ℝ))]
    with C hC
  have hceil : target + 1 ≤ theorem3DenseWindowCount C exponent := by
    have hceil_real : ((target + 1 : ℕ) : ℝ) ≤
        (theorem3DenseWindowCount C exponent : ℝ) := by
      calc
        ((target + 1 : ℕ) : ℝ) ≤ Real.rpow (C : ℝ) exponent := hC
        _ ≤ (theorem3DenseWindowCount C exponent : ℝ) :=
          theorem3DenseWindowCount_real_le C exponent
    exact_mod_cast hceil_real
  omega

/-- At positive coalition sizes, restoring the indexing offset recovers the
rounded dense-block cardinality exactly. -/
theorem theorem3DenseWindowCount_sub_one_add_one
    {C : ℕ} {exponent : ℝ} (hC_pos : 0 < C) :
    (theorem3DenseWindowCount C exponent - 1) + 1 =
      theorem3DenseWindowCount C exponent := by
  exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt (theorem3DenseWindowCount_pos hC_pos)))

/-- The T3 dense-cluster block index is a growing sequence with the exact
lower cardinality required by the beta-max variance rate. -/
theorem theorem3DenseClusterBlockIndex_properties
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun C : ℕ => theorem3DenseWindowCount C
        (theorem3DenseClusterExponent beta) - 1)
      atTop atTop ∧
    (∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem3DenseClusterExponent beta) ≤
        (((theorem3DenseWindowCount C
          (theorem3DenseClusterExponent beta) - 1 + 1 : ℕ) : ℝ))) := by
  constructor
  · exact theorem3DenseWindowCount_sub_one_tendsto_atTop
      (theorem3DenseClusterExponent_pos hbeta)
  · filter_upwards [eventually_gt_atTop 0] with C hC_pos
    rw [theorem3DenseWindowCount_sub_one_add_one hC_pos]
    exact theorem3DenseWindowCount_real_le C
      (theorem3DenseClusterExponent beta)

end

end PG24NoisyMatchingMarkets
