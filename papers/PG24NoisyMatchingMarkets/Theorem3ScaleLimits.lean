import PG24NoisyMatchingMarkets.Theorem3DenseGapExponents

/-!
# PG24 Theorem 3 scale limits

The dense-window width and the large-gap centering displacement are negative
power scales.  Their convergence to zero is used to fit the fixed epsilon
margins in the source statement around the branch-specific threshold.
-/

open Filter Topology

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The repaired dense-window width tends to zero. -/
theorem theorem3DenseWindowWidth_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ)
        (theorem3DenseWindowExponent beta))
      atTop (nhds 0) := by
  have hneg : theorem3DenseWindowExponent beta < 0 :=
    theorem3DenseWindowExponent_neg hbeta
  have hrate : 0 < -theorem3DenseWindowExponent beta := by linarith
  have hpow :=
    (tendsto_rpow_neg_atTop hrate).comp tendsto_natCast_atTop_atTop
  have hrewrite : theorem3DenseWindowExponent beta =
      -(-theorem3DenseWindowExponent beta) := by ring
  rw [hrewrite]
  exact hpow

/-- Any fixed positive margin eventually dominates the dense-window width. -/
theorem theorem3DenseWindowWidth_eventually_lt
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) < epsilon :=
  theorem3DenseWindowWidth_tendsto_zero hbeta
    (isOpen_Iio.mem_nhds hepsilon)

/-- The negative-power centering displacement in the large-gap branch tends
to zero. -/
theorem theorem3GapDisplacement_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta) :
    Tendsto
      (fun C : ℕ => Real.rpow (C : ℝ)
        (theorem3GapDisplacementExponent beta))
      atTop (nhds 0) := by
  have hneg : theorem3GapDisplacementExponent beta < 0 :=
    theorem3GapDisplacementExponent_neg hbeta
  have hrate : 0 < -theorem3GapDisplacementExponent beta := by linarith
  have hpow :=
    (tendsto_rpow_neg_atTop hrate).comp tendsto_natCast_atTop_atTop
  have hrewrite : theorem3GapDisplacementExponent beta =
      -(-theorem3GapDisplacementExponent beta) := by ring
  rw [hrewrite]
  exact hpow

/-- Any fixed positive margin eventually dominates the large-gap centering
displacement. -/
theorem theorem3GapDisplacement_eventually_lt
    {beta epsilon : ℝ} (hbeta : 0 < beta) (hepsilon : 0 < epsilon) :
    ∀ᶠ C : ℕ in atTop,
      Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta) < epsilon :=
  theorem3GapDisplacement_tendsto_zero hbeta
    (isOpen_Iio.mem_nhds hepsilon)

end

end PG24NoisyMatchingMarkets
