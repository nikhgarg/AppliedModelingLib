import PG24NoisyMatchingMarkets.Theorem3LargeGapScale
import PG24NoisyMatchingMarkets.Theorem3LogBound
import PG24NoisyMatchingMarkets.Theorem3ScaleLimits
import Mathlib.Tactic

/-!
# PG24 Theorem 3 large-gap asymptotic composition

The large-gap branch needs its centering slack to be little-o of the rounded
geometric cutoff gap.  This module derives that fact from the genuine
logarithmic maximum estimate and the beta-only rounded-gap construction.
It exposes no cutoff, coalition, or conclusion-shaped premise.
-/

open Filter Topology Asymptotics

namespace PG24NoisyMatchingMarkets

noncomputable section

/-- The rounded geometric gap has an eventual polynomial lower bound.  This
is stronger than mere divergence and is what lets the logarithmic maximum
estimate be composed with the finite rounded gap construction. -/
theorem theorem3RoundedLargeGapScale_eventually_ge_half_rpow
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ C : ℕ in atTop,
      (1 / 2 : ℝ) * Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2) ≤
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
  have hblock_lower :=
    theorem3DenseGapBlockCount_eventually_ge_floor_lowerScale
      (denseExponent := theorem3DenseClusterExponent beta)
      (prefixExponent := theorem3EarlyCutoffExponent beta)
      (width := theorem3DenseWindowExponent beta)
      (gapExponent := theorem3LargeGapExponent beta)
      (theorem3DenseClusterExponent_pos hbeta).le
      (theorem3DenseWindowExponent_neg hbeta)
      (theorem3LargeGapExponent_pos hbeta)
      rfl
  filter_upwards [hblock_lower, eventually_ge_atTop 1] with C hblock_lower hC_one
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hlowerExponent_pos :
      0 < theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta := by
    have hgap_pos := theorem3LargeGapExponent_pos hbeta
    have hwidth_neg := theorem3DenseWindowExponent_neg hbeta
    linarith
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hlower_power_one :
      1 ≤ Real.rpow (C : ℝ)
        (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta) :=
    Real.one_le_rpow hC_real_one hlowerExponent_pos.le
  have hfloor_lower :
      Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta) / 2 ≤
        (⌊Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta)⌋₊ : ℝ) :=
    (Nat.div_two_lt_floor hlower_power_one).le
  have hblock_lower_real :
      (⌊Real.rpow (C : ℝ)
        (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta)⌋₊ : ℝ) ≤
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) := by
    exact_mod_cast hblock_lower
  have hwidth_nonneg :
      0 ≤ Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) :=
    Real.rpow_nonneg (Nat.cast_nonneg C) _
  have hpower_product :
      Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) =
        Real.rpow (C : ℝ) (theorem3LargeGapExponent beta / 2) := by
    change (C : ℝ) ^
        (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta) *
        (C : ℝ) ^ theorem3DenseWindowExponent beta =
      (C : ℝ) ^ (theorem3LargeGapExponent beta / 2)
    rw [← Real.rpow_add hC_real_pos]
    congr 1
    ring
  calc
    (1 / 2 : ℝ) * Real.rpow (C : ℝ)
        (theorem3LargeGapExponent beta / 2) =
        (Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta) / 2) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
      rw [← hpower_product]
      ring
    _ ≤ (⌊Real.rpow (C : ℝ)
        (theorem3LargeGapExponent beta / 2 - theorem3DenseWindowExponent beta)⌋₊ : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) :=
      mul_le_mul_of_nonneg_right hfloor_lower hwidth_nonneg
    _ ≤ (theorem3DenseGapBlockCount C
        (theorem3DenseClusterExponent beta)
        (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) :=
      mul_le_mul_of_nonneg_right hblock_lower_real hwidth_nonneg

/-- A logarithmic scale is little-o of the rounded geometric large-gap scale.
The finite lower bound above is retained explicitly so this result does not
silently replace the rounded scale by an unproved real-power approximation. -/
theorem theorem3_log_isLittleO_roundedLargeGapScale
    {beta : ℝ} (hbeta : 0 < beta) :
    (fun C : ℕ => Real.log (C : ℝ)) =o[atTop]
      fun C : ℕ =>
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
  have hhalf_gap_pos : 0 < theorem3LargeGapExponent beta / 2 := by
    linarith [theorem3LargeGapExponent_pos hbeta]
  have hlog_power :
      (fun C : ℕ => Real.log (C : ℝ)) =o[atTop]
        fun C : ℕ => Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2) := by
    simpa [Function.comp_def] using
      (isLittleO_log_rpow_atTop hhalf_gap_pos).comp_tendsto
        tendsto_natCast_atTop_atTop
  have hpower_bigO :
      (fun C : ℕ => Real.rpow (C : ℝ)
          (theorem3LargeGapExponent beta / 2)) =O[atTop]
        fun C : ℕ =>
          (theorem3DenseGapBlockCount C
            (theorem3DenseClusterExponent beta)
            (theorem3EarlyCutoffExponent beta) : ℝ) *
            Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [theorem3RoundedLargeGapScale_eventually_ge_half_rpow hbeta]
      with C hscale_lower
    have hpower_nonneg :
        0 ≤ Real.rpow (C : ℝ) (theorem3LargeGapExponent beta / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg C) _
    have hscale_nonneg :
        0 ≤ (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
      linarith
    rw [Real.norm_of_nonneg hpower_nonneg, Real.norm_of_nonneg hscale_nonneg]
    linarith
  exact hlog_power.trans_isBigO hpower_bigO

/-- A sequence whose quotient by `log C` tends to zero is little-o of
`log C`.  The denominator is nonzero eventually, so this is a genuine
asymptotic conversion rather than an additional assumption on the sequence. -/
theorem theorem3_isLittleO_log_of_div_log_tendsto_zero
    {mean : ℕ → ℝ}
    (hmean : Tendsto (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0)) :
    mean =o[atTop] fun C : ℕ => Real.log (C : ℝ) := by
  refine (isLittleO_iff_tendsto' ?_).mpr hmean
  filter_upwards [eventually_ge_atTop 2] with C hC_two hlog_zero
  have hlog_pos : 0 < Real.log (C : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hC_two
  exact (hlog_pos.ne' hlog_zero).elim

/-- The logarithmically sublinear maximum scale is little-o of the rounded
large-gap scale. -/
theorem theorem3_mean_isLittleO_roundedLargeGapScale_of_div_log_tendsto_zero
    {beta : ℝ} (hbeta : 0 < beta)
    {mean : ℕ → ℝ}
    (hmean : Tendsto (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0)) :
    mean =o[atTop]
      fun C : ℕ =>
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) :=
  (theorem3_isLittleO_log_of_div_log_tendsto_zero hmean).trans
    (theorem3_log_isLittleO_roundedLargeGapScale hbeta)

/-- The negative-power large-gap displacement is little-o of the rounded
geometric gap.  Here rounded-gap divergence is sufficient, independently of
the logarithmic maximum estimate. -/
theorem theorem3_gapDisplacement_isLittleO_roundedLargeGapScale
    {beta : ℝ} (hbeta : 0 < beta) :
    (fun C : ℕ => Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)) =o[atTop]
      fun C : ℕ =>
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
  have hdisplacement_one :
      (fun C : ℕ => Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)) =o[atTop]
        (fun _ : ℕ => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (theorem3GapDisplacement_tendsto_zero hbeta)
  have hone_gap :
      (fun _ : ℕ => (1 : ℝ)) =o[atTop]
        fun C : ℕ =>
          (theorem3DenseGapBlockCount C
            (theorem3DenseClusterExponent beta)
            (theorem3EarlyCutoffExponent beta) : ℝ) *
            Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) := by
    rw [isLittleO_one_left_iff]
    exact tendsto_norm_atTop_atTop.comp
      (theorem3DenseGapBlockCount_mul_denseWindowScale_tendsto_atTop hbeta)
  exact hdisplacement_one.trans hone_gap

/-- The complete source-relevant centering slack is little-o of the rounded
large-gap scale: an `o(log C)` maximum term plus the shrinking displacement.
This is directly usable as the `hslack_little` premise of
`theorem3_ranked_fullAffordance_eventually_one_sub_lt_of_large_gap`. -/
theorem theorem3_mean_add_gapDisplacement_isLittleO_roundedLargeGapScale
    {beta : ℝ} (hbeta : 0 < beta)
    {mean : ℕ → ℝ}
    (hmean : Tendsto (fun C : ℕ => mean C / Real.log (C : ℝ)) atTop (nhds 0)) :
    (fun C : ℕ => mean C +
      Real.rpow (C : ℝ) (theorem3GapDisplacementExponent beta)) =o[atTop]
      fun C : ℕ =>
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta) :=
  (theorem3_mean_isLittleO_roundedLargeGapScale_of_div_log_tendsto_zero
    hbeta hmean).add
    (theorem3_gapDisplacement_isLittleO_roundedLargeGapScale hbeta)

end

end PG24NoisyMatchingMarkets
