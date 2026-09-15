import PG24NoisyMatchingMarkets.Theorem3RoundedScaleFit
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic

/-!
# PG24 Theorem 3 rounded large-gap scale

The finite dense-window / large-gap dichotomy produces
`floor(C^prefix) / ceil(C^dense)` full blocks.  This module proves that,
after multiplying by the dense-window width, the resulting geometric gap
scale diverges for the beta-only exponents.  The proof keeps the floor,
ceiling, and natural division visible rather than treating the source's
power-index notation as exact real arithmetic.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
If the block-width exponent is negative and the combined large-gap exponent
is positive, then a floor power strictly below the available quotient fits
eventually.  This is the rounding-sensitive lower bound behind the
large-gap branch.
-/
theorem theorem3DenseGapBlockCount_eventually_ge_floor_lowerScale
    {denseExponent prefixExponent width gapExponent : ℝ}
    (hdense_nonneg : 0 ≤ denseExponent)
    (hwidth_neg : width < 0)
    (hgap_pos : 0 < gapExponent)
    (hgap_eq : gapExponent = width + prefixExponent - denseExponent) :
    ∀ᶠ C : ℕ in Filter.atTop,
      ⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ ≤
        theorem3DenseGapBlockCount C denseExponent prefixExponent := by
  have hhalf_gap_pos : 0 < gapExponent / 2 := by
    linarith
  have hlowerExponent_pos : 0 < gapExponent / 2 - width := by
    linarith
  have hgap_power_tendsto :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (gapExponent / 2))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hhalf_gap_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,
    hgap_power_tendsto.eventually_ge_atTop (4 : ℝ)] with C hC_one hgap_power
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  rw [show theorem3DenseGapBlockCount C denseExponent prefixExponent =
      theorem3EarlyPrefixRank C prefixExponent /
        theorem3DenseWindowCount C denseExponent from rfl]
  apply (Nat.le_div_iff_mul_le
    (theorem3DenseWindowCount_pos (C := C) (exponent := denseExponent) hC_pos)).2
  rw [show theorem3EarlyPrefixRank C prefixExponent =
      ⌊Real.rpow (C : ℝ) prefixExponent⌋₊ from rfl]
  apply Nat.le_floor
  have hlower_floor_le :
      (⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ : ℝ) ≤
        Real.rpow (C : ℝ) (gapExponent / 2 - width) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hdense_power_one :
      1 ≤ Real.rpow (C : ℝ) denseExponent :=
    Real.one_le_rpow hC_real_one hdense_nonneg
  have hdense_count_le :
      (theorem3DenseWindowCount C denseExponent : ℝ) ≤
        2 * Real.rpow (C : ℝ) denseExponent := by
    rw [show theorem3DenseWindowCount C denseExponent =
        ⌈Real.rpow (C : ℝ) denseExponent⌉₊ from rfl]
    calc
      (⌈Real.rpow (C : ℝ) denseExponent⌉₊ : ℝ) ≤
          Real.rpow (C : ℝ) denseExponent + 1 :=
        (Nat.ceil_lt_add_one
          (Real.rpow_nonneg (Nat.cast_nonneg C) denseExponent)).le
      _ ≤ 2 * Real.rpow (C : ℝ) denseExponent := by
        linarith
  have hpower_target :
      Real.rpow (C : ℝ) (gapExponent / 2 - width) *
          (2 * Real.rpow (C : ℝ) denseExponent) ≤
        Real.rpow (C : ℝ) prefixExponent := by
    have hsum : (gapExponent / 2 - width) + denseExponent =
        prefixExponent - gapExponent / 2 := by
      linarith [hgap_eq]
    have htarget_nonneg :
        0 ≤ Real.rpow (C : ℝ) (prefixExponent - gapExponent / 2) :=
      Real.rpow_nonneg (Nat.cast_nonneg C) _
    calc
      Real.rpow (C : ℝ) (gapExponent / 2 - width) *
          (2 * Real.rpow (C : ℝ) denseExponent) =
          2 * (Real.rpow (C : ℝ) (gapExponent / 2 - width) *
            Real.rpow (C : ℝ) denseExponent) := by
        ring
      _ = 2 * Real.rpow (C : ℝ) (prefixExponent - gapExponent / 2) := by
        change 2 * ((C : ℝ) ^ (gapExponent / 2 - width) *
          (C : ℝ) ^ denseExponent) =
          2 * (C : ℝ) ^ (prefixExponent - gapExponent / 2)
        rw [← Real.rpow_add hC_real_pos
          (gapExponent / 2 - width) denseExponent]
        rw [hsum]
      _ ≤ Real.rpow (C : ℝ) (prefixExponent - gapExponent / 2) *
          Real.rpow (C : ℝ) (gapExponent / 2) := by
        nlinarith
      _ = Real.rpow (C : ℝ) prefixExponent := by
        change (C : ℝ) ^ (prefixExponent - gapExponent / 2) *
          (C : ℝ) ^ (gapExponent / 2) = (C : ℝ) ^ prefixExponent
        rw [← Real.rpow_add hC_real_pos
          (prefixExponent - gapExponent / 2) (gapExponent / 2)]
        congr 1
        ring
  calc
    ((⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ *
        theorem3DenseWindowCount C denseExponent : ℕ) : ℝ) =
        (⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ : ℝ) *
          (theorem3DenseWindowCount C denseExponent : ℝ) := by
      norm_num
    _ ≤ Real.rpow (C : ℝ) (gapExponent / 2 - width) *
        (theorem3DenseWindowCount C denseExponent : ℝ) :=
      mul_le_mul_of_nonneg_right hlower_floor_le (Nat.cast_nonneg _)
    _ ≤ Real.rpow (C : ℝ) (gapExponent / 2 - width) *
        (2 * Real.rpow (C : ℝ) denseExponent) :=
      mul_le_mul_of_nonneg_left hdense_count_le
        (Real.rpow_nonneg (Nat.cast_nonneg C) _)
    _ ≤ Real.rpow (C : ℝ) prefixExponent := hpower_target

/--
The rounded block count has the full source polynomial scale, up to a fixed
constant.  Unlike the weaker half-exponent bound used only to prove
divergence, this retains the exponent needed for quantitative tail bounds.
-/
theorem theorem3DenseGapBlockCount_eventually_ge_floor_quarter_fullScale
    {denseExponent prefixExponent width gapExponent : ℝ}
    (hdense_nonneg : 0 ≤ denseExponent)
    (hwidth_neg : width < 0)
    (hgap_pos : 0 < gapExponent)
    (hgap_eq : gapExponent = width + prefixExponent - denseExponent) :
    ∀ᶠ C : ℕ in Filter.atTop,
      ⌊(1 / 4 : ℝ) *
        Real.rpow (C : ℝ) (gapExponent - width)⌋₊ ≤
        theorem3DenseGapBlockCount C denseExponent prefixExponent := by
  have hfull_scale_pos : 0 < gapExponent - width := by
    linarith
  have hfull_scale_tendsto :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (gapExponent - width))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hfull_scale_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,
    hfull_scale_tendsto.eventually_ge_atTop (4 : ℝ)] with C hC_one hfull_scale
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  rw [show theorem3DenseGapBlockCount C denseExponent prefixExponent =
      theorem3EarlyPrefixRank C prefixExponent /
        theorem3DenseWindowCount C denseExponent from rfl]
  apply (Nat.le_div_iff_mul_le
    (theorem3DenseWindowCount_pos (C := C) (exponent := denseExponent) hC_pos)).2
  rw [show theorem3EarlyPrefixRank C prefixExponent =
      ⌊Real.rpow (C : ℝ) prefixExponent⌋₊ from rfl]
  apply Nat.le_floor
  have hquarter_nonneg :
      0 ≤ (1 / 4 : ℝ) *
        Real.rpow (C : ℝ) (gapExponent - width) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg C) _)
  have hfloor_le :
      (⌊(1 / 4 : ℝ) *
        Real.rpow (C : ℝ) (gapExponent - width)⌋₊ : ℝ) ≤
        (1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width) :=
    Nat.floor_le hquarter_nonneg
  have hdense_power_one :
      1 ≤ Real.rpow (C : ℝ) denseExponent :=
    Real.one_le_rpow hC_real_one hdense_nonneg
  have hdense_count_le :
      (theorem3DenseWindowCount C denseExponent : ℝ) ≤
        2 * Real.rpow (C : ℝ) denseExponent := by
    rw [show theorem3DenseWindowCount C denseExponent =
        ⌈Real.rpow (C : ℝ) denseExponent⌉₊ from rfl]
    calc
      (⌈Real.rpow (C : ℝ) denseExponent⌉₊ : ℝ) ≤
          Real.rpow (C : ℝ) denseExponent + 1 :=
        (Nat.ceil_lt_add_one
          (Real.rpow_nonneg (Nat.cast_nonneg C) denseExponent)).le
      _ ≤ 2 * Real.rpow (C : ℝ) denseExponent := by
        linarith
  have hpower_product :
      Real.rpow (C : ℝ) (gapExponent - width) *
          Real.rpow (C : ℝ) denseExponent =
        Real.rpow (C : ℝ) prefixExponent := by
    calc
      Real.rpow (C : ℝ) (gapExponent - width) *
          Real.rpow (C : ℝ) denseExponent =
          Real.rpow (C : ℝ) ((gapExponent - width) + denseExponent) :=
        (Real.rpow_add hC_real_pos _ _).symm
      _ = Real.rpow (C : ℝ) prefixExponent := by
        congr 1
        linarith [hgap_eq]
  calc
    ((⌊(1 / 4 : ℝ) *
        Real.rpow (C : ℝ) (gapExponent - width)⌋₊ *
        theorem3DenseWindowCount C denseExponent : ℕ) : ℝ) =
        (⌊(1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)⌋₊ : ℝ) *
          (theorem3DenseWindowCount C denseExponent : ℝ) := by
      norm_num
    _ ≤ ((1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)) *
          (theorem3DenseWindowCount C denseExponent : ℝ) :=
      mul_le_mul_of_nonneg_right hfloor_le (Nat.cast_nonneg _)
    _ ≤ ((1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)) *
          (2 * Real.rpow (C : ℝ) denseExponent) :=
      mul_le_mul_of_nonneg_left hdense_count_le hquarter_nonneg
    _ = (1 / 2 : ℝ) * Real.rpow (C : ℝ) prefixExponent := by
      rw [show ((1 / 4 : ℝ) * Real.rpow (C : ℝ) (gapExponent - width)) *
          (2 * Real.rpow (C : ℝ) denseExponent) =
          ((1 / 2 : ℝ) *
            (Real.rpow (C : ℝ) (gapExponent - width) *
              Real.rpow (C : ℝ) denseExponent)) by ring]
      rw [hpower_product]
    _ ≤ Real.rpow (C : ℝ) prefixExponent := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg C) prefixExponent]

/--
The exact rounded large-gap scale is eventually at least one eighth of its
source real-power scale.  This is the quantitative counterpart of the
divergence lemma below.
-/
theorem theorem3DenseGapBlockCount_mul_rpow_eventually_ge_eighth_rpow
    {denseExponent prefixExponent width gapExponent : ℝ}
    (hdense_nonneg : 0 ≤ denseExponent)
    (hwidth_neg : width < 0)
    (hgap_pos : 0 < gapExponent)
    (hgap_eq : gapExponent = width + prefixExponent - denseExponent) :
    ∀ᶠ C : ℕ in Filter.atTop,
      (1 / 8 : ℝ) * Real.rpow (C : ℝ) gapExponent ≤
        (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
          Real.rpow (C : ℝ) width := by
  have hfull_scale_pos : 0 < gapExponent - width := by
    linarith
  have hfull_scale_tendsto :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (gapExponent - width))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hfull_scale_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [
    theorem3DenseGapBlockCount_eventually_ge_floor_quarter_fullScale
      hdense_nonneg hwidth_neg hgap_pos hgap_eq,
    Filter.eventually_ge_atTop 1,
    hfull_scale_tendsto.eventually_ge_atTop (4 : ℝ)] with
      C hblock_lower hC_one hfull_scale
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hquarter_one :
      1 ≤ (1 / 4 : ℝ) *
        Real.rpow (C : ℝ) (gapExponent - width) := by
    linarith
  have hfloor_lower :
      ((1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)) / 2 ≤
        (⌊(1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)⌋₊ : ℝ) :=
    (Nat.div_two_lt_floor hquarter_one).le
  have hblock_lower_real :
      (⌊(1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)⌋₊ : ℝ) ≤
        (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) := by
    exact_mod_cast hblock_lower
  have hwidth_nonneg : 0 ≤ Real.rpow (C : ℝ) width :=
    Real.rpow_nonneg (Nat.cast_nonneg C) _
  have hpower_product :
      Real.rpow (C : ℝ) (gapExponent - width) *
          Real.rpow (C : ℝ) width =
        Real.rpow (C : ℝ) gapExponent := by
    calc
      Real.rpow (C : ℝ) (gapExponent - width) *
          Real.rpow (C : ℝ) width =
          Real.rpow (C : ℝ) ((gapExponent - width) + width) :=
        (Real.rpow_add hC_real_pos _ _).symm
      _ = Real.rpow (C : ℝ) gapExponent := by
        congr 1
        ring
  calc
    (1 / 8 : ℝ) * Real.rpow (C : ℝ) gapExponent =
        (((1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)) / 2) *
          Real.rpow (C : ℝ) width := by
      rw [← hpower_product]
      ring
    _ ≤ (⌊(1 / 4 : ℝ) *
          Real.rpow (C : ℝ) (gapExponent - width)⌋₊ : ℝ) *
          Real.rpow (C : ℝ) width :=
      mul_le_mul_of_nonneg_right hfloor_lower hwidth_nonneg
    _ ≤ (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
          Real.rpow (C : ℝ) width :=
      mul_le_mul_of_nonneg_right hblock_lower_real hwidth_nonneg

/--
The rounded block count times a width of exponent `width` tends to infinity
whenever the associated gap exponent is positive.  The only asymptotic input
is the exponent relation; all finite integer rounding is discharged above.
-/
theorem theorem3DenseGapBlockCount_mul_rpow_tendsto_atTop
    {denseExponent prefixExponent width gapExponent : ℝ}
    (hdense_nonneg : 0 ≤ denseExponent)
    (hwidth_neg : width < 0)
    (hgap_pos : 0 < gapExponent)
    (hgap_eq : gapExponent = width + prefixExponent - denseExponent) :
    Filter.Tendsto
      (fun C : ℕ =>
        (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
          Real.rpow (C : ℝ) width)
      Filter.atTop Filter.atTop := by
  have hhalf_gap_pos : 0 < gapExponent / 2 := by
    linarith
  have hlowerExponent_pos : 0 < gapExponent / 2 - width := by
    linarith
  have htarget_tendsto :
      Filter.Tendsto
        (fun C : ℕ =>
          (1 / 2 : ℝ) * Real.rpow (C : ℝ) (gapExponent / 2))
        Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num)
      ((tendsto_rpow_atTop hhalf_gap_pos).comp tendsto_natCast_atTop_atTop)
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ htarget_tendsto
  filter_upwards [
    theorem3DenseGapBlockCount_eventually_ge_floor_lowerScale
      hdense_nonneg hwidth_neg hgap_pos hgap_eq,
    Filter.eventually_ge_atTop 1] with C hblock_lower hC_one
  have hC_pos : 0 < C := lt_of_lt_of_le Nat.zero_lt_one hC_one
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hlower_power_one :
      1 ≤ Real.rpow (C : ℝ) (gapExponent / 2 - width) :=
    Real.one_le_rpow hC_real_one hlowerExponent_pos.le
  have hfloor_lower :
      Real.rpow (C : ℝ) (gapExponent / 2 - width) / 2 ≤
        (⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ : ℝ) :=
    (Nat.div_two_lt_floor hlower_power_one).le
  have hblock_lower_real :
      (⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ : ℝ) ≤
        (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) := by
    exact_mod_cast hblock_lower
  have hwidth_nonneg : 0 ≤ Real.rpow (C : ℝ) width :=
    Real.rpow_nonneg (Nat.cast_nonneg C) _
  have hpower_product :
      Real.rpow (C : ℝ) (gapExponent / 2 - width) *
          Real.rpow (C : ℝ) width =
        Real.rpow (C : ℝ) (gapExponent / 2) := by
    change (C : ℝ) ^ (gapExponent / 2 - width) * (C : ℝ) ^ width =
      (C : ℝ) ^ (gapExponent / 2)
    rw [← Real.rpow_add hC_real_pos]
    congr 1
    ring
  calc
    (1 / 2 : ℝ) * Real.rpow (C : ℝ) (gapExponent / 2) =
        (Real.rpow (C : ℝ) (gapExponent / 2 - width) / 2) *
          Real.rpow (C : ℝ) width := by
      rw [← hpower_product]
      ring
    _ ≤ (⌊Real.rpow (C : ℝ) (gapExponent / 2 - width)⌋₊ : ℝ) *
        Real.rpow (C : ℝ) width :=
      mul_le_mul_of_nonneg_right hfloor_lower hwidth_nonneg
    _ ≤ (theorem3DenseGapBlockCount C denseExponent prefixExponent : ℝ) *
        Real.rpow (C : ℝ) width :=
      mul_le_mul_of_nonneg_right hblock_lower_real hwidth_nonneg

/--
For the beta-only PG24 exponents, the rounded number of full dense windows
times the dense-window width diverges.  This is the large-gap scale needed to
separate the early and late ranked cutoffs.
-/
theorem theorem3DenseGapBlockCount_mul_denseWindowScale_tendsto_atTop
    {beta : ℝ} (hbeta : 0 < beta) :
    Filter.Tendsto
      (fun C : ℕ =>
        (theorem3DenseGapBlockCount C
          (theorem3DenseClusterExponent beta)
          (theorem3EarlyCutoffExponent beta) : ℝ) *
          Real.rpow (C : ℝ) (theorem3DenseWindowExponent beta))
      Filter.atTop Filter.atTop :=
  theorem3DenseGapBlockCount_mul_rpow_tendsto_atTop
    (theorem3DenseClusterExponent_pos hbeta).le
    (theorem3DenseWindowExponent_neg hbeta)
    (theorem3LargeGapExponent_pos hbeta)
    rfl

end

end PG24NoisyMatchingMarkets
