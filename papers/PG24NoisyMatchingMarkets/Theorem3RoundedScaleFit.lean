import PG24NoisyMatchingMarkets.Theorem3RoundedRanks
import Mathlib.Tactic

/-!
# PG24 Theorem 3 rounded scale fit

The finite dense-window/large-gap dichotomy requires one rounded dense window
to fit inside the rounded early prefix.  This file proves that fact directly
from a strict separation between the two power exponents.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

/--
For nonnegative exponents, a strict power-scale separation eventually survives
the ceiling/floor choices used by the finite dense-window construction.
-/
theorem theorem3DenseWindowCount_eventually_le_earlyPrefixRank
    {denseExponent prefixExponent : ℝ}
    (hdense_nonneg : 0 ≤ denseExponent)
    (hdense_lt_prefix : denseExponent < prefixExponent) :
    ∀ᶠ C : ℕ in Filter.atTop,
      theorem3DenseWindowCount C denseExponent ≤
        theorem3EarlyPrefixRank C prefixExponent := by
  have hgap_pos : 0 < prefixExponent - denseExponent :=
    sub_pos.mpr hdense_lt_prefix
  have htend :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (prefixExponent - denseExponent))
        Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hgap_pos).comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1,
    htend.eventually_ge_atTop (2 : ℝ)]
    with C hC_one hfactor_two
  rw [show theorem3DenseWindowCount C denseExponent =
      ⌈Real.rpow (C : ℝ) denseExponent⌉₊ from rfl,
    show theorem3EarlyPrefixRank C prefixExponent =
      ⌊Real.rpow (C : ℝ) prefixExponent⌋₊ from rfl]
  apply Nat.le_floor
  have hC_real_one : (1 : ℝ) ≤ (C : ℝ) := by
    exact_mod_cast hC_one
  have hC_real_pos : 0 < (C : ℝ) :=
    lt_of_lt_of_le zero_lt_one hC_real_one
  have hdense_power_one : 1 ≤ Real.rpow (C : ℝ) denseExponent :=
    Real.one_le_rpow hC_real_one hdense_nonneg
  have hsplit : Real.rpow (C : ℝ) prefixExponent =
      Real.rpow (C : ℝ) denseExponent *
        Real.rpow (C : ℝ) (prefixExponent - denseExponent) := by
    calc
      Real.rpow (C : ℝ) prefixExponent =
          Real.rpow (C : ℝ) (denseExponent + (prefixExponent - denseExponent)) := by
            have hsum : prefixExponent =
                denseExponent + (prefixExponent - denseExponent) := by
              ring
            exact congrArg (fun exponent : ℝ => Real.rpow (C : ℝ) exponent) hsum
      _ = Real.rpow (C : ℝ) denseExponent *
          Real.rpow (C : ℝ) (prefixExponent - denseExponent) :=
        Real.rpow_add hC_real_pos _ _
  have hceil_lt :
      (⌈Real.rpow (C : ℝ) denseExponent⌉₊ : ℝ) <
        Real.rpow (C : ℝ) denseExponent + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg C) denseExponent)
  calc
    (⌈Real.rpow (C : ℝ) denseExponent⌉₊ : ℝ) ≤
        Real.rpow (C : ℝ) denseExponent + 1 := hceil_lt.le
    _ ≤ Real.rpow (C : ℝ) prefixExponent := by
      rw [hsplit]
      nlinarith

/--
The beta-only PG24 exponents eventually make the rounded dense cluster fit in
the rounded early prefix.
-/
theorem theorem3DenseClusterCount_eventually_le_earlyPrefixRank
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ C : ℕ in Filter.atTop,
      theorem3DenseWindowCount C (theorem3DenseClusterExponent beta) ≤
        theorem3EarlyPrefixRank C (theorem3EarlyCutoffExponent beta) :=
  theorem3DenseWindowCount_eventually_le_earlyPrefixRank
    (theorem3DenseClusterExponent_pos hbeta).le
    (theorem3DenseCluster_lt_earlyCutoff hbeta)

end

end PG24NoisyMatchingMarkets
