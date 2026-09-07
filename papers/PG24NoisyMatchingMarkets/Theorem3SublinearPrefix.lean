import PG24NoisyMatchingMarkets.Theorem3RankedCutoffs
import Mathlib.Tactic

/-!
# PG24 Theorem 3 sublinear early prefixes

The large-gap branch removes the first `floor(C ^ exponent)` ranked cutoffs.
For every exponent strictly below one, that prefix is asymptotically a
vanishing fraction of the coalition.  The declarations here prove that
rounding fact and apply it to the semantic ranked suffix construction.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

theorem theorem3EarlyPrefixRank_div_coalitionSize_le_rpow_sub_one
    {C : ℕ} {exponent : ℝ} (hC_pos : 0 < C) :
    (theorem3EarlyPrefixRank C exponent : ℝ) /
        (((C + 1 : ℕ) : ℝ)) ≤
      Real.rpow (C : ℝ) (exponent - 1) := by
  have hC_real_pos : 0 < (C : ℝ) := by
    exact_mod_cast hC_pos
  have hden_pos : 0 < (((C + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos C
  have hfloor :
      (theorem3EarlyPrefixRank C exponent : ℝ) ≤
        Real.rpow (C : ℝ) exponent := by
    unfold theorem3EarlyPrefixRank
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg C) exponent)
  have hsplit : Real.rpow (C : ℝ) exponent =
      Real.rpow (C : ℝ) (exponent - 1) * (C : ℝ) := by
    calc
      Real.rpow (C : ℝ) exponent =
          Real.rpow (C : ℝ) ((exponent - 1) + 1) := by
            congr 1
            ring
      _ = Real.rpow (C : ℝ) (exponent - 1) * Real.rpow (C : ℝ) 1 :=
        Real.rpow_add hC_real_pos _ _
      _ = Real.rpow (C : ℝ) (exponent - 1) * (C : ℝ) := by
        rw [show Real.rpow (C : ℝ) (1 : ℝ) = (C : ℝ) by
          exact Real.rpow_one (C : ℝ)]
  calc
    (theorem3EarlyPrefixRank C exponent : ℝ) /
        (((C + 1 : ℕ) : ℝ)) ≤
      Real.rpow (C : ℝ) exponent / (((C + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hfloor hden_pos.le
    _ = Real.rpow (C : ℝ) (exponent - 1) *
        ((C : ℝ) / (((C + 1 : ℕ) : ℝ))) := by
      rw [hsplit]
      ring
    _ ≤ Real.rpow (C : ℝ) (exponent - 1) := by
      have hpow_nonneg : 0 ≤ Real.rpow (C : ℝ) (exponent - 1) :=
        Real.rpow_nonneg (Nat.cast_nonneg C) _
      have hratio_nonneg : 0 ≤ (C : ℝ) / (((C + 1 : ℕ) : ℝ)) := by
        positivity
      have hratio_le_one : (C : ℝ) / (((C + 1 : ℕ) : ℝ)) ≤ 1 := by
        rw [div_le_one hden_pos]
        exact_mod_cast Nat.le_succ C
      nlinarith

theorem theorem3EarlyPrefixRank_div_coalitionSize_tendsto_zero
    {exponent : ℝ} (hexponent_lt_one : exponent < 1) :
    Filter.Tendsto
      (fun C : ℕ =>
        (theorem3EarlyPrefixRank C exponent : ℝ) /
          (((C + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have hrate : 0 < 1 - exponent := by
    linarith
  have hpow_neg :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (-(1 - exponent)))
        Filter.atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hrate).comp tendsto_natCast_atTop_atTop
  have hpow :
      Filter.Tendsto
        (fun C : ℕ => Real.rpow (C : ℝ) (exponent - 1))
        Filter.atTop (nhds 0) := by
    have hexponent : exponent - 1 = -(1 - exponent) := by
      ring
    simpa only [hexponent] using hpow_neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 0)) hpow ?_ ?_
  · filter_upwards with C
    positivity
  · filter_upwards [Filter.eventually_gt_atTop 0] with C hC_pos
    exact theorem3EarlyPrefixRank_div_coalitionSize_le_rpow_sub_one hC_pos

theorem theorem3EarlyPrefixRank_eventually_cut_fraction_lt
    {exponent epsilon : ℝ} (hexponent_lt_one : exponent < 1)
    (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in Filter.atTop,
      (theorem3EarlyPrefixRank C exponent : ℝ) /
          (((C + 1 : ℕ) : ℝ)) < epsilon := by
  exact theorem3EarlyPrefixRank_div_coalitionSize_tendsto_zero
    hexponent_lt_one (isOpen_Iio.mem_nhds hepsilon_pos)

theorem theorem3CoalitionLargeSubset_rankedSuffix_earlyPrefix_eventually
    {exponent epsilon : ℝ} (hexponent_lt_one : exponent < 1)
    (hepsilon_pos : 0 < epsilon) :
    ∀ᶠ C : ℕ in Filter.atTop,
      ∀ cutoff : Fin (C + 1) → ℝ,
        CoalitionLargeSubset
          (Finset.univ : Finset (Fin (C + 1)))
          (theorem3RankedSuffix C cutoff
            (theorem3EarlyPrefixRank C exponent)) epsilon := by
  filter_upwards [
    theorem3EarlyPrefixRank_eventually_cut_fraction_lt
      hexponent_lt_one hepsilon_pos,
    Filter.eventually_gt_atTop 1] with C hfraction hC_one_lt cutoff
  apply theorem3CoalitionLargeSubset_rankedSuffix_of_cut_fraction_lt cutoff
    (Nat.le_of_lt
      (theorem3EarlyPrefixRank_lt_coalitionSize hC_one_lt
        hexponent_lt_one))
  exact hfraction

end

end PG24NoisyMatchingMarkets
