import FalahatgarEtAl2017MaxingRanking.PruneProbability
import FalahatgarEtAl2017MaxingRanking.PruneSize

/-!
# Geometric Prune-round contraction

Lemma 15 counts the threshold-nonbetter arms that survive each history-selected
Prune round.  This module proves the deterministic recurrence used there: a
nonincreasing count that contracts whenever it exceeds the good-anchor cutoff
falls below that cutoff once its geometric target does.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/--
A nonincreasing nonnegative-scale process either has already reached the
cutoff, or is bounded by the product of every prior contraction factor.
-/
theorem geometric_contraction_or_below
    (value : ℕ → ℝ) (delta cutoff : ℝ) (roundCount : ℕ)
    (hdelta : 0 ≤ delta)
    (hmonotone : ∀ round, value (round + 1) ≤ value round)
    (hcontract : ∀ round, cutoff < value round →
      value (round + 1) ≤ delta * value round) :
    value roundCount ≤ cutoff ∨
      value roundCount ≤ delta ^ roundCount * value 0 := by
  induction roundCount with
  | zero =>
      right
      simp
  | succ round ih =>
      rcases ih with hsmall | hgeometric
      · left
        simpa [Nat.succ_eq_add_one] using (hmonotone round).trans hsmall
      · by_cases hsmall : value round ≤ cutoff
        · left
          simpa [Nat.succ_eq_add_one] using (hmonotone round).trans hsmall
        · right
          calc
            value (round + 1) ≤ delta * value round :=
              hcontract round (lt_of_not_ge hsmall)
            _ ≤ delta * (delta ^ round * value 0) :=
              mul_le_mul_of_nonneg_left hgeometric hdelta
            _ = delta ^ (round + 1) * value 0 := by
              rw [pow_succ]
              ring

/-- A geometric target at the final scheduled round forces the count below cutoff. -/
theorem geometric_contraction_reaches_cutoff
    (value : ℕ → ℝ) (delta cutoff : ℝ) (roundCount : ℕ)
    (hdelta : 0 ≤ delta)
    (hmonotone : ∀ round, value (round + 1) ≤ value round)
    (hcontract : ∀ round, cutoff < value round →
      value (round + 1) ≤ delta * value round)
    (htarget : delta ^ roundCount * value 0 ≤ cutoff) :
    value roundCount ≤ cutoff := by
  rcases geometric_contraction_or_below value delta cutoff roundCount hdelta hmonotone
    hcontract with hsmall | hgeometric
  · exact hsmall
  · exact hgeometric.trans htarget

/-- Every source-scheduled round has a positive failure budget at most `delta / 4`. -/
theorem adaptivePruneRoundDelta_pos_le_delta_div_four
    (delta : ℝ) (hdelta : 0 < delta) (round : ℕ) :
    0 < adaptivePruneRoundDelta delta round ∧
      adaptivePruneRoundDelta delta round ≤ delta / 4 := by
  unfold adaptivePruneRoundDelta
  have hpowPos : 0 < (2 : ℝ) ^ (round + 2) := by positivity
  constructor
  · exact div_pos hdelta hpowPos
  · rw [show round + 2 = round + 2 by rfl, pow_add]
    norm_num
    have hpowGeOne : 1 ≤ (2 : ℝ) ^ round := one_le_pow₀ (by norm_num)
    have hdenPos : 0 < (2 : ℝ) ^ round * 4 := by positivity
    apply (div_le_iff₀ hdenPos).mpr
    nlinarith

/--
The source Prune-round confidence factor separates into its global confidence
term and the round-index term used in the comparison-count calculation.
-/
theorem log_two_div_adaptivePruneRoundDelta
    (delta : ℝ) (hdelta : 0 < delta) (round : ℕ) :
    Real.log (2 / adaptivePruneRoundDelta delta round) =
      Real.log (2 / delta) + (round + 2 : ℝ) * Real.log 2 := by
  unfold adaptivePruneRoundDelta
  have hdeltaNe : delta ≠ 0 := ne_of_gt hdelta
  have hglobalNe : (2 / delta : ℝ) ≠ 0 := div_ne_zero (by norm_num) hdeltaNe
  have hroundNe : ((2 : ℝ) ^ (round + 2)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfactor : 2 / (delta / (2 : ℝ) ^ (round + 2)) =
      (2 / delta) * (2 : ℝ) ^ (round + 2) := by
    field_simp [hdeltaNe]
  rw [hfactor, Real.log_mul hglobalNe hroundNe, Real.log_pow]
  norm_num

/--
The executable Prune batch count is bounded by the source's global-plus-round
logarithmic budget, with its ceiling correction kept explicit.
-/
theorem fixedSampleBudget_lt_adaptivePruneRoundSourceBudget
    (lower upper delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) : ℝ) <
      2 / (upper - lower) ^ 2 *
        (Real.log (2 / delta) + (round + 2 : ℝ) * Real.log 2) + 1 := by
  have hschedule := adaptivePruneRoundDelta_pos_le_delta_div_four delta hdelta round
  have hscheduleLeOne : adaptivePruneRoundDelta delta round ≤ 1 :=
    hschedule.2.trans (by linarith)
  have hbudget := fixedSampleBudget_lt_realTarget_add_one lower upper
    (adaptivePruneRoundDelta delta round) hschedule.1 hscheduleLeOne
  rw [log_two_div_adaptivePruneRoundDelta delta hdelta round] at hbudget
  exact hbudget

/--
On the good-anchor event, the complete finite Prune cost envelope is bounded
by a single source-log factor at the last scheduled round.  This retains the
integer horizon and the ceiling correction instead of invoking asymptotics.
-/
theorem pruneComparisonEnvelope_le_sourceLogEnvelope
    (roundCount cutoff badCount : ℕ) (lower upper delta : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      (roundCount : ℝ) * ((cutoff : ℝ) + (badCount : ℝ)) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1) := by
  let sourceBudget : ℝ :=
    2 / (upper - lower) ^ 2 *
      (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1
  have hcutoffNonnegative : 0 ≤ (cutoff : ℝ) := Nat.cast_nonneg _
  have hbadNonnegative : 0 ≤ (badCount : ℝ) := Nat.cast_nonneg _
  have henvelopeNonnegative : 0 ≤ (cutoff : ℝ) + (badCount : ℝ) :=
    add_nonneg hcutoffNonnegative hbadNonnegative
  calc
    ∑ round : Fin roundCount,
        ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
          (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      ∑ _round : Fin roundCount, ((cutoff : ℝ) + (badCount : ℝ)) * sourceBudget := by
        apply Finset.sum_le_sum
        intro round _
        have hpow : delta ^ round.val ≤ 1 :=
          pow_le_one₀ (le_of_lt hdelta) hdeltaLeOne
        have hfactor :
            (cutoff : ℝ) + delta ^ round.val * (badCount : ℝ) ≤
              (cutoff : ℝ) + (badCount : ℝ) := by
          simpa [add_comm] using
            add_le_add_left (mul_le_mul_of_nonneg_right hpow hbadNonnegative)
              (cutoff : ℝ)
        have hroundBound := fixedSampleBudget_lt_adaptivePruneRoundSourceBudget lower upper
          delta round.val hdelta hdeltaLeOne
        have hroundLeHorizon : round.val + 2 ≤ roundCount + 1 := by
          omega
        have hlogTwoNonnegative : 0 ≤ Real.log 2 := by
          exact Real.log_nonneg (by norm_num)
        have hroundBudget :
            (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
              sourceBudget := by
          apply le_trans (le_of_lt hroundBound)
          dsimp [sourceBudget]
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left
          · apply add_le_add_right
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hroundLeHorizon)
              hlogTwoNonnegative
          · exact div_nonneg (by norm_num) (sq_nonneg _)
        calc
          ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
              (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
            ((cutoff : ℝ) + (badCount : ℝ)) *
              (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) :=
              mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg _)
          _ ≤ ((cutoff : ℝ) + (badCount : ℝ)) * sourceBudget :=
            mul_le_mul_of_nonneg_left hroundBudget henvelopeNonnegative
    _ = (roundCount : ℝ) * ((cutoff : ℝ) + (badCount : ℝ)) * sourceBudget := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = (roundCount : ℝ) * ((cutoff : ℝ) + (badCount : ℝ)) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1) := rfl

/--
The source's sharper Prune cost split keeps the geometric bad-arm contribution
outside the horizon factor.  In the normalized `delta ≤ 1 / 2` regime, its
finite sum is at most twice the initial bad-arm count.
-/
theorem pruneComparisonEnvelope_le_geometricSourceLogEnvelope
    (roundCount cutoff badCount : ℕ) (lower upper delta : ℝ)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1) := by
  let sourceBudget : ℝ :=
    2 / (upper - lower) ^ 2 *
      (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1
  have hdeltaNonnegative : 0 ≤ delta := le_of_lt hdelta
  have hcutoffNonnegative : 0 ≤ (cutoff : ℝ) := Nat.cast_nonneg _
  have hbadNonnegative : 0 ≤ (badCount : ℝ) := Nat.cast_nonneg _
  have hlogGlobalNonnegative : 0 ≤ Real.log (2 / delta) := by
    apply Real.log_nonneg
    apply (one_le_div₀ hdelta).mpr
    linarith
  have hlogTwoNonnegative : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsourceBudgetNonnegative : 0 ≤ sourceBudget := by
    dsimp [sourceBudget]
    apply add_nonneg
    · apply mul_nonneg
      · exact div_nonneg (by norm_num) (sq_nonneg _)
      · exact add_nonneg hlogGlobalNonnegative
          (mul_nonneg (by positivity) hlogTwoNonnegative)
    · norm_num
  have hgeometric : ∑ round : Fin roundCount, delta ^ round.val ≤ 2 := by
    calc
      ∑ round : Fin roundCount, delta ^ round.val =
          ∑ round ∈ Finset.range roundCount, delta ^ round := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro round hround
            simp [Finset.mem_range.mp hround]
      _ ≤ ∑ round ∈ Finset.range roundCount, (1 / 2 : ℝ) ^ round := by
        apply Finset.sum_le_sum
        intro round _
        exact pow_le_pow_left₀ hdeltaNonnegative hdeltaHalf round
      _ ≤ 2 := sum_geometric_two_le roundCount
  have hweight :
      ∑ round : Fin roundCount,
          ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) ≤
        (roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ) := by
    calc
      ∑ round : Fin roundCount,
          ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) =
          (∑ _round : Fin roundCount, (cutoff : ℝ)) +
            ∑ round : Fin roundCount, delta ^ round.val * (badCount : ℝ) := by
              rw [Finset.sum_add_distrib]
      _ = (roundCount : ℝ) * (cutoff : ℝ) +
            (∑ round : Fin roundCount, delta ^ round.val) * (badCount : ℝ) := by
              rw [← Finset.sum_mul]
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ (roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ) := by
        simpa [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hgeometric hbadNonnegative)
            ((roundCount : ℝ) * (cutoff : ℝ))
  calc
    ∑ round : Fin roundCount,
        ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
          (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      ∑ round : Fin roundCount,
        ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) * sourceBudget := by
          apply Finset.sum_le_sum
          intro round _
          have hweightNonnegative : 0 ≤
              (cutoff : ℝ) + delta ^ round.val * (badCount : ℝ) :=
            add_nonneg hcutoffNonnegative
              (mul_nonneg (pow_nonneg hdeltaNonnegative _) hbadNonnegative)
          have hroundBound := fixedSampleBudget_lt_adaptivePruneRoundSourceBudget lower upper
            delta round.val hdelta (by linarith)
          have hroundLeHorizon : round.val + 2 ≤ roundCount + 1 := by omega
          have hroundBudget :
              (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
                sourceBudget := by
            apply le_trans (le_of_lt hroundBound)
            dsimp [sourceBudget]
            apply add_le_add_left
            apply mul_le_mul_of_nonneg_left
            · apply add_le_add_right
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hroundLeHorizon)
                hlogTwoNonnegative
            · exact div_nonneg (by norm_num) (sq_nonneg _)
          exact mul_le_mul_of_nonneg_left hroundBudget hweightNonnegative
    _ = (∑ round : Fin roundCount,
        ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ))) * sourceBudget := by
          rw [Finset.sum_mul]
    _ ≤ ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) * sourceBudget :=
      mul_le_mul_of_nonneg_right hweight hsourceBudgetNonnegative
    _ = ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) *
        (2 / (upper - lower) ^ 2 *
          (Real.log (2 / delta) + (roundCount + 1 : ℝ) * Real.log 2) + 1) := rfl

/--
The first moment of the finite half-geometric series has its exact tail
formula.  This is the round-weighted counterpart of `sum_geometric_two_le`:
the source confidence schedule grows linearly in the round number, while the
number of bad arms contracts geometrically.
-/
theorem weighted_half_geometric_sum_add_tail (roundCount : ℕ) :
    (∑ round ∈ Finset.range roundCount, (round : ℝ) * (1 / 2 : ℝ) ^ round) +
      2 * (roundCount + 1 : ℝ) * (1 / 2 : ℝ) ^ roundCount = 2 := by
  induction roundCount with
  | zero => norm_num
  | succ round ih =>
      rw [Finset.sum_range_succ, pow_succ]
      norm_num [Nat.cast_add, Nat.cast_one] at ih ⊢
      linarith

/-- The round-weighted finite half-geometric series is at most two. -/
theorem weighted_half_geometric_sum_le_two (roundCount : ℕ) :
    ∑ round ∈ Finset.range roundCount, (round : ℝ) * (1 / 2 : ℝ) ^ round ≤ 2 := by
  have htailNonnegative : 0 ≤
      2 * (roundCount + 1 : ℝ) * (1 / 2 : ℝ) ^ roundCount := by positivity
  have hformula := weighted_half_geometric_sum_add_tail roundCount
  linarith

/-- The same first-moment bound for every contraction factor at most one half. -/
theorem weighted_geometric_sum_le_two
    (roundCount : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∑ round ∈ Finset.range roundCount, (round : ℝ) * delta ^ round ≤ 2 := by
  calc
    ∑ round ∈ Finset.range roundCount, (round : ℝ) * delta ^ round ≤
        ∑ round ∈ Finset.range roundCount, (round : ℝ) * (1 / 2 : ℝ) ^ round := by
          apply Finset.sum_le_sum
          intro round _
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hdelta hdeltaHalf round) (Nat.cast_nonneg _)
    _ ≤ 2 := weighted_half_geometric_sum_le_two roundCount

/-- The finite geometric mass bound for every contraction factor at most one half. -/
theorem geometric_sum_le_two
    (roundCount : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∑ round ∈ Finset.range roundCount, delta ^ round ≤ 2 := by
  calc
    ∑ round ∈ Finset.range roundCount, delta ^ round ≤
        ∑ round ∈ Finset.range roundCount, (1 / 2 : ℝ) ^ round := by
          apply Finset.sum_le_sum
          intro round _
          exact pow_le_pow_left₀ hdelta hdeltaHalf round
    _ ≤ 2 := sum_geometric_two_le roundCount

/--
Summing the source confidence logarithm over the cutoff contribution keeps the
round dependence in the cutoff term only.
-/
theorem prune_cutoff_log_sum_le
    (roundCount : ℕ) (logGlobal : ℝ) :
    ∑ round ∈ Finset.range roundCount,
        (logGlobal + ((round : ℝ) + 2) * Real.log 2) ≤
      (roundCount : ℝ) *
        (logGlobal + ((roundCount : ℝ) + 1) * Real.log 2) := by
  have hlogTwoNonnegative : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    ∑ round ∈ Finset.range roundCount,
        (logGlobal + ((round : ℝ) + 2) * Real.log 2) ≤
      ∑ _round ∈ Finset.range roundCount,
        (logGlobal + ((roundCount : ℝ) + 1) * Real.log 2) := by
          apply Finset.sum_le_sum
          intro round hround
          have hroundLt : round < roundCount := Finset.mem_range.mp hround
          have hroundLe : round + 2 ≤ roundCount + 1 := by omega
          have hroundLeReal : (round : ℝ) + 2 ≤ (roundCount : ℝ) + 1 := by
            exact_mod_cast hroundLe
          simpa [add_comm] using
            (add_le_add_left
              (mul_le_mul_of_nonneg_right hroundLeReal hlogTwoNonnegative)
              logGlobal)
    _ = (roundCount : ℝ) *
        (logGlobal + ((roundCount : ℝ) + 1) * Real.log 2) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/--
The geometrically shrinking bad-arm contribution pays only a constant total
round-index penalty under the source's at-most-half contraction.
-/
theorem prune_geometric_log_sum_le
    (roundCount : ℕ) (delta logGlobal : ℝ)
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2)
    (hlogGlobal : 0 ≤ logGlobal) :
    ∑ round ∈ Finset.range roundCount,
        (delta ^ round * (logGlobal + ((round : ℝ) + 2) * Real.log 2)) ≤
      2 * logGlobal + 6 * Real.log 2 := by
  have hgeometric := geometric_sum_le_two roundCount delta hdelta hdeltaHalf
  have hweighted := weighted_geometric_sum_le_two roundCount delta hdelta hdeltaHalf
  have hlogTwoNonnegative : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hgeometricLog :
      (∑ round ∈ Finset.range roundCount, delta ^ round) * logGlobal ≤
        2 * logGlobal :=
    mul_le_mul_of_nonneg_right hgeometric hlogGlobal
  have hweightedLog :
      (∑ round ∈ Finset.range roundCount, (round : ℝ) * delta ^ round) * Real.log 2 ≤
        2 * Real.log 2 :=
    mul_le_mul_of_nonneg_right hweighted hlogTwoNonnegative
  have htailLog :
      2 * (∑ round ∈ Finset.range roundCount, delta ^ round) * Real.log 2 ≤
        4 * Real.log 2 := by
    calc
      2 * (∑ round ∈ Finset.range roundCount, delta ^ round) * Real.log 2 =
          (∑ round ∈ Finset.range roundCount, delta ^ round) * (2 * Real.log 2) := by ring
      _ ≤ 2 * (2 * Real.log 2) :=
        mul_le_mul_of_nonneg_right hgeometric (by positivity)
      _ = 4 * Real.log 2 := by ring
  calc
    ∑ round ∈ Finset.range roundCount,
        (delta ^ round * (logGlobal + ((round : ℝ) + 2) * Real.log 2)) =
      ∑ round ∈ Finset.range roundCount,
        (delta ^ round * logGlobal +
          ((round : ℝ) * delta ^ round) * Real.log 2 +
            2 * delta ^ round * Real.log 2) := by
              apply Finset.sum_congr rfl
              intro round _
              ring
    _ =
      (∑ round ∈ Finset.range roundCount, delta ^ round) * logGlobal +
        (∑ round ∈ Finset.range roundCount, (round : ℝ) * delta ^ round) * Real.log 2 +
          2 * (∑ round ∈ Finset.range roundCount, delta ^ round) * Real.log 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
            have hfirst :
                (∑ round ∈ Finset.range roundCount, delta ^ round * logGlobal) =
                  (∑ round ∈ Finset.range roundCount, delta ^ round) * logGlobal := by
              rw [Finset.sum_mul]
            have hsecond :
                (∑ round ∈ Finset.range roundCount,
                    (round : ℝ) * delta ^ round * Real.log 2) =
                  (∑ round ∈ Finset.range roundCount,
                    (round : ℝ) * delta ^ round) * Real.log 2 := by
              rw [Finset.sum_mul]
            have hthird :
                (∑ round ∈ Finset.range roundCount,
                    2 * delta ^ round * Real.log 2) =
                  2 * (∑ round ∈ Finset.range roundCount, delta ^ round) * Real.log 2 := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
            rw [hfirst, hsecond, hthird]
    _ ≤ 2 * logGlobal + 6 * Real.log 2 := by linarith

/--
The executed-round resource envelope has no cutoff term: on every round that
actually runs, the active set is at most twice the geometrically contracting
bad population.  This lemma sums the resulting ceiling-corrected Compare
budgets before specializing the initial bad population to the full carrier.
-/
theorem two_mul_geometric_pruneComparisonEnvelope_le
    (roundCount badCount : ℕ) (lower upper scheduleDelta contraction : ℝ)
    (hschedule : 0 < scheduleDelta) (hscheduleHalf : scheduleDelta ≤ 1 / 2)
    (hcontraction : 0 ≤ contraction) (hcontractionHalf : contraction ≤ 1 / 2) :
    ∑ round : Fin roundCount,
      (2 * contraction ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper
          (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ) ≤
      2 * (badCount : ℝ) *
        ((2 / (upper - lower) ^ 2) *
            (2 * Real.log (2 / scheduleDelta) + 6 * Real.log 2) + 2) := by
  let logGlobal : ℝ := Real.log (2 / scheduleDelta)
  let sourceFactor : ℝ := 2 / (upper - lower) ^ 2
  let roundLog : ℕ → ℝ := fun round =>
    logGlobal + ((round : ℝ) + 2) * Real.log 2
  have hbadNonnegative : 0 ≤ (badCount : ℝ) := Nat.cast_nonneg _
  have hlogGlobalNonnegative : 0 ≤ logGlobal := by
    dsimp [logGlobal]
    apply Real.log_nonneg
    exact (one_le_div₀ hschedule).2 (by linarith)
  have hsourceFactorNonnegative : 0 ≤ sourceFactor := by
    dsimp [sourceFactor]
    positivity
  have hlogSum := prune_geometric_log_sum_le roundCount contraction logGlobal
    hcontraction hcontractionHalf hlogGlobalNonnegative
  have hmass := geometric_sum_le_two roundCount contraction hcontraction hcontractionHalf
  have hbatchBound :
      ∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round) : ℝ) ≤
      ∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1) := by
    apply Finset.sum_le_sum
    intro round _
    have hweight : 0 ≤ 2 * contraction ^ round * (badCount : ℝ) := by positivity
    have hroundBound := fixedSampleBudget_lt_adaptivePruneRoundSourceBudget lower upper
      scheduleDelta round hschedule (by linarith : scheduleDelta ≤ 1)
    dsimp [sourceFactor, roundLog]
    exact mul_le_mul_of_nonneg_left (le_of_lt hroundBound) hweight
  have hidentity :
      (∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1)) =
      2 * (badCount : ℝ) *
        (sourceFactor *
            (∑ round ∈ Finset.range roundCount,
              contraction ^ round * roundLog round) +
          ∑ round ∈ Finset.range roundCount, contraction ^ round) := by
    calc
      (∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1)) =
        ∑ round ∈ Finset.range roundCount,
          (2 * (badCount : ℝ) * sourceFactor *
              (contraction ^ round * roundLog round) +
            2 * (badCount : ℝ) * contraction ^ round) := by
              apply Finset.sum_congr rfl
              intro round _
              ring
      _ = 2 * (badCount : ℝ) * sourceFactor *
            (∑ round ∈ Finset.range roundCount,
              contraction ^ round * roundLog round) +
          2 * (badCount : ℝ) *
            (∑ round ∈ Finset.range roundCount, contraction ^ round) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (badCount : ℝ) *
          (sourceFactor *
              (∑ round ∈ Finset.range roundCount,
                contraction ^ round * roundLog round) +
            ∑ round ∈ Finset.range roundCount, contraction ^ round) := by ring
  have hfinEq :
      (∑ round : Fin roundCount,
        (2 * contraction ^ round.val * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) =
      ∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round) : ℝ) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro round hround
    simp [Finset.mem_range.mp hround]
  rw [hfinEq]
  calc
    ∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round) : ℝ) ≤
      ∑ round ∈ Finset.range roundCount,
        (2 * contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1) := hbatchBound
    _ = 2 * (badCount : ℝ) *
        (sourceFactor *
            (∑ round ∈ Finset.range roundCount,
              contraction ^ round * roundLog round) +
          ∑ round ∈ Finset.range roundCount, contraction ^ round) := hidentity
    _ ≤ 2 * (badCount : ℝ) *
        (sourceFactor * (2 * logGlobal + 6 * Real.log 2) + 2) := by
          gcongr
    _ = 2 * (badCount : ℝ) *
        ((2 / (upper - lower) ^ 2) *
            (2 * Real.log (2 / scheduleDelta) + 6 * Real.log 2) + 2) := by
          rfl

/--
The sharp finite Prune comparison envelope.  Unlike
`pruneComparisonEnvelope_le_geometricSourceLogEnvelope`, this keeps the
round-growing confidence logarithm inside the geometrically shrinking bad-arm
sum.  Consequently the bad-arm term has no artificial horizon factor.
-/
theorem pruneComparisonEnvelope_le_sharpGeometricSourceLogEnvelope_of_contraction
    (roundCount cutoff badCount : ℕ) (lower upper scheduleDelta contraction : ℝ)
    (hschedule : 0 < scheduleDelta) (hscheduleHalf : scheduleDelta ≤ 1 / 2)
    (hcontraction : 0 ≤ contraction) (hcontractionHalf : contraction ≤ 1 / 2) :
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + contraction ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper
          (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ) ≤
      (2 / (upper - lower) ^ 2) *
        ((cutoff : ℝ) * (roundCount : ℝ) *
            (Real.log (2 / scheduleDelta) + ((roundCount : ℝ) + 1) * Real.log 2) +
          (badCount : ℝ) * (2 * Real.log (2 / scheduleDelta) + 6 * Real.log 2)) +
        ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) := by
  let logGlobal : ℝ := Real.log (2 / scheduleDelta)
  let sourceFactor : ℝ := 2 / (upper - lower) ^ 2
  let roundLog : ℕ → ℝ := fun round =>
    logGlobal + ((round : ℝ) + 2) * Real.log 2
  have hcutoffNonnegative : 0 ≤ (cutoff : ℝ) := Nat.cast_nonneg _
  have hbadNonnegative : 0 ≤ (badCount : ℝ) := Nat.cast_nonneg _
  have hsourceFactorNonnegative : 0 ≤ sourceFactor := by
    dsimp [sourceFactor]
    exact div_nonneg (by norm_num) (sq_nonneg _)
  have hlogGlobalNonnegative : 0 ≤ logGlobal := by
    dsimp [logGlobal]
    apply Real.log_nonneg
    apply (one_le_div₀ hschedule).mpr
    linarith
  have hgeometric := geometric_sum_le_two roundCount contraction hcontraction hcontractionHalf
  have hcutoffSum := prune_cutoff_log_sum_le roundCount logGlobal
  have hbadSum := prune_geometric_log_sum_le roundCount contraction logGlobal hcontraction
    hcontractionHalf hlogGlobalNonnegative
  have hcutoffTerm :
      (cutoff : ℝ) * (∑ round ∈ Finset.range roundCount, roundLog round) ≤
        (cutoff : ℝ) * ((roundCount : ℝ) *
          (logGlobal + ((roundCount : ℝ) + 1) * Real.log 2)) := by
    exact mul_le_mul_of_nonneg_left hcutoffSum hcutoffNonnegative
  have hbadTerm :
      (badCount : ℝ) * (∑ round ∈ Finset.range roundCount,
        contraction ^ round * roundLog round) ≤
        (badCount : ℝ) * (2 * logGlobal + 6 * Real.log 2) := by
    exact mul_le_mul_of_nonneg_left hbadSum hbadNonnegative
  have hbadMass :
      (badCount : ℝ) * (∑ round ∈ Finset.range roundCount, contraction ^ round) ≤
        2 * (badCount : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hgeometric hbadNonnegative
    simpa [mul_comm] using hscaled
  have hbatchBound :
      ∑ round ∈ Finset.range roundCount,
        ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round) : ℝ) ≤
        ∑ round ∈ Finset.range roundCount,
          ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
            (sourceFactor * roundLog round + 1) := by
      apply Finset.sum_le_sum
      intro round _
      have hweightNonnegative :
          0 ≤ (cutoff : ℝ) + contraction ^ round * (badCount : ℝ) :=
        add_nonneg hcutoffNonnegative
          (mul_nonneg (pow_nonneg hcontraction _) hbadNonnegative)
      have hroundBound := fixedSampleBudget_lt_adaptivePruneRoundSourceBudget lower upper
        scheduleDelta round hschedule (by linarith : scheduleDelta ≤ 1)
      dsimp [sourceFactor, roundLog]
      exact mul_le_mul_of_nonneg_left (le_of_lt hroundBound) hweightNonnegative
  have hsumIdentity :
      (∑ round ∈ Finset.range roundCount,
        ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1)) =
        sourceFactor *
          ((cutoff : ℝ) * (∑ round ∈ Finset.range roundCount, roundLog round) +
            (badCount : ℝ) * (∑ round ∈ Finset.range roundCount,
              contraction ^ round * roundLog round)) +
          ((roundCount : ℝ) * (cutoff : ℝ) +
            (badCount : ℝ) * (∑ round ∈ Finset.range roundCount, contraction ^ round)) := by
      calc
        (∑ round ∈ Finset.range roundCount,
          ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
            (sourceFactor * roundLog round + 1)) =
          ∑ round ∈ Finset.range roundCount,
            (sourceFactor * (cutoff : ℝ) * roundLog round +
              sourceFactor * (badCount : ℝ) * (contraction ^ round * roundLog round) +
              (cutoff : ℝ) + (badCount : ℝ) * contraction ^ round) := by
                apply Finset.sum_congr rfl
                intro round _
                ring
        _ = sourceFactor *
            ((cutoff : ℝ) * (∑ round ∈ Finset.range roundCount, roundLog round) +
              (badCount : ℝ) * (∑ round ∈ Finset.range roundCount,
                contraction ^ round * roundLog round)) +
            ((roundCount : ℝ) * (cutoff : ℝ) +
              (badCount : ℝ) *
                (∑ round ∈ Finset.range roundCount, contraction ^ round)) := by
                simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
                  nsmul_eq_mul]
                rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
                ring
  have hfinEq :
      (∑ round : Fin roundCount,
        ((cutoff : ℝ) + contraction ^ round.val * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round.val) : ℝ)) =
        ∑ round ∈ Finset.range roundCount,
          ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
            (fixedSampleBudget lower upper
              (adaptivePruneRoundDelta scheduleDelta round) : ℝ) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro round hround
    simp [Finset.mem_range.mp hround]
  rw [hfinEq]
  calc
    ∑ round ∈ Finset.range roundCount,
        ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
          (fixedSampleBudget lower upper
            (adaptivePruneRoundDelta scheduleDelta round) : ℝ) ≤
      ∑ round ∈ Finset.range roundCount,
        ((cutoff : ℝ) + contraction ^ round * (badCount : ℝ)) *
          (sourceFactor * roundLog round + 1) := hbatchBound
    _ = sourceFactor *
        ((cutoff : ℝ) * (∑ round ∈ Finset.range roundCount, roundLog round) +
          (badCount : ℝ) * (∑ round ∈ Finset.range roundCount,
            contraction ^ round * roundLog round)) +
        ((roundCount : ℝ) * (cutoff : ℝ) +
          (badCount : ℝ) *
            (∑ round ∈ Finset.range roundCount, contraction ^ round)) := hsumIdentity
    _ ≤ sourceFactor *
        ((cutoff : ℝ) * ((roundCount : ℝ) *
            (logGlobal + ((roundCount : ℝ) + 1) * Real.log 2)) +
          (badCount : ℝ) * (2 * logGlobal + 6 * Real.log 2)) +
        ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) := by
          apply add_le_add
          · apply mul_le_mul_of_nonneg_left
              (add_le_add hcutoffTerm hbadTerm) hsourceFactorNonnegative
          · simpa [add_comm] using
              (add_le_add_left hbadMass ((roundCount : ℝ) * (cutoff : ℝ)))
    _ = (2 / (upper - lower) ^ 2) *
        ((cutoff : ℝ) * (roundCount : ℝ) *
            (Real.log (2 / scheduleDelta) + ((roundCount : ℝ) + 1) * Real.log 2) +
          (badCount : ℝ) *
            (2 * Real.log (2 / scheduleDelta) + 6 * Real.log 2)) +
        ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) := by
          dsimp [sourceFactor, logGlobal]
          ring

/-- The original Lemma 15 envelope, with one shared factor, as a specialization. -/
theorem pruneComparisonEnvelope_le_sharpGeometricSourceLogEnvelope
    (roundCount cutoff badCount : ℕ) (lower upper delta : ℝ)
    (hdelta : 0 < delta) (hdeltaHalf : delta ≤ 1 / 2) :
    ∑ round : Fin roundCount,
      ((cutoff : ℝ) + delta ^ round.val * (badCount : ℝ)) *
        (fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round.val) : ℝ) ≤
      (2 / (upper - lower) ^ 2) *
        ((cutoff : ℝ) * (roundCount : ℝ) *
            (Real.log (2 / delta) + ((roundCount : ℝ) + 1) * Real.log 2) +
          (badCount : ℝ) * (2 * Real.log (2 / delta) + 6 * Real.log 2)) +
        ((roundCount : ℝ) * (cutoff : ℝ) + 2 * (badCount : ℝ)) := by
  exact pruneComparisonEnvelope_le_sharpGeometricSourceLogEnvelope_of_contraction
    roundCount cutoff badCount lower upper delta delta hdelta hdeltaHalf hdelta.le hdeltaHalf

/-- The elementary finite geometric estimate used to cap Lemma 15 by `n` rounds. -/
theorem card_mul_half_pow_card_le_one (card : ℕ) :
    (card : ℝ) * (1 / 2 : ℝ) ^ card ≤ 1 := by
  have hpowPos : 0 < (2 : ℝ) ^ card := by positivity
  have hcardPow : (card : ℝ) ≤ (2 : ℝ) ^ card := by
    exact_mod_cast (Nat.lt_two_pow_self (n := card)).le
  calc
    (card : ℝ) * (1 / 2 : ℝ) ^ card = (card : ℝ) / (2 : ℝ) ^ card := by
      rw [one_div_pow]
      ring
    _ ≤ 1 := (div_le_one₀ hpowPos).mpr hcardPow

/-- The active threshold-nonbetter arms counted in the size part of Lemma 15. -/
noncomputable def pruneBadArms {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    (active : Finset Arm) : Finset Arm :=
  active.filter fun arm => preferenceGap arm anchor ≤ lower

/--
The source's `t ≤ n` geometric target, in its normalized `delta ≤ 1 / 2`
regime: after one cardinality-many rounds, the initial bad population is below
the good-anchor cutoff.
-/
theorem sourceLemma15_card_round_geometric_target
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    (initial : Finset Arm) (cutoff : ℕ) (delta : ℝ)
    (hcutoff : 0 < cutoff) (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    delta ^ Fintype.card Arm *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff := by
  have hbadCard : ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤
      (Fintype.card Arm : ℝ) := by
    dsimp [pruneBadArms]
    have hfilter : (initial.filter fun arm => preferenceGap arm anchor ≤ lower).card ≤ initial.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hinitial : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    exact_mod_cast hfilter.trans hinitial
  have hpowNonneg : 0 ≤ delta ^ Fintype.card Arm := pow_nonneg hdelta _
  have hpowHalf : delta ^ Fintype.card Arm ≤ (1 / 2 : ℝ) ^ Fintype.card Arm :=
    pow_le_pow_left₀ hdelta hdeltaHalf _
  have hhalf : (Fintype.card Arm : ℝ) * (1 / 2 : ℝ) ^ Fintype.card Arm ≤ 1 :=
    card_mul_half_pow_card_le_one (Fintype.card Arm)
  calc
    delta ^ Fintype.card Arm *
        ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤
        delta ^ Fintype.card Arm * (Fintype.card Arm : ℝ) :=
      mul_le_mul_of_nonneg_left hbadCard hpowNonneg
    _ ≤ (1 / 2 : ℝ) ^ Fintype.card Arm * (Fintype.card Arm : ℝ) :=
      mul_le_mul_of_nonneg_right hpowHalf (Nat.cast_nonneg _)
    _ = (Fintype.card Arm : ℝ) * (1 / 2 : ℝ) ^ Fintype.card Arm := by ring
    _ ≤ 1 := hhalf
    _ ≤ cutoff := by exact_mod_cast Nat.succ_le_iff.mpr hcutoff

/--
At any Prune stage, the good-anchor condition bounds the active population by
its at-most-`cutoff` threshold-better part plus its bad-arm population.
-/
theorem active_card_le_cutoff_add_badCard_of_goodAnchor
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (active : Finset Arm) (hanchor : GoodAnchor preferenceGap lower cutoff anchor) :
    active.card ≤ cutoff + (pruneBadArms preferenceGap lower anchor active).card := by
  let good : Finset Arm := active.filter fun arm => lower < preferenceGap arm anchor
  let bad : Finset Arm := pruneBadArms preferenceGap lower anchor active
  have hgood : good.card ≤ cutoff := by
    have hsubset : good ⊆ (Finset.univ.filter fun arm => lower < preferenceGap arm anchor) := by
      intro arm harm
      simp only [good, Finset.mem_filter] at harm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, harm.2⟩
    exact (Finset.card_le_card hsubset).trans (by simpa [GoodAnchor] using hanchor)
  have hcover : active ⊆ good ∪ bad := by
    intro arm harm
    by_cases hlarge : lower < preferenceGap arm anchor
    · exact Finset.mem_union_left _ (by simp [good, harm, hlarge])
    · exact Finset.mem_union_right _ (by simp [bad, pruneBadArms, harm, le_of_not_gt hlarge])
  calc
    active.card ≤ (good ∪ bad).card := Finset.card_le_card hcover
    _ ≤ good.card + bad.card := Finset.card_union_le _ _
    _ ≤ cutoff + bad.card := Nat.add_le_add_right hgood _
    _ = cutoff + (pruneBadArms preferenceGap lower anchor active).card := rfl

/-- Restricting the active set can only restrict its threshold-nonbetter arms. -/
theorem pruneBadArms_subset_of_subset {Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    {smaller larger : Finset Arm} (hsubset : smaller ⊆ larger) :
    pruneBadArms preferenceGap lower anchor smaller ⊆
      pruneBadArms preferenceGap lower anchor larger := by
  intro arm harm
  simp only [pruneBadArms, Finset.mem_filter] at harm ⊢
  exact ⟨hsubset harm.1, harm.2⟩

/-- The threshold-nonbetter count is nonincreasing along every indexed Prune schedule. -/
theorem indexedPruneRounds_badCard_monotone {Ω Arm : Type*} [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    (round : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) :
    ((pruneBadArms preferenceGap lower anchor
      (indexedPruneRounds (round + 1) decision outcome active)).card : ℝ) ≤
      ((pruneBadArms preferenceGap lower anchor
        (indexedPruneRounds round decision outcome active)).card : ℝ) := by
  rw [indexedPruneRounds_succ]
  exact_mod_cast Finset.card_le_card
    (pruneBadArms_subset_of_subset preferenceGap lower anchor
      (pruneRound_subset (indexedPruneRounds round decision outcome active)
        (fun arm => decision round arm outcome)))

/--
An active set is at most twice the good-anchor cutoff once its
threshold-nonbetter subpopulation has at most that cutoff.
-/
theorem pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (active : Finset Arm)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hbad : (pruneBadArms preferenceGap lower anchor active).card ≤ cutoff) :
    active.card ≤ 2 * cutoff := by
  have hround := pruneRound_card_le_two_mul_of_goodAnchor_and_badSurvivors
    preferenceGap lower cutoff anchor active (fun _ => .upper) hanchor
    (by simpa [pruneBadArms, pruneRound] using hbad)
  simpa [pruneRound] using hround

/--
The deterministic size conclusion in Lemma 15.  The only stochastic input is
the roundwise contraction implication; its source conditional concentration
proof is kept as a separate probability bridge.
-/
theorem indexedPruneRounds_card_le_two_mul_of_geometricBadContraction
    {Ω Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (cutoff : ℕ) (anchor : Arm)
    (roundCount : ℕ) (decision : ℕ → Arm → Ω → CompareDecision)
    (outcome : Ω) (active : Finset Arm) (delta : ℝ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hdelta : 0 ≤ delta)
    (hcontract : ∀ round, cutoff <
      ((pruneBadArms preferenceGap lower anchor
        (indexedPruneRounds round decision outcome active)).card : ℝ) →
      ((pruneBadArms preferenceGap lower anchor
        (indexedPruneRounds (round + 1) decision outcome active)).card : ℝ) ≤
        delta * ((pruneBadArms preferenceGap lower anchor
          (indexedPruneRounds round decision outcome active)).card : ℝ))
    (htarget : delta ^ roundCount *
      ((pruneBadArms preferenceGap lower anchor active).card : ℝ) ≤ cutoff) :
    (indexedPruneRounds roundCount decision outcome active).card ≤ 2 * cutoff := by
  let badCount : ℕ → ℝ := fun round =>
    ((pruneBadArms preferenceGap lower anchor
      (indexedPruneRounds round decision outcome active)).card : ℝ)
  have hbadFinal : badCount roundCount ≤ cutoff := by
    apply geometric_contraction_reaches_cutoff badCount delta cutoff roundCount hdelta
    · intro round
      exact indexedPruneRounds_badCard_monotone preferenceGap lower anchor round
        decision outcome active
    · intro round hlarge
      exact hcontract round hlarge
    · simpa [badCount] using htarget
  apply pruneActive_card_le_two_mul_of_goodAnchor_and_badArms
    preferenceGap lower cutoff anchor
    (indexedPruneRounds roundCount decision outcome active) hanchor
  exact (Nat.cast_le (α := ℝ)).mp (by simpa [badCount] using hbadFinal)

end FalahatgarEtAl2017MaxingRanking
