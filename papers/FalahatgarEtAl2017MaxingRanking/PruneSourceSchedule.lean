import FalahatgarEtAl2017MaxingRanking.PruneRoundContraction
import FalahatgarEtAl2017MaxingRanking.PruneSourceNumerics

/-!
# Discrete source schedule for Prune

Algorithm 2 starts its round counter at one and guards it by `t < (log n)²`.
This module records that literal finite horizon using the already-established
base-two integer reading of `log`; it also proves that the Lemma-15 geometric
target is already met by the earlier logarithmic prefix.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL

/--
Algorithm 2 numbers rounds from one and continues while `t < (log n)²`.
`sourcePruneRoundCount` is therefore the number of executed zero-indexed
rounds under the formalized base-two integer reading of that guard.
-/
def sourcePruneRoundCount (armCount : ℕ) : ℕ :=
  (Nat.log 2 armCount) ^ 2 - 1

/-- A logarithmic prefix is contained in Algorithm 2's literal squared-log horizon. -/
theorem log_two_pred_le_sourcePruneRoundCount (armCount : ℕ) :
    Nat.log 2 armCount - 1 ≤ sourcePruneRoundCount armCount := by
  unfold sourcePruneRoundCount
  apply Nat.sub_le_sub_right
  by_cases hlogZero : Nat.log 2 armCount = 0
  · simp [hlogZero]
  · exact le_self_pow (a := Nat.log 2 armCount) (n := 2)
      (Nat.one_le_iff_ne_zero.mpr hlogZero) (by norm_num)

/-- Beyond the small boundary cases, a square is dominated by the corresponding power of two. -/
private theorem square_le_two_pow_of_four_le (k : ℕ) (hk : 4 ≤ k) : k ^ 2 ≤ 2 ^ k := by
  have hlinear : ∀ k : ℕ, 4 ≤ k → 2 * k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => intro; omega
    | succ k ih =>
        intro hksucc
        by_cases hkThree : k = 3
        · subst k
          norm_num
        · have hkFour : 4 ≤ k := by omega
          have htwo : 2 ≤ 2 ^ k := by
            calc
              2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
          calc
            2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
            _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add (ih hkFour) htwo
            _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hkThree : k = 3
      · subst k
        norm_num
      · have hkFour : 4 ≤ k := by omega
        calc
          (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
          _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add (ih hkFour) (hlinear k hkFour)
          _ = 2 ^ (k + 1) := by rw [pow_succ]; omega

/-- The literal squared-log horizon has at most one round per arm. -/
theorem sourcePruneRoundCount_le_card (armCount : ℕ) :
    sourcePruneRoundCount armCount ≤ armCount := by
  unfold sourcePruneRoundCount
  by_cases hzero : armCount = 0
  · simp [hzero]
  · let logarithm := Nat.log 2 armCount
    have hpow : logarithm ^ 2 - 1 ≤ 2 ^ logarithm := by
      by_cases hsmall : logarithm ≤ 3
      · interval_cases logarithm <;> norm_num
      · exact (Nat.sub_le _ _).trans
          (square_le_two_pow_of_four_le logarithm (by omega))
    exact hpow.trans (Nat.pow_log_le_self 2 hzero)

/-- A finite storage cap for all batches in Algorithm 2's source horizon. -/
noncomputable def sourcePruneMaxBatch {Arm : Type*} [Fintype Arm]
    (lower upper delta : ℝ) : ℕ :=
  (Finset.range (sourcePruneRoundCount (Fintype.card Arm) + 1)).sup' (by
    exact ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩)
    (fun round => fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))

/-- Every actual Prune round fits in the finite source-horizon storage cap. -/
theorem fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round
    {Arm : Type*} [Fintype Arm] (lower upper delta : ℝ) (round : ℕ)
    (hround : round < sourcePruneRoundCount (Fintype.card Arm)) :
    fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤
      sourcePruneMaxBatch (Arm := Arm) lower upper delta := by
  unfold sourcePruneMaxBatch
  apply Finset.le_sup' (fun round =>
    fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round))
  simp only [Finset.mem_range]
  omega

/-- The storage cap also covers the earlier logarithmic prefix used by legacy helpers. -/
theorem fixedSampleBudget_le_sourcePruneMaxBatch
    {Arm : Type*} [Fintype Arm] (lower upper delta : ℝ) (round : ℕ)
    (hround : round < Nat.log 2 (Fintype.card Arm) - 1) :
    fixedSampleBudget lower upper (adaptivePruneRoundDelta delta round) ≤
      sourcePruneMaxBatch (Arm := Arm) lower upper delta := by
  apply fixedSampleBudget_le_sourcePruneMaxBatch_of_source_round lower upper delta round
  exact lt_of_lt_of_le hround
    (log_two_pred_le_sourcePruneRoundCount (Fintype.card Arm))

/-- A cardinality times the final geometric weight before the log-two cap is below four. -/
theorem card_mul_half_pow_log_two_pred_lt_four (card : ℕ) (hcard : 3 ≤ card) :
    (card : ℝ) * (1 / 2 : ℝ) ^ (Nat.log 2 card - 1) < 4 := by
  let rounds := Nat.log 2 card
  have hroundsPos : 0 < rounds := by
    dsimp [rounds]
    exact Nat.log_pos Nat.one_lt_two (by omega)
  have hpowPos : 0 < (2 : ℝ) ^ (rounds - 1) := by positivity
  have hcardPowNat : card < 2 ^ (rounds + 1) := by
    simpa [rounds] using (Nat.lt_pow_succ_log_self Nat.one_lt_two card)
  have hcardPow : (card : ℝ) < (2 : ℝ) ^ (rounds + 1) := by
    exact_mod_cast hcardPowNat
  calc
    (card : ℝ) * (1 / 2 : ℝ) ^ (rounds - 1) =
        (card : ℝ) / (2 : ℝ) ^ (rounds - 1) := by
          rw [one_div_pow]
          ring
    _ < (2 : ℝ) ^ (rounds + 1) / (2 : ℝ) ^ (rounds - 1) :=
      (div_lt_div_iff_of_pos_right hpowPos).mpr hcardPow
    _ = 4 := by
      have hexp : rounds + 1 = (rounds - 1) + 2 := by omega
      rw [hexp, pow_add]
      field_simp [ne_of_gt hpowPos]
      norm_num

/-- The source Lemma-15 square-root cutoff is at least four in the nontrivial case. -/
theorem four_le_cutoff_of_sourceLemma15_sqrt
    (card cutoff : ℕ) (hcard : 3 ≤ card)
    (hcutoff : Real.sqrt (6 * (card : ℝ) * Real.log (card : ℝ)) ≤ (cutoff : ℝ)) :
    4 ≤ cutoff := by
  have hcardPos : 0 < (card : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hcard
  have hlogOne : 1 ≤ Real.log (card : ℝ) := by
    apply (Real.le_log_iff_exp_le hcardPos).mpr
    calc
      Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
      _ ≤ (card : ℝ) := by exact_mod_cast hcard
  have hinside : (4 : ℝ) ^ 2 ≤ 6 * (card : ℝ) * Real.log (card : ℝ) := by
    have hcardThree : (3 : ℝ) ≤ (card : ℝ) := by exact_mod_cast hcard
    nlinarith
  have hsqrtFour : (4 : ℝ) ≤ Real.sqrt (6 * (card : ℝ) * Real.log (card : ℝ)) :=
    Real.le_sqrt_of_sq_le hinside
  exact_mod_cast hsqrtFour.trans hcutoff

/--
The geometric bad-arm target is reached by Algorithm 2's integer
`Nat.log 2 n - 1` round cap under the source-normalized `delta ≤ 1 / 2`
regime and Lemma-15 cutoff condition.
-/
theorem sourceLemma15_log_two_pred_round_geometric_target
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    (initial : Finset Arm) (cutoff : ℕ) (delta : ℝ)
    (hcard : 3 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    delta ^ (Nat.log 2 (Fintype.card Arm) - 1) *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff := by
  let rounds := Nat.log 2 (Fintype.card Arm)
  have hbadCard : ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤
      (Fintype.card Arm : ℝ) := by
    dsimp [pruneBadArms]
    have hfilter : (initial.filter fun arm => preferenceGap arm anchor ≤ lower).card ≤ initial.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hinitial : initial.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ initial)
    exact_mod_cast hfilter.trans hinitial
  have hpowNonneg : 0 ≤ delta ^ (rounds - 1) := pow_nonneg hdelta _
  have hpowHalf : delta ^ (rounds - 1) ≤ (1 / 2 : ℝ) ^ (rounds - 1) :=
    pow_le_pow_left₀ hdelta hdeltaHalf _
  have hhalf : (Fintype.card Arm : ℝ) * (1 / 2 : ℝ) ^ (rounds - 1) < 4 := by
    simpa [rounds] using card_mul_half_pow_log_two_pred_lt_four
      (Fintype.card Arm) hcard
  have hcutoffFour : (4 : ℝ) ≤ cutoff := by
    exact_mod_cast four_le_cutoff_of_sourceLemma15_sqrt
      (Fintype.card Arm) cutoff hcard hcutoff
  calc
    delta ^ (Nat.log 2 (Fintype.card Arm) - 1) *
        ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) =
        delta ^ (rounds - 1) * ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) := by rfl
    _ ≤ delta ^ (rounds - 1) * (Fintype.card Arm : ℝ) :=
      mul_le_mul_of_nonneg_left hbadCard hpowNonneg
    _ ≤ (1 / 2 : ℝ) ^ (rounds - 1) * (Fintype.card Arm : ℝ) :=
      mul_le_mul_of_nonneg_right hpowHalf (Nat.cast_nonneg _)
    _ = (Fintype.card Arm : ℝ) * (1 / 2 : ℝ) ^ (rounds - 1) := by ring
    _ ≤ 4 := hhalf.le
    _ ≤ cutoff := hcutoffFour

/-- The earlier logarithmic target remains valid at Algorithm 2's literal horizon. -/
theorem sourceLemma15_source_round_geometric_target
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ) (lower : ℝ) (anchor : Arm)
    (initial : Finset Arm) (cutoff : ℕ) (delta : ℝ)
    (hcard : 3 ≤ Fintype.card Arm)
    (hcutoff : Real.sqrt (6 * (Fintype.card Arm : ℝ) *
      Real.log (Fintype.card Arm : ℝ)) ≤ (cutoff : ℝ))
    (hdelta : 0 ≤ delta) (hdeltaHalf : delta ≤ 1 / 2) :
    delta ^ sourcePruneRoundCount (Fintype.card Arm) *
      ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤ cutoff := by
  have hdeltaOne : delta ≤ 1 := hdeltaHalf.trans (by norm_num)
  have hprefix := sourceLemma15_log_two_pred_round_geometric_target
    preferenceGap lower anchor initial cutoff delta hcard hcutoff hdelta hdeltaHalf
  have hpow : delta ^ sourcePruneRoundCount (Fintype.card Arm) ≤
      delta ^ (Nat.log 2 (Fintype.card Arm) - 1) :=
    pow_le_pow_of_le_one hdelta hdeltaOne
      (log_two_pred_le_sourcePruneRoundCount (Fintype.card Arm))
  calc
    delta ^ sourcePruneRoundCount (Fintype.card Arm) *
        ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) ≤
        delta ^ (Nat.log 2 (Fintype.card Arm) - 1) *
          ((pruneBadArms preferenceGap lower anchor initial).card : ℝ) :=
      mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ ≤ cutoff := hprefix

end FalahatgarEtAl2017MaxingRanking
