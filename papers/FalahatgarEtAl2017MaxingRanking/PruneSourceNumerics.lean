import FalahatgarEtAl2017MaxingRanking.CanonicalPruneChernoff
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Source-schedule arithmetic for the first Prune round

The first source round uses `eta = δ / 4`.  This file derives the finite
Chernoff exponent forced by the source upper allocation `δ ≤ n' / n`; the
remaining conversion of that exponent to `δ / 2` is the logarithmic arithmetic
in Lemma 14.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- `exp 1 - 1` is bounded by the elementary constant used below. -/
theorem exp_one_sub_one_le_two : Real.exp 1 - 1 ≤ (2 : ℝ) := by
  have hexp : Real.exp 1 < (3 : ℝ) := by
    exact Real.exp_one_lt_d9.trans (by norm_num)
  linarith

/--
Under the source's first-round allocation `eta = δ / 4` and `δ ≤ n' / n`, the
actual canonical Prune failure probability has exponent at most `-n' / 2`.
-/
theorem canonicalPruneRound_card_failure_probability_le_exp_neg_half_cutoff
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta : ℝ)
    (cutoff : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (hdeltaLeOne : delta ≤ 1)
    (hcardPos : 0 < (Fintype.card Arm : ℝ))
    (hdeltaUpper : delta ≤ (cutoff : ℝ) / (Fintype.card Arm : ℝ)) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper (delta / 4))).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
            2 * cutoff} ≤ Real.exp (-(cutoff : ℝ) / 2) := by
  let eta : ℝ := delta / 4
  let badCount : ℝ :=
    ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaLeOne : eta ≤ 1 := by
    dsimp [eta]
    nlinarith
  have hbadCard : badCount ≤ (Fintype.card Arm : ℝ) := by
    dsimp [badCount]
    have hfilter :
        (active.filter fun arm => preferenceGap arm anchor ≤ lower).card ≤ active.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hactive : active.card ≤ Fintype.card Arm := by
      simpa using Finset.card_le_card (Finset.subset_univ active)
    exact_mod_cast hfilter.trans hactive
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hcardDelta : (Fintype.card Arm : ℝ) * delta ≤ cutoff := by
    simpa [mul_comm] using (le_div_iff₀ hcardPos).mp hdeltaUpper
  have hbadBudget : badCount * eta ≤ (cutoff : ℝ) / 4 := by
    dsimp [eta]
    calc
      badCount * (delta / 4) = (badCount * delta) / 4 := by ring
      _ ≤ ((Fintype.card Arm : ℝ) * delta) / 4 := by
        gcongr
      _ ≤ (cutoff : ℝ) / 4 := by gcongr
  have hbadBudgetNonneg : 0 ≤ badCount * eta := by positivity
  have hexponent :
      - (cutoff : ℝ) + badCount * ((Real.exp 1 - 1) * eta) ≤
        - (cutoff : ℝ) / 2 := by
    have hmult : (Real.exp 1 - 1) * (badCount * eta) ≤
        (2 : ℝ) * ((cutoff : ℝ) / 4) := by
      exact mul_le_mul exp_one_sub_one_le_two hbadBudget hbadBudgetNonneg (by norm_num)
    nlinarith [hmult]
  have hchernoff := canonicalPruneRound_card_failure_probability_of_goodAnchor_exponential
    preferenceGap hprobability active anchor lower upper eta cutoff 1 hanchor hseparation heta hetaLeOne
    (by norm_num : (0 : ℝ) ≤ 1)
  change (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
    (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
      ¬ (pruneRound active
        (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
      Real.exp (-(cutoff : ℝ) / 2)
  calc
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).card ≤ 2 * cutoff} ≤
        Real.exp (-(cutoff : ℝ) + badCount * ((Real.exp 1 - 1) * eta)) := by
          simpa [badCount] using hchernoff
    _ ≤ Real.exp (-(cutoff : ℝ) / 2) := (Real.exp_le_exp.mpr hexponent)

/--
The logarithmic arithmetic behind Lemma 14 converts the first-round
exponential endpoint to the required inverse-cardinality scale for `n ≥ 3`.
-/
theorem exp_neg_half_cutoff_le_one_div_two_mul_card
    (card cutoff : ℕ) (hcard : 3 ≤ card)
    (hcutoff : 8 * (Real.log (card : ℝ)) ^ 2 ≤ (cutoff : ℝ)) :
    Real.exp (-(cutoff : ℝ) / 2) ≤ 1 / (2 * (card : ℝ)) := by
  have hcardPos : 0 < (card : ℝ) := by positivity
  have hlogOne : 1 ≤ Real.log (card : ℝ) := by
    apply (Real.le_log_iff_exp_le hcardPos).mpr
    calc
      Real.exp 1 ≤ (3 : ℝ) := (Real.exp_one_lt_d9.trans (by norm_num)).le
      _ ≤ (card : ℝ) := by exact_mod_cast hcard
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hlogProduct : Real.log (2 * (card : ℝ)) ≤
      4 * (Real.log (card : ℝ)) ^ 2 := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hcardPos)]
    nlinarith [hlogOne, hlogTwo]
  have hcutoffLog : Real.log (2 * (card : ℝ)) ≤ (cutoff : ℝ) / 2 := by
    nlinarith [hcutoff, hlogProduct]
  calc
    Real.exp (-(cutoff : ℝ) / 2) ≤ Real.exp (-Real.log (2 * (card : ℝ))) := by
      apply (Real.exp_le_exp).mpr
      linarith
    _ = 1 / (2 * (card : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      ring

/--
Lemma 14's first-round size conclusion for the nontrivial `n ≥ 3` branch,
with its printed `8 log² n` and confidence-range hypotheses.
-/
theorem canonicalPruneRound_card_failure_probability_le_delta_half_of_sourceLemma14_of_card_ge_three
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta : ℝ)
    (cutoff : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (hdeltaLeOne : delta ≤ 1)
    (hcard : 3 ≤ Fintype.card Arm)
    (hcutoff : 8 * (Real.log (Fintype.card Arm : ℝ)) ^ 2 ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ (cutoff : ℝ) / (Fintype.card Arm : ℝ)) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper (delta / 4))).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
            2 * cutoff} ≤ delta / 2 := by
  have hcardPos : 0 < (Fintype.card Arm : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 3) hcard
  have hfirst := canonicalPruneRound_card_failure_probability_le_exp_neg_half_cutoff
    preferenceGap hprobability active anchor lower upper delta cutoff hanchor hseparation hdelta
    hdeltaLeOne hcardPos hdeltaUpper
  have hlogTail := exp_neg_half_cutoff_le_one_div_two_mul_card
    (Fintype.card Arm) cutoff hcard hcutoff
  calc
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper (delta / 4))).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
            2 * cutoff} ≤ Real.exp (-(cutoff : ℝ) / 2) := hfirst
    _ ≤ 1 / (2 * (Fintype.card Arm : ℝ)) := hlogTail
    _ = (1 / (Fintype.card Arm : ℝ)) / 2 := by ring
    _ ≤ delta / 2 := by gcongr

/--
Lemma 14's complete first-round size conclusion.  The `n < 3` branch is
deterministic from the source confidence range; the nontrivial branch uses
the displayed logarithmic condition.
-/
theorem canonicalPruneRound_card_failure_probability_le_delta_half_of_sourceLemma14
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta : ℝ)
    (cutoff : ℕ)
    (hanchor : GoodAnchor preferenceGap lower cutoff anchor)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (hdeltaLeOne : delta ≤ 1)
    (hcutoff : 8 * (Real.log (Fintype.card Arm : ℝ)) ^ 2 ≤ (cutoff : ℝ))
    (hdeltaLower : 1 / (Fintype.card Arm : ℝ) ≤ delta)
    (hdeltaUpper : delta ≤ (cutoff : ℝ) / (Fintype.card Arm : ℝ)) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper (delta / 4))).toMeasure.real {batchTable |
        ¬ (pruneRound active
          (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
            2 * cutoff} ≤ delta / 2 := by
  by_cases hlarge : 3 ≤ Fintype.card Arm
  · exact canonicalPruneRound_card_failure_probability_le_delta_half_of_sourceLemma14_of_card_ge_three
      preferenceGap hprobability active anchor lower upper delta cutoff hanchor hseparation hdelta
      hdeltaLeOne hlarge hcutoff hdeltaLower hdeltaUpper
  · have hsmall : Fintype.card Arm ≤ 2 := by omega
    have hcardCases : Fintype.card Arm = 0 ∨ 0 < Fintype.card Arm := by omega
    rcases hcardCases with hzero | hpositive
    · have hupperZero : delta ≤ 0 := by simpa [hzero] using hdeltaUpper
      exact (not_lt_of_ge hupperZero hdelta).elim
    · have hcutoffPosReal : 0 < (cutoff : ℝ) / (Fintype.card Arm : ℝ) :=
        lt_of_lt_of_le hdelta hdeltaUpper
      have hcutoffPos : 0 < cutoff := by
        have hcardPosReal : 0 < (Fintype.card Arm : ℝ) := by exact_mod_cast hpositive
        rcases (div_pos_iff.mp hcutoffPosReal) with hboth | hnegative
        · exact_mod_cast hboth.1
        · exact False.elim (not_lt_of_ge (Nat.cast_nonneg cutoff) hnegative.1)
      have hdeterministic : ∀ batchTable,
          (pruneRound active
            (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
              2 * cutoff := by
        intro batchTable
        calc
          (pruneRound active
            (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤ active.card :=
              Finset.card_le_card (pruneRound_subset active _)
          _ ≤ Fintype.card Arm := by
              simpa using Finset.card_le_card (Finset.subset_univ active)
          _ ≤ 2 * cutoff := by omega
      have hempty : {batchTable |
          ¬ (pruneRound active
            (canonicalPruneRoundDecision active lower upper (delta / 4) batchTable)).card ≤
              2 * cutoff} = ∅ := by
        ext batchTable
        simp [hdeterministic batchTable]
      rw [hempty]
      simpa using (div_nonneg hdelta.le (by norm_num : (0 : ℝ) ≤ 2))

/--
For any fixed active set, a fresh Prune round contracts its threshold-nonbetter
population by a factor of `delta` except at the displayed Chernoff tail.  This
is the one-round estimate used conditionally in the source proof of Lemma 15.
-/
theorem canonicalPruneRound_badSurvivor_contraction_failure_le_exp
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (preferenceGap : Arm → Arm → ℝ)
    (hprobability : CenteredComparisonProbabilities preferenceGap)
    (active : Finset Arm) (anchor : Arm) (lower upper delta eta : ℝ)
    (hseparation : lower < upper) (hdelta : 0 < delta)
    (heta : 0 < eta) (hetaLeOne : eta ≤ 1) (hetaBound : eta ≤ delta / 4) :
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        delta * ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) <
        (((pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ) *
        delta / 2) := by
  let badCount : ℝ :=
    ((active.filter fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)
  have hbadNonneg : 0 ≤ badCount := by positivity
  have hetaNonneg : 0 ≤ eta := heta.le
  have hterm : badCount * ((Real.exp 1 - 1) * eta) ≤ badCount * (delta / 2) := by
    apply mul_le_mul_of_nonneg_left _ hbadNonneg
    calc
      (Real.exp 1 - 1) * eta ≤ (2 : ℝ) * eta := by
        exact mul_le_mul_of_nonneg_right exp_one_sub_one_le_two hetaNonneg
      _ ≤ (2 : ℝ) * (delta / 4) := by
        exact mul_le_mul_of_nonneg_left hetaBound (by norm_num)
      _ = delta / 2 := by ring
  have hexponent :
      - (delta * badCount) + badCount * ((Real.exp 1 - 1) * eta) ≤
        -badCount * delta / 2 := by
    nlinarith [hterm]
  have htail := canonicalPruneRound_badSurvivorCard_probability_exponential
    preferenceGap hprobability active anchor lower upper eta (delta * badCount) 1
    hseparation heta hetaLeOne (by norm_num : (0 : ℝ) ≤ 1)
  change (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
    (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
      delta * badCount <
      (((pruneRound active
        (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
        fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
      Real.exp (-badCount * delta / 2)
  calc
    (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
      (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
        delta * badCount <
        (((pruneRound active
          (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
          fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} ≤
        (canonicalPruneRoundBatchLaw preferenceGap hprobability active anchor
          (fixedSampleBudget lower upper eta)).toMeasure.real {batchTable |
            delta * badCount ≤
            (((pruneRound active
              (canonicalPruneRoundDecision active lower upper eta batchTable)).filter
              fun arm => preferenceGap arm anchor ≤ lower).card : ℝ)} := by
          refine measureReal_mono ?_ (measure_ne_top _ _)
          intro batchTable hstrict
          simp only [Set.mem_setOf_eq] at hstrict ⊢
          exact hstrict.le
    _ ≤ Real.exp (-(1 : ℝ) * (delta * badCount) + badCount *
        ((Real.exp (1 : ℝ) - 1) * eta)) := by
      simpa [badCount] using htail
    _ = Real.exp (- (delta * badCount) + badCount * ((Real.exp 1 - 1) * eta)) := by ring_nf
    _ ≤ Real.exp (-badCount * delta / 2) := Real.exp_le_exp.mpr hexponent

/--
The numerical Chernoff conversion in Lemma 15.  A cutoff whose squared scale
exceeds `6 n log n`, together with `delta ≥ cutoff / n`, makes the displayed
one-round contraction tail at most `n⁻³`.
-/
theorem exp_neg_half_mul_le_card_inv_cube_of_sourceLemma15
    (card cutoff : ℕ) (delta : ℝ) (hcard : 2 ≤ card)
    (hcutoff : 6 * (card : ℝ) * Real.log (card : ℝ) < (cutoff : ℝ) ^ 2)
    (hdeltaLower : (cutoff : ℝ) / (card : ℝ) ≤ delta) :
    Real.exp (-(cutoff : ℝ) * delta / 2) ≤ 1 / (card : ℝ) ^ 3 := by
  have hcardPos : 0 < (card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hcutoffSqOverCard : 6 * Real.log (card : ℝ) < (cutoff : ℝ) ^ 2 / (card : ℝ) := by
    apply (lt_div_iff₀ hcardPos).mpr
    calc
      6 * Real.log (card : ℝ) * (card : ℝ) =
          6 * (card : ℝ) * Real.log (card : ℝ) := by ring
      _ < (cutoff : ℝ) ^ 2 := hcutoff
  have hcutoffNonneg : 0 ≤ (cutoff : ℝ) := Nat.cast_nonneg cutoff
  have hcutoffSqLe : (cutoff : ℝ) ^ 2 / (card : ℝ) ≤ (cutoff : ℝ) * delta := by
    calc
      (cutoff : ℝ) ^ 2 / (card : ℝ) = (cutoff : ℝ) * ((cutoff : ℝ) / (card : ℝ)) := by ring
      _ ≤ (cutoff : ℝ) * delta := mul_le_mul_of_nonneg_left hdeltaLower hcutoffNonneg
  have hexponent : 3 * Real.log (card : ℝ) ≤ (cutoff : ℝ) * delta / 2 := by
    nlinarith [hcutoffSqOverCard.trans_le hcutoffSqLe]
  calc
    Real.exp (-(cutoff : ℝ) * delta / 2) ≤ Real.exp (-(3 * Real.log (card : ℝ))) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (Real.exp (-Real.log (card : ℝ))) ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = 1 / (card : ℝ) ^ 3 := by
      rw [Real.exp_neg, Real.exp_log hcardPos]
      ring

/--
The preceding numerical bound in the weak square-root form printed in Main
Lemma 5.  The non-strict cutoff is sufficient because the Chernoff exponent
and the target inverse-cubic tail are themselves non-strict.
-/
theorem exp_neg_half_mul_le_card_inv_cube_of_sourceLemma5_sqrt
    (card cutoff : ℕ) (delta : ℝ) (hcard : 2 ≤ card)
    (hcutoff : Real.sqrt (6 * (card : ℝ) * Real.log (card : ℝ)) ≤ (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (card : ℝ) ≤ delta) :
    Real.exp (-(cutoff : ℝ) * delta / 2) ≤ 1 / (card : ℝ) ^ 3 := by
  have hcardPos : 0 < (card : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by norm_num : 0 < 2) hcard
  have hinsideNonneg : 0 ≤ 6 * (card : ℝ) * Real.log (card : ℝ) := by
    have hlogNonneg : 0 ≤ Real.log (card : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ card by omega))
    positivity
  have hcutoffSq :
      6 * (card : ℝ) * Real.log (card : ℝ) ≤ (cutoff : ℝ) ^ 2 := by
    calc
      6 * (card : ℝ) * Real.log (card : ℝ) =
          (Real.sqrt (6 * (card : ℝ) * Real.log (card : ℝ))) ^ 2 := by
            rw [Real.sq_sqrt hinsideNonneg]
      _ ≤ (cutoff : ℝ) ^ 2 := by
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hcutoff 2
  have hcutoffSqOverCard :
      6 * Real.log (card : ℝ) ≤ (cutoff : ℝ) ^ 2 / (card : ℝ) := by
    apply (le_div_iff₀ hcardPos).mpr
    calc
      6 * Real.log (card : ℝ) * (card : ℝ) =
          6 * (card : ℝ) * Real.log (card : ℝ) := by ring
      _ ≤ (cutoff : ℝ) ^ 2 := hcutoffSq
  have hcutoffNonneg : 0 ≤ (cutoff : ℝ) := Nat.cast_nonneg cutoff
  have hcutoffSqLe : (cutoff : ℝ) ^ 2 / (card : ℝ) ≤ (cutoff : ℝ) * delta := by
    calc
      (cutoff : ℝ) ^ 2 / (card : ℝ) =
          (cutoff : ℝ) * ((cutoff : ℝ) / (card : ℝ)) := by ring
      _ ≤ (cutoff : ℝ) * delta :=
        mul_le_mul_of_nonneg_left hdeltaLower hcutoffNonneg
  have hexponent : 3 * Real.log (card : ℝ) ≤ (cutoff : ℝ) * delta / 2 := by
    nlinarith [hcutoffSqOverCard.trans hcutoffSqLe]
  calc
    Real.exp (-(cutoff : ℝ) * delta / 2) ≤
        Real.exp (-(3 * Real.log (card : ℝ))) := by
          apply Real.exp_le_exp.mpr
          linarith
    _ = (Real.exp (-Real.log (card : ℝ))) ^ 3 := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = 1 / (card : ℝ) ^ 3 := by
      rw [Real.exp_neg, Real.exp_log hcardPos]
      ring

/-- The strict Supplement Lemma 15 form is an immediate specialization. -/
theorem exp_neg_half_mul_le_card_inv_cube_of_sourceLemma15_sqrt
    (card cutoff : ℕ) (delta : ℝ) (hcard : 2 ≤ card)
    (hcutoff : Real.sqrt (6 * (card : ℝ) * Real.log (card : ℝ)) < (cutoff : ℝ))
    (hdeltaLower : (cutoff : ℝ) / (card : ℝ) ≤ delta) :
    Real.exp (-(cutoff : ℝ) * delta / 2) ≤ 1 / (card : ℝ) ^ 3 := by
  exact exp_neg_half_mul_le_card_inv_cube_of_sourceLemma5_sqrt card cutoff delta hcard
    hcutoff.le hdeltaLower

end FalahatgarEtAl2017MaxingRanking
