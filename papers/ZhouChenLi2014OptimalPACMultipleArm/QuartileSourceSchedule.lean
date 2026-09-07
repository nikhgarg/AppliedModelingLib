import ZhouChenLi2014OptimalPACMultipleArm.QuartileBudgetRounds
import ZhouChenLi2014OptimalPACMultipleArm.QuartileTailSimplification
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit confidence schedule from the QE proof

Theorem 4.3 allocates round failure probability
`exp (-0.1 r) (1 - exp (-0.1)) δ`.  This file checks its finite summability
exactly, fixes an explicit floor convention for the source's real round
budget, and supplies a transparent finite confidence radius.  The source's
hidden global budget constant remains a separate resource-rate question.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The geometric confidence-decay factor displayed in Theorem 4.3's proof. -/
noncomputable def quartileSourceFailureDecay : ℝ := Real.exp (-(1 / 10 : ℝ))

/-- The source's round-`r` confidence allocation. -/
noncomputable def quartileSourceFailureBudget (delta : ℝ) (round : ℕ) : ℝ :=
  (1 - quartileSourceFailureDecay) * quartileSourceFailureDecay ^ round * delta

theorem quartileSourceFailureDecay_pos : 0 < quartileSourceFailureDecay := by
  exact Real.exp_pos _

theorem quartileSourceFailureDecay_lt_one : quartileSourceFailureDecay < 1 := by
  rw [quartileSourceFailureDecay, Real.exp_lt_one_iff]
  norm_num

theorem quartileSourceFailureBudget_nonneg {delta : ℝ} (hdelta : 0 ≤ delta)
    (round : ℕ) :
    0 ≤ quartileSourceFailureBudget delta round := by
  unfold quartileSourceFailureBudget
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr quartileSourceFailureDecay_lt_one.le)
      (pow_nonneg quartileSourceFailureDecay_pos.le _)) hdelta

/-- With positive total confidence, every source round receives positive mass. -/
theorem quartileSourceFailureBudget_pos {delta : ℝ} (hdelta : 0 < delta)
    (round : ℕ) :
    0 < quartileSourceFailureBudget delta round := by
  unfold quartileSourceFailureBudget
  exact mul_pos
    (mul_pos (sub_pos.mpr quartileSourceFailureDecay_lt_one)
      (pow_pos quartileSourceFailureDecay_pos _)) hdelta

/-- No individual geometric source confidence allocation exceeds `delta`. -/
theorem quartileSourceFailureBudget_le_total {delta : ℝ} (hdelta : 0 ≤ delta)
    (round : ℕ) :
    quartileSourceFailureBudget delta round ≤ delta := by
  unfold quartileSourceFailureBudget
  have hfactorLeOne : 1 - quartileSourceFailureDecay ≤ 1 := by
    linarith [quartileSourceFailureDecay_pos]
  have hpowNonneg : 0 ≤ quartileSourceFailureDecay ^ round :=
    pow_nonneg quartileSourceFailureDecay_pos.le _
  have hpowLeOne : quartileSourceFailureDecay ^ round ≤ 1 :=
    pow_le_one₀ quartileSourceFailureDecay_pos.le quartileSourceFailureDecay_lt_one.le
  have hweight : (1 - quartileSourceFailureDecay) *
      quartileSourceFailureDecay ^ round ≤ 1 :=
    mul_le_one₀ hfactorLeOne hpowNonneg hpowLeOne
  calc
    (1 - quartileSourceFailureDecay) * quartileSourceFailureDecay ^ round * delta ≤
        1 * delta := mul_le_mul_of_nonneg_right hweight hdelta
    _ = delta := by ring

/-- The finite source confidence allocation never exceeds its total `delta` budget. -/
theorem quartileSourceFailureBudget_sum_le (delta : ℝ) (hdelta : 0 ≤ delta)
    (roundCount : ℕ) :
    ∑ round ∈ Finset.range roundCount, quartileSourceFailureBudget delta round ≤ delta := by
  have hformula : ∀ count : ℕ,
      (∑ round ∈ Finset.range count, quartileSourceFailureBudget delta round) =
        delta * (1 - quartileSourceFailureDecay ^ count) := by
    intro count
    induction count with
    | zero => simp
    | succ count ih =>
        rw [Finset.sum_range_succ, ih]
        unfold quartileSourceFailureBudget
        ring
  rw [hformula]
  have hpow : 0 ≤ quartileSourceFailureDecay ^ roundCount :=
    pow_nonneg quartileSourceFailureDecay_pos.le _
  nlinarith

/-- The logarithmic confidence correction grows by exactly `0.1` per source
round.  This is the analytic form used when the QE rate cancels its geometric
allocation and survivor factors. -/
theorem quartileSourceFailureBudget_log_ratio_eq
    (delta : ℝ) (hdelta : 0 < delta) (round : ℕ) :
    Real.log (2 / quartileSourceFailureBudget delta round) =
      Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) + (round : ℝ) / 10 := by
  have honeMinusPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hrhoPow : quartileSourceFailureDecay ^ round =
      Real.exp (-((round : ℝ) / 10)) := by
    unfold quartileSourceFailureDecay
    convert (Real.exp_nat_mul (-(1 / 10 : ℝ)) round).symm using 1
    field_simp
  have hratio : 2 / quartileSourceFailureBudget delta round =
      (2 / ((1 - quartileSourceFailureDecay) * delta)) * Real.exp ((round : ℝ) / 10) := by
    unfold quartileSourceFailureBudget
    rw [hrhoPow, Real.exp_neg]
    field_simp [honeMinusPos.ne', hdelta.ne', Real.exp_ne_zero]
  rw [hratio, Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]

/-- After the source's `(r + 1)²` envelope normalization, the round-
confidence numerator is uniformly bounded by a constant plus the one global
`log (1 / delta)` term. -/
theorem quartileSourceConfidenceNumerator_div_sq_le
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (round : ℕ) :
    (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        ((round + 1 : ℕ) : ℝ) ^ 2 ≤
      21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) := by
  let base : ℝ := 2 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta))
  have honeMinusPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hdenomPos : 0 < (1 - quartileSourceFailureDecay) * delta :=
    mul_pos honeMinusPos hdelta
  have hdenomLeOne : (1 - quartileSourceFailureDecay) * delta ≤ 1 := by
    have honeMinusLeOne : 1 - quartileSourceFailureDecay ≤ 1 := by
      linarith [quartileSourceFailureDecay_pos]
    calc
      (1 - quartileSourceFailureDecay) * delta ≤
          (1 - quartileSourceFailureDecay) * 1 :=
        mul_le_mul_of_nonneg_left hdeltaLeOne honeMinusPos.le
      _ = 1 - quartileSourceFailureDecay := by ring
      _ ≤ 1 := honeMinusLeOne
  have hratio : 1 ≤ 2 / ((1 - quartileSourceFailureDecay) * delta) := by
    apply (le_div_iff₀ hdenomPos).mpr
    linarith
  have hbaseNonneg : 0 ≤ base := by
    dsimp [base]
    have hlog : 0 ≤ Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) :=
      Real.log_nonneg hratio
    linarith
  have hroundDenomPos : 0 < ((round + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hroundNonneg : (0 : ℝ) ≤ round := Nat.cast_nonneg round
  have hroundDenomGeOne : 1 ≤ ((round + 1 : ℕ) : ℝ) ^ 2 := by
    have hroundOne : (1 : ℝ) ≤ ((round + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le round)
    simpa using (sq_le_sq₀ (by norm_num) (by positivity)).mpr hroundOne
  have hbaseDiv : base / ((round + 1 : ℕ) : ℝ) ^ 2 ≤ base := by
    apply (div_le_iff₀ hroundDenomPos).mpr
    nlinarith
  have hroundDiv : (round : ℝ) / ((round + 1 : ℕ) : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ hroundDenomPos).mpr
    norm_num
    nlinarith [sq_nonneg (round : ℝ)]
  rw [quartileSourceFailureBudget_log_ratio_eq delta hdelta round]
  have hsplit :
      (2 + (Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) +
        (round : ℝ) / 10)) / ((round + 1 : ℕ) : ℝ) ^ 2 =
        base / ((round + 1 : ℕ) : ℝ) ^ 2 +
          ((round : ℝ) / ((round + 1 : ℕ) : ℝ) ^ 2) / 10 := by
    dsimp [base]
    ring
  rw [hsplit]
  calc
    base / ((round + 1 : ℕ) : ℝ) ^ 2 +
        ((round : ℝ) / ((round + 1 : ℕ) : ℝ) ^ 2) / 10 ≤ base + 1 / 10 := by
      gcongr
    _ = 21 / 10 + Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) := by
      dsimp [base]
      ring

/-- The source's fixed confidence constant separates from the sole
parameter-dependent logarithm. -/
theorem quartileSourceLogFactor_split
    (delta : ℝ) (hdelta : 0 < delta) :
    Real.log (2 / ((1 - quartileSourceFailureDecay) * delta)) =
      Real.log (2 / (1 - quartileSourceFailureDecay)) + Real.log (1 / delta) := by
  have hgapPos : 0 < 1 - quartileSourceFailureDecay :=
    sub_pos.mpr quartileSourceFailureDecay_lt_one
  have hratio : 2 / ((1 - quartileSourceFailureDecay) * delta) =
      (2 / (1 - quartileSourceFailureDecay)) * (1 / delta) := by
    field_simp [hgapPos.ne', hdelta.ne']
  rw [hratio, Real.log_mul (div_ne_zero (by norm_num) hgapPos.ne')
    (one_div_ne_zero hdelta.ne')]

/-- The decreasing round-budget factor printed in Algorithm 1. -/
noncomputable def quartileSourceBudgetDecay : ℝ :=
  Real.exp (1 / 5 : ℝ) * (3 / 4 : ℝ)

theorem quartileSourceBudgetDecay_pos : 0 < quartileSourceBudgetDecay := by
  unfold quartileSourceBudgetDecay
  positivity

theorem three_quarters_lt_quartileSourceBudgetDecay :
    (3 / 4 : ℝ) < quartileSourceBudgetDecay := by
  unfold quartileSourceBudgetDecay
  have hexp : 1 < Real.exp (1 / 5 : ℝ) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  nlinarith

theorem quartileSourceBudgetDecay_lt_one : quartileSourceBudgetDecay < 1 := by
  unfold quartileSourceBudgetDecay
  have hpow : Real.exp (1 / 5 : ℝ) ^ 5 < (4 / 3 : ℝ) ^ 5 := by
    calc
      Real.exp (1 / 5 : ℝ) ^ 5 = Real.exp ((5 : ℝ) * (1 / 5 : ℝ)) := by
        exact (Real.exp_nat_mul (1 / 5 : ℝ) 5).symm
      _ = Real.exp 1 := by norm_num
      _ < 3 := Real.exp_one_lt_three
      _ < (4 / 3 : ℝ) ^ 5 := by norm_num
  have hexp : Real.exp (1 / 5 : ℝ) < 4 / 3 :=
    lt_of_pow_lt_pow_left₀ 5 (by norm_num) hpow
  nlinarith

/-- The source's two geometric schedules have the cancellation used in the
rate proof: the squared confidence decay times the budget decay is exactly the
survivor contraction factor. -/
theorem quartileSourceFailureDecay_sq_mul_budgetDecay :
    quartileSourceFailureDecay ^ 2 * quartileSourceBudgetDecay = (3 / 4 : ℝ) := by
  unfold quartileSourceFailureDecay quartileSourceBudgetDecay
  have hsplit : Real.exp (-(1 / 10 : ℝ)) * Real.exp (-(1 / 10 : ℝ)) =
      Real.exp (-(1 / 5 : ℝ)) := by
    rw [← Real.exp_add]
    norm_num
  have hinverse : Real.exp (-(1 / 5 : ℝ)) * Real.exp (1 / 5 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num
  calc
    Real.exp (-(1 / 10 : ℝ)) ^ 2 *
        (Real.exp (1 / 5 : ℝ) * (3 / 4 : ℝ)) =
        (Real.exp (-(1 / 10 : ℝ)) * Real.exp (-(1 / 10 : ℝ))) *
          Real.exp (1 / 5 : ℝ) * (3 / 4 : ℝ) := by ring
    _ = Real.exp (-(1 / 5 : ℝ)) * Real.exp (1 / 5 : ℝ) * (3 / 4 : ℝ) := by
      rw [hsplit]
    _ = 3 / 4 := by rw [hinverse]; norm_num

/--
An executable floor convention for Algorithm 1's otherwise real-valued round
budget.  The floor is a formalizer-specified convention, not one stated in
the source.
-/
noncomputable def quartileSourceRoundBudget (totalBudget : ℕ) (round : ℕ) : ℕ :=
  Nat.floor ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
    (totalBudget : ℝ))

/-- Every floored source round budget is at most the initial total budget. -/
theorem quartileSourceRoundBudget_le_totalBudget (totalBudget round : ℕ) :
    quartileSourceRoundBudget totalBudget round ≤ totalBudget := by
  unfold quartileSourceRoundBudget
  have hdecayNonneg : 0 ≤ quartileSourceBudgetDecay :=
    quartileSourceBudgetDecay_pos.le
  have hpowNonneg : 0 ≤ quartileSourceBudgetDecay ^ round :=
    pow_nonneg hdecayNonneg _
  have hpowLeOne : quartileSourceBudgetDecay ^ round ≤ 1 :=
    pow_le_one₀ hdecayNonneg quartileSourceBudgetDecay_lt_one.le
  have hweightLeOne :
      (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round ≤ 1 :=
    mul_le_one₀ (by linarith [quartileSourceBudgetDecay_pos]) hpowNonneg hpowLeOne
  have hargumentNonneg :
      0 ≤ (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
        (totalBudget : ℝ) :=
    mul_nonneg
      (mul_nonneg (sub_nonneg.mpr quartileSourceBudgetDecay_lt_one.le) hpowNonneg)
      (Nat.cast_nonneg totalBudget)
  have hfloor :
      (Nat.floor ((1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
        (totalBudget : ℝ)) : ℝ) ≤
      (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
        (totalBudget : ℝ) := Nat.floor_le hargumentNonneg
  have hargumentLe :
      (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
        (totalBudget : ℝ) ≤ totalBudget := by
    have := mul_le_mul_of_nonneg_right hweightLeOne (Nat.cast_nonneg totalBudget)
    simpa using this
  exact_mod_cast hfloor.trans hargumentLe

/-- The floored geometric allocation spends no more than the source total budget. -/
theorem quartileSourceRoundBudget_sum_le_totalBudget
    (totalBudget roundCount : ℕ) :
    ∑ round ∈ Finset.range roundCount,
      quartileSourceRoundBudget totalBudget round ≤ totalBudget := by
  have hdecayNonneg : 0 ≤ quartileSourceBudgetDecay :=
    quartileSourceBudgetDecay_pos.le
  have hfloor : ∀ round : ℕ,
      (quartileSourceRoundBudget totalBudget round : ℝ) ≤
        (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
          (totalBudget : ℝ) := by
    intro round
    unfold quartileSourceRoundBudget
    apply Nat.floor_le
    exact mul_nonneg
      (mul_nonneg (sub_nonneg.mpr quartileSourceBudgetDecay_lt_one.le)
        (pow_nonneg hdecayNonneg _))
      (Nat.cast_nonneg totalBudget)
  have hweights :
      (∑ round ∈ Finset.range roundCount,
        (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
          (totalBudget : ℝ)) =
        ((1 - quartileSourceBudgetDecay) *
          ∑ round ∈ Finset.range roundCount, quartileSourceBudgetDecay ^ round) *
          (totalBudget : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hreal :
      (∑ round ∈ Finset.range roundCount,
        (quartileSourceRoundBudget totalBudget round : ℝ)) ≤ totalBudget := by
    calc
      (∑ round ∈ Finset.range roundCount,
          (quartileSourceRoundBudget totalBudget round : ℝ)) ≤
          ∑ round ∈ Finset.range roundCount,
            (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
              (totalBudget : ℝ) :=
        Finset.sum_le_sum (fun round hround => hfloor round)
      _ = ((1 - quartileSourceBudgetDecay) *
          ∑ round ∈ Finset.range roundCount, quartileSourceBudgetDecay ^ round) *
          (totalBudget : ℝ) := hweights
      _ = (1 - quartileSourceBudgetDecay ^ roundCount) * (totalBudget : ℝ) := by
        rw [mul_neg_geom_sum]
      _ ≤ totalBudget := by
        have hpow : 0 ≤ quartileSourceBudgetDecay ^ roundCount :=
          pow_nonneg hdecayNonneg _
        have hfactor : 1 - quartileSourceBudgetDecay ^ roundCount ≤ 1 := by linarith
        have := mul_le_mul_of_nonneg_right hfactor (Nat.cast_nonneg totalBudget)
        simpa using this
  exact_mod_cast hreal

/-- Along any QE state path, the floored source allocation uses at most its total budget. -/
theorem quartileSourceAllocation_total_le
    {Arm : Type*} (totalBudget roundCount : ℕ) (active : ℕ → Finset Arm) :
    ∑ round ∈ Finset.range roundCount,
      (active round).card *
        quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round
          (active round) ≤ totalBudget := by
  calc
    (∑ round ∈ Finset.range roundCount,
        (active round).card *
          quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round
            (active round)) ≤
        ∑ round ∈ Finset.range roundCount,
          quartileSourceRoundBudget totalBudget round := by
          apply Finset.sum_le_sum
          intro round hround
          exact quartilePerArmSampleCount_total_le
            (quartileSourceRoundBudget totalBudget) round (active round)
    _ ≤ totalBudget :=
      quartileSourceRoundBudget_sum_le_totalBudget totalBudget roundCount

/-- The actual fresh batch kernel for the floored Algorithm-1 QE allocation. -/
noncomputable def quartileSourceBudgetOutcomeLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) :
    AdaptiveOutcomeKernel (Finset Arm) (canonicalFreshQuartileOutcome Arm totalBudget) :=
  quartileBudgetOutcomeLaw mean hmean roundCount
    (quartileSourceRoundBudget totalBudget) totalBudget
    (fun round _ => quartileSourceRoundBudget_le_totalBudget totalBudget round)

/--
At a nonterminal source QE round, the generic two-term tail collapses to
twice its Hoeffding factor under the explicit `exp (-2)` condition.
-/
theorem quartileSourceBudgetRound_failure_probability_le_two_hoeffding
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (error : ℕ → ℝ)
    (round : ℕ) (hround : round < roundCount) (active : Finset Arm)
    (hactive : active.Nonempty)
    (hcount : 0 < quartilePerArmSampleCount
      (quartileSourceRoundBudget totalBudget) round active)
    (herror : 0 ≤ error round) (hactiveSize : 4 ≤ active.card)
    (hsmall : Real.exp
      (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
        error round) ^ 2 /
        (2 * (quartilePerArmSampleCount
          (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) ≤
        Real.exp (-2)) :
    pmfProbClassical
      (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round active)
      (quartileRoundBad mean error
        (adaptiveBatchQuartileScore roundCount
          (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
          (fun round hround active => quartilePerArmSampleCount_le_roundCap
            (quartileSourceRoundBudget totalBudget) totalBudget round active
            (quartileSourceRoundBudget_le_totalBudget totalBudget round))) round active) ≤
      2 * Real.exp
        (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
          error round) ^ 2 /
          (2 * (quartilePerArmSampleCount
            (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) := by
  let q : ℝ := Real.exp
    (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
      error round) ^ 2 /
      (2 * (quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ)))
  have hqpos : 0 < q := Real.exp_pos _
  have ht : 0 ≤ -Real.log q := by
    have hlog : Real.log q ≤ -2 := by
      apply (Real.log_le_iff_le_exp hqpos).mpr
      simpa [q] using hsmall
    linarith
  have hbase := quartileBudgetRound_failure_probability_le mean hmean roundCount
    (quartileSourceRoundBudget totalBudget) totalBudget
    (fun scheduledRound _ =>
      quartileSourceRoundBudget_le_totalBudget totalBudget scheduledRound)
    error round hround active hactive hcount herror (-Real.log q) ht
  have hsecond := quartileSurvivorChernoffTail_le_hoeffding active.card hactiveSize q
    hqpos (by simpa [q] using hsmall)
  calc
    pmfProbClassical
        (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget round active)
        (quartileRoundBad mean error
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) round active) ≤
        q + Real.exp (-(-Real.log q) * (quartileSurvivorCount active.card : ℝ) +
          (active.card : ℝ) * ((Real.exp (-Real.log q) - 1) * q)) := by
          simpa [quartileSourceBudgetOutcomeLaw, q] using hbase
    _ ≤ q + q := by linarith
    _ = 2 * q := by ring
    _ = _ := by rfl

/--
The floored source QE schedule has a literal `1 - delta` retention guarantee
when its nonterminal per-arm Hoeffding factors satisfy the displayed finite
conditions.  Terminal sets of at most three arms incur no artificial sample
or tail premise: their QE bad event is proved impossible.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_hoeffding
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (error : ℕ → ℝ)
    (initial : Finset Arm) (hinitial : initial.Nonempty) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (herror : ∀ round, round < roundCount → 0 ≤ error round)
    (hcount : ∀ round, round < roundCount → ∀ active : Finset Arm,
      4 ≤ active.card → 0 < quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active)
    (hsmall : ∀ round, round < roundCount → ∀ active : Finset Arm,
      4 ≤ active.card → Real.exp
        (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
          error round) ^ 2 /
          (2 * (quartilePerArmSampleCount
            (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) ≤
          Real.exp (-2))
    (htail : ∀ round, round < roundCount → ∀ active : Finset Arm,
      4 ≤ active.card → 2 * Real.exp
        (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
          error round) ^ 2 /
          (2 * (quartilePerArmSampleCount
            (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) ≤
          quartileSourceFailureBudget delta round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  let outcomeLaw : AdaptiveOutcomeKernel (Finset Arm)
      (canonicalFreshQuartileOutcome Arm totalBudget) :=
    quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget
  let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm totalBudget → Arm → ℝ :=
    adaptiveBatchQuartileScore roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun round hround active => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget round active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round))
  have hgeneric := freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum
    mean error initial hinitial outcomeLaw score
    (fun round => if round < roundCount then quartileSourceFailureBudget delta round else 1)
    roundCount (by
      intro round active
      by_cases hround : round < roundCount
      · change pmfProbClassical (outcomeLaw round active)
            (quartileRoundBad mean error score round active) ≤
            (if round < roundCount then quartileSourceFailureBudget delta round else 1)
        rw [if_pos hround]
        by_cases hterminal : active.card ≤ 3
        · have hzero : pmfProbClassical (outcomeLaw round active)
              (quartileRoundBad mean error score round active) = 0 := by
            unfold pmfProbClassical
            apply pmfProb_eq_zero_of_no_mass
            intro outcome hbad
            exact False.elim
              (not_quartileRoundBad_of_card_le_three mean error score round active outcome
                hterminal (herror round hround) hbad)
          rw [hzero]
          exact quartileSourceFailureBudget_nonneg hdelta round
        · have hactiveSize : 4 ≤ active.card := by omega
          have hactive : active.Nonempty := Finset.card_pos.mp (by omega)
          calc
            pmfProbClassical (outcomeLaw round active)
                (quartileRoundBad mean error score round active) ≤
                2 * Real.exp
                  (-((quartilePerArmSampleCount
                    (quartileSourceRoundBudget totalBudget) round active : ℝ) * error round) ^ 2 /
                    (2 * (quartilePerArmSampleCount
                      (quartileSourceRoundBudget totalBudget) round active : ℝ) *
                      (1 / 4 : ℝ))) := by
                simpa [outcomeLaw, score] using
                  (quartileSourceBudgetRound_failure_probability_le_two_hoeffding
                    mean hmean roundCount totalBudget error round hround active hactive
                    (hcount round hround active hactiveSize) (herror round hround) hactiveSize
                    (hsmall round hround active hactiveSize))
            _ ≤ quartileSourceFailureBudget delta round :=
              htail round hround active hactiveSize
      · change pmfProbClassical (outcomeLaw round active)
            (quartileRoundBad mean error score round active) ≤
            (if round < roundCount then quartileSourceFailureBudget delta round else 1)
        rw [if_neg hround]
        unfold pmfProbClassical
        exact pmfProb_le_one _ _)
  have hsum : (∑ round ∈ Finset.range roundCount,
      quartileSourceFailureBudget delta round) =
      ∑ round ∈ Finset.range roundCount,
        (if round < roundCount then quartileSourceFailureBudget delta round else 1) := by
    apply Finset.sum_congr rfl
    intro round hround
    rw [if_pos (Finset.mem_range.mp hround)]
  have hbudget := quartileSourceFailureBudget_sum_le delta hdelta roundCount
  simpa only [outcomeLaw, score] using (by
    calc
      1 - delta ≤ 1 - ∑ round ∈ Finset.range roundCount,
          quartileSourceFailureBudget delta round := by linarith
      _ = 1 - ∑ round ∈ Finset.range roundCount,
          (if round < roundCount then quartileSourceFailureBudget delta round else 1) := by
            rw [hsum]
      _ ≤ _ := hgeneric)

/--
The preceding source QE theorem with numerical hypotheses imposed only on
reachable active-set cardinalities.  The equality to the rounded deterministic
recurrence is proved from the finite adaptive execution law itself.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_reachable_hoeffding
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (error : ℕ → ℝ)
    (initial : Finset Arm) (hinitial : initial.Nonempty) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (herror : ∀ round, round < roundCount → 0 ≤ error round)
    (hcount : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.card = quartileSurvivorCountIter round initial.card →
      4 ≤ active.card → 0 < quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active)
    (hsmall : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.card = quartileSurvivorCountIter round initial.card →
      4 ≤ active.card → Real.exp
        (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
          error round) ^ 2 /
          (2 * (quartilePerArmSampleCount
            (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) ≤
          Real.exp (-2))
    (htail : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.card = quartileSurvivorCountIter round initial.card →
      4 ≤ active.card → 2 * Real.exp
        (-((quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active : ℝ) *
          error round) ^ 2 /
          (2 * (quartilePerArmSampleCount
            (quartileSourceRoundBudget totalBudget) round active : ℝ) * (1 / 4 : ℝ))) ≤
          quartileSourceFailureBudget delta round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  let outcomeLaw : AdaptiveOutcomeKernel (Finset Arm)
      (canonicalFreshQuartileOutcome Arm totalBudget) :=
    quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget
  let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm totalBudget → Arm → ℝ :=
    adaptiveBatchQuartileScore roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun round hround active => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget round active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round))
  have hgeneric := freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum_of_support
    mean error initial hinitial outcomeLaw score
    (fun round => if round < roundCount then quartileSourceFailureBudget delta round else 1)
    roundCount (by
      intro round stateFailure hsupport
      by_cases hround : round < roundCount
      · change pmfProbClassical (outcomeLaw round stateFailure.1)
            (quartileRoundBad mean error score round stateFailure.1) ≤
            (if round < roundCount then quartileSourceFailureBudget delta round else 1)
        rw [if_pos hround]
        have hcardEq : stateFailure.1.card =
            quartileSurvivorCountIter round initial.card := by
          simpa [outcomeLaw, score] using
            (freshQuartileRoundsStateLaw_support_card_eq_iter mean error initial outcomeLaw score
              round stateFailure hsupport)
        by_cases hterminal : stateFailure.1.card ≤ 3
        · have hzero : pmfProbClassical (outcomeLaw round stateFailure.1)
              (quartileRoundBad mean error score round stateFailure.1) = 0 := by
            unfold pmfProbClassical
            apply pmfProb_eq_zero_of_no_mass
            intro outcome hbad
            exact False.elim
              (not_quartileRoundBad_of_card_le_three mean error score round stateFailure.1
                outcome hterminal (herror round hround) hbad)
          rw [hzero]
          exact quartileSourceFailureBudget_nonneg hdelta round
        · have hactiveSize : 4 ≤ stateFailure.1.card := by omega
          have hactive : stateFailure.1.Nonempty := Finset.card_pos.mp (by omega)
          calc
            pmfProbClassical (outcomeLaw round stateFailure.1)
                (quartileRoundBad mean error score round stateFailure.1) ≤
                2 * Real.exp
                  (-((quartilePerArmSampleCount
                    (quartileSourceRoundBudget totalBudget) round stateFailure.1 : ℝ) *
                    error round) ^ 2 /
                    (2 * (quartilePerArmSampleCount
                      (quartileSourceRoundBudget totalBudget) round stateFailure.1 : ℝ) *
                      (1 / 4 : ℝ))) := by
                simpa [outcomeLaw, score] using
                  (quartileSourceBudgetRound_failure_probability_le_two_hoeffding
                    mean hmean roundCount totalBudget error round hround stateFailure.1 hactive
                    (hcount round hround stateFailure.1 hcardEq hactiveSize)
                    (herror round hround) hactiveSize
                    (hsmall round hround stateFailure.1 hcardEq hactiveSize))
            _ ≤ quartileSourceFailureBudget delta round :=
              htail round hround stateFailure.1 hcardEq hactiveSize
      · change pmfProbClassical (outcomeLaw round stateFailure.1)
            (quartileRoundBad mean error score round stateFailure.1) ≤
            (if round < roundCount then quartileSourceFailureBudget delta round else 1)
        rw [if_neg hround]
        unfold pmfProbClassical
        exact pmfProb_le_one _ _)
  have hsum : (∑ round ∈ Finset.range roundCount,
      quartileSourceFailureBudget delta round) =
      ∑ round ∈ Finset.range roundCount,
        (if round < roundCount then quartileSourceFailureBudget delta round else 1) := by
    apply Finset.sum_congr rfl
    intro round hround
    rw [if_pos (Finset.mem_range.mp hround)]
  have hbudget := quartileSourceFailureBudget_sum_le delta hdelta roundCount
  simpa only [outcomeLaw, score] using (by
    calc
      1 - delta ≤ 1 - ∑ round ∈ Finset.range roundCount,
          quartileSourceFailureBudget delta round := by linarith
      _ = 1 - ∑ round ∈ Finset.range roundCount,
          (if round < roundCount then quartileSourceFailureBudget delta round else 1) := by
            rw [hsum]
      _ ≤ _ := hgeneric)

/--
The source's floored QE schedule has the generic fresh-round retention
guarantee as soon as its explicit one-round tails fit a chosen budget.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_sum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (error t : ℕ → ℝ)
    (initial : Finset Arm) (hinitial : initial.Nonempty)
    (hcount : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty → 0 < quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active)
    (herror : ∀ round, round < roundCount → 0 ≤ error round)
    (ht : ∀ round, round < roundCount → 0 ≤ t round)
    (failureBudget : ℕ → ℝ)
    (hfailureBudgetNonneg : ∀ round, round < roundCount → 0 ≤ failureBudget round)
    (hfailureBudget : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty → quartileBudgetRoundFailureBound
        (quartileSourceRoundBudget totalBudget) error t round active ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  simpa [quartileSourceBudgetOutcomeLaw] using
    (quartileBudgetRounds_near_initial_maximum_probability_ge_one_sub_sum
      mean hmean roundCount (quartileSourceRoundBudget totalBudget) totalBudget
      (fun round _ => quartileSourceRoundBudget_le_totalBudget totalBudget round)
      error t initial hinitial hcount herror ht failureBudget hfailureBudgetNonneg hfailureBudget)

/--
Instantiating the prior theorem with the source's summable confidence schedule
gives a literal `1 - delta` QE retention statement.  The supplied premise is
the remaining numerical tail calculation, rather than an assumed PAC result.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (error t : ℕ → ℝ)
    (initial : Finset Arm) (hinitial : initial.Nonempty) (delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hcount : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty → 0 < quartilePerArmSampleCount
        (quartileSourceRoundBudget totalBudget) round active)
    (herror : ∀ round, round < roundCount → 0 ≤ error round)
    (ht : ∀ round, round < roundCount → 0 ≤ t round)
    (hfailureBudget : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty → quartileBudgetRoundFailureBound
        (quartileSourceRoundBudget totalBudget) error t round active ≤
          quartileSourceFailureBudget delta round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  have hrounds := quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_sum
    mean hmean roundCount totalBudget error t initial hinitial hcount herror ht
    (quartileSourceFailureBudget delta)
    (fun round hround => quartileSourceFailureBudget_nonneg hdelta round)
    hfailureBudget
  have hsum := quartileSourceFailureBudget_sum_le delta hdelta roundCount
  calc
    1 - delta ≤ 1 - ∑ round ∈ Finset.range roundCount,
        quartileSourceFailureBudget delta round := by linarith
    _ ≤ _ := hrounds

/--
The deterministic per-arm count on a reachable source-QE round.  This makes
the error schedule independent of the random active-set representative while
retaining the exact tie-broken survivor recurrence.
-/
noncomputable def quartileSourceScheduledPerArmSampleCount
    (totalBudget initialCount round : ℕ) : ℕ :=
  quartileSourceRoundBudget totalBudget round /
    quartileSurvivorCountIter round initialCount

/-- The explicit finite confidence radius used for the source QE tail. -/
noncomputable def quartileSourceError
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ) : ℝ :=
  Real.sqrt ((2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
    (2 * (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ)))

/-- On a reachable state, the state-dependent quotient is the scheduled quotient. -/
theorem quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
    {Arm : Type*} (totalBudget initialCount round : ℕ) (active : Finset Arm)
    (hcard : active.card = quartileSurvivorCountIter round initialCount) :
    quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget) round active =
      quartileSourceScheduledPerArmSampleCount totalBudget initialCount round := by
  simp [quartilePerArmSampleCount, quartileSourceScheduledPerArmSampleCount, hcard]

theorem quartileSourceError_nonneg
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ) :
    0 ≤ quartileSourceError totalBudget initialCount delta round :=
  Real.sqrt_nonneg _

/-- The source QE radius, set to zero after the deterministic three-arm
terminal condition.  The source switches to its final uniform stage there, so
post-terminal QE radii must not enter the accumulated QE loss. -/
noncomputable def quartileSourceTerminalError
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ) : ℝ :=
  if 4 ≤ quartileSurvivorCountIter round initialCount then
    quartileSourceError totalBudget initialCount delta round
  else 0

theorem quartileSourceTerminalError_nonneg
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ) :
    0 ≤ quartileSourceTerminalError totalBudget initialCount delta round := by
  unfold quartileSourceTerminalError
  split
  · exact quartileSourceError_nonneg totalBudget initialCount delta round
  · positivity

/-- On a nonterminal source round, the terminal-aware radius is exactly the
explicit source square-root radius. -/
theorem quartileSourceTerminalError_eq_sourceError
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ)
    (hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount) :
    quartileSourceTerminalError totalBudget initialCount delta round =
      quartileSourceError totalBudget initialCount delta round := by
  simp [quartileSourceTerminalError, hnonterminal]

/-- After at least one QE round per initial arm, the deterministic survivor
count is terminal and the terminal-aware QE radius vanishes. -/
theorem quartileSourceTerminalError_eq_zero_of_initialCount_le_round
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ)
    (hround : initialCount ≤ round) :
    quartileSourceTerminalError totalBudget initialCount delta round = 0 := by
  unfold quartileSourceTerminalError
  rw [if_neg]
  intro hnonterminal
  have hterminal : quartileSurvivorCountIter round initialCount ≤ 3 :=
    quartileSurvivorCountIter_le_three_of_le_roundCount round initialCount hround
  omega

/-- A terminal-aware QE loss sum has no contribution after the finite
score-independent stopping horizon. -/
theorem quartileSourceTerminalError_sum_eq_sum_before_initialCount
    (totalBudget initialCount : ℕ) (delta : ℝ) (roundCount : ℕ)
    (horizon : initialCount ≤ roundCount) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError totalBudget initialCount delta round) =
      ∑ round ∈ Finset.range initialCount,
        2 * quartileSourceTerminalError totalBudget initialCount delta round := by
  refine (Finset.sum_subset (Finset.range_subset_range.mpr horizon) ?_).symm
  intro round hround hbefore
  have hinitialLe : initialCount ≤ round := by
    exact Nat.le_of_not_gt (by
      intro hlt
      exact hbefore (Finset.mem_range.mpr hlt))
  rw [quartileSourceTerminalError_eq_zero_of_initialCount_le_round
    totalBudget initialCount delta round hinitialLe]
  ring

/-- A source-shaped geometric envelope for the direct QE radius calculation.
The factor `r + 1` is a deliberately simple majorant for the square-root
confidence correction; its geometric sum is finite independently of the arm
count and QE horizon. -/
noncomputable def quartileSourceGeometricTailEnvelope
    (scale : ℝ) (round : ℕ) : ℝ :=
  scale * ((round + 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round

theorem quartileSourceGeometricTailEnvelope_nonneg
    {scale : ℝ} (hscale : 0 ≤ scale) (round : ℕ) :
    0 ≤ quartileSourceGeometricTailEnvelope scale round := by
  unfold quartileSourceGeometricTailEnvelope
  exact mul_nonneg
    (mul_nonneg hscale (Nat.cast_nonneg _))
    (pow_nonneg quartileSourceFailureDecay_pos.le _)

theorem quartileSourceGeometricTailEnvelope_pos
    {scale : ℝ} (hscale : 0 < scale) (round : ℕ) :
    0 < quartileSourceGeometricTailEnvelope scale round := by
  unfold quartileSourceGeometricTailEnvelope
  exact mul_pos
    (mul_pos hscale (by exact_mod_cast Nat.succ_pos round))
    (pow_pos quartileSourceFailureDecay_pos _)

/-- Every finite partial sum of the source-shaped envelope is bounded by the
closed geometric-series value `scale / (1 - exp(-0.1))²`. -/
theorem quartileSourceGeometricTailEnvelope_sum_le
    {scale : ℝ} (hscale : 0 ≤ scale) (roundCount : ℕ) :
    (∑ round ∈ Finset.range roundCount,
      quartileSourceGeometricTailEnvelope scale round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  have hnorm : ‖quartileSourceFailureDecay‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos quartileSourceFailureDecay_pos]
    exact quartileSourceFailureDecay_lt_one
  have hsummable : Summable (fun round : ℕ =>
      (((round + 1).choose 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round) :=
    summable_choose_mul_geometric_of_norm_lt_one 1 hnorm
  have hbase :
      (∑ round ∈ Finset.range roundCount,
        ((round + 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round) ≤
        1 / (1 - quartileSourceFailureDecay) ^ 2 := by
    calc
      (∑ round ∈ Finset.range roundCount,
          ((round + 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round) =
          ∑ round ∈ Finset.range roundCount,
            (((round + 1).choose 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round := by
              apply Finset.sum_congr rfl
              intro round _
              simp
      _ ≤ ∑' round : ℕ,
          (((round + 1).choose 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round :=
        hsummable.sum_le_tsum (Finset.range roundCount) (by
          intro round _
          exact mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg quartileSourceFailureDecay_pos.le _))
      _ = 1 / (1 - quartileSourceFailureDecay) ^ (1 + 1) :=
        tsum_choose_mul_geometric_of_norm_lt_one 1 hnorm
      _ = 1 / (1 - quartileSourceFailureDecay) ^ 2 := by norm_num
  calc
    (∑ round ∈ Finset.range roundCount,
        quartileSourceGeometricTailEnvelope scale round) =
        scale * ∑ round ∈ Finset.range roundCount,
          ((round + 1 : ℕ) : ℝ) * quartileSourceFailureDecay ^ round := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro round _
            unfold quartileSourceGeometricTailEnvelope
            ring
    _ ≤ scale * (1 / (1 - quartileSourceFailureDecay) ^ 2) :=
      mul_le_mul_of_nonneg_left hbase hscale
    _ = scale / (1 - quartileSourceFailureDecay) ^ 2 := by ring

/-- Reducing the source rate calculation to its one-round numerical core:
once each terminal-aware QE loss is bounded by the geometric envelope, the
entire finite accumulated loss has a horizon-independent closed bound. -/
theorem quartileSourceTerminalError_sum_le_of_geometricEnvelope
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (roundCount : ℕ)
    (hscale : 0 ≤ scale)
    (hbound : ∀ round, round < roundCount →
      2 * quartileSourceTerminalError totalBudget initialCount delta round ≤
        quartileSourceGeometricTailEnvelope scale round) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError totalBudget initialCount delta round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  calc
    (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceTerminalError totalBudget initialCount delta round) ≤
        ∑ round ∈ Finset.range roundCount,
          quartileSourceGeometricTailEnvelope scale round := by
            apply Finset.sum_le_sum
            intro round hround
            exact hbound round (Finset.mem_range.mp hround)
    _ ≤ scale / (1 - quartileSourceFailureDecay) ^ 2 :=
      quartileSourceGeometricTailEnvelope_sum_le hscale roundCount

/-- A direct one-round radius calculation for the source schedule.  This
separates the analytic allocation lower bound from the probabilistic QE
argument: any positive target radius follows once the displayed real sample
threshold is met. -/
theorem quartileSourceError_le_of_scheduledSampleCount
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ) (target : ℝ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (htarget : 0 < target)
    (hcount :
      (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * target ^ 2) ≤
          (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ)) :
    quartileSourceError totalBudget initialCount delta round ≤ target := by
  let confidence := quartileSourceFailureBudget delta round
  let sampleCount := quartileSourceScheduledPerArmSampleCount totalBudget initialCount round
  let numerator : ℝ := 2 + Real.log (2 / confidence)
  have hconfidencePos : 0 < confidence :=
    quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : confidence ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / confidence := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hnumPos : 0 < numerator := by
    dsimp [numerator]
    have hlog : 0 ≤ Real.log (2 / confidence) := Real.log_nonneg hratio
    linarith
  have htargetSqPos : 0 < 2 * target ^ 2 := by positivity
  have hcount' : numerator / (2 * target ^ 2) ≤ (sampleCount : ℝ) := by
    simpa [numerator, confidence, sampleCount] using hcount
  have hsamplePos : 0 < (sampleCount : ℝ) := by
    have hrequiredPos : 0 < numerator / (2 * target ^ 2) :=
      div_pos hnumPos htargetSqPos
    exact hrequiredPos.trans_le hcount'
  have hscaled : numerator ≤ (sampleCount : ℝ) * (2 * target ^ 2) :=
    (div_le_iff₀ htargetSqPos).mp hcount'
  have hinside : numerator / (2 * (sampleCount : ℝ)) ≤ target ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (sampleCount : ℝ))).mpr
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hinside
  change Real.sqrt (numerator / (2 * (sampleCount : ℝ))) ≤ target
  calc
    Real.sqrt (numerator / (2 * (sampleCount : ℝ))) ≤ Real.sqrt (target ^ 2) := hsqrt
    _ = target := Real.sqrt_sq htarget.le

/-- A sufficient one-round direct allocation bound for the source-shaped
geometric envelope.  This is the exact floor/allocation numerical obligation
left before the source's sharp global rate follows from summation. -/
theorem two_mul_quartileSourceTerminalError_le_geometricEnvelope_of_scheduledSampleCount
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (hcount : 4 ≤ quartileSurvivorCountIter round initialCount →
      (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
          (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ)) :
    2 * quartileSourceTerminalError totalBudget initialCount delta round ≤
      quartileSourceGeometricTailEnvelope scale round := by
  by_cases hnonterminal : 4 ≤ quartileSurvivorCountIter round initialCount
  · rw [quartileSourceTerminalError_eq_sourceError totalBudget initialCount delta round
      hnonterminal]
    have htarget : 0 < quartileSourceGeometricTailEnvelope scale round / 2 :=
      div_pos (quartileSourceGeometricTailEnvelope_pos hscale round) (by norm_num)
    have herror := quartileSourceError_le_of_scheduledSampleCount
      totalBudget initialCount delta round
      (quartileSourceGeometricTailEnvelope scale round / 2)
      hdelta hdeltaLeOne htarget (hcount hnonterminal)
    linarith
  · rw [quartileSourceTerminalError, if_neg hnonterminal]
    simpa using quartileSourceGeometricTailEnvelope_nonneg hscale.le round

/-- Finite accumulated direct-radius bound from the source schedule's
per-round lower allocation inequalities.  The next rate boundary is proving
these inequalities from the floored geometric `Q_r` allocation at a single
explicit total budget. -/
theorem quartileSourceTerminalError_sum_le_closed_of_scheduledSampleCount
    (totalBudget initialCount : ℕ) (delta scale : ℝ) (roundCount : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) (hscale : 0 < scale)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round initialCount →
      (2 + Real.log (2 / quartileSourceFailureBudget delta round)) /
        (2 * (quartileSourceGeometricTailEnvelope scale round / 2) ^ 2) ≤
          (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ)) :
    (∑ round ∈ Finset.range roundCount,
      2 * quartileSourceTerminalError totalBudget initialCount delta round) ≤
      scale / (1 - quartileSourceFailureDecay) ^ 2 := by
  apply quartileSourceTerminalError_sum_le_of_geometricEnvelope
    totalBudget initialCount delta scale roundCount hscale.le
  intro round hround
  exact two_mul_quartileSourceTerminalError_le_geometricEnvelope_of_scheduledSampleCount
    totalBudget initialCount delta scale round hdelta hdeltaLeOne hscale
    (hcount round hround)

/--
At its explicit confidence radius, a nonzero deterministic source allocation
has exactly the desired Hoeffding factor.  The harmless `exp (-2)` margin is
what also controls the survivor-count Chernoff term.
-/
theorem quartileSourceHoeffdingFactor_eq
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcount : 0 < quartileSourceScheduledPerArmSampleCount totalBudget initialCount round) :
    Real.exp
      (-((quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
        quartileSourceError totalBudget initialCount delta round) ^ 2 /
        (2 * (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
          (1 / 4 : ℝ))) =
      Real.exp (-2) * quartileSourceFailureBudget delta round / 2 := by
  let sampleCount := quartileSourceScheduledPerArmSampleCount totalBudget initialCount round
  let confidence := quartileSourceFailureBudget delta round
  have hcountReal : 0 < (sampleCount : ℝ) := by exact_mod_cast hcount
  have hconfidencePos : 0 < confidence := by
    exact quartileSourceFailureBudget_pos hdelta round
  have hconfidenceLeOne : confidence ≤ 1 := by
    exact (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  have hratio : 1 ≤ 2 / confidence := by
    apply (le_div_iff₀ hconfidencePos).mpr
    linarith
  have hinsideNonneg :
      0 ≤ (2 + Real.log (2 / confidence)) / (2 * (sampleCount : ℝ)) := by
    exact div_nonneg (by linarith [Real.log_nonneg hratio]) (by positivity)
  have herrorSq : quartileSourceError totalBudget initialCount delta round ^ 2 =
      (2 + Real.log (2 / confidence)) / (2 * (sampleCount : ℝ)) := by
    unfold quartileSourceError
    change Real.sqrt ((2 + Real.log (2 / confidence)) / (2 * (sampleCount : ℝ))) ^ 2 = _
    exact Real.sq_sqrt hinsideNonneg
  have hexponent :
      -((sampleCount : ℝ) * quartileSourceError totalBudget initialCount delta round) ^ 2 /
        (2 * (sampleCount : ℝ) * (1 / 4 : ℝ)) =
        -(2 + Real.log (2 / confidence)) := by
    rw [show ((sampleCount : ℝ) * quartileSourceError totalBudget initialCount delta round) ^ 2 =
        (sampleCount : ℝ) ^ 2 *
          quartileSourceError totalBudget initialCount delta round ^ 2 by ring,
      herrorSq]
    field_simp [ne_of_gt hcountReal]
    ring
  calc
    Real.exp
        (-((quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
          quartileSourceError totalBudget initialCount delta round) ^ 2 /
          (2 * (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
            (1 / 4 : ℝ))) =
        Real.exp (-(2 + Real.log (2 / confidence))) := by
          simpa [sampleCount] using congrArg Real.exp hexponent
    _ = Real.exp (-2) * confidence / 2 := by
          rw [show -(2 + Real.log (2 / confidence)) = -2 + -Real.log (2 / confidence) by ring,
            Real.exp_add, Real.exp_neg, Real.exp_neg,
            Real.exp_log (div_pos (by norm_num) hconfidencePos)]
          field_simp [ne_of_gt hconfidencePos]
    _ = Real.exp (-2) * quartileSourceFailureBudget delta round / 2 := by rfl

/-- The explicit source radius makes the individual Hoeffding factor small enough. -/
theorem quartileSourceHoeffdingFactor_le_exp_neg_two
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcount : 0 < quartileSourceScheduledPerArmSampleCount totalBudget initialCount round) :
    Real.exp
      (-((quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
        quartileSourceError totalBudget initialCount delta round) ^ 2 /
        (2 * (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
          (1 / 4 : ℝ))) ≤ Real.exp (-2) := by
  rw [quartileSourceHoeffdingFactor_eq totalBudget initialCount delta round hdelta hdeltaLeOne hcount]
  have hconfidenceNonneg : 0 ≤ quartileSourceFailureBudget delta round :=
    quartileSourceFailureBudget_nonneg hdelta.le round
  have hconfidenceLeOne : quartileSourceFailureBudget delta round ≤ 1 :=
    (quartileSourceFailureBudget_le_total hdelta.le round).trans hdeltaLeOne
  nlinarith [Real.exp_pos (-2)]

/-- The two-sided Hoeffding envelope fits the scheduled source failure mass. -/
theorem two_mul_quartileSourceHoeffdingFactor_le_failureBudget
    (totalBudget initialCount : ℕ) (delta : ℝ) (round : ℕ)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcount : 0 < quartileSourceScheduledPerArmSampleCount totalBudget initialCount round) :
    2 * Real.exp
      (-((quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
        quartileSourceError totalBudget initialCount delta round) ^ 2 /
        (2 * (quartileSourceScheduledPerArmSampleCount totalBudget initialCount round : ℝ) *
          (1 / 4 : ℝ))) ≤ quartileSourceFailureBudget delta round := by
  rw [quartileSourceHoeffdingFactor_eq totalBudget initialCount delta round hdelta hdeltaLeOne hcount]
  have hconfidenceNonneg : 0 ≤ quartileSourceFailureBudget delta round :=
    quartileSourceFailureBudget_nonneg hdelta.le round
  have hexpLeOne : Real.exp (-2 : ℝ) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  calc
    2 * (Real.exp (-2) * quartileSourceFailureBudget delta round / 2) =
        Real.exp (-2) * quartileSourceFailureBudget delta round := by ring
    _ ≤ 1 * quartileSourceFailureBudget delta round :=
      mul_le_mul_of_nonneg_right hexpLeOne hconfidenceNonneg
    _ = quartileSourceFailureBudget delta round := by ring

/--
The executable source QE schedule has its literal finite retention bound at
the explicit square-root confidence radius.  The only remaining numerical
premise is that every deterministic nonterminal quotient contains a sample;
the floor convention makes that a genuine lower-budget condition, rather than
an implicit real-arithmetic assumption.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_explicitError
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round initial.card →
      0 < quartileSourceScheduledPerArmSampleCount totalBudget initial.card round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean
          (quartileSourceError totalBudget initial.card delta) initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount,
              2 * quartileSourceError totalBudget initial.card delta round ≤ mean survivor) := by
  apply quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_reachable_hoeffding
    mean hmean roundCount totalBudget
    (quartileSourceError totalBudget initial.card delta) initial hinitial delta hdelta.le
  · intro round _
    exact quartileSourceError_nonneg totalBudget initial.card delta round
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    apply hcount round hround
    omega
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    apply quartileSourceHoeffdingFactor_le_exp_neg_two totalBudget initial.card delta round
      hdelta hdeltaLeOne
    apply hcount round hround
    omega
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    apply two_mul_quartileSourceHoeffdingFactor_le_failureBudget
      totalBudget initial.card delta round hdelta hdeltaLeOne
    apply hcount round hround
    omega

/-- The same source retention theorem with zero QE loss assigned after the
deterministic terminal condition.  Its tail proof is unchanged on every
nonterminal round and terminal rounds have no QE bad event. -/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_terminalError
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round initial.card →
      0 < quartileSourceScheduledPerArmSampleCount totalBudget initial.card round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean
          (quartileSourceTerminalError totalBudget initial.card delta) initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount,
              2 * quartileSourceTerminalError totalBudget initial.card delta round ≤
                mean survivor) := by
  apply quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_reachable_hoeffding
    mean hmean roundCount totalBudget
    (quartileSourceTerminalError totalBudget initial.card delta) initial hinitial delta hdelta.le
  · intro round _
    exact quartileSourceTerminalError_nonneg totalBudget initial.card delta round
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    apply hcount round hround
    omega
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    rw [quartileSourceTerminalError_eq_sourceError totalBudget initial.card delta round (by
      rw [← hcard]
      exact hactive)]
    apply quartileSourceHoeffdingFactor_le_exp_neg_two totalBudget initial.card delta round
      hdelta hdeltaLeOne
    apply hcount round hround
    omega
  · intro round hround active hcard hactive
    rw [quartilePerArmSampleCount_eq_sourceScheduled_of_card_eq
      totalBudget initial.card round active hcard]
    rw [quartileSourceTerminalError_eq_sourceError totalBudget initial.card delta round (by
      rw [← hcard]
      exact hactive)]
    apply two_mul_quartileSourceHoeffdingFactor_le_failureBudget
      totalBudget initial.card delta round hdelta hdeltaLeOne
    apply hcount round hround
    omega

/-- A round budget at least as large as its deterministic active count gives each arm a sample. -/
theorem quartileSourceScheduledPerArmSampleCount_pos_of_roundBudget
    (totalBudget initialCount round : ℕ)
    (hactive : 0 < quartileSurvivorCountIter round initialCount)
    (hbudget : quartileSurvivorCountIter round initialCount ≤
      quartileSourceRoundBudget totalBudget round) :
    0 < quartileSourceScheduledPerArmSampleCount totalBudget initialCount round := by
  unfold quartileSourceScheduledPerArmSampleCount
  exact Nat.div_pos hbudget hactive

/--
The floor convention preserves any natural deterministic active-count bound
that already holds for the displayed real source allocation.
-/
theorem quartileSurvivorCountIter_le_quartileSourceRoundBudget_of_real
    (totalBudget initialCount round : ℕ)
    (hbound : (quartileSurvivorCountIter round initialCount : ℝ) ≤
      (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round *
        (totalBudget : ℝ)) :
    quartileSurvivorCountIter round initialCount ≤
      quartileSourceRoundBudget totalBudget round := by
  unfold quartileSourceRoundBudget
  exact Nat.le_floor hbound

/-- The positive real coefficient multiplying the source total budget in one QE round. -/
noncomputable def quartileSourceRoundBudgetWeight (round : ℕ) : ℝ :=
  (1 - quartileSourceBudgetDecay) * quartileSourceBudgetDecay ^ round

theorem quartileSourceRoundBudgetWeight_pos (round : ℕ) :
    0 < quartileSourceRoundBudgetWeight round := by
  unfold quartileSourceRoundBudgetWeight
  exact mul_pos (sub_pos.mpr quartileSourceBudgetDecay_lt_one)
    (pow_pos quartileSourceBudgetDecay_pos _)

/--
The least transparent-real target whose ceiling makes a source QE round large
enough to allocate at least one sample to every deterministic survivor.
-/
noncomputable def quartileSourceRoundBudgetRequirement
    (initialCount round : ℕ) : ℕ :=
  ⌈(quartileSurvivorCountIter round initialCount : ℝ) /
    quartileSourceRoundBudgetWeight round⌉₊

/--
Meeting the explicit per-round ceiling requirement makes the floored source
allocation cover its deterministic active-set cardinality.
-/
theorem quartileSurvivorCountIter_le_quartileSourceRoundBudget_of_requirement
    (totalBudget initialCount round : ℕ)
    (hrequirement : quartileSourceRoundBudgetRequirement initialCount round ≤ totalBudget) :
    quartileSurvivorCountIter round initialCount ≤
      quartileSourceRoundBudget totalBudget round := by
  have hweightPos : 0 < quartileSourceRoundBudgetWeight round :=
    quartileSourceRoundBudgetWeight_pos round
  have hceil :
      (quartileSurvivorCountIter round initialCount : ℝ) /
        quartileSourceRoundBudgetWeight round ≤
        (quartileSourceRoundBudgetRequirement initialCount round : ℝ) := by
    exact Nat.le_ceil _
  have hrequirementReal :
      (quartileSourceRoundBudgetRequirement initialCount round : ℝ) ≤ totalBudget := by
    exact_mod_cast hrequirement
  apply quartileSurvivorCountIter_le_quartileSourceRoundBudget_of_real
    totalBudget initialCount round
  change (quartileSurvivorCountIter round initialCount : ℝ) ≤
    quartileSourceRoundBudgetWeight round * (totalBudget : ℝ)
  have hscaled : (quartileSurvivorCountIter round initialCount : ℝ) ≤
      (totalBudget : ℝ) * quartileSourceRoundBudgetWeight round :=
    (div_le_iff₀ hweightPos).mp (hceil.trans hrequirementReal)
  simpa [mul_comm] using hscaled

/--
The finite maximum of the explicit per-round requirements over a chosen QE
horizon.  It is the smallest displayed natural budget sufficient for every
such one-sample allocation condition under the fixed floor convention.
-/
noncomputable def quartileSourceTotalBudgetRequirement
    (initialCount roundCount : ℕ) : ℕ :=
  (Finset.range roundCount).sup (quartileSourceRoundBudgetRequirement initialCount)

theorem quartileSourceRoundBudgetRequirement_le_totalBudgetRequirement
    (initialCount roundCount round : ℕ) (hround : round < roundCount) :
    quartileSourceRoundBudgetRequirement initialCount round ≤
      quartileSourceTotalBudgetRequirement initialCount roundCount := by
  unfold quartileSourceTotalBudgetRequirement
  exact Finset.le_sup (Finset.mem_range.mpr hround)

/--
Convenient budget-form corollary of the explicit source confidence schedule.
It isolates all floor effects in a visible per-round lower-bound condition.
-/
theorem quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_explicitError_of_budget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (delta : ℝ) (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1)
    (hbudget : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round initial.card →
      quartileSurvivorCountIter round initial.card ≤
        quartileSourceRoundBudget totalBudget round) :
    1 - delta ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean
          (quartileSourceError totalBudget initial.card delta) initial
          (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              (quartileSourceRoundBudget totalBudget) totalBudget round active
              (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount,
              2 * quartileSourceError totalBudget initial.card delta round ≤ mean survivor) := by
  apply quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_explicitError
    mean hmean roundCount totalBudget initial hinitial delta hdelta hdeltaLeOne
  intro round hround hactive
  apply quartileSourceScheduledPerArmSampleCount_pos_of_roundBudget
    totalBudget initial.card round
  · omega
  · exact hbudget round hround hactive

end ZhouChenLi2014OptimalPACMultipleArm
