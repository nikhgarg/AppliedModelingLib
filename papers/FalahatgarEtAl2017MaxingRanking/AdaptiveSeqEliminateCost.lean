import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminate

/-!
# Adaptive Seq-Eliminate comparison accounting

Each realized adaptive Compare call reads its pair-specific stream through its
first stopping time.  This file records that exact finite total and proves the
per-call cap from Appendix A.1 lifts to the full Seq-Eliminate execution.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- The realized number of comparison observations used at every Seq-Eliminate call. -/
noncomputable def adaptiveSeqEliminateStoppingTimes {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (epsilon delta : ℝ) (outcome : Ω) : Arm → List Arm → List ℕ
  | _incumbent, [] => []
  | incumbent, challenger :: remaining =>
      adaptiveCompareStoppingTime (observation challenger incumbent) count 0 epsilon delta outcome ::
        adaptiveSeqEliminateStoppingTimes observation count epsilon delta outcome
          (adaptiveCompareStep observation count epsilon delta outcome incumbent challenger) remaining

/-- The adaptive Seq-Eliminate run uses at most its number of calls times the cap. -/
theorem adaptiveSeqEliminateStoppingTimes_sum_le {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (count : ℕ)
    (epsilon delta : ℝ) (outcome : Ω) (initial : Arm) (challengers : List Arm) :
    (adaptiveSeqEliminateStoppingTimes observation count epsilon delta outcome initial challengers).sum ≤
      challengers.length * count := by
  induction challengers generalizing initial with
  | nil => simp [adaptiveSeqEliminateStoppingTimes]
  | cons challenger remaining ih =>
      simp only [adaptiveSeqEliminateStoppingTimes, List.sum_cons, List.length_cons]
      calc
        adaptiveCompareStoppingTime (observation challenger initial) count 0 epsilon delta outcome +
            (adaptiveSeqEliminateStoppingTimes observation count epsilon delta outcome
              (adaptiveCompareStep observation count epsilon delta outcome initial challenger)
              remaining).sum ≤
            count + remaining.length * count :=
          Nat.add_le_add
            (adaptiveCompareStoppingTime_le_count
              (observation challenger initial) count 0 epsilon delta outcome)
            (ih (initial := adaptiveCompareStep observation count epsilon delta outcome initial challenger))
        _ = (remaining.length + 1) * count := by
          simp [Nat.add_mul, Nat.add_comm]

/-- The concrete ceiling-budget form of Theorem 2's finite comparison cap. -/
theorem adaptiveSeqEliminateStoppingTimes_sum_le_ceilingBudget {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (epsilon delta : ℝ)
    (outcome : Ω) (initial : Arm) (challengers : List Arm) :
    (adaptiveSeqEliminateStoppingTimes observation
      (fixedSampleBudget 0 epsilon delta) epsilon delta outcome initial challengers).sum ≤
      challengers.length * fixedSampleBudget 0 epsilon delta := by
  exact adaptiveSeqEliminateStoppingTimes_sum_le observation
    (fixedSampleBudget 0 epsilon delta) epsilon delta outcome initial challengers

/--
Theorem 2's finite resource bound, retaining the executable ceiling correction.
With `challengers.length = |S| - 1` and the source call confidence `δ / |S|`,
this is the exact finite precursor of the printed asymptotic comparison count.
-/
theorem adaptiveSeqEliminateStoppingTimes_real_le_sourceBudget
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (epsilon delta : ℝ)
    (outcome : Ω) (initial : Arm) (challengers : List Arm)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    ((adaptiveSeqEliminateStoppingTimes observation
      (fixedSampleBudget 0 epsilon delta) epsilon delta outcome initial challengers).sum : ℝ) ≤
      (challengers.length : ℝ) *
        (2 / epsilon ^ 2 * Real.log (2 / delta) + 1) := by
  have hcount := adaptiveSeqEliminateStoppingTimes_sum_le_ceilingBudget
    observation epsilon delta outcome initial challengers
  have hcountReal :
      ((adaptiveSeqEliminateStoppingTimes observation
        (fixedSampleBudget 0 epsilon delta) epsilon delta outcome initial challengers).sum : ℝ) ≤
        ((challengers.length * fixedSampleBudget 0 epsilon delta : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hbudget := fixedSampleBudget_lt_realTarget_add_one 0 epsilon delta hdelta hdeltaLeOne
  have hbudget' : (fixedSampleBudget 0 epsilon delta : ℝ) ≤
      2 / epsilon ^ 2 * Real.log (2 / delta) + 1 := by
    simpa only [sub_zero] using le_of_lt hbudget
  calc
    ((adaptiveSeqEliminateStoppingTimes observation
      (fixedSampleBudget 0 epsilon delta) epsilon delta outcome initial challengers).sum : ℝ) ≤
        ((challengers.length * fixedSampleBudget 0 epsilon delta : ℕ) : ℝ) := hcountReal
    _ = (challengers.length : ℝ) * (fixedSampleBudget 0 epsilon delta : ℝ) := by
      norm_num
    _ ≤ (challengers.length : ℝ) *
        (2 / epsilon ^ 2 * Real.log (2 / delta) + 1) :=
      mul_le_mul_of_nonneg_left hbudget' (Nat.cast_nonneg _)

end FalahatgarEtAl2017MaxingRanking
