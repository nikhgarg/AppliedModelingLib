import ZhouChenLi2014OptimalPACMultipleArm.AdaptiveBatchQuartileRounds

/-!
# Exact per-round QE allocation

Algorithm 1 allocates a round pull budget across the current active arms.
The source leaves the integer division implicit; here it is the floor budget
per arm, with the unused remainder visibly harmless.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib.PreferenceRL

/-- The integer number of fresh samples assigned to each current active arm. -/
def quartilePerArmSampleCount {Arm : Type*} (roundBudget : ℕ → ℕ)
    (round : ℕ) (active : Finset Arm) : ℕ :=
  roundBudget round / active.card

/-- The completed round uses no more than its allocated total budget. -/
theorem quartilePerArmSampleCount_total_le
    {Arm : Type*} (roundBudget : ℕ → ℕ) (round : ℕ) (active : Finset Arm) :
    active.card * quartilePerArmSampleCount roundBudget round active ≤ roundBudget round := by
  unfold quartilePerArmSampleCount
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

/-- A round budget at least as large as the nonempty active set gives every arm a sample. -/
theorem quartilePerArmSampleCount_pos
    {Arm : Type*} (roundBudget : ℕ → ℕ) (round : ℕ) (active : Finset Arm)
    (hactive : active.Nonempty) (hbudget : active.card ≤ roundBudget round) :
    0 < quartilePerArmSampleCount roundBudget round active := by
  unfold quartilePerArmSampleCount
  exact Nat.div_pos hbudget (Finset.card_pos.mpr hactive)

/-- A global round-cap bounds each state-dependent per-arm allocation. -/
theorem quartilePerArmSampleCount_le_roundCap
    {Arm : Type*} (roundBudget : ℕ → ℕ) (roundCap : ℕ) (round : ℕ) (active : Finset Arm)
    (hcap : roundBudget round ≤ roundCap) :
    quartilePerArmSampleCount roundBudget round active ≤ roundCap := by
  unfold quartilePerArmSampleCount
  exact (Nat.div_le_self _ _).trans hcap

/--
The concrete fresh outcome kernel obtained by dividing each round's total
budget among the history-selected active arms.
-/
noncomputable def quartileBudgetOutcomeLaw {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (roundBudget : ℕ → ℕ) (roundCap : ℕ)
    (hcap : ∀ round < roundCount, roundBudget round ≤ roundCap) :
    AdaptiveOutcomeKernel (Finset Arm) (canonicalFreshQuartileOutcome Arm roundCap) :=
  adaptiveBatchQuartileOutcomeLaw mean hmean roundCount
    (quartilePerArmSampleCount roundBudget) roundCap
    (fun round hround active =>
      quartilePerArmSampleCount_le_roundCap roundBudget roundCap round active (hcap round hround))

/--
The source allocation inherits the concrete state-dependent one-round QE
tail theorem whenever its integer per-arm quotient is positive.
-/
theorem quartileBudgetRound_failure_probability_le
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (roundBudget : ℕ → ℕ) (roundCap : ℕ)
    (hcap : ∀ round < roundCount, roundBudget round ≤ roundCap)
    (error : ℕ → ℝ) (round : ℕ) (hround : round < roundCount)
    (active : Finset Arm) (hactive : active.Nonempty)
    (hcount : 0 < quartilePerArmSampleCount roundBudget round active)
    (herror : 0 ≤ error round) (t : ℝ) (ht : 0 ≤ t) :
    pmfProbClassical (quartileBudgetOutcomeLaw mean hmean roundCount roundBudget roundCap hcap
      round active)
      (quartileRoundBad mean error
        (adaptiveBatchQuartileScore roundCount (quartilePerArmSampleCount roundBudget) roundCap
          (fun round hround active => quartilePerArmSampleCount_le_roundCap
            roundBudget roundCap round active (hcap round hround))) round active) ≤
      Real.exp (-((quartilePerArmSampleCount roundBudget round active : ℝ) * error round) ^ 2 /
        (2 * (quartilePerArmSampleCount roundBudget round active : ℝ) * (1 / 4 : ℝ))) +
      Real.exp (-t * (quartileSurvivorCount active.card : ℝ) +
        (active.card : ℝ) * ((Real.exp t - 1) *
          Real.exp (-((quartilePerArmSampleCount roundBudget round active : ℝ) * error round) ^ 2 /
            (2 * (quartilePerArmSampleCount roundBudget round active : ℝ) * (1 / 4 : ℝ))))) := by
  exact adaptiveBatchQuartileRound_failure_probability_le mean hmean roundCount
    (quartilePerArmSampleCount roundBudget) roundCap
    (fun round hround active => quartilePerArmSampleCount_le_roundCap
      roundBudget roundCap round active (hcap round hround)) error round hround active hactive
    hcount herror t ht

end ZhouChenLi2014OptimalPACMultipleArm
