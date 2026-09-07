import ZhouChenLi2014OptimalPACMultipleArm.QuartileAllocation

/-!
# Fresh composition for Algorithm 1's QE allocation

This is the finite adaptive composition theorem for the actual allocation in
Algorithm 1: after the history-selected active set is known, the round budget
is divided among those arms and a fresh product batch is drawn.  The theorem
keeps every rounding and tail budget as an explicit hypothesis, leaving the
source's hidden-constant rate specialization as a separate numerical task.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL
open MeasureTheory ProbabilityTheory

/-- The source-shaped one-round QE tail expression after integer allocation. -/
noncomputable def quartileBudgetRoundFailureBound {Arm : Type*}
    (roundBudget : ℕ → ℕ) (error t : ℕ → ℝ)
    (round : ℕ) (active : Finset Arm) : ℝ :=
  Real.exp (-((quartilePerArmSampleCount roundBudget round active : ℝ) * error round) ^ 2 /
    (2 * (quartilePerArmSampleCount roundBudget round active : ℝ) * (1 / 4 : ℝ))) +
  Real.exp (-t round * (quartileSurvivorCount active.card : ℝ) +
    (active.card : ℝ) * ((Real.exp (t round) - 1) *
      Real.exp (-((quartilePerArmSampleCount roundBudget round active : ℝ) * error round) ^ 2 /
        (2 * (quartilePerArmSampleCount roundBudget round active : ℝ) * (1 / 4 : ℝ)))))

/--
All state-dependent rounds of the integer Algorithm-1 QE allocation compose
under their actual fresh product PMFs.  On the all-success event, the final
active set retains an arm within the sum of the round losses of the initial
maximum.  No independence is assumed between random active sets from
different rounds.
-/
theorem quartileBudgetRounds_near_initial_maximum_probability_ge_one_sub_sum
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (roundBudget : ℕ → ℕ) (roundCap : ℕ)
    (hcap : ∀ round < roundCount, roundBudget round ≤ roundCap)
    (error t : ℕ → ℝ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (hcount : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty → 0 < quartilePerArmSampleCount roundBudget round active)
    (herror : ∀ round, round < roundCount → 0 ≤ error round)
    (ht : ∀ round, round < roundCount → 0 ≤ t round)
    (failureBudget : ℕ → ℝ)
    (hfailureBudgetNonneg : ∀ round, round < roundCount → 0 ≤ failureBudget round)
    (hfailureBudget : ∀ round, round < roundCount → ∀ active : Finset Arm,
      active.Nonempty →
      quartileBudgetRoundFailureBound roundBudget error t round active ≤ failureBudget round) :
    1 - ∑ round ∈ Finset.range roundCount, failureBudget round ≤
      pmfProb
        (freshQuartileRoundsStateLaw mean error initial
          (quartileBudgetOutcomeLaw mean hmean roundCount roundBudget roundCap hcap)
          (adaptiveBatchQuartileScore roundCount
            (quartilePerArmSampleCount roundBudget) roundCap
            (fun round hround active => quartilePerArmSampleCount_le_roundCap
              roundBudget roundCap round active (hcap round hround))) roundCount)
        (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean initial hinitial).val -
            ∑ round ∈ Finset.range roundCount, 2 * error round ≤ mean survivor) := by
  classical
  let outcomeLaw : AdaptiveOutcomeKernel (Finset Arm)
      (canonicalFreshQuartileOutcome Arm roundCap) :=
    quartileBudgetOutcomeLaw mean hmean roundCount roundBudget roundCap hcap
  let score : ℕ → Finset Arm → canonicalFreshQuartileOutcome Arm roundCap → Arm → ℝ :=
    adaptiveBatchQuartileScore roundCount
    (quartilePerArmSampleCount roundBudget) roundCap
    (fun round hround active => quartilePerArmSampleCount_le_roundCap
      roundBudget roundCap round active (hcap round hround))
  have hgeneric := freshQuartileRounds_near_initial_maximum_probability_ge_one_sub_sum
    mean error initial hinitial outcomeLaw score
    (fun round => if round < roundCount then failureBudget round else 1) roundCount (by
      intro round active
      by_cases hround : round < roundCount
      · change pmfProbClassical (outcomeLaw round active)
            (quartileRoundBad mean error score round active) ≤
            (if round < roundCount then failureBudget round else 1)
        rw [if_pos hround]
        by_cases hactive : active.Nonempty
        · calc
            pmfProbClassical (outcomeLaw round active)
                (quartileRoundBad mean error score round active) ≤
                quartileBudgetRoundFailureBound roundBudget error t round active := by
                  exact quartileBudgetRound_failure_probability_le mean hmean roundCount
                    roundBudget roundCap hcap error round hround active hactive
                    (hcount round hround active hactive) (herror round hround)
                    (t round) (ht round hround)
            _ ≤ failureBudget round := hfailureBudget round hround active hactive
        · simpa [outcomeLaw, score, pmfProbClassical, pmfProb, quartileRoundBad, hactive]
            using hfailureBudgetNonneg round hround
      · change pmfProbClassical (outcomeLaw round active)
            (quartileRoundBad mean error score round active) ≤
            (if round < roundCount then failureBudget round else 1)
        rw [if_neg hround]
        unfold pmfProbClassical
        exact pmfProb_le_one _ _)
  have hsum : (∑ round ∈ Finset.range roundCount, failureBudget round) =
      ∑ round ∈ Finset.range roundCount,
        (if round < roundCount then failureBudget round else 1) := by
    apply Finset.sum_congr rfl
    intro round hround
    rw [if_pos (Finset.mem_range.mp hround)]
  simpa only [outcomeLaw, score] using (by
    calc
      1 - ∑ round ∈ Finset.range roundCount, failureBudget round =
          1 - ∑ round ∈ Finset.range roundCount,
            (if round < roundCount then failureBudget round else 1) := by rw [hsum]
      _ ≤ _ := hgeneric)

end ZhouChenLi2014OptimalPACMultipleArm
