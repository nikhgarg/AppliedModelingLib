import ZhouChenLi2014OptimalPACMultipleArm.QuartileAccuracyBudget
import ZhouChenLi2014OptimalPACMultipleArm.QuartileUniformFinal

/-!
# Source QE schedule followed by its uniform final stage

This file is the concrete finite-PMF correctness composition for the source's
floored QE schedule and the supplement's uniform final batch.  Its remaining
premise is only the visible nonterminal lower-budget condition introduced by
the formalizer's integer convention.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL

/-- The concrete state law of the floored source QE schedule. -/
noncomputable def quartileSourceQEStateLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (delta : ℝ) :
    PMF (Finset Arm × Bool) :=
  freshQuartileRoundsStateLaw mean
    (quartileSourceError totalBudget initial.card delta) initial
    (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
    (adaptiveBatchQuartileScore roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun round hround active => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget round active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount

/-- Every state in the finite source-QE law has the deterministic survivor
cardinality.  Thus the source terminal condition is a pathwise fact, not a
high-probability approximation. -/
theorem quartileSourceQEStateLaw_support_card_eq_iter
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (delta : ℝ)
    (stateFailure : Finset Arm × Bool)
    (hsupport : stateFailure ∈
      (quartileSourceQEStateLaw mean hmean roundCount totalBudget initial delta).support) :
    stateFailure.1.card = quartileSurvivorCountIter roundCount initial.card := by
  simpa [quartileSourceQEStateLaw] using
    (freshQuartileRoundsStateLaw_support_card_eq_iter mean
      (quartileSourceError totalBudget initial.card delta) initial
      (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
      (adaptiveBatchQuartileScore roundCount
        (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
        (fun round hround active => quartilePerArmSampleCount_le_roundCap
          (quartileSourceRoundBudget totalBudget) totalBudget round active
          (quartileSourceRoundBudget_le_totalBudget totalBudget round)))
      roundCount stateFailure hsupport)

/-- At the source terminal horizon, every state in its QE law has at most
three active arms. -/
theorem quartileSourceQEStateLaw_support_card_le_three
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (delta : ℝ)
    (stateFailure : Finset Arm × Bool)
    (hsupport : stateFailure ∈
      (quartileSourceQEStateLaw mean hmean roundCount totalBudget initial delta).support)
    (hroundCount : initial.card ≤ roundCount) :
    stateFailure.1.card ≤ 3 := by
  rw [quartileSourceQEStateLaw_support_card_eq_iter mean hmean roundCount totalBudget initial
    delta stateFailure hsupport]
  exact quartileSurvivorCountIter_le_three_of_le_roundCount roundCount initial.card hroundCount

/-- The source QE state law with no further accumulated QE loss after the
deterministic three-arm terminal condition. -/
noncomputable def quartileSourceTerminalQEStateLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm) (delta : ℝ) :
    PMF (Finset Arm × Bool) :=
  freshQuartileRoundsStateLaw mean
    (quartileSourceTerminalError totalBudget initial.card delta) initial
    (quartileSourceBudgetOutcomeLaw mean hmean roundCount totalBudget)
    (adaptiveBatchQuartileScore roundCount
      (quartilePerArmSampleCount (quartileSourceRoundBudget totalBudget)) totalBudget
      (fun round hround active => quartilePerArmSampleCount_le_roundCap
        (quartileSourceRoundBudget totalBudget) totalBudget round active
        (quartileSourceRoundBudget_le_totalBudget totalBudget round))) roundCount

/-- The complete finite PMF of source QE followed by the tagged uniform final batch. -/
noncomputable def quartileSourceUniformFinalJointLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (deltaQE epsilon deltaFinal : ℝ) :
    PMF ((Finset Arm × Bool) × canonicalQuartileUniformFinalOutcome Arm epsilon deltaFinal) :=
  (quartileSourceQEStateLaw mean hmean roundCount totalBudget initial deltaQE).bind
    (fun stateFailure =>
      (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
        (fun outcome => (stateFailure, outcome)))

/-- The complete source QE-plus-uniform-final PMF using the terminal-aware QE
loss schedule.  Its state transition kernel is unchanged; only post-terminal
loss accounting is removed. -/
noncomputable def quartileSourceTerminalUniformFinalJointLaw
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (initial : Finset Arm)
    (deltaQE epsilon deltaFinal : ℝ) :
    PMF ((Finset Arm × Bool) × canonicalQuartileUniformFinalOutcome Arm epsilon deltaFinal) :=
  (quartileSourceTerminalQEStateLaw mean hmean roundCount totalBudget initial deltaQE).bind
    (fun stateFailure =>
      (canonicalQuartileUniformFinalOutcomeLaw mean hmean epsilon deltaFinal stateFailure.1).map
        (fun outcome => (stateFailure, outcome)))

/--
The actual source QE schedule and concrete final uniform batch return an arm
within the accumulated QE loss plus the final-stage accuracy.  This is a
finite correctness theorem, separate from the source's still-active sharp
global resource-rate calculation and sequential replay.
-/
theorem quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilon deltaFinal : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilon : 0 < epsilon) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hbudget : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round (Fintype.card Arm) →
      quartileSurvivorCountIter round (Fintype.card Arm) ≤
        quartileSourceRoundBudget totalBudget round) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
          deltaQE epsilon deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean
          ((∑ round ∈ Finset.range roundCount,
            2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round) + epsilon)
          (canonicalQuartileUniformFinalOutput epsilon deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  classical
  let loss : ℝ := ∑ round ∈ Finset.range roundCount,
    2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round
  let qeLaw : PMF (Finset Arm × Bool) :=
    quartileSourceQEStateLaw mean hmean roundCount totalBudget Finset.univ deltaQE
  have hqe : 1 - deltaQE ≤ pmfProbClassical
      qeLaw (quartileStateNearInitialMaximum mean Finset.univ Finset.univ_nonempty loss) := by
    rw [pmfProbClassical_eq_pmfProb]
    have hsource :=
      quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_explicitError_of_budget
        mean hmean roundCount totalBudget Finset.univ Finset.univ_nonempty deltaQE
        hdeltaQE hdeltaQELeOne (by
          intro round hround hactive
          simpa using hbudget round hround hactive)
    calc
      1 - deltaQE ≤ pmfProb qeLaw (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean Finset.univ Finset.univ_nonempty).val - loss ≤
            mean survivor) := by
            simpa [qeLaw, loss] using hsource
      _ = pmfProb qeLaw
          (quartileStateNearInitialMaximum mean Finset.univ Finset.univ_nonempty loss) := by
            apply pmfProb_congr
            intro stateFailure
            rfl
  simpa [quartileSourceUniformFinalJointLaw] using
    (quartileUniformFinalJoint_epsilonPAC_probability_ge_one_sub
      mean hmean Finset.univ Finset.univ_nonempty (fun arm => Finset.mem_univ arm)
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round)
      epsilon deltaQE deltaFinal
      qeLaw
      hdeltaQE.le hdeltaFinal hdeltaFinalLeOne hepsilon hqe)

/-- End-to-end finite PAC theorem with the terminal-aware QE loss schedule.
Its only numerical premise is positivity of the nonterminal floored per-arm
allocations; the final-stage accuracy is then added exactly once. -/
theorem quartileSourceTerminalUniformFinalJoint_epsilonPAC_probability_ge_one_sub
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilon deltaFinal : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilon : 0 < epsilon) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hcount : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round (Fintype.card Arm) →
      0 < quartileSourceScheduledPerArmSampleCount totalBudget (Fintype.card Arm) round) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceTerminalUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
          deltaQE epsilon deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean
          ((∑ round ∈ Finset.range roundCount,
            2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round) + epsilon)
          (canonicalQuartileUniformFinalOutput epsilon deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  classical
  let loss : ℝ := ∑ round ∈ Finset.range roundCount,
    2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round
  let qeLaw : PMF (Finset Arm × Bool) :=
    quartileSourceTerminalQEStateLaw mean hmean roundCount totalBudget Finset.univ deltaQE
  have hqe : 1 - deltaQE ≤ pmfProbClassical
      qeLaw (quartileStateNearInitialMaximum mean Finset.univ Finset.univ_nonempty loss) := by
    rw [pmfProbClassical_eq_pmfProb]
    have hsource :=
      quartileSourceBudgetRounds_near_initial_maximum_probability_ge_one_sub_delta_of_terminalError
        mean hmean roundCount totalBudget Finset.univ Finset.univ_nonempty deltaQE
        hdeltaQE hdeltaQELeOne (by
          intro round hround hnonterminal
          simpa using hcount round hround hnonterminal)
    calc
      1 - deltaQE ≤ pmfProb qeLaw (fun stateFailure => stateFailure.2 = false ∧ ∃ survivor,
          survivor ∈ stateFailure.1 ∧
          mean (quartileRoundMeanMaximizer mean Finset.univ Finset.univ_nonempty).val - loss ≤
            mean survivor) := by
            simpa [qeLaw, loss] using hsource
      _ = pmfProb qeLaw
          (quartileStateNearInitialMaximum mean Finset.univ Finset.univ_nonempty loss) := by
            apply pmfProb_congr
            intro stateFailure
            rfl
  simpa [quartileSourceTerminalUniformFinalJointLaw] using
    (quartileUniformFinalJoint_epsilonPAC_probability_ge_one_sub
      mean hmean Finset.univ Finset.univ_nonempty (fun arm => Finset.mem_univ arm)
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceTerminalError totalBudget (Fintype.card Arm) deltaQE round)
      epsilon deltaQE deltaFinal
      qeLaw
      hdeltaQE.le hdeltaFinal hdeltaFinalLeOne hepsilon hqe)

/--
Target-accuracy form of the source-QE-plus-uniform-final theorem.  The
accumulated-radius inequality is intentionally an explicit mathematical
premise until the source's hidden global budget constant is derived.
-/
theorem quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_totalError
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hbudget : ∀ round, round < roundCount →
      4 ≤ quartileSurvivorCountIter round (Fintype.card Arm) →
      quartileSurvivorCountIter round (Fintype.card Arm) ≤
        quartileSourceRoundBudget totalBudget round)
    (haccuracy :
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round) + epsilonFinal ≤
        epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
          deltaQE epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  have hjoint := quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub
    mean hmean roundCount totalBudget deltaQE epsilonFinal deltaFinal
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne hbudget
  calc
    1 - (deltaQE + deltaFinal) ≤
        pmfProbClassical
          (quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
            deltaQE epsilonFinal deltaFinal)
          (fun stateOutcome => EpsilonPACBestArm mean
            ((∑ round ∈ Finset.range roundCount,
              2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round) + epsilonFinal)
            (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
              stateOutcome.1.1 stateOutcome.2)) := hjoint
    _ ≤ pmfProbClassical
          (quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
            deltaQE epsilonFinal deltaFinal)
          (fun stateOutcome => EpsilonPACBestArm mean epsilon
            (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
              stateOutcome.1.1 stateOutcome.2)) := by
      apply pmfProbClassical_le_of_imp
      intro stateOutcome hpac
      exact epsilonPACBestArm_mono mean
        (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
          stateOutcome.1.1 stateOutcome.2) haccuracy hpac

/--
The same target-accuracy theorem stated with the explicit per-round natural
ceiling requirements induced by the source allocation weight.
-/
theorem quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_requirements
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount totalBudget : ℕ) (deltaQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hrequirement : ∀ round, round < roundCount →
      quartileSourceRoundBudgetRequirement (Fintype.card Arm) round ≤ totalBudget)
    (haccuracy :
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceError totalBudget (Fintype.card Arm) deltaQE round) + epsilonFinal ≤
        epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount totalBudget Finset.univ
          deltaQE epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  apply quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_totalError
    mean hmean roundCount totalBudget deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round hround _
    exact quartileSurvivorCountIter_le_quartileSourceRoundBudget_of_requirement
      totalBudget (Fintype.card Arm) round (hrequirement round hround)
  · exact haccuracy

/--
Fully specified finite-budget specialization: the QE total budget is the
finite maximum of its source-weighted per-round ceiling requirements.  The
only remaining numerical obligation is the transparent accumulated-radius
inequality, not a hidden allocation certificate.
-/
theorem quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_explicitTotalBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonFinal : 0 < epsilonFinal) (hdeltaFinal : 0 < deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (haccuracy :
      (∑ round ∈ Finset.range roundCount,
        2 * quartileSourceError
          (quartileSourceTotalBudgetRequirement (Fintype.card Arm) roundCount)
          (Fintype.card Arm) deltaQE round) + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount
          (quartileSourceTotalBudgetRequirement (Fintype.card Arm) roundCount)
          Finset.univ deltaQE epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  apply quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_requirements
    mean hmean roundCount
    (quartileSourceTotalBudgetRequirement (Fintype.card Arm) roundCount)
    deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round hround
    exact quartileSourceRoundBudgetRequirement_le_totalBudgetRequirement
      (Fintype.card Arm) roundCount round hround
  · exact haccuracy

/--
A fully finite, source-schedule specialization with no unproved budget or
accumulated-radius premise.  The QE total is the maximum of the explicit
per-round accuracy ceilings from `QuartileAccuracyBudget`; this is a
formalizer-specified finite constant convention, rather than an assertion of
the source's unstated sharp big-O constant.
-/
theorem quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_accuracyTotalBudget
    {Arm : Type*} [Fintype Arm] [DecidableEq Arm] [Nonempty Arm]
    (mean : Arm → ℝ) (hmean : ValidBernoulliMeans mean)
    (roundCount : ℕ) (deltaQE epsilonQE epsilonFinal deltaFinal epsilon : ℝ)
    (hdeltaQE : 0 < deltaQE) (hdeltaQELeOne : deltaQE ≤ 1)
    (hepsilonQE : 0 < epsilonQE) (hepsilonFinal : 0 < epsilonFinal)
    (hdeltaFinal : 0 < deltaFinal) (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (haccuracy : epsilonQE + epsilonFinal ≤ epsilon) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical
        (quartileSourceUniformFinalJointLaw mean hmean roundCount
          (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
            roundCount epsilonQE deltaQE)
          Finset.univ deltaQE epsilonFinal deltaFinal)
        (fun stateOutcome => EpsilonPACBestArm mean epsilon
          (canonicalQuartileUniformFinalOutput epsilonFinal deltaFinal
            stateOutcome.1.1 stateOutcome.2)) := by
  apply quartileSourceUniformFinalJoint_epsilonPAC_probability_ge_one_sub_of_totalError
    mean hmean roundCount
    (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
      roundCount epsilonQE deltaQE)
    deltaQE epsilonFinal deltaFinal epsilon
    hdeltaQE hdeltaQELeOne hepsilonFinal hdeltaFinal hdeltaFinalLeOne
  · intro round hround _
    apply quartileSurvivorCountIter_le_sourceRoundBudget_of_accuracyRequirement
      (quartileSourceAccuracyTotalBudgetRequirement (Fintype.card Arm)
        roundCount epsilonQE deltaQE)
      (Fintype.card Arm) epsilonQE deltaQE round hdeltaQE hdeltaQELeOne hepsilonQE
    exact quartileSourceAccuracyRoundBudgetRequirement_le_totalBudgetRequirement
      (Fintype.card Arm) roundCount epsilonQE deltaQE round hround
  · have hinitial : 0 < Fintype.card Arm := Fintype.card_pos
    have herror := quartileSourceError_sum_two_le_epsilonQE_of_totalRequirement
      (Fintype.card Arm) roundCount epsilonQE deltaQE hinitial hdeltaQE hdeltaQELeOne
      hepsilonQE
    linarith

end ZhouChenLi2014OptimalPACMultipleArm
