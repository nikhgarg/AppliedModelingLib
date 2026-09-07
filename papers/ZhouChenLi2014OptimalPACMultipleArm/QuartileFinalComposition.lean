import ZhouChenLi2014OptimalPACMultipleArm.FreshQuartileRounds

/-!
# Attaching a final best-arm stage to Quartile-Elimination

QE leaves a random active set.  This file gives the finite-PMF composition
step needed to attach a fresh final policy without replacing that random set
by a fixed one.  The final stage is deliberately abstract here; its concrete
uniform Bernoulli realization is a separate source-to-model bridge.
-/

namespace ZhouChenLi2014OptimalPACMultipleArm

open AppliedModelingLib PreferenceRL

/-- The all-success QE state: an active survivor remains near the initial maximum. -/
def quartileStateNearInitialMaximum {Arm : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (loss : ℝ) (stateFailure : Finset Arm × Bool) : Prop :=
  stateFailure.2 = false ∧ ∃ survivor, survivor ∈ stateFailure.1 ∧
    mean (quartileRoundMeanMaximizer mean initial hinitial).val - loss ≤ mean survivor

/-- A final output is PAC relative to its current active set. -/
def finalActiveEpsilonPAC {Arm Outcome : Type*}
    (mean : Arm → ℝ) (error : ℝ) (output : Finset Arm → Outcome → Arm)
    (active : Finset Arm) (outcome : Outcome) : Prop :=
  output active outcome ∈ active ∧ ∀ competitor, competitor ∈ active →
    mean competitor - error ≤ mean (output active outcome)

/--
A final active-set PAC output is globally PAC whenever QE retained an arm near
the initial maximum and that initial set contains every candidate arm.
-/
theorem epsilonPACBestArm_of_near_initial_maximum_and_finalActivePAC
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    (mean : Arm → ℝ) (initial active : Finset Arm) (hinitial : initial.Nonempty)
    (hinitialAll : ∀ arm, arm ∈ initial) (loss finalError : ℝ)
    (output : Finset Arm → Outcome → Arm) (outcome : Outcome)
    (hnear : ∃ survivor, survivor ∈ active ∧
      mean (quartileRoundMeanMaximizer mean initial hinitial).val - loss ≤ mean survivor)
    (hfinal : finalActiveEpsilonPAC mean finalError output active outcome) :
    EpsilonPACBestArm mean (loss + finalError) (output active outcome) := by
  intro competitor
  rcases hnear with ⟨survivor, hsurvivor, hnear⟩
  rcases hfinal with ⟨_, hfinal⟩
  have hmaximum : mean competitor ≤
      mean (quartileRoundMeanMaximizer mean initial hinitial).val :=
    mean_le_quartileRoundMeanMaximizer mean initial hinitial
      ⟨competitor, hinitialAll competitor⟩
  have hfinalSurvivor := hfinal survivor hsurvivor
  linarith

/--
Finite-PMF composition of QE with a fresh final active-set policy.  The final
stage need only be PAC conditionally on the QE-success states; no independence
between the selected active set and the final outcome is asserted.
-/
theorem quartileFinalJoint_epsilonPAC_probability_ge_one_sub
    {Arm Outcome : Type*} [Fintype Arm] [DecidableEq Arm]
    [Fintype Outcome] [DecidableEq Outcome]
    (mean : Arm → ℝ) (initial : Finset Arm) (hinitial : initial.Nonempty)
    (hinitialAll : ∀ arm, arm ∈ initial) (loss finalError deltaQE deltaFinal : ℝ)
    (qeStateLaw : PMF (Finset Arm × Bool))
    (finalOutcomeLaw : Finset Arm → PMF Outcome)
    (output : Finset Arm → Outcome → Arm)
    (hdeltaQE : 0 ≤ deltaQE) (hdeltaFinal : 0 ≤ deltaFinal)
    (hdeltaFinalLeOne : deltaFinal ≤ 1)
    (hqe : 1 - deltaQE ≤ pmfProbClassical qeStateLaw
      (quartileStateNearInitialMaximum mean initial hinitial loss))
    (hfinal : ∀ stateFailure,
      quartileStateNearInitialMaximum mean initial hinitial loss stateFailure →
      1 - deltaFinal ≤ pmfProbClassical (finalOutcomeLaw stateFailure.1)
        (finalActiveEpsilonPAC mean finalError output stateFailure.1)) :
    1 - (deltaQE + deltaFinal) ≤
      pmfProbClassical (qeStateLaw.bind fun stateFailure =>
        (finalOutcomeLaw stateFailure.1).map fun outcome => (stateFailure, outcome))
        (fun stateOutcome => EpsilonPACBestArm mean (loss + finalError)
          (output stateOutcome.1.1 stateOutcome.2)) := by
  classical
  rw [pmfProbClassical_eq_pmfProb]
  have hqe' : 1 - deltaQE ≤ pmfProb qeStateLaw
      (quartileStateNearInitialMaximum mean initial hinitial loss) := by
    rw [← pmfProbClassical_eq_pmfProb]
    exact hqe
  have hfinal' : ∀ stateFailure,
      quartileStateNearInitialMaximum mean initial hinitial loss stateFailure →
      1 - deltaFinal ≤ pmfProb (finalOutcomeLaw stateFailure.1)
        (finalActiveEpsilonPAC mean finalError output stateFailure.1) := by
    intro stateFailure hstate
    rw [← pmfProbClassical_eq_pmfProb]
    exact hfinal stateFailure hstate
  have hjoint := pmfProb_bind_map_pair_joint_ge_one_sub
    qeStateLaw (fun stateFailure => finalOutcomeLaw stateFailure.1)
    (quartileStateNearInitialMaximum mean initial hinitial loss)
    (fun stateFailure outcome =>
      finalActiveEpsilonPAC mean finalError output stateFailure.1 outcome)
    deltaQE deltaFinal hdeltaQE hdeltaFinal hdeltaFinalLeOne hqe' hfinal'
  calc
    1 - (deltaQE + deltaFinal) ≤
        pmfProb (qeStateLaw.bind fun stateFailure =>
          (finalOutcomeLaw stateFailure.1).map fun outcome => (stateFailure, outcome))
          (fun stateOutcome =>
            quartileStateNearInitialMaximum mean initial hinitial loss stateOutcome.1 ∧
              finalActiveEpsilonPAC mean finalError output stateOutcome.1.1 stateOutcome.2) :=
      hjoint
    _ ≤ pmfProb (qeStateLaw.bind fun stateFailure =>
          (finalOutcomeLaw stateFailure.1).map fun outcome => (stateFailure, outcome))
          (fun stateOutcome => EpsilonPACBestArm mean (loss + finalError)
            (output stateOutcome.1.1 stateOutcome.2)) := by
      apply pmfProb_le_of_imp
      rintro ⟨stateFailure, outcome⟩ ⟨hstate, hfinalState⟩
      rcases hstate with ⟨_, hnear⟩
      exact epsilonPACBestArm_of_near_initial_maximum_and_finalActivePAC
        mean initial stateFailure.1 hinitial hinitialAll loss finalError output outcome hnear
        hfinalState

end ZhouChenLi2014OptimalPACMultipleArm
