import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

/-!
# Physical progress of a finite GPS batch trace

For a chronological finite list of literal external batches, the executable
GPS runner reaches every listed epoch under its ordinary positive-capacity,
positive-weight, and nonnegative-work hypotheses.  This is a finite execution
fact: it neither adds a terminal fence nor identifies a source process.

The endpoint-membership theorem is deliberately phrased on the actual list of
external batch epochs.  It is therefore useful when a paper proof chooses a
genuine future source event after a finite deadline and needs to know that the
preterminal execution has physically passed that event.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Under the ordinary executable GPS hypotheses, a chronological finite
batch run never finishes before its initial physical clock. -/
theorem finiteGPSRunBatchTrace_start_le_currentTime
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ j, 0 ≤ batchWork t j) :
    currentTime ≤
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).currentTime := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTrace]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hcurrent_le_event, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j, 0 ≤ batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true ∧ gap.remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hcurrent_le_event)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ j, 0 ≤ gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih (currentTime := eventTime) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      have hbatch_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork eventTime)
            (eventTime - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates.1
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        currentTime work eventTime times hbatch_applied]
      exact hcurrent_le_event.trans htail

/-- Every literal epoch included in a chronological finite batch trace has
already been reached by the trace's final physical clock.  The result uses
the executable runner's termination proof at every intervening batch, not an
assumption that a source-labelled trace has a requested endpoint. -/
theorem finiteGPSRunBatchTrace_mem_time_le_currentTime
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ j, 0 ≤ batchWork t j)
    (eventTime : ℝ) (heventTime : eventTime ∈ times) :
    eventTime ≤
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).currentTime := by
  induction times generalizing currentTime work with
  | nil =>
      simp at heventTime
  | cons head times ih =>
      rcases hchronological with ⟨hcurrent_le_head, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork head j := by
        intro j
        exact hbatch_nonneg head (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j, 0 ≤ batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork head) (head - currentTime)
      have hgap_terminates : gap.batchApplied = true ∧ gap.remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hcurrent_le_head)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ j, 0 ≤ gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork head) (head - currentTime) hwork_nonneg hbatch_head
      have htail_start_le : head ≤
          (finiteGPSRunBatchTrace capacity weight batchWork head gap.workload times).currentTime :=
        finiteGPSRunBatchTrace_start_le_currentTime capacity weight gap.workload batchWork
          head times hcapacity hweight_pos htotal_weight_le_one hgap_nonneg
          hchronological_tail hbatch_tail
      have hbatch_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork head)
            (head - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates.1
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        currentTime work head times hbatch_applied]
      rcases List.mem_cons.mp heventTime with hhead | htail
      · subst eventTime
        exact htail_start_le
      · exact ih (currentTime := head) (work := gap.workload)
          hgap_nonneg hchronological_tail hbatch_tail htail

end

end AppliedModelingLib.Probability.Queueing
