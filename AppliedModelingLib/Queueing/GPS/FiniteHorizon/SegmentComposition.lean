import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Composition of executable GPS segment histories

The batch runner already has a restart theorem for its final workload and
service fields.  This module proves the matching statement for the concrete
segment ledger emitted by the runner.  It is purely finite and deterministic:
the hypotheses certify chronological nonnegative batches so that every
prefix gap reaches its scheduled external endpoint.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Executing a chronological finite batch trace in two pieces emits exactly
the prefix segment ledger followed by the suffix ledger started from the
computed prefix state. -/
theorem finiteGPSRunBatchTraceSegments_append_eq_restart
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (leftTimes rightTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime (leftTimes ++ rightTimes))
    (hbatch_nonneg : ∀ t ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork t j) :
    finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
        (leftTimes ++ rightTimes) =
      finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work leftTimes ++
        finiteGPSRunBatchTraceSegments capacity weight batchWork
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work leftTimes).currentTime
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work leftTimes).workload
          rightTimes := by
  induction leftTimes generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments, finiteGPSRunBatchTrace]
  | cons t leftTimes ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork t j := by
        intro j
        exact hbatch_nonneg t (by simp) j
      have hbatch_tail : ∀ u ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork u j := by
        intro u hu j
        exact hbatch_nonneg u (by simp [hu]) j
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)
      have hgap_terminates : gap.batchApplied = true := by
        exact (finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)).1
      have hgap_nonneg : ∀ j, 0 ≤ gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork t) (t - currentTime) hwork_nonneg hbatch_head
      have htail := ih (currentTime := t) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      have hgap_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates
      change finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
          (t :: (leftTimes ++ rightTimes)) =
        finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work (t :: leftTimes) ++
          finiteGPSRunBatchTraceSegments capacity weight batchWork
            (finiteGPSRunBatchTrace capacity weight batchWork currentTime work (t :: leftTimes)).currentTime
            (finiteGPSRunBatchTrace capacity weight batchWork currentTime work (t :: leftTimes)).workload
            rightTimes
      rw [finiteGPSRunBatchTraceSegments_cons_of_batchApplied
        capacity weight batchWork currentTime work t (leftTimes ++ rightTimes) hgap_applied]
      rw [htail]
      rw [finiteGPSRunBatchTraceSegments_cons_of_batchApplied
        capacity weight batchWork currentTime work t leftTimes hgap_applied]
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied
        capacity weight batchWork currentTime work t leftTimes hgap_applied]
      simpa [gap, List.append_assoc]

/-- The corresponding segment-history wrapper has the same concrete
prefix/suffix ledger decomposition. -/
theorem finiteGPSRunBatchTraceWithSegments_append_eq_restart
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (leftTimes rightTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime (leftTimes ++ rightTimes))
    (hbatch_nonneg : ∀ t ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork t j) :
    (finiteGPSRunBatchTraceWithSegments capacity weight batchWork currentTime work
      (leftTimes ++ rightTimes)).segments =
      (finiteGPSRunBatchTraceWithSegments capacity weight batchWork currentTime work
        leftTimes).segments ++
        (finiteGPSRunBatchTraceWithSegments capacity weight batchWork
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work leftTimes).currentTime
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work leftTimes).workload
          rightTimes).segments := by
  exact finiteGPSRunBatchTraceSegments_append_eq_restart
    capacity weight work batchWork currentTime leftTimes rightTimes
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg

end

end AppliedModelingLib.Probability.Queueing
