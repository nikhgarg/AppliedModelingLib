import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSplit
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchTrace
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Terminal external batches after a finite GPS horizon fence

For a chronological finite GPS trace, an external batch at a requested
terminal time is applied after all service through that time.  This module
identifies its exact post-batch workload with the workload obtained by first
closing the preceding trace with a zero-work horizon fence and then adding the
literal terminal batch.  The fence is computational only; the conclusion
still concerns the original external batch trace.

This is a finite deterministic identity.  It has no stochastic, Palm, or
model-specific assumptions.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/--
Whenever a finite GPS gap reaches its supplied real endpoint, its computed
segment ledger has a literal final external segment.  That segment records the
runner's exact final workload and the original endpoint batch.

The result is structural: it needs no positivity or stochastic assumptions.
The premise says only that the existing bounded runner did reach the endpoint.
-/
theorem finiteGPSRunGapSegments_exists_terminal_external_of_batchApplied
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatchApplied :
      (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).batchApplied = true) :
    ∃ preceding terminal,
      finiteGPSRunGapSegments fuel capacity weight work batchWork
          currentTime nextBatchDelay = preceding ++ [terminal] ∧
        terminal.endpointIsExternalBatch = true ∧
        terminal.endpointWorkload =
          (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload ∧
        terminal.endpointBatch = batchWork ∧
        finiteGPSExecutionSegmentEndTime terminal = currentTime + nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGap] at hbatchApplied
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let segment := finiteGPSBuildExecutionSegment capacity weight work batchWork
        currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · refine ⟨[], segment, ?_, ?_, ?_, ?_, ?_⟩
        · simp [finiteGPSRunGapSegments, duration, segment, hterminal]
        · exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work batchWork currentTime nextBatchDelay |>.mpr
              (by simpa [duration] using hterminal)
        · simp [finiteGPSRunGap, duration, segment, hterminal]
        · funext j
          exact finiteGPSBuildExecutionSegment_endpointBatch_eq_batchWork_of_external
            capacity weight work batchWork currentTime nextBatchDelay
              (finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
                capacity weight work batchWork currentTime nextBatchDelay |>.mpr
                  (by simpa [duration] using hterminal)) j
        · simp [finiteGPSExecutionSegmentEndTime, segment, duration, hterminal]
      · have htail_batchApplied :
            (finiteGPSRunGap fuel capacity weight nextWork batchWork
              (nextBatchDelay - duration)).batchApplied = true := by
            simpa [finiteGPSRunGap, duration, nextWork, hterminal] using hbatchApplied
        obtain ⟨preceding, terminal, hsegments, hterminal_external,
          hterminal_workload, hterminal_batch, hterminal_time⟩ :=
          ih (work := nextWork) (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration) htail_batchApplied
        refine ⟨segment :: preceding, terminal, ?_, hterminal_external, ?_,
          hterminal_batch, ?_⟩
        · simp [finiteGPSRunGapSegments, duration, segment, nextWork, hterminal,
            hsegments]
        · simpa [finiteGPSRunGap, duration, nextWork, hterminal] using
            hterminal_workload
        · calc
            finiteGPSExecutionSegmentEndTime terminal =
                (currentTime + duration) + (nextBatchDelay - duration) :=
              hterminal_time
            _ = currentTime + nextBatchDelay := by ring

/--
After closing any finite GPS state at `horizon` with the computational
zero-work fence, the corresponding real batch gap has a literal final
external segment.  Its endpoint workload is the closed state plus the actual
batch at `horizon`.

This is the segment-level form of service-before-terminal-batch semantics:
callers that carry a concrete source step can use the exposed terminal segment
instead of recovering its state from aggregate trace equality.
-/
theorem finiteGPSRunGapSegments_exists_terminal_external_eq_horizonFence_add
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon)
    (i : Class) :
    ∃ preceding terminal,
      finiteGPSRunGapSegments ((finiteGPSActiveClasses result.workload).card + 1)
          capacity weight result.workload (batchWork horizon)
          result.currentTime (horizon - result.currentTime) = preceding ++ [terminal] ∧
        terminal.endpointIsExternalBatch = true ∧
        terminal.endpointWorkload i =
          (finiteGPSCloseAtHorizon capacity weight result horizon).workload i +
            batchWork horizon i ∧
        terminal.endpointBatch = batchWork horizon ∧
        finiteGPSExecutionSegmentEndTime terminal = horizon := by
  let fuel := (finiteGPSActiveClasses result.workload).card + 1
  let actualGap := finiteGPSRunGap fuel capacity weight result.workload
    (batchWork horizon) (horizon - result.currentTime)
  let zeroGap := finiteGPSRunGap fuel capacity weight result.workload
    (fun _ => 0) (horizon - result.currentTime)
  have hactual_terminates : actualGap.batchApplied = true := by
    simpa [actualGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg
        (sub_nonneg.mpr hcurrentTime_le_horizon) (Nat.lt_succ_self _)).1
  have hzero_terminates : zeroGap.batchApplied = true := by
    simpa [zeroGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg
        (sub_nonneg.mpr hcurrentTime_le_horizon) (Nat.lt_succ_self _)).1
  obtain ⟨preceding, terminal, hsegments, hterminal_external,
    hterminal_workload, hterminal_batch, hterminal_time⟩ :=
    finiteGPSRunGapSegments_exists_terminal_external_of_batchApplied
      fuel capacity weight result.workload (batchWork horizon)
      result.currentTime (horizon - result.currentTime) hactual_terminates
  refine ⟨preceding, terminal, ?_, hterminal_external, ?_, hterminal_batch, ?_⟩
  · simpa [fuel] using hsegments
  · have hgap_workload : actualGap.workload i = zeroGap.workload i + batchWork horizon i := by
      simpa [actualGap, zeroGap, fuel] using
        (finiteGPSRunGap_workload_eq_zeroBatch_add_of_batchApplied fuel capacity weight
          result.workload (batchWork horizon) (horizon - result.currentTime)
          (by simpa [zeroGap, fuel] using hzero_terminates) i)
    calc
      terminal.endpointWorkload i = actualGap.workload i := congrFun hterminal_workload i
      _ = zeroGap.workload i + batchWork horizon i := hgap_workload
      _ = (finiteGPSCloseAtHorizon capacity weight result horizon).workload i +
            batchWork horizon i := by rfl
  · calc
      finiteGPSExecutionSegmentEndTime terminal =
          result.currentTime + (horizon - result.currentTime) := hterminal_time
      _ = horizon := by ring

/--
Appending one real external batch at `horizon` to a chronological finite trace
has the same endpoint workload as closing the preceding trace through that
time with the zero-work horizon fence and then adding that real batch.

In particular, service before a simultaneous terminal batch is neither lost
nor replayed: the left side is the original executable batch trace, while the
right side exposes the same pre-batch state explicitly.
-/
theorem finiteGPSRunBatchTrace_append_singleton_workload_eq_closeAtHorizon_add
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime horizon : ℝ) (prefixTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (prefixTimes ++ [horizon]))
    (hbatch_nonneg : ∀ t ∈ prefixTimes ++ [horizon], ∀ j, 0 ≤ batchWork t j)
    (i : Class) :
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
      (prefixTimes ++ [horizon])).workload i =
      (finiteGPSCloseAtHorizon capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes)
        horizon).workload i + batchWork horizon i := by
  let prefixResult :=
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes
  have hprefix_chronological : FiniteGPSChronologicalFrom currentTime prefixTimes :=
    finiteGPSChronologicalFrom_prefix_of_append_singleton currentTime horizon prefixTimes
      hchronological
  have hstart_le_horizon : currentTime ≤ horizon :=
    finiteGPSChronologicalFrom_start_le currentTime (prefixTimes ++ [horizon])
      hchronological horizon (by simp)
  have hprefix_le_horizon : ∀ t ∈ prefixTimes, t ≤ horizon :=
    finiteGPSChronologicalFrom_prefix_le_append_singleton currentTime horizon prefixTimes
      hchronological
  have hbatch_nonneg_prefix : ∀ t ∈ prefixTimes, ∀ j, 0 ≤ batchWork t j := by
    intro t ht j
    exact hbatch_nonneg t (by simp [ht]) j
  have hprefix_nonneg : ∀ j, 0 ≤ prefixResult.workload j := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_workload_nonneg capacity weight work batchWork
        currentTime prefixTimes hwork_nonneg hbatch_nonneg_prefix)
  have hprefix_time_le_horizon : prefixResult.currentTime ≤ horizon := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_currentTime_le capacity weight work batchWork
        currentTime horizon prefixTimes hprefix_chronological hstart_le_horizon
        hprefix_le_horizon)
  have happend := finiteGPSRunBatchTrace_append_eq_restart
    capacity weight work batchWork currentTime prefixTimes [horizon]
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological
    hbatch_nonneg
  let fuel := (finiteGPSActiveClasses prefixResult.workload).card + 1
  let actualGap := finiteGPSRunGap fuel capacity weight prefixResult.workload
    (batchWork horizon) (horizon - prefixResult.currentTime)
  let zeroGap := finiteGPSRunGap fuel capacity weight prefixResult.workload
    (fun _ => 0) (horizon - prefixResult.currentTime)
  have hgap_terminates : actualGap.batchApplied = true := by
    simpa [actualGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hprefix_nonneg
        (sub_nonneg.mpr hprefix_time_le_horizon) (Nat.lt_succ_self _)).1
  have hzero_terminates : zeroGap.batchApplied = true := by
    simpa [zeroGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hprefix_nonneg
        (sub_nonneg.mpr hprefix_time_le_horizon) (Nat.lt_succ_self _)).1
  have hsuffix_workload :
      (finiteGPSRunBatchTrace capacity weight batchWork
        prefixResult.currentTime prefixResult.workload [horizon]).workload i =
        actualGap.workload i := by
    rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
      prefixResult.currentTime prefixResult.workload horizon []]
    · simp [finiteGPSRunBatchTrace, actualGap, fuel]
    · simpa [actualGap, fuel] using hgap_terminates
  have hgap_workload : actualGap.workload i = zeroGap.workload i + batchWork horizon i := by
    simpa [actualGap, zeroGap, fuel] using
      (finiteGPSRunGap_workload_eq_zeroBatch_add_of_batchApplied fuel capacity weight
        prefixResult.workload (batchWork horizon)
        (horizon - prefixResult.currentTime)
        (by simpa [zeroGap, fuel] using hzero_terminates) i)
  change
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
      (prefixTimes ++ [horizon])).workload i =
      (finiteGPSCloseAtHorizon capacity weight prefixResult horizon).workload i +
        batchWork horizon i
  calc
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
      (prefixTimes ++ [horizon])).workload i =
        (finiteGPSRunBatchTrace capacity weight batchWork
          prefixResult.currentTime prefixResult.workload [horizon]).workload i := by
            rw [happend]
            rfl
    _ = actualGap.workload i := hsuffix_workload
    _ = zeroGap.workload i + batchWork horizon i := hgap_workload
    _ = (finiteGPSCloseAtHorizon capacity weight prefixResult horizon).workload i +
          batchWork horizon i := by
            rfl

end

end AppliedModelingLib.Probability.Queueing
