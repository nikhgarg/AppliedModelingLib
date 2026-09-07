import AppliedModelingLib.Queueing.GPS.FiniteHorizon.AggregateRecursion
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Composition
import Mathlib.Tactic

/-!
# Late-batch aggregate steps of a finite GPS trace

This module connects the actual finite batch-trace runner to the deterministic
service-before-arrival scalar update.  Its theorem is an append-one step: a
chronological prefix is run by the executable GPS runner, and the next
external batch is shown to make exactly one late-batch aggregate transition.
It deliberately does not construct an infinite trace or a stochastic source.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Every listed time in a chronological trace lies after its start time. -/
theorem finiteGPSChronologicalFrom_start_le
    (start : Real) (times : List Real)
    (hchronological : FiniteGPSChronologicalFrom start times) :
    ∀ t, t ∈ times -> start ≤ t := by
  induction times generalizing start with
  | nil => simp
  | cons t times ih =>
      intro u hu
      rcases hchronological with ⟨hstart, htail⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hstart
      · exact hstart.trans (ih t htail u hu)

/-- Dropping the final singleton from a chronological trace leaves a chronological prefix. -/
theorem finiteGPSChronologicalFrom_prefix_of_append_singleton
    (start nextTime : Real) (prefixTimes : List Real)
    (hchronological : FiniteGPSChronologicalFrom start (prefixTimes ++ [nextTime])) :
    FiniteGPSChronologicalFrom start prefixTimes := by
  induction prefixTimes generalizing start with
  | nil => trivial
  | cons t prefixTimes ih =>
      rcases hchronological with ⟨hstart, htail⟩
      exact ⟨hstart, ih t htail⟩

/-- Every time in a chronological prefix precedes a following terminal batch time. -/
theorem finiteGPSChronologicalFrom_prefix_le_append_singleton
    (start nextTime : Real) (prefixTimes : List Real)
    (hchronological : FiniteGPSChronologicalFrom start (prefixTimes ++ [nextTime])) :
    ∀ t, t ∈ prefixTimes -> t ≤ nextTime := by
  induction prefixTimes generalizing start with
  | nil => simp
  | cons head prefixTimes ih =>
      intro u hu
      rcases hchronological with ⟨hstart, htail⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact finiteGPSChronologicalFrom_start_le u (prefixTimes ++ [nextTime]) htail
          nextTime (by simp)
      · exact ih head htail u hu

/--
Appending one chronological external batch to an actual finite GPS prefix is
exactly one service-before-arrival aggregate update.  The prefix state and
clock are those computed by `finiteGPSRunBatchTrace`; thus the service amount
is `capacity * (nextTime - prefix.currentTime)`.  Under the chronological and
termination hypotheses, that clock is the actual time at which the prefix
ended.  No source or infinite-path interpretation is asserted.
-/
theorem finiteGPSRunBatchTrace_append_singleton_aggregate_lateBatchUpdate
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime nextTime : Real) (prefixTimes : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (prefixTimes ++ [nextTime]))
    (hbatch_nonneg : ∀ t ∈ prefixTimes ++ [nextTime], ∀ i, 0 ≤ batchWork t i) :
    finiteGPSAggregateWork
        (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
          (prefixTimes ++ [nextTime])).workload =
      lateBatchUpdate
        (finiteGPSAggregateWork
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).workload)
        (capacity * (nextTime -
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).currentTime))
        (finiteGPSAggregateWork (batchWork nextTime)) := by
  let prefixResult :=
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes
  have hprefix_chronological : FiniteGPSChronologicalFrom currentTime prefixTimes :=
    finiteGPSChronologicalFrom_prefix_of_append_singleton currentTime nextTime prefixTimes
      hchronological
  have hstart_le_next : currentTime ≤ nextTime :=
    finiteGPSChronologicalFrom_start_le currentTime (prefixTimes ++ [nextTime]) hchronological
      nextTime (by simp)
  have hprefix_le_next : ∀ t ∈ prefixTimes, t ≤ nextTime :=
    finiteGPSChronologicalFrom_prefix_le_append_singleton currentTime nextTime prefixTimes
      hchronological
  have hbatch_nonneg_prefix : ∀ t ∈ prefixTimes, ∀ i, 0 ≤ batchWork t i := by
    intro t ht i
    exact hbatch_nonneg t (by simp [ht]) i
  have hprefix_nonneg : ∀ i, 0 ≤ prefixResult.workload i := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_workload_nonneg capacity weight work batchWork currentTime
        prefixTimes hwork_nonneg hbatch_nonneg_prefix)
  have hprefix_clock_le_next : prefixResult.currentTime ≤ nextTime := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_currentTime_le capacity weight work batchWork currentTime nextTime
        prefixTimes hprefix_chronological hstart_le_next hprefix_le_next)
  have happend := finiteGPSRunBatchTrace_append_eq_restart
    capacity weight work batchWork currentTime prefixTimes [nextTime]
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg
  let gap := finiteGPSRunGap ((finiteGPSActiveClasses prefixResult.workload).card + 1)
    capacity weight prefixResult.workload (batchWork nextTime)
      (nextTime - prefixResult.currentTime)
  have hgap_terminates : gap.batchApplied = true ∧ gap.remainingDelay = 0 := by
    exact finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses prefixResult.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      (sub_nonneg.mpr hprefix_clock_le_next) (Nat.lt_succ_self _)
  have hgap_applied :
      (finiteGPSRunGap ((finiteGPSActiveClasses prefixResult.workload).card + 1)
        capacity weight prefixResult.workload (batchWork nextTime)
        (nextTime - prefixResult.currentTime)).batchApplied = true := by
    simpa [gap] using hgap_terminates.1
  have hsuffix_workload :
      (finiteGPSRunBatchTrace capacity weight batchWork prefixResult.currentTime prefixResult.workload
        [nextTime]).workload = gap.workload := by
    rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
      prefixResult.currentTime prefixResult.workload nextTime [] hgap_applied]
    simp [finiteGPSRunBatchTrace, gap]
  have hgap_update :=
    finiteGPSRunGap_aggregateWork_eq_lateBatchUpdate
      capacity (weight := weight) (work := prefixResult.workload)
      (batchWork := batchWork nextTime)
      (nextTime - prefixResult.currentTime)
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      (sub_nonneg.mpr hprefix_clock_le_next)
  change finiteGPSAggregateWork
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
        (prefixTimes ++ [nextTime])).workload =
      lateBatchUpdate (finiteGPSAggregateWork prefixResult.workload)
        (capacity * (nextTime - prefixResult.currentTime))
        (finiteGPSAggregateWork (batchWork nextTime))
  calc
    finiteGPSAggregateWork
        (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
          (prefixTimes ++ [nextTime])).workload =
        finiteGPSAggregateWork
          (finiteGPSRunBatchTrace capacity weight batchWork prefixResult.currentTime prefixResult.workload
            [nextTime]).workload := by
              rw [happend]
              rfl
    _ = finiteGPSAggregateWork gap.workload := by rw [hsuffix_workload]
    _ = lateBatchUpdate (finiteGPSAggregateWork prefixResult.workload)
          (capacity * (nextTime - prefixResult.currentTime))
          (finiteGPSAggregateWork (batchWork nextTime)) := by
            simpa [gap] using hgap_update

end

end AppliedModelingLib.Probability.Queueing
