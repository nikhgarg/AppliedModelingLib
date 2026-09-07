import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ExecutableSegmentSemantics
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSHorizonResponse
import Mathlib.Tactic

/-!
# Executable semantic facts for the tagged finite GPS trace

This module projects direct finite-runner semantics onto the source-labelled
LG24 FCFS trace.  It proves facts about stored workload, rate, duration, and
service fields after erasing only source-job annotations.  No source endpoint
is created, no segment is renamed into a special case, and no stationary or
Palm conclusion is made here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Every literal source/fence FCFS step inherits the two executable GPS
semantics needed for a physical completion timestamp: an active class has a
positive stored rate, and stored service is exactly rate times duration. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight,
      (0 < step.segment.startWorkload i → 0 < step.segment.classRate i) ∧
        step.segment.serviceIncrement i =
          step.segment.classRate i * step.segment.duration := by
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times,
      ∀ j, 0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime heventTime j
    exact taggedAdmittedBatchAt_nonneg
      start horizon target z hsource_work_nonneg eventTime j
  have hpre_rate := finiteGPSRunBatchTraceSegments_classRate_pos_of_active
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := fun _ => 0) (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start)
    (times := (taggedAdmittedExternalBatchTrace
      start horizon target z htarget_good).times)
    (i := i) hcapacity hweight_pos htotal_weight_le_one
    (by intro j; norm_num)
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
    hbatch_nonneg
  have hpre_service := finiteGPSRunBatchTraceSegments_serviceIncrement_eq_classRate_mul_duration
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := fun _ => 0) (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start)
    (times := (taggedAdmittedExternalBatchTrace
      start horizon target z htarget_good).times)
    (i := i) hcapacity hweight_pos htotal_weight_le_one
    (by intro j; norm_num)
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
    hbatch_nonneg
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hpre_work_nonneg : ∀ j, 0 ≤ preterminal.final.workload j := by
    intro j
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload j
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro k; norm_num) hsource_work_nonneg j
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hfence_rate := finiteGPSRunGapSegments_classRate_pos_of_active
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := preterminal.final.workload) (batchWork := fun _ => 0)
    (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime) (i := i)
    hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
    (sub_nonneg.mpr hpre_time_le_horizon)
  have hfence_service := finiteGPSRunGapSegments_serviceIncrement_eq_classRate_mul_duration
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := preterminal.final.workload) (batchWork := fun _ => 0)
    (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime) (i := i)
    hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
    (sub_nonneg.mpr hpre_time_le_horizon)
  intro step hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · have hstep_segment : step.segment ∈
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)).map
          (fun laterStep => laterStep.segment) :=
      List.mem_map.mpr ⟨step, hpreterminal, rfl⟩
    rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments] at hstep_segment
    constructor
    · intro hactive
      exact hpre_rate step.segment hstep_segment hactive
    · exact hpre_service step.segment hstep_segment
  · unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hfence
    rcases List.mem_map.mp hfence with ⟨segment, hsegment, hstep_eq⟩
    subst step
    constructor
    · intro hactive
      exact hfence_rate segment hsegment hactive
    · exact hfence_service segment hsegment

/-- Every source-labelled FCFS segment in the actual finite source trace and
its computational horizon fence ends no later than the requested finite
horizon.  This is a trace-clock fact, proved from literal source batch times
and the executable zero-batch fence; it is not a caller-supplied deadline
assumption. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endTime_le_horizon
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight,
      finiteGPSExecutionSegmentEndTime step.segment ≤ horizon := by
  have hpre_endTime := finiteGPSRunBatchTraceSegments_endTime_le_of_times_le
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := fun _ => 0) (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start) (horizon := horizon)
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
    (by
      intro eventTime heventTime
      exact (taggedAdmittedExternalBatchTrace_time_lt_horizon
        start horizon target z htarget_good eventTime heventTime).le)
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hfence_endTime := finiteGPSRunGapSegments_endTime_le_currentTime_add_delay
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := preterminal.final.workload) (batchWork := fun _ => 0)
    (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime)
  intro step hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · have hstep_segment : step.segment ∈
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)).map
          (fun laterStep => laterStep.segment) :=
      List.mem_map.mpr ⟨step, hpreterminal, rfl⟩
    rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments] at hstep_segment
    exact hpre_endTime step.segment hstep_segment
  · unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hfence
    rcases List.mem_map.mp hfence with ⟨segment, hsegment, hstep_eq⟩
    subst step
    have hbound := hfence_endTime segment hsegment
    linarith

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
