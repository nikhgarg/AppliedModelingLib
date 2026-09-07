import AppliedModelingLib.Queueing.GPS.FiniteHorizon.CompletionTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSExecutionSemantics
import Mathlib.Tactic

/-!
# Completion timing for the literal tagged GPS trace

This adapter projects nonnegative executable rate and duration facts onto the
source-labelled FCFS trace.  It then bounds every emitted target completion
by its actual source/fence horizon.  No floor comparison or source-specific
completion certificate is used here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Every source-labelled source/fence step retains nonnegative stored class
rate and duration, together with its exact executable rate-times-duration
service identity. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_completionTimingSemantics
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
      0 ≤ step.segment.classRate i ∧
        0 ≤ step.segment.duration ∧
        step.segment.serviceIncrement i =
          step.segment.classRate i * step.segment.duration := by
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times,
      ∀ j, 0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime heventTime j
    exact taggedAdmittedBatchAt_nonneg
      start horizon target z hsource_work_nonneg eventTime j
  have hpre_rate := finiteGPSRunBatchTraceSegments_classRate_nonneg
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := fun _ => 0) (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start) (i := i)
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
    hcapacity hweight_pos htotal_weight_le_one
  have hpre_duration := finiteGPSRunBatchTraceSegments_duration_nonneg
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := fun _ => 0) (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start)
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
    hcapacity hweight_pos htotal_weight_le_one (by intro j; norm_num)
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
  have hfence_rate := finiteGPSRunGapSegments_classRate_nonneg
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := preterminal.final.workload) (batchWork := fun _ => 0)
    (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime) (i := i)
    hcapacity hweight_pos htotal_weight_le_one
  have hfence_duration := finiteGPSRunGapSegments_duration_nonneg
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (Class := Category) (capacity := capacity) (weight := weight)
    (work := preterminal.final.workload) (batchWork := fun _ => 0)
    (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime)
    hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
    (sub_nonneg.mpr hpre_time_le_horizon)
  intro step hstep
  have hservice := (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg i step hstep).2
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · have hstep_segment : step.segment ∈
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)).map
          (fun laterStep => laterStep.segment) :=
      List.mem_map.mpr ⟨step, hpreterminal, rfl⟩
    rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments] at hstep_segment
    exact ⟨hpre_rate step.segment hstep_segment,
      hpre_duration step.segment hstep_segment, hservice⟩
  · unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hfence
    rcases List.mem_map.mp hfence with ⟨segment, hsegment, hstep_eq⟩
    subst step
    exact ⟨hfence_rate segment hsegment, hfence_duration segment hsegment, hservice⟩

/-- Every target completion emitted by the literal source/fence trace occurs
by the finite horizon.  This covers an early actual completion independently
of any guaranteed-rate lower-bound argument. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_completionTime_le_horizon
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight) :
    completion.completionTime ≤ horizon := by
  change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
    taggedAdmittedEmptyFCFSLedger target
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight) at hcompletion
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
      completion hcompletion with
      ⟨before, step, after, hsplit, hstep_completion⟩
  have hstep_mem : step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hsem := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_completionTimingSemantics
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target
    step hstep_mem
  have htime : completion.completionTime ≤ finiteGPSExecutionSegmentEndTime step.segment :=
    finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime_of_nonneg_rate
      step.segment target
      ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)
      hsem.1 hsem.2.1 hsem.2.2 completion hstep_completion
  exact htime.trans
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endTime_le_horizon
      start horizon target z htarget_good capacity weight hstart_le_horizon step hstep_mem)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
