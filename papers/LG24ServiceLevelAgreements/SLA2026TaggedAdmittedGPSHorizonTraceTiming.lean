import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateComparison
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateProjection
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSHorizonResponse
import Mathlib.Tactic

/-!
# Physical timing of the literal tagged GPS horizon trace

This file identifies the finite FCFS source trace with one chronological
GPS segment chain.  It records that the explicit computational fence reaches
the requested physical horizon, while retaining the fence as a source-empty
suffix.  It contains no response-time or stochastic conclusion.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Erasing the literal source jobs from the full source/fence FCFS trace
gives an executable chronological segment chain from the empty initial
workload. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentChain
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    FiniteGPSExecutionSegmentsChainFrom start (fun _ : Category => 0)
      ((taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
        (fun step => step.segment)) := by
  let preterminalHistory := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let preterminalSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let fenceSegments := finiteGPSHorizonFenceSegments capacity weight
    preterminalHistory.final horizon
  have hpre_chronological : FiniteGPSChronologicalFrom start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times :=
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  have hpre_batch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro eventTime heventTime k
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime k
  have hpre_chain : FiniteGPSExecutionSegmentsChainFrom start (fun _ : Category => 0)
      preterminalHistory.segments := by
    change FiniteGPSExecutionSegmentsChainFrom start (fun _ : Category => 0)
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)
    exact finiteGPSRunBatchTraceSegments_chainFrom
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hpre_chronological hpre_batch_nonneg
  have hpre_final_work : finiteGPSExecutionSegmentsFinalWorkload
      (fun _ : Category => 0) preterminalHistory.segments =
      preterminalHistory.final.workload := by
    change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times).workload
    exact finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hpre_chronological hpre_batch_nonneg
  have hpre_final_time : finiteGPSExecutionSegmentsFinalTime start
      preterminalHistory.segments = preterminalHistory.final.currentTime := by
    change finiteGPSExecutionSegmentsFinalTime start
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times).currentTime
    exact finiteGPSExecutionSegmentsFinalTime_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hpre_chronological hpre_batch_nonneg
  have hpre_work_nonneg : ∀ k, 0 ≤ preterminalHistory.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminalHistory.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hfence_chain : FiniteGPSExecutionSegmentsChainFrom
      preterminalHistory.final.currentTime preterminalHistory.final.workload fenceSegments := by
    exact finiteGPSRunGapSegments_chainFrom
      ((finiteGPSActiveClasses preterminalHistory.final.workload).card + 1)
      capacity weight preterminalHistory.final.workload (fun _ => 0)
      preterminalHistory.final.currentTime
      (horizon - preterminalHistory.final.currentTime)
  have hfull_chain := finiteGPSExecutionSegmentsChainFrom_append
    start (fun _ : Category => 0) preterminalHistory.segments fenceSegments
    hpre_chain (by simpa [hpre_final_time, hpre_final_work] using hfence_chain)
  have hfence_segments :
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) = fenceSegments := by
    dsimp [fenceSegments]
    unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    induction finiteGPSHorizonFenceSegments capacity weight
        (taggedAdmittedFiniteGPSPreTerminalHistory
          start horizon target z htarget_good capacity weight (fun _ => 0)).final horizon with
    | nil => rfl
    | cons segment segments ih =>
        simp only [List.map_cons]
        rw [ih]
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  rw [List.map_append, taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments,
    hfence_segments]
  exact hfull_chain

/-- The erased full literal source/fence trace ends at the requested
computational horizon.  The final interval is a real zero-batch fence, not a
synthetic source arrival. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentsFinalTime_eq_horizon
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    finiteGPSExecutionSegmentsFinalTime start
      ((taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
        (fun step => step.segment)) = horizon := by
  let preterminalHistory := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let fenceSegments := finiteGPSHorizonFenceSegments capacity weight
    preterminalHistory.final horizon
  have hpre_chronological : FiniteGPSChronologicalFrom start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times :=
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  have hpre_batch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro eventTime heventTime k
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime k
  have hpre_final_time : finiteGPSExecutionSegmentsFinalTime start
      preterminalHistory.segments = preterminalHistory.final.currentTime := by
    change finiteGPSExecutionSegmentsFinalTime start
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times).currentTime
    exact finiteGPSExecutionSegmentsFinalTime_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hpre_chronological hpre_batch_nonneg
  have hpre_work_nonneg : ∀ k, 0 ≤ preterminalHistory.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminalHistory.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hfence_terminates := finiteGPSHorizonFence_terminates
    capacity weight preterminalHistory.final horizon hcapacity hweight_pos
    htotal_weight_le_one hpre_work_nonneg hpre_time_le_horizon
  have hfence_final_time : finiteGPSExecutionSegmentsFinalTime
      preterminalHistory.final.currentTime fenceSegments = horizon := by
    change finiteGPSExecutionSegmentsFinalTime preterminalHistory.final.currentTime
      (finiteGPSRunGapSegments
        ((finiteGPSActiveClasses preterminalHistory.final.workload).card + 1)
        capacity weight preterminalHistory.final.workload (fun _ => 0)
        preterminalHistory.final.currentTime
        (horizon - preterminalHistory.final.currentTime)) = horizon
    rw [finiteGPSExecutionSegmentsFinalTime_runGapSegments]
    change preterminalHistory.final.currentTime +
      (horizon - preterminalHistory.final.currentTime) -
        (finiteGPSHorizonFence capacity weight preterminalHistory.final horizon).remainingDelay = horizon
    rw [hfence_terminates.2]
    ring
  have hfence_segments :
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) = fenceSegments := by
    dsimp [fenceSegments]
    unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    induction finiteGPSHorizonFenceSegments capacity weight
        (taggedAdmittedFiniteGPSPreTerminalHistory
          start horizon target z htarget_good capacity weight (fun _ => 0)).final horizon with
    | nil => rfl
    | cons segment segments ih =>
        simp only [List.map_cons]
        rw [ih]
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  rw [List.map_append, taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments,
    hfence_segments, finiteGPSExecutionSegmentsFinalTime_append, hpre_final_time]
  exact hfence_final_time

private theorem finiteGPSFCFSSegmentStepsTotalDuration_eq_erasedSegmentDuration
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) :
    finiteGPSFCFSSegmentStepsTotalDuration steps =
      finiteGPSExecutionSegmentsTotalDuration
        (steps.map (fun step => step.segment)) := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
      change step.segment.duration + finiteGPSFCFSSegmentStepsTotalDuration steps =
        step.segment.duration + finiteGPSExecutionSegmentsTotalDuration
          (steps.map (fun later => later.segment))
      rw [ih]

/-- In any literal split of the complete source/fence FCFS trace, the
post-admission suffix has physical duration equal to the final horizon minus
the selected step's endpoint time. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_suffixTotalDuration_eq_horizon_sub_endpoint
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after) :
    finiteGPSFCFSSegmentStepsTotalDuration after =
      horizon - finiteGPSExecutionSegmentEndTime admissionStep.segment := by
  have hchain := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentChain
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfinal := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentsFinalTime_eq_horizon
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hsegments_split :
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) =
        before.map (fun step => step.segment) ++ admissionStep.segment ::
          after.map (fun step => step.segment) := by
    rw [hsplit]
    simp
  have hchain_split : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0)
      (before.map (fun step => step.segment) ++ admissionStep.segment ::
        after.map (fun step => step.segment)) := by
    rw [← hsegments_split]
    exact hchain
  have hchain_assoc : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0)
      ((before.map (fun step => step.segment) ++ [admissionStep.segment]) ++
        after.map (fun step => step.segment)) := by
    simpa [List.append_assoc] using hchain_split
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      start (fun _ : Category => 0)
      (before.map (fun step => step.segment) ++ [admissionStep.segment])
      (after.map (fun step => step.segment))).mp hchain_assoc with
      ⟨_hprefix, hafter_chain⟩
  have hafter_duration := finiteGPSExecutionSegmentsTotalDuration_eq_finalTime_sub_start
    (finiteGPSExecutionSegmentsFinalTime start
      (before.map (fun step => step.segment) ++ [admissionStep.segment]))
    (finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      (before.map (fun step => step.segment) ++ [admissionStep.segment]))
    (after.map (fun step => step.segment)) hafter_chain
  have hprefix_final : finiteGPSExecutionSegmentsFinalTime start
      (before.map (fun step => step.segment) ++ [admissionStep.segment]) =
      finiteGPSExecutionSegmentEndTime admissionStep.segment := by
    simp [finiteGPSExecutionSegmentsFinalTime_append,
      finiteGPSExecutionSegmentsFinalTime]
  have hfull_final : finiteGPSExecutionSegmentsFinalTime start
      (before.map (fun step => step.segment) ++ [admissionStep.segment] ++
        after.map (fun step => step.segment)) = horizon := by
    have hfull_final' := hfinal
    rw [hsegments_split] at hfull_final'
    simpa [List.append_assoc] using hfull_final'
  have hafter_final : finiteGPSExecutionSegmentsFinalTime
      (finiteGPSExecutionSegmentEndTime admissionStep.segment)
      (after.map (fun step => step.segment)) = horizon := by
    have hafter_final' : finiteGPSExecutionSegmentsFinalTime
        (finiteGPSExecutionSegmentsFinalTime start
          (before.map (fun step => step.segment) ++ [admissionStep.segment]))
        (after.map (fun step => step.segment)) = horizon := by
      simpa only [finiteGPSExecutionSegmentsFinalTime_append] using hfull_final
    simpa [hprefix_final] using hafter_final'
  have hduration_eq : finiteGPSFCFSSegmentStepsTotalDuration after =
      finiteGPSExecutionSegmentsTotalDuration
        (after.map (fun step => step.segment)) := by
    exact finiteGPSFCFSSegmentStepsTotalDuration_eq_erasedSegmentDuration after
  calc
    finiteGPSFCFSSegmentStepsTotalDuration after =
        finiteGPSExecutionSegmentsTotalDuration
          (after.map (fun step => step.segment)) := hduration_eq
    _ = finiteGPSExecutionSegmentsFinalTime
          (finiteGPSExecutionSegmentEndTime admissionStep.segment)
          (after.map (fun step => step.segment)) -
        finiteGPSExecutionSegmentEndTime admissionStep.segment := by
          rw [hafter_duration, hprefix_final]
    _ = horizon - finiteGPSExecutionSegmentEndTime admissionStep.segment := by
          rw [hafter_final]

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
