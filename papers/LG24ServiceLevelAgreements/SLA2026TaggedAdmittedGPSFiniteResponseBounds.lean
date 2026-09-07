import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSKeyAbsence
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompletionTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonTraceTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSPostTagTerminalStep
import Mathlib.Tactic

/-!
# Lower bounds for literal finite tagged GPS responses

The finite diagonal selector has a zero fallback.  On its literal completion
branch, this file proves nonnegativity from source admission order and the
executable segment chain, rather than treating response values as
automatically nonnegative.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A chronological executable segment chain whose durations are nonnegative
cannot begin any later segment before a nonnegative initial clock. -/
private theorem finiteGPSExecutionSegmentsChainFrom_startTime_nonneg
    (initialTime : ℝ) (initialWorkload : Category → ℝ)
    (segments : List (FiniteGPSExecutionSegment Category))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload segments)
    (hinitial : 0 ≤ initialTime)
    (hduration : ∀ segment ∈ segments, 0 ≤ segment.duration) :
    ∀ segment ∈ segments, 0 ≤ segment.startTime := by
  induction segments generalizing initialTime initialWorkload with
  | nil =>
      simp
  | cons head tail ih =>
      rcases hchain with ⟨hhead_time, _hhead_work, htail_chain⟩
      intro segment hsegment
      rcases List.mem_cons.mp hsegment with hhead | htail
      · subst segment
        rwa [hhead_time]
      · have hnext : 0 ≤ finiteGPSExecutionSegmentEndTime head := by
          unfold finiteGPSExecutionSegmentEndTime
          rw [hhead_time]
          exact add_nonneg hinitial (hduration head (by simp))
        exact ih (initialTime := finiteGPSExecutionSegmentEndTime head)
          (initialWorkload := head.endpointWorkload) htail_chain hnext
          (fun later hlater => hduration later (by simp [hlater])) segment htail

/-- A tagged completion emitted by a literal source/fence trace containing
the Palm epoch is timestamped no earlier than zero.  The proof locates the
completion after the actual zero-time source terminal, then applies the
generic nonnegative-rate FCFS timing bound on that post-terminal segment. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_zero : start ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    (hidentifier : completion.identifier = (target, 0)) :
    0 ≤ completion.completionTime := by
  have hstart_le_horizon : start ≤ horizon :=
    hstart_zero.trans hhorizon.le
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_no_earlier_tag
      start horizon target z htarget_good capacity weight
      hstart_zero hhorizon hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg with
      ⟨before, terminal, after, hsplit, _hterminal_external,
        _hterminal_jobs, _hterminal_tag, _hterminal_workload, hterminal_time,
        hbefore_endpoint_no_key⟩
  let key : TaggedAdmittedSourceJobId Category → Bool :=
    fun identifier => decide (identifier = (target, 0))
  have hempty_no_key : ∀ job ∈
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).residualJobs target,
      key job.identifier ≠ true := by
    intro job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hbefore_completion_no_key : ∀ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        taggedAdmittedEmptyFCFSLedger target before,
      key completion.identifier ≠ true := by
    apply finiteGPSFCFSRunSegmentStepsClassCompletions_forall_not_key
      key taggedAdmittedEmptyFCFSLedger before target hempty_no_key
    intro step hstep job hjob
    exact hbefore_endpoint_no_key step hstep job hjob
  have hbefore_ledger_no_key : ∀ job ∈
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target,
      key job.identifier ≠ true := by
    apply finiteGPSFCFSRunSegmentSteps_forall_not_key
      key taggedAdmittedEmptyFCFSLedger before target hempty_no_key
    intro step hstep job hjob
    exact hbefore_endpoint_no_key step hstep job hjob
  have hterminal_completion_no_key : ∀ completion ∈
      finiteGPSFCFSCompletedJobsInSegment terminal.segment target
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
          target),
      key completion.identifier ≠ true := by
    intro earlierCompletion hearlierCompletion
    rcases finiteGPSFCFSCompletedJobsInSegment_has_source_job
        terminal.segment target
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
          target) earlierCompletion hearlierCompletion with
        ⟨sourceJob, hsourceJob, hsource_identifier, _hsource_arrival⟩
    rw [hsource_identifier]
    exact hbefore_ledger_no_key sourceJob hsourceJob
  have hprefix_completion_no_key : ∀ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        taggedAdmittedEmptyFCFSLedger target (before ++ [terminal]),
      key completion.identifier ≠ true := by
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    intro earlierCompletion hearlierCompletion
    rcases List.mem_append.mp hearlierCompletion with hbefore | hterminal
    · exact hbefore_completion_no_key earlierCompletion hbefore
    · have hterminal' : earlierCompletion ∈
          finiteGPSFCFSCompletedJobsInSegment terminal.segment target
            ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
              target) := by
          simpa [finiteGPSFCFSRunSegmentStepsClassCompletions] using hterminal
      exact hterminal_completion_no_key earlierCompletion hterminal'
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
      (before ++ [terminal]) ++ after := by
    rw [hsplit]
    simp [List.append_assoc]
  have hcompletion_after : completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal) target after := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) at hcompletion
    rw [hsplit', finiteGPSFCFSRunSegmentStepsClassCompletions_append] at hcompletion
    rcases List.mem_append.mp hcompletion with hprefix | hafter
    · exfalso
      apply hprefix_completion_no_key completion hprefix
      simp [key, hidentifier]
    · simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using
        hafter
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      target after completion hcompletion_after with
      ⟨afterBefore, completionStep, afterRest, hafter_split,
        hstep_completion⟩
  have hcompletion_step_mem : completionStep ∈ after := by
    rw [hafter_split]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hpost_compatible :=
    taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before terminal after hsplit
  have hpost_nonnegative :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before terminal after hsplit
  have hafter_compatible_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      (afterBefore ++ completionStep :: afterRest) := by
    rw [← hafter_split]
    exact hpost_compatible
  have hbefore_completion_compatible :=
    finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      afterBefore (completionStep :: afterRest) hafter_compatible_split
  have hcompletion_ledger_nonnegative :=
    finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      afterBefore hpost_nonnegative hbefore_completion_compatible
  have hcompletion_step_mem_full : completionStep ∈
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr hcompletion_step_mem)))
  have hstep_timing :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_completionTimingSemantics
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target
      completionStep hcompletion_step_mem_full
  have hfull_chain := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentChain
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hsegments_split :
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) =
        before.map (fun step => step.segment) ++ terminal.segment ::
          after.map (fun step => step.segment) := by
    rw [hsplit]
    simp
  have hchain_split : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0)
      (before.map (fun step => step.segment) ++ terminal.segment ::
        after.map (fun step => step.segment)) := by
    rw [← hsegments_split]
    exact hfull_chain
  have hchain_assoc : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0)
      ((before.map (fun step => step.segment) ++ [terminal.segment]) ++
        after.map (fun step => step.segment)) := by
    simpa [List.append_assoc] using hchain_split
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      start (fun _ : Category => 0)
      (before.map (fun step => step.segment) ++ [terminal.segment])
      (after.map (fun step => step.segment))).mp hchain_assoc with
      ⟨_hprefix_chain, hafter_chain⟩
  have hprefix_final : finiteGPSExecutionSegmentsFinalTime start
      (before.map (fun step => step.segment) ++ [terminal.segment]) =
      finiteGPSExecutionSegmentEndTime terminal.segment := by
    simp [finiteGPSExecutionSegmentsFinalTime_append,
      finiteGPSExecutionSegmentsFinalTime]
  have hafter_chain_zero : FiniteGPSExecutionSegmentsChainFrom 0
      (finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
        (before.map (fun step => step.segment) ++ [terminal.segment]))
      (after.map (fun step => step.segment)) := by
    simpa [hprefix_final, hterminal_time] using hafter_chain
  have hafter_duration_nonneg : ∀ segment ∈ after.map (fun step => step.segment),
      0 ≤ segment.duration := by
    intro segment hsegment
    rcases List.mem_map.mp hsegment with ⟨step, hstep, rfl⟩
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_completionTimingSemantics
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target
      step (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr
          (List.mem_cons.mpr (Or.inr hstep))))).2.1
  have hcompletion_step_start_nonnegative : 0 ≤ completionStep.segment.startTime :=
    finiteGPSExecutionSegmentsChainFrom_startTime_nonneg
      0
      (finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
        (before.map (fun step => step.segment) ++ [terminal.segment]))
      (after.map (fun step => step.segment)) hafter_chain_zero (by norm_num)
      hafter_duration_nonneg completionStep.segment
      (List.mem_map.mpr ⟨completionStep, hcompletion_step_mem, rfl⟩)
  have hcompletion_ge_start :=
    finiteGPSFCFSCompletedJobsInSegment_completionTime_ge_startTime_of_nonneg_rate_and_jobs
      completionStep.segment target
      ((finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
        afterBefore).residualJobs target)
      hstep_timing.1
      (fun queuedJob hqueuedJob =>
        hcompletion_ledger_nonnegative target queuedJob hqueuedJob)
      completion hstep_completion
  exact hcompletion_step_start_nonnegative.trans hcompletion_ge_start

/-- The total literal finite response is nonnegative on the executable
source-good carrier.  The `none` branch is exactly zero; the `some` branch
uses the preceding source-order and executable-timing theorem. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_zero : start ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    0 ≤ taggedAdmittedFiniteGPSHorizonFenceTotalResponse
      start horizon target z htarget_good capacity weight := by
  unfold taggedAdmittedFiniteGPSHorizonFenceTotalResponse
  split
  · next completion hselected =>
      exact taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_nonneg
        start horizon target z htarget_good capacity weight hstart_zero hhorizon
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg completion
        (taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_source_faithful
          start horizon target z htarget_good capacity weight completion hselected).1
        (taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_source_faithful
          start horizon target z htarget_good capacity weight completion hselected).2.1
  · norm_num

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
