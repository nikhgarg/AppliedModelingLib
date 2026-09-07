import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTraceProgress
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSDeadline
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTemporalSeparation
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonPrefix
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonTraceTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSLiteralHorizonCompletion
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedTargetSourceOrder
import Mathlib.Tactic

/-!
# Genuine-future-source separation for tagged GPS completions

The finite GPS source runner stops after literal source batches and then its
full-horizon wrapper appends a source-empty computational fence.  This file
records the physical fact needed to distinguish those two phases: if a
genuine source epoch is in the preterminal batch trace, then that trace has
actually reached the epoch; any completion strictly before it cannot be
emitted by the later fence.

The result is deliberately about timestamps, source membership, and the
executable FCFS fold.  It does not assume a completion belongs to the source
prefix merely because a related horizon response has a witness.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

private theorem finiteGPSFCFSSegmentStepsEndpointWorkload_eq_erasedFinalWorkload_future
    (initialWorkload : Category → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload steps =
      finiteGPSExecutionSegmentsFinalWorkload initialWorkload
        (steps.map fun step => step.segment) := by
  induction steps generalizing initialWorkload with
  | nil => rfl
  | cons step steps ih =>
      simpa [finiteGPSFCFSSegmentStepsEndpointWorkload,
        finiteGPSExecutionSegmentsFinalWorkload] using
        ih (initialWorkload := step.segment.endpointWorkload)

/-- The literal post-tag suffix of a reset-start source/fence trace has its
actual physical chain and reaches the requested horizon.  This is a finite
trace decomposition, not a source-arrival assertion about the horizon fence. -/
private theorem taggedAdmittedFiniteGPSPostAdmissionSuffix_chain_and_finalTime_future
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
        before ++ admissionStep :: after)
    (hadmission_time : finiteGPSExecutionSegmentEndTime admissionStep.segment = 0) :
    FiniteGPSExecutionSegmentsChainFrom 0
        (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
        (after.map fun step => step.segment) ∧
      finiteGPSExecutionSegmentsFinalTime 0
        (after.map fun step => step.segment) = horizon := by
  have hfull_chain := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentChain
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfull_final :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentsFinalTime_eq_horizon
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  let preSegments := before.map (fun step => step.segment) ++ [admissionStep.segment]
  let postSegments := after.map (fun step => step.segment)
  have hsegments_split :
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) = preSegments ++ postSegments := by
    dsimp [preSegments, postSegments]
    rw [hsplit]
    simp [List.append_assoc]
  have hchain_split : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0) (preSegments ++ postSegments) := by
    rw [← hsegments_split]
    exact hfull_chain
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      start (fun _ : Category => 0) preSegments postSegments).mp hchain_split with
      ⟨_hprefix_chain, hsuffix_chain⟩
  have hprefix_final_time :
      finiteGPSExecutionSegmentsFinalTime start preSegments =
        finiteGPSExecutionSegmentEndTime admissionStep.segment := by
    dsimp [preSegments]
    simp [finiteGPSExecutionSegmentsFinalTime_append,
      finiteGPSExecutionSegmentsFinalTime]
  have hprefix_final_workload :
      finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0) preSegments =
        taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep := by
    dsimp [preSegments, taggedAdmittedFiniteGPSPostAdmissionWorkload]
    rw [finiteGPSFCFSSegmentStepsEndpointWorkload_eq_erasedFinalWorkload_future]
    simp
  have hsuffix_chain_zero : FiniteGPSExecutionSegmentsChainFrom 0
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep) postSegments := by
    simpa [hprefix_final_time, hadmission_time, hprefix_final_workload] using
      hsuffix_chain
  have hfull_final_split :
      finiteGPSExecutionSegmentsFinalTime start (preSegments ++ postSegments) = horizon := by
    rw [← hsegments_split]
    exact hfull_final
  have hsuffix_final : finiteGPSExecutionSegmentsFinalTime 0 postSegments = horizon := by
    rw [finiteGPSExecutionSegmentsFinalTime_append,
      hprefix_final_time, hadmission_time] at hfull_final_split
    exact hfull_final_split
  exact ⟨hsuffix_chain_zero, hsuffix_final⟩

/-- A literal source epoch retained in a preterminal tagged batch trace is
no later than the actual clock reached by the executable finite GPS run. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_sourceArrival_le_currentTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) (n : ℤ)
    (hindex : n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k) :
    taggedAdmittedSourceArrival target z (k, n) ≤
      (taggedAdmittedFiniteGPSPreTerminalRun
        start horizon target z htarget_good capacity weight initialWork).currentTime := by
  let sourceTime := taggedAdmittedSourceArrival target z (k, n)
  have hsourceTime_batch : sourceTime ∈ taggedAdmittedBatchTimes start horizon target z := by
    apply (mem_taggedAdmittedBatchTimes_iff start horizon target z sourceTime).mpr
    exact ⟨(k, n),
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hindex, rfl⟩
  have hsourceTime_trace : sourceTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times :=
    (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hsourceTime_batch
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times, ∀ j,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime j
  change sourceTime ≤
    (finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt start horizon target z) start initialWork
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times).currentTime
  exact finiteGPSRunBatchTrace_mem_time_le_currentTime
    capacity weight initialWork (taggedAdmittedBatchAt start horizon target z)
    start (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
    hcapacity hweight_pos htotal_weight_le_one hinitial_nonneg
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
    hbatch_nonneg sourceTime hsourceTime_trace

/-- Completions emitted by the explicitly source-empty horizon-fence suffix
are no earlier than the actual preterminal source-run clock. -/
theorem taggedAdmittedFiniteGPSHorizonFenceSuffix_targetCompletions_ge_preTerminalCurrentTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∀ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category))
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)))
      target
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight),
      (taggedAdmittedFiniteGPSPreTerminalRun
        start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤
        completion.completionTime := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let preterminalSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let fenceSteps := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    start horizon target z htarget_good capacity weight
  let fenceSegments := finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon
  let initial := finiteGPSFCFSRunSegmentSteps
    (taggedAdmittedEmptyFCFSLedger (Category := Category)) preterminalSteps
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hempty_matches : ∀ i,
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).classWork i =
        (fun _ : Category => 0) i := by
    intro i
    simp [taggedAdmittedEmptyFCFSLedger, FiniteGPSFCFSJobLedger.classWork,
      finiteGPSFCFSJobWork]
  have hpre_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) preterminalSteps := by
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one
      (by intro i; norm_num) hsource_work_nonneg hempty_nonneg hempty_matches
  have hinitial_nonneg : initial.Nonnegative := by
    exact finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) preterminalSteps hempty_nonneg hpre_compatible
  have hfence_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      initial preterminal.final.workload fenceSteps := by
    exact taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_compatible
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
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
  have hfence_chain : FiniteGPSExecutionSegmentsChainFrom
      preterminal.final.currentTime preterminal.final.workload fenceSegments := by
    exact finiteGPSRunGapSegments_chainFrom
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      capacity weight preterminal.final.workload (fun _ => 0)
      preterminal.final.currentTime (horizon - preterminal.final.currentTime)
  have hfence_duration : ∀ segment ∈ fenceSegments, 0 ≤ segment.duration := by
    exact finiteGPSRunGapSegments_duration_nonneg
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
      (sub_nonneg.mpr hpre_time_le_horizon)
  have hfence_rate : ∀ segment ∈ fenceSegments,
      0 ≤ segment.classRate target := by
    exact finiteGPSRunGapSegments_classRate_nonneg
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one
  have hfence_steps_segments :
      fenceSteps.map (fun step => step.segment) = fenceSegments := by
    dsimp [fenceSteps, fenceSegments, preterminal]
    simp [taggedAdmittedFiniteGPSHorizonFenceFCFSSteps, Function.comp_def]
  have hchain_steps : FiniteGPSExecutionSegmentsChainFrom
      preterminal.final.currentTime preterminal.final.workload
      (fenceSteps.map fun step => step.segment) := by
    rw [hfence_steps_segments]
    exact hfence_chain
  have hrate_steps : ∀ step ∈ fenceSteps, 0 ≤ step.segment.classRate target := by
    intro step hstep
    apply hfence_rate step.segment
    rw [← hfence_steps_segments]
    exact List.mem_map.mpr ⟨step, hstep, rfl⟩
  have hduration_steps : ∀ step ∈ fenceSteps, 0 ≤ step.segment.duration := by
    intro step hstep
    apply hfence_duration step.segment
    rw [← hfence_steps_segments]
    exact List.mem_map.mpr ⟨step, hstep, rfl⟩
  have htemporal :=
    finiteGPSFCFSRunSegmentStepsClassCompletions_all_completionTime_ge_start_of_compatible
      initial preterminal.final.workload target fenceSteps preterminal.final.currentTime
      hinitial_nonneg hfence_compatible hchain_steps hrate_steps hduration_steps
  simpa [preterminal, preterminalSteps, fenceSteps, initial,
    taggedAdmittedFiniteGPSPreTerminalHistory] using htemporal

/-- A full source/fence completion that is strictly earlier than the actual
preterminal source-run clock was emitted in the literal preterminal source
trace.  The conclusion contains no caller-supplied preterminal-membership
assumption. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_mem_preTerminal_of_completionTime_lt_preTerminalCurrentTime
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
      start horizon target z htarget_good capacity weight)
    (hcompletion_lt : completion.completionTime <
      (taggedAdmittedFiniteGPSPreTerminalRun
        start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime) :
    completion ∈ taggedAdmittedFiniteGPSPreTerminalTargetCompletions
      start horizon target z htarget_good capacity weight := by
  change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
    (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight) at hcompletion
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hcompletion
  apply finiteGPSFCFSRunSegmentStepsClassCompletion_mem_left_of_append_of_completionTime_lt
    (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0))
    (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight)
    (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime
    completion
  · exact taggedAdmittedFiniteGPSHorizonFenceSuffix_targetCompletions_ge_preTerminalCurrentTime
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  · exact hcompletion
  · exact hcompletion_lt

/-- At any reset-start finite horizon that reaches the target comparator
deadline, the literal source/fence FCFS trace contains the selected job by
that deadline.  The horizon is only an execution endpoint: the completion
bound itself is the physical comparator deadline. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_finiteComparatorResponse_at_laterHorizon
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat) (horizon : ℝ)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z)
    (hdeadline_le_horizon :
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart ≤ horizon) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        resetTime horizon target z htarget_good G.capacity G.weight,
      witness.completion.completionTime ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart ∧
        witness.response ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by
  let deadline := stationaryAdmittedTargetPalmFiniteComparatorResponse
    target (G.capacity * G.weight target) z remoteStart
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have hpre_nonneg : 0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target (G.capacity * G.weight target) z remoteStart :=
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target (G.capacity * G.weight target) z remoteStart
  have hdeadline_pos : 0 < deadline := by
    rw [show deadline = stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart by rfl,
      stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div]
    exact div_pos (add_pos_of_nonneg_of_pos hpre_nonneg htagged_work_pos) hrate_pos
  have hhorizon_pos : 0 < horizon := hdeadline_pos.trans_le hdeadline_le_horizon
  have hstart_le_horizon : resetTime ≤ horizon :=
    hreset_zero.trans hhorizon_pos.le
  have htagged_source_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0) := by
    simpa [stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using htagged_work_pos
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_frontWork
      resetTime horizon target z htarget_good G.capacity G.weight
      hreset_zero hhorizon_pos (G.capacity_pos target) G.weight_pos
      G.total_weight_le_one hsource_work_nonneg htagged_work_pos with
      ⟨before, terminal, after, frontWork, hsplit, hterminal_singleton,
        hterminal_workload, hterminal_time, hfront, hfront_eq_endpoint,
        hfront_pos⟩
  have htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      terminal.endpointJobs.jobs target := by
    rw [hterminal_singleton]
    simp
  have hpost_nonneg :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit
  have hpost_compatible :=
    taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit
  have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal).residualJobs target :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
      before terminal target (taggedAdmittedFCFSJob target z (target, 0))
      htag_admitted
  have htag_residual_pos :
      0 < (taggedAdmittedFCFSJob target z (target, 0)).residualWork := by
    simpa [taggedAdmittedFCFSJob] using htagged_source_work_pos
  rcases taggedAdmittedFiniteGPSPostAdmissionSuffix_chain_and_finalTime_future
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit hterminal_time with
      ⟨hafter_chain, hafter_final⟩
  have hfront_le_numerator : frontWork ≤
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (G.capacity * G.weight target) z remoteStart := by
    rw [hfront_eq_endpoint, hterminal_workload]
    exact taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_le_finiteComparatorNumerator
      resetTime horizon target z htarget_good G.capacity G.weight remoteStart
      hcoverage hreset_zero hhorizon_pos (G.capacity_pos target) G.weight_pos
      G.total_weight_le_one hsource_work_nonneg
  have hresponse_eq : deadline =
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (G.capacity * G.weight target) z remoteStart /
          (G.capacity * G.weight target) := by
    exact stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div
      target (G.capacity * G.weight target) z remoteStart
  have hnumerator_eq_rate_deadline :
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        (G.capacity * G.weight target) * deadline := by
    calc
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        deadline * (G.capacity * G.weight target) :=
          (eq_div_iff (ne_of_gt hrate_pos)).mp hresponse_eq |>.symm
      _ = (G.capacity * G.weight target) * deadline := by ring
  have hfront_le_deadline_floor : frontWork ≤
      G.capacity * G.weight target * (deadline - 0) := by
    calc
      frontWork ≤ stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart := hfront_le_numerator
      _ = (G.capacity * G.weight target) * deadline :=
        hnumerator_eq_rate_deadline
      _ = G.capacity * G.weight target * (deadline - 0) := by ring
  have hdeadline_le_after_final : deadline ≤
      finiteGPSExecutionSegmentsFinalTime 0 (after.map fun step => step.segment) := by
    rw [hafter_final]
    exact hdeadline_le_horizon
  have hafter_classRate_pos_of_active : ∀ step ∈ after,
      0 < step.segment.startWorkload target → 0 < step.segment.classRate target := by
    intro step hstep hactive
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))).1 hactive
  have hafter_service_eq : ∀ step ∈ after,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration := by
    intro step hstep
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))).2
  have hafter_floor : ∀ step ∈ after,
      0 < step.segment.startWorkload target →
        G.capacity * G.weight target * step.segment.duration ≤
          step.segment.serviceIncrement target := by
    intro step hstep hactive
    exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      resetTime horizon target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep)))) hactive
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_by_deadline_of_compatible
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      (G.capacity * G.weight target)
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      target after (taggedAdmittedFCFSJob target z (target, 0)) frontWork 0 deadline
      hpost_nonneg hpost_compatible hafter_chain hdeadline_pos.le hdeadline_le_after_final
      hrate_pos hafter_classRate_pos_of_active hafter_service_eq hafter_floor
      htag_after htag_residual_pos (by simp) hfront hfront_pos
      hfront_le_deadline_floor with
      ⟨completion, hcompletion, hkey, hcompletion_time⟩
  have hidentifier : completion.identifier = (target, 0) :=
    of_decide_eq_true hkey
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      resetTime horizon target z htarget_good G.capacity G.weight =
        (before ++ [terminal]) ++ after := by
    rw [hsplit]
    simp [List.append_assoc]
  have hfull_completion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      resetTime horizon target z htarget_good G.capacity G.weight := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime horizon target z htarget_good G.capacity G.weight)
    rw [hsplit', finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    apply List.mem_append.mpr
    right
    simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using
      hcompletion
  have harrival : completion.arrivalTime = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
      resetTime horizon target z htarget_good G.capacity G.weight completion hfull_completion hidentifier
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      resetTime horizon target z htarget_good G.capacity G.weight :=
    { completion := completion
      completion_mem := hfull_completion
      identifier_eq_tag := hidentifier
      arrival_eq_zero := harrival }
  refine ⟨witness, hcompletion_time, ?_⟩
  rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    resetTime horizon target z htarget_good G.capacity G.weight witness]
  exact hcompletion_time

/-- A good target source path supplies a genuine future source epoch beyond
the finite comparator deadline.  At the resulting later source horizon, the
selected completion is already in the literal preterminal source trace, so
the finite selector has a concrete non-fallback value without a caller-made
membership or fence-crossing assumption. -/
theorem exists_taggedAdmittedFiniteGPSPreTerminalSelection_at_futureSourceHorizon
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ completionHorizon : ℝ,
      ∃ selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category),
        resetTime ≤ completionHorizon ∧
          taggedAdmittedFiniteGPSFirstTagCompletion? target
            (finiteGPSFCFSRunSegmentStepsClassCompletions
              (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
              (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
                resetTime completionHorizon target z htarget_good
                G.capacity G.weight (fun _ => 0))) = some selected := by
  let deadline := stationaryAdmittedTargetPalmFiniteComparatorResponse
    target (G.capacity * G.weight target) z remoteStart
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have hpre_nonneg : 0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target (G.capacity * G.weight target) z remoteStart :=
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target (G.capacity * G.weight target) z remoteStart
  have hdeadline_pos : 0 < deadline := by
    rw [show deadline = stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart by rfl,
      stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div]
    exact div_pos (add_pos_of_nonneg_of_pos hpre_nonneg htagged_work_pos) hrate_pos
  rcases exists_taggedAdmittedFutureTargetSourceArrival_gt
      target z htarget_good deadline with ⟨n, hdeadline_lt_future⟩
  let futureTime := taggedAdmittedSourceArrival target z
    (target, Int.ofNat (n + 1))
  let completionHorizon := futureTime + 1
  have hfuture_pos : 0 < futureTime := hdeadline_pos.trans hdeadline_lt_future
  have hfuture_lt_horizon : futureTime < completionHorizon := by
    dsimp [completionHorizon]
    linarith
  have hreset_le_future : resetTime ≤ futureTime :=
    hreset_zero.trans hfuture_pos.le
  have hreset_le_horizon : resetTime ≤ completionHorizon :=
    hreset_le_future.trans hfuture_lt_horizon.le
  have hfuture_index : Int.ofNat (n + 1) ∈
      taggedAdmittedArrivalIndicesBetween resetTime completionHorizon target z target := by
    apply (mem_taggedAdmittedSourceJobLedger_iff
      resetTime completionHorizon target z target (Int.ofNat (n + 1))).mp
    apply (mem_taggedAdmittedSourceJobLedger_interval_iff
      resetTime completionHorizon target z htarget_good
      (target, Int.ofNat (n + 1))).mpr
    simpa [futureTime] using ⟨hreset_le_future, hfuture_lt_horizon⟩
  have hdeadline_le_horizon : deadline ≤ completionHorizon := by
    exact (hdeadline_lt_future.trans hfuture_lt_horizon).le
  rcases taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_finiteComparatorResponse_at_laterHorizon
      M G target z resetTime remoteStart completionHorizon htarget_good
      hsource_work_nonneg hreset_zero hcoverage htagged_work_pos
      hdeadline_le_horizon with
      ⟨witness, hwitness_deadline, _hwitness_response⟩
  have hfuture_le_preterminal : futureTime ≤
      (taggedAdmittedFiniteGPSPreTerminalRun
        resetTime completionHorizon target z htarget_good
        G.capacity G.weight (fun _ => 0)).currentTime := by
    simpa [futureTime] using
      (taggedAdmittedFiniteGPSPreTerminalRun_sourceArrival_le_currentTime
        resetTime completionHorizon target z htarget_good G.capacity G.weight
        (fun _ => 0) (G.capacity_pos target) G.weight_pos G.total_weight_le_one
        (by intro k; norm_num) hsource_work_nonneg target (Int.ofNat (n + 1))
        hfuture_index)
  have hwitness_preterminal_time : witness.completion.completionTime <
      (taggedAdmittedFiniteGPSPreTerminalRun
        resetTime completionHorizon target z htarget_good
        G.capacity G.weight (fun _ => 0)).currentTime := by
    exact (hwitness_deadline.trans_lt hdeadline_lt_future).trans_le hfuture_le_preterminal
  have hwitness_preterminal : witness.completion ∈
      taggedAdmittedFiniteGPSPreTerminalTargetCompletions
        resetTime completionHorizon target z htarget_good G.capacity G.weight :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_mem_preTerminal_of_completionTime_lt_preTerminalCurrentTime
      resetTime completionHorizon target z htarget_good G.capacity G.weight
      hreset_le_horizon (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg witness.completion witness.completion_mem
      hwitness_preterminal_time
  rcases taggedAdmittedFiniteGPSFirstTagCompletion?_exists_of_mem
      target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime completionHorizon target z htarget_good
          G.capacity G.weight (fun _ => 0)))
      witness.completion hwitness_preterminal witness.identifier_eq_tag with
      ⟨selected, hselected⟩
  exact ⟨completionHorizon, selected, hreset_le_horizon, hselected⟩

/-- A genuine future target source epoch supplies a concrete reset-start
completion horizon whose literal source/fence response is stable along all
sufficiently remote diagonal horizons.  The selected completion is produced
internally from the executable source trace; callers receive only the scalar
stabilization needed by the remote-past construction. -/
theorem exists_eventually_taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_futureSourceHorizon
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ completionHorizon : ℝ,
      resetTime ≤ completionHorizon ∧
        ∀ᶠ N : Nat in Filter.atTop,
          taggedAdmittedGPSDiagonalStart N ≤ resetTime ∧
            taggedAdmittedFiniteGPSHorizonFenceTotalResponse
                resetTime (taggedAdmittedGPSDiagonalHorizon N)
                target z htarget_good G.capacity G.weight =
              taggedAdmittedFiniteGPSHorizonFenceTotalResponse
                resetTime completionHorizon target z htarget_good G.capacity G.weight := by
  rcases exists_taggedAdmittedFiniteGPSPreTerminalSelection_at_futureSourceHorizon
      M G target z resetTime remoteStart htarget_good hsource_work_nonneg
      hreset_zero hcoverage htagged_work_pos with
      ⟨completionHorizon, selected, hreset_completion, hselected⟩
  refine ⟨completionHorizon, hreset_completion, ?_⟩
  exact eventually_taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
    resetTime completionHorizon target z htarget_good G.capacity G.weight selected
    hreset_completion (G.capacity_pos target) G.weight_pos G.total_weight_le_one
    hsource_work_nonneg hselected

/-- On a physical global-reset path, the literal diagonal response eventually
equals one fixed reset-start finite response.  The fixed completion is chosen
from a genuine future source epoch, then carried through later literal source
prefixes before the scalar diagonal/reset bridge is applied.  No trace list,
crossing certificate, or preterminal-membership premise remains in this
source-facing conclusion. -/
theorem exists_eventually_taggedAdmittedGPSDiagonalFiniteResponse_eq_resetHorizonResponse_of_pastGlobalMax_futureSource
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (resetTime : ℝ) (remoteStart : Nat)
    (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ completionHorizon : ℝ,
      ∀ᶠ N : Nat in Filter.atTop,
        taggedAdmittedGPSDiagonalFiniteResponse
            target z htarget_good G.capacity G.weight N =
          taggedAdmittedFiniteGPSHorizonFenceTotalResponse
            resetTime completionHorizon target z htarget_good G.capacity G.weight := by
  let hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z :=
    ⟨fun n => (hsource_work_pos.1 n).le,
      fun k n => (hsource_work_pos.2 k n).le⟩
  rcases exists_taggedAdmittedFiniteGPSPreTerminalSelection_at_futureSourceHorizon
      M G target z resetTime remoteStart htarget_good hsource_work_nonneg
      hreset_zero hcoverage htagged_work_pos with
      ⟨completionHorizon, selected, hreset_completion, hselected⟩
  refine ⟨completionHorizon, ?_⟩
  filter_upwards [eventually_taggedAdmittedGPSDiagonal_contains
    resetTime completionHorizon] with N hwindow
  have hreset_preterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime (taggedAdmittedGPSDiagonalHorizon N)
          target z htarget_good G.capacity G.weight (fun _ => 0))) = some selected :=
    taggedAdmittedFiniteGPSPreTerminalSelection_persists_of_resetHorizon
      resetTime completionHorizon (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight selected hreset_completion hwindow.2
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one hsource_work_nonneg
      hselected
  have hdiagonal_reset :=
    taggedAdmittedGPSDiagonalFiniteResponse_eq_resetHorizonResponse_of_pastGlobalMax_and_preterminalSelection
      M G target z htarget_good hsource_work_pos resetTime hreset_zero hglobal N
      hwindow.1 selected hreset_preterminal_selected
  have hreset_stable :=
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
      resetTime completionHorizon (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight selected hreset_completion hwindow.2
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one hsource_work_nonneg
      hselected
  exact hdiagonal_reset.trans hreset_stable.symm

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
