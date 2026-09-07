import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSKeyAbsence
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonTerminalBatch
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompatibleCompletionBridge
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedClosedPreTagSourceReplay
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedResetPartition
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSResetRestart
import Mathlib.Tactic

/-!
# Literal source front work at the tagged GPS admission

This finite pathwise adapter chooses the first actual source endpoint carrying
the Palm tag.  The choice is made from literal identifiers rather than a work
value or a scheduler-specific name.  It records the resulting absence of the
tag from the concrete pre-admission FCFS ledger, which is the exact ordering
fact needed before connecting post-admission front work to the closed pre-tag
comparator.

No stationary, Palm-tail, or response-time claim is made here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- From the literal zero-time Palm convention, the chronological source
trace on `[0, horizon)` starts with the actual tagged source batch.  This is
a source-time ordering statement, not a conclusion from a positive work
mark. -/
theorem taggedAdmittedBatchTimeTrace_zero_cons
    (horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hhorizon : 0 < horizon) :
    ∃ tail,
      taggedAdmittedBatchTimeTrace 0 horizon target z = 0 :: tail := by
  classical
  let times := taggedAdmittedBatchTimes 0 horizon target z
  have hzero_mem : (0 : ℝ) ∈ times := by
    apply (mem_taggedAdmittedBatchTimes_iff 0 horizon target z 0).mpr
    refine ⟨(target, 0), ?_, ?_⟩
    · exact (mem_taggedAdmittedTargetSourceId_iff 0 horizon target z htarget_good).mpr
        ⟨le_rfl, hhorizon⟩
    · exact taggedAdmittedSourceArrival_target_zero target z
  have hzero_first : ∀ laterTime ∈ times.erase 0, (0 : ℝ) ≤ laterTime := by
    intro laterTime hlaterTime
    exact taggedAdmittedBatchTimes_suffix_ge_reset 0 horizon target z htarget_good
      laterTime (Finset.mem_of_mem_erase hlaterTime)
  refine ⟨(times.erase 0).sort (fun left right : ℝ => left ≤ right), ?_⟩
  change times.sort (fun left right : ℝ => left ≤ right) = _
  calc
    times.sort (fun left right : ℝ => left ≤ right) =
        (Finset.cons 0 (times.erase 0) (Finset.notMem_erase 0 times)).sort
          (fun left right : ℝ => left ≤ right) := by
      congr 1
      ext eventTime
      by_cases heventTime : eventTime = 0
      · subst eventTime
        simp [hzero_mem]
      · simp [heventTime]
    _ = 0 :: (times.erase 0).sort (fun left right : ℝ => left ≤ right) :=
      Finset.sort_cons (r := fun left right : ℝ => left ≤ right)
        (s := times.erase 0) (a := 0) hzero_first (Finset.notMem_erase 0 times)

/-- Appending a known final physical time preserves a chronological source
trace when every existing time is no later than that endpoint.  This local
list fact is used only to expose the actual zero-time Palm batch to the
finite GPS terminal-batch runner. -/
private theorem finiteGPSChronologicalFrom_append_singleton_of_forall_le
    (start endpoint : ℝ) (times : List ℝ)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_endpoint : start ≤ endpoint)
    (htimes_endpoint : ∀ eventTime ∈ times, eventTime ≤ endpoint) :
    FiniteGPSChronologicalFrom start (times ++ [endpoint]) := by
  induction times generalizing start with
  | nil =>
      simpa [FiniteGPSChronologicalFrom] using hstart_endpoint
  | cons eventTime times ih =>
      rcases hchronological with ⟨hstart_eventTime, htail⟩
      refine ⟨hstart_eventTime, ?_⟩
      apply ih eventTime htail
      · exact htimes_endpoint eventTime (by simp)
      · intro laterTime hlaterTime
        exact htimes_endpoint laterTime (by simp [hlaterTime])

/-- Running the literal source prefix before zero followed by its actual
Palm batch gives the computationally closed pre-tag GPS state plus the Palm
work mark.  The left side is deliberately the genuine source batch function
on the prefix-plus-zero time list, so the equality exposes service-before-
batch rather than identifying the Palm event with a synthetic fence. -/
theorem taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_eq
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z)
      resetTime (fun _ : Category => 0)
      (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target =
      (taggedAdmittedFiniteGPSRun
        resetTime 0 target z htarget_good capacity weight (fun _ => 0)
        hreset_zero).workload target +
        stationaryAdmittedTargetPalmWorkAtZero target z := by
  let prefixTimes := taggedAdmittedBatchTimeTrace resetTime 0 target z
  have hprefix_chronological : FiniteGPSChronologicalFrom resetTime prefixTimes := by
    simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using
      (taggedAdmittedExternalBatchTrace resetTime 0 target z htarget_good).chronological
  have hprefix_le_zero : ∀ eventTime ∈ prefixTimes, eventTime ≤ 0 := by
    intro eventTime heventTime
    have heventTime_lt : eventTime < 0 := by
      apply taggedAdmittedExternalBatchTrace_time_lt_horizon
        resetTime 0 target z htarget_good eventTime
      simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using heventTime
    exact heventTime_lt.le
  have hchronological : FiniteGPSChronologicalFrom resetTime (prefixTimes ++ [0]) :=
    finiteGPSChronologicalFrom_append_singleton_of_forall_le
      resetTime 0 prefixTimes hprefix_chronological hreset_zero hprefix_le_zero
  have hbatch_nonneg : ∀ eventTime ∈ prefixTimes ++ [0], ∀ k,
      0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hprefix_eq :
      finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z)
        resetTime (fun _ : Category => 0) prefixTimes =
      taggedAdmittedFiniteGPSPreTerminalRun resetTime 0 target z htarget_good
        capacity weight (fun _ => 0) := by
    simpa [prefixTimes] using
      (taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
        resetTime 0 horizon target z htarget_good capacity weight
        (fun _ => 0) (le_of_lt hhorizon))
  have hbatch_zero : taggedAdmittedBatchAt resetTime horizon target z 0 target =
      stationaryAdmittedTargetPalmWorkAtZero target z :=
    taggedAdmittedBatchAt_target_zero_eq_workAtZero
      resetTime horizon target z htarget_good hreset_zero hhorizon
  have hterminal := finiteGPSRunBatchTrace_append_singleton_workload_eq_closeAtHorizon_add
    capacity weight (fun _ : Category => 0)
    (taggedAdmittedBatchAt resetTime horizon target z)
    resetTime 0 prefixTimes
    hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
    hchronological hbatch_nonneg target
  change
    (finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z)
      resetTime (fun _ : Category => 0)
      (prefixTimes ++ [0])).workload target = _
  calc
    (finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z)
      resetTime (fun _ : Category => 0)
      (prefixTimes ++ [0])).workload target =
        (finiteGPSCloseAtHorizon capacity weight
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime horizon target z)
            resetTime (fun _ => 0) prefixTimes) 0).workload target +
          taggedAdmittedBatchAt resetTime horizon target z 0 target := hterminal
    _ = (taggedAdmittedFiniteGPSRun
          resetTime 0 target z htarget_good capacity weight (fun _ => 0)
          hreset_zero).workload target +
          stationaryAdmittedTargetPalmWorkAtZero target z := by
        rw [hprefix_eq, hbatch_zero]
        rfl

/-- The concrete finite source execution through the real zero-time Palm
batch is bounded by the finite target-comparator numerator.  This theorem
contains no completion claim: it combines only the literal terminal-batch
identity with the closed pre-tag source replay comparison. -/
theorem taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_le_finiteComparatorNumerator
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z)
      resetTime (fun _ : Category => 0)
      (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target ≤
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (capacity * weight target) z remoteStart := by
  rw [taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_eq
    resetTime horizon target z htarget_good capacity weight
    hreset_zero hhorizon hcapacity hweight_pos htotal_weight_le_one
    hsource_work_nonneg]
  unfold stationaryAdmittedTargetPalmFiniteComparatorNumerator
  exact add_le_add
    (taggedAdmittedFiniteGPSRun_target_workload_le_stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg)
    (le_refl _)

/-- Choose the first literal source endpoint in the finite tagged trace that
carries the Palm tag.  Every earlier target endpoint batch is key-free.  This
is a list-order fact over the actual executable trace, not an assumption that
the tag is unique in some unnamed scheduler state. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after job,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        job ∈ admissionStep.endpointJobs.jobs target ∧
        decide (job.identifier = (target, 0)) = true ∧
        ∀ earlierStep ∈ before, ∀ earlierJob ∈ earlierStep.endpointJobs.jobs target,
          decide (earlierJob.identifier = (target, 0)) ≠ true := by
  apply finiteGPSFCFSSegmentJobSteps_exists_first_endpoint_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
    target
  rcases taggedAdmittedTargetFCFSJob_admitted_in_horizonFenceRun
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, hsplit, htag⟩
  refine ⟨admissionStep, ?_, taggedAdmittedFCFSJob target z (target, 0), htag, ?_⟩
  · rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  · simp

/-- The actual FCFS ledger just before the first Palm-tag endpoint contains
no tagged job.  The proof is generic fold preservation applied to the literal
source split above, so it does not rely on the names of queueing functions or
on a numerical work test. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_preLedger_no_tag
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after job,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        job ∈ admissionStep.endpointJobs.jobs target ∧
        decide (job.identifier = (target, 0)) = true ∧
        (∀ earlier ∈
          (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target,
          decide (earlier.identifier = (target, 0)) ≠ true) := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, job, hsplit, hjob, hkey, hbefore⟩
  refine ⟨before, admissionStep, after, job, hsplit, hjob, hkey, ?_⟩
  apply finiteGPSFCFSRunSegmentSteps_forall_not_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    taggedAdmittedEmptyFCFSLedger before target
  · intro initialJob hinitialJob
    simp [taggedAdmittedEmptyFCFSLedger] at hinitialJob
  · exact hbefore

/-- A target endpoint carrying the Palm tag is its literal zero-time source
batch.  Its target-class FCFS list is therefore the singleton tagged job.
This is obtained from the source endpoint-batch trace, rather than from a
cardinality argument about aggregate workload. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_key_endpointJobs_target_eq_singleton
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target)
    (hkey : decide (job.identifier = (target, 0)) = true) :
    step.endpointJobs.jobs target = [taggedAdmittedFCFSJob target z (target, 0)] := by
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · have hexternal : step.segment.endpointIsExternalBatch = true :=
      taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_external
        start horizon target z htarget_good capacity weight (fun _ => 0)
        step hpreterminal job hjob
    have hendpoint_mem : step.endpointJobs ∈
        taggedAdmittedFiniteGPSExternalEndpointJobBatches
          (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
            start horizon target z htarget_good capacity weight (fun _ => 0)) := by
      unfold taggedAdmittedFiniteGPSExternalEndpointJobBatches
      apply List.mem_filterMap.mpr
      refine ⟨step, hpreterminal, ?_⟩
      simp [hexternal]
    rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hsource_work_nonneg] at hendpoint_mem
    rcases List.mem_map.mp hendpoint_mem with ⟨eventTime, _heventTime, hendpoint_eq⟩
    have hjob_at : job ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      rw [hendpoint_eq]
      exact hjob
    unfold taggedAdmittedFCFSJobsAt at hjob_at
    rcases List.mem_map.mp hjob_at with ⟨n, _hn, hsource_job_eq⟩
    have hidentifier : (target, n) = (target, 0) := by
      calc
        (target, n) = (taggedAdmittedFCFSJob target z (target, n)).identifier := rfl
        _ = job.identifier := congrArg FiniteGPSFCFSJob.identifier hsource_job_eq
        _ = (target, 0) := of_decide_eq_true hkey
    have hn_zero : n = 0 := by
      exact congrArg Prod.snd hidentifier
    have htag_at : taggedAdmittedFCFSJob target z (target, 0) ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      subst n
      exact List.mem_map.mpr ⟨0, _hn, rfl⟩
    have htag_index := (mem_taggedAdmittedFCFSJob_jobsAt_iff
      start horizon target z eventTime target 0).mp htag_at |>.1
    have htag_interval := (mem_taggedAdmittedArrivalIndicesBetween_iff
      start horizon target z htarget_good target 0).mp htag_index
    have hstart_zero : start ≤ 0 := by
      simpa [taggedAdmittedSourceArrival_target_zero] using htag_interval.1
    have hzero_lt_horizon : 0 < horizon := by
      simpa [taggedAdmittedSourceArrival_target_zero] using htag_interval.2
    have harrival := (mem_taggedAdmittedFCFSJob_jobsAt_iff
      start horizon target z eventTime target 0).mp htag_at |>.2
    rw [taggedAdmittedSourceArrival_target_zero] at harrival
    have heventTime_zero : eventTime = 0 := harrival.symm
    subst eventTime
    rw [← hendpoint_eq]
    exact taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
      start horizon target z htarget_good hstart_zero hzero_lt_horizon
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      start horizon target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- At the first literal Palm-tag endpoint, front work is exactly the
post-service residual work in the real source FCFS ledger plus the Palm job's
own source work.  Earlier key absence comes from the actual trace fold; the
endpoint singleton comes from literal zero-time source provenance. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_frontWork_eq
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        finiteGPSExecutionSegmentEndTime admissionStep.segment = 0 ∧
        finiteGPSFCFSFrontWork
          (fun identifier : TaggedAdmittedSourceJobId Category =>
            decide (identifier = (target, 0)))
          ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
          some
            (finiteGPSFCFSJobWork
              (finiteGPSFCFSConsume (admissionStep.segment.serviceIncrement target)
                ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
                  target)) +
              stationaryAdmittedTargetPalmWorkAtZero target z) := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_preLedger_no_tag
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, job, hsplit, hjob, hkey, hpre_no_tag⟩
  have hendpoint := taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_key_endpointJobs_target_eq_singleton
    start horizon target z htarget_good capacity weight
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    admissionStep
    (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp)))
    job hjob hkey
  have htag : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target := by
    rw [hendpoint]
    simp
  have hend_zero : finiteGPSExecutionSegmentEndTime admissionStep.segment = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_tag_endTime_eq_zero
      start horizon target z htarget_good capacity weight admissionStep
      (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp))) htag
  refine ⟨before, admissionStep, after, hsplit, hend_zero, ?_⟩
  have hfront := finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq_of_ledger_no_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
    admissionStep.segment admissionStep.endpointJobs target
    (taggedAdmittedFCFSJob target z (target, 0))
    hpre_no_tag hendpoint (by simp)
  simpa [taggedAdmittedFiniteGPSPostAdmissionLedger, taggedAdmittedFCFSJob,
    stationaryAdmittedTargetPalmWorkAtZero, stationaryAdmittedTargetPalmWorkPath] using hfront

/-- The concrete front work at the first literal tag endpoint is strictly
positive whenever the Palm job's source work is positive.  All pre-service
residual work is nonnegative by the compatibility certificate of the same
actual prefix; no numerical property of the source selector is used. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_frontWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ before admissionStep after frontWork,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        finiteGPSFCFSFrontWork
          (fun identifier : TaggedAdmittedSourceJobId Category =>
            decide (identifier = (target, 0)))
          ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
          some frontWork ∧
        0 < frontWork := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_frontWork_eq
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, hsplit, _hend_zero, hfront⟩
  let preServiceJobs := finiteGPSFCFSConsume (admissionStep.segment.serviceIncrement target)
    ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)
  let frontWork : ℝ := finiteGPSFCFSJobWork preServiceJobs +
    stationaryAdmittedTargetPalmWorkAtZero target z
  refine ⟨before, admissionStep, after, frontWork, hsplit, ?_, ?_⟩
  · simpa [frontWork, preServiceJobs] using hfront
  · have hpost_nonneg := taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
        start horizon target z htarget_good capacity weight
        (hstart.trans hhorizon.le) hcapacity hweight_pos htotal_weight_le_one
        hsource_work_nonneg before admissionStep after hsplit
    have hpreService_nonneg : ∀ job ∈ preServiceJobs, 0 ≤ job.residualWork := by
      intro job hjob
      exact hpost_nonneg target job (by
        change job ∈ preServiceJobs ++ admissionStep.endpointJobs.jobs target
        exact List.mem_append.mpr (Or.inl hjob))
    have hpreService_work_nonneg : 0 ≤ finiteGPSFCFSJobWork preServiceJobs := by
      unfold finiteGPSFCFSJobWork
      apply List.sum_nonneg
      intro residual hresidual
      rcases List.mem_map.mp hresidual with ⟨job, hjob, rfl⟩
      exact hpreService_nonneg job hjob
    exact add_pos_of_nonneg_of_pos hpreService_work_nonneg htagged_work_pos

/-- The literal FCFS front work through the Palm tag is exactly the target
coordinate of the same executable GPS segment immediately after the tag's
endpoint batch.  The proof uses the compatibility invariant to turn FCFS
service-before-endpoint accounting into the stored aggregate balance; it does
not substitute a target-only or stationary state for the actual GPS state. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_frontWork_eq_postAdmissionTargetWorkload
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        finiteGPSExecutionSegmentEndTime admissionStep.segment = 0 ∧
        finiteGPSFCFSFrontWork
          (fun identifier : TaggedAdmittedSourceJobId Category =>
            decide (identifier = (target, 0)))
          ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
          some (admissionStep.segment.endpointWorkload target) := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_firstLiteralPostAdmissionSplit_preLedger_no_tag
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, job, hsplit, hjob, hkey, hpre_no_tag⟩
  have hendpoint := taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_key_endpointJobs_target_eq_singleton
    start horizon target z htarget_good capacity weight
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    admissionStep
    (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp)))
    job hjob hkey
  have htag : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target := by
    rw [hendpoint]
    simp
  have hend_zero : finiteGPSExecutionSegmentEndTime admissionStep.segment = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_tag_endTime_eq_zero
      start horizon target z htarget_good capacity weight admissionStep
      (by rw [hsplit]; exact List.mem_append.mpr (Or.inr (by simp))) htag
  have hfull : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      start horizon target z htarget_good capacity weight
      (hstart.trans hhorizon.le) hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg
  have hfull_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) (before ++ admissionStep :: after) := by
    rw [← hsplit]
    exact hfull
  have hbefore_compatible := finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before (admissionStep :: after) hfull_split
  have hadmission_suffix := finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before (admissionStep :: after) hfull_split
  rcases hadmission_suffix with ⟨hledger_matches, hstart_matches, hbatch_matches,
    _hendpoint_nonneg, hservice_nonneg, hservice_le, hbalance, _htail⟩
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i queuedJob hqueuedJob
    simp [taggedAdmittedEmptyFCFSLedger] at hqueuedJob
  have hbefore_nonneg := finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before hempty_nonneg hbefore_compatible
  have hconsumed_work : finiteGPSFCFSJobWork
      (finiteGPSFCFSConsume (admissionStep.segment.serviceIncrement target)
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
          target)) =
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target -
        admissionStep.segment.serviceIncrement target := by
    exact finiteGPSFCFSConsume_jobWork_eq_sub
      (admissionStep.segment.serviceIncrement target)
      ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)
      (hservice_nonneg target)
      (fun queuedJob hqueuedJob => hbefore_nonneg target queuedJob hqueuedJob)
      (hservice_le target)
  have hpre_work_eq_start :
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target =
        admissionStep.segment.startWorkload target := by
    calc
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target =
          finiteGPSFCFSSegmentStepsEndpointWorkload (fun _ : Category => 0) before target :=
        hledger_matches target
      _ = admissionStep.segment.startWorkload target := hstart_matches target
  have htag_batch : admissionStep.segment.endpointBatch target =
      stationaryAdmittedTargetPalmWorkAtZero target z := by
    calc
      admissionStep.segment.endpointBatch target =
          admissionStep.endpointJobs.classWork target := (hbatch_matches target).symm
      _ = finiteGPSFCFSJobWork (admissionStep.endpointJobs.jobs target) := rfl
      _ = stationaryAdmittedTargetPalmWorkAtZero target z := by
        rw [hendpoint]
        simp [finiteGPSFCFSJobWork, taggedAdmittedFCFSJob,
          stationaryAdmittedTargetPalmWorkAtZero,
          stationaryAdmittedTargetPalmWorkPath]
  refine ⟨before, admissionStep, after, hsplit, hend_zero, ?_⟩
  have hfront := finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq_of_ledger_no_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
    admissionStep.segment admissionStep.endpointJobs target
    (taggedAdmittedFCFSJob target z (target, 0))
    hpre_no_tag hendpoint (by simp)
  have hfront' : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((finiteGPSFCFSApplySegment
        (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
        admissionStep.segment admissionStep.endpointJobs).residualJobs target) =
      some
        (finiteGPSFCFSJobWork
          (finiteGPSFCFSConsume (admissionStep.segment.serviceIncrement target)
            ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
              target)) +
          stationaryAdmittedTargetPalmWorkAtZero target z) := by
    simpa [taggedAdmittedFCFSJob, stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using hfront
  rw [show taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep =
      finiteGPSFCFSApplySegment
        (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
        admissionStep.segment admissionStep.endpointJobs by rfl]
  rw [hfront']
  congr 1
  calc
    finiteGPSFCFSJobWork
        (finiteGPSFCFSConsume (admissionStep.segment.serviceIncrement target)
          ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
            target)) +
        stationaryAdmittedTargetPalmWorkAtZero target z =
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target -
          admissionStep.segment.serviceIncrement target +
        admissionStep.segment.endpointBatch target := by
          rw [hconsumed_work, htag_batch]
    _ = admissionStep.segment.endpointWorkload target := by
      rw [hpre_work_eq_start]
      linarith [hbalance target]

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
