import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateComparison
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSFCFS
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedTargetSourceOrder
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponse
import Mathlib.Tactic

/-!
# Literal-source constant-rate comparison for the finite LG24 GPS trace

This module instantiates the generic finite-GPS segment comparison with the
actual tagged target/passive source ledger.  It starts from an explicitly zero
physical reset state and preserves the exact executable segment ledger on the
scalar side.  In particular, it does not identify that refined ledger with the
target-only comparator: internal depletion endpoints and passive source
endpoint batches remain present here until a separate compression theorem
accounts for their zero target contribution.

The result is finite and pathwise.  It does not assert stationarity, a Palm
response law, or a tail bound.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal source work of the `n`th target predecessor is exactly the
same mark used by the target-only remote-past comparator.  This is a
source-coordinate identity; it does not rely on a scheduler event name. -/
@[simp]
theorem taggedAdmittedSourceWork_target_negSucc_eq_remotePastBatch
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (n : Nat) :
    taggedAdmittedSourceWork target z (target, Int.negSucc n) =
      stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  simp [taggedAdmittedSourceWork,
    stationaryAdmittedTargetPalmRemotePastBatch,
    markedRenewalPastWork,
    stationaryAdmittedTargetPalmMarkedRenewalSample,
    twoSidedGap]

/-- At a literal target predecessor epoch, the target coordinate of the
collapsed source batch is exactly that predecessor's direct-comparator work
mark.  Simultaneous passive work is retained in other coordinates of the
same GPS batch; strict target source order rules out another target mark at
this epoch. -/
theorem taggedAdmittedBatchAt_target_predecessor_eq_remotePastBatch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (n : Nat)
    (hn : Int.negSucc n ∈
      taggedAdmittedArrivalIndicesBetween start horizon target z target) :
    taggedAdmittedBatchAt start horizon target z
        (candidatePalmArrival z.1.1 (Int.negSucc n)) target =
      stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  classical
  let hstrict := suspensionGoodGapPath_strictMono z.1.1 htarget_good.1
  unfold taggedAdmittedBatchAt
  rw [Finset.sum_eq_single (Int.negSucc n)]
  · simp only [taggedAdmittedSourceWork_target_negSucc_eq_remotePastBatch]
  · intro m hm hne
    have hm_time : candidatePalmArrival z.1.1 m =
        candidatePalmArrival z.1.1 (Int.negSucc n) :=
      by simpa [taggedAdmittedSourceArrival] using (Finset.mem_filter.mp hm).2
    exact False.elim (hne (hstrict.injective hm_time))
  · intro hnotmem
    exfalso
    exact hnotmem (Finset.mem_filter.mpr ⟨hn, by
      simp [taggedAdmittedSourceArrival]⟩)

/-- At each retained literal target predecessor epoch, the target FCFS
endpoint list has exactly that one indexed source job.  This selects a target
arrival by its source label and physical time, so it remains valid when that
job's work mark happens to be zero. -/
theorem taggedAdmittedFCFSJobsAt_target_predecessor_eq_singleton
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (n : Nat)
    (hn : Int.negSucc n ∈
      taggedAdmittedArrivalIndicesBetween start horizon target z target) :
    (taggedAdmittedFCFSJobsAt start horizon target z
      (candidatePalmArrival z.1.1 (Int.negSucc n))).jobs target =
      [taggedAdmittedFCFSJob target z (target, Int.negSucc n)] := by
  have hstrict := suspensionGoodGapPath_strictMono z.1.1 htarget_good.1
  have hindices : taggedAdmittedJobIndicesAt start horizon target z
      (candidatePalmArrival z.1.1 (Int.negSucc n)) target = {Int.negSucc n} := by
    ext m
    rw [mem_taggedAdmittedJobIndicesAt_iff]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨_hm, hm_time⟩
      apply hstrict.injective
      simpa [taggedAdmittedSourceArrival] using hm_time
    · intro hm
      subst m
      exact ⟨hn, by simp [taggedAdmittedSourceArrival]⟩
  change
    ((taggedAdmittedJobIndicesAt start horizon target z
      (candidatePalmArrival z.1.1 (Int.negSucc n)) target).sort
        (fun left right : ℤ => left ≤ right)).map
          (fun m => taggedAdmittedFCFSJob target z (target, m)) = _
  rw [hindices]
  simp

/-- An external source epoch without a target source record has zero target
batch work.  This is the source-side premise for compressing passive-source
endpoint batches; it depends on the ledger predicate, not on a scheduler
function name. -/
theorem taggedAdmittedBatchAt_target_eq_zero_of_no_target_arrival
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (hno_target_arrival : ∀ n ∈
      taggedAdmittedArrivalIndicesBetween start horizon target z target,
      candidatePalmArrival z.1.1 n ≠ eventTime) :
    taggedAdmittedBatchAt start horizon target z eventTime target = 0 := by
  classical
  unfold taggedAdmittedBatchAt
  apply Finset.sum_eq_zero
  intro n hn
  exfalso
  apply hno_target_arrival n (Finset.mem_filter.mp hn).1
  simpa [taggedAdmittedSourceArrival] using (Finset.mem_filter.mp hn).2

/-- The literal target coordinate of the actual source batch at zero is the
Palm tag's own work mark.  The identity is only about that target coordinate:
other categories may still have simultaneous source jobs in the same batch. -/
theorem taggedAdmittedBatchAt_target_zero_eq_workAtZero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    taggedAdmittedBatchAt start horizon target z 0 target =
      stationaryAdmittedTargetPalmWorkAtZero target z := by
  calc
    taggedAdmittedBatchAt start horizon target z 0 target =
        (taggedAdmittedFCFSJobsAt start horizon target z 0).classWork target :=
      (taggedAdmittedFCFSJobsAt_classWork_eq_taggedAdmittedBatchAt
        start horizon target z 0 target).symm
    _ = stationaryAdmittedTargetPalmWorkAtZero target z := by
      change finiteGPSFCFSJobWork
        ((taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target) = _
      rw [taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
        start horizon target z htarget_good hstart hhorizon]
      simp [finiteGPSFCFSJobWork,
        taggedAdmittedFCFSJob, stationaryAdmittedTargetPalmWorkAtZero,
        stationaryAdmittedTargetPalmWorkPath]

/-- Starting the genuine finite target/passive source trace at a literal
zero-work reset bounds its target workload by the scalar service-before-batch
recursion over the runner's *exact emitted segment ledger*.  Every source
batch is still applied after the preceding interval's service; an internal
GPS depletion endpoint has its actual zero endpoint batch. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_target_workload_le_constantRateSegmentComparator
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).workload target ≤
      finiteGPSConstantRateSegmentComparator (capacity * weight target) target
        (taggedAdmittedFiniteGPSPreTerminalHistory
          resetTime horizon target z htarget_good capacity weight (fun _ => 0)).segments := by
  have hcomparison :=
    finiteGPSRunBatchTrace_workload_le_constantRateSegmentComparator_of_initialZero
      (capacity := capacity) (weight := weight)
      (work := fun _ : Category => 0)
      (batchWork := taggedAdmittedBatchAt resetTime horizon target z)
      (currentTime := resetTime) (i := target)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one
      (by intro k; norm_num)
      (by norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      (by
        intro eventTime _ k
        exact taggedAdmittedBatchAt_nonneg
          resetTime horizon target z hsource_work_nonneg eventTime k)
  simpa [taggedAdmittedFiniteGPSPreTerminalRun,
    taggedAdmittedFiniteGPSPreTerminalHistory,
    finiteGPSRunExternalBatchTrace,
    finiteGPSRunExternalBatchTraceWithSegments] using hcomparison

/-- The literal-source pre-tag segment history closed by the explicit
zero-work computational fence.  The fence reaches `horizon` but is not a
source arrival and carries no source-job identity. -/
def taggedAdmittedFiniteGPSClosedPreTagHistory
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    FiniteGPSBatchSegmentHistory Category :=
  finiteGPSCloseAtHorizonWithSegments capacity weight
    (taggedAdmittedFiniteGPSPreTerminalHistory
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)) horizon

/-- Every endpoint in the terminal part of the closed pre-tag history has
zero target batch work.  These segments preserve elapsed service to the tag
time, but they cannot be mistaken for source admissions. -/
theorem taggedAdmittedFiniteGPSClosedPreTagHistory_fence_target_batch_zero
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (segment : FiniteGPSExecutionSegment Category)
    (hsegment : segment ∈ finiteGPSHorizonFenceSegments capacity weight
      (taggedAdmittedFiniteGPSPreTerminalHistory
        resetTime horizon target z htarget_good capacity weight (fun _ => 0)).final
      horizon) :
    segment.endpointBatch target = 0 := by
  exact finiteGPSHorizonFenceSegments_forall_endpointBatch_eq_zero
    capacity weight
    (taggedAdmittedFiniteGPSPreTerminalHistory
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).final
    horizon segment hsegment target

/-- The closed segment history retains exactly the ordinary source run closed
at the requested physical horizon. -/
theorem taggedAdmittedFiniteGPSClosedPreTagHistory_final
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_le_horizon : resetTime ≤ horizon) :
    (taggedAdmittedFiniteGPSClosedPreTagHistory
      resetTime horizon target z htarget_good capacity weight).final =
      taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
        capacity weight (fun _ => 0) hreset_le_horizon := by
  rfl

/-- The appended source trace and its explicit computational fence form one
chronological concrete segment chain.  The common endpoint is the actual
pre-terminal runner clock, not a fabricated source batch. -/
theorem taggedAdmittedFiniteGPSClosedPreTagHistory_segments_chainFrom
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_le_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    FiniteGPSExecutionSegmentsChainFrom resetTime (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime horizon target z htarget_good capacity weight).segments := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    resetTime horizon target z htarget_good capacity weight (fun _ => 0)
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      ∀ k, 0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hpre_chain : FiniteGPSExecutionSegmentsChainFrom resetTime
      (fun _ : Category => 0) preterminal.segments := by
    change FiniteGPSExecutionSegmentsChainFrom resetTime (fun _ : Category => 0)
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times)
    exact finiteGPSRunBatchTraceSegments_chainFrom
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      hbatch_nonneg
  have hpre_final_work : finiteGPSExecutionSegmentsFinalWorkload
      (fun _ : Category => 0) preterminal.segments = preterminal.final.workload := by
    change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times).workload
    exact finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      hbatch_nonneg
  have hpre_final_time : finiteGPSExecutionSegmentsFinalTime resetTime
      preterminal.segments = preterminal.final.currentTime := by
    change finiteGPSExecutionSegmentsFinalTime resetTime
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times).currentTime
    exact finiteGPSExecutionSegmentsFinalTime_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      hbatch_nonneg
  have hpre_nonneg : ∀ k, 0 ≤ preterminal.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      hreset_le_horizon
  have hfence_chain : FiniteGPSExecutionSegmentsChainFrom
      preterminal.final.currentTime preterminal.final.workload
      (finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) := by
    exact finiteGPSRunGapSegments_chainFrom
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      capacity weight preterminal.final.workload (fun _ => 0)
      preterminal.final.currentTime (horizon - preterminal.final.currentTime)
  change FiniteGPSExecutionSegmentsChainFrom resetTime (fun _ : Category => 0)
    (preterminal.segments ++
      finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon)
  apply finiteGPSExecutionSegmentsChainFrom_append resetTime (fun _ : Category => 0)
    preterminal.segments
    (finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon)
    hpre_chain
  simpa only [hpre_final_time, hpre_final_work] using hfence_chain

/-- The closed pre-tag source trace has the same target workload as the
source executor after the terminal computational fence, and is no larger
than the scalar comparator over that exact closed segment ledger.  This
retains the final service interval to `horizon`; it does not yet compress the
ledger to target-only arrival epochs. -/
theorem taggedAdmittedFiniteGPSRun_target_workload_le_constantRateClosedSegmentComparator
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_le_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (taggedAdmittedFiniteGPSRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      hreset_le_horizon).workload target ≤
      finiteGPSConstantRateSegmentComparator (capacity * weight target) target
        (taggedAdmittedFiniteGPSClosedPreTagHistory
          resetTime horizon target z htarget_good capacity weight).segments := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    resetTime horizon target z htarget_good capacity weight (fun _ => 0)
  let closed := taggedAdmittedFiniteGPSClosedPreTagHistory
    resetTime horizon target z htarget_good capacity weight
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      ∀ k, 0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hpre_nonneg : ∀ k, 0 ≤ preterminal.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      hreset_le_horizon
  have hpre_step : ∀ segment ∈ preterminal.segments,
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target) := by
    change ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target)
    exact finiteGPSRunBatchTraceSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      hbatch_nonneg
  have hfence_step : ∀ segment ∈
      finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon,
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target) := by
    change ∀ segment ∈ finiteGPSRunGapSegments
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      capacity weight preterminal.final.workload (fun _ => 0)
      preterminal.final.currentTime (horizon - preterminal.final.currentTime),
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target)
    exact finiteGPSRunGapSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hpre_nonneg
      (sub_nonneg.mpr hpre_time_le_horizon)
  have hstep : ∀ segment ∈ closed.segments,
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target) := by
    change ∀ segment ∈ preterminal.segments ++
      finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon,
      segment.endpointWorkload target ≤
        lateBatchUpdate (segment.startWorkload target)
          (capacity * weight target * segment.duration)
          (segment.endpointBatch target)
    intro segment hsegment
    rcases List.mem_append.mp hsegment with hpre | hfence
    · exact hpre_step segment hpre
    · exact hfence_step segment hfence
  have hcomparison := finiteGPSExecutionSegmentsFinalWorkload_le_constantRateComparator
    (fun _ : Category => 0) (capacity * weight target) target closed.segments resetTime
    (by norm_num)
    (taggedAdmittedFiniteGPSClosedPreTagHistory_segments_chainFrom
      resetTime horizon target z htarget_good capacity weight hreset_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg)
    hstep
  have hfinal : finiteGPSExecutionSegmentsFinalWorkload
      (fun _ : Category => 0) closed.segments target =
      (taggedAdmittedFiniteGPSRun
        resetTime horizon target z htarget_good capacity weight (fun _ => 0)
        hreset_le_horizon).workload target := by
    have hpre_final_work : finiteGPSExecutionSegmentsFinalWorkload
        (fun _ : Category => 0) preterminal.segments = preterminal.final.workload := by
      change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
        (finiteGPSRunBatchTraceSegments capacity weight
          (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times) =
        (finiteGPSRunBatchTrace capacity weight
          (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times).workload
      exact finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
        hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
        hbatch_nonneg
    change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      (preterminal.segments ++
        finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) target = _
    rw [finiteGPSExecutionSegmentsFinalWorkload_append, hpre_final_work]
    simpa [taggedAdmittedFiniteGPSRun, finiteGPSCloseAtHorizon,
      finiteGPSHorizonFenceSegments, finiteGPSHorizonFence] using
      congrFun
        (finiteGPSExecutionSegmentsFinalWorkload_runGapSegments
          ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
          capacity weight preterminal.final.workload (fun _ => 0)
          preterminal.final.currentTime (horizon - preterminal.final.currentTime)) target
  rw [hfinal] at hcomparison
  exact hcomparison

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
