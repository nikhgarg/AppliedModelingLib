import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSSemanticProjection
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSHorizonResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedClosedPreTagProjectionCertificate
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedTargetPredecessorSourceOrder
import Mathlib.Tactic

/-!
# Source-labelled projection of the LG24 closed pre-tag GPS trace

The finite GPS runner's raw segment ledger deliberately has no source IDs.
This adapter performs the target projection before that information is erased:
it partitions the actual FCFS-annotated segment steps by the literal target
predecessor source labels in `[resetTime, 0)`.  In particular, a predecessor
with zero work remains a selected endpoint.  The Palm tag at zero is absent
from the selected pre-tag history, and the computational fence at zero remains
in the final service-only suffix.

This file contains only finite source provenance and segment accounting.  The
stochastic reset/tail wrapper is supplied separately.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The complete source-annotated pre-tag trace: actual source batches in
`[resetTime, 0)`, followed by a computational zero-work fence to time zero.
The fence does not contain the Palm tag; the tag is appended only by the
separate response/completion argument. -/
def taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) :=
  taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
    resetTime 0 target z htarget_good capacity weight

/-- Erasing the literal source annotations from the closed pre-tag FCFS trace
recovers exactly the executable closed segment history used by the GPS scalar
comparison. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_segments_eq_closed_history
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight).map (fun step => step.segment) =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments := by
  unfold taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
  simp only [taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps, List.map_append]
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments]
  simp only [taggedAdmittedFiniteGPSHorizonFenceFCFSSteps, List.map_map]
  change (taggedAdmittedFiniteGPSPreTerminalHistory
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)).segments ++
      (finiteGPSHorizonFenceSegments capacity weight
        (taggedAdmittedFiniteGPSPreTerminalHistory
          resetTime 0 target z htarget_good capacity weight (fun _ => 0)).final 0).map
        (fun segment => segment) = _
  simp [taggedAdmittedFiniteGPSClosedPreTagHistory,
    finiteGPSCloseAtHorizonWithSegments]

/-- A semantic selector for exactly the literal target predecessor source
labels that lie in the chosen finite remote window.  This is intentionally a
source-ID membership condition, not `endpointBatch target ≠ 0`. -/
def taggedAdmittedClosedPreTagStepIsTargetPredecessor
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (step : FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) : Prop :=
  ∃ n : Nat, n < remoteStart ∧
    taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈ step.endpointJobs.jobs target

/-- Decidable list-filter form of the literal predecessor predicate.  The
proposition remains the review-facing specification; this Boolean wrapper is
only the executable list API used to retain source-labelled steps. -/
noncomputable def taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) → Bool := by
  classical
  exact fun step => decide
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step)

theorem taggedAdmittedClosedPreTagStepIsTargetPredecessorBool_eq_true_iff
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :
    taggedAdmittedClosedPreTagStepIsTargetPredecessorBool target z remoteStart step = true ↔
      taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step := by
  classical
  simp [taggedAdmittedClosedPreTagStepIsTargetPredecessorBool]

/-- Decidable source-label predicate on an already extracted endpoint batch.
It is extensionally the same literal predecessor condition as the step
predicate above, but deliberately does not consult endpoint work values. -/
noncomputable def taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category) → Bool := by
  classical
  exact fun endpointJobs => decide (∃ n : Nat, n < remoteStart ∧
    taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈ endpointJobs.jobs target)

theorem taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool_eq_true_iff
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Category
      (TaggedAdmittedSourceJobId Category)) :
    taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
      target z remoteStart endpointJobs = true ↔
      ∃ n : Nat, n < remoteStart ∧
        taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
          endpointJobs.jobs target := by
  classical
  simp [taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool]

/-- The same literal-label filter after endpoint jobs have been paired with
their physical source time.  The time is retained for the subsequent source
ordering certificate; selection itself still depends only on source IDs. -/
noncomputable def taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    TaggedAdmittedFiniteGPSTimedEndpointJobs Category → Bool :=
  fun batch => taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
    target z remoteStart batch.endpointJobs

/-- Partition the actual annotated pre-tag trace at literal target source
predecessor endpoints.  All source and internal endpoints not carrying one of
those labels remain concrete prefix/suffix steps and therefore retain their
service durations. -/
noncomputable def taggedAdmittedClosedPreTagSourceProjectionPartition
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    List (FiniteGPSFCFSSemanticProjectionBlock Category
      (TaggedAdmittedSourceJobId Category)) ×
      List (FiniteGPSFCFSSegmentJobStep Category
        (TaggedAdmittedSourceJobId Category)) := by
  classical
  exact finiteGPSFCFSSemanticProjectionPartition
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)

/-- The source-labelled semantic partition erases to exactly the original
closed executable segment ledger.  It is a rebracketing theorem, not a
source-model approximation. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_erase_eq_closed_history
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    finiteGPSConstantRateProjectionSegments
      (partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase)
      (partition.2.map fun step => step.segment) =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments := by
  classical
  unfold taggedAdmittedClosedPreTagSourceProjectionPartition
  exact (finiteGPSFCFSSemanticProjectionSegments_eq_erase
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)).trans
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_segments_eq_closed_history
      resetTime target z htarget_good capacity weight)

/-- The retained annotated endpoints of the source partition are exactly the
chronological literal-label filter of the original closed trace.  This keeps
the source selection auditable before source labels are erased. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_eq_filter_bool
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1.map
        (fun block => block.retained) =
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight).filter
        (taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
          target z remoteStart) := by
  classical
  unfold taggedAdmittedClosedPreTagSourceProjectionPartition
  simpa [taggedAdmittedClosedPreTagStepIsTargetPredecessorBool] using
    (finiteGPSFCFSSemanticProjectionPartition_retained_eq_filter
      (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight))

/-- Every retained annotated endpoint in the source partition contains a
literal selected target predecessor label, including a zero-work label. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_has_target_predecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    ∀ block ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1,
      taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart block.retained := by
  classical
  unfold taggedAdmittedClosedPreTagSourceProjectionPartition
  exact finiteGPSFCFSSemanticProjectionPartition_retained_selected
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)

/-- Every annotated step occurring in a selected block's prefix has no
literal target predecessor source label in the finite remote window. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_zeroPrefix_has_no_target_predecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    ∀ block ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1,
      ∀ step ∈ block.zeroPrefix,
        ¬ taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step := by
  classical
  unfold taggedAdmittedClosedPreTagSourceProjectionPartition
  exact finiteGPSFCFSSemanticProjectionPartition_zeroPrefix_not_selected
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)

/-- Every annotated step in the terminal source-to-tag suffix has no literal
target predecessor source label in the finite remote window.  The zero-time
computational fence is therefore kept as service-only rather than reclassified
as a source batch. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_has_no_target_predecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    ∀ step ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).2,
      ¬ taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step := by
  classical
  unfold taggedAdmittedClosedPreTagSourceProjectionPartition
  exact finiteGPSFCFSSemanticProjectionPartition_terminal_not_selected
    (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
    (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)

/-- A target-class job attached to one concrete source-labelled GPS step is
necessarily a literal target source record in the local finite ledger.  If
the step is external, its physical endpoint is exactly that record's source
epoch; an internal step has an explicitly empty endpoint-job list.  This is
the local provenance fact used below instead of inferring source arrivals
from a nonzero aggregate work mark. -/
private theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_origin
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hnextBatchDelay : nextBatchDelay = eventTime - currentTime)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).endpointJobs.jobs target) :
    ∃ n : ℤ,
      n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z target ∧
      job = taggedAdmittedFCFSJob target z (target, n) ∧
      finiteGPSExecutionSegmentEndTime
        (taggedAdmittedFiniteGPSBuildSegmentJobStep
          start horizon target z eventTime capacity weight work
          currentTime nextBatchDelay).segment =
        candidatePalmArrival z.1.1 n := by
  let segment := finiteGPSBuildExecutionSegment capacity weight work
    (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay
  by_cases hexternal : segment.endpointIsExternalBatch = true
  · have hjob' : job ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    unfold taggedAdmittedFCFSJobsAt at hjob'
    rcases List.mem_map.mp hjob' with ⟨n, hn, hjob_eq⟩
    have hn_indices : n ∈
        taggedAdmittedJobIndicesAt start horizon target z eventTime target :=
      (Finset.mem_sort (fun left right : ℤ => left ≤ right)).mp hn
    rcases (mem_taggedAdmittedJobIndicesAt_iff
      start horizon target z eventTime target n).mp hn_indices with
      ⟨hn_ledger, hn_time⟩
    refine ⟨n, hn_ledger, hjob_eq.symm, ?_⟩
    change finiteGPSExecutionSegmentEndTime segment =
      candidatePalmArrival z.1.1 n
    rw [finiteGPSBuildExecutionSegment_endTime]
    have hduration : finiteGPSNextStepDuration capacity weight work nextBatchDelay =
        nextBatchDelay :=
      (finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
        capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay).mp hexternal
    rw [hduration]
    calc
      currentTime + nextBatchDelay = eventTime := by
        rw [hnextBatchDelay]
        ring
      _ = candidatePalmArrival z.1.1 n := by
        simpa [taggedAdmittedSourceArrival] using hn_time.symm
  · have hjob_empty : job ∈
        (taggedAdmittedFCFSComputationalEndpointJobs
          (Category := Category)).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob_empty

/-- A literal source job can occur in a constructed annotated step only when
the executable segment actually reached its scheduled external endpoint.
This is deliberately about the stored endpoint tag, rather than a numerical
batch value, and is the bridge from source-labelled selection to the actual
external-endpoint trace. -/
private theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).endpointJobs.jobs target) :
    (taggedAdmittedFiniteGPSBuildSegmentJobStep
      start horizon target z eventTime capacity weight work
      currentTime nextBatchDelay).segment.endpointIsExternalBatch = true := by
  let segment := finiteGPSBuildExecutionSegment capacity weight work
    (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay
  change segment.endpointIsExternalBatch = true
  by_cases hexternal : segment.endpointIsExternalBatch = true
  · exact hexternal
  · have hjob_empty : job ∈
        (taggedAdmittedFCFSComputationalEndpointJobs
          (Category := Category)).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob_empty

/-- At a source-labelled step carrying a specified literal target
predecessor, the stored target endpoint batch is exactly that predecessor's
direct-comparator work mark.  This proves the batch identity from the source
job membership itself, so a zero mark cannot erase the predecessor. -/
private theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_target_predecessor_batch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) (n : Nat)
    (hjob : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).endpointJobs.jobs target) :
    (taggedAdmittedFiniteGPSBuildSegmentJobStep
      start horizon target z eventTime capacity weight work
      currentTime nextBatchDelay).segment.endpointBatch target =
      stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  let segment := finiteGPSBuildExecutionSegment capacity weight work
    (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay
  by_cases hexternal : segment.endpointIsExternalBatch = true
  · have hjob' : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    rcases (mem_taggedAdmittedFCFSJob_jobsAt_iff
      start horizon target z eventTime target (Int.negSucc n)).mp hjob' with
      ⟨hn_ledger, hn_time⟩
    have hn_time' : candidatePalmArrival z.1.1 (Int.negSucc n) = eventTime := by
      simpa [taggedAdmittedSourceArrival] using hn_time
    change segment.endpointBatch target =
      stationaryAdmittedTargetPalmRemotePastBatch target z n
    calc
      segment.endpointBatch target =
          taggedAdmittedBatchAt start horizon target z eventTime target := by
        simpa [segment] using
          (finiteGPSBuildExecutionSegment_endpointBatch_eq_batchWork_of_external
            capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay (by simpa [segment] using hexternal) target)
      _ = taggedAdmittedBatchAt start horizon target z
          (candidatePalmArrival z.1.1 (Int.negSucc n)) target := by
        rw [hn_time']
      _ = stationaryAdmittedTargetPalmRemotePastBatch target z n :=
        taggedAdmittedBatchAt_target_predecessor_eq_remotePastBatch
          start horizon target z htarget_good n hn_ledger
  · have hjob_empty : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        (taggedAdmittedFCFSComputationalEndpointJobs
          (Category := Category)).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob_empty

/-- The same provenance statement for every interval emitted while advancing
to one scheduled source epoch.  Internal depletion endpoints contribute no
source jobs; the one external endpoint, when reached, is tied to the
scheduled physical epoch by the runner's actual delay accounting. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_origin
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hnextBatchDelay : nextBatchDelay = eventTime - currentTime) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work
      currentTime nextBatchDelay,
      ∀ job ∈ step.endpointJobs.jobs target,
        ∃ n : ℤ,
          n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z target ∧
          job = taggedAdmittedFCFSJob target z (target, n) ∧
          finiteGPSExecutionSegmentEndTime step.segment =
            candidatePalmArrival z.1.1 n := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay = [step] := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step, hduration]
        intro laterStep hlaterStep job hjob
        have hlaterStep_eq : laterStep = step := by
          simpa [hsteps] using hlaterStep
        subst laterStep
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_origin
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
          hnextBatchDelay job hjob
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay =
          step :: taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration) := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step, hduration]
        have htail_delay : nextBatchDelay - duration =
            eventTime - (currentTime + duration) := by
          rw [hnextBatchDelay]
          ring
        intro laterStep hlaterStep job hjob
        rw [hsteps] at hlaterStep
        rcases List.mem_cons.mp hlaterStep with hhead | htail
        · subst laterStep
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_origin
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay
            hnextBatchDelay job hjob
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            htail_delay laterStep htail job hjob

/-- Internal depletion endpoints in one bounded source gap are explicitly
source-empty.  Thus any literal target job seen in that gap identifies an
actual reached external endpoint. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work
      currentTime nextBatchDelay,
      ∀ job ∈ step.endpointJobs.jobs target,
        step.segment.endpointIsExternalBatch = true := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay = [step] := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step, hduration]
        intro laterStep hlaterStep job hjob
        have hlaterStep_eq : laterStep = step := by
          simpa [hsteps] using hlaterStep
        subst laterStep
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_external
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
          job hjob
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay =
          step :: taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration) := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step, hduration]
        intro laterStep hlaterStep job hjob
        rw [hsteps] at hlaterStep
        rcases List.mem_cons.mp hlaterStep with hhead | htail
        · subst laterStep
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_job_external
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay
            job hjob
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            laterStep htail job hjob

/-- The predecessor-batch identity propagates through every internal
depletion interval of one executable source gap. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_target_predecessor_batch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) (n : Nat) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work
      currentTime nextBatchDelay,
      taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        step.endpointJobs.jobs target →
      step.segment.endpointBatch target =
        stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let head := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay = [head] := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head, hduration]
        intro step hstep hjob
        have hstep_eq : step = head := by
          simpa [hsteps] using hstep
        subst step
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_predecessor_batch
          start horizon target z htarget_good eventTime capacity weight work
          currentTime nextBatchDelay n hjob
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay =
          head :: taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration) := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head, hduration]
        intro step hstep hjob
        rw [hsteps] at hstep
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_predecessor_batch
            start horizon target z htarget_good eventTime capacity weight work
            currentTime nextBatchDelay n hjob
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            step htail hjob

/-- Every target-class source job admitted by the finite annotated batch
trace is a literal target ledger record and is attached at its own physical
epoch.  The statement follows the executable trace recursion, including the
stopped-gap branch, so it does not assume that a name such as `external`
means that an event was reached. -/
private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_job_origin
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (times : List ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      ∀ job ∈ step.endpointJobs.jobs target,
        ∃ n : ℤ,
          n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z target ∧
          job = taggedAdmittedFCFSJob target z (target, n) ∧
          finiteGPSExecutionSegmentEndTime step.segment =
            candidatePalmArrival z.1.1 n := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      by_cases hbatchApplied : gap.batchApplied = true
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight eventTime gap.workload times := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_origin
            start horizon target z eventTime gapFuel capacity weight work
            currentTime (eventTime - currentTime) rfl step hgap job hjob
        · exact ih (currentTime := eventTime) (work := gap.workload)
            step htail job hjob
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_origin
          start horizon target z eventTime gapFuel capacity weight work
          currentTime (eventTime - currentTime) rfl step hstep job hjob

/-- Literal target jobs remain attached only to actual external source
endpoints throughout the complete finite batch-trace recursion.  The stopped
gap branch is retained explicitly, so this does not assume that later source
times were reached merely because they appeared in an input list. -/
private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_job_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (times : List ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      ∀ job ∈ step.endpointJobs.jobs target,
        step.segment.endpointIsExternalBatch = true := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      by_cases hbatchApplied : gap.batchApplied = true
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight eventTime gap.workload times := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_external
            start horizon target z eventTime gapFuel capacity weight work
            currentTime (eventTime - currentTime) step hgap job hjob
        · exact ih (currentTime := eventTime) (work := gap.workload)
            step htail job hjob
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_job_external
          start horizon target z eventTime gapFuel capacity weight work
          currentTime (eventTime - currentTime) step hstep job hjob

/-- The literal predecessor-batch identity likewise propagates through the
complete finite source batch trace, including its ordinary stopped-gap
branch. -/
private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_predecessor_batch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (times : List ℝ) (n : Nat) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        step.endpointJobs.jobs target →
      step.segment.endpointBatch target =
        stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      by_cases hbatchApplied : gap.batchApplied = true
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight eventTime gap.workload times := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep hjob
        rw [hsteps] at hstep
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_predecessor_batch
            start horizon target z htarget_good eventTime gapFuel capacity weight work
            currentTime (eventTime - currentTime) n step hgap hjob
        · exact ih (currentTime := eventTime) (work := gap.workload)
            step htail hjob
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep hjob
        rw [hsteps] at hstep
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_predecessor_batch
          start horizon target z htarget_good eventTime gapFuel capacity weight work
          currentTime (eventTime - currentTime) n step hstep hjob

/-- Target jobs occurring in the source-annotated pre-terminal execution
come from the exact finite target source ledger and remain attached to their
physical source epoch. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_origin
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target) :
    ∃ n : ℤ,
      n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z target ∧
      job = taggedAdmittedFCFSJob target z (target, n) ∧
      finiteGPSExecutionSegmentEndTime step.segment =
        candidatePalmArrival z.1.1 n := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_job_origin
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      step hstep job hjob)

/-- Every literal target source job in the pre-terminal annotated execution
occurs at an actual external endpoint. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target) :
    step.segment.endpointIsExternalBatch = true := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_job_external
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      step hstep job hjob)

/-- If the actual Palm tag is present in a source-annotated finite trace,
its endpoint is its literal source epoch zero.  This applies to a positive
horizon response trace; the separate closed pre-tag trace below deliberately
does not contain this job. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_tag_endTime_eq_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
    (htag : taggedAdmittedFCFSJob target z (target, 0) ∈
      step.endpointJobs.jobs target) :
    finiteGPSExecutionSegmentEndTime step.segment = 0 := by
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · rcases taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_origin
        start horizon target z htarget_good capacity weight (fun _ => 0)
        step hpreterminal (taggedAdmittedFCFSJob target z (target, 0)) htag with
        ⟨n, _hn, htag_eq, htime⟩
    have hn_zero : n = 0 :=
      taggedAdmittedFCFSJob_injective target z target htag_eq.symm
    subst n
    simpa using htime
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      start horizon target z htarget_good capacity weight step hfence
    rw [hempty] at htag
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at htag

/-- A literal target predecessor carried by a pre-terminal source step has
exactly its direct target-comparator batch mark in the stored aggregate GPS
segment. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSStep_target_predecessor_batch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork)
    (n : Nat)
    (hjob : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
      step.endpointJobs.jobs target) :
    step.segment.endpointBatch target =
      stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_predecessor_batch
      start horizon target z htarget_good capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times n
      step hstep hjob)

/-- The closed pre-tag trace adds a source-empty computational fence only, so
the same predecessor batch identity holds for every retained literal target
endpoint in the full closed trace. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSStep_target_predecessor_batch
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (n : Nat)
    (hjob : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
      step.endpointJobs.jobs target) :
    step.segment.endpointBatch target =
      stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  unfold taggedAdmittedFiniteGPSClosedPreTagFCFSSteps at hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSStep_target_predecessor_batch
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      step hpreterminal n hjob
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      resetTime 0 target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- Every annotated source step emitted before the terminal fence has a
nonnegative actual elapsed duration under the finite GPS runner hypotheses. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_duration_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ k, 0 ≤ initialWork k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork) :
    0 ≤ step.segment.duration := by
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times,
      ∀ k, 0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro eventTime heventTime k
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg
      eventTime k
  have hsegments := finiteGPSRunBatchTraceSegments_duration_nonneg
    (times := (taggedAdmittedExternalBatchTrace
      start horizon target z htarget_good).times)
    (capacity := capacity) (weight := weight) (work := initialWork)
    (batchWork := taggedAdmittedBatchAt start horizon target z)
    (currentTime := start)
    hcapacity hweight_pos htotal_weight_le_one hinitial_nonneg
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
    hbatch_nonneg
  have hsegment : step.segment ∈
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork).map
        (fun laterStep => laterStep.segment) :=
    List.mem_map.mpr ⟨step, hstep, rfl⟩
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments] at hsegment
  change step.segment ∈ finiteGPSRunBatchTraceSegments capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times at hsegment
  exact hsegments step.segment hsegment

/-- The computational horizon-fence intervals also have nonnegative actual
duration.  The fence remains source-empty; this theorem only records the
runner's physical elapsed-service invariant. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_duration_nonneg
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight) :
    0 ≤ step.segment.duration := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hpre_work_nonneg : ∀ k, 0 ≤ preterminal.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hsegments := finiteGPSRunGapSegments_duration_nonneg
    ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
    (capacity := capacity) (weight := weight) (work := preterminal.final.workload)
    (batchWork := fun _ => 0) (currentTime := preterminal.final.currentTime)
    (nextBatchDelay := horizon - preterminal.final.currentTime)
    hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
    (sub_nonneg.mpr hpre_time_le_horizon)
  unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hstep
  rcases List.mem_map.mp hstep with ⟨segment, hsegment, hstep_eq⟩
  subst step
  exact hsegments segment (by simpa [preterminal, finiteGPSHorizonFenceSegments] using hsegment)

/-- Every concrete annotated interval in the entire closed pre-tag source
trace has nonnegative elapsed duration.  This joins the literal source trace
to the computational fence without treating either endpoint as a synthetic
arrival. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_duration_nonneg
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight) :
    0 ≤ step.segment.duration := by
  unfold taggedAdmittedFiniteGPSClosedPreTagFCFSSteps at hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_duration_nonneg
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hsource_work_nonneg step hpreterminal
  · exact taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_duration_nonneg
      resetTime 0 target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg step hfence

/-- The closed pre-tag trace adds only the explicitly source-empty
computational fence.  Hence every target job found anywhere in that closed
trace still has a literal target ledger label and its true source epoch. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_origin
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target) :
    ∃ n : ℤ,
      n ∈ taggedAdmittedArrivalIndicesBetween resetTime 0 target z target ∧
      job = taggedAdmittedFCFSJob target z (target, n) ∧
      finiteGPSExecutionSegmentEndTime step.segment =
        candidatePalmArrival z.1.1 n := by
  unfold taggedAdmittedFiniteGPSClosedPreTagFCFSSteps at hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_origin
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      step hpreterminal job hjob
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      resetTime 0 target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- The closed pre-tag trace adds only source-empty fence steps, so a literal
target source job anywhere in it is still attached to an actual external
source endpoint. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_external
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target) :
    step.segment.endpointIsExternalBatch = true := by
  unfold taggedAdmittedFiniteGPSClosedPreTagFCFSSteps at hstep
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_job_external
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      step hpreterminal job hjob
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      resetTime 0 target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- Source-labelled finite-window selection can retain only actual external
endpoints.  This is the key semantic fact allowing the selected FCFS trace to
be compared with the chronological source-endpoint trace; no endpoint work
test is used. -/
theorem taggedAdmittedClosedPreTagStepIsTargetPredecessor_external
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (hselected : taggedAdmittedClosedPreTagStepIsTargetPredecessor
      target z remoteStart step) :
    step.segment.endpointIsExternalBatch = true := by
  rcases hselected with ⟨n, _hn, hjob⟩
  exact taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_external
    resetTime target z htarget_good capacity weight step hstep
    (taggedAdmittedFCFSJob target z (target, Int.negSucc n)) hjob

/-- Filtering annotated steps by literal target predecessors and then
erasing only their endpoint-job annotations agrees with first extracting the
actual external endpoint trace and filtering its endpoint batches by the same
literal labels.  The sole non-list premise rules out a source-labelled job at
an internal endpoint; no work value is inspected. -/
private theorem taggedAdmittedFiniteGPSSelectedEndpointJobs_eq_externalEndpointJobs_filter
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hselected_external : ∀ step ∈ steps,
      taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step →
        step.segment.endpointIsExternalBatch = true) :
    (steps.filter (taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
      target z remoteStart)).map (fun step => step.endpointJobs) =
      (taggedAdmittedFiniteGPSExternalEndpointJobBatches steps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) := by
  classical
  induction steps with
  | nil =>
      simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches]
  | cons step steps ih =>
      have htail_external : ∀ later ∈ steps,
          taggedAdmittedClosedPreTagStepIsTargetPredecessor
            target z remoteStart later →
            later.segment.endpointIsExternalBatch = true := by
        intro later hlater hselected
        exact hselected_external later (by simp [hlater]) hselected
      have htail := ih htail_external
      by_cases hselected : taggedAdmittedClosedPreTagStepIsTargetPredecessor
          target z remoteStart step
      · have hexternal : step.segment.endpointIsExternalBatch = true :=
          hselected_external step (by simp) hselected
        have hselected_bool :
            taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
              target z remoteStart step = true :=
          taggedAdmittedClosedPreTagStepIsTargetPredecessorBool_eq_true_iff
            target z remoteStart step |>.mpr hselected
        have hendpoint_selected : ∃ n : Nat, n < remoteStart ∧
            taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
              step.endpointJobs.jobs target := by
          exact hselected
        have hendpoint_selected_bool :
            taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
              target z remoteStart step.endpointJobs = true :=
          taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool_eq_true_iff
            target z remoteStart step.endpointJobs |>.mpr hendpoint_selected
        simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
          hselected_bool, hexternal, hendpoint_selected_bool] using
          congrArg (List.cons step.endpointJobs) htail
      · have hendpoint_not_selected : ¬ (∃ n : Nat, n < remoteStart ∧
            taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
              step.endpointJobs.jobs target) := by
          intro hendpoint_selected
          exact hselected hendpoint_selected
        have hselected_bool :
            taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
              target z remoteStart step = false := by
          simp [taggedAdmittedClosedPreTagStepIsTargetPredecessorBool, hselected]
        have hendpoint_not_selected_bool :
            taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
              target z remoteStart step.endpointJobs = false := by
          simp [taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool,
            hendpoint_not_selected]
        by_cases hexternal : step.segment.endpointIsExternalBatch = true
        · simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
            hselected_bool, hendpoint_not_selected_bool, hexternal] using htail
        · simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
            hselected_bool, hendpoint_not_selected_bool, hexternal] using htail

/-- Source-empty annotated steps cannot survive the literal predecessor
filter even if their concrete segment happens to be tagged as an external
computational endpoint. -/
private theorem taggedAdmittedFiniteGPSExternalEndpointJobBatches_filter_eq_nil_of_target_jobs_empty
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hjobs_empty : ∀ step ∈ steps, step.endpointJobs.jobs target = []) :
    (taggedAdmittedFiniteGPSExternalEndpointJobBatches steps).filter
      (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
        target z remoteStart) = [] := by
  classical
  induction steps with
  | nil =>
      simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches]
  | cons step steps ih =>
      have hhead_empty : step.endpointJobs.jobs target = [] :=
        hjobs_empty step (by simp)
      have htail_empty : ∀ later ∈ steps, later.endpointJobs.jobs target = [] := by
        intro later hlater
        exact hjobs_empty later (by simp [hlater])
      have htail := ih htail_empty
      have hhead_not_selected :
          taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
            target z remoteStart step.endpointJobs = false := by
        simp [taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool,
          hhead_empty]
      by_cases hexternal : step.segment.endpointIsExternalBatch = true
      · simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
          hexternal, hhead_not_selected] using htail
      · simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
          hexternal] using htail

/-- Erasing the physical-time wrapper after filtering the literal source
endpoint trace is exactly the corresponding filter of endpoint-job batches.
The wrapper is retained elsewhere to certify chronological source times. -/
private theorem taggedAdmittedFCFSSourceEndpointBatchTrace_filter_map_endpointJobs
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    ((taggedAdmittedFCFSSourceEndpointBatchTrace start horizon target z).filter
      (taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
        target z remoteStart)).map (fun batch => batch.endpointJobs) =
      ((taggedAdmittedBatchTimeTrace start horizon target z).map
        (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime)).filter
          (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
            target z remoteStart) := by
  unfold taggedAdmittedFCFSSourceEndpointBatchTrace
  rw [List.filter_map, List.filter_map]
  simp [Function.comp_def,
    taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool]

/-- The retained endpoints of the semantic closed-trace partition, with
their source annotations still present, are exactly the literal target-label
filter of the chronological timed source endpoint trace.  This eliminates
all GPS scheduling implementation details before the remaining finite source
ordering proof: selected zero-work arrivals survive because membership is by
source identifier, not batch magnitude. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_endpointJobs_eq_sourceEndpointFilter
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    (partition.1.map fun block => block.retained.endpointJobs) =
      ((taggedAdmittedFCFSSourceEndpointBatchTrace resetTime 0 target z).filter
        (taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
          target z remoteStart)).map (fun batch => batch.endpointJobs) := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  let closedSteps := taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
    resetTime target z htarget_good capacity weight
  let preterminalSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    resetTime 0 target z htarget_good capacity weight (fun _ => 0)
  let fenceSteps := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    resetTime 0 target z htarget_good capacity weight
  have hretained_steps : partition.1.map (fun block => block.retained) =
      closedSteps.filter (taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
        target z remoteStart) := by
    simpa [partition, closedSteps] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_retained_eq_filter_bool
        resetTime target z htarget_good capacity weight remoteStart)
  have hretained_endpointJobs : partition.1.map (fun block => block.retained.endpointJobs) =
      (closedSteps.filter (taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
        target z remoteStart)).map (fun step => step.endpointJobs) := by
    simpa [List.map_map] using congrArg (List.map fun step => step.endpointJobs)
      hretained_steps
  have hselected_external : ∀ step ∈ closedSteps,
      taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart step →
        step.segment.endpointIsExternalBatch = true := by
    intro step hstep hselected
    exact taggedAdmittedClosedPreTagStepIsTargetPredecessor_external
      resetTime target z htarget_good capacity weight remoteStart step
      (by simpa [closedSteps] using hstep) hselected
  have hselected_endpointJobs :=
    taggedAdmittedFiniteGPSSelectedEndpointJobs_eq_externalEndpointJobs_filter
      target z remoteStart closedSteps hselected_external
  have hfence_jobs_empty : ∀ step ∈ fenceSteps, step.endpointJobs.jobs target = [] := by
    intro step hstep
    have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      resetTime 0 target z htarget_good capacity weight step
      (by simpa [fenceSteps] using hstep)
    rw [hempty]
    rfl
  have hfence_filtered :=
    taggedAdmittedFiniteGPSExternalEndpointJobBatches_filter_eq_nil_of_target_jobs_empty
      target z remoteStart fenceSteps hfence_jobs_empty
  have hclosed_steps : closedSteps = preterminalSteps ++ fenceSteps := by
    simp [closedSteps, preterminalSteps, fenceSteps,
      taggedAdmittedFiniteGPSClosedPreTagFCFSSteps,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps]
  have hclosed_external_filter :
      (taggedAdmittedFiniteGPSExternalEndpointJobBatches closedSteps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) =
      (taggedAdmittedFiniteGPSExternalEndpointJobBatches preterminalSteps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) := by
    rw [hclosed_steps]
    have hexternal_append :
        taggedAdmittedFiniteGPSExternalEndpointJobBatches
          (preterminalSteps ++ fenceSteps) =
        taggedAdmittedFiniteGPSExternalEndpointJobBatches preterminalSteps ++
          taggedAdmittedFiniteGPSExternalEndpointJobBatches fenceSteps := by
      simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
        List.filterMap_append]
    rw [hexternal_append]
    rw [List.filter_append]
    rw [hfence_filtered]
    simp
  have hpreterminal_external :=
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hsource_work_nonneg
  have hpreterminal_external_filter :
      (taggedAdmittedFiniteGPSExternalEndpointJobBatches preterminalSteps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) =
      ((taggedAdmittedBatchTimeTrace resetTime 0 target z).map
        (fun eventTime => taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime)).filter
          (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
            target z remoteStart) := by
    simpa [preterminalSteps, taggedAdmittedExternalBatchTrace] using
      congrArg (List.filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart)) hpreterminal_external
  calc
    partition.1.map (fun block => block.retained.endpointJobs) =
        (closedSteps.filter (taggedAdmittedClosedPreTagStepIsTargetPredecessorBool
          target z remoteStart)).map (fun step => step.endpointJobs) :=
      hretained_endpointJobs
    _ = (taggedAdmittedFiniteGPSExternalEndpointJobBatches closedSteps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) := hselected_endpointJobs
    _ = (taggedAdmittedFiniteGPSExternalEndpointJobBatches preterminalSteps).filter
        (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
          target z remoteStart) := hclosed_external_filter
    _ = ((taggedAdmittedBatchTimeTrace resetTime 0 target z).map
        (fun eventTime => taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime)).filter
          (taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool
            target z remoteStart) := hpreterminal_external_filter
    _ = ((taggedAdmittedFCFSSourceEndpointBatchTrace resetTime 0 target z).filter
        (taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
          target z remoteStart)).map (fun batch => batch.endpointJobs) :=
      (taggedAdmittedFCFSSourceEndpointBatchTrace_filter_map_endpointJobs
        resetTime 0 target z remoteStart).symm

/-- The local endpoint wrapper and the source-order module use extensionally
the same literal predecessor predicate.  This short bridge keeps the source
ordering proof independent of the scheduler trace while retaining the
review-facing existential source-ID specification. -/
theorem taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool_eq_sourceOrderPredicate
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool target z remoteStart =
      taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart := by
  classical
  funext batch
  by_cases hselected : ∃ n : Nat, n < remoteStart ∧
      taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        batch.endpointJobs.jobs target
  · have hlocal : taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
        target z remoteStart batch = true := by
      exact taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool_eq_true_iff
        target z remoteStart batch.endpointJobs |>.mpr hselected
    have hsource : taggedAdmittedIsRemotePredecessorEndpointBatch
        target z remoteStart batch = true := by
      exact taggedAdmittedIsRemotePredecessorEndpointBatch_eq_true_iff
        target z remoteStart batch |>.mpr hselected
    simp [hlocal, hsource]
  · have hlocal : taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
        target z remoteStart batch = false := by
      simp [taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool,
        taggedAdmittedFCFSEndpointJobsHasTargetPredecessorBool, hselected]
    have hsource : taggedAdmittedIsRemotePredecessorEndpointBatch
        target z remoteStart batch = false := by
      apply Bool.eq_false_iff.mpr
      intro hsource_true
      apply hselected
      exact (taggedAdmittedIsRemotePredecessorEndpointBatch_eq_true_iff
        target z remoteStart batch).mp hsource_true
    simp [hlocal, hsource]

/-- The retained endpoint-job list of the actual closed FCFS trace is the
canonical chronological source predecessor list.  The equality is only about
literal endpoint labels; physical segment timing stays in the concrete
closed trace and is certified separately. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_endpointJobs_eq_chronological
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    partition.1.map (fun block => block.retained.endpointJobs) =
      (taggedAdmittedChronologicalRemotePredecessorEndpointTrace
        resetTime target z remoteStart).map (fun batch => batch.endpointJobs) := by
  classical
  dsimp only
  calc
    (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1.map
        (fun block => block.retained.endpointJobs) =
        ((taggedAdmittedFCFSSourceEndpointBatchTrace resetTime 0 target z).filter
          (taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool
            target z remoteStart)).map (fun batch => batch.endpointJobs) :=
      taggedAdmittedClosedPreTagSourceProjectionPartition_retained_endpointJobs_eq_sourceEndpointFilter
        resetTime target z htarget_good capacity weight remoteStart
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    _ = ((taggedAdmittedFCFSSourceEndpointBatchTrace resetTime 0 target z).filter
          (taggedAdmittedIsRemotePredecessorEndpointBatch
            target z remoteStart)).map (fun batch => batch.endpointJobs) := by
      rw [taggedAdmittedFCFSSourceEndpointHasTargetPredecessorBool_eq_sourceOrderPredicate]
    _ = (taggedAdmittedChronologicalRemotePredecessorEndpointTrace
          resetTime target z remoteStart).map (fun batch => batch.endpointJobs) := by
      rw [taggedAdmittedFCFSSourceEndpointBatchTrace_filter_remotePredecessor_eq_chronological
        resetTime target z htarget_good remoteStart hcoverage]

/-- The semantic partition has exactly one annotated retained block for each
finite target predecessor, and its order is the literal chronological source
order.  This is an enumeration result, not a reconstruction from aggregate
work: the pointwise equality retains the full endpoint job batch. -/
theorem exists_taggedAdmittedClosedPreTagSourceProjectionPartition_chronologicalBlocks
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    ∃ blocks : Fin remoteStart → FiniteGPSFCFSSemanticProjectionBlock Category
        (TaggedAdmittedSourceJobId Category),
      List.ofFn blocks = partition.1 ∧
      ∀ j : Fin remoteStart,
        (blocks j).retained.endpointJobs =
          ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
            resetTime target z remoteStart)[j.1]'(by simp [
              taggedAdmittedChronologicalRemotePredecessorEndpointTrace])).endpointJobs := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  let chronological := taggedAdmittedChronologicalRemotePredecessorEndpointTrace
    resetTime target z remoteStart
  have hordered : partition.1.map (fun block => block.retained.endpointJobs) =
      chronological.map (fun batch => batch.endpointJobs) := by
    simpa [partition, chronological] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_retained_endpointJobs_eq_chronological
        resetTime target z htarget_good capacity weight remoteStart hcoverage
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg)
  have hchronological_length : chronological.length = remoteStart := by
    simp [chronological, taggedAdmittedChronologicalRemotePredecessorEndpointTrace]
  have hlength : partition.1.length = remoteStart := by
    have hlengths := congrArg List.length hordered
    simpa [hchronological_length] using hlengths
  let blocks : Fin remoteStart → FiniteGPSFCFSSemanticProjectionBlock Category
      (TaggedAdmittedSourceJobId Category) := fun j =>
    partition.1.get ⟨j.1, by rw [hlength]; exact j.2⟩
  have hblocks : List.ofFn blocks = partition.1 := by
    apply List.ext_getElem
    · simp [hlength]
    · intro i hi_blocks hi_partition
      rw [List.getElem_ofFn]
      simp [blocks]
  refine ⟨blocks, hblocks, ?_⟩
  intro j
  have hj_partition : j.1 < partition.1.length := by
    rw [hlength]
    exact j.2
  have hj_chronological : j.1 < chronological.length := by
    rw [hchronological_length]
    exact j.2
  have hleft : (partition.1.map (fun block => block.retained.endpointJobs))[j.1]? =
      some (blocks j).retained.endpointJobs := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hj_partition]
    simp [blocks]
  have hright : (chronological.map (fun batch => batch.endpointJobs))[j.1]? =
      some (chronological[j.1]'hj_chronological).endpointJobs := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hj_chronological]
    rfl
  have hget := congrArg (fun entries => entries[j.1]?) hordered
  change (partition.1.map (fun block => block.retained.endpointJobs))[j.1]? =
    (chronological.map (fun batch => batch.endpointJobs))[j.1]? at hget
  rw [hleft, hright] at hget
  exact Option.some.inj hget

/-- Once the reset window is known to cover exactly `remoteStart` literal
target predecessors, every target job occurring in the closed annotated trace
has one of those selected source labels.  This is the source-side converse
needed to show that a nonselected step has zero target aggregate batch work. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_is_remote_predecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ step.endpointJobs.jobs target) :
    ∃ n : Nat, n < remoteStart ∧
      job = taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∧
      finiteGPSExecutionSegmentEndTime step.segment =
        candidatePalmArrival z.1.1 (Int.negSucc n) := by
  rcases taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_origin
      resetTime target z htarget_good capacity weight step hstep job hjob with
      ⟨n, hn_ledger, hjob_eq, htime⟩
  have hindices : taggedAdmittedArrivalIndicesBetween resetTime 0 target z target =
      (Finset.range remoteStart).image Int.negSucc :=
    taggedAdmittedTargetArrivalIndicesBetween_eq_range_image_of_pastWindowCoverage
      resetTime target z htarget_good remoteStart hcoverage
  rw [hindices] at hn_ledger
  rcases Finset.mem_image.mp hn_ledger with ⟨m, hm, hmn⟩
  refine ⟨m, Finset.mem_range.mp hm, ?_, ?_⟩
  · simpa [hmn] using hjob_eq
  · simpa [hmn] using htime

/-- A closed source-trace step that carries none of the literal target
predecessors selected for the finite remote window has zero *target* endpoint
batch.  This conclusion is semantic: it combines literal job provenance with
the compatible FCFS aggregate certificate, and never tests whether a target
work mark happened to be nonzero. -/
theorem taggedAdmittedFiniteGPSClosedPreTagFCFSStep_target_batch_eq_zero_of_no_target_predecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight)
    (hno_target_predecessor :
      ¬ taggedAdmittedClosedPreTagStepIsTargetPredecessor
        target z remoteStart step) :
    step.segment.endpointBatch target = 0 := by
  have hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight) := by
    exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      resetTime 0 target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have haggregate :=
    finiteGPSFCFSRunSegmentStepsCompatible_endpointJobs_aggregateCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight)
      hcompatible step hstep
  have hjobs_empty : step.endpointJobs.jobs target = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro job hjob
    rcases taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_is_remote_predecessor
        resetTime target z htarget_good capacity weight remoteStart hcoverage
        step hstep job hjob with
        ⟨n, hn, hjob_eq, _htime⟩
    apply hno_target_predecessor
    refine ⟨n, hn, ?_⟩
    simpa [hjob_eq] using hjob
  rw [← haggregate target]
  simp [FiniteGPSFCFSEndpointJobs.classWork, hjobs_empty,
    finiteGPSFCFSJobWork]

/-- Every discarded prefix step in the literal-target semantic partition has
zero target aggregate work.  Its service duration remains in the projected
block; only its target endpoint batch is zero. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_zeroPrefix_target_batch_zero
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∀ block ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1,
      ∀ step ∈ block.zeroPrefix, step.segment.endpointBatch target = 0 := by
  classical
  intro block hblock step hstep
  have hno_target_predecessor :=
    taggedAdmittedClosedPreTagSourceProjectionPartition_zeroPrefix_has_no_target_predecessor
      resetTime target z htarget_good capacity weight remoteStart
      block hblock step hstep
  have hsource_step : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight := by
    unfold taggedAdmittedClosedPreTagSourceProjectionPartition at hblock
    exact finiteGPSFCFSSemanticProjectionPartition_zeroPrefix_mem_original
      (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight)
      block hblock step hstep
  exact taggedAdmittedFiniteGPSClosedPreTagFCFSStep_target_batch_eq_zero_of_no_target_predecessor
    resetTime target z htarget_good capacity weight remoteStart hcoverage
    hreset_le_zero hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    step hsource_step hno_target_predecessor

/-- The final source-to-tag suffix of the semantic partition also has zero
target endpoint batches.  It is a real service suffix (including the
computational zero fence), not a replacement arrival at the Palm epoch. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_target_batch_zero
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∀ step ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).2,
      step.segment.endpointBatch target = 0 := by
  classical
  intro step hstep
  have hno_target_predecessor :=
    taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_has_no_target_predecessor
      resetTime target z htarget_good capacity weight remoteStart step hstep
  have hsource_step : step ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight := by
    unfold taggedAdmittedClosedPreTagSourceProjectionPartition at hstep
    exact finiteGPSFCFSSemanticProjectionPartition_terminal_mem_original
      (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight)
      step hstep
  exact taggedAdmittedFiniteGPSClosedPreTagFCFSStep_target_batch_eq_zero_of_no_target_predecessor
    resetTime target z htarget_good capacity weight remoteStart hcoverage
    hreset_le_zero hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    step hsource_step hno_target_predecessor

/-- Every retained block carries a literal finite-window target predecessor,
and its retained concrete segment ends at that predecessor's actual physical
epoch.  The witness is an identifier, not a positive-work test; a zero-mark
exponential arrival remains retained. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_predecessor_endTime
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    ∀ block ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1,
      ∃ n : Nat, n < remoteStart ∧
        taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
          block.retained.endpointJobs.jobs target ∧
        finiteGPSExecutionSegmentEndTime block.retained.segment =
          candidatePalmArrival z.1.1 (Int.negSucc n) := by
  classical
  intro block hblock
  rcases taggedAdmittedClosedPreTagSourceProjectionPartition_retained_has_target_predecessor
      resetTime target z htarget_good capacity weight remoteStart
      block hblock with ⟨n, hn, hjob⟩
  have hsource_step : block.retained ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight := by
    unfold taggedAdmittedClosedPreTagSourceProjectionPartition at hblock
    exact finiteGPSFCFSSemanticProjectionPartition_retained_mem_original
      (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight)
      block hblock
  rcases taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_target_job_origin
      resetTime target z htarget_good capacity weight block.retained hsource_step
      (taggedAdmittedFCFSJob target z (target, Int.negSucc n)) hjob with
      ⟨m, _hm, hjob_eq, htime⟩
  have hindex : m = Int.negSucc n :=
    taggedAdmittedFCFSJob_injective target z target hjob_eq.symm
  refine ⟨n, hn, hjob, ?_⟩
  simpa [hindex] using htime

/-- The retained endpoint's stored target aggregate batch is the work mark
of the same literal predecessor identified by the semantic selector. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_retained_predecessor_batch
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat) :
    ∀ block ∈ (taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart).1,
      ∃ n : Nat, n < remoteStart ∧
        taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
          block.retained.endpointJobs.jobs target ∧
        block.retained.segment.endpointBatch target =
          stationaryAdmittedTargetPalmRemotePastBatch target z n := by
  classical
  intro block hblock
  rcases taggedAdmittedClosedPreTagSourceProjectionPartition_retained_has_target_predecessor
      resetTime target z htarget_good capacity weight remoteStart
      block hblock with ⟨n, hn, hjob⟩
  have hsource_step : block.retained ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
      resetTime target z htarget_good capacity weight := by
    unfold taggedAdmittedClosedPreTagSourceProjectionPartition at hblock
    exact finiteGPSFCFSSemanticProjectionPartition_retained_mem_original
      (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight)
      block hblock
  refine ⟨n, hn, hjob, ?_⟩
  exact taggedAdmittedFiniteGPSClosedPreTagFCFSStep_target_predecessor_batch
    resetTime target z htarget_good capacity weight block.retained hsource_step n hjob

/-- The executable closed pre-tag scalar comparator is exactly its semantic
projection onto literal target predecessor endpoints.  This is the fully
source-instantiated compression step: discarded intervals and the final
source-to-tag suffix have proved zero target batches, but all of their actual
service durations remain in the scalar recursion.  It does not yet claim the
retained blocks have been enumerated in remote-past order; that separate
finite ordering obligation is what connects this result to Lindley's direct
target comparator. -/
theorem taggedAdmittedFiniteGPSClosedSegmentComparator_eq_sourceProjection
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    finiteGPSConstantRateSegmentComparator (capacity * weight target) target
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments =
      finiteGPSConstantRateProjectionComparatorFrom 0
        (capacity * weight target) target
        (partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase)
        (partition.2.map fun step => step.segment) := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  let blocks := partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase
  let terminal := partition.2.map fun step => step.segment
  have hsegments : finiteGPSConstantRateProjectionSegments blocks terminal =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments := by
    simpa [partition, blocks, terminal] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_erase_eq_closed_history
        resetTime target z htarget_good capacity weight remoteStart)
  change finiteGPSConstantRateSegmentComparatorFrom 0
    (capacity * weight target) target
    (taggedAdmittedFiniteGPSClosedPreTagHistory
      resetTime 0 target z htarget_good capacity weight).segments = _
  rw [← hsegments]
  apply finiteGPSConstantRateSegmentComparatorFrom_eq_projectionComparatorFrom
    0 (capacity * weight target) target blocks terminal
  · norm_num
  · exact mul_nonneg hcapacity.le (hweight_pos target).le
  · intro rawBlock hrawBlock rawSegment hrawSegment
    rcases List.mem_map.mp (by simpa [blocks] using hrawBlock) with
      ⟨annotatedBlock, hannotatedBlock, rfl⟩
    change rawSegment ∈ annotatedBlock.zeroPrefix.map (fun step => step.segment)
      at hrawSegment
    rcases List.mem_map.mp hrawSegment with ⟨annotatedStep, hannotatedStep, rfl⟩
    have hsource_step : annotatedStep ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight := by
      exact finiteGPSFCFSSemanticProjectionPartition_zeroPrefix_mem_original
        (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
        (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
          resetTime target z htarget_good capacity weight)
        annotatedBlock (by simpa [partition] using hannotatedBlock)
        annotatedStep hannotatedStep
    exact taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_duration_nonneg
      resetTime target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      annotatedStep hsource_step
  · intro rawBlock hrawBlock
    rcases List.mem_map.mp (by simpa [blocks] using hrawBlock) with
      ⟨annotatedBlock, hannotatedBlock, rfl⟩
    have hsource_step : annotatedBlock.retained ∈
        taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
          resetTime target z htarget_good capacity weight := by
      exact finiteGPSFCFSSemanticProjectionPartition_retained_mem_original
        (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
        (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
          resetTime target z htarget_good capacity weight)
        annotatedBlock (by simpa [partition] using hannotatedBlock)
    simpa [FiniteGPSFCFSSemanticProjectionBlock.erase] using
      (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_duration_nonneg
        resetTime target z htarget_good capacity weight hreset_le_zero
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
        annotatedBlock.retained hsource_step)
  · intro rawSegment hrawSegment
    rcases List.mem_map.mp (by simpa [terminal] using hrawSegment) with
      ⟨annotatedStep, hannotatedStep, rfl⟩
    have hsource_step : annotatedStep ∈ taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
        resetTime target z htarget_good capacity weight := by
      exact finiteGPSFCFSSemanticProjectionPartition_terminal_mem_original
        (taggedAdmittedClosedPreTagStepIsTargetPredecessor target z remoteStart)
        (taggedAdmittedFiniteGPSClosedPreTagFCFSSteps
          resetTime target z htarget_good capacity weight)
        annotatedStep (by simpa [partition] using hannotatedStep)
    exact taggedAdmittedFiniteGPSClosedPreTagFCFSSteps_duration_nonneg
      resetTime target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      annotatedStep hsource_step
  · intro rawBlock hrawBlock rawSegment hrawSegment
    rcases List.mem_map.mp (by simpa [blocks] using hrawBlock) with
      ⟨annotatedBlock, hannotatedBlock, rfl⟩
    change rawSegment ∈ annotatedBlock.zeroPrefix.map (fun step => step.segment)
      at hrawSegment
    rcases List.mem_map.mp hrawSegment with ⟨annotatedStep, hannotatedStep, rfl⟩
    exact taggedAdmittedClosedPreTagSourceProjectionPartition_zeroPrefix_target_batch_zero
      resetTime target z htarget_good capacity weight remoteStart hcoverage
      hreset_le_zero hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      annotatedBlock (by simpa [partition] using hannotatedBlock)
      annotatedStep hannotatedStep
  · intro rawSegment hrawSegment
    rcases List.mem_map.mp (by simpa [terminal] using hrawSegment) with
      ⟨annotatedStep, hannotatedStep, rfl⟩
    exact taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_target_batch_zero
      resetTime target z htarget_good capacity weight remoteStart hcoverage
      hreset_le_zero hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      annotatedStep (by simpa [partition] using hannotatedStep)
  · intro rawBlock hrawBlock
    rcases List.mem_map.mp (by simpa [blocks] using hrawBlock) with
      ⟨annotatedBlock, hannotatedBlock, rfl⟩
    rcases taggedAdmittedClosedPreTagSourceProjectionPartition_retained_predecessor_batch
        resetTime target z htarget_good capacity weight remoteStart
        annotatedBlock (by simpa [partition] using hannotatedBlock) with
        ⟨n, _hn, _hjob, hbatch⟩
    change 0 ≤ annotatedBlock.retained.segment.endpointBatch target
    rw [hbatch, ← taggedAdmittedSourceWork_target_negSucc_eq_remotePastBatch]
    exact taggedAdmittedSourceWork_nonneg target z hsource_work_nonneg
      (target, Int.negSucc n)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
