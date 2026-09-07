import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSRateFloor
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteExecution
import Mathlib.Tactic

/-!
# Source-identified FCFS accounting for the tagged direct-admitted GPS input

This module refines the finite target/passive tagged GPS construction with
literal source-job identities.  The selected request is retained as the real
identifier `(target, 0)`; passive jobs retain their actual category and
integer source labels.  At an external endpoint the FCFS batch contains
exactly the source jobs at that physical epoch.  Internal depletion endpoints
and a possible terminal horizon fence carry an explicitly empty source batch.

The module remains finite and pathwise.  In particular it does not construct
a stationary GPS workload, a Palm response process, or a tail bound.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The FCFS record for one literal target/passive source job.  No synthetic
scheduler index is introduced: the identifier is the actual `(category, index)`
source label. -/
def taggedAdmittedFCFSJob
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) :
    FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category) :=
  { identifier := job
    arrivalTime := taggedAdmittedSourceArrival target z job
    residualWork := taggedAdmittedSourceWork target z job }

omit [Fintype Category] in
@[simp]
theorem taggedAdmittedFCFSJob_identifier
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) :
    (taggedAdmittedFCFSJob target z job).identifier = job := rfl

omit [Fintype Category] in
@[simp]
theorem taggedAdmittedFCFSJob_arrivalTime
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) :
    (taggedAdmittedFCFSJob target z job).arrivalTime =
      taggedAdmittedSourceArrival target z job := rfl

omit [Fintype Category] in
@[simp]
theorem taggedAdmittedFCFSJob_residualWork
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (job : TaggedAdmittedSourceJobId Category) :
    (taggedAdmittedFCFSJob target z job).residualWork =
      taggedAdmittedSourceWork target z job := rfl

omit [Fintype Category] in
/-- Within a fixed class, retaining the literal integer label makes the
source-job representation injective. -/
theorem taggedAdmittedFCFSJob_injective
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (k : Category) :
    Function.Injective (fun n : ℤ => taggedAdmittedFCFSJob target z (k, n)) := by
  intro left right hjob
  have hidentifier := congrArg FiniteGPSFCFSJob.identifier hjob
  exact congrArg Prod.snd hidentifier

/-- Literal source indices of one category that occur at one exact physical
endpoint epoch. -/
def taggedAdmittedJobIndicesAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (k : Category) : Finset ℤ :=
  (taggedAdmittedArrivalIndicesBetween start horizon target z k).filter fun n =>
    taggedAdmittedSourceArrival target z (k, n) = eventTime

/-- The explicit FCFS source jobs arriving at one exact external epoch.  The
integer source label gives a deterministic within-class order for ties. -/
def taggedAdmittedFCFSJobsAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ) :
    FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category) where
  jobs := fun k =>
    ((taggedAdmittedJobIndicesAt start horizon target z eventTime k).sort
      (fun left right : ℤ => left ≤ right)).map
      (fun n => taggedAdmittedFCFSJob target z (k, n))

omit [Fintype Category] in
/-- Endpoint-index membership is exactly finite-ledger membership plus the
literal source epoch equality. -/
theorem mem_taggedAdmittedJobIndicesAt_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (k : Category) (n : ℤ) :
    n ∈ taggedAdmittedJobIndicesAt start horizon target z eventTime k ↔
      n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k ∧
        taggedAdmittedSourceArrival target z (k, n) = eventTime := by
  simp [taggedAdmittedJobIndicesAt]

omit [Fintype Category] in
/-- A literal source job occurs in an endpoint list precisely at its actual
physical arrival epoch. -/
theorem mem_taggedAdmittedFCFSJob_jobsAt_iff
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (k : Category) (n : ℤ) :
    taggedAdmittedFCFSJob target z (k, n) ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs k ↔
      n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k ∧
        taggedAdmittedSourceArrival target z (k, n) = eventTime := by
  constructor
  · intro hjob
    unfold taggedAdmittedFCFSJobsAt at hjob
    rcases List.mem_map.mp hjob with ⟨m, hm, hm_job⟩
    have hindex : m = n := taggedAdmittedFCFSJob_injective target z k hm_job
    subst m
    apply (mem_taggedAdmittedJobIndicesAt_iff start horizon target z eventTime k n).mp
    exact (Finset.mem_sort (fun left right : ℤ => left ≤ right)).mp hm
  · rintro ⟨hn, htime⟩
    unfold taggedAdmittedFCFSJobsAt
    apply List.mem_map.mpr
    refine ⟨n, ?_, rfl⟩
    apply (Finset.mem_sort (fun left right : ℤ => left ≤ right)).mpr
    exact (mem_taggedAdmittedJobIndicesAt_iff start horizon target z eventTime k n).mpr
      ⟨hn, htime⟩

omit [Fintype Category] in
/-- Each actual source job is placed in one endpoint batch, indexed by its
own literal source epoch. -/
theorem taggedAdmittedFCFSJob_appears_in_exactly_one_batch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (k : Category) (n : ℤ)
    (hn : n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k) :
    taggedAdmittedFCFSJob target z (k, n) ∈
        (taggedAdmittedFCFSJobsAt start horizon target z
          (taggedAdmittedSourceArrival target z (k, n))).jobs k ∧
      ∀ eventTime,
        taggedAdmittedFCFSJob target z (k, n) ∈
          (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs k →
          eventTime = taggedAdmittedSourceArrival target z (k, n) := by
  constructor
  · exact (mem_taggedAdmittedFCFSJob_jobsAt_iff
      start horizon target z (taggedAdmittedSourceArrival target z (k, n)) k n).mpr
      ⟨hn, rfl⟩
  · intro eventTime hjob
    exact (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z eventTime k n).mp
      hjob |>.2.symm

omit [Fintype Category] in
/-- Summing source-identified endpoint jobs gives exactly the existing
aggregate target/passive source batch. -/
theorem taggedAdmittedFCFSJobsAt_classWork_eq_taggedAdmittedBatchAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (k : Category) :
    (taggedAdmittedFCFSJobsAt start horizon target z eventTime).classWork k =
      taggedAdmittedBatchAt start horizon target z eventTime k := by
  let indices := taggedAdmittedJobIndicesAt start horizon target z eventTime k
  have hnodup : (indices.sort (fun left right : ℤ => left ≤ right)).Nodup :=
    Finset.sort_nodup indices (fun left right : ℤ => left ≤ right)
  have htoFinset : (indices.sort (fun left right : ℤ => left ≤ right)).toFinset =
      indices := by
    ext n
    simp
  simp [FiniteGPSFCFSEndpointJobs.classWork, finiteGPSFCFSJobWork,
    taggedAdmittedFCFSJobsAt]
  change ((indices.sort (fun left right : ℤ => left ≤ right)).map
      (fun n => taggedAdmittedSourceWork target z (k, n))).sum =
    taggedAdmittedBatchAt start horizon target z eventTime k
  calc
    ((indices.sort (fun left right : ℤ => left ≤ right)).map
        (fun n => taggedAdmittedSourceWork target z (k, n))).sum =
        (indices.sort (fun left right : ℤ => left ≤ right)).toFinset.sum
          (fun n => taggedAdmittedSourceWork target z (k, n)) :=
      (List.sum_toFinset (fun n => taggedAdmittedSourceWork target z (k, n)) hnodup).symm
    _ = ∑ n ∈ indices, taggedAdmittedSourceWork target z (k, n) := by
      rw [htoFinset]
    _ = taggedAdmittedBatchAt start horizon target z eventTime k := by
      rfl

omit [Fintype Category] in
/-- Nonnegative literal source work yields a nonnegative explicit endpoint
job batch. -/
theorem taggedAdmittedFCFSJobsAt_nonnegative
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (eventTime : ℝ) :
    (taggedAdmittedFCFSJobsAt start horizon target z eventTime).Nonnegative := by
  intro k job hjob
  unfold taggedAdmittedFCFSJobsAt at hjob
  rcases List.mem_map.mp hjob with ⟨n, _hn, rfl⟩
  exact taggedAdmittedSourceWork_nonneg target z hwork_nonneg (k, n)

/-- If the finite interval contains the Palm epoch, the actual selected
request `(target, 0)` occurs in its zero-time FCFS endpoint batch. -/
theorem taggedAdmittedTargetFCFSJob_mem_zeroBatch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target := by
  apply (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z 0 target 0).mpr
  refine ⟨?_, taggedAdmittedSourceArrival_target_zero target z⟩
  exact (mem_taggedAdmittedSourceJobLedger_iff start horizon target z target 0).mp
    ((mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
      ⟨hstart, hhorizon⟩)

/-- A source endpoint batch retains its exact physical epoch together with
its source-identified FCFS jobs. -/
structure TaggedAdmittedFiniteGPSTimedEndpointJobs (Category : Type*) where
  eventTime : ℝ
  endpointJobs : FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category)

/-- The chronological endpoint-job trace of the literal tagged source
batches. -/
def taggedAdmittedFCFSSourceEndpointBatchTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    List (TaggedAdmittedFiniteGPSTimedEndpointJobs Category) :=
  (taggedAdmittedBatchTimeTrace start horizon target z).map fun eventTime =>
    { eventTime := eventTime
      endpointJobs := taggedAdmittedFCFSJobsAt start horizon target z eventTime }

/-- Every timed source endpoint batch has exactly the aggregate source work
used by the tagged finite GPS trace at that epoch. -/
theorem taggedAdmittedFCFSSourceEndpointBatchTrace_classWork
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (batch : TaggedAdmittedFiniteGPSTimedEndpointJobs Category)
    (hbatch : batch ∈ taggedAdmittedFCFSSourceEndpointBatchTrace start horizon target z)
    (k : Category) :
    batch.endpointJobs.classWork k =
      taggedAdmittedBatchAt start horizon target z batch.eventTime k := by
  rcases List.mem_map.mp hbatch with ⟨eventTime, _heventTime, rfl⟩
  exact taggedAdmittedFCFSJobsAt_classWork_eq_taggedAdmittedBatchAt
    start horizon target z eventTime k

/-- Each literal finite-ledger job occurs in exactly one timed source
endpoint batch. -/
theorem taggedAdmittedFCFSJob_appears_once_in_sourceEndpointBatchTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (k : Category) (n : ℤ)
    (hn : n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k) :
    ∃! batch : TaggedAdmittedFiniteGPSTimedEndpointJobs Category,
      batch ∈ taggedAdmittedFCFSSourceEndpointBatchTrace start horizon target z ∧
        taggedAdmittedFCFSJob target z (k, n) ∈ batch.endpointJobs.jobs k := by
  let sourceTime := taggedAdmittedSourceArrival target z (k, n)
  have hsourceTime_batch : sourceTime ∈ taggedAdmittedBatchTimes start horizon target z := by
    apply (mem_taggedAdmittedBatchTimes_iff start horizon target z sourceTime).mpr
    exact ⟨(k, n),
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hn, rfl⟩
  have hsourceTime_trace : sourceTime ∈ taggedAdmittedBatchTimeTrace start horizon target z :=
    (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hsourceTime_batch
  let sourceBatch : TaggedAdmittedFiniteGPSTimedEndpointJobs Category :=
    { eventTime := sourceTime
      endpointJobs := taggedAdmittedFCFSJobsAt start horizon target z sourceTime }
  refine ⟨sourceBatch, ?_, ?_⟩
  · constructor
    · exact List.mem_map.mpr ⟨sourceTime, hsourceTime_trace, rfl⟩
    · simpa [sourceBatch] using
        (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z sourceTime k n).mpr
          ⟨hn, rfl⟩
  · intro batch hbatch
    rcases List.mem_map.mp hbatch.1 with ⟨eventTime, _heventTime, hbatch_eq⟩
    subst batch
    have heventTime_eq_sourceTime : eventTime = sourceTime :=
      (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z eventTime k n).mp
        hbatch.2 |>.2.symm
    subst eventTime
    rfl

/-- Empty source-job data at an internal computational endpoint. -/
def taggedAdmittedFCFSComputationalEndpointJobs :
    FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category) where
  jobs := fun _ => []

omit [Fintype Category] [DecidableEq Category] in
@[simp]
theorem taggedAdmittedFCFSComputationalEndpointJobs_classWork (k : Category) :
    (taggedAdmittedFCFSComputationalEndpointJobs (Category := Category)).classWork k = 0 := by
  simp [FiniteGPSFCFSEndpointJobs.classWork,
    taggedAdmittedFCFSComputationalEndpointJobs]

omit [Fintype Category] [DecidableEq Category] in
theorem taggedAdmittedFCFSComputationalEndpointJobs_nonnegative :
    (taggedAdmittedFCFSComputationalEndpointJobs (Category := Category)).Nonnegative := by
  intro k job hjob
  simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- When a concrete GPS segment reaches its scheduled source epoch, the
literal source jobs at that epoch exactly decompose the segment batch. -/
theorem taggedAdmittedFCFSJobsAt_aggregateCompatible_buildExecutionSegment_of_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = true) :
    (taggedAdmittedFCFSJobsAt start horizon target z eventTime).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay) := by
  intro k
  rw [taggedAdmittedFCFSJobsAt_classWork_eq_taggedAdmittedBatchAt]
  exact (finiteGPSBuildExecutionSegment_endpointBatch_eq_batchWork_of_external
    capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay hExternal k).symm

/-- An internal depletion endpoint contains no source job and has zero
aggregate endpoint batch by the executable GPS kernel. -/
theorem taggedAdmittedFCFSComputationalEndpointJobs_aggregateCompatible_buildExecutionSegment_of_not_external
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hnotExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = false) :
    (taggedAdmittedFCFSComputationalEndpointJobs (Category := Category)).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay) := by
  intro k
  rw [taggedAdmittedFCFSComputationalEndpointJobs_classWork]
  exact (finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_not_external
    capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay hnotExternal k).symm

/-- Select literal source jobs only for an external segment endpoint.  An
internal endpoint is explicitly source-empty. -/
def taggedAdmittedFiniteGPSEndpointJobsForSegment
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (segment : FiniteGPSExecutionSegment Category) :
    FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category) :=
  if segment.endpointIsExternalBatch = true then
    taggedAdmittedFCFSJobsAt start horizon target z eventTime
  else
    taggedAdmittedFCFSComputationalEndpointJobs

omit [Fintype Category] in
/-- The selected endpoint-job decomposition is nonnegative under the
explicit pathwise nonnegative source-work condition. -/
theorem taggedAdmittedFiniteGPSEndpointJobsForSegment_nonnegative
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (eventTime : ℝ) (segment : FiniteGPSExecutionSegment Category) :
    (taggedAdmittedFiniteGPSEndpointJobsForSegment
      start horizon target z eventTime segment).Nonnegative := by
  by_cases hExternal : segment.endpointIsExternalBatch = true
  · simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using
      (taggedAdmittedFCFSJobsAt_nonnegative start horizon target z hwork_nonneg eventTime)
  · simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using
      (taggedAdmittedFCFSComputationalEndpointJobs_nonnegative (Category := Category))

/-- One concrete GPS segment together with the source-job decomposition
selected by its computed endpoint tag. -/
def taggedAdmittedFiniteGPSBuildSegmentJobStep
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  { segment := finiteGPSBuildExecutionSegment capacity weight work
      (taggedAdmittedBatchAt start horizon target z eventTime)
      currentTime nextBatchDelay
    endpointJobs := taggedAdmittedFiniteGPSEndpointJobsForSegment
      start horizon target z eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay) }

/-- The constructed source-labelled step has nonnegative endpoint jobs. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (eventTime : ℝ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedFiniteGPSBuildSegmentJobStep
      start horizon target z eventTime capacity weight work
      currentTime nextBatchDelay).endpointJobs.Nonnegative := by
  simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using
    (taggedAdmittedFiniteGPSEndpointJobsForSegment_nonnegative
      start horizon target z hwork_nonneg eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay))

/-- The endpoint jobs selected from the segment tag always have exactly the
aggregate batch work recorded by that concrete segment. -/
theorem taggedAdmittedFiniteGPSEndpointJobsForBuildSegment_aggregateCompatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedFiniteGPSEndpointJobsForSegment start horizon target z eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay)).AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay) := by
  by_cases hExternal :
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay).endpointIsExternalBatch = true
  · simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using
      (taggedAdmittedFCFSJobsAt_aggregateCompatible_buildExecutionSegment_of_external
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay hExternal)
  · have hnotExternal :
        (finiteGPSBuildExecutionSegment capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          currentTime nextBatchDelay).endpointIsExternalBatch = false := by
      cases htag :
          (finiteGPSBuildExecutionSegment capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch <;> simp_all
    simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using
      (taggedAdmittedFCFSComputationalEndpointJobs_aggregateCompatible_buildExecutionSegment_of_not_external
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
        hnotExternal)

/-- The explicit source-labelled step is aggregate-compatible with its own
concrete GPS segment. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedFiniteGPSBuildSegmentJobStep
      start horizon target z eventTime capacity weight work
      currentTime nextBatchDelay).endpointJobs.AggregateCompatible
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).segment := by
  simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using
    (taggedAdmittedFiniteGPSEndpointJobsForBuildSegment_aggregateCompatible
      start horizon target z eventTime capacity weight work currentTime nextBatchDelay)

/-- Prepend one concrete tagged-source GPS step to a compatible FCFS tail.
The side conditions come from the executable kernel and the explicit source
work condition; the transition itself is the fixed FCFS fold. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_compatible_cons
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (tail : List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (htail : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSApplySegment initial
        (taggedAdmittedFiniteGPSBuildSegmentJobStep
          start horizon target z eventTime capacity weight work
          currentTime nextBatchDelay).segment
        (taggedAdmittedFiniteGPSBuildSegmentJobStep
          start horizon target z eventTime capacity weight work
          currentTime nextBatchDelay).endpointJobs)
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).segment.endpointWorkload tail) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay :: tail) := by
  let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
    start horizon target z eventTime capacity weight work currentTime nextBatchDelay
  change
    (∀ i, initial.classWork i = work i) ∧
      (∀ i, work i = step.segment.startWorkload i) ∧
      step.endpointJobs.AggregateCompatible step.segment ∧
      step.endpointJobs.Nonnegative ∧
      (∀ i, 0 ≤ step.segment.serviceIncrement i) ∧
      (∀ i, step.segment.serviceIncrement i ≤ initial.classWork i) ∧
      (∀ i, step.segment.endpointWorkload i =
        step.segment.startWorkload i + step.segment.endpointBatch i -
          step.segment.serviceIncrement i) ∧
      FiniteGPSFCFSRunSegmentStepsCompatible
        (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        step.segment.endpointWorkload tail
  refine ⟨hinitial_matches_work, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rfl
  · exact taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
      start horizon target z eventTime capacity weight work currentTime nextBatchDelay
  · exact taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
      start horizon target z hsource_work_nonneg eventTime capacity weight work
      currentTime nextBatchDelay
  · intro i
    simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
        (batchWork := taggedAdmittedBatchAt start horizon target z eventTime)
        (startTime := currentTime)
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hnextBatchDelay_nonneg (i := i))
  · intro i
    rw [hinitial_matches_work i]
    simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_serviceIncrement_le_startWorkload
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay i)
  · intro i
    simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
      (finiteGPSBuildExecutionSegment_balance capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay i)
  · simpa [step] using htail

/-- A single concrete tagged-source GPS step gives a compatible FCFS
transition from any explicit nonnegative ledger representing its input work. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_compatible_singleton
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      [taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay] := by
  let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
    start horizon target z eventTime capacity weight work currentTime nextBatchDelay
  have hnext_matches : ∀ i,
      (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).classWork i =
        step.segment.endpointWorkload i := by
    intro i
    simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
      (finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
        (JobId := TaggedAdmittedSourceJobId Category)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay initial step.endpointJobs
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work
        (by
          simpa [step] using
            (taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
              start horizon target z eventTime capacity weight work
              currentTime nextBatchDelay)) i)
  simpa [step] using
    (taggedAdmittedFiniteGPSBuildSegmentJobStep_compatible_cons
      start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      initial [] hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hsource_work_nonneg hnextBatchDelay_nonneg
      hinitial_matches_work hnext_matches)

/-- Mirror the executable finite GPS gap recursion while retaining the
literal source jobs at an external endpoint and an empty list at internal
depletion endpoints. -/
def taggedAdmittedFiniteGPSGapSegmentJobSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay
      if duration = nextBatchDelay then
        [step]
      else
        step :: taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
          fuel capacity weight nextWork (currentTime + duration) (nextBatchDelay - duration)

/-- Erasing explicit FCFS jobs recovers the actual concrete GPS segments from
the generic bounded gap runner. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_segments
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay).map
        (fun step => step.segment) =
      finiteGPSRunGapSegments fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, finiteGPSRunGapSegments]
  | succ fuel ih =>
      simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps,
        finiteGPSRunGapSegments]
      split <;>
        simp [taggedAdmittedFiniteGPSBuildSegmentJobStep, ih]

/-- The endpoint workload computed from the annotated gap is exactly the
finite gap runner's workload. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload work
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay) =
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        nextBatchDelay).workload := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, finiteGPSRunGap,
        finiteGPSFCFSSegmentStepsEndpointWorkload]
  | succ fuel ih =>
      simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps, finiteGPSRunGap]
      split <;>
        simp [taggedAdmittedFiniteGPSBuildSegmentJobStep,
          finiteGPSFCFSSegmentStepsEndpointWorkload, ih]

/-- A compatible finite FCFS fold preserves nonnegative residual jobs. -/
theorem taggedAdmittedFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (initialWorkload : Category → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible :
      FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    (finiteGPSFCFSRunSegmentSteps initial steps).Nonnegative := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial_nonneg
  | cons step steps ih =>
      rcases hcompatible with ⟨_hledger_initial, _hinitial_start,
        _hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        _hservice_le_ledger, _hsegment_balance, htail⟩
      have hnext_nonneg :
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
        finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
          hinitial_nonneg hservice_nonneg hendpoint_nonneg
      simpa [finiteGPSFCFSRunSegmentSteps] using
        ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload)
          hnext_nonneg htail

omit [Fintype Category] [DecidableEq Category] in
/-- Compatibility composes when the second finite list starts from the exact
FCFS ledger and workload produced by the first. -/
theorem taggedAdmittedFiniteGPSFCFSRunSegmentStepsCompatible_append
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (initialWorkload : Category → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hleft : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload left)
    (hright : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps initial left)
      (finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload left) right) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload (left ++ right) := by
  induction left generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using hright
  | cons step left ih =>
      rcases hleft with ⟨hledger_initial, hinitial_start,
        hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        hservice_le_ledger, hsegment_balance, hleft_tail⟩
      refine ⟨hledger_initial, hinitial_start, hbatch_compatible,
        hendpoint_nonneg, hservice_nonneg, hservice_le_ledger,
        hsegment_balance, ?_⟩
      apply ih
      · exact hleft_tail
      · simpa [finiteGPSFCFSRunSegmentSteps,
          finiteGPSFCFSSegmentStepsEndpointWorkload] using hright

/-- Every segment in the annotated gap has an endpoint-job decomposition
matching the concrete batch field it stores. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_aggregateCompatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay,
      step.endpointJobs.AggregateCompatible step.segment := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      unfold taggedAdmittedFiniteGPSGapSegmentJobSteps
      dsimp only
      split
      · intro step hstep
        have hstep_eq : step = taggedAdmittedFiniteGPSBuildSegmentJobStep
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay := by
          simpa using hstep
        subst step
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      · intro step hstep
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime +
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (nextBatchDelay := nextBatchDelay -
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            step htail

/-- The source-identified FCFS jobs realize every finite GPS gap through the
same internal-depletion recursion as the executable aggregate runner. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_compatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay) := by
  induction fuel generalizing work currentTime nextBatchDelay initial with
  | zero =>
      simpa [taggedAdmittedFiniteGPSGapSegmentJobSteps] using hinitial_matches_work
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsingle := taggedAdmittedFiniteGPSBuildSegmentJobStep_compatible_singleton
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
          initial hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg hnextBatchDelay_nonneg hinitial_nonneg
          hinitial_matches_work
        simpa [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, hduration, step] using hsingle
      · have hinternal :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay := by
            simpa [duration] using hduration
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hresidual_delay_nonneg : 0 ≤ nextBatchDelay - duration := by
          rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
              nextBatchDelay)
        have hstep_service_nonneg : ∀ i, 0 ≤ step.segment.serviceIncrement i := by
          intro i
          simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
            (finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
              (batchWork := taggedAdmittedBatchAt start horizon target z eventTime)
              (startTime := currentTime)
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
              hnextBatchDelay_nonneg (i := i))
        have hstep_endpoint_nonneg : step.endpointJobs.Nonnegative := by
          simpa [step] using
            (taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_nonnegative
              start horizon target z hsource_work_nonneg eventTime capacity weight work
              currentTime nextBatchDelay)
        have hnext_initial_nonneg :
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
          finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
            hinitial_nonneg hstep_service_nonneg hstep_endpoint_nonneg
        have hnext_initial_matches : ∀ i,
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).classWork i =
              finiteGPSNextEventState capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay i := by
          intro i
          simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
            (finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
              (JobId := TaggedAdmittedSourceJobId Category)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay initial step.endpointJobs
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
              hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work
              (by
                simpa [step] using
                  (taggedAdmittedFiniteGPSBuildSegmentJobStep_aggregateCompatible
                    start horizon target z eventTime capacity weight work
                    currentTime nextBatchDelay)) i)
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration)
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          hnext_work_nonneg hresidual_delay_nonneg hnext_initial_nonneg
          hnext_initial_matches
        have hcons := taggedAdmittedFiniteGPSBuildSegmentJobStep_compatible_cons
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
          initial
          (taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
            fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration))
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg hnextBatchDelay_nonneg
          hinitial_matches_work (by simpa [step] using htail)
        simpa [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, hduration, step] using hcons

/-- Extract the endpoint-job batches from concrete segments that genuinely
reached their scheduled external source epoch. -/
def taggedAdmittedFiniteGPSExternalEndpointJobBatches
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) :
    List (FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category)) :=
  steps.filterMap fun step =>
    if step.segment.endpointIsExternalBatch = true then some step.endpointJobs else none

/-- If a bounded gap reaches its scheduled source batch, it has exactly one
external endpoint job batch, namely that literal source batch. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_externalEndpointJobBatches_eq_singleton_of_batchApplied
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatchApplied :
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        nextBatchDelay).batchApplied = true) :
    taggedAdmittedFiniteGPSExternalEndpointJobBatches
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay) =
      [taggedAdmittedFCFSJobsAt start horizon target z eventTime] := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGap] at hbatchApplied
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hduration' :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay =
              nextBatchDelay := by
            simpa [duration] using hduration
        have htag :
            (taggedAdmittedFiniteGPSBuildSegmentJobStep
              start horizon target z eventTime capacity weight work
              currentTime nextBatchDelay).segment.endpointIsExternalBatch = true := by
          change (finiteGPSBuildExecutionSegment capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch = true
          exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay |>.mpr hduration
        have hendpoint :
            (taggedAdmittedFiniteGPSBuildSegmentJobStep
              start horizon target z eventTime capacity weight work
              currentTime nextBatchDelay).endpointJobs =
              taggedAdmittedFCFSJobsAt start horizon target z eventTime := by
          have htag' :
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay).endpointIsExternalBatch = true := by
            simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using htag
          simp [taggedAdmittedFiniteGPSBuildSegmentJobStep,
            taggedAdmittedFiniteGPSEndpointJobsForSegment, htag']
        rw [show taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime (fuel + 1) capacity weight work
            currentTime nextBatchDelay =
            [taggedAdmittedFiniteGPSBuildSegmentJobStep
              start horizon target z eventTime capacity weight work
              currentTime nextBatchDelay] by
          simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, hduration']]
        simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches, htag, hendpoint]
      · have htailApplied :
            (finiteGPSRunGap fuel capacity weight
              (finiteGPSNextEventState capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
              (taggedAdmittedBatchAt start horizon target z eventTime)
              (nextBatchDelay - duration)).batchApplied = true := by
            simpa [finiteGPSRunGap, duration, hduration] using hbatchApplied
        have hheadNotExternal :
            (taggedAdmittedFiniteGPSBuildSegmentJobStep
              start horizon target z eventTime capacity weight work
              currentTime nextBatchDelay).segment.endpointIsExternalBatch ≠ true := by
            intro htag
            apply hduration
            apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay |>.mp
            simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using htag
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration) htailApplied
        simpa [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
          taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, hduration,
          hheadNotExternal] using htail

/-- Mirror the generic finite batch-trace recursion with the tagged-source
annotations.  If a bounded runner could not reach a batch it records only the
actual partial gap; under the ordinary positive GPS conditions below every
scheduled source batch is reached. -/
def taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight : Category → ℝ) (currentTime : ℝ) (work : Category → ℝ) :
    List ℝ → List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category))
  | [] => []
  | eventTime :: times =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      if gap.batchApplied = true then
        gapSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight eventTime gap.workload times
      else
        gapSteps

/-- The annotated batch recursion continues exactly when the executable gap
runner reaches the scheduled source batch. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime eventTime : ℝ) (times : List ℝ)
    (hbatchApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)).batchApplied = true) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work (eventTime :: times) =
      taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
        ((finiteGPSActiveClasses work).card + 1) capacity weight work
        currentTime (eventTime - currentTime) ++
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z
        capacity weight eventTime
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime)).workload times := by
  simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps, hbatchApplied]

/-- If a bounded gap did not reach the pending source epoch, the annotated
trace correctly stops at that gap and does not invent later source jobs. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime eventTime : ℝ) (times : List ℝ)
    (hbatchNotApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)).batchApplied ≠ true) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work (eventTime :: times) =
      taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
        ((finiteGPSActiveClasses work).card + 1) capacity weight work
        currentTime (eventTime - currentTime) := by
  simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps, hbatchNotApplied]

/-- Erasing the endpoint-job data from the annotated trace recovers exactly
the concrete segment sequence emitted by the generic pre-terminal runner. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_segments
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times).map
        (fun step => step.segment) =
      finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt start horizon target z) currentTime work times := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchApplied,
          finiteGPSRunBatchTraceSegments_cons_of_batchApplied
            capacity weight (taggedAdmittedBatchAt start horizon target z)
            currentTime work eventTime times hbatchApplied]
        simp only [List.map_append]
        rw [taggedAdmittedFiniteGPSGapSegmentJobSteps_segments]
        rw [ih
          (currentTime := eventTime)
          (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).workload)]
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchNotApplied,
          finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
            capacity weight (taggedAdmittedBatchAt start horizon target z)
            currentTime work eventTime times hbatchNotApplied]
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_segments
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

omit [Fintype Category] [DecidableEq Category] in
/-- Reading the endpoint workload after concatenated annotated FCFS steps is
the same as first reading the left list's endpoint and continuing from there. -/
theorem taggedAdmittedFiniteGPSFCFSSegmentStepsEndpointWorkload_append
    (initialWorkload : Category → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload (left ++ right) =
      finiteGPSFCFSSegmentStepsEndpointWorkload
        (finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload left) right := by
  induction left generalizing initialWorkload with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload]
  | cons step left ih =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload, ih]

/-- The endpoint workload of the complete tagged annotated source trace is
exactly the workload returned by the pre-terminal aggregate batch runner. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload work
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) currentTime work times).workload := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSRunBatchTrace, finiteGPSFCFSSegmentStepsEndpointWorkload]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchApplied,
          finiteGPSRunBatchTrace_cons_of_batchApplied
            capacity weight (taggedAdmittedBatchAt start horizon target z)
            currentTime work eventTime times hbatchApplied,
          taggedAdmittedFiniteGPSFCFSSegmentStepsEndpointWorkload_append,
          taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner,
          ih]
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchNotApplied,
          finiteGPSRunBatchTrace_cons_of_not_batchApplied
            capacity weight (taggedAdmittedBatchAt start horizon target z)
            currentTime work eventTime times hbatchNotApplied]
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

/-- Under the ordinary finite GPS hypotheses, the annotated tagged source
trace satisfies the generic FCFS fold invariant.  The supplied initial ledger
represents only the explicit pre-`start` workload; it is never synthesized
from later source jobs. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_compatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work times) := by
  induction times generalizing currentTime work initial with
  | nil =>
      simpa [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps] using
        hinitial_matches_work
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j,
          0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ taggedAdmittedBatchAt start horizon target z laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      have hgap_terminates :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).batchApplied = true := by
        exact (finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)).1
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
        capacity weight work currentTime (eventTime - currentTime)
      have hgap_compatible :
          FiniteGPSFCFSRunSegmentStepsCompatible initial work gapSteps := by
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_compatible
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime) initial
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hsource_work_nonneg (sub_nonneg.mpr hdelay) hinitial_nonneg
          hinitial_matches_work
      have hgap_fold_nonneg :
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).Nonnegative :=
        taggedAdmittedFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
          initial work gapSteps hinitial_nonneg hgap_compatible
      have hgap_endpoint :
          finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps =
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).workload := by
        simpa [gapSteps] using
          (taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointWorkload_eq_runner
            start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
            capacity weight work currentTime (eventTime - currentTime))
      have hgap_fold_matches : ∀ i,
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).classWork i =
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).workload i := by
        intro i
        calc
          (finiteGPSFCFSRunSegmentSteps initial gapSteps).classWork i =
              finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps i :=
            finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
              initial work gapSteps hinitial_nonneg hgap_compatible i
          _ = (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).workload i := by
            rw [hgap_endpoint]
      have hgap_work_nonneg : ∀ j, 0 ≤
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih
        (currentTime := eventTime)
        (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime)).workload)
        (initial := finiteGPSFCFSRunSegmentSteps initial gapSteps)
        hgap_work_nonneg hchronological_tail hbatch_tail hgap_fold_nonneg
        hgap_fold_matches
      have htail_from_gap_endpoint :
          FiniteGPSFCFSRunSegmentStepsCompatible
            (finiteGPSFCFSRunSegmentSteps initial gapSteps)
            (finiteGPSFCFSSegmentStepsEndpointWorkload work gapSteps)
            (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
              start horizon target z capacity weight eventTime
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
                (eventTime - currentTime)).workload times) := by
        rw [hgap_endpoint]
        exact htail
      have happend := taggedAdmittedFiniteGPSFCFSRunSegmentStepsCompatible_append
        initial work gapSteps
        (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight eventTime
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).workload times)
        hgap_compatible htail_from_gap_endpoint
      rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon target z capacity weight work currentTime eventTime times hgap_terminates]
      simpa [gapSteps] using happend

/-- With the standard positive GPS conditions, every scheduled source batch
is reached exactly once and the external endpoint job batches of the actual
annotated segment trace are the chronological literal source-batch trace. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_externalEndpointJobBatches_eq_sourceBatchTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j) :
    taggedAdmittedFiniteGPSExternalEndpointJobBatches
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work times) =
      times.map (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches,
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j,
          0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ taggedAdmittedBatchAt start horizon target z laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      have hgap_terminates :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).batchApplied = true ∧
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ j, 0 ≤
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih
        (currentTime := eventTime)
        (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime)).workload)
        hgap_nonneg hchronological_tail hbatch_tail
      rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon target z capacity weight work currentTime eventTime times hgap_terminates.1]
      unfold taggedAdmittedFiniteGPSExternalEndpointJobBatches
      rw [List.filterMap_append]
      change taggedAdmittedFiniteGPSExternalEndpointJobBatches
          (taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
            ((finiteGPSActiveClasses work).card + 1) capacity weight work
            currentTime (eventTime - currentTime)) ++
          taggedAdmittedFiniteGPSExternalEndpointJobBatches
            (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
              start horizon target z capacity weight eventTime
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
                (eventTime - currentTime)).workload times) =
        (eventTime :: times).map
          (fun laterTime => taggedAdmittedFCFSJobsAt start horizon target z laterTime)
      rw [taggedAdmittedFiniteGPSGapSegmentJobSteps_externalEndpointJobBatches_eq_singleton_of_batchApplied
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)
          hgap_terminates.1,
        htail]
      rfl

/-- The concrete pre-terminal segment history for the genuine tagged
target/passive source trace.  This is the segment-level counterpart of the
existing aggregate pre-terminal run. -/
def taggedAdmittedFiniteGPSPreTerminalHistory
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    FiniteGPSBatchSegmentHistory Category :=
  finiteGPSRunExternalBatchTraceWithSegments capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good)

/-- The pre-terminal segment history retains exactly the original aggregate
finite runner result. -/
theorem taggedAdmittedFiniteGPSPreTerminalHistory_final
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    (taggedAdmittedFiniteGPSPreTerminalHistory
      start horizon target z htarget_good capacity weight initialWork).final =
      taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork := rfl

/-- The source-labelled FCFS steps for the pre-terminal tagged batch trace. -/
def taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) :=
  taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    start horizon target z capacity weight start initialWork
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times

/-- Erasing source-job data from the pre-terminal FCFS steps recovers exactly
the concrete segment history used by the tagged aggregate run. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork).map
        (fun step => step.segment) =
      (taggedAdmittedFiniteGPSPreTerminalHistory
        start horizon target z htarget_good capacity weight initialWork).segments := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps,
    taggedAdmittedFiniteGPSPreTerminalHistory,
    finiteGPSRunExternalBatchTraceWithSegments] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_segments
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)

/-- Every literal-source FCFS step in the actual pre-terminal execution has
the concrete GPS guaranteed-rate floor whenever the chosen class was
backlogged at that step's left endpoint.  The proof goes through the
executable segment erasure, not a caller-supplied path relation.  Thus an
external endpoint batch is still absent from the preceding interval, while
internal depletion endpoints remain present as source-empty FCFS steps. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    ∀ step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (taggedAdmittedExternalBatchTrace
        start horizon target z htarget_good).times, ∀ j,
        0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime j
  have hrunner :=
    finiteGPSRunBatchTraceSegments_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      (times := (taggedAdmittedExternalBatchTrace
        start horizon target z htarget_good).times)
      (i := i)
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
      hbatch_nonneg
  intro step hstep hactive
  have hstep_segment : step.segment ∈
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork).map
        (fun laterStep => laterStep.segment) :=
    List.mem_map.mpr ⟨step, hstep, rfl⟩
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments] at hstep_segment
  change step.segment ∈ finiteGPSRunBatchTraceSegments capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times at hstep_segment
  exact hrunner step.segment hstep_segment hactive

/-- Summing only the chronologically ordered intervals in which class `i` is
actually backlogged, the literal-source FCFS execution stores at least its
GPS guaranteed rate times the exact active elapsed duration.  Endpoint source
jobs and internal source-empty depletion endpoints remain in the underlying
trace; the active filter merely excludes intervals that cannot serve `i`. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_weightedCapacity_mul_activeDuration_le_activeService
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    capacity * weight i * finiteGPSFCFSSegmentStepsActiveDuration i
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) ≤
      finiteGPSFCFSSegmentStepsActiveService i
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight initialWork) := by
  apply finiteGPSFCFSSegmentSteps_weightedCapacity_mul_activeDuration_le_activeService
  intro step hstep hactive
  exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    start horizon target z htarget_good capacity weight initialWork
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hsource_work_nonneg i
    step hstep hactive

/-- The actual external endpoint job batches in the pre-terminal FCFS steps
are exactly the chronological literal tagged source batches. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    taggedAdmittedFiniteGPSExternalEndpointJobBatches
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) =
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.map
        (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (taggedAdmittedExternalBatchTrace
        start horizon target z htarget_good).times, ∀ j,
        0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime j
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_externalEndpointJobBatches_eq_sourceBatchTrace
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
      hbatch_nonneg)

/-- The source-labelled pre-terminal steps satisfy the generic FCFS fold
compatibility invariant from an explicit nonnegative initial job ledger. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_work_nonneg : ∀ i, 0 ≤ initialWork i)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = initialWork i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial initialWork
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) := by
  have hbatch_nonneg :
      ∀ eventTime ∈ (taggedAdmittedExternalBatchTrace
        start horizon target z htarget_good).times, ∀ j,
        0 ≤ taggedAdmittedBatchAt start horizon target z eventTime j := by
    intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime j
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_compatible
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times initial
      hcapacity hweight_pos htotal_weight_le_one
      hinitial_work_nonneg hsource_work_nonneg
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
      hbatch_nonneg hinitial_nonneg hinitial_matches_work)

/-- The endpoint workload read from the pre-terminal FCFS steps is precisely
the final workload of the concrete tagged source segment history. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointWorkload_eq_history
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWork
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) =
      (taggedAdmittedFiniteGPSPreTerminalHistory
        start horizon target z htarget_good capacity weight initialWork).final.workload := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps,
    taggedAdmittedFiniteGPSPreTerminalHistory,
    finiteGPSRunExternalBatchTraceWithSegments] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
      start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)

/-- Folding literal source jobs through the pre-terminal tagged GPS segments
produces a residual FCFS ledger whose aggregate class work equals the concrete
pre-terminal GPS endpoint workload. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_fold_classWork_eq_history
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_work_nonneg : ∀ i, 0 ≤ initialWork i)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = initialWork i)
    (i : Category) :
    (finiteGPSFCFSRunSegmentSteps initial
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork)).classWork i =
      (taggedAdmittedFiniteGPSPreTerminalHistory
        start horizon target z htarget_good capacity weight initialWork).final.workload i := by
  calc
    (finiteGPSFCFSRunSegmentSteps initial
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork)).classWork i =
        finiteGPSFCFSSegmentStepsEndpointWorkload initialWork
          (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
            start horizon target z htarget_good capacity weight initialWork) i :=
      finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
        initial initialWork
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight initialWork)
        hinitial_nonneg
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
          start horizon target z htarget_good capacity weight initialWork initial
          hcapacity hweight_pos htotal_weight_le_one hinitial_work_nonneg hsource_work_nonneg
          hinitial_nonneg hinitial_matches_work) i
    _ = (taggedAdmittedFiniteGPSPreTerminalHistory
        start horizon target z htarget_good capacity weight initialWork).final.workload i := by
      rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointWorkload_eq_history
        start horizon target z htarget_good capacity weight initialWork]

/-- Each literal finite-ledger source job occurs in exactly one actual
external endpoint batch of the tagged pre-terminal segment execution.  This
is a statement about the emitted endpoint list, so internal depletion steps
are excluded by construction. -/
theorem taggedAdmittedFCFSJob_appears_once_in_preTerminalExternalEndpointBatches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (k : Category) (n : ℤ)
    (hn : n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k) :
    ∃! endpointJobs : FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category),
      endpointJobs ∈ taggedAdmittedFiniteGPSExternalEndpointJobBatches
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight initialWork) ∧
        taggedAdmittedFCFSJob target z (k, n) ∈ endpointJobs.jobs k := by
  let sourceTime := taggedAdmittedSourceArrival target z (k, n)
  have hsourceTime_batch : sourceTime ∈ taggedAdmittedBatchTimes start horizon target z := by
    apply (mem_taggedAdmittedBatchTimes_iff start horizon target z sourceTime).mpr
    exact ⟨(k, n),
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hn, rfl⟩
  have hsourceTime_trace : sourceTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times :=
    (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hsourceTime_batch
  let sourceBatch := taggedAdmittedFCFSJobsAt start horizon target z sourceTime
  have hendpoint_trace :=
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
      start horizon target z htarget_good capacity weight initialWork
      hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hsource_work_nonneg
  refine ⟨sourceBatch, ?_, ?_⟩
  · constructor
    · rw [hendpoint_trace]
      exact List.mem_map.mpr ⟨sourceTime, hsourceTime_trace, rfl⟩
    · simpa [sourceBatch] using
        (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z sourceTime k n).mpr
          ⟨hn, rfl⟩
  · intro endpointJobs hendpointJobs
    rw [hendpoint_trace] at hendpointJobs
    rcases List.mem_map.mp hendpointJobs.1 with ⟨eventTime, _heventTime, hbatch_eq⟩
    subst endpointJobs
    have heventTime_eq_sourceTime : eventTime = sourceTime :=
      (mem_taggedAdmittedFCFSJob_jobsAt_iff start horizon target z eventTime k n).mp
        hendpointJobs.2 |>.2.symm
    subst eventTime
    rfl

/-- In particular, if the interval contains the Palm epoch, the actual
selected request `(target, 0)` appears exactly once in an external endpoint
batch of the pre-terminal execution. -/
theorem taggedAdmittedTargetFCFSJob_appears_once_in_preTerminalExternalEndpointBatches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃! endpointJobs : FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category),
      endpointJobs ∈ taggedAdmittedFiniteGPSExternalEndpointJobBatches
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight initialWork) ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈ endpointJobs.jobs target := by
  apply taggedAdmittedFCFSJob_appears_once_in_preTerminalExternalEndpointBatches
    start horizon target z htarget_good capacity weight initialWork
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hsource_work_nonneg target 0
  exact (mem_taggedAdmittedSourceJobLedger_iff start horizon target z target 0).mp
    ((mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
      ⟨hstart, hhorizon⟩)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
