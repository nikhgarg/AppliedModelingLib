import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Finite FCFS job accounting over concrete GPS segments

`AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace` records finite aggregate GPS service intervals.
This module adds only the deterministic within-class FCFS job ledger needed to
account for that service.  A queue is an ordered finite list: its order is the
FCFS order, while each job's identifier and arrival time remain metadata
separate from its residual work.  The segment itself provides only aggregate
endpoint batch work, so individual endpoint job lists are explicit input here;
they are never recovered from an aggregate batch total.

The update applies a segment's actual stored class-service increment to the
head of each class queue, then appends the supplied endpoint jobs.  Thus an
endpoint arrival cannot receive service in the preceding segment, including an
arrival/depletion tie.  This module is finite and deterministic only.  It does
not construct stochastic arrivals, identify source jobs, prove stationarity or
Palm facts, or derive a response-time tail bound.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- A finite FCFS job keeps its source-level identifier and arrival timestamp
separate from its mutable residual work.  The containing list, rather than the
timestamp alone, fixes the FCFS order and can therefore represent an explicit
tie-breaking order among simultaneous arrivals. -/
structure FiniteGPSFCFSJob (JobId : Type*) where
  identifier : JobId
  arrivalTime : ℝ
  residualWork : ℝ

/-- Total residual work in an ordered finite FCFS queue. -/
def finiteGPSFCFSJobWork
    (jobs : List (FiniteGPSFCFSJob JobId)) : ℝ :=
  (jobs.map fun job => job.residualWork).sum

@[simp]
theorem finiteGPSFCFSJobWork_nil :
    finiteGPSFCFSJobWork (JobId := JobId) [] = 0 := by
  simp [finiteGPSFCFSJobWork]

@[simp]
theorem finiteGPSFCFSJobWork_cons
    (job : FiniteGPSFCFSJob JobId) (jobs : List (FiniteGPSFCFSJob JobId)) :
    finiteGPSFCFSJobWork (job :: jobs) =
      job.residualWork + finiteGPSFCFSJobWork jobs := by
  simp [finiteGPSFCFSJobWork]

@[simp]
theorem finiteGPSFCFSJobWork_append
    (left right : List (FiniteGPSFCFSJob JobId)) :
    finiteGPSFCFSJobWork (left ++ right) =
      finiteGPSFCFSJobWork left + finiteGPSFCFSJobWork right := by
  simp [finiteGPSFCFSJobWork]

/-- Consume a nonnegative amount of class service in FCFS order.  The function
first reduces or completes the current head job, and recurses only after that
head has been fully consumed.  Its behavior is used below only under the
explicit nonnegative-service and no-overservice hypotheses. -/
def finiteGPSFCFSConsume
    (availableService : ℝ) :
    List (FiniteGPSFCFSJob JobId) → List (FiniteGPSFCFSJob JobId)
  | [] => []
  | job :: jobs =>
      if availableService < job.residualWork then
        { job with residualWork := job.residualWork - availableService } :: jobs
      else
        finiteGPSFCFSConsume (availableService - job.residualWork) jobs

/-- In the partial-head branch, FCFS changes only the first job's residual
work and preserves the remaining order verbatim. -/
theorem finiteGPSFCFSConsume_eq_partial_head
    (availableService : ℝ) (job : FiniteGPSFCFSJob JobId)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hpartial : availableService < job.residualWork) :
    finiteGPSFCFSConsume availableService (job :: jobs) =
      { job with residualWork := job.residualWork - availableService } :: jobs := by
  simp [finiteGPSFCFSConsume, hpartial]

/-- In the completion branch, FCFS removes the current head before touching
any later job. -/
theorem finiteGPSFCFSConsume_eq_after_complete_head
    (availableService : ℝ) (job : FiniteGPSFCFSJob JobId)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hcomplete : ¬ availableService < job.residualWork) :
    finiteGPSFCFSConsume availableService (job :: jobs) =
      finiteGPSFCFSConsume (availableService - job.residualWork) jobs := by
  simp [finiteGPSFCFSConsume, hcomplete]

/-- Consuming a nonnegative service budget preserves nonnegative residual work
when every input job has nonnegative residual work. -/
theorem finiteGPSFCFSConsume_residualWork_nonneg
    (availableService : ℝ) (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    ∀ job ∈ finiteGPSFCFSConsume availableService jobs, 0 ≤ job.residualWork := by
  induction jobs generalizing availableService with
  | nil =>
      simp [finiteGPSFCFSConsume]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · intro outputJob hmem
        rw [finiteGPSFCFSConsume_eq_partial_head availableService job jobs hpartial] at hmem
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst outputJob
          exact (sub_nonneg.mpr hpartial.le)
        · exact hjobs_nonneg outputJob (by simp [htail])
      · have hjob_le_service : job.residualWork ≤ availableService :=
          le_of_not_gt hpartial
        have hresidualService_nonneg : 0 ≤ availableService - job.residualWork :=
          sub_nonneg.mpr hjob_le_service
        rw [finiteGPSFCFSConsume_eq_after_complete_head availableService job jobs hpartial]
        apply ih (availableService - job.residualWork) hresidualService_nonneg
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])

/-- FCFS consumption exactly subtracts the supplied service whenever the
service is nonnegative and no larger than the queue's aggregate residual work.
This is the finite conservation law used to couple job accounting to a GPS
workload segment. -/
theorem finiteGPSFCFSConsume_jobWork_eq_sub
    (availableService : ℝ) (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hservice_le_work : availableService ≤ finiteGPSFCFSJobWork jobs) :
    finiteGPSFCFSJobWork (finiteGPSFCFSConsume availableService jobs) =
      finiteGPSFCFSJobWork jobs - availableService := by
  induction jobs generalizing availableService with
  | nil =>
      simp [finiteGPSFCFSConsume, finiteGPSFCFSJobWork] at hservice_le_work ⊢
      linarith
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hpartial : availableService < job.residualWork
      · rw [finiteGPSFCFSConsume_eq_partial_head availableService job jobs hpartial]
        simp only [finiteGPSFCFSJobWork_cons]
        ring
      · have hjob_le_service : job.residualWork ≤ availableService :=
          le_of_not_gt hpartial
        have hresidualService_nonneg : 0 ≤ availableService - job.residualWork :=
          sub_nonneg.mpr hjob_le_service
        have hresidualService_le_tail :
            availableService - job.residualWork ≤ finiteGPSFCFSJobWork jobs := by
          rw [finiteGPSFCFSJobWork_cons] at hservice_le_work
          linarith
        rw [finiteGPSFCFSConsume_eq_after_complete_head availableService job jobs hpartial]
        rw [ih (availableService - job.residualWork) hresidualService_nonneg
          hjobs_tail_nonneg hresidualService_le_tail]
        rw [finiteGPSFCFSJobWork_cons]
        ring

/-- Per-class ordered residual-job queues. -/
structure FiniteGPSFCFSJobLedger (Class JobId : Type*) where
  residualJobs : Class → List (FiniteGPSFCFSJob JobId)

/-- Aggregate residual workload of one class in an FCFS job ledger. -/
def FiniteGPSFCFSJobLedger.classWork
    (ledger : FiniteGPSFCFSJobLedger Class JobId) (i : Class) : ℝ :=
  finiteGPSFCFSJobWork (ledger.residualJobs i)

/-- All residual jobs in the finite ledger have nonnegative work. -/
def FiniteGPSFCFSJobLedger.Nonnegative
    (ledger : FiniteGPSFCFSJobLedger Class JobId) : Prop :=
  ∀ i job, job ∈ ledger.residualJobs i → 0 ≤ job.residualWork

/-- An explicit ordered set of jobs arriving at one segment's right endpoint.
It is deliberately separate from `FiniteGPSExecutionSegment.endpointBatch`:
the latter is aggregate work and carries neither job identifiers nor an FCFS
order within a simultaneous batch. -/
structure FiniteGPSFCFSEndpointJobs (Class JobId : Type*) where
  jobs : Class → List (FiniteGPSFCFSJob JobId)

/-- Aggregate work in one explicit endpoint-job batch. -/
def FiniteGPSFCFSEndpointJobs.classWork
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId) (i : Class) : ℝ :=
  finiteGPSFCFSJobWork (endpointJobs.jobs i)

/-- Every explicitly supplied endpoint job has nonnegative work. -/
def FiniteGPSFCFSEndpointJobs.Nonnegative
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId) : Prop :=
  ∀ i job, job ∈ endpointJobs.jobs i → 0 ≤ job.residualWork

/-- Endpoint job data is aggregate-compatible with a concrete segment when
the sum of its per-class residual works is exactly the segment's stored batch
work.  This says nothing about an execution path; it is only the necessary
bridge from aggregate arrivals to identified finite jobs. -/
def FiniteGPSFCFSEndpointJobs.AggregateCompatible
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (segment : FiniteGPSExecutionSegment Class) : Prop :=
  ∀ i, endpointJobs.classWork i = segment.endpointBatch i

/-- Apply one concrete GPS segment to a job ledger: consume the segment's
stored class service in FCFS order, then append the explicitly supplied jobs
at its endpoint. -/
def finiteGPSFCFSApplySegment
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId) :
    FiniteGPSFCFSJobLedger Class JobId :=
  { residualJobs := fun i =>
      finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i) ++
        endpointJobs.jobs i }

/-- One concrete segment preserves nonnegative residual job work when its
stored service increments are nonnegative and both the preexisting ledger and
the explicit endpoint jobs are nonnegative. -/
theorem finiteGPSFCFSApplySegment_nonnegative
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (hledger_nonneg : ledger.Nonnegative)
    (hservice_nonneg : ∀ i, 0 ≤ segment.serviceIncrement i)
    (hendpoint_nonneg : endpointJobs.Nonnegative) :
    (finiteGPSFCFSApplySegment ledger segment endpointJobs).Nonnegative := by
  intro i outputJob hmem
  simp only [finiteGPSFCFSApplySegment] at hmem
  rcases List.mem_append.mp hmem with hserved | hendpoint
  · exact finiteGPSFCFSConsume_residualWork_nonneg
      (segment.serviceIncrement i) (ledger.residualJobs i) (hservice_nonneg i)
      (by
        intro job hjob
        exact hledger_nonneg i job hjob) outputJob hserved
  · exact hendpoint_nonneg i outputJob hendpoint

/-- Aggregate residual work after one FCFS segment update is the old class
work minus the segment's actual service plus the explicitly identified
endpoint-job work. -/
theorem finiteGPSFCFSApplySegment_classWork
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (i : Class)
    (hledger_nonneg : ledger.Nonnegative)
    (hservice_nonneg : 0 ≤ segment.serviceIncrement i)
    (hservice_le_ledger_work : segment.serviceIncrement i ≤ ledger.classWork i) :
    (finiteGPSFCFSApplySegment ledger segment endpointJobs).classWork i =
      ledger.classWork i - segment.serviceIncrement i + endpointJobs.classWork i := by
  have hconsume :
      finiteGPSFCFSJobWork
        (finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i)) =
        finiteGPSFCFSJobWork (ledger.residualJobs i) - segment.serviceIncrement i :=
    finiteGPSFCFSConsume_jobWork_eq_sub (segment.serviceIncrement i)
      (ledger.residualJobs i) hservice_nonneg
      (by
        intro job hjob
        exact hledger_nonneg i job hjob)
      hservice_le_ledger_work
  unfold FiniteGPSFCFSJobLedger.classWork FiniteGPSFCFSEndpointJobs.classWork
    finiteGPSFCFSApplySegment
  rw [finiteGPSFCFSJobWork_append, hconsume]

/-- If a ledger represents the segment's left workload and the explicit
endpoint-job list has exactly the segment's aggregate endpoint work, the FCFS
update represents its concrete post-endpoint workload.  The balance premise is
kept explicit because `FiniteGPSExecutionSegment` is a data structure; the
next theorem instantiates it for the actual kernel constructor. -/
theorem finiteGPSFCFSApplySegment_classWork_eq_endpointWorkload
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (i : Class)
    (hledger_nonneg : ledger.Nonnegative)
    (hservice_nonneg : 0 ≤ segment.serviceIncrement i)
    (hservice_le_ledger_work : segment.serviceIncrement i ≤ ledger.classWork i)
    (hledger_matches_start : ledger.classWork i = segment.startWorkload i)
    (hendpoint_compatible : endpointJobs.AggregateCompatible segment)
    (hsegment_balance :
      segment.endpointWorkload i =
        segment.startWorkload i + segment.endpointBatch i -
          segment.serviceIncrement i) :
    (finiteGPSFCFSApplySegment ledger segment endpointJobs).classWork i =
      segment.endpointWorkload i := by
  rw [finiteGPSFCFSApplySegment_classWork ledger segment endpointJobs i
    hledger_nonneg hservice_nonneg hservice_le_ledger_work,
    hledger_matches_start, hendpoint_compatible i]
  linarith

/-- A concrete kernel segment never records more class service than the
left-endpoint class workload. -/
theorem finiteGPSBuildExecutionSegment_serviceIncrement_le_startWorkload
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) (i : Class) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).serviceIncrement i ≤
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).startWorkload i := by
  change finiteGPSServiceIncrement capacity weight work
      (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i ≤ work i
  unfold finiteGPSServiceIncrement
  exact sub_le_self _ (le_max_left _ _)

/-- Under the ordinary finite GPS assumptions, the concrete kernel's stored
service increment is nonnegative. -/
theorem finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    0 ≤ (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).serviceIncrement i := by
  have hrate_nonneg : 0 ≤ finiteGPSClassRate capacity weight work i := by
    by_cases hactive : 0 < work i
    · exact (finiteGPSClassRate_pos_of_active hcapacity hweight_pos
        htotal_weight_le_one hactive).le
    · rw [finiteGPSClassRate_eq_zero_of_not_active hactive]
  rw [finiteGPSBuildExecutionSegment_serviceIncrement,
    finiteGPSServiceIncrement_eq_rate_mul_nextStep hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg]
  exact mul_nonneg hrate_nonneg
    (finiteGPSNextStepDuration_nonneg hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg)

/-- Specialization of finite FCFS conservation to an actual kernel segment.
This is the source-independent bridge needed by a later stochastic adapter:
given an initial ordered job ledger whose aggregate class work is `work`, and
an explicit endpoint job batch whose aggregate matches `batchWork`, the FCFS
ledger exactly realizes the kernel's post-batch workload vector. -/
theorem finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ)
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hledger_nonneg : ledger.Nonnegative)
    (hledger_matches_work : ∀ i, ledger.classWork i = work i)
    (hendpoint_compatible : endpointJobs.AggregateCompatible
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay)) :
    ∀ i,
      (finiteGPSFCFSApplySegment ledger
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay) endpointJobs).classWork i =
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).endpointWorkload i := by
  intro i
  apply finiteGPSFCFSApplySegment_classWork_eq_endpointWorkload
    ledger (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay) endpointJobs i hledger_nonneg
  · exact finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hnextBatchDelay_nonneg
  · rw [hledger_matches_work i]
    exact finiteGPSBuildExecutionSegment_serviceIncrement_le_startWorkload
      capacity weight work batchWork startTime nextBatchDelay i
  · exact hledger_matches_work i
  · exact hendpoint_compatible
  · exact finiteGPSBuildExecutionSegment_balance capacity weight work batchWork
      startTime nextBatchDelay i

/-- Job-level input for one concrete GPS segment.  The segment is retained as
data and determines the service; `endpointJobs` contributes only the missing
individual job decomposition of its aggregate endpoint batch. -/
structure FiniteGPSFCFSSegmentJobStep (Class JobId : Type*) where
  segment : FiniteGPSExecutionSegment Class
  endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId

/-- Run finite FCFS accounting over the supplied concrete segment list.  This
is a fixed fold, not a caller-supplied queue-transition relation. -/
def finiteGPSFCFSRunSegmentSteps
    (initial : FiniteGPSFCFSJobLedger Class JobId) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) →
      FiniteGPSFCFSJobLedger Class JobId
  | [] => initial
  | step :: steps =>
      finiteGPSFCFSRunSegmentSteps
        (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) steps

/-- The post-endpoint workload vector of the last emitted segment in a finite
step list.  For an empty list it is the supplied initial vector.  This names
only the endpoint of the emitted list; it makes no claim about an external
horizon or a stationary continuation. -/
def finiteGPSFCFSSegmentStepsEndpointWorkload
    (initialWorkload : Class → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) → Class → ℝ
  | [] => initialWorkload
  | step :: steps =>
      finiteGPSFCFSSegmentStepsEndpointWorkload step.segment.endpointWorkload steps

/-- Total class service recorded by an emitted finite segment list.  This is a
ledger of the service increments actually stored in those segments, rather
than a claim about service after their last endpoint. -/
def finiteGPSFCFSSegmentStepsTotalService :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) → Class → ℝ
  | [] => fun _ => 0
  | step :: steps =>
      fun i => step.segment.serviceIncrement i +
        finiteGPSFCFSSegmentStepsTotalService steps i

/-- Total aggregate endpoint-batch work represented by an emitted finite
segment list.  The identity below proves that it agrees with the explicit job
batch totals under aggregate compatibility. -/
def finiteGPSFCFSSegmentStepsTotalEndpointBatchWork :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) → Class → ℝ
  | [] => fun _ => 0
  | step :: steps =>
      fun i => step.segment.endpointBatch i +
        finiteGPSFCFSSegmentStepsTotalEndpointBatchWork steps i

/-- The finite job-accounting output together with the final endpoint
workload of the emitted segment list and its recorded total service. -/
structure FiniteGPSFCFSRunSegmentSummary (Class JobId : Type*) where
  finalLedger : FiniteGPSFCFSJobLedger Class JobId
  finalEndpointWorkload : Class → ℝ
  totalService : Class → ℝ

/-- Compute the finite FCFS fold summary directly from concrete segment/job
steps. -/
def finiteGPSFCFSRunSegmentStepsSummary
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    FiniteGPSFCFSRunSegmentSummary Class JobId :=
  { finalLedger := finiteGPSFCFSRunSegmentSteps initial steps
    finalEndpointWorkload := finiteGPSFCFSSegmentStepsEndpointWorkload
      initialWorkload steps
    totalService := finiteGPSFCFSSegmentStepsTotalService steps }

/-- Recursive finite compatibility invariant for the concrete FCFS fold.
It is a verification condition, not an alternate execution definition: every
next ledger in the recursion is computed by `finiteGPSFCFSApplySegment`.
Besides the initial/start and endpoint-balance identities, it requires only
the explicit endpoint job decomposition and the no-overservice facts needed
for finite FCFS conservation. -/
def FiniteGPSFCFSRunSegmentStepsCompatible
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) → Prop
  | [] => ∀ i, initial.classWork i = initialWorkload i
  | step :: steps =>
      (∀ i, initial.classWork i = initialWorkload i) ∧
        (∀ i, initialWorkload i = step.segment.startWorkload i) ∧
        step.endpointJobs.AggregateCompatible step.segment ∧
        step.endpointJobs.Nonnegative ∧
        (∀ i, 0 ≤ step.segment.serviceIncrement i) ∧
        (∀ i, step.segment.serviceIncrement i ≤ initial.classWork i) ∧
        (∀ i, step.segment.endpointWorkload i =
          step.segment.startWorkload i + step.segment.endpointBatch i -
            step.segment.serviceIncrement i) ∧
        FiniteGPSFCFSRunSegmentStepsCompatible
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          step.segment.endpointWorkload steps

/-- Every concrete step of a compatible FCFS trace carries endpoint jobs
whose aggregate work agrees with the stored executable segment batch.  This
is an extractor for the recursive compatibility certificate, not a new
scheduler assumption; it is useful whenever semantic source provenance shows
that one class's endpoint-job list is empty. -/
theorem finiteGPSFCFSRunSegmentStepsCompatible_endpointJobs_aggregateCompatible
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    ∀ step ∈ steps, step.endpointJobs.AggregateCompatible step.segment := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simp
  | cons head tail ih =>
      rcases hcompatible with ⟨_hinitial, _hstart, hhead, _hendpoint,
        _hservice, _hservice_le, _hbalance, htail⟩
      intro step hstep
      rcases List.mem_cons.mp hstep with hstep | hstep
      · subst step
        exact hhead
      · exact ih
          (initial := finiteGPSFCFSApplySegment initial head.segment head.endpointJobs)
          (initialWorkload := head.segment.endpointWorkload) htail step hstep

/-- The recursive FCFS compatibility certificate composes at a concrete
step-list boundary.  The right certificate starts from the ledger and
endpoint workload actually produced by the left fold; no jobs or workload
are reconstructed at the boundary. -/
theorem finiteGPSFCFSRunSegmentStepsCompatible_append
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
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
      rcases hleft with ⟨hinitial, hstart, hbatch, hendpoint, hservice,
        hservice_le, hbalance, htail⟩
      refine ⟨hinitial, hstart, hbatch, hendpoint, hservice, hservice_le,
        hbalance, ?_⟩
      apply ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        (initialWorkload := step.segment.endpointWorkload)
        htail
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using hright

/-- A compatible concatenated trace restricts to its literal left prefix. -/
theorem finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload
      (left ++ right)) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload left := by
  induction left generalizing initial initialWorkload with
  | nil =>
      cases right with
      | nil =>
          simpa [FiniteGPSFCFSRunSegmentStepsCompatible] using hcompatible
      | cons step right =>
          exact hcompatible.1
  | cons step left ih =>
      rcases hcompatible with ⟨hinitial, hstart, hbatch, hendpoint, hservice,
        hservice_le, hbalance, htail⟩
      refine ⟨hinitial, hstart, hbatch, hendpoint, hservice, hservice_le,
        hbalance, ?_⟩
      exact ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        (initialWorkload := step.segment.endpointWorkload) htail

/-- A compatible concatenated trace restricts to its literal right suffix,
started from the ledger and endpoint workload computed by the left fold. -/
theorem finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload
      (left ++ right)) :
    FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps initial left)
      (finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload left) right := by
  induction left generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using hcompatible
  | cons step left ih =>
      rcases hcompatible with ⟨_hinitial, _hstart, _hbatch, _hendpoint,
        _hservice, _hservice_le, _hbalance, htail⟩
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using
        ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload) htail

/-- A concrete compatible FCFS fold preserves nonnegative residual jobs from
a nonnegative initial ledger. -/
theorem finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    (finiteGPSFCFSRunSegmentSteps initial steps).Nonnegative := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial_nonneg
  | cons step steps ih =>
      rcases hcompatible with ⟨_hinitial, _hstart, _hbatch, hendpoint,
        hservice, _hservice_le, _hbalance, htail⟩
      have hnext_nonneg :
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
        finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
          hinitial_nonneg hservice hendpoint
      simpa [finiteGPSFCFSRunSegmentSteps] using
        ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload) hnext_nonneg htail
/-- Service records add under concatenation of finite emitted step lists. -/
theorem finiteGPSFCFSSegmentStepsTotalService_append
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) (i : Class) :
    finiteGPSFCFSSegmentStepsTotalService (left ++ right) i =
      finiteGPSFCFSSegmentStepsTotalService left i +
        finiteGPSFCFSSegmentStepsTotalService right i := by
  induction left with
  | nil => simp [finiteGPSFCFSSegmentStepsTotalService]
  | cons step left ih =>
      simp [finiteGPSFCFSSegmentStepsTotalService, ih]
      ring

/-- Endpoint-batch work records add under concatenation of finite emitted
step lists. -/
theorem finiteGPSFCFSSegmentStepsTotalEndpointBatchWork_append
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) (i : Class) :
    finiteGPSFCFSSegmentStepsTotalEndpointBatchWork (left ++ right) i =
      finiteGPSFCFSSegmentStepsTotalEndpointBatchWork left i +
        finiteGPSFCFSSegmentStepsTotalEndpointBatchWork right i := by
  induction left with
  | nil => simp [finiteGPSFCFSSegmentStepsTotalEndpointBatchWork]
  | cons step left ih =>
      simp [finiteGPSFCFSSegmentStepsTotalEndpointBatchWork, ih]
      ring

/-- Under the finite compatibility invariant, the computed FCFS ledger's
class aggregates exactly equal the endpoint workload of the concrete emitted
GPS segment list. -/
theorem finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible :
      FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial steps).classWork i =
        finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload steps i := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using hcompatible
  | cons step steps ih =>
      rcases hcompatible with ⟨hledger_initial, hinitial_start,
        hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        hservice_le_ledger, hsegment_balance, htail⟩
      have hnext_nonneg :
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
        finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
          hinitial_nonneg hservice_nonneg hendpoint_nonneg
      have hstep_matches : ∀ i,
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).classWork i =
            step.segment.endpointWorkload i := by
        intro i
        apply finiteGPSFCFSApplySegment_classWork_eq_endpointWorkload
          initial step.segment step.endpointJobs i hinitial_nonneg
            (hservice_nonneg i) (hservice_le_ledger i)
        · calc
            initial.classWork i = initialWorkload i := hledger_initial i
            _ = step.segment.startWorkload i := hinitial_start i
        · exact hbatch_compatible
        · exact hsegment_balance i
      have htail_matches := ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        (initialWorkload := step.segment.endpointWorkload)
        hnext_nonneg htail
      simpa [finiteGPSFCFSRunSegmentSteps,
        finiteGPSFCFSSegmentStepsEndpointWorkload] using htail_matches

/-- The concrete endpoint workload of a compatible emitted segment list has
the global finite workload conservation identity: initial work plus its
recorded endpoint batches minus its recorded actual service. -/
theorem finiteGPSFCFSSegmentStepsEndpointWorkload_conservation
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcompatible :
      FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    ∀ i,
      finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload steps i =
        initialWorkload i +
          finiteGPSFCFSSegmentStepsTotalEndpointBatchWork steps i -
          finiteGPSFCFSSegmentStepsTotalService steps i := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload,
        finiteGPSFCFSSegmentStepsTotalEndpointBatchWork,
        finiteGPSFCFSSegmentStepsTotalService]
  | cons step steps ih =>
      rcases hcompatible with ⟨hledger_initial, hinitial_start,
        hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        hservice_le_ledger, hsegment_balance, htail⟩
      have htail_conservation := ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        (initialWorkload := step.segment.endpointWorkload) htail
      intro i
      change finiteGPSFCFSSegmentStepsEndpointWorkload
          step.segment.endpointWorkload steps i =
        initialWorkload i +
          (step.segment.endpointBatch i +
            finiteGPSFCFSSegmentStepsTotalEndpointBatchWork steps i) -
          (step.segment.serviceIncrement i +
            finiteGPSFCFSSegmentStepsTotalService steps i)
      rw [htail_conservation i, hsegment_balance i]
      rw [← hinitial_start i]
      ring

/-- The summary exposes the fixed FCFS fold, the final emitted endpoint, and
the exact total service record without adding any post-list continuation. -/
theorem finiteGPSFCFSRunSegmentStepsSummary_classWork_eq_endpointWorkload
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible :
      FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps) :
    ∀ i,
      (finiteGPSFCFSRunSegmentStepsSummary initial initialWorkload steps).finalLedger.classWork i =
        (finiteGPSFCFSRunSegmentStepsSummary initial initialWorkload steps).finalEndpointWorkload i := by
  exact finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
    initial initialWorkload steps hinitial_nonneg hcompatible

end

end AppliedModelingLib.Probability.Queueing
