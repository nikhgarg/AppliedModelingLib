import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import Mathlib.Tactic

/-!
# Completed-job ledgers for finite GPS/FCFS segments

`AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS` applies a finite class-service increment in head-first
FCFS order, but its residual queue alone does not expose which individual jobs
finished during that interval.  This module records that finite completion
prefix.  Each record retains the source job identifier and arrival metadata,
the completed work, and the offset/time implied by a constant positive class
rate.

The underlying consumer is still the existing `finiteGPSFCFSConsume`.  This
module does not alter it or introduce a second queue transition.  Completion
records are generated solely from the pre-segment ordered queue and the
segment's stored service increment.  Endpoint jobs therefore remain outside
the preceding interval: they are appended only by
`finiteGPSFCFSApplySegment` after consumption.

The construction is finite and deterministic.  It makes no stochastic,
stationary, Palm, or response-tail claim.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- One FCFS job completed during a finite constant-rate service segment.  The
`completionOffset` is measured from the segment's start.  Its interpretation
as elapsed time uses a positive `classRate`, made explicit by the theorems
below. -/
structure FiniteGPSFCFSCompletion (JobId : Type*) where
  identifier : JobId
  arrivalTime : ℝ
  completedWork : ℝ
  completionOffset : ℝ
  completionTime : ℝ

/-- Turn a fully consumed FCFS job into its completion record.  `serviceBefore`
is the work already delivered to earlier FCFS jobs in the same segment. -/
def finiteGPSFCFSCompletionOf
    (segmentStart classRate serviceBefore : ℝ)
    (job : FiniteGPSFCFSJob JobId) :
    FiniteGPSFCFSCompletion JobId :=
  { identifier := job.identifier
    arrivalTime := job.arrivalTime
    completedWork := job.residualWork
    completionOffset := (serviceBefore + job.residualWork) / classRate
    completionTime := segmentStart + (serviceBefore + job.residualWork) / classRate }

@[simp]
theorem finiteGPSFCFSCompletionOf_identifier
    (segmentStart classRate serviceBefore : ℝ)
    (job : FiniteGPSFCFSJob JobId) :
    (finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job).identifier =
      job.identifier := rfl

@[simp]
theorem finiteGPSFCFSCompletionOf_arrivalTime
    (segmentStart classRate serviceBefore : ℝ)
    (job : FiniteGPSFCFSJob JobId) :
    (finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job).arrivalTime =
      job.arrivalTime := rfl

@[simp]
theorem finiteGPSFCFSCompletionOf_completedWork
    (segmentStart classRate serviceBefore : ℝ)
    (job : FiniteGPSFCFSJob JobId) :
    (finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job).completedWork =
      job.residualWork := rfl

@[simp]
theorem finiteGPSFCFSCompletionOf_completionTime
    (segmentStart classRate serviceBefore : ℝ)
    (job : FiniteGPSFCFSJob JobId) :
    (finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job).completionTime =
      segmentStart +
        (finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job).completionOffset := rfl

/-- The completed head prefix after consuming `availableService`.  The helper
carries the service already assigned to earlier jobs so that each completion
receives its actual within-segment offset. -/
def finiteGPSFCFSCompletedJobsFrom
    (segmentStart classRate serviceBefore availableService : ℝ) :
    List (FiniteGPSFCFSJob JobId) → List (FiniteGPSFCFSCompletion JobId)
  | [] => []
  | job :: jobs =>
      if availableService < job.residualWork then
        []
      else
        finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job ::
          finiteGPSFCFSCompletedJobsFrom segmentStart classRate
            (serviceBefore + job.residualWork)
            (availableService - job.residualWork) jobs

/-- Completed FCFS jobs from the start of one finite service segment. -/
def finiteGPSFCFSCompletedJobs
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    List (FiniteGPSFCFSCompletion JobId) :=
  finiteGPSFCFSCompletedJobsFrom segmentStart classRate 0 availableService jobs

/-- Completed jobs of one class in a concrete finite GPS segment.  The input
list is the pre-segment FCFS queue; endpoint jobs are intentionally absent. -/
def finiteGPSFCFSCompletedJobsInSegment
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    List (FiniteGPSFCFSCompletion JobId) :=
  finiteGPSFCFSCompletedJobs segment.startTime (segment.classRate i)
    (segment.serviceIncrement i) jobs

/-- Completed jobs for every class of a pre-segment FCFS ledger. -/
def finiteGPSFCFSCompletedJobsForLedgerSegment
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class) :
    Class → List (FiniteGPSFCFSCompletion JobId) :=
  fun i => finiteGPSFCFSCompletedJobsInSegment segment i (ledger.residualJobs i)

@[simp]
theorem finiteGPSFCFSCompletedJobsFrom_nil
    (segmentStart classRate serviceBefore availableService : ℝ) :
    finiteGPSFCFSCompletedJobsFrom (JobId := JobId)
      segmentStart classRate serviceBefore availableService [] = [] := rfl

/-- If the available service stops strictly inside the current head, there is
no completed job at or after that head. -/
theorem finiteGPSFCFSCompletedJobsFrom_eq_nil_of_partial_head
    (segmentStart classRate serviceBefore availableService : ℝ)
    (job : FiniteGPSFCFSJob JobId) (jobs : List (FiniteGPSFCFSJob JobId))
    (hpartial : availableService < job.residualWork) :
    finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
      availableService (job :: jobs) = [] := by
  simp [finiteGPSFCFSCompletedJobsFrom, hpartial]

/-- If the current head is fully consumed, it is recorded before any later
FCFS job is inspected. -/
theorem finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
    (segmentStart classRate serviceBefore availableService : ℝ)
    (job : FiniteGPSFCFSJob JobId) (jobs : List (FiniteGPSFCFSJob JobId))
    (hcomplete : ¬ availableService < job.residualWork) :
    finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
      availableService (job :: jobs) =
      finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job ::
        finiteGPSFCFSCompletedJobsFrom segmentStart classRate
          (serviceBefore + job.residualWork)
          (availableService - job.residualWork) jobs := by
  simp [finiteGPSFCFSCompletedJobsFrom, hcomplete]

/-- The total original work represented by a finite completion list. -/
def finiteGPSFCFSCompletionWork
    (completions : List (FiniteGPSFCFSCompletion JobId)) : ℝ :=
  (completions.map fun completion => completion.completedWork).sum

@[simp]
theorem finiteGPSFCFSCompletionWork_nil :
    finiteGPSFCFSCompletionWork (JobId := JobId) [] = 0 := by
  simp [finiteGPSFCFSCompletionWork]

@[simp]
theorem finiteGPSFCFSCompletionWork_cons
    (completion : FiniteGPSFCFSCompletion JobId)
    (completions : List (FiniteGPSFCFSCompletion JobId)) :
    finiteGPSFCFSCompletionWork (completion :: completions) =
      completion.completedWork + finiteGPSFCFSCompletionWork completions := by
  simp [finiteGPSFCFSCompletionWork]

/-- Identifiers in an ordered FCFS completion prefix. -/
def finiteGPSFCFSCompletionIdentifiers
    (completions : List (FiniteGPSFCFSCompletion JobId)) : List JobId :=
  completions.map fun completion => completion.identifier

/-- Identifiers in an ordered FCFS job queue. -/
def finiteGPSFCFSJobIdentifiers
    (jobs : List (FiniteGPSFCFSJob JobId)) : List JobId :=
  jobs.map fun job => job.identifier

/-- The completion identifiers form an initial prefix of the input FCFS queue,
with `remaining` the uncompleted source suffix.  This deliberately uses a
source-job suffix rather than equality of residual queues, because the current
head may have been partially served. -/
def FiniteGPSFCFSCompletionHeadOrder
    (completions : List (FiniteGPSFCFSCompletion JobId))
    (jobs : List (FiniteGPSFCFSJob JobId)) : Prop :=
  ∃ remaining : List (FiniteGPSFCFSJob JobId),
    finiteGPSFCFSJobIdentifiers jobs =
      finiteGPSFCFSCompletionIdentifiers completions ++
        finiteGPSFCFSJobIdentifiers remaining

/-- Completion records preserve head-first FCFS order.  No work, rate, or
positivity hypothesis is needed for this structural fact. -/
theorem finiteGPSFCFSCompletedJobsFrom_head_order
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    FiniteGPSFCFSCompletionHeadOrder
      (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
        availableService jobs) jobs := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      refine ⟨[], ?_⟩
      simp [finiteGPSFCFSCompletedJobsFrom, finiteGPSFCFSCompletionIdentifiers,
        finiteGPSFCFSJobIdentifiers]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · refine ⟨job :: jobs, ?_⟩
        simp [finiteGPSFCFSCompletedJobsFrom, hpartial,
          finiteGPSFCFSCompletionIdentifiers, finiteGPSFCFSJobIdentifiers]
      · rcases ih (serviceBefore := serviceBefore + job.residualWork)
          (availableService := availableService - job.residualWork) with
          ⟨remaining, hremaining⟩
        refine ⟨remaining, ?_⟩
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial]
        simpa [finiteGPSFCFSCompletionIdentifiers, finiteGPSFCFSJobIdentifiers,
          finiteGPSFCFSCompletionOf] using
          congrArg (fun identifiers : List JobId => job.identifier :: identifiers) hremaining

/-- Completion records preserve head-first order from the segment start. -/
theorem finiteGPSFCFSCompletedJobs_head_order
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    FiniteGPSFCFSCompletionHeadOrder
      (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs) jobs := by
  simpa [finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_head_order (JobId := JobId)
      segmentStart classRate 0 availableService jobs)

/-- The segment view preserves head-first FCFS order for each class. -/
theorem finiteGPSFCFSCompletedJobsInSegment_head_order
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    FiniteGPSFCFSCompletionHeadOrder
      (finiteGPSFCFSCompletedJobsInSegment segment i jobs) jobs := by
  simpa [finiteGPSFCFSCompletedJobsInSegment] using
    (finiteGPSFCFSCompletedJobs_head_order (JobId := JobId)
      segment.startTime (segment.classRate i) (segment.serviceIncrement i) jobs)

/-- Every emitted completion record has its advertised absolute completion
time.  This is an exact definition-level relation; positivity of the rate is
needed only for its physical elapsed-time interpretation. -/
theorem finiteGPSFCFSCompletedJobsFrom_completionTime_eq_start_add_offset
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segmentStart classRate
      serviceBefore availableService jobs,
      completion.completionTime = segmentStart + completion.completionOffset := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial]
      · intro completion hcompletion
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial] at hcompletion
        rcases List.mem_cons.mp hcompletion with hhead | htail
        · subst completion
          exact finiteGPSFCFSCompletionOf_completionTime
            segmentStart classRate serviceBefore job
        · exact ih (serviceBefore := serviceBefore + job.residualWork)
            (availableService := availableService - job.residualWork) completion htail

/-- Every segment completion record satisfies its start-plus-offset timestamp
identity. -/
theorem finiteGPSFCFSCompletedJobsInSegment_completionTime_eq_start_add_offset
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      completion.completionTime = segment.startTime + completion.completionOffset := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_completionTime_eq_start_add_offset
      (JobId := JobId) segment.startTime (segment.classRate i) 0
      (segment.serviceIncrement i) jobs)

/-- A completion emitted by the finite FCFS accounting lies no later than
the service budget that generated that completed prefix.  The statement is
purely local to one constant-rate service interval; no queueing or source
model is assumed. -/
theorem finiteGPSFCFSCompletedJobsFrom_completionTime_le_start_add_serviceBudget_div
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segmentStart classRate
      serviceBefore availableService jobs,
      completion.completionTime ≤
        segmentStart + (serviceBefore + availableService) / classRate := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial]
      · intro completion hcompletion
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial] at hcompletion
        rcases List.mem_cons.mp hcompletion with hhead | htail
        · subst completion
          change segmentStart + (serviceBefore + job.residualWork) / classRate ≤
            segmentStart + (serviceBefore + availableService) / classRate
          have hdiv : (serviceBefore + job.residualWork) / classRate ≤
              (serviceBefore + availableService) / classRate := by
            apply div_le_div_of_nonneg_right
            · linarith [le_of_not_gt hpartial]
            · exact hclassRate_pos.le
          simpa [add_comm] using add_le_add_left hdiv segmentStart
        · have htail_bound := ih
            (serviceBefore := serviceBefore + job.residualWork)
            (availableService := availableService - job.residualWork)
            completion htail
          convert htail_bound using 1
          ring

/-- If an executable segment stores service as its positive class rate times
its duration, every FCFS completion emitted from that segment occurs by the
segment's concrete right endpoint. -/
theorem finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < segment.classRate i)
    (hservice_eq_rate_mul_duration :
      segment.serviceIncrement i = segment.classRate i * segment.duration) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      completion.completionTime ≤ finiteGPSExecutionSegmentEndTime segment := by
  intro completion hcompletion
  have hbudget := finiteGPSFCFSCompletedJobsFrom_completionTime_le_start_add_serviceBudget_div
    (JobId := JobId) segment.startTime (segment.classRate i) 0
    (segment.serviceIncrement i) jobs hclassRate_pos completion hcompletion
  calc
    completion.completionTime ≤
        segment.startTime + (0 + segment.serviceIncrement i) / segment.classRate i := hbudget
    _ = finiteGPSExecutionSegmentEndTime segment := by
      rw [hservice_eq_rate_mul_duration]
      unfold finiteGPSExecutionSegmentEndTime
      field_simp [ne_of_gt hclassRate_pos]
      ring

/-- Strict positivity of every queued job.  This is stronger than the ordinary
nonnegative-work invariant and is exactly what rules out zero-work jobs being
silently emitted as completions when the available service is zero. -/
def finiteGPSFCFSJobsStrictlyPositive
    (jobs : List (FiniteGPSFCFSJob JobId)) : Prop :=
  ∀ job ∈ jobs, 0 < job.residualWork

/-- With positive residual work, zero service produces no completion records.
The positivity premise is necessary because the underlying FCFS consumer treats
a zero-work head as already complete. -/
theorem finiteGPSFCFSCompletedJobsFrom_eq_nil_of_zero_service
    (segmentStart classRate serviceBefore : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hjobs_pos : finiteGPSFCFSJobsStrictlyPositive jobs) :
    finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore 0 jobs = [] := by
  cases jobs with
  | nil => rfl
  | cons job jobs =>
      have hjob_pos : 0 < job.residualWork := hjobs_pos job (by simp)
      simp [finiteGPSFCFSCompletedJobsFrom, hjob_pos]

/-- With positive residual work, zero segment service produces no completions.
No positive-rate assumption is needed for this no-service fact. -/
theorem finiteGPSFCFSCompletedJobsInSegment_eq_nil_of_zero_service
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hjobs_pos : finiteGPSFCFSJobsStrictlyPositive jobs)
    (hservice_zero : segment.serviceIncrement i = 0) :
    finiteGPSFCFSCompletedJobsInSegment segment i jobs = [] := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
    hservice_zero] using
    (finiteGPSFCFSCompletedJobsFrom_eq_nil_of_zero_service
      (JobId := JobId) segment.startTime (segment.classRate i) 0 jobs hjobs_pos)

/-- The total work of completed jobs never exceeds the nonnegative service
budget.  This makes the residual `availableService - completionWork` an
explicit nonnegative amount of service that may have gone to a partially
served head job. -/
theorem finiteGPSFCFSCompletionWork_le_availableService_from
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionWork
      (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
        availableService jobs) ≤ availableService := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom, hservice_nonneg]
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial, hservice_nonneg]
      · have hjob_le_service : job.residualWork ≤ availableService :=
          le_of_not_gt hpartial
        have hresidual_service_nonneg :
            0 ≤ availableService - job.residualWork :=
          sub_nonneg.mpr hjob_le_service
        have htail := ih
          (serviceBefore := serviceBefore + job.residualWork)
          (availableService := availableService - job.residualWork)
          hresidual_service_nonneg hjobs_tail_nonneg
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial]
        simp only [finiteGPSFCFSCompletionWork_cons,
          finiteGPSFCFSCompletionOf_completedWork]
        linarith

/-- The total work of completed jobs never exceeds the nonnegative service
increment from the segment start. -/
theorem finiteGPSFCFSCompletionWork_le_availableService
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionWork
      (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs) ≤
        availableService := by
  simpa [finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletionWork_le_availableService_from
      (JobId := JobId) segmentStart classRate 0 availableService jobs
      hservice_nonneg hjobs_nonneg)

/-- Finite FCFS accounting conserves all pre-segment work: completed job work,
residual queue work, and the explicitly identified partial-head service sum to
the original queue work.  The no-overservice premise is the same one required
by the existing FCFS consumer conservation theorem. -/
theorem finiteGPSFCFSCompletedJobs_conservation
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hservice_le_work : availableService ≤ finiteGPSFCFSJobWork jobs) :
    finiteGPSFCFSCompletionWork
        (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs) +
      finiteGPSFCFSJobWork (finiteGPSFCFSConsume availableService jobs) +
      (availableService - finiteGPSFCFSCompletionWork
        (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs)) =
        finiteGPSFCFSJobWork jobs := by
  have hremaining := finiteGPSFCFSConsume_jobWork_eq_sub
    (JobId := JobId) availableService jobs hservice_nonneg hjobs_nonneg
      hservice_le_work
  rw [hremaining]
  ring

/-- The service not represented by fully completed jobs is nonnegative under
the ordinary nonnegative-work and nonnegative-service conditions. -/
theorem finiteGPSFCFSCompletedJobs_partialService_nonneg
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    0 ≤ availableService - finiteGPSFCFSCompletionWork
      (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs) := by
  exact sub_nonneg.mpr
    (finiteGPSFCFSCompletionWork_le_availableService (JobId := JobId)
      segmentStart classRate availableService jobs hservice_nonneg hjobs_nonneg)

/-- If the service budget is exactly the positive head work, and all later
jobs have positive residual work, precisely that head completes. -/
theorem finiteGPSFCFSCompletedJobs_eq_singleton_of_service_eq_headWork
    (segmentStart classRate availableService : ℝ)
    (job : FiniteGPSFCFSJob JobId) (jobs : List (FiniteGPSFCFSJob JobId))
    (hservice_eq_headWork : availableService = job.residualWork)
    (htail_pos : finiteGPSFCFSJobsStrictlyPositive jobs) :
    finiteGPSFCFSCompletedJobs segmentStart classRate availableService (job :: jobs) =
      [finiteGPSFCFSCompletionOf segmentStart classRate 0 job] := by
  have hcomplete : ¬ availableService < job.residualWork := by
    rw [hservice_eq_headWork]
    exact lt_irrefl _
  unfold finiteGPSFCFSCompletedJobs
  rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
    segmentStart classRate 0 availableService job jobs hcomplete]
  have htail_zero : availableService - job.residualWork = 0 := by
    rw [hservice_eq_headWork]
    ring
  simp only [zero_add]
  rw [htail_zero]
  rw [finiteGPSFCFSCompletedJobsFrom_eq_nil_of_zero_service
    segmentStart classRate job.residualWork jobs htail_pos]

/-- A positive-rate, positive-duration segment whose service is exactly its
head job's work records that job as completing at the right endpoint.  This
includes a completion/external-arrival tie: only the pre-segment head appears
here, while endpoint arrivals are appended later by the existing FCFS update. -/
theorem finiteGPSFCFSCompletedJobsInSegment_eq_singleton_at_endpoint
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (job : FiniteGPSFCFSJob JobId) (jobs : List (FiniteGPSFCFSJob JobId))
    (hrate_pos : 0 < segment.classRate i)
    (hduration_pos : 0 < segment.duration)
    (hservice_eq_rate_duration :
      segment.serviceIncrement i = segment.classRate i * segment.duration)
    (hhead_work_eq_service : job.residualWork = segment.serviceIncrement i)
    (htail_pos : finiteGPSFCFSJobsStrictlyPositive jobs) :
    finiteGPSFCFSCompletedJobsInSegment segment i (job :: jobs) =
      [finiteGPSFCFSCompletionOf segment.startTime (segment.classRate i) 0 job] ∧
      (finiteGPSFCFSCompletionOf segment.startTime (segment.classRate i) 0 job).completionOffset =
        segment.duration ∧
      (finiteGPSFCFSCompletionOf segment.startTime (segment.classRate i) 0 job).completionTime =
        finiteGPSExecutionSegmentEndTime segment := by
  have hservice_eq_headWork : segment.serviceIncrement i = job.residualWork :=
    hhead_work_eq_service.symm
  have hlist := finiteGPSFCFSCompletedJobs_eq_singleton_of_service_eq_headWork
    (JobId := JobId) segment.startTime (segment.classRate i)
      (segment.serviceIncrement i) job jobs hservice_eq_headWork htail_pos
  have hrate_ne : segment.classRate i ≠ 0 := ne_of_gt hrate_pos
  have hoffset :
      (finiteGPSFCFSCompletionOf segment.startTime (segment.classRate i) 0 job).completionOffset =
        segment.duration := by
    change (0 + job.residualWork) / segment.classRate i = segment.duration
    simp only [zero_add]
    rw [hhead_work_eq_service, hservice_eq_rate_duration]
    field_simp [hrate_ne]
  have htime :
      (finiteGPSFCFSCompletionOf segment.startTime (segment.classRate i) 0 job).completionTime =
        finiteGPSExecutionSegmentEndTime segment := by
    change segment.startTime + (0 + job.residualWork) / segment.classRate i =
      segment.startTime + segment.duration
    simp only [zero_add]
    rw [hhead_work_eq_service, hservice_eq_rate_duration]
    field_simp [hrate_ne]
  exact ⟨by simpa [finiteGPSFCFSCompletedJobsInSegment] using hlist, hoffset, htime⟩

end

end AppliedModelingLib.Probability.Queueing
