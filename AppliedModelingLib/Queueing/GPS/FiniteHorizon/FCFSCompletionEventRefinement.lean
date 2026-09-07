import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionEventSelector
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFenceRefinement
import Mathlib.Tactic

/-!
# Event-level refinement at a finite FCFS time cut

A finite GPS execution may represent the same constant-rate service interval
either as one segment or as two segments separated by a computational horizon
cut.  The concrete `FiniteGPSFCFSCompletion` records intentionally retain
segment-local fields, so those records need not agree across the two
representations.  The source identifier, arrival time, and absolute
completion time do agree.

This module records the reusable, scheduler-independent part of that fact.
It works at a literal temporal cut and compares only completion events strictly
before that cut.  Consequently a later endpoint batch is irrelevant without
being assumed absent, while a completion exactly at the cut is deliberately
left to the post-cut side of the interface.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- The stable completion events whose absolute completion time is strictly
before a requested physical cut.  This is the observation appropriate for a
finite horizon: a job completed exactly at the horizon is not silently
classified as pre-horizon. -/
def finiteGPSFCFSCompletionEventsBefore
    (cut : ℝ) (events : List (JobId × ℝ × ℝ)) : List (JobId × ℝ × ℝ) :=
  events.filter fun event => event.2.2 < cut

@[simp]
theorem finiteGPSFCFSCompletionEventsBefore_nil (cut : ℝ) :
    finiteGPSFCFSCompletionEventsBefore (JobId := JobId) cut [] = [] := by
  rfl

@[simp]
theorem finiteGPSFCFSCompletionEventsBefore_append
    (cut : ℝ) (left right : List (JobId × ℝ × ℝ)) :
    finiteGPSFCFSCompletionEventsBefore cut (left ++ right) =
      finiteGPSFCFSCompletionEventsBefore cut left ++
        finiteGPSFCFSCompletionEventsBefore cut right := by
  simp [finiteGPSFCFSCompletionEventsBefore]

/-- With nonnegative queued work and a positive class rate, a completion
emitted by a constant-rate FCFS interval cannot precede the interval's
physical start. -/
theorem finiteGPSFCFSCompletedJobsFrom_completionTime_ge_start_of_nonneg
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hserviceBefore_nonneg : 0 ≤ serviceBefore)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segmentStart classRate
      serviceBefore availableService jobs,
      segmentStart ≤ completion.completionTime := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom]
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial]
      · intro completion hcompletion
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial] at hcompletion
        rcases List.mem_cons.mp hcompletion with hhead | htail
        · subst completion
          change segmentStart ≤ segmentStart +
            (serviceBefore + job.residualWork) / classRate
          have hnumerator_nonneg : 0 ≤ serviceBefore + job.residualWork :=
            add_nonneg hserviceBefore_nonneg hjob_nonneg
          have hquotient_nonneg : 0 ≤
              (serviceBefore + job.residualWork) / classRate :=
            div_nonneg hnumerator_nonneg hclassRate_pos.le
          linarith
        · exact ih
            (serviceBefore := serviceBefore + job.residualWork)
            (availableService := availableService - job.residualWork)
            (add_nonneg hserviceBefore_nonneg hjob_nonneg)
            hjobs_tail_nonneg completion htail

/-- The segment-start specialization of the preceding lower timestamp bound. -/
theorem finiteGPSFCFSCompletedJobs_completionTime_ge_start_of_nonneg
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobs segmentStart classRate
      availableService jobs,
      segmentStart ≤ completion.completionTime := by
  simpa [finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_completionTime_ge_start_of_nonneg
      (JobId := JobId) segmentStart classRate 0 availableService jobs
      hclassRate_pos (by norm_num) hjobs_nonneg)

/-- Every stable event emitted by a constant-rate FCFS interval with
nonnegative queued work has absolute completion time at least the interval
start. -/
theorem finiteGPSFCFSCompletionEvents_all_completionTime_ge_start_of_nonneg
    (segmentStart classRate availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    ∀ event ∈ finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobs segmentStart classRate availableService jobs),
      segmentStart ≤ event.2.2 := by
  intro event hevent
  rw [finiteGPSFCFSCompletionEvents] at hevent
  rcases List.mem_map.mp hevent with ⟨completion, hcompletion, rfl⟩
  exact finiteGPSFCFSCompletedJobs_completionTime_ge_start_of_nonneg
    segmentStart classRate availableService jobs hclassRate_pos hjobs_nonneg
    completion hcompletion

/-- If every event in a list lies at or after a cut, its strict pre-cut
observation is empty. -/
theorem finiteGPSFCFSCompletionEventsBefore_eq_nil_of_all_ge
    (cut : ℝ) (events : List (JobId × ℝ × ℝ))
    (hall : ∀ event ∈ events, cut ≤ event.2.2) :
    finiteGPSFCFSCompletionEventsBefore cut events = [] := by
  unfold finiteGPSFCFSCompletionEventsBefore
  apply List.filter_eq_nil_iff.mpr
  intro event hevent
  simp only [decide_eq_true_eq, not_lt]
  exact hall event hevent

/-- Splitting a nonnegative constant-rate FCFS service interval at its
physical cut preserves exactly the stable completion events strictly before
that cut.  The second service piece may be nonzero; its events begin at the
cut and are therefore excluded. -/
theorem finiteGPSFCFSCompletionEventsBefore_split
    (segmentStart classRate firstService secondService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hfirst_nonneg : 0 ≤ firstService)
    (hsecond_nonneg : 0 ≤ secondService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionEventsBefore
        (segmentStart + firstService / classRate)
        (finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobs segmentStart classRate
            (firstService + secondService) jobs)) =
      finiteGPSFCFSCompletionEventsBefore
        (segmentStart + firstService / classRate)
        (finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobs segmentStart classRate firstService jobs)) := by
  have hsplit := finiteGPSFCFSCompletionEvents_split
    (JobId := JobId) segmentStart classRate firstService secondService jobs
    hclassRate_pos hfirst_nonneg hsecond_nonneg hjobs_nonneg
  rw [hsplit, finiteGPSFCFSCompletionEventsBefore_append]
  have hresidual_nonneg : ∀ job ∈ finiteGPSFCFSConsume firstService jobs,
      0 ≤ job.residualWork :=
    finiteGPSFCFSConsume_residualWork_nonneg firstService jobs hfirst_nonneg
      hjobs_nonneg
  have hsecond_events_after : ∀ event ∈
      finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobs
          (segmentStart + firstService / classRate) classRate secondService
          (finiteGPSFCFSConsume firstService jobs)),
      segmentStart + firstService / classRate ≤ event.2.2 :=
    finiteGPSFCFSCompletionEvents_all_completionTime_ge_start_of_nonneg
      (segmentStart + firstService / classRate) classRate secondService
      (finiteGPSFCFSConsume firstService jobs) hclassRate_pos hresidual_nonneg
  rw [finiteGPSFCFSCompletionEventsBefore_eq_nil_of_all_ge
    (segmentStart + firstService / classRate) _ hsecond_events_after]
  simp

/-- Segment-level form of the arbitrary-cut event refinement.  `prefix` is
the physical service delivered before the cut and `whole` continues with an
arbitrary nonnegative amount of additional service.  The two segments may
differ in every non-observable bookkeeping field, including their endpoint
batches; endpoint jobs are appended only after this interval's completions
are emitted. -/
theorem finiteGPSFCFSCompletionEventsBefore_eq_of_segmentServiceExtension
    (whole initialSegment : FiniteGPSExecutionSegment Class) (i : Class)
    (additionalService : ℝ) (jobs : List (FiniteGPSFCFSJob JobId))
    (hstart : whole.startTime = initialSegment.startTime)
    (hrate : whole.classRate i = initialSegment.classRate i)
    (hservice : whole.serviceIncrement i =
      initialSegment.serviceIncrement i + additionalService)
    (hclassRate_pos : 0 < initialSegment.classRate i)
    (hinitialSegment_service_nonneg : 0 ≤ initialSegment.serviceIncrement i)
    (hadditional_nonneg : 0 ≤ additionalService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionEventsBefore
        (initialSegment.startTime + initialSegment.serviceIncrement i /
          initialSegment.classRate i)
        (finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobsInSegment whole i jobs)) =
      finiteGPSFCFSCompletionEventsBefore
        (initialSegment.startTime + initialSegment.serviceIncrement i /
          initialSegment.classRate i)
        (finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobsInSegment initialSegment i jobs)) := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, hstart, hrate, hservice] using
    (finiteGPSFCFSCompletionEventsBefore_split
      (JobId := JobId) initialSegment.startTime (initialSegment.classRate i)
      (initialSegment.serviceIncrement i) additionalService jobs
      hclassRate_pos hinitialSegment_service_nonneg hadditional_nonneg hjobs_nonneg)

/-- Forward membership form of segment refinement.  Every stable completion
event emitted by the pre-cut service piece is also emitted when that piece is
continued by arbitrary nonnegative service.  Unlike an equality of raw
completion records, this conclusion remains valid when a job straddles the
cut. -/
theorem finiteGPSFCFSCompletionEvent_mem_of_segmentServiceExtension
    (whole initialSegment : FiniteGPSExecutionSegment Class) (i : Class)
    (additionalService : ℝ) (jobs : List (FiniteGPSFCFSJob JobId))
    (hstart : whole.startTime = initialSegment.startTime)
    (hrate : whole.classRate i = initialSegment.classRate i)
    (hservice : whole.serviceIncrement i =
      initialSegment.serviceIncrement i + additionalService)
    (hclassRate_pos : 0 < initialSegment.classRate i)
    (hinitialSegment_service_nonneg : 0 ≤ initialSegment.serviceIncrement i)
    (hadditional_nonneg : 0 ≤ additionalService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (event : JobId × ℝ × ℝ)
    (hevent : event ∈ finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobsInSegment initialSegment i jobs)) :
    event ∈ finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobsInSegment whole i jobs) := by
  have hsplit := finiteGPSFCFSCompletionEvents_split
    (JobId := JobId) initialSegment.startTime (initialSegment.classRate i)
    (initialSegment.serviceIncrement i) additionalService jobs
    hclassRate_pos hinitialSegment_service_nonneg hadditional_nonneg hjobs_nonneg
  have hwhole : finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobsInSegment whole i jobs) =
      finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobsInSegment initialSegment i jobs) ++
        finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobs
            (initialSegment.startTime +
              initialSegment.serviceIncrement i / initialSegment.classRate i)
            (initialSegment.classRate i) additionalService
            (finiteGPSFCFSConsume (initialSegment.serviceIncrement i) jobs)) := by
    simpa [finiteGPSFCFSCompletedJobsInSegment, hstart, hrate, hservice] using hsplit
  rw [hwhole]
  exact List.mem_append.mpr (Or.inl hevent)

/-- Stable completion events of a class-wise FCFS trace.  This is a compact
notation for the source-and-absolute-time observation; it deliberately does
not expose segment-local completion-record fields. -/
def finiteGPSFCFSRunSegmentStepsClassCompletionEvents
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    List (JobId × ℝ × ℝ) :=
  finiteGPSFCFSCompletionEvents
    (finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps)

/-- Stable class-completion events compose across a finite step-list
boundary, beginning the right trace from the actual prefix ledger. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletionEvents_append
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i (left ++ right) =
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i left ++
        finiteGPSFCFSRunSegmentStepsClassCompletionEvents
          (finiteGPSFCFSRunSegmentSteps initial left) i right := by
  simp only [finiteGPSFCFSRunSegmentStepsClassCompletionEvents]
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSCompletionEvents_append]

/-- If all events emitted by a suffix start at or after a cut, appending that
suffix does not change the strict pre-cut observation of the full trace. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletionEventsBefore_append_eq_of_tail_all_ge
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (cut : ℝ) (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (htail : ∀ event ∈
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents
        (finiteGPSFCFSRunSegmentSteps initial left) i right,
      cut ≤ event.2.2) :
    finiteGPSFCFSCompletionEventsBefore cut
      (finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i
        (left ++ right)) =
      finiteGPSFCFSCompletionEventsBefore cut
        (finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i left) := by
  rw [finiteGPSFCFSRunSegmentStepsClassCompletionEvents_append,
    finiteGPSFCFSCompletionEventsBefore_append,
    finiteGPSFCFSCompletionEventsBefore_eq_nil_of_all_ge cut _ htail]
  simp

/-- FCFS-observationally equivalent step lists have exactly the same stable
completion events.  This is stronger than the final scalar selector equality
and is useful when a generic GPS refinement exposes a common segment prefix. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletionEvents_eq_of_fcfsObservableEq
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hequivalent : List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
      left right) :
    finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i left =
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i right := by
  unfold finiteGPSFCFSRunSegmentStepsClassCompletionEvents
  rw [finiteGPSFCFSCompletionTraceEquivalent_of_fcfsObservableEq
    initial left right hequivalent i]

/-- A semantic one-cut refinement of a class's FCFS step trace.  The two
traces execute literally the same prefix.  The short trace then stops after
one service interval, while the long trace continues that interval by an
arbitrary nonnegative amount and may execute an arbitrary later suffix.

Endpoint-job batches are deliberately not equated at the displayed terminal
steps: they are appended after the interval's completions, so they cannot
alter an event emitted by its shared service prefix. -/
structure FiniteGPSFCFSClassServiceExtensionTrace
    (i : Class)
    (shortSteps longSteps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) where
  common : List (FiniteGPSFCFSSegmentJobStep Class JobId)
  shortTerminal : FiniteGPSFCFSSegmentJobStep Class JobId
  longTerminal : FiniteGPSFCFSSegmentJobStep Class JobId
  suffix : List (FiniteGPSFCFSSegmentJobStep Class JobId)
  additionalService : ℝ
  short_eq : shortSteps = common ++ [shortTerminal]
  long_eq : longSteps = common ++ longTerminal :: suffix
  start_eq : longTerminal.segment.startTime = shortTerminal.segment.startTime
  classRate_eq : longTerminal.segment.classRate i = shortTerminal.segment.classRate i
  service_eq : longTerminal.segment.serviceIncrement i =
    shortTerminal.segment.serviceIncrement i + additionalService
  short_classRate_pos : 0 < shortTerminal.segment.classRate i
  short_service_nonneg : 0 ≤ shortTerminal.segment.serviceIncrement i
  additionalService_nonneg : 0 ≤ additionalService

/-- Event-membership form of an arbitrary horizon cut.  A stable event
emitted by the short trace is retained by its longer semantic refinement.
This is the correct replacement for raw completion-record equality: a
straddling job may have different local `completedWork` and `completionOffset`
fields, while its identifier, arrival time, and absolute completion time are
unchanged. -/
theorem finiteGPSFCFSCompletionEvent_mem_of_classServiceExtensionTrace
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (shortSteps longSteps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hrefinement : FiniteGPSFCFSClassServiceExtensionTrace i shortSteps longSteps)
    (hcommon_jobs_nonneg :
      ∀ job ∈ (finiteGPSFCFSRunSegmentSteps initial
        hrefinement.common).residualJobs i, 0 ≤ job.residualWork) :
    ∀ event ∈ finiteGPSFCFSRunSegmentStepsClassCompletionEvents
      initial i shortSteps,
      event ∈ finiteGPSFCFSRunSegmentStepsClassCompletionEvents
        initial i longSteps := by
  rcases hrefinement with ⟨common, shortTerminal, longTerminal, suffix,
    additionalService, hshort_eq, hlong_eq, hstart_eq, hclassRate_eq,
    hservice_eq, hshort_classRate_pos, hshort_service_nonneg,
    hadditionalService_nonneg⟩
  intro event hevent
  have hshort_events :
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i shortSteps =
        finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i common ++
          finiteGPSFCFSCompletionEvents
            (finiteGPSFCFSCompletedJobsInSegment shortTerminal.segment i
              ((finiteGPSFCFSRunSegmentSteps initial common).residualJobs i)) := by
    rw [hshort_eq,
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents_append]
    simp [finiteGPSFCFSRunSegmentStepsClassCompletionEvents,
      finiteGPSFCFSRunSegmentStepsClassCompletions]
  have hlong_events :
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i longSteps =
        finiteGPSFCFSRunSegmentStepsClassCompletionEvents initial i common ++
          finiteGPSFCFSRunSegmentStepsClassCompletionEvents
            (finiteGPSFCFSRunSegmentSteps initial common) i
            (longTerminal :: suffix) := by
    rw [hlong_eq,
      finiteGPSFCFSRunSegmentStepsClassCompletionEvents_append]
  rw [hshort_events] at hevent
  rcases List.mem_append.mp hevent with hcommon | hterminal
  · rw [hlong_events]
    exact List.mem_append.mpr (Or.inl hcommon)
  · have hlong_terminal : event ∈ finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobsInSegment longTerminal.segment i
          ((finiteGPSFCFSRunSegmentSteps initial common).residualJobs i)) :=
      finiteGPSFCFSCompletionEvent_mem_of_segmentServiceExtension
        longTerminal.segment shortTerminal.segment i additionalService
        ((finiteGPSFCFSRunSegmentSteps initial common).residualJobs i)
        hstart_eq hclassRate_eq hservice_eq hshort_classRate_pos
        hshort_service_nonneg hadditionalService_nonneg hcommon_jobs_nonneg event hterminal
    rw [hlong_events]
    apply List.mem_append.mpr
    right
    change event ∈ finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (finiteGPSFCFSRunSegmentSteps initial common) i (longTerminal :: suffix))
    simp only [finiteGPSFCFSRunSegmentStepsClassCompletions,
      finiteGPSFCFSCompletionEvents_append]
    exact List.mem_append.mpr (Or.inl hlong_terminal)

end

end AppliedModelingLib.Probability.Queueing
