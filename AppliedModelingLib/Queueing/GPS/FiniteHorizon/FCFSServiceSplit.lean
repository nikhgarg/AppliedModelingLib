import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletion
import Mathlib.Tactic

/-!
# Exact splitting of finite FCFS service intervals

This module isolates the deterministic algebra behind refining one constant-rate
FCFS service interval into two consecutive intervals.  The results retain the
ordered residual queue and the individual completion records; they do not infer
queue equality from aggregate workload conservation.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {JobId : Type*}

/-- Delivering two nonnegative amounts of service consecutively is exactly the
same residual FCFS update as delivering their sum at once. -/
theorem finiteGPSFCFSConsume_add
    (firstService secondService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hfirst_nonneg : 0 ≤ firstService)
    (hsecond_nonneg : 0 ≤ secondService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSConsume (firstService + secondService) jobs =
      finiteGPSFCFSConsume secondService (finiteGPSFCFSConsume firstService jobs) := by
  induction jobs generalizing firstService secondService with
  | nil =>
      simp [finiteGPSFCFSConsume]
  | cons job jobs ih =>
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hfirst_partial : firstService < job.residualWork
      · by_cases htotal_partial : firstService + secondService < job.residualWork
        · have hsecond_partial : secondService < job.residualWork - firstService := by
            linarith
          rw [finiteGPSFCFSConsume_eq_partial_head
            (firstService + secondService) job jobs htotal_partial]
          rw [finiteGPSFCFSConsume_eq_partial_head
            firstService job jobs hfirst_partial]
          rw [finiteGPSFCFSConsume_eq_partial_head
            secondService
            { job with residualWork := job.residualWork - firstService }
            jobs hsecond_partial]
          congr 1
          cases job
          simp
          ring
        · have hsecond_complete : ¬ secondService < job.residualWork - firstService := by
            linarith [le_of_not_gt htotal_partial]
          rw [finiteGPSFCFSConsume_eq_after_complete_head
            (firstService + secondService) job jobs htotal_partial]
          rw [finiteGPSFCFSConsume_eq_partial_head
            firstService job jobs hfirst_partial]
          rw [finiteGPSFCFSConsume_eq_after_complete_head
            secondService
            { job with residualWork := job.residualWork - firstService }
            jobs hsecond_complete]
          congr 1
          ring
      · have hfirst_complete : job.residualWork ≤ firstService :=
          le_of_not_gt hfirst_partial
        have htotal_complete : ¬ firstService + secondService < job.residualWork := by
          linarith
        rw [finiteGPSFCFSConsume_eq_after_complete_head
          (firstService + secondService) job jobs htotal_complete]
        rw [finiteGPSFCFSConsume_eq_after_complete_head
          firstService job jobs hfirst_partial]
        have hfirst_residual_nonneg : 0 ≤ firstService - job.residualWork := by
          linarith
        have htail := ih
          (firstService := firstService - job.residualWork)
          (secondService := secondService) hfirst_residual_nonneg hsecond_nonneg hjobs_tail_nonneg
        have hservice_sum :
            firstService + secondService - job.residualWork =
              (firstService - job.residualWork) + secondService := by ring
        rw [hservice_sum]
        exact htail

/-- The segment-local part of a completion record.  `completedWork` and
`completionOffset` are local to the service segment which emitted the record;
the source identifier, arrival time, and absolute completion time are the
invariants needed to compare a refinement with an unsplit execution. -/
def finiteGPSFCFSCompletionEvent
    (completion : FiniteGPSFCFSCompletion JobId) : JobId × ℝ × ℝ :=
  (completion.identifier, completion.arrivalTime, completion.completionTime)

/-- The ordered source-and-time events represented by a finite completion
ledger. -/
def finiteGPSFCFSCompletionEvents
    (completions : List (FiniteGPSFCFSCompletion JobId)) : List (JobId × ℝ × ℝ) :=
  completions.map finiteGPSFCFSCompletionEvent

@[simp]
theorem finiteGPSFCFSCompletionEvents_append
    (left right : List (FiniteGPSFCFSCompletion JobId)) :
    finiteGPSFCFSCompletionEvents (left ++ right) =
      finiteGPSFCFSCompletionEvents left ++ finiteGPSFCFSCompletionEvents right := by
  simp [finiteGPSFCFSCompletionEvents]

/-- Completion events depend on a segment description only through the
effective physical start `segmentStart + serviceBefore / classRate`.  This is
an exact algebraic statement; rate positivity is required separately when that
quotient is interpreted as elapsed time. -/
theorem finiteGPSFCFSCompletionEventsFrom_eq_of_effectiveStart_eq
    (leftStart rightStart classRate leftServiceBefore rightServiceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (heffective_start : leftStart + leftServiceBefore / classRate =
      rightStart + rightServiceBefore / classRate) :
    finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobsFrom leftStart classRate leftServiceBefore
        availableService jobs) =
      finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobsFrom rightStart classRate rightServiceBefore
          availableService jobs) := by
  induction jobs generalizing leftServiceBefore rightServiceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom, finiteGPSFCFSCompletionEvents]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial, finiteGPSFCFSCompletionEvents]
      · have heffective_next :
            leftStart + (leftServiceBefore + job.residualWork) / classRate =
              rightStart + (rightServiceBefore + job.residualWork) / classRate := by
          calc
            leftStart + (leftServiceBefore + job.residualWork) / classRate =
                (leftStart + leftServiceBefore / classRate) +
                  job.residualWork / classRate := by ring
            _ = (rightStart + rightServiceBefore / classRate) +
                  job.residualWork / classRate := by rw [heffective_start]
            _ = rightStart + (rightServiceBefore + job.residualWork) / classRate := by ring
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          leftStart classRate leftServiceBefore availableService job jobs hpartial]
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          rightStart classRate rightServiceBefore availableService job jobs hpartial]
        have htail := ih
          (leftServiceBefore := leftServiceBefore + job.residualWork)
          (rightServiceBefore := rightServiceBefore + job.residualWork)
          (availableService := availableService - job.residualWork)
          heffective_next
        change finiteGPSFCFSCompletionEvent
              (finiteGPSFCFSCompletionOf leftStart classRate leftServiceBefore job) ::
            finiteGPSFCFSCompletionEvents
              (finiteGPSFCFSCompletedJobsFrom leftStart classRate
                (leftServiceBefore + job.residualWork)
                (availableService - job.residualWork) jobs) =
          finiteGPSFCFSCompletionEvent
              (finiteGPSFCFSCompletionOf rightStart classRate rightServiceBefore job) ::
            finiteGPSFCFSCompletionEvents
              (finiteGPSFCFSCompletedJobsFrom rightStart classRate
                (rightServiceBefore + job.residualWork)
                (availableService - job.residualWork) jobs)
        rw [htail]
        simp [finiteGPSFCFSCompletionEvent, finiteGPSFCFSCompletionOf]
        exact heffective_next

/-- Splitting a nonnegative amount of FCFS service into two consecutive
constant-rate intervals preserves the ordered source-and-absolute-time
completion events exactly.  The raw completion records themselves are not
equal in general: when a head job straddles the boundary, its second-segment
record intentionally stores only the residual work and a segment-local offset.
-/
theorem finiteGPSFCFSCompletionEventsFrom_split
    (segmentStart classRate serviceBefore firstService secondService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hfirst_nonneg : 0 ≤ firstService)
    (hsecond_nonneg : 0 ≤ secondService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
        (firstService + secondService) jobs) =
      finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
          firstService jobs) ++
        finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobsFrom
            (segmentStart + (serviceBefore + firstService) / classRate) classRate 0
            secondService (finiteGPSFCFSConsume firstService jobs)) := by
  induction jobs generalizing serviceBefore firstService secondService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom, finiteGPSFCFSCompletionEvents,
        finiteGPSFCFSConsume]
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hfirst_partial : firstService < job.residualWork
      · by_cases htotal_partial : firstService + secondService < job.residualWork
        · have hsecond_partial : secondService < job.residualWork - firstService := by
            linarith
          simp [finiteGPSFCFSCompletedJobsFrom, finiteGPSFCFSConsume,
            hfirst_partial, htotal_partial, hsecond_partial,
            finiteGPSFCFSCompletionEvents]
        · have hsecond_complete : ¬ secondService < job.residualWork - firstService := by
            linarith [le_of_not_gt htotal_partial]
          rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segmentStart classRate serviceBefore (firstService + secondService)
            job jobs htotal_partial]
          rw [finiteGPSFCFSCompletedJobsFrom_eq_nil_of_partial_head
            segmentStart classRate serviceBefore firstService job jobs hfirst_partial]
          rw [finiteGPSFCFSConsume_eq_partial_head
            firstService job jobs hfirst_partial]
          rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            (segmentStart + (serviceBefore + firstService) / classRate) classRate 0
            secondService { job with residualWork := job.residualWork - firstService }
            jobs hsecond_complete]
          have heffective_tail :
              segmentStart + (serviceBefore + job.residualWork) / classRate =
                (segmentStart + (serviceBefore + firstService) / classRate) +
                  (job.residualWork - firstService) / classRate := by
            ring
          have htail := finiteGPSFCFSCompletionEventsFrom_eq_of_effectiveStart_eq
            (JobId := JobId)
            segmentStart
            (segmentStart + (serviceBefore + firstService) / classRate)
            classRate
            (serviceBefore + job.residualWork)
            (job.residualWork - firstService)
            (firstService + secondService - job.residualWork)
            jobs heffective_tail
          have hservice_eq :
              firstService + secondService - job.residualWork =
                secondService - (job.residualWork - firstService) := by ring
          have htail_maps :
              List.map finiteGPSFCFSCompletionEvent
                  (finiteGPSFCFSCompletedJobsFrom segmentStart classRate
                    (serviceBefore + job.residualWork)
                    (firstService + secondService - job.residualWork) jobs) =
                List.map finiteGPSFCFSCompletionEvent
                  (finiteGPSFCFSCompletedJobsFrom
                    (segmentStart + (serviceBefore + firstService) / classRate) classRate
                    (job.residualWork - firstService)
                    (secondService - (job.residualWork - firstService)) jobs) := by
            simpa only [finiteGPSFCFSCompletionEvents, hservice_eq] using htail
          simp only [finiteGPSFCFSCompletionEvents, List.map_cons, List.map_nil,
            List.nil_append]
          rw [htail_maps]
          simp only [zero_add]
          congr 1
          simp [finiteGPSFCFSCompletionEvent, finiteGPSFCFSCompletionOf]
          field_simp [ne_of_gt hclassRate_pos]
          ring
      · have hfirst_complete : job.residualWork ≤ firstService :=
          le_of_not_gt hfirst_partial
        have htotal_complete : ¬ firstService + secondService < job.residualWork := by
          linarith
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore (firstService + secondService)
          job jobs htotal_complete]
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore firstService job jobs hfirst_partial]
        rw [finiteGPSFCFSConsume_eq_after_complete_head
          firstService job jobs hfirst_partial]
        have hfirst_residual_nonneg : 0 ≤ firstService - job.residualWork := by
          linarith
        have htail := ih
          (serviceBefore := serviceBefore + job.residualWork)
          (firstService := firstService - job.residualWork)
          (secondService := secondService)
          hfirst_residual_nonneg hsecond_nonneg hjobs_tail_nonneg
        have hstart_eq :
            segmentStart +
                ((serviceBefore + job.residualWork) +
                  (firstService - job.residualWork)) / classRate =
              segmentStart + (serviceBefore + firstService) / classRate := by
          ring
        rw [hstart_eq] at htail
        have hservice_sum :
            firstService - job.residualWork + secondService =
              firstService + secondService - job.residualWork := by ring
        rw [hservice_sum] at htail
        have htail_maps :
            List.map finiteGPSFCFSCompletionEvent
                (finiteGPSFCFSCompletedJobsFrom segmentStart classRate
                  (serviceBefore + job.residualWork)
                  (firstService + secondService - job.residualWork) jobs) =
              List.map finiteGPSFCFSCompletionEvent
                  (finiteGPSFCFSCompletedJobsFrom segmentStart classRate
                    (serviceBefore + job.residualWork)
                    (firstService - job.residualWork) jobs) ++
                List.map finiteGPSFCFSCompletionEvent
                  (finiteGPSFCFSCompletedJobsFrom
                    (segmentStart + (serviceBefore + firstService) / classRate) classRate 0
                    secondService
                    (finiteGPSFCFSConsume (firstService - job.residualWork) jobs)) := by
          simpa only [finiteGPSFCFSCompletionEvents] using htail
        simp only [finiteGPSFCFSCompletionEvents, List.map_cons]
        rw [htail_maps]
        simp [finiteGPSFCFSCompletionEvent, finiteGPSFCFSCompletionOf]

/-- The segment-start specialization of
`finiteGPSFCFSCompletionEventsFrom_split`.  It compares the completed-job
ledgers produced by a whole interval with the ledgers produced by its two
consecutive pieces, through their source-and-absolute-time events. -/
theorem finiteGPSFCFSCompletionEvents_split
    (segmentStart classRate firstService secondService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_pos : 0 < classRate)
    (hfirst_nonneg : 0 ≤ firstService)
    (hsecond_nonneg : 0 ≤ secondService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    finiteGPSFCFSCompletionEvents
      (finiteGPSFCFSCompletedJobs segmentStart classRate
        (firstService + secondService) jobs) =
      finiteGPSFCFSCompletionEvents
        (finiteGPSFCFSCompletedJobs segmentStart classRate firstService jobs) ++
        finiteGPSFCFSCompletionEvents
          (finiteGPSFCFSCompletedJobs (segmentStart + firstService / classRate)
            classRate secondService (finiteGPSFCFSConsume firstService jobs)) := by
  simpa [finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletionEventsFrom_split
      (JobId := JobId) segmentStart classRate 0 firstService secondService jobs
      hclassRate_pos hfirst_nonneg hsecond_nonneg hjobs_nonneg)

end

end AppliedModelingLib.Probability.Queueing
