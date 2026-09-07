import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ExecutableSegmentSemantics
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletion
import Mathlib.Tactic

/-!
# Nonnegative executable GPS timing for FCFS completions

The executable GPS kernel never assigns a negative class rate.  Together with
nonnegative segment duration, this is enough to locate every FCFS completion
at or before its segment endpoint, including the degenerate zero-rate case.
The result is finite and source-agnostic.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- Every executable GPS class rate is nonnegative.  The inactive branch is
exactly zero; the active branch has the existing strict rate lower bound. -/
theorem finiteGPSClassRate_nonneg
    {capacity : ℝ} {weight work : Class → ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1) :
    0 ≤ finiteGPSClassRate capacity weight work i := by
  by_cases hactive : 0 < work i
  · exact (finiteGPSClassRate_pos_of_active
      hcapacity hweight_pos htotal_weight_le_one hactive).le
  · rw [finiteGPSClassRate_eq_zero_of_not_active hactive]

/-- A concrete kernel segment retains the nonnegativity of its stored
class-rate field. -/
theorem finiteGPSBuildExecutionSegment_classRate_nonneg
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1) :
    0 ≤ (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).classRate i := by
  exact finiteGPSClassRate_nonneg hcapacity hweight_pos htotal_weight_le_one

/-- Every segment emitted by one bounded GPS gap has nonnegative stored
class rate. -/
theorem finiteGPSRunGapSegments_classRate_nonneg
    (fuel : ℕ) {capacity nextBatchDelay : ℝ}
    {weight work batchWork : Class → ℝ} {currentTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      0 ≤ segment.classRate i := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · intro segment hsegment
        have hsegment_eq : segment =
            finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hterminal] using hsegment
        subst segment
        exact finiteGPSBuildExecutionSegment_classRate_nonneg
          hcapacity hweight_pos htotal_weight_le_one
      · intro segment hsegment
        have hlist : finiteGPSRunGapSegments (fuel + 1)
            capacity weight work batchWork currentTime nextBatchDelay =
            finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay ::
            finiteGPSRunGapSegments fuel capacity weight
              (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
              batchWork (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hterminal]
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_classRate_nonneg
            hcapacity hweight_pos htotal_weight_le_one
        · exact ih (work := finiteGPSNextEventState capacity weight work batchWork
              nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration) segment htail

/-- Every segment emitted by the finite chronological batch runner has a
nonnegative stored class rate.  This is structural in the emitted segment
ledger and does not assume source labels or a particular arrival law. -/
theorem finiteGPSRunBatchTraceSegments_classRate_nonneg
    {capacity : ℝ} {weight work : Class → ℝ}
    {batchWork : ℝ → Class → ℝ} {currentTime : ℝ} {i : Class}
    (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      0 ≤ segment.classRate i := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      by_cases hbatchApplied : gap.batchApplied = true
      · have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
            currentTime work (eventTime :: times) =
            finiteGPSRunGapSegments gapFuel capacity weight work
              (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_batchApplied
              capacity weight batchWork currentTime work eventTime times
              (by simpa [gap, gapFuel] using hbatchApplied))
        intro segment hsegment
        rw [htrace] at hsegment
        rcases List.mem_append.mp hsegment with hgap | htail
        · exact finiteGPSRunGapSegments_classRate_nonneg gapFuel
            hcapacity hweight_pos htotal_weight_le_one segment hgap
        · exact ih (currentTime := eventTime) (work := gap.workload)
            segment htail
      · have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
            currentTime work (eventTime :: times) =
            finiteGPSRunGapSegments gapFuel capacity weight work
              (batchWork eventTime) currentTime (eventTime - currentTime) := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
              capacity weight batchWork currentTime work eventTime times
              (by simpa [gap, gapFuel] using hbatchApplied))
        intro segment hsegment
        rw [htrace] at hsegment
        exact finiteGPSRunGapSegments_classRate_nonneg gapFuel
          hcapacity hweight_pos htotal_weight_le_one segment hsegment

private theorem finiteGPSFCFSCompletedJobsFrom_completionTime_eq_start_of_zero_rate
    (segmentStart serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segmentStart 0
      serviceBefore availableService jobs,
      completion.completionTime = segmentStart := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial]
      · intro completion hcompletion
        rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart 0 serviceBefore availableService job jobs hpartial] at hcompletion
        rcases List.mem_cons.mp hcompletion with hhead | htail
        · subst completion
          simp [finiteGPSFCFSCompletionOf]
        · exact ih (serviceBefore := serviceBefore + job.residualWork)
            (availableService := availableService - job.residualWork) completion htail

/-- A finite FCFS completion produced by a segment with nonnegative rate and
duration occurs no later than that segment's endpoint.  The zero-rate case
is handled directly: Lean's total real division gives zero elapsed offset,
so a degenerate completion is timestamped at the segment start. -/
theorem finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime_of_nonneg_rate
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_nonneg : 0 ≤ segment.classRate i)
    (hduration_nonneg : 0 ≤ segment.duration)
    (hservice_eq_rate_mul_duration :
      segment.serviceIncrement i = segment.classRate i * segment.duration) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      completion.completionTime ≤ finiteGPSExecutionSegmentEndTime segment := by
  intro completion hcompletion
  by_cases hclassRate_pos : 0 < segment.classRate i
  · exact finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime
      segment i jobs hclassRate_pos hservice_eq_rate_mul_duration completion hcompletion
  · have hclassRate_zero : segment.classRate i = 0 :=
      le_antisymm (le_of_not_gt hclassRate_pos) hclassRate_nonneg
    have htime : completion.completionTime = segment.startTime := by
      change completion ∈ finiteGPSFCFSCompletedJobsFrom segment.startTime
        (segment.classRate i) 0 (segment.serviceIncrement i) jobs at hcompletion
      rw [hclassRate_zero] at hcompletion
      exact finiteGPSFCFSCompletedJobsFrom_completionTime_eq_start_of_zero_rate
        segment.startTime 0 (segment.serviceIncrement i) jobs completion hcompletion
    rw [htime]
    unfold finiteGPSExecutionSegmentEndTime
    linarith

/-- A completed FCFS job from a nonnegative-rate segment is never timestamped
before that segment's start when the source queue has nonnegative residual
work.  The result also covers a zero class rate: Lean's total division makes
the recorded offset zero in that degenerate branch. -/
theorem finiteGPSFCFSCompletedJobsInSegment_completionTime_ge_startTime_of_nonneg_rate_and_jobs
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hclassRate_nonneg : 0 ≤ segment.classRate i)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork) :
    ∀ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      segment.startTime ≤ completion.completionTime := by
  change ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segment.startTime
      (segment.classRate i) 0 (segment.serviceIncrement i) jobs,
      segment.startTime ≤ completion.completionTime
  have hgeneral : ∀ (serviceBefore availableService : ℝ),
      0 ≤ serviceBefore →
      ∀ completion ∈ finiteGPSFCFSCompletedJobsFrom segment.startTime
        (segment.classRate i) serviceBefore availableService jobs,
        segment.startTime ≤ completion.completionTime := by
    intro serviceBefore availableService hserviceBefore
    induction jobs generalizing serviceBefore availableService with
    | nil =>
        simp [finiteGPSFCFSCompletedJobsFrom]
    | cons job jobs ih =>
        by_cases hpartial : availableService < job.residualWork
        · simp [finiteGPSFCFSCompletedJobsFrom, hpartial]
        · intro completion hcompletion
          rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segment.startTime (segment.classRate i) serviceBefore availableService
            job jobs hpartial] at hcompletion
          rcases List.mem_cons.mp hcompletion with hhead | htail
          · subst completion
            change segment.startTime ≤ segment.startTime +
              (serviceBefore + job.residualWork) / segment.classRate i
            exact le_add_of_nonneg_right
              (div_nonneg (add_nonneg hserviceBefore
                (hjobs_nonneg job (by simp))) hclassRate_nonneg)
          · exact ih
              (fun later hlater => hjobs_nonneg later (by simp [hlater]))
              (serviceBefore + job.residualWork)
              (availableService - job.residualWork)
              (add_nonneg hserviceBefore (hjobs_nonneg job (by simp)))
              completion htail
  exact hgeneral 0 (segment.serviceIncrement i) (by norm_num)

end

end AppliedModelingLib.Probability.Queueing
