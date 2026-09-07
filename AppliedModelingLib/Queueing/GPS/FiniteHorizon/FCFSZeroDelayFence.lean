import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFenceRefinement
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSServiceSplit
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSegmentRefinement
import Mathlib.Tactic

/-!
# FCFS semantics of a zero-delay GPS fence endpoint

When a computational zero-work fence lands exactly at the physical drain
point, a real source batch at that same time has two different executable
representations.  The direct run admits the batch at the end of the draining
service segment.  The fenced run first emits a computational drain segment
with a literally empty source-job batch, then emits a distinct zero-duration,
zero-service external endpoint carrying the real jobs.

The raw segment lists are intentionally not equated.  This module instead
states the semantic stutter relation explicitly and proves that it preserves
the FCFS residual ledger and every completion record, including source job
identifiers, arrival times, and absolute completion times.  Endpoint jobs are
always caller-supplied source data; the generic scheduler never reconstructs
them from aggregate batch work.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- A source-faithful zero-delay fence stutter.  The direct and computational
drain segments retain identical FCFS-relevant service/timing fields.  The
computational endpoint has no source jobs, while the separate instantaneous
external endpoint carries exactly the direct endpoint's literal job batch. -/
def FiniteGPSFCFSZeroDelayFenceStutter
    (direct computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId) : Prop :=
  FiniteGPSExecutionSegment.FCFSObservableEq direct.segment computational.segment ∧
    (∀ i, computational.endpointJobs.jobs i = []) ∧
    (∀ i, realEndpoint.segment.serviceIncrement i = 0) ∧
    direct.endpointJobs = realEndpoint.endpointJobs ∧
    direct.segment.endpointIsExternalBatch = true ∧
    computational.segment.endpointIsExternalBatch = true ∧
    realEndpoint.segment.endpointIsExternalBatch = true ∧
    realEndpoint.segment.duration = 0 ∧
    realEndpoint.segment.startTime =
      finiteGPSExecutionSegmentEndTime computational.segment

omit [Fintype Class] [DecidableEq Class] in
/-- The separate real endpoint in a zero-delay fence stutter occurs at exactly
the same physical time as the direct source endpoint. -/
theorem FiniteGPSFCFSZeroDelayFenceStutter.realEndpointTime_eq_directEnd
    (direct computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hstutter : FiniteGPSFCFSZeroDelayFenceStutter direct computational realEndpoint) :
    finiteGPSExecutionSegmentEndTime realEndpoint.segment =
      finiteGPSExecutionSegmentEndTime direct.segment := by
  rcases hstutter with ⟨⟨hstart, hduration, _hrate, _hservice⟩,
    _hcomputational_empty, _hreal_service_zero, _hjobs, _hdirect_external,
    _hcomputational_external, _hreal_external, hreal_duration, hreal_start⟩
  simp only [finiteGPSExecutionSegmentEndTime] at hreal_start ⊢
  rw [hreal_duration, hreal_start, hstart, hduration]
  ring

omit [Fintype Class] [DecidableEq Class] in
/-- Completion records depend only on the concrete service/timing fields of a
segment, not on its endpoint batch annotation or external bookkeeping tag. -/
theorem finiteGPSFCFSCompletedJobsInSegment_eq_of_segmentFCFSObservableEq
    (i : Class) (jobs : List (FiniteGPSFCFSJob JobId))
    (left right : FiniteGPSExecutionSegment Class)
    (hequivalent : FiniteGPSExecutionSegment.FCFSObservableEq left right) :
    finiteGPSFCFSCompletedJobsInSegment left i jobs =
      finiteGPSFCFSCompletedJobsInSegment right i jobs := by
  rcases hequivalent with ⟨hstart, _hduration, hrate, hservice⟩
  simp [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
    hstart, hrate, hservice]

omit [Fintype Class] [DecidableEq Class] in
/-- A zero-service endpoint is an exact FCFS residual-ledger stutter after a
prior segment with the same service as the direct segment.  This uses the
generic service-splitting theorem with a second service amount of zero, so it
does not silently drop zero-residual bookkeeping cases. -/
theorem finiteGPSFCFSRunSegmentSteps_eq_of_zeroDelayFenceStutter
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (direct computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hstutter : FiniteGPSFCFSZeroDelayFenceStutter direct computational realEndpoint)
    (hinitial_nonneg : initial.Nonnegative)
    (hcomputational_service_nonneg :
      ∀ i, 0 ≤ computational.segment.serviceIncrement i) :
    finiteGPSFCFSRunSegmentSteps initial [direct] =
      finiteGPSFCFSRunSegmentSteps initial [computational, realEndpoint] := by
  rcases hstutter with ⟨hobservational, hcomputational_empty, hreal_service_zero,
    hendpoint_jobs, _hdirect_external, _hcomputational_external, _hreal_external,
    _hreal_duration, _hreal_start⟩
  rcases hobservational with ⟨_hstart, _hduration, _hrate, hservice⟩
  apply (FiniteGPSFCFSJobLedger.mk.injEq _ _).mpr
  funext i
  simp only [finiteGPSFCFSApplySegment]
  rw [hendpoint_jobs]
  rw [hcomputational_empty i, List.append_nil, hreal_service_zero i]
  have hconsume := finiteGPSFCFSConsume_add
    (JobId := JobId) (computational.segment.serviceIncrement i) 0
    (initial.residualJobs i) (hcomputational_service_nonneg i) (by norm_num)
    (fun job hjob => hinitial_nonneg i job hjob)
  simpa [hservice] using congrArg
    (fun jobs => jobs ++ realEndpoint.endpointJobs.jobs i) hconsume

/-- The zero-duration real endpoint emits no completion record after the
computational drain, provided the finite source ledger has the usual strict
positivity invariant.  This condition rules out a spurious completion of a
zero-work placeholder at the instantaneous endpoint. -/
private theorem finiteGPSFCFSCompletedJobsInRealEndpoint_eq_nil_of_zeroDelayFenceStutter
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hcomputational_empty : ∀ i, computational.endpointJobs.jobs i = [])
    (hreal_service_zero : ∀ i, realEndpoint.segment.serviceIncrement i = 0)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (i : Class) :
    finiteGPSFCFSCompletedJobsInSegment realEndpoint.segment i
      ((finiteGPSFCFSApplySegment initial computational.segment
        computational.endpointJobs).residualJobs i) = [] := by
  have hcomputational_endpoint_pos : ∀ j job,
      job ∈ computational.endpointJobs.jobs j → 0 < job.residualWork := by
    intro j job hjob
    rw [hcomputational_empty j] at hjob
    simp at hjob
  have hpost_pos : finiteGPSFCFSJobsStrictlyPositive
      ((finiteGPSFCFSApplySegment initial computational.segment
        computational.endpointJobs).residualJobs i) := by
    intro job hjob
    exact finiteGPSFCFSApplySegment_residualWork_pos initial computational.segment
      computational.endpointJobs hinitial_pos hcomputational_endpoint_pos i job hjob
  exact finiteGPSFCFSCompletedJobsInSegment_eq_nil_of_zero_service
    realEndpoint.segment i
    ((finiteGPSFCFSApplySegment initial computational.segment
      computational.endpointJobs).residualJobs i)
    hpost_pos (hreal_service_zero i)

/-- A source-faithful zero-delay fence stutter preserves the full ordered FCFS
completion records.  In particular it preserves identifiers, source arrival
timestamps, and absolute completion timestamps; it makes no raw-segment-list
equality claim. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_zeroDelayFenceStutter
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (direct computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hstutter : FiniteGPSFCFSZeroDelayFenceStutter direct computational realEndpoint)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork) :
    finiteGPSFCFSCompletionTraceEquivalent initial [direct]
      [computational, realEndpoint] := by
  rcases hstutter with ⟨hobservational, hcomputational_empty, hreal_service_zero,
    _hendpoint_jobs, _hdirect_external, _hcomputational_external, _hreal_external,
    _hreal_duration, _hreal_start⟩
  intro i
  simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
  rw [finiteGPSFCFSCompletedJobsInSegment_eq_of_segmentFCFSObservableEq i
    (initial.residualJobs i) direct.segment computational.segment hobservational]
  rw [finiteGPSFCFSCompletedJobsInRealEndpoint_eq_nil_of_zeroDelayFenceStutter
    initial computational realEndpoint hcomputational_empty hreal_service_zero hinitial_pos i]
  simp

/-- The zero-delay stutter remains sound before a common continuation.  The
continuation starts from the proved-equal literal FCFS ledger, so this theorem
does not treat equality of aggregate GPS workload as a proxy for job state. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_zeroDelayFenceStutter_append
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (direct computational realEndpoint : FiniteGPSFCFSSegmentJobStep Class JobId)
    (suffix : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hstutter : FiniteGPSFCFSZeroDelayFenceStutter direct computational realEndpoint)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (hcomputational_service_nonneg :
      ∀ i, 0 ≤ computational.segment.serviceIncrement i) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      ([direct] ++ suffix) ([computational, realEndpoint] ++ suffix) := by
  have hledger := finiteGPSFCFSRunSegmentSteps_eq_of_zeroDelayFenceStutter
    initial direct computational realEndpoint hstutter hinitial_nonneg
    hcomputational_service_nonneg
  have htrace := finiteGPSFCFSCompletionTraceEquivalent_of_zeroDelayFenceStutter
    initial direct computational realEndpoint hstutter hinitial_pos
  intro i
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSRunSegmentStepsClassCompletions_append, htrace i, hledger]

/-- The executable scheduler supplies the segment portion of a zero-delay
fence stutter at a terminal drain.  The real endpoint job batch is passed in
unchanged on both paths; this result does not synthesize source jobs from
`batchWork`. -/
theorem finiteGPSFCFSZeroDelayFenceStutter_of_terminalDrain
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime drainDelay : ℝ)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (hterminal : finiteGPSNextStepDuration capacity weight work drainDelay = drainDelay) :
    FiniteGPSFCFSZeroDelayFenceStutter
      { segment := finiteGPSBuildExecutionSegment capacity weight work batchWork
          currentTime drainDelay
        endpointJobs := endpointJobs }
      { segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime drainDelay
        endpointJobs := finiteGPSFCFSEmptyEndpointJobs }
      { segment := finiteGPSBuildExecutionSegment capacity weight (fun _ => 0) batchWork
          (currentTime + drainDelay) 0
        endpointJobs := endpointJobs } := by
  refine ⟨?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · apply finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
    rfl
  · intro i
    rfl
  · intro i
    simp [finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
      finiteGPSActiveClasses, finiteGPSServiceIncrement, finiteGPSRemainingAfter]
  · exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
      capacity weight work batchWork currentTime drainDelay |>.mpr hterminal
  · exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
      capacity weight work (fun _ => 0) currentTime drainDelay |>.mpr hterminal
  · simp [finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
      finiteGPSActiveClasses]
  · simp [finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
      finiteGPSActiveClasses]
  · simpa [finiteGPSExecutionSegmentEndTime, finiteGPSBuildExecutionSegment] using
      congrArg (fun delay => currentTime + delay) hterminal.symm

end

end AppliedModelingLib.Probability.Queueing
