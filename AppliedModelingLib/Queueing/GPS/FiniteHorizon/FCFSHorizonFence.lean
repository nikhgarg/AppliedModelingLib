import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import Mathlib.Tactic

/-!
# FCFS accounting for zero-batch GPS fences

The executable GPS runner represents a computational horizon fence as a
finite sequence of ordinary GPS segments with zero endpoint batch work.  This
module gives those segments an explicit empty FCFS endpoint ledger and proves
the same recursive compatibility invariant used for source-labelled traces.

Nothing is added at a fence endpoint: the empty job lists are a semantic
representation of the fact that a fence is not a source-arrival event.  The
result is deliberately finite and deterministic; it does not create a
stationary queue or a response-time distribution.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- Explicitly empty endpoint jobs for a computational, non-arrival fence. -/
def finiteGPSFCFSEmptyEndpointJobs : FiniteGPSFCFSEndpointJobs Class JobId where
  jobs := fun _ => []

@[simp]
theorem finiteGPSFCFSEmptyEndpointJobs_jobs (i : Class) :
    (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).jobs i = [] := rfl

theorem finiteGPSFCFSEmptyEndpointJobs_nonnegative :
    (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).Nonnegative := by
  intro i job hjob
  simp at hjob

theorem finiteGPSFCFSEmptyEndpointJobs_classWork (i : Class) :
    (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).classWork i = 0 := by
  simp [FiniteGPSFCFSEndpointJobs.classWork, finiteGPSFCFSJobWork,
    finiteGPSFCFSEmptyEndpointJobs]

/-- Attach the explicitly empty FCFS batch to each computational fence
segment, without changing the segment list or its service fields. -/
def finiteGPSFCFSEmptyEndpointSteps
    (segments : List (FiniteGPSExecutionSegment Class)) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) :=
  segments.map fun segment =>
    { segment := segment
      endpointJobs := finiteGPSFCFSEmptyEndpointJobs }

private theorem finiteGPSFCFSEmptyEndpointJobs_aggregateCompatible_of_endpointBatch_zero
    (segment : FiniteGPSExecutionSegment Class)
    (hbatch : ∀ i, segment.endpointBatch i = 0) :
    (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).AggregateCompatible
      segment := by
  intro i
  rw [finiteGPSFCFSEmptyEndpointJobs_classWork, hbatch i]

private theorem finiteGPSFCFSEmptyKernelStep_compatible
    (capacity : ℝ) (weight work : Class → ℝ) (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      [{ segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
         endpointJobs := finiteGPSFCFSEmptyEndpointJobs }] := by
  let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
    currentTime nextBatchDelay
  have hbatch : ∀ i, segment.endpointBatch i = 0 := by
    intro i
    exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
      capacity weight work currentTime nextBatchDelay i
  have hendpoint :
      (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).AggregateCompatible
        segment :=
    finiteGPSFCFSEmptyEndpointJobs_aggregateCompatible_of_endpointBatch_zero segment hbatch
  have hservice_nonneg : ∀ i, 0 ≤ segment.serviceIncrement i := by
    intro i
    exact finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg
  have hservice_le : ∀ i, segment.serviceIncrement i ≤ initial.classWork i := by
    intro i
    rw [hinitial_matches_work i]
    exact finiteGPSBuildExecutionSegment_serviceIncrement_le_startWorkload
      capacity weight work (fun _ => 0) currentTime nextBatchDelay i
  refine ⟨hinitial_matches_work, ?_, hendpoint,
    finiteGPSFCFSEmptyEndpointJobs_nonnegative, hservice_nonneg, hservice_le, ?_, ?_⟩
  · intro i
    change work i = segment.startWorkload i
    rfl
  · intro i
    exact finiteGPSBuildExecutionSegment_balance
      capacity weight work (fun _ => 0) currentTime nextBatchDelay i
  · intro i
    exact finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
      capacity weight work (fun _ => 0) currentTime nextBatchDelay initial
      finiteGPSFCFSEmptyEndpointJobs hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work hendpoint i

/-- A literal zero-batch GPS gap, equipped with explicit empty FCFS endpoint
lists, satisfies the concrete FCFS compatibility invariant.  This is the
generic bridge needed to append a computational horizon fence to any
source-labelled finite trace. -/
theorem finiteGPSRunGapSegments_emptyEndpointSteps_compatible_of_zeroBatch
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i) :
    FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (finiteGPSFCFSEmptyEndpointSteps
        (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
          currentTime nextBatchDelay)) := by
  induction fuel generalizing work currentTime nextBatchDelay initial with
  | zero =>
      simpa [finiteGPSRunGapSegments, finiteGPSFCFSEmptyEndpointSteps] using
        hinitial_matches_work
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsingle :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work (fun _ => 0)
              currentTime nextBatchDelay =
              [finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
                currentTime nextBatchDelay] := by
            simp [finiteGPSRunGapSegments, duration, hduration]
        rw [hsingle]
        simpa [finiteGPSFCFSEmptyEndpointSteps] using
          (finiteGPSFCFSEmptyKernelStep_compatible
            (JobId := JobId) capacity weight work currentTime nextBatchDelay initial
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work)
      · have hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
            nextBatchDelay := by
            simpa [duration] using hduration
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hnext_delay_nonneg : 0 ≤ nextBatchDelay - duration := by
          rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work nextBatchDelay)
        let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
        let step : FiniteGPSFCFSSegmentJobStep Class JobId :=
          { segment := segment
            endpointJobs := finiteGPSFCFSEmptyEndpointJobs }
        have hhead := finiteGPSFCFSEmptyKernelStep_compatible
          (JobId := JobId) capacity weight work currentTime nextBatchDelay initial
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work
        have hnext_nonneg :
            (finiteGPSFCFSApplySegment initial segment
              finiteGPSFCFSEmptyEndpointJobs).Nonnegative := by
          apply finiteGPSFCFSApplySegment_nonnegative initial segment
            finiteGPSFCFSEmptyEndpointJobs hinitial_nonneg
          · intro i
            exact finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
              hnextBatchDelay_nonneg
          · exact finiteGPSFCFSEmptyEndpointJobs_nonnegative
        have hnext_matches : ∀ i,
            (finiteGPSFCFSApplySegment initial segment
              finiteGPSFCFSEmptyEndpointJobs).classWork i =
              finiteGPSNextEventState capacity weight work (fun _ => 0)
                nextBatchDelay i := by
          intro i
          have hbatch :
              (finiteGPSFCFSEmptyEndpointJobs (Class := Class) (JobId := JobId)).AggregateCompatible
                segment := by
            apply finiteGPSFCFSEmptyEndpointJobs_aggregateCompatible_of_endpointBatch_zero
            intro j
            exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
              capacity weight work currentTime nextBatchDelay j
          exact finiteGPSFCFSApplyKernelSegment_classWork_eq_nextEvent
            capacity weight work (fun _ => 0) currentTime nextBatchDelay initial
            finiteGPSFCFSEmptyEndpointJobs hcapacity hweight_pos htotal_weight_le_one
            hwork_nonneg hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work hbatch i
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration)
          (initial := finiteGPSFCFSApplySegment initial segment
            finiteGPSFCFSEmptyEndpointJobs)
          hnext_work_nonneg hnext_delay_nonneg hnext_nonneg hnext_matches
        have hsegments :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work (fun _ => 0)
              currentTime nextBatchDelay =
              segment :: finiteGPSRunGapSegments fuel capacity weight
                (finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay)
                (fun _ => 0) (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hduration, segment]
        rw [hsegments]
        change FiniteGPSFCFSRunSegmentStepsCompatible initial work
          (step :: finiteGPSFCFSEmptyEndpointSteps
            (finiteGPSRunGapSegments fuel capacity weight
              (finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay)
              (fun _ => 0) (currentTime + duration) (nextBatchDelay - duration)))
        change FiniteGPSFCFSRunSegmentStepsCompatible initial work
          (step :: _) at hhead
        rcases hhead with ⟨hinit, hstart, hbatch, hendpoint, hservice,
          hservice_le, hbalance, hhead_tail⟩
        refine ⟨hinit, hstart, hbatch, hendpoint, hservice, hservice_le,
          hbalance, ?_⟩
        simpa [step, segment] using htail

end

end AppliedModelingLib.Probability.Queueing
