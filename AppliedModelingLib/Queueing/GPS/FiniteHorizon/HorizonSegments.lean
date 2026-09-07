import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Terminal horizon-fence segment histories

`AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace` closes an already computed finite batch trace by
running a zero-work terminal fence to a requested horizon.  This module adds
the corresponding concrete segment ledger.  Fence segments are deliberately
kept separate from source batch data: their endpoint batch vector is proved
identically zero, and no source-arrival metadata is introduced.

The result is a finite deterministic closure only.  It does not identify a
fence with an arrival, construct a stochastic process, assert stationarity or
Palm facts, or say anything beyond the endpoint reached by the closed finite
runner.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- A concrete kernel segment built with the zero endpoint batch carries zero
endpoint batch work, independently of whether it ends at an internal depletion
or at the computational fence endpoint. -/
theorem finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
    (capacity : ℝ) (weight work : Class → ℝ)
    (startTime nextBatchDelay : ℝ) (i : Class) :
    (finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
      startTime nextBatchDelay).endpointBatch i = 0 := by
  simp [finiteGPSBuildExecutionSegment, finiteGPSBatchApplied]

/-- Every segment emitted by a finite zero-batch gap has zero endpoint batch
work.  This is a statement about work only; the generic construction carries
no source-event identity for these fence segments. -/
theorem finiteGPSRunGapSegments_forall_endpointBatch_eq_zero_of_zeroBatch
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
      currentTime nextBatchDelay, ∀ i, segment.endpointBatch i = 0 := by
  induction fuel generalizing currentTime work nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      unfold finiteGPSRunGapSegments
      dsimp only
      split
      · intro segment hmem i
        have hsegment : segment =
            finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
              currentTime nextBatchDelay := by
          simpa using hmem
        subst segment
        exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
          capacity weight work currentTime nextBatchDelay i
      · intro segment hmem i
        rcases List.mem_cons.mp hmem with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
            capacity weight work currentTime nextBatchDelay i
        · exact ih
            (work := finiteGPSNextEventState capacity weight work (fun _ => 0)
              nextBatchDelay)
            (currentTime := currentTime +
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (nextBatchDelay := nextBatchDelay -
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            segment htail i

/-- The concrete finite segment ledger of the zero-work terminal fence.  It
is intentionally not an external batch trace and has no source-arrival
metadata. -/
def finiteGPSHorizonFenceSegments
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) :
    List (FiniteGPSExecutionSegment Class) :=
  finiteGPSRunGapSegments ((finiteGPSActiveClasses result.workload).card + 1)
    capacity weight result.workload (fun _ => 0)
    result.currentTime (horizon - result.currentTime)

/-- The horizon-fence segment service ledger is exactly the service field of
the existing deterministic horizon-fence runner. -/
theorem finiteGPSHorizonFenceSegments_service_eq_fence
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSHorizonFenceSegments capacity weight result horizon) i =
      (finiteGPSHorizonFence capacity weight result horizon).service i := by
  exact finiteGPSRunGapSegments_service_eq_runner
    ((finiteGPSActiveClasses result.workload).card + 1)
    capacity weight result.workload (fun _ => 0)
    result.currentTime (horizon - result.currentTime) i

/-- All endpoint batches in the terminal fence ledger are identically zero. -/
theorem finiteGPSHorizonFenceSegments_forall_endpointBatch_eq_zero
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) :
    ∀ segment ∈ finiteGPSHorizonFenceSegments capacity weight result horizon,
      ∀ i, segment.endpointBatch i = 0 := by
  exact finiteGPSRunGapSegments_forall_endpointBatch_eq_zero_of_zeroBatch
    ((finiteGPSActiveClasses result.workload).card + 1)
    capacity weight result.workload result.currentTime
    (horizon - result.currentTime)

/-- Append the concrete zero-batch horizon-fence segments to an existing
finite segment history.  The final runner result is exactly
`finiteGPSCloseAtHorizon`; the fence list remains separately recoverable via
`finiteGPSHorizonFenceSegments`. -/
def finiteGPSCloseAtHorizonWithSegments
    (capacity : ℝ) (weight : Class → ℝ)
    (history : FiniteGPSBatchSegmentHistory Class) (horizon : ℝ) :
    FiniteGPSBatchSegmentHistory Class :=
  { final := finiteGPSCloseAtHorizon capacity weight history.final horizon
    segments := history.segments ++
      finiteGPSHorizonFenceSegments capacity weight history.final horizon }

/-- The closing history's final result is definitionally the existing
zero-batch horizon closure. -/
theorem finiteGPSCloseAtHorizonWithSegments_final_eq_closeAtHorizon
    (capacity : ℝ) (weight : Class → ℝ)
    (history : FiniteGPSBatchSegmentHistory Class) (horizon : ℝ) :
    (finiteGPSCloseAtHorizonWithSegments capacity weight history horizon).final =
      finiteGPSCloseAtHorizon capacity weight history.final horizon := rfl

/-- If the incoming segment history's accumulated segments represent its
stored service field, appending the fence segments represents the closed
runner's stored service field exactly. -/
theorem finiteGPSCloseAtHorizonWithSegments_segments_service_eq_final
    (capacity : ℝ) (weight : Class → ℝ)
    (history : FiniteGPSBatchSegmentHistory Class) (horizon : ℝ)
    (hhistory_service : ∀ i,
      finiteGPSExecutionSegmentsService history.segments i = history.final.service i)
    (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSCloseAtHorizonWithSegments capacity weight history horizon).segments i =
      (finiteGPSCloseAtHorizonWithSegments capacity weight history horizon).final.service i := by
  change finiteGPSExecutionSegmentsService
      (history.segments ++ finiteGPSHorizonFenceSegments capacity weight history.final horizon) i =
    (finiteGPSCloseAtHorizon capacity weight history.final horizon).service i
  rw [finiteGPSExecutionSegmentsService_append, hhistory_service i,
    finiteGPSHorizonFenceSegments_service_eq_fence]
  rfl

/-- Under the explicit finite GPS positivity, nonnegative-work, and preclock
conditions, the appended zero-batch segment history reaches the requested
horizon in the same sense as `finiteGPSCloseAtHorizon`. -/
theorem finiteGPSCloseAtHorizonWithSegments_currentTime
    (capacity : ℝ) (weight : Class → ℝ)
    (history : FiniteGPSBatchSegmentHistory Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ history.final.workload j)
    (hcurrentTime_le_horizon : history.final.currentTime ≤ horizon) :
    (finiteGPSCloseAtHorizonWithSegments capacity weight history horizon).final.currentTime =
      horizon := by
  exact finiteGPSCloseAtHorizon_currentTime capacity weight history.final horizon
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    hcurrentTime_le_horizon

/-- The appended fence portion has no aggregate endpoint batch work in any
class, so it is formally separated from source admission work. -/
theorem finiteGPSCloseAtHorizonWithSegments_fence_endpointBatch_zero
    (capacity : ℝ) (weight : Class → ℝ)
    (history : FiniteGPSBatchSegmentHistory Class) (horizon : ℝ) :
    ∀ segment ∈ finiteGPSHorizonFenceSegments capacity weight history.final horizon,
      ∀ i, segment.endpointBatch i = 0 := by
  exact finiteGPSHorizonFenceSegments_forall_endpointBatch_eq_zero
    capacity weight history.final horizon

/-- Convenience closure for the standard computed batch-segment history. -/
def finiteGPSRunBatchTraceCloseAtHorizonWithSegments
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (times : List ℝ) (horizon : ℝ) :
    FiniteGPSBatchSegmentHistory Class :=
  finiteGPSCloseAtHorizonWithSegments capacity weight
    (finiteGPSRunBatchTraceWithSegments capacity weight batchWork
      currentTime work times) horizon

/-- The standard raw-batch history satisfies the prerequisite service ledger
identity, so its terminal segment closure needs no additional hypothesis. -/
theorem finiteGPSRunBatchTraceCloseAtHorizonWithSegments_segments_service_eq_final
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ) (horizon : ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSRunBatchTraceCloseAtHorizonWithSegments capacity weight batchWork
        currentTime work times horizon).segments i =
      (finiteGPSRunBatchTraceCloseAtHorizonWithSegments capacity weight batchWork
        currentTime work times horizon).final.service i := by
  apply finiteGPSCloseAtHorizonWithSegments_segments_service_eq_final
  intro j
  exact finiteGPSRunBatchTraceWithSegments_service
    capacity weight work batchWork currentTime times j

end

end AppliedModelingLib.Probability.Queueing
