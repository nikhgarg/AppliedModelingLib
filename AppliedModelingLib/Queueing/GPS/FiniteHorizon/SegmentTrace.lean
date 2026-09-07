import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

/-!
# Finite segment-level GPS execution histories

`AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchEvent` supplies one concrete GPS event step and
`AppliedModelingLib.Queueing.GPS.FiniteHorizon.Runner` resolves every internal depletion before an external
arrival batch.  This module records those computed steps as finite execution
segments.  A segment contains its actual half-open service interval, the
workload snapshot and GPS rates at its left endpoint, the pre-batch endpoint
workload, and the batch applied at its right endpoint.

The history is produced by the runner's recursion; it is not a caller-supplied
path certificate.  Exact arrival/depletion ties follow the existing kernel:
service accrues over the preceding interval and the external batch is applied
once at the shared right endpoint.

This is deliberately only a finite deterministic construction.  It makes no
FCFS job-order, stationary, Palm, or infinite-horizon claim.  In particular,
the later stochastic construction must still supply a finite external-batch
trace and then establish its stationary/Palm limiting interpretation.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- One concrete constant-rate GPS interval.  `preEndpointWorkload` is the
workload after service over `[startTime, startTime + duration]` and before the
batch at the right endpoint.  `endpointWorkload` is the post-batch snapshot
from which a following segment, if any, starts. -/
structure FiniteGPSExecutionSegment (Class : Type*) where
  startTime : ℝ
  duration : ℝ
  startWorkload : Class → ℝ
  classRate : Class → ℝ
  serviceIncrement : Class → ℝ
  preEndpointWorkload : Class → ℝ
  endpointBatch : Class → ℝ
  endpointWorkload : Class → ℝ
  endpointIsExternalBatch : Bool

/-- Right endpoint of a concrete finite GPS segment. -/
def finiteGPSExecutionSegmentEndTime
    (segment : FiniteGPSExecutionSegment Class) : ℝ :=
  segment.startTime + segment.duration

/-- The affine workload evolution associated with a segment before its
right-endpoint batch is applied.  The endpoint identities below justify this
as the local piecewise-linear workload representation under the GPS positivity
conditions. -/
def finiteGPSExecutionSegmentLinearWorkload
    (segment : FiniteGPSExecutionSegment Class) (time : ℝ) : Class → ℝ :=
  fun i =>
    segment.startWorkload i - segment.classRate i * (time - segment.startTime)

/-- The affine cumulative service accrued from a segment's left endpoint. -/
def finiteGPSExecutionSegmentLinearService
    (segment : FiniteGPSExecutionSegment Class) (time : ℝ) : Class → ℝ :=
  fun i => segment.classRate i * (time - segment.startTime)

/-- The concrete segment emitted by one invocation of the existing GPS event
kernel.  Every field is computed from that kernel; no transition condition is
accepted from a caller. -/
def finiteGPSBuildExecutionSegment
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) : FiniteGPSExecutionSegment Class :=
  let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
  { startTime := startTime
    duration := duration
    startWorkload := work
    classRate := finiteGPSClassRate capacity weight work
    serviceIncrement := finiteGPSServiceIncrement capacity weight work duration
    preEndpointWorkload := finiteGPSRemainingAfter capacity weight work duration
    endpointBatch := finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay
    endpointWorkload := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
    endpointIsExternalBatch := decide (duration = nextBatchDelay) }

@[simp]
theorem finiteGPSBuildExecutionSegment_startTime
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).startTime = startTime := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_duration
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).duration =
      finiteGPSNextStepDuration capacity weight work nextBatchDelay := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_startWorkload
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).startWorkload = work := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_classRate
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).classRate =
      finiteGPSClassRate capacity weight work := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_serviceIncrement
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).serviceIncrement =
      finiteGPSServiceIncrement capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_preEndpointWorkload
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).preEndpointWorkload =
      finiteGPSRemainingAfter capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_endpointBatch
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointBatch =
      finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay := rfl

@[simp]
theorem finiteGPSBuildExecutionSegment_endpointWorkload
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointWorkload =
      finiteGPSNextEventState capacity weight work batchWork nextBatchDelay := rfl

/-- The segment's Boolean endpoint tag is true exactly when the concrete
kernel reached the pending external batch.  Thus an equality tie is externally
ended rather than replayed as a separate depletion event. -/
theorem finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointIsExternalBatch = true ↔
      finiteGPSNextStepDuration capacity weight work nextBatchDelay = nextBatchDelay := by
  simp [finiteGPSBuildExecutionSegment]

/-- Under the GPS positivity hypotheses, a concrete segment is a genuine
nonnegative-time interval whenever its pending external batch delay is
nonnegative. -/
theorem finiteGPSBuildExecutionSegment_duration_nonneg
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay : 0 ≤ nextBatchDelay) :
    0 ≤ (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).duration := by
  exact finiteGPSNextStepDuration_nonneg hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg hnextBatchDelay

/-- An external endpoint applies the entire pending simultaneous batch.  In
particular, an arrival/depletion equality tie has this behavior. -/
theorem finiteGPSBuildExecutionSegment_endpointBatch_eq_batchWork_of_external
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ)
    (hExternal :
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).endpointIsExternalBatch = true) (i : Class) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointBatch i = batchWork i := by
  have heq : finiteGPSNextStepDuration capacity weight work nextBatchDelay =
      nextBatchDelay :=
    finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff capacity weight work
      batchWork startTime nextBatchDelay |>.mp hExternal
  simp [finiteGPSBuildExecutionSegment, finiteGPSBatchApplied, heq]

/-- A non-external endpoint receives no batch work. -/
theorem finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_not_external
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ)
    (hnotExternal :
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).endpointIsExternalBatch = false) (i : Class) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointBatch i = 0 := by
  have hne : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
      nextBatchDelay := by
    intro heq
    have htrue :
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).endpointIsExternalBatch = true :=
      finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff capacity weight work
        batchWork startTime nextBatchDelay |>.mpr heq
    simp [htrue] at hnotExternal
  simp [finiteGPSBuildExecutionSegment, finiteGPSBatchApplied, hne]

/-- The segment's post-endpoint snapshot has the exact workload balance from
the kernel, including the actual endpoint batch. -/
theorem finiteGPSBuildExecutionSegment_balance
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) (i : Class) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointWorkload i =
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).startWorkload i +
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).endpointBatch i -
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).serviceIncrement i := by
  exact finiteGPSNextEventState_balance capacity weight work batchWork nextBatchDelay i

/-- The right endpoint is the start time plus the kernel's actual event
duration. -/
theorem finiteGPSBuildExecutionSegment_endTime
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    finiteGPSExecutionSegmentEndTime
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) =
      startTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay := rfl

/-- Under the ordinary finite GPS positivity conditions, the pre-batch
endpoint agrees exactly with the segment's affine workload evolution. -/
theorem finiteGPSBuildExecutionSegment_preEndpoint_eq_linear
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).preEndpointWorkload i =
      finiteGPSExecutionSegmentLinearWorkload
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay)
        (finiteGPSExecutionSegmentEndTime
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay)) i := by
  change finiteGPSRemainingAfter capacity weight work
      (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
    work i - finiteGPSClassRate capacity weight work i *
      ((startTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay) -
        startTime)
  rw [finiteGPSRemainingAfter_eq_linear_nextStep hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg]
  ring

/-- Under the same conditions, the stored service increment is the affine
cumulative service at the segment's right endpoint. -/
theorem finiteGPSBuildExecutionSegment_service_eq_linear
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).serviceIncrement i =
      finiteGPSExecutionSegmentLinearService
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay)
        (finiteGPSExecutionSegmentEndTime
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay)) i := by
  change finiteGPSServiceIncrement capacity weight work
      (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
    finiteGPSClassRate capacity weight work i *
      ((startTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay) -
        startTime)
  rw [finiteGPSServiceIncrement_eq_rate_mul_nextStep hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg]
  ring

/-- Verification predicate for adjacency of a list emitted by the concrete
runner.  This is not used to define execution: it merely records that each
following segment starts at the preceding post-batch endpoint. -/
def FiniteGPSExecutionSegmentsChainFrom
    (startTime : ℝ) (startWorkload : Class → ℝ) :
    List (FiniteGPSExecutionSegment Class) → Prop
  | [] => True
  | segment :: segments =>
      segment.startTime = startTime ∧
        segment.startWorkload = startWorkload ∧
        FiniteGPSExecutionSegmentsChainFrom
          (finiteGPSExecutionSegmentEndTime segment)
          segment.endpointWorkload segments

/-- Sum the service increments stored in a finite segment list. -/
def finiteGPSExecutionSegmentsService
    (segments : List (FiniteGPSExecutionSegment Class)) (i : Class) : ℝ :=
  (segments.map fun segment => segment.serviceIncrement i).sum

/-- Stored service is additive under concatenation of concrete segment
ledgers. -/
theorem finiteGPSExecutionSegmentsService_append
    (left right : List (FiniteGPSExecutionSegment Class)) (i : Class) :
    finiteGPSExecutionSegmentsService (left ++ right) i =
      finiteGPSExecutionSegmentsService left i +
        finiteGPSExecutionSegmentsService right i := by
  simp [finiteGPSExecutionSegmentsService]

/-- Concrete segment output paired with the existing finite gap runner's
computed result. -/
structure FiniteGPSGapSegmentHistory (Class : Type*) where
  final : FiniteGPSGapRunResult Class
  segments : List (FiniteGPSExecutionSegment Class)

/-- Record the same internal event recursion as `finiteGPSRunGap`.  Fuel
exhaustion deliberately yields no further segment, exactly as the runner
returns its current state.  Positive GPS assumptions later give the concrete
active-class fuel bound that reaches the pending batch. -/
def finiteGPSRunGapSegments
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) : List (FiniteGPSExecutionSegment Class) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let segment := finiteGPSBuildExecutionSegment capacity weight work batchWork
        currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
      if duration = nextBatchDelay then
        [segment]
      else
        segment :: finiteGPSRunGapSegments fuel capacity weight nextWork batchWork
          (currentTime + duration) (nextBatchDelay - duration)

/-- The finite segment history uses the existing runner as its final state and
the same concrete event recursion for its interval ledger. -/
def finiteGPSRunGapWithSegments
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) : FiniteGPSGapSegmentHistory Class :=
  { final := finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay
    segments := finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay }

/-- The segment ledger begins at the supplied time/workload and every later
segment begins at the preceding concrete post-batch endpoint. -/
theorem finiteGPSRunGapSegments_chainFrom
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    FiniteGPSExecutionSegmentsChainFrom currentTime work
      (finiteGPSRunGapSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay) := by
  induction fuel generalizing currentTime work nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments, FiniteGPSExecutionSegmentsChainFrom]
  | succ fuel ih =>
      unfold finiteGPSRunGapSegments
      dsimp only
      split
      · simp [FiniteGPSExecutionSegmentsChainFrom]
      · constructor
        · rfl
        constructor
        · rfl
        · simpa [finiteGPSExecutionSegmentEndTime,
            finiteGPSBuildExecutionSegment] using
            ih
              (work := finiteGPSNextEventState capacity weight work batchWork
                nextBatchDelay)
              (currentTime := currentTime +
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              (nextBatchDelay := nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)

/-- The stored segment increments telescope to precisely the existing gap
runner's service field.  This is the concrete finite identity needed to turn
the segment ledger into a later piecewise-linear cumulative-service function. -/
theorem finiteGPSRunGapSegments_service_eq_runner
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSRunGapSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay) i =
      (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).service i := by
  induction fuel generalizing currentTime work nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments, finiteGPSRunGap,
        finiteGPSExecutionSegmentsService]
  | succ fuel ih =>
      unfold finiteGPSRunGapSegments finiteGPSRunGap
      dsimp only
      split
      · simp [finiteGPSExecutionSegmentsService]
      · change
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            currentTime nextBatchDelay).serviceIncrement i +
            finiteGPSExecutionSegmentsService
              (finiteGPSRunGapSegments fuel capacity weight
                (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                batchWork
                (currentTime +
                  finiteGPSNextStepDuration capacity weight work nextBatchDelay)
                (nextBatchDelay -
                  finiteGPSNextStepDuration capacity weight work nextBatchDelay)) i =
            finiteGPSServiceIncrement capacity weight work
              (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i +
              (finiteGPSRunGap fuel capacity weight
                (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                batchWork
                (nextBatchDelay -
                  finiteGPSNextStepDuration capacity weight work nextBatchDelay)).service i
        rw [ih
          (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          (currentTime := currentTime +
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (nextBatchDelay := nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)]
        rfl

/-- The history's recorded service is exactly the finite runner's service. -/
theorem finiteGPSRunGapWithSegments_service
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSRunGapWithSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay).segments i =
      (finiteGPSRunGapWithSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay).final.service i := by
  exact finiteGPSRunGapSegments_service_eq_runner fuel capacity weight work batchWork
    currentTime nextBatchDelay i

/-- Segment history for a finite chronological batch trace. -/
structure FiniteGPSBatchSegmentHistory (Class : Type*) where
  final : FiniteGPSBatchTraceResult Class
  segments : List (FiniteGPSExecutionSegment Class)

/-- Record all concrete service intervals used by `finiteGPSRunBatchTrace`.
The same active-class fuel bound is passed to each gap as in that runner. -/
def finiteGPSRunBatchTraceSegments
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) : List ℝ →
      List (FiniteGPSExecutionSegment Class)
  | [] => []
  | t :: times =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gapSegments := finiteGPSRunGapSegments gapFuel capacity weight work
        (batchWork t) currentTime (t - currentTime)
      let gapWork := finiteGPSRunGap gapFuel capacity weight work
        (batchWork t) (t - currentTime)
      if gapWork.batchApplied = true then
        gapSegments ++ finiteGPSRunBatchTraceSegments capacity weight batchWork
          t gapWork.workload times
      else
        gapSegments

/-- The segment ledger continues past a batch exactly when the underlying
bounded gap runner reached that batch. -/
theorem finiteGPSRunBatchTraceSegments_cons_of_batchApplied
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (t : ℝ)
    (times : List ℝ)
    (hbatchApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)).batchApplied = true) :
    finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work (t :: times) =
      finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) currentTime (t - currentTime) ++
        finiteGPSRunBatchTraceSegments capacity weight batchWork t
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).workload times := by
  simp [finiteGPSRunBatchTraceSegments, hbatchApplied]

/-- If the bounded gap cannot reach its pending batch, the segment ledger
stops at the actual partial gap and does not fabricate later segments. -/
theorem finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (t : ℝ)
    (times : List ℝ)
    (hbatchNotApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)).batchApplied ≠ true) :
    finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work (t :: times) =
      finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) currentTime (t - currentTime) := by
  simp [finiteGPSRunBatchTraceSegments, hbatchNotApplied]

/-- The complete concrete interval ledger paired with the existing batch-trace
runner's final result. -/
def finiteGPSRunBatchTraceWithSegments
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (times : List ℝ) :
    FiniteGPSBatchSegmentHistory Class :=
  { final := finiteGPSRunBatchTrace capacity weight batchWork currentTime work times
    segments := finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times }

/-- The finite batch history's stored service equals the existing batch trace
runner's cumulative service. -/
theorem finiteGPSRunBatchTraceSegments_service_eq_runner
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times) i =
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).service i := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments, finiteGPSRunBatchTrace,
        finiteGPSExecutionSegmentsService]
  | cons t times ih =>
      by_cases hbatchApplied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).batchApplied = true
      · rw [finiteGPSRunBatchTraceSegments_cons_of_batchApplied
          capacity weight batchWork currentTime work t times hbatchApplied,
          finiteGPSRunBatchTrace_cons_of_batchApplied
            capacity weight batchWork currentTime work t times hbatchApplied]
        change finiteGPSExecutionSegmentsService
            (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork t) currentTime (t - currentTime) ++
              finiteGPSRunBatchTraceSegments capacity weight batchWork t
                (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                  capacity weight work (batchWork t) (t - currentTime)).workload times) i =
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).service i +
            (finiteGPSRunBatchTrace capacity weight batchWork t
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (batchWork t) (t - currentTime)).workload times).service i
        rw [finiteGPSExecutionSegmentsService_append,
          finiteGPSRunGapSegments_service_eq_runner]
        rw [ih
          (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).workload)
          (currentTime := t)]
      · rw [finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
          capacity weight batchWork currentTime work t times hbatchApplied,
          finiteGPSRunBatchTrace_cons_of_not_batchApplied
            capacity weight batchWork currentTime work t times hbatchApplied]
        exact finiteGPSRunGapSegments_service_eq_runner
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork t) currentTime (t - currentTime) i

/-- The segment ledger begins at the requested initial state within every
first gap.  A full cross-gap endpoint-chain theorem additionally needs the
runner termination hypotheses, because only then does each gap reach its
scheduled external endpoint rather than stop at exhausted fuel. -/
theorem finiteGPSRunBatchTraceSegments_firstGap_chainFrom
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (t : ℝ) (times : List ℝ) :
    FiniteGPSExecutionSegmentsChainFrom currentTime work
      (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) currentTime (t - currentTime)) := by
  exact finiteGPSRunGapSegments_chainFrom
    ((finiteGPSActiveClasses work).card + 1) capacity weight work (batchWork t)
    currentTime (t - currentTime)

/-- The batch-history wrapper inherits the exact cumulative-service identity. -/
theorem finiteGPSRunBatchTraceWithSegments_service
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ) (i : Class) :
    finiteGPSExecutionSegmentsService
      (finiteGPSRunBatchTraceWithSegments capacity weight batchWork
        currentTime work times).segments i =
      (finiteGPSRunBatchTraceWithSegments capacity weight batchWork
        currentTime work times).final.service i := by
  exact finiteGPSRunBatchTraceSegments_service_eq_runner capacity weight work batchWork
    currentTime times i

/-- The concrete interval ledger is also independent of the particular
adequate event-decision fuel budget.  This is stronger than equality of the
gap runner result: it preserves every generated segment and its exact clock
coordinates, which is what a source-labelled FCFS replay needs. -/
theorem finiteGPSRunGapSegments_eq_of_activeCard_lt
    (fuel fuel' : ℕ) {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    (currentTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel)
    (hfuel' : (finiteGPSActiveClasses work).card < fuel') :
    finiteGPSRunGapSegments fuel capacity weight work batchWork currentTime nextBatchDelay =
      finiteGPSRunGapSegments fuel' capacity weight work batchWork currentTime nextBatchDelay := by
  induction fuel generalizing fuel' work currentTime nextBatchDelay with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          exact (Nat.not_lt_zero _ hfuel').elim
      | succ fuel' =>
          by_cases hterminal :
              finiteGPSNextStepDuration capacity weight work nextBatchDelay =
                nextBatchDelay
          · simp [finiteGPSRunGapSegments, hterminal]
          · have hnext_work_nonneg : ∀ j, 0 ≤
                finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j :=
              finiteGPSNextEventState_nonneg_of_internal (batchWork := batchWork)
                hterminal
            have hresidual_nonneg : 0 ≤ nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
              exact sub_nonneg.mpr
                (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
                  nextBatchDelay)
            have hdescent := finiteGPSActiveClasses_ssubset_nextEvent_of_internal
              (batchWork := batchWork) hcapacity hweight_pos htotal_weight_le_one
              hwork_nonneg hterminal
            have hnext_card_lt_fuel :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)).card <
                    fuel := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel)
            have hnext_card_lt_fuel' :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)).card <
                    fuel' := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel')
            have htail := ih (fuel' := fuel')
              (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
              (currentTime := currentTime +
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              (nextBatchDelay := nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              hnext_work_nonneg hresidual_nonneg hnext_card_lt_fuel hnext_card_lt_fuel'
            simp only [finiteGPSRunGapSegments, if_neg hterminal]
            rw [htail]

/-- Distinct-time external trace wrapper for the concrete segment ledger. -/
def finiteGPSRunExternalBatchTraceWithSegments
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (start : ℝ) (work : Class → ℝ)
    (trace : FiniteGPSExternalBatchTrace start) : FiniteGPSBatchSegmentHistory Class :=
  finiteGPSRunBatchTraceWithSegments capacity weight batchWork start work trace.times

end

end AppliedModelingLib.Probability.Queueing
