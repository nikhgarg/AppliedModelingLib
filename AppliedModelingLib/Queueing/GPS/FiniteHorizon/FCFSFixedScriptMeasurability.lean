import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSConsumeSkeleton
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSPaddedReplayMeasurability
import Mathlib.Tactic

/-!
# Borel fixed-script GPS/FCFS replay

This module supplies the finite coordinate induction missing from the generic
padded GPS/FCFS replay interface.  A script fixes the finite segment layout,
endpoint job order, and a completed-head count for every active slot.  Queue
identifiers are not treated as measurable: every tracked queue coordinate
carries an explicit static key Boolean, which is preserved by partial service
and removed only when its head is completed.

The executable transition remains `finiteGPSFCFSApplySegment`.  The fixed
count data merely partitions its finite FCFS comparisons into Borel fibers.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId Omega : Type*} [Fintype Class] [DecidableEq Class]
  [MeasurableSpace Omega]

/-- One coordinate job together with a source-fixed Boolean key value.  The
pointwise equality is explicit, so no measurable-space structure on `JobId`
or on identifiers is needed. -/
structure FiniteGPSFCFSFixedKeyJobCoordinate
    (Omega JobId : Type*) (key : JobId → Bool) where
  job : Omega → FiniteGPSFCFSJob JobId
  keyValue : Bool
  keyValue_eq : ∀ omega, key (job omega).identifier = keyValue

/-- Erase the static key annotation when passing a fixed queue to the existing
FCFS coordinate API. -/
def FiniteGPSFCFSFixedKeyJobCoordinate.erase
    {key : JobId → Bool}
    (coordinate : FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key) :
    Omega → FiniteGPSFCFSJob JobId :=
  coordinate.job

/-- The coordinate list underlying a keyed fixed queue. -/
def FiniteGPSFCFSFixedKeyQueue.erase
    {key : JobId → Bool}
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    List (Omega → FiniteGPSFCFSJob JobId) :=
  queue.map FiniteGPSFCFSFixedKeyJobCoordinate.erase

@[simp]
theorem FiniteGPSFCFSFixedKeyQueue.erase_nil {key : JobId → Bool} :
    FiniteGPSFCFSFixedKeyQueue.erase
      (key := key) ([] : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) = [] := rfl

@[simp]
theorem FiniteGPSFCFSFixedKeyQueue.erase_cons
    {key : JobId → Bool}
    (coordinate : FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    FiniteGPSFCFSFixedKeyQueue.erase (coordinate :: queue) =
      coordinate.job :: FiniteGPSFCFSFixedKeyQueue.erase queue := rfl

/-- Real-coordinate Borelness for a keyed static queue. -/
def FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
    {key : JobId → Bool}
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) : Prop :=
  FiniteGPSFCFSFixedQueueCoordinatesMeasurable
    (FiniteGPSFCFSFixedKeyQueue.erase queue)

/-- A keyed static queue automatically satisfies the older fixed-key-shape
interface used by the scalar local response theorem. -/
theorem FiniteGPSFCFSFixedKeyQueue.keyShape
    (key : JobId → Bool)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    FiniteGPSFCFSFixedQueueKeyShape key (FiniteGPSFCFSFixedKeyQueue.erase queue) := by
  intro coordinate hcoordinate
  rcases List.mem_map.mp hcoordinate with ⟨keyedCoordinate, hmem, rfl⟩
  exact ⟨keyedCoordinate.keyValue, keyedCoordinate.keyValue_eq⟩

/-- Fixed-count consumption at the coordinate level, retaining static key
annotations on every residual job. -/
def finiteGPSFCFSConsumeByCountKeyedCoordinates
    {key : JobId → Bool} (availableService : Omega → ℝ) : Nat →
      List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key) →
        List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)
  | 0, [] => []
  | 0, coordinate :: queue =>
      { job := fun omega => { coordinate.job omega with
          residualWork := (coordinate.job omega).residualWork - availableService omega }
        keyValue := coordinate.keyValue
        keyValue_eq := by
          intro omega
          simpa using coordinate.keyValue_eq omega } :: queue
  | completedCount + 1, [] => []
  | completedCount + 1, coordinate :: queue =>
      finiteGPSFCFSConsumeByCountKeyedCoordinates
        (fun omega => availableService omega - (coordinate.job omega).residualWork)
        completedCount queue

/-- Erasing key annotations commutes with fixed-count coordinate consumption. -/
theorem finiteGPSFCFSConsumeByCountKeyedCoordinates_erase
    {key : JobId → Bool} (availableService : Omega → ℝ) (completedCount : Nat)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    FiniteGPSFCFSFixedKeyQueue.erase
      (finiteGPSFCFSConsumeByCountKeyedCoordinates availableService completedCount queue) =
      finiteGPSFCFSConsumeByCountCoordinates availableService completedCount
        (FiniteGPSFCFSFixedKeyQueue.erase queue) := by
  induction completedCount generalizing availableService queue with
  | zero =>
      cases queue with
      | nil => rfl
      | cons coordinate queue =>
          simp [finiteGPSFCFSConsumeByCountKeyedCoordinates,
            finiteGPSFCFSConsumeByCountCoordinates,
            FiniteGPSFCFSFixedKeyQueue.erase,
            FiniteGPSFCFSFixedKeyJobCoordinate.erase]
  | succ completedCount ih =>
      cases queue with
      | nil => rfl
      | cons coordinate queue =>
          simpa [finiteGPSFCFSConsumeByCountKeyedCoordinates,
            finiteGPSFCFSConsumeByCountCoordinates,
            FiniteGPSFCFSFixedKeyQueue.erase] using
            ih (availableService := fun omega =>
              availableService omega - (coordinate.job omega).residualWork) (queue := queue)

/-- Fixed-count consumption preserves Borel real coordinates of a keyed
static queue. -/
theorem finiteGPSFCFSConsumeByCountKeyedCoordinates_measurable
    {key : JobId → Bool}
    (availableService : Omega → ℝ) (havailableService : Measurable availableService)
    (completedCount : Nat)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (hcoordinates : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable queue) :
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      (finiteGPSFCFSConsumeByCountKeyedCoordinates availableService completedCount queue) := by
  rw [FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
    finiteGPSFCFSConsumeByCountKeyedCoordinates_erase]
  exact finiteGPSFCFSConsumeByCountCoordinates_measurable availableService
    havailableService completedCount (FiniteGPSFCFSFixedKeyQueue.erase queue) hcoordinates

/-- The finite static predicate saying whether a completed prefix contains a
keyed job.  It depends only on key-vector data and completed-head count. -/
def finiteGPSFCFSConsumeByCountKeyedHasKey {key : JobId → Bool} : Nat →
    List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key) → Bool
  | 0, _ => false
  | _completedCount + 1, [] => false
  | completedCount + 1, coordinate :: queue =>
      coordinate.keyValue || finiteGPSFCFSConsumeByCountKeyedHasKey completedCount queue

/-- On a matching fixed-count branch, the concrete completed-job scan contains
a keyed job exactly when the static completed-prefix key predicate is true. -/
theorem finiteGPSFCFSFirstKeyCompletion?_ne_none_iff_keyedHasKey_of_matches
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore : ℝ)
    (availableService : ℝ) (completedCount : Nat)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (omega : Omega)
    (hmatches : FiniteGPSFCFSConsumeByCountMatches availableService completedCount
      ((FiniteGPSFCFSFixedKeyQueue.erase queue).map fun coordinate => coordinate omega)) :
    finiteGPSFCFSFirstKeyCompletion? key
      (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
        availableService ((FiniteGPSFCFSFixedKeyQueue.erase queue).map
          fun coordinate => coordinate omega)) ≠ none ↔
      finiteGPSFCFSConsumeByCountKeyedHasKey completedCount queue = true := by
  induction completedCount generalizing availableService serviceBefore queue with
  | zero =>
      cases queue with
      | nil =>
          simp [FiniteGPSFCFSFixedKeyQueue.erase,
            finiteGPSFCFSFirstKeyCompletion?,
            finiteGPSFCFSConsumeByCountKeyedHasKey]
      | cons coordinate queue =>
          have hpartial : availableService < (coordinate.job omega).residualWork := by
            simpa [FiniteGPSFCFSConsumeByCountMatches,
              FiniteGPSFCFSFixedKeyQueue.erase,
              FiniteGPSFCFSFixedKeyJobCoordinate.erase] using hmatches
          have hcompleted : finiteGPSFCFSCompletedJobsFrom segmentStart classRate
              serviceBefore availableService
              ((FiniteGPSFCFSFixedKeyQueue.erase (coordinate :: queue)).map
                fun later => later omega) = [] := by
            change finiteGPSFCFSCompletedJobsFrom segmentStart classRate
              serviceBefore availableService (coordinate.job omega ::
                (FiniteGPSFCFSFixedKeyQueue.erase queue).map
                  fun later => later omega) = []
            rw [finiteGPSFCFSCompletedJobsFrom_eq_nil_of_partial_head
              segmentStart classRate serviceBefore availableService
              (coordinate.job omega) ((FiniteGPSFCFSFixedKeyQueue.erase queue).map
                fun later => later omega) hpartial]
          rw [hcompleted]
          simp [finiteGPSFCFSFirstKeyCompletion?,
            finiteGPSFCFSConsumeByCountKeyedHasKey]
  | succ completedCount ih =>
      cases queue with
      | nil =>
          simp [FiniteGPSFCFSFixedKeyQueue.erase,
            FiniteGPSFCFSConsumeByCountMatches] at hmatches
      | cons coordinate queue =>
          have hcomplete : ¬ availableService < (coordinate.job omega).residualWork := by
            exact hmatches.1
          have htail := ih
            (availableService := availableService - (coordinate.job omega).residualWork)
            (serviceBefore := serviceBefore + (coordinate.job omega).residualWork)
            (queue := queue) hmatches.2
          change finiteGPSFCFSFirstKeyCompletion? key
              (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
                availableService (coordinate.job omega ::
                  (FiniteGPSFCFSFixedKeyQueue.erase queue).map
                    (fun later => later omega))) ≠ none ↔
            finiteGPSFCFSConsumeByCountKeyedHasKey (completedCount + 1)
              (coordinate :: queue) = true
          rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segmentStart classRate serviceBefore availableService
            (coordinate.job omega) ((FiniteGPSFCFSFixedKeyQueue.erase queue).map
              fun later => later omega) hcomplete]
          cases hkey : coordinate.keyValue with
          | false =>
              simpa [finiteGPSFCFSFirstKeyCompletion?,
                finiteGPSFCFSConsumeByCountKeyedHasKey,
                coordinate.keyValue_eq omega, hkey] using htail
          | true =>
              simp [finiteGPSFCFSFirstKeyCompletion?,
                finiteGPSFCFSConsumeByCountKeyedHasKey,
                coordinate.keyValue_eq omega, hkey]

/-- Evaluating a keyed coordinate residual queue agrees with the executable
FCFS consumer on its matching completed-count fiber. -/
theorem finiteGPSFCFSConsumeByCountKeyedCoordinates_eval_eq_consume_of_matches
    {key : JobId → Bool}
    (availableService : Omega → ℝ) (completedCount : Nat)
    (queue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) (omega : Omega)
    (hmatches : FiniteGPSFCFSConsumeByCountMatches (availableService omega)
      completedCount ((FiniteGPSFCFSFixedKeyQueue.erase queue).map
        fun coordinate => coordinate omega)) :
    (FiniteGPSFCFSFixedKeyQueue.erase
      (finiteGPSFCFSConsumeByCountKeyedCoordinates availableService completedCount queue)).map
        (fun coordinate => coordinate omega) =
      finiteGPSFCFSConsume (availableService omega)
        ((FiniteGPSFCFSFixedKeyQueue.erase queue).map fun coordinate => coordinate omega) := by
  rw [finiteGPSFCFSConsumeByCountKeyedCoordinates_erase]
  exact finiteGPSFCFSConsumeByCountCoordinates_eval_eq_consume_of_matches
    availableService completedCount (FiniteGPSFCFSFixedKeyQueue.erase queue) omega hmatches

/-- Erasing static key annotations commutes with appending fixed queue
coordinates. -/
theorem FiniteGPSFCFSFixedKeyQueue.erase_append
    {key : JobId → Bool}
    (left right : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    FiniteGPSFCFSFixedKeyQueue.erase (left ++ right) =
      FiniteGPSFCFSFixedKeyQueue.erase left ++
        FiniteGPSFCFSFixedKeyQueue.erase right := by
  simp [FiniteGPSFCFSFixedKeyQueue.erase]

/-- Borel real coordinates are preserved by appending two keyed static
queues. -/
theorem FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable_append
    {key : JobId → Bool}
    (left right : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (hleft : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable left)
    (hright : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable right) :
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable (left ++ right) := by
  constructor
  · intro coordinate hcoordinate
    rw [FiniteGPSFCFSFixedKeyQueue.erase_append] at hcoordinate
    rcases List.mem_append.mp hcoordinate with hleftMem | hrightMem
    · exact hleft.1 coordinate hleftMem
    · exact hright.1 coordinate hrightMem
  · intro coordinate hcoordinate
    rw [FiniteGPSFCFSFixedKeyQueue.erase_append] at hcoordinate
    rcases List.mem_append.mp hcoordinate with hleftMem | hrightMem
    · exact hleft.2 coordinate hleftMem
    · exact hright.2 coordinate hrightMem

/-- One finite literal script slot fixes the segment coordinate and ordered
endpoint-job coordinates.  The tracked endpoint queue is additionally paired
with a finite static key vector. -/
structure FiniteGPSFCFSFixedScriptSlot
    (Class Omega JobId : Type*) (key : JobId → Bool) where
  segment : Omega → FiniteGPSExecutionSegment Class
  endpointJobs : Class → List (Omega → FiniteGPSFCFSJob JobId)
  trackedEndpointJobs : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)
  active : Bool

/-- A fixed discrete FCFS branch augments one literal script slot by the
number of completed FCFS heads in its active service segment. -/
structure FiniteGPSFCFSFixedScriptSkeletonSlot
    (Class Omega JobId : Type*) (key : JobId → Bool) where
  scriptSlot : FiniteGPSFCFSFixedScriptSlot Class Omega JobId key
  completedCount : Nat

/-- The literal segment/job step evaluated from one fixed script slot. -/
def FiniteGPSFCFSFixedScriptSkeletonSlot.step
    {key : JobId → Bool}
    (slot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key)
    (omega : Omega) : FiniteGPSFCFSSegmentJobStep Class JobId :=
  { segment := slot.scriptSlot.segment omega
    endpointJobs := { jobs := fun i =>
      (slot.scriptSlot.endpointJobs i).map fun job => job omega } }

/-- The tracked endpoint coordinates are exactly the tracked component of the
literal endpoint-job step.  This remains explicit because the tracked class is
chosen by the consuming theorem. -/
def FiniteGPSFCFSFixedScriptSkeletonSlot.TrackedEndpointCompatible
    {key : JobId → Bool} (trackedClass : Class)
    (slot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key) : Prop :=
  slot.scriptSlot.endpointJobs trackedClass =
    FiniteGPSFCFSFixedKeyQueue.erase slot.scriptSlot.trackedEndpointJobs

/-- The Borel real-coordinate requirements for one fixed script slot. -/
def FiniteGPSFCFSFixedScriptSkeletonSlot.CoordinatesMeasurable
    {key : JobId → Bool} (trackedClass : Class)
    (slot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key) : Prop :=
  FiniteGPSExecutionSegmentCoordinatesMeasurable slot.scriptSlot.segment ∧
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      slot.scriptSlot.trackedEndpointJobs

/-- Coordinate residual queue after one fixed script slot.  An inactive slot
does not consume service or append endpoint work, matching the padded literal
step list below. -/
def FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue
    {key : JobId → Bool} (trackedClass : Class)
    (slot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key) :=
  if slot.scriptSlot.active = true then
    finiteGPSFCFSConsumeByCountKeyedCoordinates
      (fun omega => (slot.scriptSlot.segment omega).serviceIncrement trackedClass)
      slot.completedCount preQueue ++ slot.scriptSlot.trackedEndpointJobs
  else preQueue

/-- The literal finite step sequence associated with a fixed padded script.
Inactive skeleton slots are omitted, exactly as they are skipped by
`finiteGPSFCFSPaddedReplayMatchesFrom`. -/
def finiteGPSFCFSFixedScriptSteps
    {key : JobId → Bool} :
    List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key) →
      Omega → List (FiniteGPSFCFSSegmentJobStep Class JobId)
  | [], _ => []
  | slot :: slots, omega =>
      if slot.scriptSlot.active = true then
        slot.step omega :: finiteGPSFCFSFixedScriptSteps slots omega
      else finiteGPSFCFSFixedScriptSteps slots omega

/-- Fixed-script evaluation respects literal list concatenation.  This is the
composition law used to join a source-labelled finite prefix to a separately
constructed source-empty horizon fence while retaining one global FCFS replay.
-/
theorem finiteGPSFCFSFixedScriptSteps_append
    {key : JobId → Bool}
    (left right : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (omega : Omega) :
    finiteGPSFCFSFixedScriptSteps (left ++ right) omega =
      finiteGPSFCFSFixedScriptSteps left omega ++
        finiteGPSFCFSFixedScriptSteps right omega := by
  induction left with
  | nil =>
      rfl
  | cons slot left ih =>
      simp only [List.cons_append, finiteGPSFCFSFixedScriptSteps]
      cases hactive : slot.scriptSlot.active with
      | false =>
          simpa [hactive] using ih
      | true =>
          simp [hactive, ih]

/-- The real branch predicate for a fixed script.  The only random branch test
is the finite FCFS comparison at an active slot. -/
def finiteGPSFCFSFixedScriptBranchMatches
    {key : JobId → Bool} (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key) → Omega → Prop
  | [], _ => True
  | slot :: slots, omega =>
      if slot.scriptSlot.active = true then
        FiniteGPSFCFSConsumeByCountMatches
          ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
          slot.completedCount
          ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
            fun coordinate => coordinate omega) ∧
          finiteGPSFCFSFixedScriptBranchMatches trackedClass
            (slot.nextQueue trackedClass preQueue) slots omega
      else finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue slots omega

/-- Construct the fixed padded replay slots whose prequeues are generated from
the coordinate FCFS recurrence.  `keyCompletes` is computed solely from the
static completed-prefix key vector. -/
def finiteGPSFCFSFixedScriptReplaySlots
    (key : JobId → Bool) (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) :
    List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key) →
      List (FiniteGPSFCFSPaddedReplaySlot Class JobId Omega)
  | [] => []
  | slot :: slots =>
      { segment := slot.scriptSlot.segment
        preQueue := FiniteGPSFCFSFixedKeyQueue.erase preQueue
        active := slot.scriptSlot.active
        keyCompletes := if slot.scriptSlot.active = true then
          finiteGPSFCFSConsumeByCountKeyedHasKey slot.completedCount preQueue
        else false } ::
        finiteGPSFCFSFixedScriptReplaySlots key trackedClass
          (slot.nextQueue trackedClass preQueue) slots

/-- The coordinate queue generated after one fixed script slot is Borel when
the current queue and that slot's real coordinates are Borel. -/
theorem FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue_measurable
    {key : JobId → Bool} (trackedClass : Class)
    (slot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (hslot : slot.CoordinatesMeasurable trackedClass)
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue) :
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      (slot.nextQueue trackedClass preQueue) := by
  cases hactive : slot.scriptSlot.active with
  | false =>
      simpa [FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue, hactive] using hpreQueue
  | true =>
      have hservice : Measurable (fun omega =>
          (slot.scriptSlot.segment omega).serviceIncrement trackedClass) :=
        hslot.1.2.2.2.2.1 trackedClass
      have hconsumed : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
          (finiteGPSFCFSConsumeByCountKeyedCoordinates
            (fun omega => (slot.scriptSlot.segment omega).serviceIncrement trackedClass)
            slot.completedCount preQueue) :=
        finiteGPSFCFSConsumeByCountKeyedCoordinates_measurable
          (fun omega => (slot.scriptSlot.segment omega).serviceIncrement trackedClass)
          hservice slot.completedCount preQueue hpreQueue
      simpa [FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue, hactive] using
        (FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable_append _ _ hconsumed hslot.2)

/-- Every fixed completed-count script branch is a Borel fiber.  The proof is
a finite induction over the literal padded layout; no list-valued random
measurability is assumed. -/
theorem measurableSet_finiteGPSFCFSFixedScriptBranchMatches
    {key : JobId → Bool} (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (hcoordinates : ∀ slot ∈ slots, slot.CoordinatesMeasurable trackedClass) :
    MeasurableSet {omega |
      finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue slots omega} := by
  induction slots generalizing preQueue with
  | nil =>
      simp [finiteGPSFCFSFixedScriptBranchMatches]
  | cons slot slots ih =>
      have hslot : slot.CoordinatesMeasurable trackedClass :=
        hcoordinates slot (by simp)
      have htailCoordinates : ∀ later ∈ slots,
          later.CoordinatesMeasurable trackedClass := by
        intro later hlater
        exact hcoordinates later (by simp [hlater])
      cases hactive : slot.scriptSlot.active with
      | false =>
          simpa [finiteGPSFCFSFixedScriptBranchMatches, hactive] using
            ih (preQueue := preQueue) hpreQueue htailCoordinates
      | true =>
          have hservice : Measurable (fun omega =>
              (slot.scriptSlot.segment omega).serviceIncrement trackedClass) :=
            hslot.1.2.2.2.2.1 trackedClass
          have hbranch : MeasurableSet {omega |
              FiniteGPSFCFSConsumeByCountMatches
                ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                slot.completedCount
                ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                  fun coordinate => coordinate omega)} :=
            measurableSet_finiteGPSFCFSConsumeByCountMatches
              (fun omega => (slot.scriptSlot.segment omega).serviceIncrement trackedClass)
              hservice slot.completedCount
              (FiniteGPSFCFSFixedKeyQueue.erase preQueue) hpreQueue
          have hnextQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
              (slot.nextQueue trackedClass preQueue) :=
            slot.nextQueue_measurable trackedClass preQueue hslot hpreQueue
          have htail := ih (preQueue := slot.nextQueue trackedClass preQueue)
            hnextQueue htailCoordinates
          have hset : {omega |
              finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue
                (slot :: slots) omega} =
              {omega | FiniteGPSFCFSConsumeByCountMatches
                ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                slot.completedCount
                ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                  fun coordinate => coordinate omega)} ∩
                {omega | finiteGPSFCFSFixedScriptBranchMatches trackedClass
                  (slot.nextQueue trackedClass preQueue) slots omega} := by
            ext omega
            simp [finiteGPSFCFSFixedScriptBranchMatches, hactive]
          rw [hset]
          exact hbranch.inter htail

/-- Every literal finite fixed script lies on some completed-count branch at
each sample point.  The witness is allowed to depend on that point; later
countable gluing ranges over the resulting finite static count lists. -/
theorem exists_finiteGPSFCFSFixedScriptBranchMatches
    {key : JobId → Bool} (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSlot Class Omega JobId key))
    (omega : Omega) :
    ∃ skeletonSlots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key),
      skeletonSlots.map (fun skeletonSlot => skeletonSlot.scriptSlot) = slots ∧
        finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue skeletonSlots omega := by
  induction slots generalizing preQueue with
  | nil =>
      exact ⟨[], rfl, trivial⟩
  | cons slot slots ih =>
      cases hactive : slot.active with
      | false =>
          rcases ih (preQueue := preQueue) with ⟨skeletonSlots, hslots, hmatches⟩
          let skeletonSlot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key :=
            { scriptSlot := slot, completedCount := 0 }
          refine ⟨skeletonSlot :: skeletonSlots, ?_, ?_⟩
          · simpa [skeletonSlot] using congrArg (List.cons slot) hslots
          · simpa [finiteGPSFCFSFixedScriptBranchMatches, skeletonSlot, hactive] using hmatches
      | true =>
          rcases exists_finiteGPSFCFSConsumeByCountMatches
              ((slot.segment omega).serviceIncrement trackedClass)
              ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                fun coordinate => coordinate omega) with
            ⟨completedCount, hcount⟩
          let skeletonSlot : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key :=
            { scriptSlot := slot, completedCount := completedCount }
          let nextQueue := skeletonSlot.nextQueue trackedClass preQueue
          rcases ih (preQueue := nextQueue) with ⟨skeletonSlots, hslots, hmatches⟩
          refine ⟨skeletonSlot :: skeletonSlots, ?_, ?_⟩
          · simpa [skeletonSlot] using congrArg (List.cons slot) hslots
          · have hhead : FiniteGPSFCFSConsumeByCountMatches
                ((slot.segment omega).serviceIncrement trackedClass)
                completedCount
                ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                  fun coordinate => coordinate omega) := hcount
            simpa [finiteGPSFCFSFixedScriptBranchMatches, skeletonSlot, nextQueue,
              hactive] using And.intro hhead hmatches

/-- On a completed-count branch, the coordinate recurrence is exactly the
literal FCFS run of the fixed script.  In particular, its generated padded
replay slots satisfy the existing `MatchesFrom` relation. -/
theorem finiteGPSFCFSFixedScriptBranchMatches_implies_paddedReplayMatchesFrom
    (key : JobId → Bool) (trackedClass : Class)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (omega : Omega)
    (hinitial : initial.residualJobs trackedClass =
      (FiniteGPSFCFSFixedKeyQueue.erase preQueue).map fun coordinate => coordinate omega)
    (hendpoint : ∀ slot ∈ slots, slot.TrackedEndpointCompatible trackedClass)
    (hbranch : finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue slots omega) :
    finiteGPSFCFSPaddedReplayMatchesFrom key trackedClass omega initial
      (finiteGPSFCFSFixedScriptSteps slots omega)
      (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue slots) := by
  induction slots generalizing initial preQueue with
  | nil =>
      simp [finiteGPSFCFSFixedScriptSteps,
        finiteGPSFCFSFixedScriptReplaySlots,
        finiteGPSFCFSPaddedReplayMatchesFrom]
  | cons slot slots ih =>
      have hslotEndpoint : slot.TrackedEndpointCompatible trackedClass :=
        hendpoint slot (by simp)
      have htailEndpoint : ∀ later ∈ slots,
          later.TrackedEndpointCompatible trackedClass := by
        intro later hlater
        exact hendpoint later (by simp [hlater])
      cases hactive : slot.scriptSlot.active with
      | false =>
          have hnextQueue : slot.nextQueue trackedClass preQueue = preQueue := by
            simp [FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue, hactive]
          have htailBranch : finiteGPSFCFSFixedScriptBranchMatches trackedClass
              preQueue slots omega := by
            simpa [finiteGPSFCFSFixedScriptBranchMatches, hactive] using hbranch
          have htailMatch := ih (initial := initial) (preQueue := preQueue)
            hinitial htailEndpoint htailBranch
          cases hsteps : finiteGPSFCFSFixedScriptSteps slots omega with
          | nil =>
              simpa [finiteGPSFCFSFixedScriptSteps,
                finiteGPSFCFSFixedScriptReplaySlots,
                finiteGPSFCFSPaddedReplayMatchesFrom, hactive, hsteps, hnextQueue] using htailMatch
          | cons actual actualSteps =>
              simpa [finiteGPSFCFSFixedScriptSteps,
                finiteGPSFCFSFixedScriptReplaySlots,
                finiteGPSFCFSPaddedReplayMatchesFrom, hactive, hsteps, hnextQueue] using htailMatch
      | true =>
          have hheadAndTail :
              FiniteGPSFCFSConsumeByCountMatches
                ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                slot.completedCount
                ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                  fun coordinate => coordinate omega) ∧
                finiteGPSFCFSFixedScriptBranchMatches trackedClass
                  (slot.nextQueue trackedClass preQueue) slots omega := by
            simpa [finiteGPSFCFSFixedScriptBranchMatches, hactive] using hbranch
          rcases hheadAndTail with ⟨hcount, htailBranch⟩
          have hkeyCompletes :
              finiteGPSFCFSConsumeByCountKeyedHasKey slot.completedCount preQueue = true ↔
                finiteGPSFCFSFirstKeyCompletion? key
                  (finiteGPSFCFSCompletedJobsInSegment (slot.scriptSlot.segment omega)
                    trackedClass (initial.residualJobs trackedClass)) ≠ none := by
            rw [hinitial]
            simpa [finiteGPSFCFSCompletedJobsInSegment,
              finiteGPSFCFSCompletedJobs] using
              (finiteGPSFCFSFirstKeyCompletion?_ne_none_iff_keyedHasKey_of_matches
                key (slot.scriptSlot.segment omega).startTime
                ((slot.scriptSlot.segment omega).classRate trackedClass) 0
                ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                slot.completedCount preQueue omega hcount).symm
          have hconsume :
              (FiniteGPSFCFSFixedKeyQueue.erase
                (finiteGPSFCFSConsumeByCountKeyedCoordinates
                  (fun sample =>
                    (slot.scriptSlot.segment sample).serviceIncrement trackedClass)
                  slot.completedCount preQueue)).map
                  (fun coordinate => coordinate omega) =
                finiteGPSFCFSConsume
                  ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                  ((FiniteGPSFCFSFixedKeyQueue.erase preQueue).map
                    fun coordinate => coordinate omega) :=
            finiteGPSFCFSConsumeByCountKeyedCoordinates_eval_eq_consume_of_matches
              (fun sample =>
                (slot.scriptSlot.segment sample).serviceIncrement trackedClass)
              slot.completedCount preQueue omega hcount
          have hendpointEval :
              (slot.scriptSlot.endpointJobs trackedClass).map (fun job => job omega) =
                (FiniteGPSFCFSFixedKeyQueue.erase
                  slot.scriptSlot.trackedEndpointJobs).map
                    (fun coordinate => coordinate omega) := by
            rw [hslotEndpoint]
          have hnextInitial :
              (finiteGPSFCFSApplySegment initial (slot.step omega).segment
                (slot.step omega).endpointJobs).residualJobs trackedClass =
                (FiniteGPSFCFSFixedKeyQueue.erase
                  (slot.nextQueue trackedClass preQueue)).map
                    (fun coordinate => coordinate omega) := by
            change finiteGPSFCFSConsume
                ((slot.scriptSlot.segment omega).serviceIncrement trackedClass)
                (initial.residualJobs trackedClass) ++
                (slot.scriptSlot.endpointJobs trackedClass).map (fun job => job omega) =
              (FiniteGPSFCFSFixedKeyQueue.erase
                (slot.nextQueue trackedClass preQueue)).map
                  (fun coordinate => coordinate omega)
            rw [hinitial, hendpointEval]
            simp only [FiniteGPSFCFSFixedScriptSkeletonSlot.nextQueue, hactive,
              ↓reduceIte, FiniteGPSFCFSFixedKeyQueue.erase_append, List.map_append]
            rw [hconsume]
          have hslotMatch :
              ({ segment := slot.scriptSlot.segment
                 preQueue := FiniteGPSFCFSFixedKeyQueue.erase preQueue
                 active := slot.scriptSlot.active
                 keyCompletes := if slot.scriptSlot.active = true then
                   finiteGPSFCFSConsumeByCountKeyedHasKey slot.completedCount preQueue
                 else false } : FiniteGPSFCFSPaddedReplaySlot Class JobId Omega).Matches
                key trackedClass initial (slot.step omega) omega := by
            constructor
            · rfl
            constructor
            · exact hinitial
            · simpa [finiteGPSFCFSFixedScriptReplaySlots, hactive] using hkeyCompletes
          have htailMatch := ih
            (initial := finiteGPSFCFSApplySegment initial (slot.step omega).segment
              (slot.step omega).endpointJobs)
            (preQueue := slot.nextQueue trackedClass preQueue)
            hnextInitial htailEndpoint htailBranch
          simpa [finiteGPSFCFSFixedScriptSteps,
            finiteGPSFCFSFixedScriptReplaySlots,
            finiteGPSFCFSPaddedReplayMatchesFrom, hactive] using
            And.intro hslotMatch htailMatch

/-- Every generated replay slot has Borel real coordinates and a static key
shape whenever the fixed script and its initial tracked queue do. -/
theorem finiteGPSFCFSFixedScriptReplaySlots_coordinatesMeasurable
    (key : JobId → Bool) (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (hcoordinates : ∀ slot ∈ slots, slot.CoordinatesMeasurable trackedClass) :
    ∀ replaySlot ∈ finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue slots,
      replaySlot.CoordinatesMeasurable key trackedClass := by
  induction slots generalizing preQueue with
  | nil =>
      simp [finiteGPSFCFSFixedScriptReplaySlots]
  | cons slot slots ih =>
      have hslot : slot.CoordinatesMeasurable trackedClass :=
        hcoordinates slot (by simp)
      have htailCoordinates : ∀ later ∈ slots,
          later.CoordinatesMeasurable trackedClass := by
        intro later hlater
        exact hcoordinates later (by simp [hlater])
      have hnextQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
          (slot.nextQueue trackedClass preQueue) :=
        slot.nextQueue_measurable trackedClass preQueue hslot hpreQueue
      intro replaySlot hmem
      simp only [finiteGPSFCFSFixedScriptReplaySlots] at hmem
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst replaySlot
        exact ⟨hslot.1, hpreQueue,
          FiniteGPSFCFSFixedKeyQueue.keyShape key preQueue⟩
      · exact ih (preQueue := slot.nextQueue trackedClass preQueue)
          hnextQueue htailCoordinates replaySlot htail

/-- The fixed-script padded replay response is Borel.  Its equality to the
literal FCFS completion response is supplied separately on each Borel branch
fiber below. -/
theorem measurable_finiteGPSFCFSFixedScriptReplayResponse
    (key : JobId → Bool) (trackedClass : Class)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (hcoordinates : ∀ slot ∈ slots, slot.CoordinatesMeasurable trackedClass) :
    Measurable (finiteGPSFCFSPaddedReplayResponse key trackedClass
      (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue slots)) := by
  apply measurable_finiteGPSFCFSPaddedReplayResponse key trackedClass
  exact finiteGPSFCFSFixedScriptReplaySlots_coordinatesMeasurable
    key trackedClass preQueue slots hpreQueue hcoordinates

/-- On a Borel completed-count branch, the Borel fixed-script replay response
is exactly the literal response obtained from the executable FCFS trace. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_fixedScriptReplayResponse_of_branch
    (key : JobId → Bool) (trackedClass : Class)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (slots : List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key))
    (omega : Omega)
    (hinitial : initial.residualJobs trackedClass =
      (FiniteGPSFCFSFixedKeyQueue.erase preQueue).map fun coordinate => coordinate omega)
    (hendpoint : ∀ slot ∈ slots, slot.TrackedEndpointCompatible trackedClass)
    (hbranch : finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue slots omega) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial trackedClass
        (finiteGPSFCFSFixedScriptSteps slots omega)) =
      finiteGPSFCFSPaddedReplayResponse key trackedClass
        (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue slots) omega := by
  exact finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_paddedReplayResponse_of_matches
    key trackedClass initial (finiteGPSFCFSFixedScriptSteps slots omega)
    (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue slots) omega
    (finiteGPSFCFSFixedScriptBranchMatches_implies_paddedReplayMatchesFrom
      key trackedClass initial preQueue slots omega hinitial hendpoint hbranch)

end

end AppliedModelingLib.Probability.Queueing
