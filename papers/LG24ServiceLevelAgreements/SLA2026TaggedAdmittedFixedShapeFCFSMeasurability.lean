import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSMeasurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentMeasurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteReplayMeasurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import Mathlib.Tactic

/-!
# Fixed-shape Borel view of the literal tagged FCFS completion scan

This adapter identifies the generic fixed-queue scalar selector with the
paper's literal `taggedAdmittedFiniteGPSFirstTagCompletion?` scan.  It remains
strictly local to one fixed queue and one finite service segment: it does not
claim Borel measurability for the random source-labelled FCFS fold or the
full diagonal response.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.Queueing

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category Omega : Type*} [Fintype Category] [DecidableEq Category]
  [MeasurableSpace Omega]

/-- The paper's literal tag scan is the generic first-key scan for the
Boolean key already used by the finite tagged response construction. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_eq_firstKeyCompletion?
    (target : Category)
    (completions : List (FiniteGPSFCFSCompletion
      (TaggedAdmittedSourceJobId Category))) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target completions =
      finiteGPSFCFSFirstKeyCompletion?
        (taggedAdmittedTargetCompletionKey target) completions := by
  induction completions with
  | nil => rfl
  | cons completion completions ih =>
      by_cases htag : completion.identifier = (target, 0)
      · simp [taggedAdmittedFiniteGPSFirstTagCompletion?,
          finiteGPSFCFSFirstKeyCompletion?, taggedAdmittedTargetCompletionKey,
          htag]
      · simp [taggedAdmittedFiniteGPSFirstTagCompletion?,
          finiteGPSFCFSFirstKeyCompletion?, taggedAdmittedTargetCompletionKey,
          htag, ih]

/-- Response obtained by applying the existing literal tagged completion scan
to the completions emitted from one fixed FCFS queue/segment shape. -/
def taggedAdmittedFixedQueueFirstTagResponseFromTrace
    (target : Category)
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))) : ℝ :=
  match taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
        availableService jobs) with
  | some completion => completion.completionTime - completion.arrivalTime
  | none => 0

/-- The direct fixed-queue scalar equals the response from the existing
literal tagged completion scan exactly. -/
theorem taggedAdmittedFixedQueueFirstTagResponse_eq_existingCompletionScan
    (target : Category)
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))) :
    finiteGPSFCFSFirstKeyCompletionResponse
      (taggedAdmittedTargetCompletionKey target)
      segmentStart classRate serviceBefore availableService jobs =
      taggedAdmittedFixedQueueFirstTagResponseFromTrace target
        segmentStart classRate serviceBefore availableService jobs := by
  rw [finiteGPSFCFSFirstKeyCompletionResponse_eq_completionTraceScan,
    taggedAdmittedFixedQueueFirstTagResponseFromTrace,
    taggedAdmittedFiniteGPSFirstTagCompletion?_eq_firstKeyCompletion?]
  simp [finiteGPSFCFSFirstKeyCompletionResponseFromTrace]
  split <;> simp_all

/-- On a fixed static queue shape, the response from the existing literal
tag-completion scan is Borel in the real segment/job coordinates.  Slot key
values are supplied as fixed shape data; no random list or full finite FCFS
selector is hidden in this statement. -/
theorem measurable_taggedAdmittedFixedQueueFirstTagResponseFromTrace_apply
    (target : Category)
    (segmentStart classRate serviceBefore availableService : Omega → ℝ)
    (hsegmentStart : Measurable segmentStart)
    (hclassRate : Measurable classRate)
    (hserviceBefore : Measurable serviceBefore)
    (havailableService : Measurable availableService)
    (jobs : List (Omega → FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category)))
    (hcoordinates : FiniteGPSFCFSFixedQueueCoordinatesMeasurable jobs)
    (hkeyShape : FiniteGPSFCFSFixedQueueKeyShape
      (taggedAdmittedTargetCompletionKey target) jobs) :
    Measurable fun omega =>
      taggedAdmittedFixedQueueFirstTagResponseFromTrace target
        (segmentStart omega) (classRate omega) (serviceBefore omega)
        (availableService omega) (jobs.map fun job => job omega) := by
  have hmeasurable := measurable_finiteGPSFCFSFirstKeyCompletionResponse_apply
    (taggedAdmittedTargetCompletionKey target)
    segmentStart classRate serviceBefore availableService
    hsegmentStart hclassRate hserviceBefore havailableService jobs
    hcoordinates hkeyShape
  have heq : (fun omega =>
      finiteGPSFCFSFirstKeyCompletionResponse
        (taggedAdmittedTargetCompletionKey target)
        (segmentStart omega) (classRate omega) (serviceBefore omega)
        (availableService omega) (jobs.map fun job => job omega)) =
      fun omega => taggedAdmittedFixedQueueFirstTagResponseFromTrace target
        (segmentStart omega) (classRate omega) (serviceBefore omega)
        (availableService omega) (jobs.map fun job => job omega) := by
    funext omega
    exact taggedAdmittedFixedQueueFirstTagResponse_eq_existingCompletionScan
      target (segmentStart omega) (classRate omega) (serviceBefore omega)
      (availableService omega) (jobs.map fun job => job omega)
  rw [heq] at hmeasurable
  exact hmeasurable

/-- Default value for totalized source-labelled GPS step access.  Its empty
endpoint batch is only an out-of-range convention; it is not a source arrival
or an execution step. -/
def taggedAdmittedFiniteGPSFCFSSegmentJobStepDefault :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  { segment := finiteGPSExecutionSegmentDefault
    endpointJobs := taggedAdmittedFCFSComputationalEndpointJobs }

/-- Totalized source-labelled access to a bounded GPS gap's generated step
list.  The underlying list remains the executable event recursion. -/
def taggedAdmittedFiniteGPSGapSegmentJobStepAt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : Nat) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) (slot : Nat) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  (taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
    fuel capacity weight work currentTime nextBatchDelay).getD slot
      taggedAdmittedFiniteGPSFCFSSegmentJobStepDefault

/-- Erasing endpoint-job data from a totalized literal source step gives
exactly the corresponding totalized segment of the generic GPS gap runner. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobStepAt_segment
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : Nat) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) (slot : Nat) :
    (taggedAdmittedFiniteGPSGapSegmentJobStepAt start horizon target z eventTime
      fuel capacity weight work currentTime nextBatchDelay slot).segment =
      finiteGPSRunGapSegmentAt fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay slot := by
  change ((taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
        fuel capacity weight work currentTime nextBatchDelay).getD slot
        taggedAdmittedFiniteGPSFCFSSegmentJobStepDefault).segment =
      (finiteGPSRunGapSegments fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay).getD slot finiteGPSExecutionSegmentDefault
  rw [← List.getD_map
    (taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
      fuel capacity weight work currentTime nextBatchDelay)
    taggedAdmittedFiniteGPSFCFSSegmentJobStepDefault
    (fun step : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category) => step.segment)]
  rw [taggedAdmittedFiniteGPSGapSegmentJobSteps_segments]
  rfl

/-- A fixed source-pattern representative defines one exact Borel GPS-gap
coordinate family.  It uses the representative's equality block as the
pending external batch; matching-pattern equality below identifies that
block with the literal source batch. -/
def taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt
    (start : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (z : TaggedAdmittedSourceGoodCarrier target) (slot : Nat) :
    FiniteGPSExecutionSegment Category :=
  finiteGPSRunGapSegmentAt ((finiteGPSActiveClasses initialWork).card + 1)
    capacity weight initialWork
    (fun k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k)
    start (taggedAdmittedSourceArrival target z.1 pivot - start) slot

/-- Every totalized segment coordinate of the fixed representative gap is
Borel on the Palm good carrier.  This is a segment-level theorem only: it
does not assert Borel measurability of source-labelled residual FCFS queues
or of a full tagged completion scan. -/
theorem finiteGPSExecutionSegmentCoordinatesMeasurable_taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt
    (start : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category)
    (capacity : ℝ) (weight initialWork : Category → ℝ) (slot : Nat) :
    FiniteGPSExecutionSegmentCoordinatesMeasurable (fun z :
      TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt
        start target pattern pivot capacity weight initialWork z slot) := by
  let eventTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
    taggedAdmittedSourceArrival target z.1 pivot
  have heventTime : Measurable eventTime :=
    measurable_taggedAdmittedSourceArrival_goodCarrier target pivot
  let blockWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
    fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
  have hblockWork : ∀ k, Measurable (fun z => blockWork z k) := by
    intro k
    exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
      target pattern pivot k
  let delay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
    eventTime z - start
  have hdelay : Measurable delay := heventTime.sub measurable_const
  simpa [taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt,
    eventTime, blockWork, delay] using
    (finiteGPSExecutionSegmentCoordinatesMeasurable_gapSegmentAt
      ((finiteGPSActiveClasses initialWork).card + 1) capacity weight
      (fun _ : TaggedAdmittedSourceGoodCarrier target => initialWork) blockWork
      (by intro k; exact measurable_const) hblockWork
      (fun _ : TaggedAdmittedSourceGoodCarrier target => start) delay
      measurable_const hdelay slot)

/-- On a matching pattern fiber, a representative's Borel gap coordinate is
literally the segment coordinate of the source-labelled FCFS job-step list.
The proof uses the finite source ledger and equality-block work identity, not
any naming convention or a hidden no-ties assumption. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobStepAt_segment_eq_taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt_of_matches
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ script.pivots)
    (capacity : ℝ) (weight initialWork : Category → ℝ) (slot : Nat)
    (hmatches : pattern.Matches start horizon target z.1) :
    (taggedAdmittedFiniteGPSGapSegmentJobStepAt start horizon target z.1
      (taggedAdmittedSourceArrival target z.1 pivot)
      ((finiteGPSActiveClasses initialWork).card + 1) capacity weight initialWork
      start (taggedAdmittedSourceArrival target z.1 pivot - start) slot).segment =
      taggedAdmittedSourceArrivalPatternRepresentativeGapSegmentAt
        start target pattern pivot capacity weight initialWork z slot := by
  rw [taggedAdmittedFiniteGPSGapSegmentJobStepAt_segment]
  have hpivotLabel : pivot ∈ pattern.labels := script.pivot_mem pivot hpivot
  have hbatch : taggedAdmittedBatchAt start horizon target z.1
      (taggedAdmittedSourceArrival target z.1 pivot) =
      fun k => taggedAdmittedSourceArrivalPatternBlockWork target z.1
        pattern pivot k := by
    funext k
    exact (taggedAdmittedSourceArrivalPatternBlockWork_eq_taggedAdmittedBatchAt_of_matches
      start horizon target z.1 pattern hmatches pivot hpivotLabel k).symm
  rw [hbatch]
  rfl

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
