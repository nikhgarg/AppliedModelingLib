import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFixedScriptMeasurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFixedShapeFCFSMeasurability
import Mathlib.Tactic

/-!
# Fixed-pattern source endpoints for the tagged GPS/FCFS replay

This adapter turns one fixed source-arrival comparison pattern and one of its
representative equality blocks into finite, ordered FCFS endpoint coordinates.
The endpoint jobs retain their literal source identifiers; their target-key
bits are explicit fixed data.  A later layer supplies finite GPS active-slot
and FCFS completed-head branch data before these coordinates are glued to the
literal variable-length execution.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.Queueing

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal source indices in one fixed pattern equality block and class.
Sorting this finite set gives the same within-class FCFS tie order used by the
literal endpoint constructor. -/
def taggedAdmittedSourceArrivalPatternBlockIndices
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (k : Category) : Finset ℤ :=
  ((pattern.tieBlock pivot).filter fun job => job.1 = k).image fun job => job.2

/-- Ordered FCFS job coordinates for one fixed pattern equality block. -/
def taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (k : Category) :
    List (TaggedAdmittedSourceGoodCarrier target →
      FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category)) :=
  ((taggedAdmittedSourceArrivalPatternBlockIndices pattern pivot k).sort
    (fun left right : ℤ => left ≤ right)).map fun n z =>
      taggedAdmittedFCFSJob target z.1 (k, n)

/-- The real coordinates of every fixed pattern-block endpoint job are Borel
on the source good carrier. -/
theorem taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates_measurable
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (k : Category) :
    FiniteGPSFCFSFixedQueueCoordinatesMeasurable
      (taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
        target pattern pivot k) := by
  constructor
  · intro coordinate hcoordinate
    simp only [taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates] at hcoordinate
    rcases List.mem_map.mp hcoordinate with ⟨n, _hn, rfl⟩
    simpa [taggedAdmittedFCFSJob] using
      (measurable_taggedAdmittedSourceArrival_goodCarrier target (k, n))
  · intro coordinate hcoordinate
    simp only [taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates] at hcoordinate
    rcases List.mem_map.mp hcoordinate with ⟨n, _hn, rfl⟩
    simpa [taggedAdmittedFCFSJob] using
      ((measurable_taggedAdmittedSourceWork target (k, n)).comp measurable_subtype_coe)

/-- Target-class pattern-block endpoint coordinates carrying explicit static
Boolean values for the distinguished source-job key. -/
def taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) :
    List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)) :=
  ((taggedAdmittedSourceArrivalPatternBlockIndices pattern pivot target).sort
    (fun left right : ℤ => left ≤ right)).map fun n =>
      { job := fun z => taggedAdmittedFCFSJob target z.1 (target, n)
        keyValue := decide ((target, n) = (target, 0))
        keyValue_eq := by
          intro z
          simp [taggedAdmittedTargetCompletionKey, taggedAdmittedFCFSJob] }

/-- Erasing the explicit key bits gives the ordinary target-class endpoint
coordinates exactly. -/
theorem taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_erase
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) :
    FiniteGPSFCFSFixedKeyQueue.erase
      (taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
        target pattern pivot) =
      taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
        target pattern pivot target := by
  simp [taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates,
    taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates,
    FiniteGPSFCFSFixedKeyQueue.erase,
    FiniteGPSFCFSFixedKeyJobCoordinate.erase]

/-- The target block's key-annotated coordinates are Borel because erasing
the finite static Boolean vector recovers the Borel real-coordinate list. -/
theorem taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_measurable
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) :
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      (taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
        target pattern pivot) := by
  rw [FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
    taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_erase]
  exact taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates_measurable
    target pattern pivot target

/-- On a matching tie-aware source pattern, the static indices of a pattern
block are exactly the literal source indices at the pivot epoch.  This is an
identifier-level equality proved from the finite source-ledger fiber; it is
used only for the pointwise executable bridge, never as a measurability
assertion about identifiers or lists. -/
theorem taggedAdmittedSourceArrivalPatternBlockIndices_eq_taggedAdmittedJobIndicesAt_of_matches
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels)
    (k : Category) :
    taggedAdmittedSourceArrivalPatternBlockIndices pattern pivot k =
      taggedAdmittedJobIndicesAt start horizon target z
        (taggedAdmittedSourceArrival target z pivot) k := by
  rw [taggedAdmittedSourceArrivalPatternBlockIndices,
    pattern.tieBlock_eq_sourceLedger_arrivalFiber
      start horizon target z hmatches pivot hpivot]
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, mem_taggedAdmittedJobIndicesAt_iff]
  constructor
  · rintro ⟨job, hmem, hindex⟩
    rcases hmem with ⟨hmem, hclass⟩
    rcases hmem with ⟨hledger, harrival⟩
    rcases job with ⟨j, m⟩
    change j = k at hclass
    change m = n at hindex
    have hj : j = k := hclass
    have hm : m = n := hindex
    subst j
    subst m
    exact ⟨(mem_taggedAdmittedSourceJobLedger_iff start horizon target z k n).mp hledger,
      harrival⟩
  · rintro ⟨hindex, harrival⟩
    refine ⟨(k, n), ?_, rfl⟩
    exact ⟨⟨(mem_taggedAdmittedSourceJobLedger_iff start horizon target z k n).mpr hindex,
      harrival⟩, rfl⟩

/-- Evaluating the fixed pattern-block FCFS coordinates gives the literal
source-labelled endpoint list on the matching-pattern fiber.  In particular,
this preserves the paper's tie order rather than replacing a source batch by
an aggregate workload. -/
theorem taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates_eval_eq_jobsAt_of_matches
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z.1)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels)
    (k : Category) :
    (taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
      target pattern pivot k).map (fun coordinate => coordinate z) =
      (taggedAdmittedFCFSJobsAt start horizon target z.1
        (taggedAdmittedSourceArrival target z.1 pivot)).jobs k := by
  unfold taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
    taggedAdmittedFCFSJobsAt
  rw [taggedAdmittedSourceArrivalPatternBlockIndices_eq_taggedAdmittedJobIndicesAt_of_matches
    start horizon target z.1 pattern hmatches pivot hpivot k]
  simp

/-- The target-class keyed endpoint coordinates evaluate to the literal
target endpoint queue on the matching-pattern fiber. -/
theorem taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_eval_eq_jobsAt_of_matches
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z.1)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels) :
    (FiniteGPSFCFSFixedKeyQueue.erase
      (taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
        target pattern pivot)).map (fun coordinate => coordinate z) =
      (taggedAdmittedFCFSJobsAt start horizon target z.1
        (taggedAdmittedSourceArrival target z.1 pivot)).jobs target := by
  rw [taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_erase]
  exact taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates_eval_eq_jobsAt_of_matches
    start horizon target z pattern hmatches pivot hpivot target

/-- The literal source-labelled gap-step list is independent of the chosen
adequate GPS event fuel.  Unlike an aggregate runner equality, this retains
the actual source identifiers and endpoint queues in every emitted step. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_activeCard_lt
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel fuel' : ℕ) {capacity nextBatchDelay : ℝ} {weight work : Category → ℝ}
    (currentTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel)
    (hfuel' : (finiteGPSActiveClasses work).card < fuel') :
    taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay =
      taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel' capacity weight work currentTime nextBatchDelay := by
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
          · simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, hterminal]
          · have hnext_work_nonneg : ∀ k, 0 ≤
                finiteGPSNextEventState capacity weight work
                  (taggedAdmittedBatchAt start horizon target z eventTime)
                  nextBatchDelay k :=
              finiteGPSNextEventState_nonneg_of_internal
                (batchWork := taggedAdmittedBatchAt start horizon target z eventTime)
                hterminal
            have hresidual_nonneg : 0 ≤ nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
              exact sub_nonneg.mpr
                (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
                  nextBatchDelay)
            have hdescent := finiteGPSActiveClasses_ssubset_nextEvent_of_internal
              (batchWork := taggedAdmittedBatchAt start horizon target z eventTime)
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hterminal
            have hnext_card_lt_fuel :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work
                    (taggedAdmittedBatchAt start horizon target z eventTime)
                    nextBatchDelay)).card < fuel := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel)
            have hnext_card_lt_fuel' :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work
                    (taggedAdmittedBatchAt start horizon target z eventTime)
                    nextBatchDelay)).card < fuel' := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel')
            have htail := ih (fuel' := fuel')
              (work := finiteGPSNextEventState capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
              (currentTime := currentTime +
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              (nextBatchDelay := nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              hnext_work_nonneg hresidual_nonneg hnext_card_lt_fuel hnext_card_lt_fuel'
            simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps, if_neg hterminal]
            rw [htail]

/-- The dynamic active-class fuel used by the executable source recursion can
be replaced by the static `Fintype.card + 1` bound.  This changes neither the
actual source-labelled step list nor its endpoint queues. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_uniformFuel
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    {capacity nextBatchDelay : ℝ} {weight work : Category → ℝ}
    (currentTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
      ((finiteGPSActiveClasses work).card + 1) capacity weight work
      currentTime nextBatchDelay =
      taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z eventTime
        (Fintype.card Category + 1) capacity weight work currentTime nextBatchDelay := by
  apply taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_activeCard_lt
    start horizon target z eventTime
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · exact hwork_nonneg
  · exact hnextBatchDelay_nonneg
  · exact Nat.lt_succ_self _
  · exact Nat.lt_succ_of_le (Finset.card_le_univ _)

/-- Finite discrete data for one padded source GPS gap slot.  `active` says
whether the literal recursive source trace contains the slot;
`endpointIsExternal` says whether that active segment reaches the pending
source batch; `completedCount` is the FCFS branch datum consumed by the
generic fixed-script replay.  None of these fields is inferred from a name or
from list-valued measurability. -/
structure TaggedAdmittedSourceGapBranchAtom where
  active : Bool
  endpointIsExternal : Bool
  completedCount : Nat

/-- Static fixed-script slots for one source-pattern gap.  The coordinate
recursion follows the executable GPS event update regardless of whether a
later branch marks a slot inactive; inactive slots are omitted only by the
fixed-script replay.  Thus this remains a padded presentation of the literal
source recursion, not a synthetic scheduler. -/
def taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ) :
    List TaggedAdmittedSourceGapBranchAtom →
      List (FiniteGPSFCFSFixedScriptSkeletonSlot Category
        (TaggedAdmittedSourceGoodCarrier target)
        (TaggedAdmittedSourceJobId Category)
        (taggedAdmittedTargetCompletionKey target))
  | [] => []
  | atom :: atoms =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        finiteGPSNextStepDuration capacity weight (work z) (nextBatchDelay z)
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun z =>
        finiteGPSNextEventState capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        currentTime z + duration z
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        nextBatchDelay z - duration z
      { scriptSlot :=
          { segment := fun z => finiteGPSBuildExecutionSegment capacity weight
              (work z) (batchWork z) (currentTime z) (nextBatchDelay z)
            endpointJobs := fun k =>
              if atom.endpointIsExternal = true then
                taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                  target pattern pivot k
              else []
            trackedEndpointJobs :=
              if atom.endpointIsExternal = true then
                taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
                  target pattern pivot
              else []
            active := atom.active }
        completedCount := atom.completedCount } ::
        taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
          target pattern pivot capacity weight nextWork nextTime remainingDelay atoms

/-- Every source-pattern fixed-script slot has Borel real coordinates when
the finite GPS input coordinates do.  The proof follows the same executable
event recurrence as the slot construction; source identifiers remain static
labels and are never given a measurable-space structure. -/
theorem taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_coordinatesMeasurable
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    ∀ slot ∈ taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms,
      slot.CoordinatesMeasurable target := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots]
  | cons atom atoms ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      have hbatchWork : ∀ k, Measurable (fun z => batchWork z k) := by
        intro k
        exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
          target pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        finiteGPSNextStepDuration capacity weight (work z) (nextBatchDelay z)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun z =>
        finiteGPSNextEventState capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      have hnextWork : ∀ k, Measurable (fun z => nextWork z k) := by
        intro k
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay k
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        currentTime z + duration z
      have hnextTime : Measurable nextTime := hcurrentTime.add hduration
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        nextBatchDelay z - duration z
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have hsegment : FiniteGPSExecutionSegmentCoordinatesMeasurable (fun z =>
          finiteGPSBuildExecutionSegment capacity weight (work z) (batchWork z)
            (currentTime z) (nextBatchDelay z)) :=
        finiteGPSExecutionSegmentCoordinatesMeasurable_build
          capacity weight work batchWork hwork hbatchWork currentTime nextBatchDelay
          hcurrentTime hnextBatchDelay
      have htracked : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
          (if atom.endpointIsExternal = true then
            taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
              target pattern pivot
          else []) := by
        cases hendpoint : atom.endpointIsExternal with
        | false =>
            simp [hendpoint, FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
              FiniteGPSFCFSFixedKeyQueue.erase,
              FiniteGPSFCFSFixedQueueCoordinatesMeasurable]
        | true =>
            simpa [hendpoint] using
              (taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_measurable
                target pattern pivot)
      let scriptSlot : FiniteGPSFCFSFixedScriptSlot Category
          (TaggedAdmittedSourceGoodCarrier target)
          (TaggedAdmittedSourceJobId Category)
          (taggedAdmittedTargetCompletionKey target) :=
        { segment := fun z => finiteGPSBuildExecutionSegment capacity weight
            (work z) (batchWork z) (currentTime z) (nextBatchDelay z)
          endpointJobs := fun k =>
            if atom.endpointIsExternal = true then
              taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                target pattern pivot k
            else []
          trackedEndpointJobs :=
            if atom.endpointIsExternal = true then
              taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
                target pattern pivot
            else []
          active := atom.active }
      let head : FiniteGPSFCFSFixedScriptSkeletonSlot Category
          (TaggedAdmittedSourceGoodCarrier target)
          (TaggedAdmittedSourceJobId Category)
          (taggedAdmittedTargetCompletionKey target) :=
        { scriptSlot := scriptSlot
          completedCount := atom.completedCount }
      have hhead : head.CoordinatesMeasurable target :=
        ⟨hsegment, htracked⟩
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) hnextWork hnextTime hremainingDelay
      intro slot hslot
      simp only [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots] at hslot
      rcases List.mem_cons.mp hslot with hslot | hslot
      · subst slot
        simpa [batchWork, duration, nextWork, nextTime, remainingDelay,
          scriptSlot, head] using hhead
      · simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using
          htail slot hslot

/-- The target endpoint component of each source-pattern script slot is
exactly the erased static keyed queue used by the generic FCFS replay. -/
theorem taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_trackedEndpointCompatible
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    ∀ slot ∈ taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms,
      slot.TrackedEndpointCompatible target := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots]
  | cons atom atoms ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        finiteGPSNextStepDuration capacity weight (work z) (nextBatchDelay z)
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun z =>
        finiteGPSNextEventState capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        currentTime z + duration z
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        nextBatchDelay z - duration z
      let scriptSlot : FiniteGPSFCFSFixedScriptSlot Category
          (TaggedAdmittedSourceGoodCarrier target)
          (TaggedAdmittedSourceJobId Category)
          (taggedAdmittedTargetCompletionKey target) :=
        { segment := fun z => finiteGPSBuildExecutionSegment capacity weight
            (work z) (batchWork z) (currentTime z) (nextBatchDelay z)
          endpointJobs := fun k =>
            if atom.endpointIsExternal = true then
              taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                target pattern pivot k
            else []
          trackedEndpointJobs :=
            if atom.endpointIsExternal = true then
              taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates
                target pattern pivot
            else []
          active := atom.active }
      let head : FiniteGPSFCFSFixedScriptSkeletonSlot Category
          (TaggedAdmittedSourceGoodCarrier target)
          (TaggedAdmittedSourceJobId Category)
          (taggedAdmittedTargetCompletionKey target) :=
        { scriptSlot := scriptSlot
          completedCount := atom.completedCount }
      have hhead : head.TrackedEndpointCompatible target := by
        cases hendpoint : atom.endpointIsExternal with
        | false =>
            simp [FiniteGPSFCFSFixedScriptSkeletonSlot.TrackedEndpointCompatible,
              head, scriptSlot, hendpoint, FiniteGPSFCFSFixedKeyQueue.erase]
        | true =>
            simpa [FiniteGPSFCFSFixedScriptSkeletonSlot.TrackedEndpointCompatible,
              head, scriptSlot, hendpoint] using
              (taggedAdmittedSourceArrivalPatternBlockTargetKeyedJobCoordinates_erase
                target pattern pivot).symm
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay)
      intro slot hslot
      simp only [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots] at hslot
      rcases List.mem_cons.mp hslot with hslot | hslot
      · subst slot
        simpa [batchWork, duration, nextWork, nextTime, remainingDelay,
          scriptSlot, head] using hhead
      · simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using
          htail slot hslot

/-- The semantic finite branch predicate for a padded source GPS gap.  It is
defined directly from the executable next-event comparison at each recursive
state.  In particular, an inactive tail is permitted only after the terminal
external event; it is not recognized by comparing a default segment to a
possibly degenerate real segment. -/
def taggedAdmittedSourceArrivalPatternGapShapeMatches
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ) :
    List TaggedAdmittedSourceGapBranchAtom →
      TaggedAdmittedSourceGoodCarrier target → Prop
  | [] => fun _ => True
  | atom :: atoms =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        finiteGPSNextStepDuration capacity weight (work z) (nextBatchDelay z)
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun z =>
        finiteGPSNextEventState capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        currentTime z + duration z
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        nextBatchDelay z - duration z
      fun z => atom.active = true ∧
        if duration z = nextBatchDelay z then
          atom.endpointIsExternal = true ∧ atoms.Forall (fun later => later.active = false)
        else atom.endpointIsExternal = false ∧
          taggedAdmittedSourceArrivalPatternGapShapeMatches
            target pattern pivot capacity weight nextWork nextTime remainingDelay atoms z

/-- Every fixed active/external source-gap branch is a Borel fiber.  The
proof is a structural recursion over event comparisons and finite static
atoms, not a claim that a variable source step list is measurable. -/
theorem measurableSet_taggedAdmittedSourceArrivalPatternGapShapeMatches
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    MeasurableSet {z |
      taggedAdmittedSourceArrivalPatternGapShapeMatches
        target pattern pivot capacity weight work currentTime nextBatchDelay atoms z} := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternGapShapeMatches]
  | cons atom atoms ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      have hbatchWork : ∀ k, Measurable (fun z => batchWork z k) := by
        intro k
        exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
          target pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        finiteGPSNextStepDuration capacity weight (work z) (nextBatchDelay z)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun z =>
        finiteGPSNextEventState capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      have hnextWork : ∀ k, Measurable (fun z => nextWork z k) := by
        intro k
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay k
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        currentTime z + duration z
      have hnextTime : Measurable nextTime := hcurrentTime.add hduration
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun z =>
        nextBatchDelay z - duration z
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have hterminal : MeasurableSet {z |
          duration z = nextBatchDelay z} :=
        measurableSet_eq_fun hduration hnextBatchDelay
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) hnextWork hnextTime hremainingDelay
      cases hactive : atom.active with
      | false =>
          have hset : {z |
              taggedAdmittedSourceArrivalPatternGapShapeMatches
                target pattern pivot capacity weight work currentTime nextBatchDelay
                  (atom :: atoms) z} = ∅ := by
            ext z
            simp [taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork,
              duration, nextWork, nextTime, remainingDelay, hactive]
          rw [hset]
          exact MeasurableSet.empty
      | true =>
          cases hexternal : atom.endpointIsExternal with
          | false =>
              have hset : {z |
                  taggedAdmittedSourceArrivalPatternGapShapeMatches
                    target pattern pivot capacity weight work currentTime nextBatchDelay
                      (atom :: atoms) z} =
                  {z | duration z ≠ nextBatchDelay z} ∩
                    {z | taggedAdmittedSourceArrivalPatternGapShapeMatches
                      target pattern pivot capacity weight nextWork nextTime
                        remainingDelay atoms z} := by
                ext z
                simp [taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork,
                  duration, nextWork, nextTime, remainingDelay, hactive, hexternal]
              rw [hset]
              exact hterminal.compl.inter htail
          | true =>
              by_cases hinactive : atoms.Forall (fun later => later.active = false)
              · have hset : {z |
                    taggedAdmittedSourceArrivalPatternGapShapeMatches
                      target pattern pivot capacity weight work currentTime nextBatchDelay
                        (atom :: atoms) z} = {z | duration z = nextBatchDelay z} := by
                  ext z
                  simp [taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork,
                    duration, nextWork, nextTime, remainingDelay, hactive, hexternal,
                    hinactive]
                rw [hset]
                exact hterminal
              · have hset : {z |
                    taggedAdmittedSourceArrivalPatternGapShapeMatches
                      target pattern pivot capacity weight work currentTime nextBatchDelay
                        (atom :: atoms) z} = ∅ := by
                  ext z
                  simp [taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork,
                    duration, nextWork, nextTime, remainingDelay, hactive, hexternal,
                    hinactive]
                rw [hset]
                exact MeasurableSet.empty

/-- A static inactive suffix contributes no literal script steps.  This is
the padding fact used after a terminal external source event. -/
theorem finiteGPSFCFSFixedScriptSteps_gapSlots_eq_nil_of_forall_inactive
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (atoms : List TaggedAdmittedSourceGapBranchAtom)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (hinactive : atoms.Forall (fun atom => atom.active = false)) :
    finiteGPSFCFSFixedScriptSteps
      (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
        target pattern pivot capacity weight work currentTime nextBatchDelay atoms) z = [] := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      rfl
  | cons atom atoms ih =>
      simp only [List.forall_cons] at hinactive
      rcases hinactive with ⟨hactive, htailInactive⟩
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun sample k =>
          taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        currentTime sample + duration sample
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        nextBatchDelay sample - duration sample
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) htailInactive
      simpa [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots,
        finiteGPSFCFSFixedScriptSteps, hactive, batchWork, duration, nextWork,
        nextTime, remainingDelay] using htail

/-- On a matching source-pattern fiber, an active/external shape certificate
identifies the static padded script with the literal source-labelled GPS gap
step list.  This is the pointwise executable bridge used after Borel branch
construction; no list-valued source coordinate is declared measurable. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_fixedScriptSteps_of_shape
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z.1)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels)
    (capacity : ℝ) (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (atoms : List TaggedAdmittedSourceGapBranchAtom)
    (hshape : taggedAdmittedSourceArrivalPatternGapShapeMatches
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms z) :
    taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z.1
      (taggedAdmittedSourceArrival target z.1 pivot) atoms.length capacity weight
      (work z) (currentTime z) (nextBatchDelay z) =
      finiteGPSFCFSFixedScriptSteps
        (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
          target pattern pivot capacity weight work currentTime nextBatchDelay atoms) z := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      rfl
  | cons atom atoms ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ :=
        fun sample k =>
          taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
      have hbatch : batchWork z =
          taggedAdmittedBatchAt start horizon target z.1
            (taggedAdmittedSourceArrival target z.1 pivot) := by
        funext k
        exact taggedAdmittedSourceArrivalPatternBlockWork_eq_taggedAdmittedBatchAt_of_matches
          start horizon target z.1 pattern hmatches pivot hpivot k
      have hbatch' : (fun k =>
          taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k) =
          taggedAdmittedBatchAt start horizon target z.1
            (taggedAdmittedSourceArrival target z.1 pivot) := by
        simpa [batchWork] using hbatch
      let duration : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : TaggedAdmittedSourceGoodCarrier target → Category → ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)
      let nextTime : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        currentTime sample + duration sample
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target → ℝ := fun sample =>
        nextBatchDelay sample - duration sample
      have hshape' : atom.active = true ∧
          (if duration z = nextBatchDelay z then
            atom.endpointIsExternal = true ∧
              atoms.Forall (fun later => later.active = false)
          else atom.endpointIsExternal = false ∧
            taggedAdmittedSourceArrivalPatternGapShapeMatches
              target pattern pivot capacity weight nextWork nextTime remainingDelay atoms z) := by
        simpa [taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork,
          duration, nextWork, nextTime, remainingDelay] using hshape
      rcases hshape' with ⟨hactive, hshape'⟩
      by_cases hterminal : duration z = nextBatchDelay z
      ·
          have hexternal : atom.endpointIsExternal = true :=
            (if_pos hterminal ▸ hshape').1
          have hinactive : atoms.Forall (fun later => later.active = false) :=
            (if_pos hterminal ▸ hshape').2
          have hsourceTerminal :
              finiteGPSNextStepDuration capacity weight (work z)
                (nextBatchDelay z) = nextBatchDelay z := by
            simpa [duration] using hterminal
          have hsourceExternal :
              (finiteGPSBuildExecutionSegment capacity weight (work z)
                (taggedAdmittedBatchAt start horizon target z.1
                  (taggedAdmittedSourceArrival target z.1 pivot))
                (currentTime z) (nextBatchDelay z)).endpointIsExternalBatch = true :=
            finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight (work z)
              (taggedAdmittedBatchAt start horizon target z.1
                (taggedAdmittedSourceArrival target z.1 pivot))
              (currentTime z) (nextBatchDelay z) |>.mpr hsourceTerminal
          have hendpoint :
              ({ jobs := fun k =>
                  (taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                    target pattern pivot k).map fun coordinate => coordinate z } :
                FiniteGPSFCFSEndpointJobs Category
                  (TaggedAdmittedSourceJobId Category)) =
                taggedAdmittedFCFSJobsAt start horizon target z.1
                  (taggedAdmittedSourceArrival target z.1 pivot) := by
            change ({ jobs := fun k =>
                (taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                  target pattern pivot k).map fun coordinate => coordinate z } :
                FiniteGPSFCFSEndpointJobs Category
                  (TaggedAdmittedSourceJobId Category)) =
                ({ jobs := fun k =>
                  (taggedAdmittedFCFSJobsAt start horizon target z.1
                    (taggedAdmittedSourceArrival target z.1 pivot)).jobs k } :
                  FiniteGPSFCFSEndpointJobs Category
                    (TaggedAdmittedSourceJobId Category))
            apply congrArg FiniteGPSFCFSEndpointJobs.mk
            funext k
            exact taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates_eval_eq_jobsAt_of_matches
              start horizon target z pattern hmatches pivot hpivot k
          have htailEmpty :=
            finiteGPSFCFSFixedScriptSteps_gapSlots_eq_nil_of_forall_inactive
              target pattern pivot capacity weight nextWork nextTime remainingDelay
              atoms z hinactive
          have htailEmpty' :
              finiteGPSFCFSFixedScriptSteps
                (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
                  target pattern pivot capacity weight
                  (fun sample => finiteGPSNextEventState capacity weight (work sample)
                    (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                      target sample.1 pattern pivot k)
                    (nextBatchDelay sample))
                  (fun sample => currentTime sample +
                    finiteGPSNextStepDuration capacity weight (work sample)
                      (nextBatchDelay sample))
                  (fun sample => nextBatchDelay sample -
                    finiteGPSNextStepDuration capacity weight (work sample)
                      (nextBatchDelay sample)) atoms) z = [] := by
            simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using htailEmpty
          have hsourceExternal' :
              (finiteGPSBuildExecutionSegment capacity weight (work z)
                (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                  target z.1 pattern pivot k)
                (currentTime z) (nextBatchDelay z)).endpointIsExternalBatch = true := by
            simpa [hbatch'] using hsourceExternal
          have hhead :
              taggedAdmittedFiniteGPSBuildSegmentJobStep start horizon target z.1
                (taggedAdmittedSourceArrival target z.1 pivot)
                capacity weight (work z) (currentTime z) (nextBatchDelay z) =
                { segment := finiteGPSBuildExecutionSegment capacity weight (work z)
                    (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                      target z.1 pattern pivot k)
                    (currentTime z) (nextBatchDelay z)
                  endpointJobs :=
                    { jobs := fun k =>
                      (taggedAdmittedSourceArrivalPatternBlockFCFSJobCoordinates
                        target pattern pivot k).map fun coordinate => coordinate z } } := by
            simp only [taggedAdmittedFiniteGPSBuildSegmentJobStep]
            rw [← hbatch']
            simp only [taggedAdmittedFiniteGPSEndpointJobsForSegment,
              if_pos hsourceExternal']
            rw [← hendpoint]
          change taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z.1
            (taggedAdmittedSourceArrival target z.1 pivot) (atoms.length + 1)
            capacity weight (work z) (currentTime z) (nextBatchDelay z) = _
          simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps]
          simp only [if_pos hsourceTerminal]
          simp only [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots,
            finiteGPSFCFSFixedScriptSteps, if_pos hactive]
          rw [hhead]
          simp [FiniteGPSFCFSFixedScriptSkeletonSlot.step, hexternal, htailEmpty']
      ·
          have hexternal : atom.endpointIsExternal = false :=
            (if_neg hterminal ▸ hshape').1
          have htailShape :
              taggedAdmittedSourceArrivalPatternGapShapeMatches
                target pattern pivot capacity weight nextWork nextTime remainingDelay atoms z :=
            (if_neg hterminal ▸ hshape').2
          have hsourceNotTerminal :
              finiteGPSNextStepDuration capacity weight (work z)
                (nextBatchDelay z) ≠ nextBatchDelay z := by
            simpa [duration] using hterminal
          have hsourceExternalFalse :
              (finiteGPSBuildExecutionSegment capacity weight (work z)
                (taggedAdmittedBatchAt start horizon target z.1
                  (taggedAdmittedSourceArrival target z.1 pivot))
                (currentTime z) (nextBatchDelay z)).endpointIsExternalBatch = false := by
            apply Bool.eq_false_of_not_eq_true
            intro hExternal
            apply hsourceNotTerminal
            exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight (work z)
              (taggedAdmittedBatchAt start horizon target z.1
                (taggedAdmittedSourceArrival target z.1 pivot))
              (currentTime z) (nextBatchDelay z) |>.mp hExternal
          have htail := ih (work := nextWork) (currentTime := nextTime)
            (nextBatchDelay := remainingDelay) htailShape
          have htail' :
              taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z.1
                (taggedAdmittedSourceArrival target z.1 pivot) atoms.length capacity weight
                (finiteGPSNextEventState capacity weight (work z)
                  (taggedAdmittedBatchAt start horizon target z.1
                    (taggedAdmittedSourceArrival target z.1 pivot))
                  (nextBatchDelay z))
                (currentTime z + finiteGPSNextStepDuration capacity weight (work z)
                  (nextBatchDelay z))
                (nextBatchDelay z - finiteGPSNextStepDuration capacity weight (work z)
                  (nextBatchDelay z)) =
                finiteGPSFCFSFixedScriptSteps
                  (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
                    target pattern pivot capacity weight
                    (fun sample => finiteGPSNextEventState capacity weight (work sample)
                      (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                        target sample.1 pattern pivot k)
                      (nextBatchDelay sample))
                    (fun sample => currentTime sample +
                      finiteGPSNextStepDuration capacity weight (work sample)
                        (nextBatchDelay sample))
                    (fun sample => nextBatchDelay sample -
                      finiteGPSNextStepDuration capacity weight (work sample)
                        (nextBatchDelay sample)) atoms) z := by
            simpa [batchWork, duration, nextWork, nextTime, remainingDelay, hbatch] using htail
          have hsourceExternalFalse' :
              (finiteGPSBuildExecutionSegment capacity weight (work z)
                (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                  target z.1 pattern pivot k)
                (currentTime z) (nextBatchDelay z)).endpointIsExternalBatch = false := by
            simpa [hbatch'] using hsourceExternalFalse
          have hhead :
              taggedAdmittedFiniteGPSBuildSegmentJobStep start horizon target z.1
                (taggedAdmittedSourceArrival target z.1 pivot)
                capacity weight (work z) (currentTime z) (nextBatchDelay z) =
                { segment := finiteGPSBuildExecutionSegment capacity weight (work z)
                    (fun k => taggedAdmittedSourceArrivalPatternBlockWork
                      target z.1 pattern pivot k)
                    (currentTime z) (nextBatchDelay z)
                  endpointJobs :=
                    taggedAdmittedFCFSComputationalEndpointJobs } := by
            simp only [taggedAdmittedFiniteGPSBuildSegmentJobStep]
            rw [← hbatch']
            simp [taggedAdmittedFiniteGPSEndpointJobsForSegment,
              hsourceExternalFalse']
          simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps, if_neg hsourceNotTerminal]
          simp only [taggedAdmittedSourceArrivalPatternGapFixedScriptSlots,
            finiteGPSFCFSFixedScriptSteps, if_pos hactive]
          rw [hhead]
          simp [FiniteGPSFCFSFixedScriptSkeletonSlot.step,
            taggedAdmittedFCFSComputationalEndpointJobs, hexternal, htail',
            batchWork, duration, nextWork, nextTime, remainingDelay]

/-- The source-pattern, executable GPS-shape, and finite FCFS-count branch
fiber for one gap.  Its three conjuncts are intentionally separate: a source
comparison pattern fixes source identifiers and tie order, the shape fiber
fixes only actual GPS event comparisons, and the final fiber fixes the finite
FCFS threshold comparisons. -/
def taggedAdmittedSourceArrivalPatternGapFixedScriptBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    Set (TaggedAdmittedSourceGoodCarrier target) :=
  taggedAdmittedSourceArrivalPatternFiber start horizon target pattern ∩
    ({z | taggedAdmittedSourceArrivalPatternGapShapeMatches
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms z} ∩
      {z | finiteGPSFCFSFixedScriptBranchMatches target preQueue
        (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
          target pattern pivot capacity weight work currentTime nextBatchDelay atoms) z})

/-- Every fixed source-pattern/GPS-shape/FCFS-count branch for one literal
gap is Borel.  This is a semantic branch construction: source ledger data,
GPS endpoint comparisons, and FCFS prefix comparisons are each checked by
their actual finite real-coordinate predicates. -/
theorem measurableSet_taggedAdmittedSourceArrivalPatternGapFixedScriptBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    MeasurableSet (taggedAdmittedSourceArrivalPatternGapFixedScriptBranchFiber
      start horizon target pattern pivot capacity weight work currentTime
      nextBatchDelay preQueue atoms) := by
  unfold taggedAdmittedSourceArrivalPatternGapFixedScriptBranchFiber
  refine (measurableSet_taggedAdmittedSourceArrivalPatternFiber
    start horizon target pattern).inter ?_
  refine (measurableSet_taggedAdmittedSourceArrivalPatternGapShapeMatches
    target pattern pivot capacity weight work currentTime nextBatchDelay
    hwork hcurrentTime hnextBatchDelay atoms).inter ?_
  exact measurableSet_finiteGPSFCFSFixedScriptBranchMatches target preQueue
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms)
    hpreQueue
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_coordinatesMeasurable
      target pattern pivot capacity weight work currentTime nextBatchDelay
      hwork hcurrentTime hnextBatchDelay atoms)

/-- The Borel fixed-script representative of a source-pattern gap response.
The literal source trace is identified with this function only on the Borel
fiber below; this theorem itself does not treat a variable source job list as
measurable. -/
theorem measurable_taggedAdmittedSourceArrivalPatternGapFixedScriptReplayResponse
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (atoms : List TaggedAdmittedSourceGapBranchAtom) :
    Measurable (finiteGPSFCFSPaddedReplayResponse
      (taggedAdmittedTargetCompletionKey target) target
      (finiteGPSFCFSFixedScriptReplaySlots
        (taggedAdmittedTargetCompletionKey target) target preQueue
        (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
          target pattern pivot capacity weight work currentTime nextBatchDelay atoms))) := by
  exact measurable_finiteGPSFCFSFixedScriptReplayResponse
    (taggedAdmittedTargetCompletionKey target) target preQueue
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms)
    hpreQueue
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_coordinatesMeasurable
      target pattern pivot capacity weight work currentTime nextBatchDelay
      hwork hcurrentTime hnextBatchDelay atoms)

/-- On one fixed Borel source-pattern/GPS-shape/FCFS-count fiber, the Borel
fixed-script representative is exactly the response from the literal
source-labelled FCFS trace.  The statement is parameterized by an explicit
fixed target prequeue and matching literal initial ledger so that subsequent
finite-gap composition must supply its queue transport rather than erase it. -/
theorem taggedAdmittedFiniteGPSGapFirstKeyCompletionResponse_eq_fixedScriptReplayResponse_of_branchFiber
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (hpivot : pivot ∈ pattern.labels)
    (capacity : ℝ) (weight : Category → ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target → Category → ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (atoms : List TaggedAdmittedSourceGapBranchAtom)
    (hinitial : initial.residualJobs target =
      (FiniteGPSFCFSFixedKeyQueue.erase preQueue).map fun coordinate => coordinate z)
    (hfiber : z ∈ taggedAdmittedSourceArrivalPatternGapFixedScriptBranchFiber
      start horizon target pattern pivot capacity weight work currentTime
      nextBatchDelay preQueue atoms) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace
      (taggedAdmittedTargetCompletionKey target)
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial target
        (taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z.1
          (taggedAdmittedSourceArrival target z.1 pivot) atoms.length
          capacity weight (work z) (currentTime z) (nextBatchDelay z))) =
      finiteGPSFCFSPaddedReplayResponse
        (taggedAdmittedTargetCompletionKey target) target
        (finiteGPSFCFSFixedScriptReplaySlots
          (taggedAdmittedTargetCompletionKey target) target preQueue
          (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
            target pattern pivot capacity weight work currentTime nextBatchDelay atoms)) z := by
  change pattern.Matches start horizon target z.1 ∧
    taggedAdmittedSourceArrivalPatternGapShapeMatches
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms z ∧
    finiteGPSFCFSFixedScriptBranchMatches target preQueue
      (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
        target pattern pivot capacity weight work currentTime nextBatchDelay atoms) z at hfiber
  rcases hfiber with ⟨hmatches, hshape, hbranch⟩
  rw [taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_fixedScriptSteps_of_shape
    start horizon target z pattern hmatches pivot hpivot capacity weight work
    currentTime nextBatchDelay atoms hshape]
  exact finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_fixedScriptReplayResponse_of_branch
    (taggedAdmittedTargetCompletionKey target) target initial preQueue
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms) z
    hinitial
    (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_trackedEndpointCompatible
      target pattern pivot capacity weight work currentTime nextBatchDelay atoms)
    hbranch

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
