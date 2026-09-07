import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFixedScriptMeasurability
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSHorizonFence
import Mathlib.Tactic

/-!
# Fixed-script Borel presentation of a source-empty GPS fence

A computational horizon fence contains genuine GPS service segments but no
external source jobs.  This module gives it a finite fixed-script presentation
whose endpoint queues are explicitly empty in every slot.  The shape predicate
uses the executable next-event comparison directly; it never recognizes an
inactive slot by comparing a default segment with a real one.

The interface is generic in the input carrier.  A concrete adapter supplies
the Borel workload and clock coordinates, and glues these source-empty slots
to the preceding source-labelled trace.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId Omega : Type*} [Fintype Class] [DecidableEq Class]
  [MeasurableSpace Omega]

/-- Finite discrete branch data for one padded source-empty fence slot.  The
only endpoint datum is the FCFS completed-head count: all fence endpoint job
lists are definitionally empty. -/
structure FiniteGPSFCFSEmptyFenceBranchAtom where
  active : Bool
  completedCount : Nat

/-- Static padded slots for a zero-batch computational fence.  The coordinate
state follows the literal GPS next-event recurrence whether or not later
slots are active; inactive slots are omitted only by the fixed-script replay.
-/
def finiteGPSFCFSEmptyFenceFixedScriptSlots
    (key : JobId -> Bool) (capacity : ℝ) (weight : Class -> ℝ)
    (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ) :
    List FiniteGPSFCFSEmptyFenceBranchAtom ->
      List (FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key)
  | [] => []
  | atom :: atoms =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      let duration : Omega -> ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      let nextWork : Omega -> Class -> ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      let nextTime : Omega -> ℝ := fun omega => currentTime omega + duration omega
      let remainingDelay : Omega -> ℝ := fun omega =>
        nextBatchDelay omega - duration omega
      { scriptSlot :=
          { segment := fun omega => finiteGPSBuildExecutionSegment capacity weight
              (work omega) (batchWork omega) (currentTime omega)
                (nextBatchDelay omega)
            endpointJobs := fun _ => []
            trackedEndpointJobs := []
            active := atom.active }
        completedCount := atom.completedCount } ::
        finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight nextWork
          nextTime remainingDelay atoms

/-- Every real coordinate in a fixed source-empty fence script is Borel when
its starting workload and clock coordinates are Borel.  Empty endpoint lists
need no identifier-level measurable structure. -/
theorem finiteGPSFCFSEmptyFenceFixedScriptSlots_coordinatesMeasurable
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (hwork : forall k, Measurable (fun omega => work omega k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    ∀ slot ∈ finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight
      work currentTime nextBatchDelay atoms,
      slot.CoordinatesMeasurable trackedClass := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [finiteGPSFCFSEmptyFenceFixedScriptSlots]
  | cons atom atoms ih =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      have hbatchWork : forall k, Measurable (fun omega => batchWork omega k) := by
        intro k
        simpa [batchWork] using (measurable_const : Measurable (fun _ : Omega => (0 : ℝ)))
      let duration : Omega -> ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : Omega -> Class -> ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      have hnextWork : forall k, Measurable (fun omega => nextWork omega k) := by
        intro k
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay k
      let nextTime : Omega -> ℝ := fun omega => currentTime omega + duration omega
      have hnextTime : Measurable nextTime := hcurrentTime.add hduration
      let remainingDelay : Omega -> ℝ := fun omega =>
        nextBatchDelay omega - duration omega
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have hsegment : FiniteGPSExecutionSegmentCoordinatesMeasurable (fun omega =>
          finiteGPSBuildExecutionSegment capacity weight (work omega) (batchWork omega)
            (currentTime omega) (nextBatchDelay omega)) :=
        finiteGPSExecutionSegmentCoordinatesMeasurable_build capacity weight work batchWork
          hwork hbatchWork currentTime nextBatchDelay hcurrentTime hnextBatchDelay
      have htracked : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
          ([] : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key)) := by
        simp [FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
          FiniteGPSFCFSFixedQueueCoordinatesMeasurable,
          FiniteGPSFCFSFixedKeyQueue.erase]
      let scriptSlot : FiniteGPSFCFSFixedScriptSlot Class Omega JobId key :=
        { segment := fun omega => finiteGPSBuildExecutionSegment capacity weight
            (work omega) (batchWork omega) (currentTime omega) (nextBatchDelay omega)
          endpointJobs := fun _ => []
          trackedEndpointJobs := []
          active := atom.active }
      let head : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key :=
        { scriptSlot := scriptSlot
          completedCount := atom.completedCount }
      have hhead : head.CoordinatesMeasurable trackedClass := ⟨hsegment, htracked⟩
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) hnextWork hnextTime hremainingDelay
      intro slot hslot
      simp only [finiteGPSFCFSEmptyFenceFixedScriptSlots] at hslot
      rcases List.mem_cons.mp hslot with hslot | hslot
      · subst slot
        simpa [batchWork, duration, nextWork, nextTime, remainingDelay,
          scriptSlot, head] using hhead
      · simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using
          htail slot hslot

/-- In every source-empty fence slot, the tracked endpoint queue is exactly
the empty target-class endpoint list. -/
theorem finiteGPSFCFSEmptyFenceFixedScriptSlots_trackedEndpointCompatible
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    ∀ slot ∈ finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight
      work currentTime nextBatchDelay atoms,
      slot.TrackedEndpointCompatible trackedClass := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [finiteGPSFCFSEmptyFenceFixedScriptSlots]
  | cons atom atoms ih =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      let duration : Omega -> ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      let nextWork : Omega -> Class -> ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      let nextTime : Omega -> ℝ := fun omega => currentTime omega + duration omega
      let remainingDelay : Omega -> ℝ := fun omega =>
        nextBatchDelay omega - duration omega
      let scriptSlot : FiniteGPSFCFSFixedScriptSlot Class Omega JobId key :=
        { segment := fun omega => finiteGPSBuildExecutionSegment capacity weight
            (work omega) (batchWork omega) (currentTime omega) (nextBatchDelay omega)
          endpointJobs := fun _ => []
          trackedEndpointJobs := []
          active := atom.active }
      let head : FiniteGPSFCFSFixedScriptSkeletonSlot Class Omega JobId key :=
        { scriptSlot := scriptSlot
          completedCount := atom.completedCount }
      have hhead : head.TrackedEndpointCompatible trackedClass := by
        simp [FiniteGPSFCFSFixedScriptSkeletonSlot.TrackedEndpointCompatible,
          head, scriptSlot, FiniteGPSFCFSFixedKeyQueue.erase]
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay)
      intro slot hslot
      simp only [finiteGPSFCFSEmptyFenceFixedScriptSlots] at hslot
      rcases List.mem_cons.mp hslot with hslot | hslot
      · subst slot
        simpa [batchWork, duration, nextWork, nextTime, remainingDelay,
          scriptSlot, head] using hhead
      · simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using
          htail slot hslot

/-- The executable shape predicate for a padded zero-batch fence.  It records
the actual next-event equality at each active slot.  Once the fence reaches
its endpoint, only a static inactive suffix is permitted; if fixed fuel is
exhausted on internal steps, the empty recursive base records that fact
without inventing a terminal source event. -/
def finiteGPSFCFSEmptyFenceShapeMatches
    (key : JobId -> Bool) (capacity : ℝ) (weight : Class -> ℝ)
    (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ) :
    List FiniteGPSFCFSEmptyFenceBranchAtom -> Omega -> Prop
  | [] => fun _ => True
  | atom :: atoms =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      let duration : Omega -> ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      let nextWork : Omega -> Class -> ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      let nextTime : Omega -> ℝ := fun omega => currentTime omega + duration omega
      let remainingDelay : Omega -> ℝ := fun omega =>
        nextBatchDelay omega - duration omega
      fun omega => atom.active = true ∧
        if duration omega = nextBatchDelay omega then
          atoms.Forall (fun later => later.active = false)
        else finiteGPSFCFSEmptyFenceShapeMatches key capacity weight nextWork
          nextTime remainingDelay atoms omega

/-- Every fixed source-empty fence shape is a Borel fiber.  This is a finite
recursion over actual endpoint comparisons, rather than a measurability claim
for a variable segment list. -/
theorem measurableSet_finiteGPSFCFSEmptyFenceShapeMatches
    (key : JobId -> Bool) (capacity : ℝ) (weight : Class -> ℝ)
    (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (hwork : ∀ k, Measurable (fun omega => work omega k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    MeasurableSet {omega |
      finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
        nextBatchDelay atoms omega} := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      simp [finiteGPSFCFSEmptyFenceShapeMatches]
  | cons atom atoms ih =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      have hbatchWork : ∀ k, Measurable (fun omega => batchWork omega k) := by
        intro k
        simpa [batchWork] using (measurable_const : Measurable (fun _ : Omega => (0 : ℝ)))
      let duration : Omega -> ℝ := fun omega =>
        finiteGPSNextStepDuration capacity weight (work omega) (nextBatchDelay omega)
      have hduration : Measurable duration :=
        measurable_finiteGPSNextStepDuration_apply capacity weight work hwork
          nextBatchDelay hnextBatchDelay
      let nextWork : Omega -> Class -> ℝ := fun omega =>
        finiteGPSNextEventState capacity weight (work omega) (batchWork omega)
          (nextBatchDelay omega)
      have hnextWork : ∀ k, Measurable (fun omega => nextWork omega k) := by
        intro k
        exact measurable_finiteGPSNextEventState_apply capacity weight work batchWork
          hwork hbatchWork nextBatchDelay hnextBatchDelay k
      let nextTime : Omega -> ℝ := fun omega => currentTime omega + duration omega
      have hnextTime : Measurable nextTime := hcurrentTime.add hduration
      let remainingDelay : Omega -> ℝ := fun omega =>
        nextBatchDelay omega - duration omega
      have hremainingDelay : Measurable remainingDelay := hnextBatchDelay.sub hduration
      have hterminal : MeasurableSet {omega | duration omega = nextBatchDelay omega} :=
        measurableSet_eq_fun hduration hnextBatchDelay
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) hnextWork hnextTime hremainingDelay
      cases hactive : atom.active with
      | false =>
          have hset : {omega |
              finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
                nextBatchDelay (atom :: atoms) omega} = ∅ := by
            ext omega
            simp [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
              nextWork, nextTime, remainingDelay, hactive]
          rw [hset]
          exact MeasurableSet.empty
      | true =>
          by_cases hinactive : atoms.Forall (fun later => later.active = false)
          · have hset : {omega |
                finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
                  nextBatchDelay (atom :: atoms) omega} =
                {omega | duration omega = nextBatchDelay omega} ∪
                  ({omega | duration omega ≠ nextBatchDelay omega} ∩
                    {omega | finiteGPSFCFSEmptyFenceShapeMatches key capacity weight
                      nextWork nextTime remainingDelay atoms omega}) := by
                ext omega
                by_cases hterminal' : duration omega = nextBatchDelay omega
                · simp [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
                    nextWork, nextTime, remainingDelay, hactive, hinactive,
                    hterminal']
                · simp [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
                    nextWork, nextTime, remainingDelay, hactive, hinactive,
                    hterminal']
            rw [hset]
            exact hterminal.union (hterminal.compl.inter htail)
          · have hset : {omega |
                finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
                  nextBatchDelay (atom :: atoms) omega} =
                {omega | duration omega ≠ nextBatchDelay omega} ∩
                  {omega | finiteGPSFCFSEmptyFenceShapeMatches key capacity weight
                    nextWork nextTime remainingDelay atoms omega} := by
                ext omega
                by_cases hterminal' : duration omega = nextBatchDelay omega
                · simp [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
                    nextWork, nextTime, remainingDelay, hactive, hinactive,
                    hterminal']
                · simp [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
                    nextWork, nextTime, remainingDelay, hactive, hinactive,
                    hterminal']
            rw [hset]
            exact hterminal.compl.inter htail

/-- A static inactive fence suffix emits no FCFS steps. -/
theorem finiteGPSFCFSFixedScriptSteps_emptyFenceSlots_eq_nil_of_forall_inactive
    (key : JobId -> Bool) (capacity : ℝ) (weight : Class -> ℝ)
    (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) (omega : Omega)
    (hinactive : atoms.Forall (fun atom => atom.active = false)) :
    finiteGPSFCFSFixedScriptSteps
      (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work currentTime
        nextBatchDelay atoms) omega = [] := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      rfl
  | cons atom atoms ih =>
      simp only [List.forall_cons] at hinactive
      rcases hinactive with ⟨hactive, htailInactive⟩
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      let duration : Omega -> ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : Omega -> Class -> ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)
      let nextTime : Omega -> ℝ := fun sample => currentTime sample + duration sample
      let remainingDelay : Omega -> ℝ := fun sample =>
        nextBatchDelay sample - duration sample
      have htail := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay) htailInactive
      simpa [finiteGPSFCFSEmptyFenceFixedScriptSlots,
        finiteGPSFCFSFixedScriptSteps, hactive, batchWork, duration, nextWork,
        nextTime, remainingDelay] using htail

/-- On its executable branch fiber, a padded source-empty fence script is
exactly the literal empty-endpoint FCFS representation of the generated GPS
segments.  The equality retains every concrete segment; it does not replace
the fence by a no-op or a source arrival. -/
theorem finiteGPSFCFSEmptyEndpointSteps_runGapSegments_eq_fixedScriptSteps_of_shape
    (key : JobId -> Bool) (capacity : ℝ) (weight : Class -> ℝ)
    (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) (omega : Omega)
    (hshape : finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work
      currentTime nextBatchDelay atoms omega) :
    finiteGPSFCFSEmptyEndpointSteps
      (finiteGPSRunGapSegments atoms.length capacity weight (work omega)
        (fun _ => 0) (currentTime omega) (nextBatchDelay omega)) =
      finiteGPSFCFSFixedScriptSteps
        (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
          currentTime nextBatchDelay atoms) omega := by
  induction atoms generalizing work currentTime nextBatchDelay with
  | nil =>
      rfl
  | cons atom atoms ih =>
      let batchWork : Omega -> Class -> ℝ := fun _ _ => 0
      let duration : Omega -> ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : Omega -> Class -> ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)
      let nextTime : Omega -> ℝ := fun sample => currentTime sample + duration sample
      let remainingDelay : Omega -> ℝ := fun sample =>
        nextBatchDelay sample - duration sample
      have hshape' : atom.active = true ∧
          (if duration omega = nextBatchDelay omega then
            atoms.Forall (fun later => later.active = false)
          else finiteGPSFCFSEmptyFenceShapeMatches key capacity weight nextWork
            nextTime remainingDelay atoms omega) := by
        simpa [finiteGPSFCFSEmptyFenceShapeMatches, batchWork, duration,
          nextWork, nextTime, remainingDelay] using hshape
      rcases hshape' with ⟨hactive, hshape'⟩
      by_cases hterminal : duration omega = nextBatchDelay omega
      · have hinactive : atoms.Forall (fun later => later.active = false) := by
          simpa [hterminal] using hshape'
        have hsourceTerminal : finiteGPSNextStepDuration capacity weight (work omega)
            (nextBatchDelay omega) = nextBatchDelay omega := by
          simpa [duration] using hterminal
        have htailEmpty :=
          finiteGPSFCFSFixedScriptSteps_emptyFenceSlots_eq_nil_of_forall_inactive
            key capacity weight nextWork nextTime remainingDelay atoms omega hinactive
        have htailEmpty' : finiteGPSFCFSFixedScriptSteps
            (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight
              (fun sample => finiteGPSNextEventState capacity weight (work sample)
                (fun _ => 0) (nextBatchDelay sample))
              (fun sample => currentTime sample +
                finiteGPSNextStepDuration capacity weight (work sample)
                  (nextBatchDelay sample))
              (fun sample => nextBatchDelay sample -
                finiteGPSNextStepDuration capacity weight (work sample)
                  (nextBatchDelay sample)) atoms) omega = [] := by
            simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using htailEmpty
        change finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments (atoms.length + 1) capacity weight (work omega)
            (fun _ => 0) (currentTime omega) (nextBatchDelay omega)) = _
        simp only [finiteGPSRunGapSegments, if_pos hsourceTerminal]
        simp only [finiteGPSFCFSEmptyFenceFixedScriptSlots,
          finiteGPSFCFSFixedScriptSteps, if_pos hactive]
        simp only [finiteGPSFCFSEmptyEndpointSteps, List.map_cons, List.map_nil]
        rw [htailEmpty']
        rfl
      · have htailShape : finiteGPSFCFSEmptyFenceShapeMatches key capacity weight
            nextWork nextTime remainingDelay atoms omega := by
          simpa [hterminal] using hshape'
        have hsourceNotTerminal : finiteGPSNextStepDuration capacity weight (work omega)
            (nextBatchDelay omega) ≠ nextBatchDelay omega := by
          simpa [duration] using hterminal
        have htail := ih (work := nextWork) (currentTime := nextTime)
          (nextBatchDelay := remainingDelay) htailShape
        have htail' : finiteGPSFCFSEmptyEndpointSteps
            (finiteGPSRunGapSegments atoms.length capacity weight
              (finiteGPSNextEventState capacity weight (work omega) (fun _ => 0)
                (nextBatchDelay omega))
              (fun _ => 0)
              (currentTime omega + finiteGPSNextStepDuration capacity weight (work omega)
                (nextBatchDelay omega))
              (nextBatchDelay omega - finiteGPSNextStepDuration capacity weight (work omega)
                (nextBatchDelay omega))) =
            finiteGPSFCFSFixedScriptSteps
              (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight
                (fun sample => finiteGPSNextEventState capacity weight (work sample)
                  (fun _ => 0) (nextBatchDelay sample))
                (fun sample => currentTime sample +
                  finiteGPSNextStepDuration capacity weight (work sample)
                    (nextBatchDelay sample))
                (fun sample => nextBatchDelay sample -
                  finiteGPSNextStepDuration capacity weight (work sample)
                    (nextBatchDelay sample)) atoms) omega := by
          simpa [batchWork, duration, nextWork, nextTime, remainingDelay] using htail
        change finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments (atoms.length + 1) capacity weight (work omega)
            (fun _ => 0) (currentTime omega) (nextBatchDelay omega)) = _
        simp only [finiteGPSRunGapSegments, if_neg hsourceNotTerminal]
        simp only [finiteGPSFCFSEmptyFenceFixedScriptSlots,
          finiteGPSFCFSFixedScriptSteps, if_pos hactive]
        simp only [finiteGPSFCFSEmptyEndpointSteps, List.map_cons]
        congr

/-- The Borel branch fiber for a source-empty fence.  The first conjunct pins
the script's static slot count to the literal runner's active-class fuel; this
is required on arbitrary inputs and is intentionally not replaced by a
nonnegative-work uniform-fuel shortcut. -/
def finiteGPSFCFSEmptyFenceFixedScriptBranchFiber
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) : Set Omega :=
  {omega | atoms.length = (finiteGPSActiveClasses (work omega)).card + 1} ∩
    ({omega | finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work
      currentTime nextBatchDelay atoms omega} ∩
      {omega | finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue
        (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
          currentTime nextBatchDelay atoms) omega})

/-- Every fixed actual-fuel/shape/completed-count fence branch is Borel. -/
theorem measurableSet_finiteGPSFCFSEmptyFenceFixedScriptBranchFiber
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (hwork : ∀ k, Measurable (fun omega => work omega k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    MeasurableSet (finiteGPSFCFSEmptyFenceFixedScriptBranchFiber key trackedClass
      capacity weight work currentTime nextBatchDelay preQueue atoms) := by
  unfold finiteGPSFCFSEmptyFenceFixedScriptBranchFiber
  have hactiveCard : Measurable fun omega =>
      (finiteGPSActiveClasses (work omega)).card :=
    measurable_finiteGPSActiveClasses_card_apply work hwork
  have hfuel : MeasurableSet {omega |
      atoms.length = (finiteGPSActiveClasses (work omega)).card + 1} := by
    exact measurableSet_eq_fun measurable_const (hactiveCard.add measurable_const)
  refine hfuel.inter ?_
  refine (measurableSet_finiteGPSFCFSEmptyFenceShapeMatches key capacity weight
    work currentTime nextBatchDelay hwork hcurrentTime hnextBatchDelay atoms).inter ?_
  exact measurableSet_finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue
    (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
      currentTime nextBatchDelay atoms) hpreQueue
    (finiteGPSFCFSEmptyFenceFixedScriptSlots_coordinatesMeasurable key trackedClass
      capacity weight work currentTime nextBatchDelay hwork hcurrentTime
      hnextBatchDelay atoms)

/-- The fixed-script padded replay response for a source-empty fence is
Borel in the supplied finite real coordinates. -/
theorem measurable_finiteGPSFCFSEmptyFenceFixedScriptReplayResponse
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (hwork : ∀ k, Measurable (fun omega => work omega k))
    (hcurrentTime : Measurable currentTime)
    (hnextBatchDelay : Measurable nextBatchDelay)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    Measurable (finiteGPSFCFSPaddedReplayResponse key trackedClass
      (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue
        (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
          currentTime nextBatchDelay atoms))) := by
  exact measurable_finiteGPSFCFSFixedScriptReplayResponse key trackedClass preQueue
    (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
      currentTime nextBatchDelay atoms) hpreQueue
    (finiteGPSFCFSEmptyFenceFixedScriptSlots_coordinatesMeasurable key trackedClass
      capacity weight work currentTime nextBatchDelay hwork hcurrentTime
      hnextBatchDelay atoms)

/-- On a complete actual-fuel fence branch, the Borel fixed-script response
is exactly the response emitted by the literal empty-endpoint FCFS trace. -/
theorem finiteGPSFCFSFirstKeyCompletionResponseFromTrace_emptyFence_eq_fixedScriptReplayResponse_of_branchFiber
    (key : JobId -> Bool) (trackedClass : Class) (capacity : ℝ)
    (weight : Class -> ℝ) (work : Omega -> Class -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega JobId key))
    (atoms : List FiniteGPSFCFSEmptyFenceBranchAtom) (omega : Omega)
    (hinitial : initial.residualJobs trackedClass =
      (FiniteGPSFCFSFixedKeyQueue.erase preQueue).map fun coordinate => coordinate omega)
    (hfiber : omega ∈ finiteGPSFCFSEmptyFenceFixedScriptBranchFiber key trackedClass
      capacity weight work currentTime nextBatchDelay preQueue atoms) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace key
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial trackedClass
        (finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments ((finiteGPSActiveClasses (work omega)).card + 1)
            capacity weight (work omega) (fun _ => 0) (currentTime omega)
              (nextBatchDelay omega)))) =
      finiteGPSFCFSPaddedReplayResponse key trackedClass
        (finiteGPSFCFSFixedScriptReplaySlots key trackedClass preQueue
          (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
            currentTime nextBatchDelay atoms)) omega := by
  change atoms.length = (finiteGPSActiveClasses (work omega)).card + 1 ∧
    finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
      nextBatchDelay atoms omega ∧
    finiteGPSFCFSFixedScriptBranchMatches trackedClass preQueue
      (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
        currentTime nextBatchDelay atoms) omega at hfiber
  rcases hfiber with ⟨hfuel, hshape, hbranch⟩
  rw [← hfuel]
  rw [finiteGPSFCFSEmptyEndpointSteps_runGapSegments_eq_fixedScriptSteps_of_shape
    key capacity weight work currentTime nextBatchDelay atoms omega hshape]
  exact finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_fixedScriptReplayResponse_of_branch
    key trackedClass initial preQueue
    (finiteGPSFCFSEmptyFenceFixedScriptSlots key capacity weight work
      currentTime nextBatchDelay atoms) omega hinitial
    (finiteGPSFCFSEmptyFenceFixedScriptSlots_trackedEndpointCompatible key
      trackedClass capacity weight work currentTime nextBatchDelay atoms)
    hbranch

end

end AppliedModelingLib.Probability.Queueing
