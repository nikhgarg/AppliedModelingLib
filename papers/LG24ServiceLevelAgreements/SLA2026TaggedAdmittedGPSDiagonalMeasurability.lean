import AppliedModelingLib.Foundations.Probability.MeasurableCountableEvaluation
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCanonicalTail
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedPreTerminalFixedScriptMeasurability
import Mathlib.Tactic

/-!
# Borel measurability of the literal tagged diagonal GPS response

This module closes the finite source/fence executor with a countable family
of semantic fixed-script fibers.  Source and empty-fence atoms record only
the executable GPS event comparisons.  The FCFS completed-head counts are a
separate countable coordinate of the final replay skeleton, so no branch
depends on a dynamically transported ledger.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

local instance taggedAdmittedSourceArrivalPattern_countable :
    Countable (TaggedAdmittedSourceArrivalPattern Category) := by
  exact (show Function.Injective (fun pattern : TaggedAdmittedSourceArrivalPattern Category =>
      (pattern.labels, pattern.equalPairs, pattern.earlierPairs)) by
    intro left right h
    cases left
    cases right
    simp_all).countable

local instance taggedAdmittedSourceArrivalPattern_sortedRepresentativeScript_countable
    (pattern : TaggedAdmittedSourceArrivalPattern Category) :
    Countable (TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern) := by
  exact (show Function.Injective
      (fun script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern =>
        script.pivots) by
    intro left right h
    cases left
    cases right
    simp_all).countable

local instance taggedAdmittedSourceGapBranchAtom_countable :
    Countable TaggedAdmittedSourceGapBranchAtom := by
  exact (show Function.Injective (fun atom : TaggedAdmittedSourceGapBranchAtom =>
      (atom.active, atom.endpointIsExternal, atom.completedCount)) by
    intro left right h
    cases left
    cases right
    simp_all).countable

local instance finiteGPSFCFSEmptyFenceBranchAtom_countable :
    Countable FiniteGPSFCFSEmptyFenceBranchAtom := by
  exact (show Function.Injective (fun atom : FiniteGPSFCFSEmptyFenceBranchAtom =>
      (atom.active, atom.completedCount)) by
    intro left right h
    cases left
    cases right
    simp_all).countable

/-- The count data for a global fixed FCFS script is intentionally separate
from the source/fence GPS-shape atoms. -/
def taggedAdmittedFixedScriptWithCompletedCounts
    {Omega : Type*}
    (target : Category)
    (slots : List (FiniteGPSFCFSFixedScriptSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target))) :
    List Nat ->
      List (FiniteGPSFCFSFixedScriptSkeletonSlot Category Omega
        (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target))
  | [] => slots.map fun slot => { scriptSlot := slot, completedCount := 0 }
  | count :: counts =>
      match slots with
      | [] => []
      | slot :: slots =>
          { scriptSlot := slot, completedCount := count } ::
            taggedAdmittedFixedScriptWithCompletedCounts target slots counts

/-- Forgetting the independent completed-count vector recovers the original
fixed slot layout exactly. -/
theorem taggedAdmittedFixedScriptWithCompletedCounts_map_scriptSlot
    {Omega : Type*}
    (target : Category)
    (slots : List (FiniteGPSFCFSFixedScriptSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (counts : List Nat) :
    (taggedAdmittedFixedScriptWithCompletedCounts (target := target) slots counts).map
      (fun skeleton => skeleton.scriptSlot) = slots := by
  induction counts generalizing slots with
  | nil =>
      simp only [taggedAdmittedFixedScriptWithCompletedCounts, List.map_map,
        Function.comp_apply]
      exact List.map_id _
  | cons count counts ih =>
      cases slots with
      | nil => rfl
      | cons slot slots =>
          simp [taggedAdmittedFixedScriptWithCompletedCounts, ih]

/-- A completed-count vector extracted from an arbitrary fixed skeleton
reconstructs that skeleton whenever its literal slot layout agrees with the
given shape. -/
theorem taggedAdmittedFixedScriptWithCompletedCounts_eq_of_map_scriptSlot
    {Omega : Type*}
    (target : Category)
    (skeletons : List (FiniteGPSFCFSFixedScriptSkeletonSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (slots : List (FiniteGPSFCFSFixedScriptSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (hslots : skeletons.map (fun skeleton => skeleton.scriptSlot) = slots) :
    taggedAdmittedFixedScriptWithCompletedCounts (target := target) slots
      (skeletons.map fun skeleton => skeleton.completedCount) = skeletons := by
  induction skeletons generalizing slots with
  | nil =>
      simp at hslots
      subst slots
      rfl
  | cons skeleton skeletons ih =>
      cases slots with
      | nil =>
          simp at hslots
      | cons slot slots =>
          simp only [List.map_cons] at hslots
          have hhead : skeleton.scriptSlot = slot := by
            exact List.cons.inj hslots |>.1
          have htail : skeletons.map (fun later => later.scriptSlot) = slots := by
            exact List.cons.inj hslots |>.2
          subst slot
          simp [taggedAdmittedFixedScriptWithCompletedCounts, ih slots htail]

/-- Every fixed executable slot layout lies on one completed-count branch.
The count vector is independent finite discrete data; it does not alter the
GPS shape or the literal endpoint coordinate functions. -/
theorem exists_taggedAdmittedFixedScriptWithCompletedCounts_branchMatches
    {Omega : Type*} [MeasurableSpace Omega]
    (target : Category)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (slots : List (FiniteGPSFCFSFixedScriptSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (omega : Omega) :
    ∃ counts : List Nat,
      finiteGPSFCFSFixedScriptBranchMatches target preQueue
        (taggedAdmittedFixedScriptWithCompletedCounts (target := target) slots counts)
          omega := by
  rcases exists_finiteGPSFCFSFixedScriptBranchMatches target preQueue slots omega with
    ⟨skeletons, hslots, hbranch⟩
  refine ⟨skeletons.map fun skeleton => skeleton.completedCount, ?_⟩
  rw [taggedAdmittedFixedScriptWithCompletedCounts_eq_of_map_scriptSlot
    (target := target) skeletons slots hslots]
  exact hbranch

/-- The finite executable GPS comparison shape of one source gap.  The
completed-count fields are deliberately fixed to zero: FCFS count branches
are supplied independently by the global skeleton. -/
def taggedAdmittedSourceGapExecutionShapeAtoms
    (fuel : Nat) (capacity : ℝ) (weight work batchWork : Category -> ℝ)
    (currentTime nextBatchDelay : ℝ) : List TaggedAdmittedSourceGapBranchAtom :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
      if duration = nextBatchDelay then
        { active := true, endpointIsExternal := true, completedCount := 0 } ::
          List.replicate fuel
            { active := false, endpointIsExternal := false, completedCount := 0 }
      else
        { active := true, endpointIsExternal := false, completedCount := 0 } ::
          taggedAdmittedSourceGapExecutionShapeAtoms fuel capacity weight nextWork batchWork
            (currentTime + duration) (nextBatchDelay - duration)

/-- The execution-derived source atoms satisfy the source-gap semantic
predicate at the supplied sample.  This is a finite structural fact about
the actual next-event comparisons, with no termination or sign premise. -/
theorem taggedAdmittedSourceArrivalPatternGapShapeMatches_executionShapeAtoms
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (pivot : TaggedAdmittedSourceJobId Category) (capacity : ℝ)
    (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (z : TaggedAdmittedSourceGoodCarrier target) :
    ∀ fuel : Nat,
      taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot capacity weight
        work currentTime nextBatchDelay
        (taggedAdmittedSourceGapExecutionShapeAtoms fuel capacity weight (work z)
          (taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot)
          (currentTime z) (nextBatchDelay z)) z := by
  intro fuel
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedSourceGapExecutionShapeAtoms,
        taggedAdmittedSourceArrivalPatternGapShapeMatches]
  | succ fuel ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample k =>
        taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
      let duration : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)
      let nextTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
        currentTime sample + duration sample
      let remainingDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
        nextBatchDelay sample - duration sample
      have hih := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay)
      by_cases hterminal : duration z = nextBatchDelay z
      · have hinactive : (List.replicate fuel
            { active := false, endpointIsExternal := false,
              completedCount := 0 } : List TaggedAdmittedSourceGapBranchAtom).Forall
              (fun atom => atom.active = false) := by
            have hrep : ∀ n : Nat, (List.replicate n
                { active := false, endpointIsExternal := false,
                  completedCount := 0 } : List TaggedAdmittedSourceGapBranchAtom).Forall
                  (fun atom => atom.active = false) := by
              intro n
              induction n with
              | zero => simp
              | succ n hn =>
                  rw [List.replicate_succ, List.forall_cons]
                  exact ⟨rfl, hn⟩
            exact hrep fuel
        simpa [taggedAdmittedSourceGapExecutionShapeAtoms,
          taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork, duration,
          nextWork, nextTime, remainingDelay, hterminal, hinactive]
      · simpa [taggedAdmittedSourceGapExecutionShapeAtoms,
          taggedAdmittedSourceArrivalPatternGapShapeMatches, batchWork, duration,
          nextWork, nextTime, remainingDelay, hterminal] using hih

/-- The execution-derived padded source-gap atom list has exactly its chosen
fuel length, including its inactive tail after an external endpoint. -/
theorem taggedAdmittedSourceGapExecutionShapeAtoms_length
    (fuel : Nat) (capacity : ℝ) (weight work batchWork : Category -> ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedSourceGapExecutionShapeAtoms fuel capacity weight work batchWork
      currentTime nextBatchDelay).length = fuel := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero => rfl
  | succ fuel ih =>
      unfold taggedAdmittedSourceGapExecutionShapeAtoms
      dsimp only
      split
      · simp
      · simp [ih]

/-- The complete source-prefix GPS comparison shape at one sample.  If a
bounded source gap does not reach its pending batch, all later source gaps
are represented by empty inactive lists, exactly matching the literal
partial-state stop semantics. -/
def taggedAdmittedSourcePreTerminalExecutionShapeAtoms
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (work : Category -> ℝ) (currentTime : ℝ) :
    List (TaggedAdmittedSourceJobId Category) ->
      List (List TaggedAdmittedSourceGapBranchAtom)
  | [] => []
  | pivot :: pivots =>
      let batchWork := taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot
      let arrival := taggedAdmittedSourceArrival target z.1 pivot
      let nextBatchDelay := arrival - currentTime
      let fuel := (finiteGPSActiveClasses work).card + 1
      let atoms := taggedAdmittedSourceGapExecutionShapeAtoms fuel capacity weight work
        batchWork currentTime nextBatchDelay
      let gap := finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay
      atoms :: if gap.batchApplied = true then
        taggedAdmittedSourcePreTerminalExecutionShapeAtoms target pattern capacity weight z
          gap.workload arrival pivots
      else List.replicate pivots.length []

/-- A replicated suffix of empty source-gap atom lists is semantically
inactive. -/
theorem taggedAdmittedSourceGapAtomListsAllInactive_replicate_nil
    (n : Nat) :
    TaggedAdmittedSourceGapAtomListsAllInactive
      (List.replicate n ([] : List TaggedAdmittedSourceGapBranchAtom)) := by
  induction n with
  | zero => simp [TaggedAdmittedSourceGapAtomListsAllInactive]
  | succ n ih =>
      rw [List.replicate_succ]
      rw [TaggedAdmittedSourceGapAtomListsAllInactive, List.forall_cons]
      refine ⟨by simp, ?_⟩
      simpa [TaggedAdmittedSourceGapAtomListsAllInactive] using ih

/-- The source-prefix atoms extracted from one execution satisfy every
actual-fuel and partial-stop condition of the complete source-prefix shape
predicate. -/
theorem taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches_executionShapeAtoms
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (z : TaggedAdmittedSourceGoodCarrier target) :
    ∀ pivots : List (TaggedAdmittedSourceJobId Category),
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
        weight work currentTime pivots
        (taggedAdmittedSourcePreTerminalExecutionShapeAtoms target pattern capacity weight z
          (work z) (currentTime z) pivots) z := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
        taggedAdmittedSourcePreTerminalExecutionShapeAtoms]
  | cons pivot pivots ih =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample k =>
        taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
      let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
        taggedAdmittedSourceArrival target sample.1 pivot
      let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
        arrival sample - currentTime sample
      let fuel : Nat := (finiteGPSActiveClasses (work z)).card + 1
      let atoms : List TaggedAdmittedSourceGapBranchAtom :=
        taggedAdmittedSourceGapExecutionShapeAtoms fuel capacity weight (work z)
          (batchWork z) (currentTime z) (nextBatchDelay z)
      let gap : FiniteGPSGapRunResult Category :=
        finiteGPSRunGap fuel capacity weight (work z) (batchWork z) (nextBatchDelay z)
      have hatoms_length : atoms.length = fuel := by
        exact taggedAdmittedSourceGapExecutionShapeAtoms_length fuel capacity weight
          (work z) (batchWork z) (currentTime z) (nextBatchDelay z)
      have hgapShape : taggedAdmittedSourceArrivalPatternGapShapeMatches
          target pattern pivot capacity weight work currentTime nextBatchDelay atoms z := by
        simpa [atoms, batchWork] using
          (taggedAdmittedSourceArrivalPatternGapShapeMatches_executionShapeAtoms
            target pattern pivot capacity weight work currentTime nextBatchDelay z fuel)
      let nextWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample =>
        (finiteGPSRunGap atoms.length capacity weight (work sample) (batchWork sample)
          (nextBatchDelay sample)).workload
      have hnextWork_z : nextWork z = gap.workload := by
        simp [nextWork, gap, hatoms_length]
      have hgap_z :
          finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
            (nextBatchDelay z) = gap := by
        simp [gap, hatoms_length]
      by_cases hbatch : gap.batchApplied = true
      · have htail := ih (work := nextWork) (currentTime := arrival)
        have htail' : taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
            target pattern capacity weight nextWork arrival pivots
            (taggedAdmittedSourcePreTerminalExecutionShapeAtoms target pattern capacity weight z
              gap.workload (arrival z) pivots) z := by
          simpa [hnextWork_z] using htail
        change atoms.length = (finiteGPSActiveClasses (work z)).card + 1 ∧
          taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot capacity
            weight work currentTime nextBatchDelay atoms z ∧
          (if (finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)).batchApplied = true then _ else _)
        rw [hgap_z, hbatch]
        exact ⟨by simpa [fuel] using hatoms_length, hgapShape, htail'⟩
      · have hinactive : TaggedAdmittedSourceGapAtomListsAllInactive
            (List.replicate pivots.length ([] : List TaggedAdmittedSourceGapBranchAtom)) :=
          taggedAdmittedSourceGapAtomListsAllInactive_replicate_nil pivots.length
        have hbatchRaw :
            (finiteGPSRunGap fuel capacity weight (work z) (batchWork z)
              (nextBatchDelay z)).batchApplied ≠ true := by
          simpa [gap] using hbatch
        have hbatchExpanded :
            (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
              capacity weight (work z)
              (taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot)
              (taggedAdmittedSourceArrival target z.1 pivot - currentTime z)).batchApplied
                ≠ true := by
          simpa [fuel, batchWork, nextBatchDelay] using hbatchRaw
        change atoms.length = (finiteGPSActiveClasses (work z)).card + 1 ∧
          taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot capacity
            weight work currentTime nextBatchDelay atoms z ∧
          (if (finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)).batchApplied = true then _ else _)
        rw [hgap_z]
        simp only [if_neg hbatch]
        exact ⟨by simpa [fuel] using hatoms_length, hgapShape,
          by simpa [taggedAdmittedSourcePreTerminalExecutionShapeAtoms,
            hbatchExpanded] using hinactive⟩

/-- The finite executable comparison shape of a source-empty horizon fence.
As for source atoms, its completed-count fields remain zero because those
counts belong to the independent global FCFS branch. -/
def taggedAdmittedEmptyFenceExecutionShapeAtoms
    (fuel : Nat) (capacity : ℝ) (weight work : Category -> ℝ)
    (currentTime nextBatchDelay : ℝ) : List FiniteGPSFCFSEmptyFenceBranchAtom :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
        nextBatchDelay
      if duration = nextBatchDelay then
        { active := true, completedCount := 0 } ::
          List.replicate fuel { active := false, completedCount := 0 }
      else
        { active := true, completedCount := 0 } ::
          taggedAdmittedEmptyFenceExecutionShapeAtoms fuel capacity weight nextWork
            (currentTime + duration) (nextBatchDelay - duration)

/-- The execution-derived empty-fence atoms satisfy the exact source-empty
GPS comparison predicate at the given sample. -/
theorem finiteGPSFCFSEmptyFenceShapeMatches_executionShapeAtoms
    {Omega : Type*} [MeasurableSpace Omega]
    (key : TaggedAdmittedSourceJobId Category -> Bool)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : Omega -> Category -> ℝ)
    (currentTime nextBatchDelay : Omega -> ℝ) (omega : Omega) :
    ∀ fuel : Nat,
      finiteGPSFCFSEmptyFenceShapeMatches key capacity weight work currentTime
        nextBatchDelay
        (taggedAdmittedEmptyFenceExecutionShapeAtoms fuel capacity weight (work omega)
          (currentTime omega) (nextBatchDelay omega)) omega := by
  intro fuel
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedEmptyFenceExecutionShapeAtoms,
        finiteGPSFCFSEmptyFenceShapeMatches]
  | succ fuel ih =>
      let duration : Omega -> ℝ := fun sample =>
        finiteGPSNextStepDuration capacity weight (work sample) (nextBatchDelay sample)
      let nextWork : Omega -> Category -> ℝ := fun sample =>
        finiteGPSNextEventState capacity weight (work sample) (fun _ => 0)
          (nextBatchDelay sample)
      let nextTime : Omega -> ℝ := fun sample => currentTime sample + duration sample
      let remainingDelay : Omega -> ℝ := fun sample => nextBatchDelay sample - duration sample
      have hih := ih (work := nextWork) (currentTime := nextTime)
        (nextBatchDelay := remainingDelay)
      by_cases hterminal : duration omega = nextBatchDelay omega
      · have hinactive : (List.replicate fuel
            { active := false, completedCount := 0 } :
              List FiniteGPSFCFSEmptyFenceBranchAtom).Forall
                (fun atom => atom.active = false) := by
            have hrep : ∀ n : Nat, (List.replicate n
                { active := false, completedCount := 0 } :
                  List FiniteGPSFCFSEmptyFenceBranchAtom).Forall
                    (fun atom => atom.active = false) := by
              intro n
              induction n with
              | zero => simp
              | succ n hn =>
                  rw [List.replicate_succ, List.forall_cons]
                  exact ⟨rfl, hn⟩
            exact hrep fuel
        simpa [taggedAdmittedEmptyFenceExecutionShapeAtoms,
          finiteGPSFCFSEmptyFenceShapeMatches, duration, nextWork, nextTime,
          remainingDelay, hterminal, hinactive]
      · simpa [taggedAdmittedEmptyFenceExecutionShapeAtoms,
          finiteGPSFCFSEmptyFenceShapeMatches, duration, nextWork, nextTime,
          remainingDelay, hterminal] using hih

/-- The empty-fence execution-shape list has exactly the chosen fuel length. -/
theorem taggedAdmittedEmptyFenceExecutionShapeAtoms_length
    (fuel : Nat) (capacity : ℝ) (weight work : Category -> ℝ)
    (currentTime nextBatchDelay : ℝ) :
    (taggedAdmittedEmptyFenceExecutionShapeAtoms fuel capacity weight work currentTime
      nextBatchDelay).length = fuel := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero => rfl
  | succ fuel ih =>
      unfold taggedAdmittedEmptyFenceExecutionShapeAtoms
      dsimp only
      split
      · simp
      · simp [ih]

/-- Real-coordinate Borelness of a completed-count refinement follows from
the Borelness of the count-free literal slot layout. -/
theorem taggedAdmittedFixedScriptWithCompletedCounts_coordinatesMeasurable
    {Omega : Type*} [MeasurableSpace Omega]
    (target : Category)
    (base : List (FiniteGPSFCFSFixedScriptSkeletonSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (hbase : ∀ slot ∈ base, slot.CoordinatesMeasurable target)
    (counts : List Nat) :
    ∀ slot ∈ taggedAdmittedFixedScriptWithCompletedCounts (target := target)
      (base.map fun baseSlot => baseSlot.scriptSlot) counts,
      slot.CoordinatesMeasurable target := by
  intro slot hslot
  have hscriptMem : slot.scriptSlot ∈
      (taggedAdmittedFixedScriptWithCompletedCounts (target := target)
        (base.map fun baseSlot => baseSlot.scriptSlot) counts).map
          (fun skeleton => skeleton.scriptSlot) := by
    exact List.mem_map.mpr ⟨slot, hslot, rfl⟩
  rw [taggedAdmittedFixedScriptWithCompletedCounts_map_scriptSlot] at hscriptMem
  rcases List.mem_map.mp hscriptMem with ⟨baseSlot, hbaseSlot, hscript_eq⟩
  change FiniteGPSExecutionSegmentCoordinatesMeasurable slot.scriptSlot.segment ∧
    FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable slot.scriptSlot.trackedEndpointJobs
  rw [← hscript_eq]
  exact hbase baseSlot hbaseSlot

/-- Endpoint-key compatibility is likewise preserved by independently
refining a literal slot layout with completed-head counts. -/
theorem taggedAdmittedFixedScriptWithCompletedCounts_trackedEndpointCompatible
    {Omega : Type*}
    (target : Category)
    (base : List (FiniteGPSFCFSFixedScriptSkeletonSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (hbase : ∀ slot ∈ base, slot.TrackedEndpointCompatible target)
    (counts : List Nat) :
    ∀ slot ∈ taggedAdmittedFixedScriptWithCompletedCounts (target := target)
      (base.map fun baseSlot => baseSlot.scriptSlot) counts,
      slot.TrackedEndpointCompatible target := by
  intro slot hslot
  have hscriptMem : slot.scriptSlot ∈
      (taggedAdmittedFixedScriptWithCompletedCounts (target := target)
        (base.map fun baseSlot => baseSlot.scriptSlot) counts).map
          (fun skeleton => skeleton.scriptSlot) := by
    exact List.mem_map.mpr ⟨slot, hslot, rfl⟩
  rw [taggedAdmittedFixedScriptWithCompletedCounts_map_scriptSlot] at hscriptMem
  rcases List.mem_map.mp hscriptMem with ⟨baseSlot, hbaseSlot, hscript_eq⟩
  change slot.scriptSlot.endpointJobs target =
    FiniteGPSFCFSFixedKeyQueue.erase slot.scriptSlot.trackedEndpointJobs
  rw [← hscript_eq]
  exact hbase baseSlot hbaseSlot

/-- The literal step list depends only on the fixed script-slot layout and
not on completed-count annotations. -/
theorem finiteGPSFCFSFixedScriptSteps_eq_of_map_scriptSlot_eq
    {Omega : Type*}
    (target : Category)
    (left right : List (FiniteGPSFCFSFixedScriptSkeletonSlot Category Omega
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)))
    (hslots : left.map (fun slot => slot.scriptSlot) =
      right.map (fun slot => slot.scriptSlot)) (omega : Omega) :
    finiteGPSFCFSFixedScriptSteps left omega =
      finiteGPSFCFSFixedScriptSteps right omega := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightSlot right =>
          simp at hslots
  | cons leftSlot left ih =>
      cases right with
      | nil =>
          simp at hslots
      | cons rightSlot right =>
          simp only [List.map_cons] at hslots
          have hhead : leftSlot.scriptSlot = rightSlot.scriptSlot :=
            List.cons.inj hslots |>.1
          have htail : left.map (fun slot => slot.scriptSlot) =
              right.map (fun slot => slot.scriptSlot) :=
            List.cons.inj hslots |>.2
          simp only [finiteGPSFCFSFixedScriptSteps]
          cases hactive : rightSlot.scriptSlot.active with
          | false =>
              have hleftActive : leftSlot.scriptSlot.active = false := by
                simpa [hhead] using hactive
              simp [hactive, hleftActive, ih right htail]
          | true =>
              have hleftActive : leftSlot.scriptSlot.active = true := by
                simpa [hhead] using hactive
              have hstep : leftSlot.step omega = rightSlot.step omega := by
                simp [FiniteGPSFCFSFixedScriptSkeletonSlot.step, hhead]
              simp [hactive, hleftActive, hstep, ih right htail]

/-- The source-prefix aggregate state used to initialize the empty fence. -/
def taggedAdmittedSourceFenceFixedSourceResult
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom)) :
    TaggedAdmittedSourceGoodCarrier target -> FiniteGPSBatchTraceResult Category :=
  taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern capacity weight
    (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms

/-- Static source and source-empty fence slots before independently attaching
the finite FCFS completed-count vector. -/
def taggedAdmittedSourceFenceFixedBaseSlots
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom) :
    List (FiniteGPSFCFSFixedScriptSkeletonSlot Category
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)) :=
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern capacity weight
    (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms ++
  finiteGPSFCFSEmptyFenceFixedScriptSlots (taggedAdmittedTargetCompletionKey target)
    capacity weight (fun z k => (sourceResult z).workload k)
    (fun z => (sourceResult z).currentTime)
    (fun z => horizon - (sourceResult z).currentTime) fenceAtoms

/-- The global fixed FCFS skeleton for a source prefix followed by its
literal empty-endpoint fence. -/
def taggedAdmittedSourceFenceFixedGlobalSlots
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat) :
    List (FiniteGPSFCFSFixedScriptSkeletonSlot Category
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category) (taggedAdmittedTargetCompletionKey target)) :=
  taggedAdmittedFixedScriptWithCompletedCounts (target := target)
    (taggedAdmittedSourceFenceFixedBaseSlots start horizon target pattern script capacity
      weight sourceAtoms fenceAtoms |>.map fun slot => slot.scriptSlot)
    counts

/-- One fully semantic Borel fiber for the literal source/fence response.
The three GPS components are explicit: source comparison pattern, every
source-gap comparison, and the source-empty fence comparison.  FCFS count
choices appear only in the final global skeleton predicate. -/
def taggedAdmittedSourceFenceFixedBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat) : Set (TaggedAdmittedSourceGoodCarrier target) :=
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  taggedAdmittedSourceArrivalPatternFiber start horizon target pattern ∩
    ({z | taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
      capacity weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z} ∩
      ({z | fenceAtoms.length =
        (finiteGPSActiveClasses (fun k => (sourceResult z).workload k)).card + 1} ∩
        ({z | finiteGPSFCFSEmptyFenceShapeMatches (taggedAdmittedTargetCompletionKey target)
          capacity weight (fun sample k => (sourceResult sample).workload k)
          (fun sample => (sourceResult sample).currentTime)
          (fun sample => horizon - (sourceResult sample).currentTime) fenceAtoms z} ∩
          {z | finiteGPSFCFSFixedScriptBranchMatches target []
            (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
              capacity weight sourceAtoms fenceAtoms counts) z})))

/-- The complete countable discrete index of a source/fence FCFS replay
branch.  Its components are executable source comparisons, executable source
and fence comparison atoms, and an independently chosen FCFS count vector. -/
abbrev TaggedAdmittedSourceFenceFixedBranchIndex (Category : Type*) :=
  Σ pattern : TaggedAdmittedSourceArrivalPattern Category,
    TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern ×
      List (List TaggedAdmittedSourceGapBranchAtom) ×
        List FiniteGPSFCFSEmptyFenceBranchAtom × List Nat

/-- The branch fiber selected by a complete static index. -/
def taggedAdmittedSourceFenceFixedBranchIndexFiber
    (start horizon : ℝ) (target : Category) (capacity : ℝ) (weight : Category -> ℝ)
    (index : TaggedAdmittedSourceFenceFixedBranchIndex Category) :
    Set (TaggedAdmittedSourceGoodCarrier target) :=
  taggedAdmittedSourceFenceFixedBranchFiber start horizon target index.1 index.2.1
    capacity weight index.2.2.1 index.2.2.2.1 index.2.2.2.2

/-- Every fully fixed source/fence/count branch is Borel on the Palm good
carrier.  All measurable comparisons are concrete executor comparisons; the
only countable discrete data are the finite pattern, shape atoms, and FCFS
completed-head vector. -/
theorem measurableSet_taggedAdmittedSourceFenceFixedBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat) :
    MeasurableSet (taggedAdmittedSourceFenceFixedBranchFiber start horizon target
      pattern script capacity weight sourceAtoms fenceAtoms counts) := by
  let zeroWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun _ _ => 0
  let startTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun _ => start
  have hzeroWork : ∀ k, Measurable (fun z => zeroWork z k) := by
    intro k
    simpa [zeroWork] using (measurable_const : Measurable (fun _ :
      TaggedAdmittedSourceGoodCarrier target => (0 : ℝ)))
  have hstartTime : Measurable startTime := by
    simpa [startTime] using (measurable_const : Measurable (fun _ :
      TaggedAdmittedSourceGoodCarrier target => start))
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  have hsourceResult : FiniteGPSBatchTraceResultMeasurable sourceResult := by
    simpa [sourceResult, taggedAdmittedSourceFenceFixedSourceResult, zeroWork,
      startTime] using
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult_measurable target
        pattern capacity weight zeroWork startTime hzeroWork hstartTime script.pivots
          sourceAtoms)
  let fenceWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun z k =>
    (sourceResult z).workload k
  let fenceTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
    (sourceResult z).currentTime
  let fenceDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
    horizon - fenceTime z
  have hfenceWork : ∀ k, Measurable (fun z => fenceWork z k) := by
    intro k
    exact hsourceResult.1 k
  have hfenceTime : Measurable fenceTime := hsourceResult.2.1
  have hfenceDelay : Measurable fenceDelay := measurable_const.sub hfenceTime
  have hsourceShape : MeasurableSet {z |
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
        weight zeroWork startTime script.pivots sourceAtoms z} :=
    measurableSet_taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
      capacity weight zeroWork startTime hzeroWork hstartTime script.pivots sourceAtoms
  have hfenceFuel : MeasurableSet {z | fenceAtoms.length =
      (finiteGPSActiveClasses (fenceWork z)).card + 1} := by
    exact measurableSet_eq_fun measurable_const
      ((measurable_finiteGPSActiveClasses_card_apply fenceWork hfenceWork).add
        measurable_const)
  have hfenceShape : MeasurableSet {z |
      finiteGPSFCFSEmptyFenceShapeMatches (taggedAdmittedTargetCompletionKey target)
        capacity weight fenceWork fenceTime fenceDelay fenceAtoms z} :=
    measurableSet_finiteGPSFCFSEmptyFenceShapeMatches
      (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
      fenceDelay hfenceWork hfenceTime hfenceDelay fenceAtoms
  let sourceSlots := taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
    target pattern capacity weight zeroWork startTime script.pivots sourceAtoms
  let fenceSlots := finiteGPSFCFSEmptyFenceFixedScriptSlots
    (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
    fenceDelay fenceAtoms
  let baseSlots := sourceSlots ++ fenceSlots
  have hsourceSlots : ∀ slot ∈ sourceSlots, slot.CoordinatesMeasurable target := by
    simpa [sourceSlots] using
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_coordinatesMeasurable
        target pattern capacity weight zeroWork startTime hzeroWork hstartTime script.pivots
          sourceAtoms)
  have hfenceSlots : ∀ slot ∈ fenceSlots, slot.CoordinatesMeasurable target := by
    simpa [fenceSlots] using
      (finiteGPSFCFSEmptyFenceFixedScriptSlots_coordinatesMeasurable
        (taggedAdmittedTargetCompletionKey target) target capacity weight fenceWork
        fenceTime fenceDelay hfenceWork hfenceTime hfenceDelay fenceAtoms)
  have hbaseSlots : ∀ slot ∈ baseSlots, slot.CoordinatesMeasurable target := by
    intro slot hslot
    simp only [baseSlots] at hslot
    rcases List.mem_append.mp hslot with hsource | hfence
    · exact hsourceSlots slot hsource
    · exact hfenceSlots slot hfence
  have hglobalSlots : ∀ slot ∈
      taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
        weight sourceAtoms fenceAtoms counts,
      slot.CoordinatesMeasurable target := by
    apply taggedAdmittedFixedScriptWithCompletedCounts_coordinatesMeasurable target baseSlots
      hbaseSlots counts
  have hemptyQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      ([] : List (FiniteGPSFCFSFixedKeyJobCoordinate
        (TaggedAdmittedSourceGoodCarrier target) (TaggedAdmittedSourceJobId Category)
        (taggedAdmittedTargetCompletionKey target))) := by
    simp [FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
      FiniteGPSFCFSFixedQueueCoordinatesMeasurable, FiniteGPSFCFSFixedKeyQueue.erase]
  have hfcfs : MeasurableSet {z |
      finiteGPSFCFSFixedScriptBranchMatches target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z} :=
    measurableSet_finiteGPSFCFSFixedScriptBranchMatches target []
      (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
        capacity weight sourceAtoms fenceAtoms counts) hemptyQueue hglobalSlots
  unfold taggedAdmittedSourceFenceFixedBranchFiber
  dsimp only
  exact (measurableSet_taggedAdmittedSourceArrivalPatternFiber start horizon target pattern).inter
    (hsourceShape.inter (hfenceFuel.inter (hfenceShape.inter hfcfs)))

/-- All real coordinates of a fully fixed source/fence/count replay are
Borel on the Palm good carrier.  This factors the coordinate obligation out
of both branch measurability and response measurability. -/
theorem taggedAdmittedSourceFenceFixedGlobalSlots_coordinatesMeasurable
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat) :
    ∀ slot ∈ taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
      capacity weight sourceAtoms fenceAtoms counts,
      slot.CoordinatesMeasurable target := by
  let zeroWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun _ _ => 0
  let startTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun _ => start
  have hzeroWork : ∀ k, Measurable (fun z => zeroWork z k) := by
    intro k
    simpa [zeroWork] using (measurable_const : Measurable (fun _ :
      TaggedAdmittedSourceGoodCarrier target => (0 : ℝ)))
  have hstartTime : Measurable startTime := by
    simpa [startTime] using (measurable_const : Measurable (fun _ :
      TaggedAdmittedSourceGoodCarrier target => start))
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  have hsourceResult : FiniteGPSBatchTraceResultMeasurable sourceResult := by
    simpa [sourceResult, taggedAdmittedSourceFenceFixedSourceResult, zeroWork,
      startTime] using
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult_measurable target
        pattern capacity weight zeroWork startTime hzeroWork hstartTime script.pivots
          sourceAtoms)
  let fenceWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun z k =>
    (sourceResult z).workload k
  let fenceTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
    (sourceResult z).currentTime
  let fenceDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
    horizon - fenceTime z
  have hfenceWork : ∀ k, Measurable (fun z => fenceWork z k) := by
    intro k
    exact hsourceResult.1 k
  have hfenceTime : Measurable fenceTime := hsourceResult.2.1
  have hfenceDelay : Measurable fenceDelay := measurable_const.sub hfenceTime
  let sourceSlots := taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
    target pattern capacity weight zeroWork startTime script.pivots sourceAtoms
  let fenceSlots := finiteGPSFCFSEmptyFenceFixedScriptSlots
    (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
      fenceDelay fenceAtoms
  let baseSlots := sourceSlots ++ fenceSlots
  have hsourceSlots : ∀ slot ∈ sourceSlots, slot.CoordinatesMeasurable target := by
    simpa [sourceSlots] using
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_coordinatesMeasurable
        target pattern capacity weight zeroWork startTime hzeroWork hstartTime script.pivots
          sourceAtoms)
  have hfenceSlots : ∀ slot ∈ fenceSlots, slot.CoordinatesMeasurable target := by
    simpa [fenceSlots] using
      (finiteGPSFCFSEmptyFenceFixedScriptSlots_coordinatesMeasurable
        (taggedAdmittedTargetCompletionKey target) target capacity weight fenceWork
        fenceTime fenceDelay hfenceWork hfenceTime hfenceDelay fenceAtoms)
  have hbaseSlots : ∀ slot ∈ baseSlots, slot.CoordinatesMeasurable target := by
    intro slot hslot
    simp only [baseSlots] at hslot
    rcases List.mem_append.mp hslot with hsource | hfence
    · exact hsourceSlots slot hsource
    · exact hfenceSlots slot hfence
  apply taggedAdmittedFixedScriptWithCompletedCounts_coordinatesMeasurable target baseSlots
    hbaseSlots counts

/-- The response of any fully static source/fence/count replay is Borel. -/
theorem measurable_taggedAdmittedSourceFenceFixedReplayResponse
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat) :
    Measurable (finiteGPSFCFSPaddedReplayResponse (taggedAdmittedTargetCompletionKey target)
      target
      (finiteGPSFCFSFixedScriptReplaySlots (taggedAdmittedTargetCompletionKey target) target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts))) := by
  have hemptyQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable
      ([] : List (FiniteGPSFCFSFixedKeyJobCoordinate
        (TaggedAdmittedSourceGoodCarrier target) (TaggedAdmittedSourceJobId Category)
        (taggedAdmittedTargetCompletionKey target))) := by
    simp [FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable,
      FiniteGPSFCFSFixedQueueCoordinatesMeasurable, FiniteGPSFCFSFixedKeyQueue.erase]
  exact measurable_finiteGPSFCFSFixedScriptReplayResponse
    (taggedAdmittedTargetCompletionKey target) target []
    (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
      weight sourceAtoms fenceAtoms counts)
    hemptyQueue
    (taggedAdmittedSourceFenceFixedGlobalSlots_coordinatesMeasurable start horizon target
      pattern script capacity weight sourceAtoms fenceAtoms counts)

/-- On a source-pattern/shape fiber, the static source aggregate state is
the actual pre-terminal executor state used by the literal horizon fence. -/
theorem taggedAdmittedSourceFenceFixedSourceResult_eq_preTerminalHistoryFinal_of_shape
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (hmatches : pattern.Matches start horizon target z.1)
    (hshape : taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
      capacity weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z) :
    taggedAdmittedSourceFenceFixedSourceResult start horizon target pattern script capacity
      weight sourceAtoms z =
      (taggedAdmittedFiniteGPSPreTerminalHistory start horizon target z.1 z.2 capacity weight
        (fun _ => 0)).final := by
  have hresult :=
    taggedAdmittedSourceArrivalPatternPreTerminalFixedResult_eq_finiteGPSRunBatchTrace_of_shape
      start horizon target z pattern hmatches capacity weight (fun _ _ => 0) (fun _ => start)
      script.pivots sourceAtoms script.pivot_mem hshape
  have htimes := script.arrivalTimes_eq_taggedAdmittedBatchTimeTrace_of_matches
    start horizon target z.1 hmatches
  rw [taggedAdmittedFiniteGPSPreTerminalHistory_final]
  change taggedAdmittedSourceFenceFixedSourceResult start horizon target pattern script capacity
      weight sourceAtoms z =
    finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z.1)
      start (fun _ => 0)
      (taggedAdmittedExternalBatchTrace start horizon target z.1 z.2).times
  have hrun :
      finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z.1)
        start (fun _ => 0)
        (script.pivots.map fun pivot => taggedAdmittedSourceArrival target z.1 pivot) =
      finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z.1)
        start (fun _ => 0) (taggedAdmittedBatchTimeTrace start horizon target z.1) := by
    exact congrArg
      (finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z.1)
        start (fun _ => 0)) htimes
  simpa [taggedAdmittedSourceFenceFixedSourceResult,
    taggedAdmittedFiniteGPSPreTerminalRun, finiteGPSRunExternalBatchTrace,
    taggedAdmittedExternalBatchTrace] using hresult.trans hrun

/-- On a complete semantic branch, the global fixed skeleton emits exactly
the literal source-labelled pre-terminal FCFS steps followed by the literal
source-empty computational horizon fence. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_eq_sourceFenceFixedGlobalSteps_of_branch
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat)
    (hfiber : z ∈ taggedAdmittedSourceFenceFixedBranchFiber start horizon target
      pattern script capacity weight sourceAtoms fenceAtoms counts) :
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps start horizon target z.1 z.2
      capacity weight =
      finiteGPSFCFSFixedScriptSteps
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z := by
  let zeroWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun _ _ => 0
  let startTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun _ => start
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  let sourceSlots := taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
    target pattern capacity weight zeroWork startTime script.pivots sourceAtoms
  let fenceWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample k =>
    (sourceResult sample).workload k
  let fenceTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
    (sourceResult sample).currentTime
  let fenceDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
    horizon - fenceTime sample
  let fenceSlots := finiteGPSFCFSEmptyFenceFixedScriptSlots
    (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
      fenceDelay fenceAtoms
  let baseSlots := sourceSlots ++ fenceSlots
  change pattern.Matches start horizon target z.1 ∧
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
        weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z ∧
      fenceAtoms.length =
        (finiteGPSActiveClasses (fun k => (sourceResult z).workload k)).card + 1 ∧
      finiteGPSFCFSEmptyFenceShapeMatches (taggedAdmittedTargetCompletionKey target)
        capacity weight fenceWork fenceTime fenceDelay fenceAtoms z ∧
      finiteGPSFCFSFixedScriptBranchMatches target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z at hfiber
  rcases hfiber with ⟨hmatches, hsourceShape, hfenceFuel, hfenceShape, _hfcfs⟩
  have hsourceSteps :
      taggedAdmittedFiniteGPSPreTerminalFCFSSteps start horizon target z.1 z.2 capacity
        weight (fun _ => 0) =
      finiteGPSFCFSFixedScriptSteps sourceSlots z := by
    have hprefix :=
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_preTerminalFixedScriptSteps_of_shape
        start horizon target z pattern hmatches capacity weight zeroWork startTime
        script.pivots sourceAtoms script.pivot_mem (by simpa [zeroWork, startTime] using
          hsourceShape)
    have htimes := script.arrivalTimes_eq_taggedAdmittedBatchTimeTrace_of_matches
      start horizon target z.1 hmatches
    change taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1 capacity
        weight start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z.1 z.2).times = _
    have htraceTime :
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1 capacity
          weight start (fun _ => 0)
          (taggedAdmittedExternalBatchTrace start horizon target z.1 z.2).times =
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1 capacity
          weight start (fun _ => 0)
          (script.pivots.map fun pivot => taggedAdmittedSourceArrival target z.1 pivot) := by
      simpa [taggedAdmittedExternalBatchTrace] using
        congrArg
          (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1
            capacity weight start (fun _ => 0)) htimes.symm
    exact htraceTime.trans (by simpa [sourceSlots, zeroWork, startTime] using hprefix)
  have hsourceResult : sourceResult z =
      (taggedAdmittedFiniteGPSPreTerminalHistory start horizon target z.1 z.2 capacity
        weight (fun _ => 0)).final := by
    simpa [sourceResult, zeroWork, startTime] using
      (taggedAdmittedSourceFenceFixedSourceResult_eq_preTerminalHistoryFinal_of_shape
        start horizon target z pattern script capacity weight sourceAtoms hmatches
          (by simpa [zeroWork, startTime] using hsourceShape))
  have hfenceSteps :
      taggedAdmittedFiniteGPSHorizonFenceFCFSSteps start horizon target z.1 z.2 capacity
        weight =
      finiteGPSFCFSFixedScriptSteps fenceSlots z := by
    change finiteGPSFCFSEmptyEndpointSteps
        (finiteGPSHorizonFenceSegments capacity weight
          (taggedAdmittedFiniteGPSPreTerminalHistory start horizon target z.1 z.2
            capacity weight (fun _ => 0)).final horizon) = _
    rw [← hsourceResult]
    change finiteGPSFCFSEmptyEndpointSteps
        (finiteGPSRunGapSegments ((finiteGPSActiveClasses (fenceWork z)).card + 1)
          capacity weight (fenceWork z) (fun _ => 0) (fenceTime z)
            (fenceDelay z)) = _
    rw [← hfenceFuel]
    simpa [fenceSlots] using
      (finiteGPSFCFSEmptyEndpointSteps_runGapSegments_eq_fixedScriptSteps_of_shape
        (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
        fenceDelay fenceAtoms z hfenceShape)
  have hbaseSteps :
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps start horizon target z.1 z.2 capacity
        weight = finiteGPSFCFSFixedScriptSteps baseSlots z := by
    unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
    simp only [baseSlots, finiteGPSFCFSFixedScriptSteps_append]
    rw [hsourceSteps, hfenceSteps]
  have hglobalMap :
      (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
        weight sourceAtoms fenceAtoms counts).map (fun slot => slot.scriptSlot) =
      baseSlots.map (fun slot => slot.scriptSlot) := by
    simpa [taggedAdmittedSourceFenceFixedGlobalSlots,
      taggedAdmittedSourceFenceFixedBaseSlots, sourceResult, sourceSlots, fenceWork,
      fenceTime, fenceDelay, fenceSlots, baseSlots,
      taggedAdmittedSourceFenceFixedSourceResult, zeroWork, startTime] using
      (taggedAdmittedFixedScriptWithCompletedCounts_map_scriptSlot
        (target := target) (taggedAdmittedSourceFenceFixedBaseSlots start horizon target
          pattern script capacity weight sourceAtoms fenceAtoms |>.map
            fun slot => slot.scriptSlot) counts)
  calc
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps start horizon target z.1 z.2 capacity
        weight = finiteGPSFCFSFixedScriptSteps baseSlots z := hbaseSteps
    _ = finiteGPSFCFSFixedScriptSteps
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z :=
      finiteGPSFCFSFixedScriptSteps_eq_of_map_scriptSlot_eq target baseSlots
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) hglobalMap.symm z

/-- The paper's tagged selector and the generic Boolean-key selector agree
on response values when every selected tagged completion retains its literal
Palm arrival time zero. -/
theorem taggedAdmittedFiniteGPSFirstTagTotal_eq_firstKeyResponseFromTrace
    (target : Category)
    (completions : List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)))
    (harrival_zero : ∀ completion ∈ completions,
      completion.identifier = (target, 0) -> completion.arrivalTime = 0) :
    (match taggedAdmittedFiniteGPSFirstTagCompletion? target completions with
      | some completion => completion.completionTime
      | none => 0) =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace
        (taggedAdmittedTargetCompletionKey target) completions := by
  rw [taggedAdmittedFiniteGPSFirstTagCompletion?_eq_firstKeyCompletion?]
  cases hselected : finiteGPSFCFSFirstKeyCompletion?
      (taggedAdmittedTargetCompletionKey target) completions with
  | none =>
      simp [finiteGPSFCFSFirstKeyCompletionResponseFromTrace, hselected]
  | some completion =>
      have htag : taggedAdmittedFiniteGPSFirstTagCompletion? target completions =
          some completion := by
        simpa [taggedAdmittedFiniteGPSFirstTagCompletion?_eq_firstKeyCompletion?]
          using hselected
      have hmem_tag := taggedAdmittedFiniteGPSFirstTagCompletion?_eq_some
        target completions completion htag
      have harrival : completion.arrivalTime = 0 :=
        harrival_zero completion hmem_tag.1 hmem_tag.2
      simp [finiteGPSFCFSFirstKeyCompletionResponseFromTrace, hselected, harrival]

/-- The literal total tagged horizon response is exactly the generic
first-key completion response from its actual FCFS trace. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_firstKeyResponseFromTrace
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category -> ℝ) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse start horizon target z htarget_good
      capacity weight =
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace
        (taggedAdmittedTargetCompletionKey target)
        (finiteGPSFCFSRunSegmentStepsClassCompletions taggedAdmittedEmptyFCFSLedger target
          (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps start horizon target z htarget_good
            capacity weight)) := by
  unfold taggedAdmittedFiniteGPSHorizonFenceTotalResponse
  unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
  unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
  apply taggedAdmittedFiniteGPSFirstTagTotal_eq_firstKeyResponseFromTrace target
  intro completion hcompletion hidentifier
  exact taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
    start horizon target z htarget_good capacity weight completion hcompletion hidentifier

/-- On a complete semantic source/fence/count branch, the literal total
response is the Borel fixed replay response.  The source and fence retain
their own executable shape witnesses; only completed FCFS heads are supplied
by the independent final count vector. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_sourceFenceFixedReplayResponse_of_branch
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (sourceAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (fenceAtoms : List FiniteGPSFCFSEmptyFenceBranchAtom)
    (counts : List Nat)
    (hfiber : z ∈ taggedAdmittedSourceFenceFixedBranchFiber start horizon target
      pattern script capacity weight sourceAtoms fenceAtoms counts) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse start horizon target z.1 z.2
      capacity weight =
      finiteGPSFCFSPaddedReplayResponse (taggedAdmittedTargetCompletionKey target) target
        (finiteGPSFCFSFixedScriptReplaySlots (taggedAdmittedTargetCompletionKey target)
          target []
          (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
            capacity weight sourceAtoms fenceAtoms counts)) z := by
  let zeroWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun _ _ => 0
  let startTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun _ => start
  let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
    pattern script capacity weight sourceAtoms
  let sourceSlots := taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
    target pattern capacity weight zeroWork startTime script.pivots sourceAtoms
  let fenceWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample k =>
    (sourceResult sample).workload k
  let fenceTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
    (sourceResult sample).currentTime
  let fenceDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
    horizon - fenceTime sample
  let fenceSlots := finiteGPSFCFSEmptyFenceFixedScriptSlots
    (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
      fenceDelay fenceAtoms
  let baseSlots := sourceSlots ++ fenceSlots
  change pattern.Matches start horizon target z.1 ∧
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
        weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z ∧
      fenceAtoms.length =
        (finiteGPSActiveClasses (fun k => (sourceResult z).workload k)).card + 1 ∧
      finiteGPSFCFSEmptyFenceShapeMatches (taggedAdmittedTargetCompletionKey target)
        capacity weight fenceWork fenceTime fenceDelay fenceAtoms z ∧
      finiteGPSFCFSFixedScriptBranchMatches target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z at hfiber
  rcases hfiber with ⟨hmatches, hsourceShape, hfenceFuel, hfenceShape, hfcfs⟩
  have hsteps :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_eq_sourceFenceFixedGlobalSteps_of_branch
      start horizon target z pattern script capacity weight sourceAtoms fenceAtoms counts
      (by
        exact ⟨hmatches, hsourceShape, hfenceFuel, hfenceShape, hfcfs⟩)
  have hsourceEndpoint : ∀ slot ∈ sourceSlots, slot.TrackedEndpointCompatible target := by
    simpa [sourceSlots] using
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_trackedEndpointCompatible
        target pattern capacity weight zeroWork startTime script.pivots sourceAtoms)
  have hfenceEndpoint : ∀ slot ∈ fenceSlots, slot.TrackedEndpointCompatible target := by
    simpa [fenceSlots] using
      (finiteGPSFCFSEmptyFenceFixedScriptSlots_trackedEndpointCompatible
        (taggedAdmittedTargetCompletionKey target) target capacity weight fenceWork fenceTime
          fenceDelay fenceAtoms)
  have hbaseEndpoint : ∀ slot ∈ baseSlots, slot.TrackedEndpointCompatible target := by
    intro slot hslot
    simp only [baseSlots] at hslot
    rcases List.mem_append.mp hslot with hsource | hfence
    · exact hsourceEndpoint slot hsource
    · exact hfenceEndpoint slot hfence
  have hglobalEndpoint : ∀ slot ∈
      taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
        weight sourceAtoms fenceAtoms counts,
      slot.TrackedEndpointCompatible target := by
    apply taggedAdmittedFixedScriptWithCompletedCounts_trackedEndpointCompatible target
      baseSlots hbaseEndpoint counts
  have hinitial :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).residualJobs target =
        (FiniteGPSFCFSFixedKeyQueue.erase
          ([] : List (FiniteGPSFCFSFixedKeyJobCoordinate
            (TaggedAdmittedSourceGoodCarrier target) (TaggedAdmittedSourceJobId Category)
            (taggedAdmittedTargetCompletionKey target)))).map fun coordinate => coordinate z := by
    simp [taggedAdmittedEmptyFCFSLedger, FiniteGPSFCFSFixedKeyQueue.erase]
  calc
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse start horizon target z.1 z.2
        capacity weight =
        finiteGPSFCFSFirstKeyCompletionResponseFromTrace
          (taggedAdmittedTargetCompletionKey target)
          (finiteGPSFCFSRunSegmentStepsClassCompletions taggedAdmittedEmptyFCFSLedger target
            (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps start horizon target z.1 z.2
              capacity weight)) :=
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_firstKeyResponseFromTrace
        start horizon target z.1 z.2 capacity weight
    _ = finiteGPSFCFSFirstKeyCompletionResponseFromTrace
          (taggedAdmittedTargetCompletionKey target)
          (finiteGPSFCFSRunSegmentStepsClassCompletions taggedAdmittedEmptyFCFSLedger target
            (finiteGPSFCFSFixedScriptSteps
              (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
                capacity weight sourceAtoms fenceAtoms counts) z)) := by
      rw [hsteps]
    _ = finiteGPSFCFSPaddedReplayResponse (taggedAdmittedTargetCompletionKey target) target
          (finiteGPSFCFSFixedScriptReplaySlots (taggedAdmittedTargetCompletionKey target)
            target []
            (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
              capacity weight sourceAtoms fenceAtoms counts)) z :=
      finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_fixedScriptReplayResponse_of_branch
        (taggedAdmittedTargetCompletionKey target) target taggedAdmittedEmptyFCFSLedger []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
          weight sourceAtoms fenceAtoms counts) z hinitial hglobalEndpoint hfcfs

/-- The semantic source/fence/count fibers cover every point of the Palm
good carrier.  At each point the shape atoms and their fuel are read from the
literal executor, while the independent count vector is supplied by the
generic FCFS branch-cover theorem. -/
theorem iUnion_taggedAdmittedSourceFenceFixedBranchIndexFiber_eq_univ
    (start horizon : ℝ) (target : Category) (capacity : ℝ) (weight : Category -> ℝ) :
    (⋃ index : TaggedAdmittedSourceFenceFixedBranchIndex Category,
      taggedAdmittedSourceFenceFixedBranchIndexFiber start horizon target capacity weight
        index) = Set.univ := by
  classical
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    let pattern := taggedAdmittedSourceArrivalPatternOf start horizon target z.1
    have hmatches : pattern.Matches start horizon target z.1 := by
      simpa [pattern] using (taggedAdmittedSourceArrivalPatternOf_matches start horizon target z.1)
    rcases TaggedAdmittedSourceArrivalPattern.nonempty_sortedRepresentativeScript_of_matches
      start horizon target z.1 pattern hmatches with ⟨script⟩
    let sourceAtoms := taggedAdmittedSourcePreTerminalExecutionShapeAtoms target pattern
      capacity weight z (fun _ => 0) start script.pivots
    have hsourceShape :
        taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
          weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z := by
      simpa [sourceAtoms] using
        (taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches_executionShapeAtoms
          target pattern capacity weight (fun _ _ => 0) (fun _ => start) z script.pivots)
    let sourceResult := taggedAdmittedSourceFenceFixedSourceResult start horizon target
      pattern script capacity weight sourceAtoms
    let fenceWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ := fun sample k =>
      (sourceResult sample).workload k
    let fenceTime : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
      (sourceResult sample).currentTime
    let fenceDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
      horizon - fenceTime sample
    let fuel := (finiteGPSActiveClasses (fenceWork z)).card + 1
    let fenceAtoms := taggedAdmittedEmptyFenceExecutionShapeAtoms fuel capacity weight
      (fenceWork z) (fenceTime z) (fenceDelay z)
    have hfenceFuel : fenceAtoms.length =
        (finiteGPSActiveClasses (fenceWork z)).card + 1 := by
      simpa [fenceAtoms, fuel] using
        (taggedAdmittedEmptyFenceExecutionShapeAtoms_length fuel capacity weight
          (fenceWork z) (fenceTime z) (fenceDelay z))
    have hfenceShape : finiteGPSFCFSEmptyFenceShapeMatches
        (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
        fenceDelay fenceAtoms z := by
      simpa [fenceAtoms] using
        (finiteGPSFCFSEmptyFenceShapeMatches_executionShapeAtoms
          (taggedAdmittedTargetCompletionKey target) capacity weight fenceWork fenceTime
          fenceDelay z fuel)
    let baseSlots := taggedAdmittedSourceFenceFixedBaseSlots start horizon target pattern script
      capacity weight sourceAtoms fenceAtoms
    rcases exists_taggedAdmittedFixedScriptWithCompletedCounts_branchMatches target []
      (baseSlots.map fun slot => slot.scriptSlot) z with ⟨counts, hfcfs⟩
    have hglobalFCFS : finiteGPSFCFSFixedScriptBranchMatches target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script capacity
          weight sourceAtoms fenceAtoms counts) z := by
      simpa [taggedAdmittedSourceFenceFixedGlobalSlots, baseSlots] using hfcfs
    refine Set.mem_iUnion.mpr ⟨⟨pattern, script, sourceAtoms, fenceAtoms, counts⟩, ?_⟩
    change z ∈ taggedAdmittedSourceFenceFixedBranchFiber start horizon target pattern script
      capacity weight sourceAtoms fenceAtoms counts
    change pattern.Matches start horizon target z.1 ∧
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern capacity
        weight (fun _ _ => 0) (fun _ => start) script.pivots sourceAtoms z ∧
      fenceAtoms.length =
        (finiteGPSActiveClasses (fun k => (sourceResult z).workload k)).card + 1 ∧
      finiteGPSFCFSEmptyFenceShapeMatches (taggedAdmittedTargetCompletionKey target)
        capacity weight fenceWork fenceTime fenceDelay fenceAtoms z ∧
      finiteGPSFCFSFixedScriptBranchMatches target []
        (taggedAdmittedSourceFenceFixedGlobalSlots start horizon target pattern script
          capacity weight sourceAtoms fenceAtoms counts) z
    exact ⟨hmatches, hsourceShape, hfenceFuel, hfenceShape, hglobalFCFS⟩

/-- The literal finite diagonal response is Borel on the Palm good carrier.
The proof glues actual source/fence execution fibers, not a named family of
synthetic cases: every fiber records the concrete comparisons performed by
the executable finite trace. -/
theorem measurable_taggedAdmittedGPSDiagonalFiniteResponse_goodCarrier
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (N : Nat) :
    Measurable (fun z : TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedGPSDiagonalFiniteResponse target z.1 z.2 G.capacity G.weight N) := by
  classical
  haveI : Countable (TaggedAdmittedSourceFenceFixedBranchIndex Category) := by
    infer_instance
  refine measurable_of_countable_measurable_cover
    (cover := fun index : TaggedAdmittedSourceFenceFixedBranchIndex Category =>
      taggedAdmittedSourceFenceFixedBranchIndexFiber
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target G.capacity G.weight index)
    (hcover_measurable := ?_)
    (hcover := ?_)
    (f := fun z : TaggedAdmittedSourceGoodCarrier target =>
      taggedAdmittedGPSDiagonalFiniteResponse target z.1 z.2 G.capacity G.weight N)
    (piece := fun index => finiteGPSFCFSPaddedReplayResponse
      (taggedAdmittedTargetCompletionKey target) target
      (finiteGPSFCFSFixedScriptReplaySlots (taggedAdmittedTargetCompletionKey target)
        target []
        (taggedAdmittedSourceFenceFixedGlobalSlots
          (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
          target index.1 index.2.1 G.capacity G.weight index.2.2.1 index.2.2.2.1
          index.2.2.2.2)))
    (hpiece := ?_)
    (hagree := ?_)
  · intro index
    simpa [taggedAdmittedSourceFenceFixedBranchIndexFiber] using
      (measurableSet_taggedAdmittedSourceFenceFixedBranchFiber
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target index.1 index.2.1 G.capacity G.weight index.2.2.1 index.2.2.2.1
        index.2.2.2.2)
  · exact iUnion_taggedAdmittedSourceFenceFixedBranchIndexFiber_eq_univ
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target G.capacity G.weight
  · intro index
    exact measurable_taggedAdmittedSourceFenceFixedReplayResponse
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target index.1 index.2.1 G.capacity G.weight index.2.2.1 index.2.2.2.1
      index.2.2.2.2
  · intro index z hz
    change z ∈ taggedAdmittedSourceFenceFixedBranchFiber
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target index.1 index.2.1 G.capacity G.weight index.2.2.1 index.2.2.2.1
      index.2.2.2.2 at hz
    simpa [taggedAdmittedGPSDiagonalFiniteResponse] using
      (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_sourceFenceFixedReplayResponse_of_branch
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z index.1 index.2.1 G.capacity G.weight index.2.2.1 index.2.2.2.1
        index.2.2.2.2 hz)

/-- The fully totalized diagonal finite response used by the canonical GPS
tail is Borel.  Its bad-carrier branch is the explicit zero branch already
present in the executable definition. -/
theorem measurable_taggedAdmittedGPSDiagonalFiniteResponseTotal
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (N : Nat) :
    Measurable (taggedAdmittedGPSDiagonalFiniteResponseTotal M G target N) := by
  exact measurable_taggedAdmittedGPSDiagonalFiniteResponseTotal_of_good_measurable
    M G target N
    (measurable_taggedAdmittedGPSDiagonalFiniteResponse_goodCarrier M G target N)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
