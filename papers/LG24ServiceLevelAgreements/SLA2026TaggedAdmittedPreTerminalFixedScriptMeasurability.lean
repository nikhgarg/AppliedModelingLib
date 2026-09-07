import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSEmptyFenceFixedScriptMeasurability
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedPatternGapFixedScriptMeasurability
import Mathlib.Tactic

/-!
# Full fixed-script presentation of a finite tagged source prefix

This module composes the one-gap source-labelled fixed-script bridge over a
fixed tie-aware source representative script.  Every gap retains its actual
active-class fuel as explicit finite branch data.  In particular, the Borel
construction covers the complete Palm good carrier rather than using the
nonnegative-work termination theorem to silently discard off-event inputs.

The source-empty horizon-fence suffix is composed separately after this
pre-terminal adapter has identified the literal source prefix.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.Queueing

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Concatenate one fixed source-pattern GPS-gap script for every listed
representative.  The state carried to the next gap is the actual bounded
runner result at the current branch's fixed fuel.  If that runner does not
reach a later source batch, the associated full-shape predicate below makes
all later slots inactive rather than fabricating a source execution. -/
def taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ) :
    List (TaggedAdmittedSourceJobId Category) ->
      List (List TaggedAdmittedSourceGapBranchAtom) ->
        List (FiniteGPSFCFSFixedScriptSkeletonSlot Category
          (TaggedAdmittedSourceGoodCarrier target)
          (TaggedAdmittedSourceJobId Category)
          (taggedAdmittedTargetCompletionKey target))
  | [], _ => []
  | _ :: _, [] => []
  | pivot :: pivots, atoms :: gapAtoms =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        taggedAdmittedSourceArrival target z.1 pivot
      let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        arrival z - currentTime z
      let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
        fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      taggedAdmittedSourceArrivalPatternGapFixedScriptSlots target pattern pivot
        capacity weight work currentTime nextBatchDelay atoms ++
        taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight (fun z => (gap z).workload) arrival pivots gapAtoms

/-- The fixed-slot constructor specialized to a source comparison pattern's
sorted representative script. -/
def taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlotsOfScript
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (script : TaggedAdmittedSourceArrivalPattern.SortedRepresentativeScript pattern)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)) :=
  taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
    capacity weight work currentTime script.pivots gapAtoms

/-- The aggregate finite GPS state carried by a fixed source-prefix script.
Unlike the FCFS slots, this value records the whole executor result needed to
start the source-empty horizon fence.  It follows the actual `batchApplied`
bit of each bounded gap, including the partial-state stop case. -/
def taggedAdmittedSourceArrivalPatternPreTerminalFixedResult
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ) :
    List (TaggedAdmittedSourceJobId Category) ->
      List (List TaggedAdmittedSourceGapBranchAtom) ->
        TaggedAdmittedSourceGoodCarrier target -> FiniteGPSBatchTraceResult Category
  | [], _ => fun z =>
      { workload := work z
        currentTime := currentTime z
        service := fun _ => 0 }
  | _ :: _, [] => fun z =>
      { workload := work z
        currentTime := currentTime z
        service := fun _ => 0 }
  | pivot :: pivots, atoms :: gapAtoms =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        taggedAdmittedSourceArrival target z.1 pivot
      let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        arrival z - currentTime z
      let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
        fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      fun z =>
        if (gap z).batchApplied = true then
          let later := taggedAdmittedSourceArrivalPatternPreTerminalFixedResult
            target pattern capacity weight (fun sample => (gap sample).workload) arrival
              pivots gapAtoms z
          { workload := later.workload
            currentTime := later.currentTime
            service := fun k => (gap z).service k + later.service k }
        else
          { workload := (gap z).workload
            currentTime := arrival z - (gap z).remainingDelay
            service := (gap z).service }

/-- The fixed source-prefix aggregate state is coordinatewise Borel.  This
is a direct finite decomposition through the executable `batchApplied` bit,
so it remains valid off the nonnegative-work carrier as well. -/
theorem taggedAdmittedSourceArrivalPatternPreTerminalFixedResult_measurable
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime) :
    ∀ (pivots : List (TaggedAdmittedSourceJobId Category))
      (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)),
      FiniteGPSBatchTraceResultMeasurable
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
          capacity weight work currentTime pivots gapAtoms) := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      intro gapAtoms
      refine ⟨?_, ?_, ?_⟩
      · intro k
        simpa [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult] using hwork k
      · simpa [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult] using hcurrentTime
      · intro k
        simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult]
  | cons pivot pivots ih =>
      intro gapAtoms
      cases gapAtoms with
      | nil =>
          refine ⟨?_, ?_, ?_⟩
          · intro k
            simpa [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult] using hwork k
          · simpa [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult] using hcurrentTime
          · intro k
            simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult]
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
          have hbatchWork : ∀ k, Measurable (fun z => batchWork z k) := by
            intro k
            exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
              target pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            taggedAdmittedSourceArrival target z.1 pivot
          have harrival : Measurable arrival :=
            measurable_taggedAdmittedSourceArrival_goodCarrier target pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            arrival z - currentTime z
          have hnextBatchDelay : Measurable nextBatchDelay := harrival.sub hcurrentTime
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)
          have hgap : FiniteGPSGapRunResultMeasurable gap := by
            exact finiteGPSGapRunResultMeasurable_apply atoms.length capacity weight
              work batchWork hwork hbatchWork nextBatchDelay hnextBatchDelay
          have htail := ih (work := fun z => (gap z).workload)
            (currentTime := arrival) hgap.1 harrival gapAtoms
          have hbatchApplied : MeasurableSet {z | (gap z).batchApplied = true} :=
            (MeasurableSet.singleton true).preimage hgap.2.2.2
          refine ⟨?_, ?_, ?_⟩
          · intro k
            have hformula :
                (fun z =>
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                    capacity weight work currentTime (pivot :: pivots)
                      (atoms :: gapAtoms) z).workload k) =
                fun z => if (gap z).batchApplied = true then
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                    capacity weight (fun later => (gap later).workload) arrival pivots
                      gapAtoms z).workload k
                else (gap z).workload k := by
              funext z
              by_cases h : (gap z).batchApplied = true <;>
                simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult,
                  batchWork, arrival, nextBatchDelay, gap, h]
            rw [hformula]
            exact Measurable.ite hbatchApplied (htail.1 k) (hgap.1 k)
          · have hformula :
                (fun z =>
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                    capacity weight work currentTime (pivot :: pivots)
                      (atoms :: gapAtoms) z).currentTime) =
                fun z => if (gap z).batchApplied = true then
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                    capacity weight (fun later => (gap later).workload) arrival pivots
                      gapAtoms z).currentTime
                else arrival z - (gap z).remainingDelay := by
              funext z
              by_cases h : (gap z).batchApplied = true <;>
                simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult,
                  batchWork, arrival, nextBatchDelay, gap, h]
            rw [hformula]
            exact Measurable.ite hbatchApplied htail.2.1 (harrival.sub hgap.2.1)
          · intro k
            have hformula :
                (fun z =>
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                    capacity weight work currentTime (pivot :: pivots)
                      (atoms :: gapAtoms) z).service k) =
                fun z => if (gap z).batchApplied = true then
                  (gap z).service k +
                    (taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                      capacity weight (fun later => (gap later).workload) arrival pivots
                        gapAtoms z).service k
                else (gap z).service k := by
              funext z
              by_cases h : (gap z).batchApplied = true <;>
                simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult,
                  batchWork, arrival, nextBatchDelay, gap, h]
            rw [hformula]
            exact Measurable.ite hbatchApplied ((hgap.2.2.1 k).add (htail.2.2 k))
              (hgap.2.2.1 k)

/-- Every coordinate in a complete fixed source-prefix script is Borel.  The
proof runs over fixed representative and branch lists; source identifiers are
fixed labels while only their real arrival/work coordinates are measured. -/
theorem taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_coordinatesMeasurable
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime) :
    ∀ (pivots : List (TaggedAdmittedSourceJobId Category))
      (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)),
      ∀ slot ∈ taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
        target pattern capacity weight work currentTime pivots gapAtoms,
        slot.CoordinatesMeasurable target := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      intro gapAtoms slot hslot
      simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
  | cons pivot pivots ih =>
      intro gapAtoms
      cases gapAtoms with
      | nil =>
          intro slot hslot
          simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
          have hbatchWork : ∀ k, Measurable (fun z => batchWork z k) := by
            intro k
            exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
              target pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            taggedAdmittedSourceArrival target z.1 pivot
          have harrival : Measurable arrival :=
            measurable_taggedAdmittedSourceArrival_goodCarrier target pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            arrival z - currentTime z
          have hnextBatchDelay : Measurable nextBatchDelay := harrival.sub hcurrentTime
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)
          have hgap : FiniteGPSGapRunResultMeasurable gap := by
            exact finiteGPSGapRunResultMeasurable_apply atoms.length capacity weight
              work batchWork hwork hbatchWork nextBatchDelay hnextBatchDelay
          have hgapSlots :=
            taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_coordinatesMeasurable
              target pattern pivot capacity weight work currentTime nextBatchDelay
              hwork hcurrentTime hnextBatchDelay atoms
          have htail := ih (work := fun z => (gap z).workload)
            (currentTime := arrival) hgap.1 harrival gapAtoms
          intro slot hslot
          simp only [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
          rcases List.mem_append.mp hslot with hslot | hslot
          · exact hgapSlots slot hslot
          · exact htail slot hslot

/-- Every slot in a concatenated source-prefix script carries the same
literal target endpoint representation as its underlying one-gap script. -/
theorem taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_trackedEndpointCompatible
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ) :
    ∀ (pivots : List (TaggedAdmittedSourceJobId Category))
      (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)),
      ∀ slot ∈ taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots
        target pattern capacity weight work currentTime pivots gapAtoms,
        slot.TrackedEndpointCompatible target := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      intro gapAtoms slot hslot
      simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
  | cons pivot pivots ih =>
      intro gapAtoms
      cases gapAtoms with
      | nil =>
          intro slot hslot
          simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            taggedAdmittedSourceArrival target z.1 pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            arrival z - currentTime z
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)
          have hgap :=
            taggedAdmittedSourceArrivalPatternGapFixedScriptSlots_trackedEndpointCompatible
              target pattern pivot capacity weight work currentTime nextBatchDelay atoms
          have htail := ih (work := fun z => (gap z).workload)
            (currentTime := arrival) gapAtoms
          intro slot hslot
          simp only [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots] at hslot
          rcases List.mem_append.mp hslot with hslot | hslot
          · exact hgap slot hslot
          · exact htail slot hslot

/-- A static collection of later source-gap branch lists is inactive when
every one of its padded atoms is inactive.  This is used precisely on the
actual stopped-runner branch: it represents no later source execution. -/
def TaggedAdmittedSourceGapAtomListsAllInactive :
    List (List TaggedAdmittedSourceGapBranchAtom) -> Prop :=
  List.Forall fun atoms => atoms.Forall fun atom => atom.active = false

/-- If every remaining source-gap atom is inactive, the corresponding suffix
of the full fixed script emits no FCFS steps. -/
theorem finiteGPSFCFSFixedScriptSteps_preTerminalSlots_eq_nil_of_gapAtomsAllInactive
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ) :
    ∀ (pivots : List (TaggedAdmittedSourceJobId Category))
      (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
      (z : TaggedAdmittedSourceGoodCarrier target),
      TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms ->
      finiteGPSFCFSFixedScriptSteps
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight work currentTime pivots gapAtoms) z = [] := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      intro gapAtoms z _
      rfl
  | cons pivot pivots ih =>
      intro gapAtoms z hinactive
      cases gapAtoms with
      | nil =>
          rfl
      | cons atoms gapAtoms =>
          simp only [TaggedAdmittedSourceGapAtomListsAllInactive, List.forall_cons] at hinactive
          rcases hinactive with ⟨hatomsInactive, htailInactive⟩
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun sample k =>
              taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            taggedAdmittedSourceArrival target sample.1 pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            arrival sample - currentTime sample
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun sample => finiteGPSRunGap atoms.length capacity weight (work sample)
              (batchWork sample) (nextBatchDelay sample)
          have hgapEmpty :=
            finiteGPSFCFSFixedScriptSteps_gapSlots_eq_nil_of_forall_inactive
              target pattern pivot capacity weight work currentTime nextBatchDelay
              atoms z hatomsInactive
          have htail := ih (work := fun sample => (gap sample).workload)
            (currentTime := arrival) gapAtoms z htailInactive
          simp only [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots]
          rw [finiteGPSFCFSFixedScriptSteps_append]
          rw [hgapEmpty, htail]
          rfl

/-- The finite semantic branch predicate for an entire fixed source-prefix
script.  It fixes the literal active-class fuel of each reached gap, its
actual GPS event shape, and whether the bounded runner reaches the next
source batch.  If it does not, all remaining script atoms must be inactive.
-/
def taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ) :
    List (TaggedAdmittedSourceJobId Category) ->
      List (List TaggedAdmittedSourceGapBranchAtom) ->
        TaggedAdmittedSourceGoodCarrier target -> Prop
  | [], [] => fun _ => True
  | [], _ :: _ => fun _ => False
  | _ :: _, [] => fun _ => False
  | pivot :: pivots, atoms :: gapAtoms =>
      let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
        fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
      let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        taggedAdmittedSourceArrival target z.1 pivot
      let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
        arrival z - currentTime z
      let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
        fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
          (nextBatchDelay z)
      fun z => atoms.length = (finiteGPSActiveClasses (work z)).card + 1 ∧
        taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot
          capacity weight work currentTime nextBatchDelay atoms z ∧
        if (gap z).batchApplied = true then
          taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
            capacity weight (fun later => (gap later).workload) arrival pivots gapAtoms z
        else TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms

/-- Every complete actual-fuel source-prefix branch is Borel.  Its finite
case split follows the runner's genuine `batchApplied` bit, so an exhausted
gap ends the source prefix instead of being treated as a successful source
arrival. -/
theorem measurableSet_taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime) :
    ∀ (pivots : List (TaggedAdmittedSourceJobId Category))
      (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)),
      MeasurableSet {z |
        taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
          capacity weight work currentTime pivots gapAtoms z} := by
  intro pivots
  induction pivots generalizing work currentTime with
  | nil =>
      intro gapAtoms
      cases gapAtoms <;>
        simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches]
  | cons pivot pivots ih =>
      intro gapAtoms
      cases gapAtoms with
      | nil =>
          simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches]
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun z k => taggedAdmittedSourceArrivalPatternBlockWork target z.1 pattern pivot k
          have hbatchWork : ∀ k, Measurable (fun z => batchWork z k) := by
            intro k
            exact measurable_taggedAdmittedSourceArrivalPatternBlockWork_goodCarrier
              target pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            taggedAdmittedSourceArrival target z.1 pivot
          have harrival : Measurable arrival :=
            measurable_taggedAdmittedSourceArrival_goodCarrier target pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun z =>
            arrival z - currentTime z
          have hnextBatchDelay : Measurable nextBatchDelay := harrival.sub hcurrentTime
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun z => finiteGPSRunGap atoms.length capacity weight (work z) (batchWork z)
              (nextBatchDelay z)
          have hgap : FiniteGPSGapRunResultMeasurable gap := by
            exact finiteGPSGapRunResultMeasurable_apply atoms.length capacity weight
              work batchWork hwork hbatchWork nextBatchDelay hnextBatchDelay
          have hactiveCard : Measurable fun z =>
              (finiteGPSActiveClasses (work z)).card :=
            measurable_finiteGPSActiveClasses_card_apply work hwork
          have hfuel : MeasurableSet {z |
              atoms.length = (finiteGPSActiveClasses (work z)).card + 1} := by
            exact measurableSet_eq_fun measurable_const
              (hactiveCard.add measurable_const)
          have hgapShape :=
            measurableSet_taggedAdmittedSourceArrivalPatternGapShapeMatches
              target pattern pivot capacity weight work currentTime nextBatchDelay
              hwork hcurrentTime hnextBatchDelay atoms
          have htail := ih (work := fun z => (gap z).workload)
            (currentTime := arrival) hgap.1 harrival gapAtoms
          have hbatchApplied : MeasurableSet {z | (gap z).batchApplied = true} :=
            (MeasurableSet.singleton true).preimage hgap.2.2.2
          by_cases hinactive : TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms
          · have hset : {z |
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight work currentTime (pivot :: pivots)
                    (atoms :: gapAtoms) z} =
                ({z | atoms.length = (finiteGPSActiveClasses (work z)).card + 1} ∩
                  {z | taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot
                    capacity weight work currentTime nextBatchDelay atoms z}) ∩
                  ({z | (gap z).batchApplied = true} ∩
                    {z | taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
                      target pattern capacity weight (fun later => (gap later).workload)
                        arrival pivots gapAtoms z} ∪
                    {z | (gap z).batchApplied ≠ true}) := by
                ext z
                by_cases hbatch : (gap z).batchApplied = true
                · simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
                    batchWork, arrival, nextBatchDelay, gap, hbatch, hinactive, and_assoc]
                · simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
                    batchWork, arrival, nextBatchDelay, gap, hbatch, hinactive, and_assoc]
            rw [hset]
            exact (hfuel.inter hgapShape).inter
              ((hbatchApplied.inter htail).union hbatchApplied.compl)
          · have hset : {z |
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight work currentTime (pivot :: pivots)
                    (atoms :: gapAtoms) z} =
                ({z | atoms.length = (finiteGPSActiveClasses (work z)).card + 1} ∩
                  {z | taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot
                    capacity weight work currentTime nextBatchDelay atoms z}) ∩
                  ({z | (gap z).batchApplied = true} ∩
                    {z | taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
                      target pattern capacity weight (fun later => (gap later).workload)
                        arrival pivots gapAtoms z}) := by
                ext z
                by_cases hbatch : (gap z).batchApplied = true
                · simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
                    batchWork, arrival, nextBatchDelay, gap, hbatch, hinactive, and_assoc]
                · simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
                    batchWork, arrival, nextBatchDelay, gap, hbatch, hinactive, and_assoc]
            rw [hset]
            exact (hfuel.inter hgapShape).inter (hbatchApplied.inter htail)

/-- On a matching source-pattern fiber, a complete actual-fuel prefix shape
identifies the literal tagged pre-terminal trace with its static FCFS script.
The proof follows the executable `batchApplied` branch at every source epoch:
when it is false, the semantic shape requires the remaining padded scripts to
be inactive, rather than pretending that later source batches were reached. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_preTerminalFixedScriptSteps_of_shape
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z.1)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (hpivots : ∀ pivot ∈ pivots, pivot ∈ pattern.labels)
    (hshape : taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
      target pattern capacity weight work currentTime pivots gapAtoms z) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1
      capacity weight (currentTime z) (work z)
      (pivots.map fun pivot => taggedAdmittedSourceArrival target z.1 pivot) =
      finiteGPSFCFSFixedScriptSteps
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight work currentTime pivots gapAtoms) z := by
  induction pivots generalizing work currentTime gapAtoms with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
        taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots,
        finiteGPSFCFSFixedScriptSteps]
  | cons pivot pivots ih =>
      cases gapAtoms with
      | nil =>
          simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches] at hshape
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun sample k =>
              taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            taggedAdmittedSourceArrival target sample.1 pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            arrival sample - currentTime sample
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun sample => finiteGPSRunGap atoms.length capacity weight (work sample)
              (batchWork sample) (nextBatchDelay sample)
          have hpivot : pivot ∈ pattern.labels := hpivots pivot (by simp)
          have hbatch : batchWork z =
              taggedAdmittedBatchAt start horizon target z.1 (arrival z) := by
            funext k
            exact taggedAdmittedSourceArrivalPatternBlockWork_eq_taggedAdmittedBatchAt_of_matches
              start horizon target z.1 pattern hmatches pivot hpivot k
          have hshape' : atoms.length = (finiteGPSActiveClasses (work z)).card + 1 ∧
              taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot
                capacity weight work currentTime nextBatchDelay atoms z ∧
              (if (gap z).batchApplied = true then
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight (fun later => (gap later).workload) arrival pivots
                    gapAtoms z
              else TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms) := by
            simpa [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
              batchWork, arrival, nextBatchDelay, gap] using hshape
          rcases hshape' with ⟨hfuel, hgapShape, htailShape⟩
          have hgapSteps :=
            taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_fixedScriptSteps_of_shape
              start horizon target z pattern hmatches pivot hpivot capacity weight work
              currentTime nextBatchDelay atoms hgapShape
          have hgapSteps' :
              taggedAdmittedFiniteGPSGapSegmentJobSteps start horizon target z.1 (arrival z)
                ((finiteGPSActiveClasses (work z)).card + 1) capacity weight (work z)
                (currentTime z) (arrival z - currentTime z) =
                finiteGPSFCFSFixedScriptSteps
                  (taggedAdmittedSourceArrivalPatternGapFixedScriptSlots target pattern pivot
                    capacity weight work currentTime nextBatchDelay atoms) z := by
            simpa [arrival, nextBatchDelay, hfuel] using hgapSteps
          by_cases hbatchApplied : (gap z).batchApplied = true
          · have hbatchApplied' :
                (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                  capacity weight (work z)
                  (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                  (arrival z - currentTime z)).batchApplied = true := by
                simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using
                  hbatchApplied
            have htailShape' :
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight (fun later => (gap later).workload) arrival pivots
                    gapAtoms z := by
              simpa [hbatchApplied] using htailShape
            have htail := ih (work := fun later => (gap later).workload)
              (currentTime := arrival) (gapAtoms := gapAtoms)
              (fun later hlater => hpivots later (by simp [hlater])) htailShape'
            have htail' :
                taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1
                  capacity weight (arrival z)
                  (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                    capacity weight (work z)
                    (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                    (arrival z - currentTime z)).workload
                  (pivots.map fun later => taggedAdmittedSourceArrival target z.1 later) =
                finiteGPSFCFSFixedScriptSteps
                  (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
                    capacity weight (fun later => (gap later).workload) arrival pivots
                      gapAtoms) z := by
              simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using htail
            simp only [List.map_cons]
            rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
              start horizon target z.1 capacity weight (work z) (currentTime z) (arrival z)
                (pivots.map fun later => taggedAdmittedSourceArrival target z.1 later)
                hbatchApplied']
            simp only [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots]
            rw [finiteGPSFCFSFixedScriptSteps_append, hgapSteps', htail']
          · have hbatchNotApplied' :
                (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                  capacity weight (work z)
                  (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                  (arrival z - currentTime z)).batchApplied ≠ true := by
                simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using
                  hbatchApplied
            have hinactive : TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms := by
              simpa [hbatchApplied] using htailShape
            have htailEmpty :=
              finiteGPSFCFSFixedScriptSteps_preTerminalSlots_eq_nil_of_gapAtomsAllInactive
                target pattern capacity weight (fun later => (gap later).workload) arrival
                  pivots gapAtoms z hinactive
            simp only [List.map_cons]
            rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
              start horizon target z.1 capacity weight (work z) (currentTime z) (arrival z)
                (pivots.map fun later => taggedAdmittedSourceArrival target z.1 later)
                hbatchNotApplied']
            simp only [taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots]
            rw [finiteGPSFCFSFixedScriptSteps_append, hgapSteps', htailEmpty]
            simpa [arrival, nextBatchDelay]

/-- On a semantic source-prefix shape, the Borel aggregate state carried by
the fixed script is the literal finite GPS batch-runner state.  This is the
state equality used to attach the source-empty horizon fence; it preserves a
partial runner state when a bounded gap does not reach its pending batch. -/
theorem taggedAdmittedSourceArrivalPatternPreTerminalFixedResult_eq_finiteGPSRunBatchTrace_of_shape
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (hmatches : pattern.Matches start horizon target z.1)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (hpivots : ∀ pivot ∈ pivots, pivot ∈ pattern.labels)
    (hshape : taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
      target pattern capacity weight work currentTime pivots gapAtoms z) :
    taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
      capacity weight work currentTime pivots gapAtoms z =
      finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z.1)
        (currentTime z) (work z)
        (pivots.map fun pivot => taggedAdmittedSourceArrival target z.1 pivot) := by
  induction pivots generalizing work currentTime gapAtoms with
  | nil =>
      simp [taggedAdmittedSourceArrivalPatternPreTerminalFixedResult,
        finiteGPSRunBatchTrace]
  | cons pivot pivots ih =>
      cases gapAtoms with
      | nil =>
          simp [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches] at hshape
      | cons atoms gapAtoms =>
          let batchWork : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ :=
            fun sample k =>
              taggedAdmittedSourceArrivalPatternBlockWork target sample.1 pattern pivot k
          let arrival : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            taggedAdmittedSourceArrival target sample.1 pivot
          let nextBatchDelay : TaggedAdmittedSourceGoodCarrier target -> ℝ := fun sample =>
            arrival sample - currentTime sample
          let gap : TaggedAdmittedSourceGoodCarrier target -> FiniteGPSGapRunResult Category :=
            fun sample => finiteGPSRunGap atoms.length capacity weight (work sample)
              (batchWork sample) (nextBatchDelay sample)
          have hpivot : pivot ∈ pattern.labels := hpivots pivot (by simp)
          have hbatch : batchWork z =
              taggedAdmittedBatchAt start horizon target z.1 (arrival z) := by
            funext k
            exact taggedAdmittedSourceArrivalPatternBlockWork_eq_taggedAdmittedBatchAt_of_matches
              start horizon target z.1 pattern hmatches pivot hpivot k
          have hshape' : atoms.length = (finiteGPSActiveClasses (work z)).card + 1 ∧
              taggedAdmittedSourceArrivalPatternGapShapeMatches target pattern pivot
                capacity weight work currentTime nextBatchDelay atoms z ∧
              (if (gap z).batchApplied = true then
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight (fun later => (gap later).workload) arrival pivots
                    gapAtoms z
              else TaggedAdmittedSourceGapAtomListsAllInactive gapAtoms) := by
            simpa [taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches,
              batchWork, arrival, nextBatchDelay, gap] using hshape
          rcases hshape' with ⟨hfuel, _hgapShape, htailShape⟩
          by_cases hbatchApplied : (gap z).batchApplied = true
          · have hbatchApplied' :
                (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                  capacity weight (work z)
                  (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                  (arrival z - currentTime z)).batchApplied = true := by
                simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using
                  hbatchApplied
            have htailShape' :
                taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
                  capacity weight (fun later => (gap later).workload) arrival pivots
                    gapAtoms z := by
              simpa [hbatchApplied] using htailShape
            have htail := ih (work := fun later => (gap later).workload)
              (currentTime := arrival) (gapAtoms := gapAtoms)
              (fun later hlater => hpivots later (by simp [hlater])) htailShape'
            have htail' :
                taggedAdmittedSourceArrivalPatternPreTerminalFixedResult target pattern
                  capacity weight (fun later => (gap later).workload) arrival pivots
                    gapAtoms z =
                finiteGPSRunBatchTrace capacity weight
                  (taggedAdmittedBatchAt start horizon target z.1)
                  (arrival z)
                  (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                    capacity weight (work z)
                    (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                    (arrival z - currentTime z)).workload
                  (pivots.map fun later => taggedAdmittedSourceArrival target z.1 later) := by
              simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using htail
            simp only [List.map_cons]
            rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight
              (taggedAdmittedBatchAt start horizon target z.1) (currentTime z) (work z)
              (arrival z) (pivots.map fun later =>
                taggedAdmittedSourceArrival target z.1 later) hbatchApplied']
            change (if (gap z).batchApplied = true then _ else _) = _
            rw [if_pos hbatchApplied, htail']
            simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch]
          · have hbatchNotApplied' :
                (finiteGPSRunGap ((finiteGPSActiveClasses (work z)).card + 1)
                  capacity weight (work z)
                  (taggedAdmittedBatchAt start horizon target z.1 (arrival z))
                  (arrival z - currentTime z)).batchApplied ≠ true := by
                simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch] using
                  hbatchApplied
            simp only [List.map_cons]
            rw [finiteGPSRunBatchTrace_cons_of_not_batchApplied capacity weight
              (taggedAdmittedBatchAt start horizon target z.1) (currentTime z) (work z)
              (arrival z) (pivots.map fun later =>
                taggedAdmittedSourceArrival target z.1 later) hbatchNotApplied']
            change (if (gap z).batchApplied = true then _ else _) = _
            rw [if_neg hbatchApplied]
            simpa [gap, batchWork, arrival, nextBatchDelay, hfuel, hbatch]

/-- A complete fixed source-prefix branch fixes the source comparison
pattern, every actual-fuel GPS gap shape, and the finite FCFS comparisons for
the concatenated script.  The three components remain separate so that the
cover is semantic rather than dependent on theorem or helper names. -/
def taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)) :
    Set (TaggedAdmittedSourceGoodCarrier target) :=
  taggedAdmittedSourceArrivalPatternFiber start horizon target pattern ∩
    ({z | taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
      capacity weight work currentTime pivots gapAtoms z} ∩
      {z | finiteGPSFCFSFixedScriptBranchMatches target preQueue
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight work currentTime pivots gapAtoms) z})

/-- Every complete fixed source-prefix branch is Borel.  The proof composes
the source-pattern fiber, the actual executable GPS comparisons, and the
fixed FCFS prefix comparisons, each of which is a finite coordinate check. -/
theorem measurableSet_taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptBranchFiber
    (start horizon : ℝ) (target : Category)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)) :
    MeasurableSet
      (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptBranchFiber
        start horizon target pattern capacity weight work currentTime preQueue pivots
          gapAtoms) := by
  unfold taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptBranchFiber
  refine (measurableSet_taggedAdmittedSourceArrivalPatternFiber
    start horizon target pattern).inter ?_
  refine (measurableSet_taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches
    target pattern capacity weight work currentTime hwork hcurrentTime pivots
      gapAtoms).inter ?_
  exact measurableSet_finiteGPSFCFSFixedScriptBranchMatches target preQueue
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
      capacity weight work currentTime pivots gapAtoms)
    hpreQueue
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_coordinatesMeasurable
      target pattern capacity weight work currentTime hwork hcurrentTime pivots
        gapAtoms)

/-- The fixed-script replay response for a complete source prefix is Borel.
Literal source traces are related to it only on the semantic branch fiber
below, not by asserting measurability of a variable source-labelled list. -/
theorem measurable_taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptReplayResponse
    (target : Category) (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (hwork : ∀ k, Measurable (fun z => work z k))
    (hcurrentTime : Measurable currentTime)
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (hpreQueue : FiniteGPSFCFSFixedKeyQueue.CoordinatesMeasurable preQueue)
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom)) :
    Measurable (finiteGPSFCFSPaddedReplayResponse
      (taggedAdmittedTargetCompletionKey target) target
      (finiteGPSFCFSFixedScriptReplaySlots
        (taggedAdmittedTargetCompletionKey target) target preQueue
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight work currentTime pivots gapAtoms))) := by
  exact measurable_finiteGPSFCFSFixedScriptReplayResponse
    (taggedAdmittedTargetCompletionKey target) target preQueue
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
      capacity weight work currentTime pivots gapAtoms)
    hpreQueue
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_coordinatesMeasurable
      target pattern capacity weight work currentTime hwork hcurrentTime pivots
        gapAtoms)

/-- On a complete semantic source-prefix branch, the Borel fixed replay is
the response from the literal tagged trace.  The initial ledger and queue are
explicit to retain the FCFS transport obligation at later source/fence joins. -/
theorem taggedAdmittedFiniteGPSBatchTraceFirstKeyCompletionResponse_eq_preTerminalFixedScriptReplayResponse_of_branchFiber
    (start horizon : ℝ) (target : Category)
    (z : TaggedAdmittedSourceGoodCarrier target)
    (pattern : TaggedAdmittedSourceArrivalPattern Category)
    (capacity : ℝ) (weight : Category -> ℝ)
    (work : TaggedAdmittedSourceGoodCarrier target -> Category -> ℝ)
    (currentTime : TaggedAdmittedSourceGoodCarrier target -> ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (preQueue : List (FiniteGPSFCFSFixedKeyJobCoordinate
      (TaggedAdmittedSourceGoodCarrier target)
      (TaggedAdmittedSourceJobId Category)
      (taggedAdmittedTargetCompletionKey target)))
    (pivots : List (TaggedAdmittedSourceJobId Category))
    (gapAtoms : List (List TaggedAdmittedSourceGapBranchAtom))
    (hpivots : ∀ pivot ∈ pivots, pivot ∈ pattern.labels)
    (hinitial : initial.residualJobs target =
      (FiniteGPSFCFSFixedKeyQueue.erase preQueue).map fun coordinate => coordinate z)
    (hfiber : z ∈ taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptBranchFiber
      start horizon target pattern capacity weight work currentTime preQueue pivots
        gapAtoms) :
    finiteGPSFCFSFirstKeyCompletionResponseFromTrace
      (taggedAdmittedTargetCompletionKey target)
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial target
        (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps start horizon target z.1
          capacity weight (currentTime z) (work z)
          (pivots.map fun pivot => taggedAdmittedSourceArrival target z.1 pivot))) =
      finiteGPSFCFSPaddedReplayResponse
        (taggedAdmittedTargetCompletionKey target) target
        (finiteGPSFCFSFixedScriptReplaySlots
          (taggedAdmittedTargetCompletionKey target) target preQueue
          (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
            capacity weight work currentTime pivots gapAtoms)) z := by
  change pattern.Matches start horizon target z.1 ∧
      taggedAdmittedSourceArrivalPatternPreTerminalShapeMatches target pattern
        capacity weight work currentTime pivots gapAtoms z ∧
      finiteGPSFCFSFixedScriptBranchMatches target preQueue
        (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
          capacity weight work currentTime pivots gapAtoms) z at hfiber
  rcases hfiber with ⟨hmatches, hshape, hbranch⟩
  rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_preTerminalFixedScriptSteps_of_shape
    start horizon target z pattern hmatches capacity weight work currentTime pivots
      gapAtoms hpivots hshape]
  exact finiteGPSFCFSFirstKeyCompletionResponseFromTrace_eq_fixedScriptReplayResponse_of_branch
    (taggedAdmittedTargetCompletionKey target) target initial preQueue
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots target pattern
      capacity weight work currentTime pivots gapAtoms) z hinitial
    (taggedAdmittedSourceArrivalPatternPreTerminalFixedScriptSlots_trackedEndpointCompatible
      target pattern capacity weight work currentTime pivots gapAtoms)
    hbranch

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
