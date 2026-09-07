import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateProjection
import Mathlib.Tactic

/-!
# Semantic projection of source-annotated GPS FCFS steps

The concrete GPS segment ledger intentionally does not retain source-job
identifiers.  When a later comparison must retain a selected source epoch even
when that epoch's work mark is zero, the partition has to be performed before
erasing FCFS endpoint-job annotations.  This file provides that purely finite
list adapter.

The caller supplies a semantic predicate on annotated endpoint steps.  The
predicate can inspect literal source labels, source times, or another
application-level witness; this module never selects an endpoint because a
numeric batch is nonzero.  The output groups every nonselected prefix with the
next selected endpoint and keeps a final nonselected suffix as actual
service-only segments.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

/-- A selected annotated endpoint together with the consecutive annotated
steps that precede it. -/
structure FiniteGPSFCFSSemanticProjectionBlock (Class JobId : Type*) where
  zeroPrefix : List (FiniteGPSFCFSSegmentJobStep Class JobId)
  retained : FiniteGPSFCFSSegmentJobStep Class JobId

/-- Erase source-job annotations from one semantic block, retaining its
concrete segment sequence. -/
def FiniteGPSFCFSSemanticProjectionBlock.erase
    (block : FiniteGPSFCFSSemanticProjectionBlock Class JobId) :
    FiniteGPSConstantRateProjectionBlock Class :=
  { zeroPrefix := block.zeroPrefix.map fun step => step.segment
    retained := block.retained.segment }

/-- Concrete annotated steps represented by one semantic projection block. -/
def finiteGPSFCFSSemanticProjectionBlockSteps
    (block : FiniteGPSFCFSSemanticProjectionBlock Class JobId) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) :=
  block.zeroPrefix ++ [block.retained]

/-- Partition annotated steps from right to left.  A nonselected step is
prepended to the next selected endpoint if one exists, and otherwise becomes
part of the final service-only suffix. -/
def finiteGPSFCFSSemanticProjectionPartition
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected] :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) →
      List (FiniteGPSFCFSSemanticProjectionBlock Class JobId) ×
        List (FiniteGPSFCFSSegmentJobStep Class JobId)
  | [] => ([], [])
  | step :: steps =>
      let tail := finiteGPSFCFSSemanticProjectionPartition selected steps
      match tail.1 with
      | [] =>
          if selected step then
            ([{ zeroPrefix := [], retained := step }], tail.2)
          else
            ([], step :: tail.2)
      | first :: rest =>
          if selected step then
            ({ zeroPrefix := [], retained := step } :: first :: rest, tail.2)
          else
            ({ zeroPrefix := step :: first.zeroPrefix, retained := first.retained } :: rest,
              tail.2)

/-- Erase the partitioned annotations to the generic concrete semantic
projection representation. -/
def finiteGPSFCFSSemanticProjectionSegments
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    List (FiniteGPSExecutionSegment Class) :=
  let partition := finiteGPSFCFSSemanticProjectionPartition selected steps
  finiteGPSConstantRateProjectionSegments (partition.1.map
    FiniteGPSFCFSSemanticProjectionBlock.erase) (partition.2.map fun step => step.segment)

/-- The semantic partition is an exact rebracketing of the annotated step
list after source annotations are erased. -/
theorem finiteGPSFCFSSemanticProjectionSegments_eq_erase
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSSemanticProjectionSegments selected steps =
      steps.map fun step => step.segment := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSemanticProjectionSegments,
        finiteGPSFCFSSemanticProjectionPartition,
        finiteGPSConstantRateProjectionSegments]
  | cons step steps ih =>
      unfold finiteGPSFCFSSemanticProjectionSegments
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail : finiteGPSConstantRateProjectionSegments
          (blocks.map FiniteGPSFCFSSemanticProjectionBlock.erase)
          (terminal.map fun laterStep => laterStep.segment) =
          steps.map fun laterStep => laterStep.segment := by
        simpa [finiteGPSFCFSSemanticProjectionSegments, hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · simp [hselected, FiniteGPSFCFSSemanticProjectionBlock.erase,
              finiteGPSConstantRateProjectionSegments,
              finiteGPSConstantRateProjectionBlockSegments]
            simpa [finiteGPSConstantRateProjectionSegments] using htail
          · simp [hselected, finiteGPSConstantRateProjectionSegments]
            simpa [finiteGPSConstantRateProjectionSegments] using htail
      | cons first rest =>
          by_cases hselected : selected step
          · simp [hselected, FiniteGPSFCFSSemanticProjectionBlock.erase,
              finiteGPSConstantRateProjectionSegments,
              finiteGPSConstantRateProjectionBlockSegments]
            simpa [finiteGPSConstantRateProjectionSegments,
              finiteGPSConstantRateProjectionBlockSegments,
              FiniteGPSFCFSSemanticProjectionBlock.erase] using htail
          · simp [hselected, FiniteGPSFCFSSemanticProjectionBlock.erase,
              finiteGPSConstantRateProjectionSegments,
              finiteGPSConstantRateProjectionBlockSegments,
              List.append_assoc]
            simpa [finiteGPSConstantRateProjectionSegments,
              finiteGPSConstantRateProjectionBlockSegments,
              FiniteGPSFCFSSemanticProjectionBlock.erase, List.append_assoc] using htail

/-- Every retained annotated endpoint produced by the partition satisfies the
caller-supplied semantic selection predicate. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_selected
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ block ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).1,
      selected block.retained := by
  induction steps with
  | nil => simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail_selected : ∀ block ∈ blocks, selected block.retained := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · simp [hselected]
          · simp [hselected]
      | cons first rest =>
          by_cases hselected : selected step
          · simp only [if_pos hselected, List.mem_cons]
            intro block hblock
            rcases hblock with hhead | htail
            · subst block
              exact hselected
            · exact htail_selected block (List.mem_cons.mpr htail)
          · simp only [if_neg hselected, List.mem_cons]
            intro block hblock
            rcases hblock with hhead | htail
            · subst block
              exact htail_selected first (by simp)
            · exact htail_selected block (by simp [htail])

/-- The partition preserves the original chronological order of selected
annotated endpoints exactly.  This is a purely list-theoretic fact: callers
may choose the predicate from literal source labels, physical epochs, or any
other semantic evidence without giving the generic adapter a scheduler-name
convention. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_eq_filter
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    (finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
      (fun block => block.retained) = steps.filter selected := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail : blocks.map (fun block => block.retained) = steps.filter selected := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · simpa [hselected] using congrArg (List.cons step) htail
          · simpa [hselected] using htail
      | cons first rest =>
          by_cases hselected : selected step
          · simpa [hselected] using congrArg (List.cons step) htail
          · simpa [hselected] using htail

/-- Retained endpoints form an order-preserving sublist of the original
annotated trace.  This is a generic list fact: the selection predicate may
refer to source labels, physical times, or any other semantic witness. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_sublist_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    List.Sublist
      ((finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
        (fun block => block.retained)) steps := by
  rw [finiteGPSFCFSSemanticProjectionPartition_retained_eq_filter]
  exact List.filter_sublist

/-- Membership in the retained endpoints has both required semantic parts:
the step occurred in the original trace and satisfies the supplied selector.
No numerical endpoint-batch test is involved. -/
theorem mem_finiteGPSFCFSSemanticProjectionPartition_retained_iff
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (step : FiniteGPSFCFSSegmentJobStep Class JobId) :
    step ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
      (fun block => block.retained) ↔ step ∈ steps ∧ selected step := by
  rw [finiteGPSFCFSSemanticProjectionPartition_retained_eq_filter]
  simp

/-- A duplicate-free annotated trace remains duplicate-free after semantic
selection.  This makes retained source-label enumeration unique whenever the
source executor's trace is unique. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_nodup_of_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hnodup : steps.Nodup) :
    ((finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
      (fun block => block.retained)).Nodup := by
  exact List.Nodup.sublist
    (finiteGPSFCFSSemanticProjectionPartition_retained_sublist_original selected steps)
    hnodup

/-- Every pairwise ordering invariant on the original annotated trace is
inherited by retained endpoints in the same chronological order. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_pairwise_of_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (relation : FiniteGPSFCFSSegmentJobStep Class JobId →
      FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    (hpairwise : steps.Pairwise relation) :
    ((finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
      (fun block => block.retained)).Pairwise relation := by
  exact List.Pairwise.sublist
    (finiteGPSFCFSSemanticProjectionPartition_retained_sublist_original selected steps)
    hpairwise

/-- Every retained annotated endpoint is literally a member of the original
trace.  Together with `retained_eq_filter`, this lets a source adapter carry
its own label and physical-time provenance through the semantic partition. -/
theorem finiteGPSFCFSSemanticProjectionPartition_retained_mem_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ block ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).1,
      block.retained ∈ steps := by
  intro block hblock
  have hretained : block.retained ∈
      (finiteGPSFCFSSemanticProjectionPartition selected steps).1.map
        (fun laterBlock => laterBlock.retained) :=
    List.mem_map.mpr ⟨block, hblock, rfl⟩
  rw [finiteGPSFCFSSemanticProjectionPartition_retained_eq_filter] at hretained
  exact (List.mem_filter.mp hretained).1

/-- Every annotated step placed in a projected zero-prefix is literally a
member of the caller's original trace.  This gives source adapters a direct
provenance route for discarded service intervals, without reconstructing the
partition from erased scheduler data. -/
theorem finiteGPSFCFSSemanticProjectionPartition_zeroPrefix_mem_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ block ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).1,
      ∀ step ∈ block.zeroPrefix, step ∈ steps := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail : ∀ block ∈ blocks, ∀ laterStep ∈ block.zeroPrefix,
          laterStep ∈ steps := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step <;> simp [hselected]
      | cons first rest =>
          by_cases hselected : selected step
          · simp only [if_pos hselected, List.mem_cons]
            intro block hblock laterStep hlaterStep
            rcases hblock with hhead | htail_block
            · subst block
              simp at hlaterStep
            · exact Or.inr
                (htail block (List.mem_cons.mpr htail_block) laterStep hlaterStep)
          · simp only [if_neg hselected, List.mem_cons]
            intro block hblock laterStep hlaterStep
            rcases hblock with hhead | htail_block
            · subst block
              rcases List.mem_cons.mp hlaterStep with hstep | hprefix
              · subst laterStep
                exact Or.inl rfl
              · exact Or.inr
                  (htail first (by simp) laterStep hprefix)
            · exact Or.inr
                (htail block (by simp [htail_block]) laterStep hlaterStep)

/-- Every annotated step left in the final service-only suffix is literally
drawn from the caller's original trace.  In particular, a source adapter may
prove its endpoint batch is zero from semantic provenance while retaining all
of its actual elapsed service. -/
theorem finiteGPSFCFSSemanticProjectionPartition_terminal_mem_original
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ step ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).2,
      step ∈ steps := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail : ∀ laterStep ∈ terminal, laterStep ∈ steps := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · intro laterStep hlaterStep
            exact List.mem_cons.mpr (Or.inr
              (htail laterStep (by simpa [hselected] using hlaterStep)))
          · intro laterStep hlaterStep
            rcases List.mem_cons.mp (by simpa [hselected] using hlaterStep) with hhead | htail_step
            · subst laterStep
              exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr (Or.inr (htail laterStep htail_step))
      | cons first rest =>
          by_cases hselected : selected step
          · intro laterStep hlaterStep
            exact List.mem_cons.mpr (Or.inr
              (htail laterStep (by simpa [hselected] using hlaterStep)))
          · intro laterStep hlaterStep
            exact List.mem_cons.mpr (Or.inr
              (htail laterStep (by simpa [hselected] using hlaterStep)))

/-- Every step grouped before a retained endpoint is nonselected according to
the supplied semantic predicate. -/
theorem finiteGPSFCFSSemanticProjectionPartition_zeroPrefix_not_selected
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ block ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).1,
      ∀ step ∈ block.zeroPrefix, ¬ selected step := by
  induction steps with
  | nil => simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail_prefix : ∀ block ∈ blocks, ∀ laterStep ∈ block.zeroPrefix,
          ¬ selected laterStep := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · simp [hselected]
          · simp [hselected]
      | cons first rest =>
          by_cases hselected : selected step
          · simp only [if_pos hselected, List.mem_cons]
            intro block hblock laterStep hlaterStep
            rcases hblock with hhead | htail
            · subst block
              simp at hlaterStep
            · exact htail_prefix block (List.mem_cons.mpr htail) laterStep hlaterStep
          · simp only [if_neg hselected, List.mem_cons]
            intro block hblock laterStep hlaterStep
            rcases hblock with hhead | htail
            · subst block
              rcases List.mem_cons.mp hlaterStep with hstep | hprefix
              · subst laterStep
                exact hselected
              · exact htail_prefix first (by simp) laterStep hprefix
            · exact htail_prefix block (by simp [htail]) laterStep hlaterStep

/-- Every step retained in the final service-only suffix is nonselected. -/
theorem finiteGPSFCFSSemanticProjectionPartition_terminal_not_selected
    (selected : FiniteGPSFCFSSegmentJobStep Class JobId → Prop)
    [DecidablePred selected]
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    ∀ step ∈ (finiteGPSFCFSSemanticProjectionPartition selected steps).2,
      ¬ selected step := by
  induction steps with
  | nil => simp [finiteGPSFCFSSemanticProjectionPartition]
  | cons step steps ih =>
      simp only [finiteGPSFCFSSemanticProjectionPartition]
      generalize hpartition : finiteGPSFCFSSemanticProjectionPartition selected steps = partition
      rcases partition with ⟨blocks, terminal⟩
      have htail_terminal : ∀ laterStep ∈ terminal, ¬ selected laterStep := by
        simpa [hpartition] using ih
      cases blocks with
      | nil =>
          by_cases hselected : selected step
          · simpa [hselected] using htail_terminal
          · intro laterStep hlaterStep
            simp only [if_neg hselected, List.mem_cons] at hlaterStep
            rcases hlaterStep with hhead | htail
            · subst laterStep
              exact hselected
            · exact htail_terminal laterStep htail
      | cons first rest =>
          by_cases hselected : selected step <;>
            simpa [hselected] using htail_terminal

end

end AppliedModelingLib.Probability.Queueing
