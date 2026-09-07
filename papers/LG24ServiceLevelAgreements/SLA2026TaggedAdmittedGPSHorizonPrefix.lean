import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonPersistence
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalIndex
import Mathlib.Tactic

/-!
# Source-prefix factorization across reset-start GPS horizons

The finite replay at a shorter horizon ends with a computational fence and is
therefore not itself a prefix of a longer replay.  This module factors only
the literal preterminal source execution.  The two computational fences are
then retained as distinct tails when applying the horizon-persistence layer.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open Filter
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The source-labelled gap annotation is extensional in the actual batch
vector and source-job endpoint list at its scheduled epoch. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_sourceData_eq
    (startLeft horizonLeft startRight horizonRight : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : Real)
    (fuel : Nat) (capacity : Real) (weight work : Category -> Real)
    (currentTime nextBatchDelay : Real)
    (hbatch : taggedAdmittedBatchAt startLeft horizonLeft target z eventTime =
      taggedAdmittedBatchAt startRight horizonRight target z eventTime)
    (hjobs : taggedAdmittedFCFSJobsAt startLeft horizonLeft target z eventTime =
      taggedAdmittedFCFSJobsAt startRight horizonRight target z eventTime) :
    taggedAdmittedFiniteGPSGapSegmentJobSteps
        startLeft horizonLeft target z eventTime fuel capacity weight work
        currentTime nextBatchDelay =
      taggedAdmittedFiniteGPSGapSegmentJobSteps
        startRight horizonRight target z eventTime fuel capacity weight work
        currentTime nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [taggedAdmittedFiniteGPSGapSegmentJobSteps]
      simp only [hbatch, taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, hjobs]
      split
      · rfl
      · congr 1
        exact ih
          (finiteGPSNextEventState capacity weight work
            (taggedAdmittedBatchAt startRight horizonRight target z eventTime)
            nextBatchDelay)
          (currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (nextBatchDelay - finiteGPSNextStepDuration capacity weight work nextBatchDelay)

/-- An annotated finite source-batch replay is extensional in the exact
batch vectors and exact source-job endpoint lists on the scheduled trace.
This avoids using equality of aggregate GPS state as a proxy for labelled
FCFS history. -/
private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceData_eq
    (startLeft horizonLeft startRight horizonRight : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : Real)
    (weight currentWork : Category -> Real) (currentTime : Real)
    (times : List Real)
    (hbatch : forall eventTime, eventTime ∈ times ->
      taggedAdmittedBatchAt startLeft horizonLeft target z eventTime =
        taggedAdmittedBatchAt startRight horizonRight target z eventTime)
    (hjobs : forall eventTime, eventTime ∈ times ->
      taggedAdmittedFCFSJobsAt startLeft horizonLeft target z eventTime =
        taggedAdmittedFCFSJobsAt startRight horizonRight target z eventTime) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        startLeft horizonLeft target z capacity weight currentTime currentWork times =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        startRight horizonRight target z capacity weight currentTime currentWork times := by
  induction times generalizing currentTime currentWork with
  | nil =>
      rfl
  | cons eventTime times ih =>
      have hbatch_head := hbatch eventTime (by simp)
      have hjobs_head := hjobs eventTime (by simp)
      have hbatch_tail : forall laterTime, laterTime ∈ times ->
          taggedAdmittedBatchAt startLeft horizonLeft target z laterTime =
            taggedAdmittedBatchAt startRight horizonRight target z laterTime := by
        intro laterTime hlaterTime
        exact hbatch laterTime (by simp [hlaterTime])
      have hjobs_tail : forall laterTime, laterTime ∈ times ->
          taggedAdmittedFCFSJobsAt startLeft horizonLeft target z laterTime =
            taggedAdmittedFCFSJobsAt startRight horizonRight target z laterTime := by
        intro laterTime hlaterTime
        exact hjobs laterTime (by simp [hlaterTime])
      have hgap_steps := taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_sourceData_eq
        startLeft horizonLeft startRight horizonRight target z eventTime
        ((finiteGPSActiveClasses currentWork).card + 1) capacity weight currentWork
        currentTime (eventTime - currentTime) hbatch_head hjobs_head
      have hgap : finiteGPSRunGap ((finiteGPSActiveClasses currentWork).card + 1)
          capacity weight currentWork
          (taggedAdmittedBatchAt startLeft horizonLeft target z eventTime)
          (eventTime - currentTime) =
        finiteGPSRunGap ((finiteGPSActiveClasses currentWork).card + 1)
          capacity weight currentWork
          (taggedAdmittedBatchAt startRight horizonRight target z eventTime)
          (eventTime - currentTime) := by
        rw [hbatch_head]
      unfold taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      dsimp only
      rw [hgap]
      split
      · rw [hgap_steps]
        congr 1
        exact ih (currentTime := eventTime)
          (currentWork := (finiteGPSRunGap ((finiteGPSActiveClasses currentWork).card + 1)
            capacity weight currentWork
            (taggedAdmittedBatchAt startRight horizonRight target z eventTime)
            (eventTime - currentTime)).workload)
          hbatch_tail hjobs_tail
      · exact hgap_steps

/-- Extending a literal reset-start horizon preserves the complete
source-labelled preterminal replay at the shorter horizon.  The right factor
starts from the exact aggregate state produced by that shorter replay.  This
is a source-time statement only: it does not insert either horizon's
computational zero-work fence. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_resetHorizon_factor
    (resetTime smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (hreset_small : resetTime <= smallHorizon)
    (hsmall_large : smallHorizon <= largeHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime largeHorizon target z htarget_good capacity weight (fun _ => 0) =
      taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          resetTime largeHorizon target z capacity weight
          (taggedAdmittedFiniteGPSPreTerminalRun
            resetTime smallHorizon target z htarget_good capacity weight
            (fun _ => 0)).currentTime
          (taggedAdmittedFiniteGPSPreTerminalRun
            resetTime smallHorizon target z htarget_good capacity weight
            (fun _ => 0)).workload
          (taggedAdmittedExternalBatchTrace
            smallHorizon largeHorizon target z htarget_good).times := by
  have hrestart := taggedAdmittedFiniteGPSPreTerminalFCFSSteps_eq_fullSourceRestartAtReset
    resetTime smallHorizon largeHorizon target z htarget_good capacity weight
    (fun _ => 0) hreset_small hsmall_large hcapacity hweight_pos htotal_weight_le_one
    (by intro k; norm_num) hsource_work_nonneg
  have hprefix_steps :
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          resetTime largeHorizon target z capacity weight resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace
            resetTime smallHorizon target z htarget_good).times =
        taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) := by
    unfold taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    apply taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceData_eq
      resetTime largeHorizon resetTime smallHorizon target z capacity weight
      (fun _ => 0) resetTime
      (taggedAdmittedExternalBatchTrace
        resetTime smallHorizon target z htarget_good).times
    · intro eventTime heventTime
      apply taggedAdmittedBatchAt_eq_prefix_of_lt_reset
        resetTime smallHorizon largeHorizon target z htarget_good hsmall_large eventTime
      apply taggedAdmittedBatchTimes_prefix_lt_reset
        resetTime smallHorizon target z htarget_good eventTime
      exact (Finset.mem_sort (fun left right : Real => left <= right)).mp
        (by simpa [taggedAdmittedExternalBatchTrace,
          taggedAdmittedBatchTimeTrace] using heventTime)
    · intro eventTime heventTime
      apply taggedAdmittedFCFSJobsAt_eq_prefix_of_lt_reset
        resetTime smallHorizon largeHorizon target z htarget_good hsmall_large eventTime
      apply taggedAdmittedBatchTimes_prefix_lt_reset
        resetTime smallHorizon target z htarget_good eventTime
      exact (Finset.mem_sort (fun left right : Real => left <= right)).mp
        (by simpa [taggedAdmittedExternalBatchTrace,
          taggedAdmittedBatchTimeTrace] using heventTime)
  have hprefix_run :
      finiteGPSRunBatchTrace capacity weight
          (taggedAdmittedBatchAt resetTime largeHorizon target z)
          resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace
            resetTime smallHorizon target z htarget_good).times =
        taggedAdmittedFiniteGPSPreTerminalRun
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) := by
    simpa [taggedAdmittedExternalBatchTrace] using
      (taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
        resetTime smallHorizon largeHorizon target z htarget_good capacity weight
        (fun _ => 0) hsmall_large)
  calc
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime largeHorizon target z htarget_good capacity weight (fun _ => 0) =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          resetTime largeHorizon target z capacity weight resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace
            resetTime smallHorizon target z htarget_good).times ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          resetTime largeHorizon target z capacity weight
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime largeHorizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedExternalBatchTrace
              resetTime smallHorizon target z htarget_good).times).currentTime
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime largeHorizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedExternalBatchTrace
              resetTime smallHorizon target z htarget_good).times).workload
          (taggedAdmittedExternalBatchTrace
            smallHorizon largeHorizon target z htarget_good).times := hrestart
    _ = taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          resetTime largeHorizon target z capacity weight
          (taggedAdmittedFiniteGPSPreTerminalRun
            resetTime smallHorizon target z htarget_good capacity weight
            (fun _ => 0)).currentTime
          (taggedAdmittedFiniteGPSPreTerminalRun
            resetTime smallHorizon target z htarget_good capacity weight
            (fun _ => 0)).workload
          (taggedAdmittedExternalBatchTrace
            smallHorizon largeHorizon target z htarget_good).times := by
      rw [hprefix_steps, hprefix_run]

/-- Two reset-start horizon traces have an exact common prefix consisting
only of literal source work.  The short and long computational fences remain
inside their respective tails, so this result is suitable for the
source-labelled horizon-persistence theorem. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_resetHorizon_commonPrefix
    (resetTime smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (hreset_small : resetTime <= smallHorizon)
    (hsmall_large : smallHorizon <= largeHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    exists sourcePrefix smallTail largeTail,
      sourcePrefix = taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) /\
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime smallHorizon target z htarget_good capacity weight =
          sourcePrefix ++ smallTail /\
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime largeHorizon target z htarget_good capacity weight =
          sourcePrefix ++ largeTail := by
  let continuation := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    resetTime largeHorizon target z capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0)).currentTime
    (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0)).workload
    (taggedAdmittedExternalBatchTrace
      smallHorizon largeHorizon target z htarget_good).times
  refine ⟨taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0),
    taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      resetTime smallHorizon target z htarget_good capacity weight,
    continuation ++ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      resetTime largeHorizon target z htarget_good capacity weight,
    rfl, rfl, ?_⟩
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  change
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime largeHorizon target z htarget_good capacity weight (fun _ => 0) ++
      taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        resetTime largeHorizon target z htarget_good capacity weight =
      taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0) ++
        (continuation ++ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
          resetTime largeHorizon target z htarget_good capacity weight)
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_resetHorizon_factor
    resetTime smallHorizon largeHorizon target z htarget_good capacity weight
    hreset_small hsmall_large hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg]
  simp only [continuation, List.append_assoc]

/-- A source-selected Palm completion remains selected after extending the
literal reset-start source trace.  This is stated before adding either
horizon's computational fence, so it preserves the actual completion
provenance needed by the physical diagonal-reset bridge. -/
theorem taggedAdmittedFiniteGPSPreTerminalSelection_persists_of_resetHorizon
    (resetTime smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hreset_small : resetTime <= smallHorizon)
    (hsmall_large : smallHorizon <= largeHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hpreterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0))) =
        some selected) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime largeHorizon target z htarget_good capacity weight (fun _ => 0))) =
        some selected := by
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_resetHorizon_factor
    resetTime smallHorizon largeHorizon target z htarget_good capacity weight
    hreset_small hsmall_large hcapacity hweight_pos htotal_weight_le_one
    hsource_work_nonneg]
  exact taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
    target
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0))
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      resetTime largeHorizon target z capacity weight
      (taggedAdmittedFiniteGPSPreTerminalRun
        resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0)).currentTime
      (taggedAdmittedFiniteGPSPreTerminalRun
        resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0)).workload
      (taggedAdmittedExternalBatchTrace
        smallHorizon largeHorizon target z htarget_good).times)
    selected hpreterminal_selected

/-- Once the literal source prefix through `smallHorizon` has selected the
Palm completion, every later reset-start replay has the same total selected
response.  The selection hypothesis is deliberately about the preterminal
source trace, rather than merely a source-plus-computational-fence witness. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
    (resetTime smallHorizon largeHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hreset_small : resetTime <= smallHorizon)
    (hsmall_large : smallHorizon <= largeHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hpreterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime smallHorizon target z htarget_good capacity weight (fun _ => 0))) =
        some selected) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime smallHorizon target z htarget_good capacity weight =
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime largeHorizon target z htarget_good capacity weight := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_resetHorizon_commonPrefix
      resetTime smallHorizon largeHorizon target z htarget_good capacity weight
      hreset_small hsmall_large hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg with
      ⟨sourcePrefix, smallTail, largeTail, hsourcePrefix, hsmall_steps, hlarge_steps⟩
  apply taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_commonSourcePrefix
    resetTime smallHorizon largeHorizon target z htarget_good capacity weight
    sourcePrefix smallTail largeTail selected hsmall_steps hlarge_steps
  simpa only [hsourcePrefix] using hpreterminal_selected

/-- A fixed reset-start source completion is stable throughout all sufficiently
large diagonal right horizons.  The conjunction retains the corresponding
left-boundary containment so a caller can separately supply the exact FCFS
reset-crossing refinement without redoing horizon persistence. -/
theorem eventually_taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
    (resetTime completionHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hreset_completion : resetTime <= completionHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hpreterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime completionHorizon target z htarget_good capacity weight (fun _ => 0))) =
        some selected) :
    ∀ᶠ N : Nat in atTop,
      taggedAdmittedGPSDiagonalStart N <= resetTime /\
        taggedAdmittedFiniteGPSHorizonFenceTotalResponse
            resetTime (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good capacity weight =
          taggedAdmittedFiniteGPSHorizonFenceTotalResponse
            resetTime completionHorizon target z htarget_good capacity weight := by
  filter_upwards [eventually_taggedAdmittedGPSDiagonal_contains
    resetTime completionHorizon] with N hwindow
  refine ⟨hwindow.1, ?_⟩
  exact (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
    resetTime completionHorizon (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good capacity weight selected hreset_completion hwindow.2
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    hpreterminal_selected).symm

/-- Witness-facing form of reset-start horizon stabilization.  The added
membership premise states exactly what a finite source/fence witness alone
does not: its tagged completion has already been emitted by the literal
preterminal source trace at the completion horizon. -/
theorem eventually_taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_witness_response_of_preterminalMembership
    (resetTime completionHorizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category -> Real)
    (hreset_zero : resetTime <= 0) (hcompletion_pos : 0 < completionHorizon)
    (hcapacity : 0 < capacity) (hweight_pos : forall k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      resetTime completionHorizon target z htarget_good capacity weight)
    (hcompletion_preterminal : witness.completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime completionHorizon target z htarget_good capacity weight (fun _ => 0))) :
    ∀ᶠ N : Nat in atTop,
      taggedAdmittedGPSDiagonalStart N <= resetTime /\
        taggedAdmittedFiniteGPSHorizonFenceTotalResponse
            resetTime (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good capacity weight = witness.response := by
  rcases taggedAdmittedFiniteGPSFirstTagCompletion?_exists_of_mem
      target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime completionHorizon target z htarget_good capacity weight (fun _ => 0)))
      witness.completion hcompletion_preterminal witness.identifier_eq_tag with
      ⟨selected, hpreterminal_selected⟩
  filter_upwards [
    eventually_taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_of_resetHorizon_preterminalSelection
      resetTime completionHorizon target z htarget_good capacity weight selected
      (hreset_zero.trans hcompletion_pos.le) hcapacity hweight_pos
      htotal_weight_le_one hsource_work_nonneg hpreterminal_selected] with N hstable
  refine ⟨hstable.1, ?_⟩
  calc
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good capacity weight =
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime completionHorizon target z htarget_good capacity weight := hstable.2
    _ = witness.response :=
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_witness_response
        resetTime completionHorizon target z htarget_good capacity weight
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
        hreset_zero hcompletion_pos witness

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
