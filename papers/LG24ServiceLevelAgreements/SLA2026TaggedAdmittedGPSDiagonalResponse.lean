import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSKeyAccounting
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompletionBridge
import Mathlib.Tactic

/-!
# Canonical diagonal finite responses for the tagged admitted GPS trace

This module gives the literal finite GPS execution a deterministic response
value at every diagonal window `[-N, N + 1)`.  It scans the executable target
completion list in its generated order and returns the first completion whose
source identifier is the Palm tag.  The sole fallback is `0` when that finite
trace contains no such completion.

The construction is intentionally conditional on the existing good-carrier
proof needed to build the literal source trace.  It neither chooses a past
reset witness nor makes a measurability claim.  Those are separate stationary
source-model obligations.  In particular, the lemmas below establish only
finite source faithfulness and conversion of a selected completion into the
existing finite response witness.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The Boolean key used throughout this module for the literal Palm source
job. -/
def taggedAdmittedTargetCompletionKey (target : Category) :
    TaggedAdmittedSourceJobId Category → Bool :=
  fun identifier => decide (identifier = (target, 0))

/-- In one literal source batch, the Palm source label occurs once precisely
when that batch is at physical time zero. -/
theorem taggedAdmittedFCFSJobsAt_targetKeyCount
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) (eventTime : ℝ) :
    ((taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target).countP
        (fun job => taggedAdmittedTargetCompletionKey target job.identifier) =
      if eventTime = 0 then 1 else 0 := by
  by_cases hevent : eventTime = 0
  · subst eventTime
    rw [if_pos (show (0 : ℝ) = 0 by rfl)]
    apply AppliedModelingLib.Probability.Queueing.List.countP_eq_one_of_nodup_of_mem_of_keyed_eq
      (fun job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category) =>
        taggedAdmittedTargetCompletionKey target job.identifier)
      ((taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target)
      (taggedAdmittedFCFSJob target z (target, 0))
    · unfold taggedAdmittedFCFSJobsAt
      exact (Finset.sort_nodup
        (taggedAdmittedJobIndicesAt start horizon target z 0 target)
        (fun left right : ℤ => left ≤ right)).map
          (taggedAdmittedFCFSJob_injective target z target)
    · apply (mem_taggedAdmittedFCFSJob_jobsAt_iff
        start horizon target z 0 target 0).mpr
      exact ⟨(mem_taggedAdmittedSourceJobLedger_iff
        start horizon target z target 0).mp
        ((mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
          ⟨hstart, hhorizon⟩), taggedAdmittedSourceArrival_target_zero target z⟩
    · simp [taggedAdmittedTargetCompletionKey]
    · intro job hjob hkey
      unfold taggedAdmittedFCFSJobsAt at hjob
      rcases List.mem_map.mp hjob with ⟨n, _hn, rfl⟩
      have hidentifier : (target, n) = (target, 0) :=
        of_decide_eq_true hkey
      have hn : n = 0 := congrArg Prod.snd hidentifier
      subst n
      rfl
  · simp only [if_neg hevent]
    rw [List.countP_eq_zero]
    intro job hjob hkey
    unfold taggedAdmittedFCFSJobsAt at hjob
    rcases List.mem_map.mp hjob with ⟨n, _hn, hjob_eq⟩
    have hidentifier : (target, n) = (target, 0) := by
      have hidentifier' :
          (taggedAdmittedFCFSJob target z (target, n)).identifier = (target, 0) := by
        exact (congrArg FiniteGPSFCFSJob.identifier hjob_eq).trans
          (of_decide_eq_true hkey)
      simpa using hidentifier'
    have hn : n = 0 := congrArg Prod.snd hidentifier
    subst n
    rw [← hjob_eq] at hjob
    have htag_mem : taggedAdmittedFCFSJob target z (target, 0) ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      simpa [taggedAdmittedFCFSJobsAt] using hjob
    have harrival := (mem_taggedAdmittedFCFSJob_jobsAt_iff
      start horizon target z eventTime target 0).mp htag_mem |>.2
    rw [taggedAdmittedSourceArrival_target_zero] at harrival
    exact hevent harrival.symm

/-- For every annotated finite gap, endpoint key accounting agrees exactly
with the filtered list of its genuine external source endpoints.  Internal
depletion endpoints contribute the explicitly empty computational batch. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointKeyCount_eq_externalEndpointKeyCount
    (key : TaggedAdmittedSourceJobId Category → Bool) (i : Category)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount key i
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay) =
      ((taggedAdmittedFiniteGPSExternalEndpointJobBatches
        (taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay)).map
        fun endpointJobs =>
          (endpointJobs.jobs i).countP fun job => key job.identifier).sum := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps,
        finiteGPSFCFSSegmentStepsEndpointKeyCount,
        taggedAdmittedFiniteGPSExternalEndpointJobBatches]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have htag : step.segment.endpointIsExternalBatch = true := by
          change (finiteGPSBuildExecutionSegment capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch = true
          apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay |>.mpr
          simpa [duration] using hduration
        simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, hduration,
          finiteGPSFCFSSegmentStepsEndpointKeyCount,
          taggedAdmittedFiniteGPSExternalEndpointJobBatches, step, htag]
      · have hnotExternal : step.segment.endpointIsExternalBatch ≠ true := by
          intro htag
          apply hduration
          apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay |>.mp
          simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using htag
        have hnotExternal' :
            (finiteGPSBuildExecutionSegment capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay).endpointIsExternalBatch ≠ true := by
          simpa [step, taggedAdmittedFiniteGPSBuildSegmentJobStep] using hnotExternal
        have hendpoint : step.endpointJobs =
            taggedAdmittedFCFSComputationalEndpointJobs := by
          simp [step, taggedAdmittedFiniteGPSBuildSegmentJobStep,
            taggedAdmittedFiniteGPSEndpointJobsForSegment, hnotExternal']
        have hcount : (step.endpointJobs.jobs i).countP
            (fun job => key job.identifier) = 0 := by
          rw [hendpoint]
          simp [taggedAdmittedFCFSComputationalEndpointJobs]
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration)
        simpa [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, hduration,
          finiteGPSFCFSSegmentStepsEndpointKeyCount,
          taggedAdmittedFiniteGPSExternalEndpointJobBatches, step,
          hnotExternal, hcount] using htail

/-- The same endpoint-count identity for a complete annotated source batch
trace.  It holds even for a stopped bounded trace: only endpoint batches
actually reached by the executable runner are counted. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointKeyCount_eq_externalEndpointKeyCount
    (key : TaggedAdmittedSourceJobId Category → Bool) (i : Category)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) :
    ∀ times : List ℝ,
      finiteGPSFCFSSegmentStepsEndpointKeyCount key i
        (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work times) =
        ((taggedAdmittedFiniteGPSExternalEndpointJobBatches
          (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight currentTime work times)).map
          fun endpointJobs =>
            (endpointJobs.jobs i).countP fun job => key job.identifier).sum := by
  intro times
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSFCFSSegmentStepsEndpointKeyCount,
        taggedAdmittedFiniteGPSExternalEndpointJobBatches]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatch' :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatch']
        rw [finiteGPSFCFSSegmentStepsEndpointKeyCount_append]
        rw [taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointKeyCount_eq_externalEndpointKeyCount
          key i start horizon target z eventTime
          ((finiteGPSActiveClasses work).card + 1) capacity weight work currentTime
          (eventTime - currentTime)]
        have htail := ih
          (currentTime := eventTime)
          (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).workload)
        rw [htail]
        simp [taggedAdmittedFiniteGPSExternalEndpointJobBatches]
      · have hbatch' :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatch']
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointKeyCount_eq_externalEndpointKeyCount
          key i start horizon target z eventTime
          ((finiteGPSActiveClasses work).card + 1) capacity weight work currentTime
          (eventTime - currentTime)

/-- Endpoint key accounting for the named pre-terminal literal source trace. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointKeyCount_eq_externalEndpointKeyCount
    (key : TaggedAdmittedSourceJobId Category → Bool) (i : Category)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount key i
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) =
      ((taggedAdmittedFiniteGPSExternalEndpointJobBatches
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight initialWork)).map
        fun endpointJobs =>
          (endpointJobs.jobs i).countP fun job => key job.identifier).sum := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointKeyCount_eq_externalEndpointKeyCount
      key i start horizon target z capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)

/-- The computational horizon-fence suffix contributes no source identifier
to endpoint key accounting. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointKeyCount_eq_zero
    (key : TaggedAdmittedSourceJobId Category → Bool) (i : Category)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount key i
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight) = 0 := by
  unfold finiteGPSFCFSSegmentStepsEndpointKeyCount
  apply List.sum_eq_zero
  intro count hcount
  rcases List.mem_map.mp hcount with ⟨step, hstep, rfl⟩
  rw [taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
    start horizon target z htarget_good capacity weight step hstep]
  simp [taggedAdmittedFCFSComputationalEndpointJobs]

/-- Full literal source/fence endpoint key accounting is exactly its
pre-terminal source accounting; the appended computational fence has none. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endpointKeyCount_eq_preTerminal
    (key : TaggedAdmittedSourceJobId Category → Bool) (i : Category)
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount key i
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) =
      finiteGPSFCFSSegmentStepsEndpointKeyCount key i
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)) := by
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  rw [finiteGPSFCFSSegmentStepsEndpointKeyCount_append,
    taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointKeyCount_eq_zero]
  omega

/-- In a literal finite horizon containing zero, the whole source/fence FCFS
trace receives exactly one endpoint job with the Palm source identifier. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_targetEndpointKeyCount_eq_one
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount
      (taggedAdmittedTargetCompletionKey target) target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) = 1 := by
  rw [taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endpointKeyCount_eq_preTerminal]
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointKeyCount_eq_externalEndpointKeyCount]
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
    start horizon target z htarget_good capacity weight (fun _ => 0)
    hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
    hsource_work_nonneg]
  rw [List.map_map, Function.comp_def]
  simp_rw [taggedAdmittedFCFSJobsAt_targetKeyCount
    start horizon target z htarget_good hstart hhorizon]
  have hcount_indicator :
      ((taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.map
        fun eventTime => if eventTime = 0 then 1 else 0).sum =
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.countP
          (fun eventTime => decide (eventTime = 0)) := by
    simpa only [decide_eq_true_eq] using
      (AppliedModelingLib.Probability.Queueing.List.sum_map_indicator_eq_countP
        (fun eventTime : ℝ => decide (eventTime = 0))
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)
  rw [hcount_indicator]
  apply AppliedModelingLib.Probability.Queueing.List.countP_eq_one_of_nodup_of_mem_of_keyed_eq
    (fun eventTime : ℝ => decide (eventTime = 0))
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times 0
  · exact (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).nodup
  · change 0 ∈ taggedAdmittedBatchTimeTrace start horizon target z
    apply (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr
    apply (mem_taggedAdmittedBatchTimes_iff start horizon target z 0).mpr
    refine ⟨(target, 0), ?_, taggedAdmittedSourceArrival_target_zero target z⟩
    exact (mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
      ⟨hstart, hhorizon⟩
  · simp
  · intro eventTime heventTime hkey
    exact of_decide_eq_true hkey

/-- The literal source/fence FCFS completion trace cannot contain two
different records for the Palm source label.  This is derived from exact
endpoint key accounting, rather than from the order chosen by the response
selector. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_eq_of_identifier_eq_tag
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (left right : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hleft : left ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    (hleft_identifier : left.identifier = (target, 0))
    (hright : right ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    (hright_identifier : right.identifier = (target, 0)) :
    left = right := by
  apply finiteGPSFCFSRunSegmentStepsClassCompletion_eq_of_mem_key_of_endpointKeyCount_le_one
    (taggedAdmittedTargetCompletionKey target)
    (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
  · simp [taggedAdmittedEmptyFCFSLedger]
  · rw [taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_targetEndpointKeyCount_eq_one
      start horizon target z htarget_good capacity weight hcapacity hweight_pos
      htotal_weight_le_one hsource_work_nonneg hstart hhorizon]
  · exact hleft
  · simp [taggedAdmittedTargetCompletionKey, hleft_identifier]
  · exact hright
  · simp [taggedAdmittedTargetCompletionKey, hright_identifier]

/-- Scan a literal target-class completion list in execution order for the
Palm tag.  This is a deterministic list operation, not a choice of a finite
completion witness. -/
def taggedAdmittedFiniteGPSFirstTagCompletion?
    (target : Category) :
    List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)) →
      Option (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
  | [] => none
  | completion :: completions =>
      if completion.identifier = (target, 0) then some completion
      else taggedAdmittedFiniteGPSFirstTagCompletion? target completions

/-- A completion returned by the deterministic scan is an actual member of
the scanned trace and has the literal Palm identifier. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_eq_some
    (target : Category) :
    ∀ (completions : List (FiniteGPSFCFSCompletion
      (TaggedAdmittedSourceJobId Category)))
      (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)),
      taggedAdmittedFiniteGPSFirstTagCompletion? target completions = some selected →
        selected ∈ completions ∧ selected.identifier = (target, 0) := by
  intro completions
  induction completions with
  | nil =>
      intro selected hselected
      simp [taggedAdmittedFiniteGPSFirstTagCompletion?] at hselected
  | cons completion completions ih =>
      intro selected hselected
      by_cases htag : completion.identifier = (target, 0)
      · simp [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] at hselected
        subst selected
        exact ⟨by simp, htag⟩
      · have htail : taggedAdmittedFiniteGPSFirstTagCompletion? target completions =
            some selected := by
          simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using hselected
        rcases ih selected htail with ⟨hmem, hidentifier⟩
        exact ⟨by simp [hmem], hidentifier⟩

/-- If an actual finite completion list contains the Palm tag, its
deterministic scan returns some tagged completion.  The returned record need
not be asserted equal to an arbitrary witness: the trace may contain more
than one record with the same identifier until that uniqueness property is
proved separately. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_exists_of_mem
    (target : Category)
    (completions : List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)))
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ completions)
    (hidentifier : completion.identifier = (target, 0)) :
    ∃ selected, taggedAdmittedFiniteGPSFirstTagCompletion? target completions = some selected := by
  induction completions generalizing completion with
  | nil =>
      simp at hcompletion
  | cons head tail ih =>
      by_cases hhead : head.identifier = (target, 0)
      · exact ⟨head, by
          simp [taggedAdmittedFiniteGPSFirstTagCompletion?, hhead]⟩
      · rcases List.mem_cons.mp hcompletion with hcompletion | hcompletion
        · subst completion
          exact False.elim (hhead hidentifier)
        · rcases ih completion hcompletion hidentifier with ⟨selected, hselected⟩
          exact ⟨selected, by
            simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, hhead] using hselected⟩

/-- The deterministic tagged-completion selector for the complete literal
finite GPS trace with its source-empty computational horizon fence. -/
def taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    Option (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)) :=
  taggedAdmittedFiniteGPSFirstTagCompletion? target
    (taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)

/-- A total finite-trace response value.  `0` is used only when the literal
finite completion trace does not yet contain the tagged completion. -/
def taggedAdmittedFiniteGPSHorizonFenceTotalResponse
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) : ℝ :=
  match taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight with
  | some completion => completion.completionTime
  | none => 0

/-- A completion selected from the literal finite trace has the source tag,
is actually emitted by that trace, and retains its source arrival epoch. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_source_faithful
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight = some selected) :
    selected ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight ∧
      selected.identifier = (target, 0) ∧ selected.arrivalTime = 0 := by
  have hscan := taggedAdmittedFiniteGPSFirstTagCompletion?_eq_some
    target
    (taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    selected hselected
  refine ⟨hscan.1, hscan.2, ?_⟩
  exact taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
    start horizon target z htarget_good capacity weight selected hscan.1 hscan.2

/-- On the selected-completion branch, the total response is exactly that
completion's literal completion time. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight = some selected) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
      start horizon target z htarget_good capacity weight = selected.completionTime := by
  simp [taggedAdmittedFiniteGPSHorizonFenceTotalResponse, hselected]

/-- A selected deterministic completion induces the pre-existing finite
response witness, with equal response value. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_toWitness
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight = some selected) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion = selected ∧
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        start horizon target z htarget_good capacity weight = witness.response := by
  rcases taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_source_faithful
      start horizon target z htarget_good capacity weight selected hselected with
      ⟨hmem, hidentifier, harrival⟩
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight :=
    { completion := selected
      completion_mem := hmem
      identifier_eq_tag := hidentifier
      arrival_eq_zero := harrival }
  refine ⟨witness, rfl, ?_⟩
  rw [taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
    start horizon target z htarget_good capacity weight selected hselected]
  exact (TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    start horizon target z htarget_good capacity weight witness).symm

/-- Any pre-existing finite tagged response witness guarantees that the
deterministic selector has a completion branch. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_exists_of_witness
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight) :
    ∃ selected, taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight = some selected := by
  exact taggedAdmittedFiniteGPSFirstTagCompletion?_exists_of_mem
    target
    (taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    witness.completion witness.completion_mem witness.identifier_eq_tag

/-- In a literal finite horizon containing the Palm epoch, the deterministic
completion scan selects the same record as any existing finite tagged
response witness.  This is the bridge from the canonical selector to a
completion obtained by a separate finite deadline proof. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_eq_some_witness_completion
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight) :
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      start horizon target z htarget_good capacity weight = some witness.completion := by
  rcases taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_exists_of_witness
      start horizon target z htarget_good capacity weight witness with
      ⟨selected, hselected⟩
  have hselected_faithful :=
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_source_faithful
      start horizon target z htarget_good capacity weight selected hselected
  have hcompletion_eq :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_eq_of_identifier_eq_tag
      start horizon target z htarget_good capacity weight hcapacity hweight_pos
      htotal_weight_le_one hsource_work_nonneg hstart hhorizon
      selected witness.completion hselected_faithful.1 hselected_faithful.2.1
      witness.completion_mem witness.identifier_eq_tag
  rw [hcompletion_eq] at hselected
  exact hselected

/-- The total canonical finite response equals the response represented by
any finite tagged witness once the literal source trace contains the Palm
epoch.  Its fallback branch is therefore impossible under a finite completion
witness, and no `Classical.choose` is involved. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_witness_response
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight) :
    taggedAdmittedFiniteGPSHorizonFenceTotalResponse
      start horizon target z htarget_good capacity weight = witness.response := by
  have hselected :=
    taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_eq_some_witness_completion
      start horizon target z htarget_good capacity weight hcapacity hweight_pos
      htotal_weight_le_one hsource_work_nonneg hstart hhorizon witness
  rw [taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
    start horizon target z htarget_good capacity weight witness.completion hselected]
  exact (TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    start horizon target z htarget_good capacity weight witness).symm

/-- Left endpoint of the canonical `N`th diagonal replay window. -/
def taggedAdmittedGPSDiagonalStart (N : ℕ) : ℝ := -(N : ℝ)

/-- Right endpoint of the canonical `N`th diagonal replay window. -/
def taggedAdmittedGPSDiagonalHorizon (N : ℕ) : ℝ := (N : ℝ) + 1

theorem taggedAdmittedGPSDiagonalStart_le_zero (N : ℕ) :
    taggedAdmittedGPSDiagonalStart N ≤ 0 := by
  simp [taggedAdmittedGPSDiagonalStart]

theorem taggedAdmittedGPSDiagonalHorizon_pos (N : ℕ) :
    0 < taggedAdmittedGPSDiagonalHorizon N := by
  dsimp [taggedAdmittedGPSDiagonalHorizon]
  positivity

theorem taggedAdmittedGPSDiagonalStart_le_horizon (N : ℕ) :
    taggedAdmittedGPSDiagonalStart N ≤ taggedAdmittedGPSDiagonalHorizon N := by
  dsimp [taggedAdmittedGPSDiagonalStart, taggedAdmittedGPSDiagonalHorizon]
  have hN : (0 : ℝ) ≤ (N : ℝ) := by positivity
  linarith

/-- The deterministic selected completion in the literal diagonal window
`[-N, N + 1)`. -/
def taggedAdmittedGPSDiagonalTagCompletion?
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (N : ℕ) :
    Option (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)) :=
  taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good capacity weight

/-- The total canonical diagonal finite response.  It uses the literal
executable trace on `[-N, N + 1)` and falls back to `0` only when the finite
trace has no tagged completion. -/
def taggedAdmittedGPSDiagonalFiniteResponse
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (N : ℕ) : ℝ :=
  taggedAdmittedFiniteGPSHorizonFenceTotalResponse
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good capacity weight

/-- Extraction of a literal finite response witness from a completion branch
of the canonical diagonal replay. -/
theorem taggedAdmittedGPSDiagonalFiniteResponse_toWitness
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (N : ℕ)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good capacity weight N = some selected) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good capacity weight,
      witness.completion = selected ∧
      taggedAdmittedGPSDiagonalFiniteResponse
        target z htarget_good capacity weight N = witness.response := by
  exact taggedAdmittedFiniteGPSHorizonFenceTagCompletion?_toWitness
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good capacity weight selected hselected

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
