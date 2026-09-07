import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompletionBridge
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedClosedPreTagSourceProjection
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSExecutionSemantics
import Mathlib.Tactic

/-!
# Compatible literal tagged-completion bridge

This module refines the earlier finite completion bridge by deriving its
post-admission FCFS safety facts from the compatibility certificate of the
*whole literal source trace*.  A caller supplies an actual split of that
trace at the endpoint that admits the tag and the literal suffix to be used
for the deadline argument.  No list is reconstructed and no endpoint work is
silently inserted.

The resulting theorem is deliberately finite and conditional.  It does not
choose the tag endpoint, prove that a selected suffix is a physical
post-zero/deadline interval, construct a stationary GPS process, or assert a
Palm response-time law.  Those are source-model obligations, retained as
explicit hypotheses at the final adapter boundary.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The aggregate workload immediately after the literal endpoint that
admits the tag.  This is the endpoint workload produced by the same concrete
prefix that defines `taggedAdmittedFiniteGPSPostAdmissionLedger`. -/
def taggedAdmittedFiniteGPSPostAdmissionWorkload
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :
    Category → ℝ :=
  finiteGPSFCFSSegmentStepsEndpointWorkload (fun _ : Category => 0)
    (before ++ [admissionStep])

/-- Folding the literal prefix through its endpoint is exactly the named
post-admission ledger. -/
theorem taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :
    taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep =
      finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
        (before ++ [admissionStep]) := by
  rw [finiteGPSFCFSRunSegmentSteps_append]
  simp [taggedAdmittedFiniteGPSPostAdmissionLedger,
    finiteGPSFCFSRunSegmentSteps]

/-- An explicit literal split of the full source/fence trace gives the
actual post-admission suffix its FCFS compatibility certificate.  In
particular, endpoint-job nonnegativity and no-overservice are inherited from
the executable full trace rather than supplied ad hoc by a completion caller.
-/
theorem taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after) :
    FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
      after := by
  let preSteps := before ++ [admissionStep]
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight = preSteps ++ after := by
    dsimp [preSteps]
    rw [hsplit]
    simp [List.append_assoc]
  have hfull : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfull_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) (preSteps ++ after) := by
    rw [← hsplit']
    exact hfull
  have hsuffix := finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) preSteps after hfull_split
  simpa only [preSteps, taggedAdmittedFiniteGPSPostAdmissionWorkload,
    taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using hsuffix

/-- The post-admission ledger in an explicit literal full-trace split is
nonnegative.  This is obtained by restricting the full compatibility
certificate to the concrete prefix and folding its proved local invariants.
-/
theorem taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after) :
    (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).Nonnegative := by
  let preSteps := before ++ [admissionStep]
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight = preSteps ++ after := by
    dsimp [preSteps]
    rw [hsplit]
    simp [List.append_assoc]
  have hfull : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfull_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) (preSteps ++ after) := by
    rw [← hsplit']
    exact hfull
  have hprefix := finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) preSteps after hfull_split
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hprefix_nonneg := finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) preSteps hempty_nonneg hprefix
  simpa only [preSteps, taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix]
    using hprefix_nonneg

/-- When the literal source interval contains the Palm epoch, the existing
source-admission theorem supplies an actual split at the endpoint that carries
the tag.  Thus downstream applications need not manufacture a list position
or postulate that the tag was inserted into an initial ledger. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalPostAdmissionSplit
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈
          admissionStep.endpointJobs.jobs target := by
  rcases taggedAdmittedTargetFCFSJob_admitted_in_horizonFenceRun
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, hsplit, htag_admitted⟩
  exact ⟨before, admissionStep, after, hsplit, htag_admitted⟩

/-- The literal tag-admission split obtained from the positive-horizon source
trace is anchored at physical time zero.  This is derived from source-job
provenance, not accepted as a timing premise by a completion caller. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalPostAdmissionSplit_at_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃ before admissionStep after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight =
          before ++ admissionStep :: after ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈
          admissionStep.endpointJobs.jobs target ∧
        finiteGPSExecutionSegmentEndTime admissionStep.segment = 0 := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalPostAdmissionSplit
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨before, admissionStep, after, hsplit, htag_admitted⟩
  refine ⟨before, admissionStep, after, hsplit, htag_admitted, ?_⟩
  apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSStep_tag_endTime_eq_zero
    start horizon target z htarget_good capacity weight admissionStep
  · rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  · exact htag_admitted

/-- A completion emitted by a literal selected suffix meets a supplied
deadline when every suffix segment has its actual positive target rate,
stores its rate-times-duration service identity, and ends no later than that
deadline. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_completionTime_le_of_segmentBounds
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (i : Category)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (deadline : ℝ)
    (hclassRate_pos : ∀ step ∈ steps, 0 < step.segment.classRate i)
    (hservice_eq_rate_mul_duration : ∀ step ∈ steps,
      step.segment.serviceIncrement i = step.segment.classRate i * step.segment.duration)
    (hend_le_deadline : ∀ step ∈ steps,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline)
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i steps) :
    completion.completionTime ≤ deadline := by
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
      initial i steps completion hcompletion with
      ⟨before, step, after, hsplit, hstepCompletion⟩
  have hstep_mem : step ∈ steps := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  exact (finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime
    step.segment i ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i)
    (hclassRate_pos step hstep_mem)
    (hservice_eq_rate_mul_duration step hstep_mem)
    completion hstepCompletion).trans (hend_le_deadline step hstep_mem)

/-- Source adapter for the generic compatible completion theorem.  Given an
actual literal split at the tag-admission endpoint, this theorem derives the
post-admission nonnegativity, endpoint-batch safety, and no-overservice facts
from the full executable trace.  Its remaining premises separate cleanly:
the front-work comparison is the substantive comparator obligation;
`hafter_classRate_pos` and `hafter_service_eq_rate_mul_duration` are
executable-segment semantic facts still awaiting projection lemmas; and
`hafter_end_le_deadline` is the genuine source-clock condition for the
selected literal suffix.

It intentionally does not assert that the selected admission endpoint is the
physical zero boundary, or that the selected suffix contains precisely the
source segments through `deadline`; a source timing theorem must establish
those facts before this finite adapter can support a response-tail claim. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_literalPostAdmissionFrontWork_le_floorDuration
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after)
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (htagged_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0))
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ capacity * weight target *
      finiteGPSFCFSSegmentStepsTotalDuration after)
    (deadline : ℝ)
    (hafter_classRate_pos : ∀ step ∈ after, 0 < step.segment.classRate target)
    (hafter_service_eq_rate_mul_duration : ∀ step ∈ after,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration)
    (hafter_end_le_deadline : ∀ step ∈ after,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.completionTime ≤ deadline ∧
        witness.response ≤ deadline := by
  have hpost_compatible :=
    taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before admissionStep after hsplit
  have hpost_nonneg :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before admissionStep after hsplit
  have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
      before admissionStep target (taggedAdmittedFCFSJob target z (target, 0)) htag_admitted
  have htag_pos : 0 < (taggedAdmittedFCFSJob target z (target, 0)).residualWork := by
    simpa [taggedAdmittedFCFSJob] using htagged_work_pos
  have hafter_floor : ∀ step ∈ after,
      0 < step.segment.startWorkload target →
        capacity * weight target * step.segment.duration ≤
          step.segment.serviceIncrement target := by
    intro step hstep hactive
    apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target step
    · rw [hsplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep)))
    · exact hactive
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration_of_compatible
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      capacity weight
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
      target after frontWork (taggedAdmittedFCFSJob target z (target, 0))
      hpost_nonneg hpost_compatible htag_after htag_pos (by simp) hafter_floor
      hfront hfront_pos hfront_le_floor_duration with
      ⟨completion, hcompletion, hkey⟩
  have hidentifier : completion.identifier = (target, 0) :=
    of_decide_eq_true hkey
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        (before ++ [admissionStep]) ++ after := by
    rw [hsplit]
    simp [List.append_assoc]
  have hfull_completion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
    rw [hsplit', finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    apply List.mem_append.mpr
    right
    simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using hcompletion
  have harrival : completion.arrivalTime = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
      start horizon target z htarget_good capacity weight completion hfull_completion hidentifier
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight :=
    { completion := completion
      completion_mem := hfull_completion
      identifier_eq_tag := hidentifier
      arrival_eq_zero := harrival }
  have htime : completion.completionTime ≤ deadline :=
    finiteGPSFCFSRunSegmentStepsClassCompletion_completionTime_le_of_segmentBounds
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      target after deadline hafter_classRate_pos hafter_service_eq_rate_mul_duration
      hafter_end_le_deadline completion hcompletion
  refine ⟨witness, htime, ?_⟩
  rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    start horizon target z htarget_good capacity weight witness]
  exact htime

/-- Finite deadline-window completion theorem for the literal target tag.
The window is not a caller-declared busy list: it is the canonical initial
active prefix of the actual post-admission suffix.  Compatibility and ledger
nonnegativity are restricted from the complete source/fence trace.  If the
front work fits in the GPS floor over that concrete prefix, a target
completion is emitted in the prefix.

The remaining endpoint-time premise says exactly that this selected concrete
window ends by `deadline`.  Unlike the older `busy` bridge, there is no
premise asserting target activity: membership in the canonical prefix proves
it.  The rate/service premises are stated semantically over stored segment
fields and can be discharged by executable-trace projection lemmas. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_initialActivePrefixFrontWork_le_floorDuration
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after)
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (htagged_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0))
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ capacity * weight target *
      finiteGPSFCFSSegmentStepsTotalDuration
        (finiteGPSFCFSSegmentStepsInitialActivePrefix target after))
    (hafter_classRate_pos_of_active : ∀ step ∈ after,
      0 < step.segment.startWorkload target → 0 < step.segment.classRate target)
    (hafter_service_eq_rate_mul_duration : ∀ step ∈ after,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration)
    (deadline : ℝ)
    (hactivePrefix_end_le_deadline : ∀ step ∈
      finiteGPSFCFSSegmentStepsInitialActivePrefix target after,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.completionTime ≤ deadline ∧
        witness.response ≤ deadline := by
  let activeSteps := finiteGPSFCFSSegmentStepsInitialActivePrefix target after
  let laterSteps := after.dropWhile fun step =>
    decide (0 < step.segment.startWorkload target)
  have hafter_eq : after = activeSteps ++ laterSteps := by
    dsimp [activeSteps, laterSteps,
      finiteGPSFCFSSegmentStepsInitialActivePrefix]
    exact List.takeWhile_append_dropWhile.symm
  have hpost_compatible :=
    taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before admissionStep after hsplit
  have hpost_nonneg :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      before admissionStep after hsplit
  have hpost_compatible_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
      (activeSteps ++ laterSteps) := by
    rw [← hafter_eq]
    exact hpost_compatible
  have hactive_compatible := finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
    (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
    activeSteps laterSteps hpost_compatible_split
  have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
      before admissionStep target (taggedAdmittedFCFSJob target z (target, 0)) htag_admitted
  have htag_pos : 0 < (taggedAdmittedFCFSJob target z (target, 0)).residualWork := by
    simpa [taggedAdmittedFCFSJob] using htagged_work_pos
  have hactive_floor : ∀ step ∈ activeSteps,
      0 < step.segment.startWorkload target →
        capacity * weight target * step.segment.duration ≤
          step.segment.serviceIncrement target := by
    intro step hstep hactive
    apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target step
    · rw [hsplit]
      apply List.mem_append.mpr
      right
      apply List.mem_cons.mpr
      right
      exact List.takeWhile_subset _ (by
        simpa [activeSteps, finiteGPSFCFSSegmentStepsInitialActivePrefix] using hstep)
    · exact hactive
  have hactive_classRate_pos : ∀ step ∈ activeSteps,
      0 < step.segment.classRate target := by
    intro step hstep
    apply hafter_classRate_pos_of_active step
      (List.takeWhile_subset _ (by
        simpa [activeSteps, finiteGPSFCFSSegmentStepsInitialActivePrefix] using hstep))
    exact finiteGPSFCFSSegmentStepsInitialActivePrefix_mem_active
      target after step (by simpa [activeSteps] using hstep)
  have hactive_service_eq : ∀ step ∈ activeSteps,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration := by
    intro step hstep
    apply hafter_service_eq_rate_mul_duration step
    exact List.takeWhile_subset _ (by
      simpa [activeSteps, finiteGPSFCFSSegmentStepsInitialActivePrefix] using hstep)
  have hactive_end_le_deadline : ∀ step ∈ activeSteps,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline := by
    intro step hstep
    apply hactivePrefix_end_le_deadline step
    simpa [activeSteps] using hstep
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration_of_compatible
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      capacity weight
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
      target activeSteps frontWork (taggedAdmittedFCFSJob target z (target, 0))
      hpost_nonneg hactive_compatible htag_after htag_pos (by simp) hactive_floor
      hfront hfront_pos (by simpa [activeSteps] using hfront_le_floor_duration) with
      ⟨completion, hcompletion, hkey⟩
  have hidentifier : completion.identifier = (target, 0) :=
    of_decide_eq_true hkey
  have hfull_split : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        (before ++ [admissionStep]) ++ (activeSteps ++ laterSteps) := by
    rw [hsplit, hafter_eq]
    simp [List.append_assoc]
  have hfull_completion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
    rw [hfull_split]
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append
      taggedAdmittedEmptyFCFSLedger target (before ++ [admissionStep])
      (activeSteps ++ laterSteps)]
    apply List.mem_append.mpr
    right
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
        (before ++ [admissionStep])) target activeSteps laterSteps]
    apply List.mem_append.mpr
    left
    simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using hcompletion
  have harrival : completion.arrivalTime = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
      start horizon target z htarget_good capacity weight completion hfull_completion hidentifier
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight :=
    { completion := completion
      completion_mem := hfull_completion
      identifier_eq_tag := hidentifier
      arrival_eq_zero := harrival }
  have htime : completion.completionTime ≤ deadline :=
    finiteGPSFCFSRunSegmentStepsClassCompletion_completionTime_le_of_segmentBounds
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      target activeSteps deadline hactive_classRate_pos hactive_service_eq
      hactive_end_le_deadline completion hcompletion
  refine ⟨witness, htime, ?_⟩
  rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    start horizon target z htarget_good capacity weight witness]
  exact htime

/-- The executable GPS runner discharges the rate and service semantic
premises of the canonical deadline-window theorem.  What remains is only the
front-work comparison and the literal source-clock assertion that the chosen
canonical post-tag window ends by `deadline`. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_initialActivePrefixFrontWork_le_floorDuration_of_executableSemantics
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after)
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (htagged_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0))
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ capacity * weight target *
      finiteGPSFCFSSegmentStepsTotalDuration
        (finiteGPSFCFSSegmentStepsInitialActivePrefix target after))
    (deadline : ℝ)
    (hactivePrefix_end_le_deadline : ∀ step ∈
      finiteGPSFCFSSegmentStepsInitialActivePrefix target after,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.completionTime ≤ deadline ∧
        witness.response ≤ deadline := by
  apply taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_initialActivePrefixFrontWork_le_floorDuration
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    before admissionStep after hsplit htag_admitted htagged_work_pos
    frontWork hfront hfront_pos hfront_le_floor_duration
  · intro step hstep hactive
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))) |>.1 hactive
  · intro step hstep
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))) |>.2
  · exact hactivePrefix_end_le_deadline

/-- Natural finite-horizon specialization of the canonical deadline-window
bridge.  The executable source/fence trace itself proves that every selected
post-tag active-prefix segment ends by `horizon`, so no deadline-bound premise
remains.  This is still a finite conditional theorem: the unresolved
mathematical input is precisely the literal FCFS front-work comparison. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_by_horizon_of_initialActivePrefixFrontWork_le_floorDuration
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after)
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (htagged_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0))
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ capacity * weight target *
      finiteGPSFCFSSegmentStepsTotalDuration
        (finiteGPSFCFSSegmentStepsInitialActivePrefix target after)) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.completionTime ≤ horizon ∧
        witness.response ≤ horizon := by
  apply taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_initialActivePrefixFrontWork_le_floorDuration_of_executableSemantics
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    before admissionStep after hsplit htag_admitted htagged_work_pos
    frontWork hfront hfront_pos hfront_le_floor_duration
  intro step hstep
  apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endTime_le_horizon
    start horizon target z htarget_good capacity weight hstart_le_horizon step
  rw [hsplit]
  apply List.mem_append.mpr
  right
  apply List.mem_cons.mpr
  right
  exact List.takeWhile_subset _ (by
    simpa [finiteGPSFCFSSegmentStepsInitialActivePrefix] using hstep)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
