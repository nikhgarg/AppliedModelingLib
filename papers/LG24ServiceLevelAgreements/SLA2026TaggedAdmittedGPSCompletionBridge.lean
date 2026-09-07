import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSTaggedCompletion
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSHorizonResponse
import Mathlib.Tactic

/-!
# Literal tagged completion from a finite admitted GPS trace

This module connects the finite, source-identified LG24 GPS trace to the
generic FCFS tagged-completion theorem.  It deliberately begins only after a
caller has supplied an actual source-boundary reset and selected the concrete
step whose endpoint admits the Palm target job.  The selected post-admission
suffix is required to remain target-active at every left endpoint; that is the
finite busy period whose duration may be charged to the GPS service floor.

No arrivals are moved to the initial state.  The literal tag is appended at
its real source endpoint, and any later computational horizon-fence endpoint
has the explicitly empty source-job batch.  This gives a finite conditional
completion witness and a deadline bound, but does not construct a stationary
GPS process or assert a response-time tail law.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The literal FCFS ledger immediately after one selected endpoint step of
the executable GPS trace.  In the intended use that endpoint is the source
batch at time zero containing `(target, 0)`; it is not an initial-condition
insertion. -/
def taggedAdmittedFiniteGPSPostAdmissionLedger
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :
    FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category) :=
  finiteGPSFCFSApplySegment
    (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
    admissionStep.segment admissionStep.endpointJobs

/-- The literal endpoint admission remains in the FCFS ledger used for the
subsequent concrete segments.  Service in the admission step is already over
when its endpoint batch is appended. -/
theorem taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (target : Category)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hadmission : job ∈ admissionStep.endpointJobs.jobs target) :
    job ∈ (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target := by
  unfold taggedAdmittedFiniteGPSPostAdmissionLedger
  simp only [finiteGPSFCFSApplySegment]
  exact List.mem_append.mpr (Or.inr hadmission)

/-- Every endpoint job in the full source trace has faithful arrival-zero
metadata for the distinguished Palm tag.  The pre-terminal side uses literal
source batches; the horizon-fence side is explicitly empty. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight,
      ∀ k job, job ∈ step.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
  intro step hstep k job hjob hidentifier
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_arrival_zero
      start horizon target z htarget_good capacity weight step hpreterminal k job hjob
      hidentifier
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      start horizon target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- A target-labelled completion in the full finite trace retains the exact
Palm source arrival time zero.  This follows through the concrete FCFS fold,
including its source-empty computational horizon fence. -/
theorem taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight)
    (hidentifier : completion.identifier = (target, 0)) :
    completion.arrivalTime = 0 := by
  change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) at hcompletion
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
      completion hcompletion with
      ⟨before, step, after, hsplit, hstepCompletion⟩
  have hbefore_endpoint : ∀ earlierStep ∈ before, ∀ k job,
      job ∈ earlierStep.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
    intro earlierStep hearlier k job hjob htag
    apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_target_arrival_zero
      start horizon target z htarget_good capacity weight earlierStep
    · rw [hsplit]
      exact List.mem_append.mpr (Or.inl hearlier)
    · exact hjob
    · exact htag
  have hbefore_ledger : TaggedAdmittedTargetArrivalZeroLedger target
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before) := by
    apply taggedAdmittedFCFSRunSegmentSteps_target_arrival_zero target z
      taggedAdmittedEmptyFCFSLedger before
    · exact taggedAdmittedEmptyFCFSLedger_target_arrival_zero target
    · exact hbefore_endpoint
  rcases finiteGPSFCFSCompletedJobsInSegment_has_source_job
      step.segment target
      ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)
      completion hstepCompletion with
      ⟨sourceJob, hsourceJob, hcompletion_identifier, hcompletion_arrival⟩
  have hsource_identifier : sourceJob.identifier = (target, 0) := by
    calc
      sourceJob.identifier = completion.identifier := hcompletion_identifier.symm
      _ = (target, 0) := hidentifier
  have hsource_arrival : sourceJob.arrivalTime = 0 :=
    hbefore_ledger target sourceJob hsourceJob hsource_identifier
  calc
    completion.arrivalTime = sourceJob.arrivalTime := hcompletion_arrival
    _ = 0 := hsource_arrival

/-- A finite completion emitted by a selected concrete suffix meets a
deadline whenever each selected segment has a positive class rate, records
exact rate-times-duration service, and ends by that deadline. -/
private theorem finiteGPSFCFSRunSegmentStepsClassCompletion_completionTime_le_of_segmentBounds
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

/-- Conditional source-faithful tagged completion bridge.  `start` is the
actual source boundary supplied by a prior reset construction; the supplied
split identifies the concrete endpoint where the literal tag is appended.
If a subsequent selected consecutive busy prefix stays target-active and its
GPS guaranteed-rate duration covers the literal FCFS front work, it emits a
completion record for `(target, 0)` by `deadline`.  The remaining finite
trace is retained only to lift that concrete completion into the full
source/fence execution.

The nonnegativity and segment-timestamp hypotheses are explicit finite
executor obligations.  They are not substituted by a stationary or
continuous-path assumption here. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_postAdmissionFrontWork_le_floorDuration
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
    (busy : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (tail : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: (busy ++ tail))
    (htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      admissionStep.endpointJobs.jobs target)
    (hpost_target_nonneg : ∀ job ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target,
      0 ≤ job.residualWork)
    (hbusy_service_nonneg : ∀ step ∈ busy, 0 ≤ step.segment.serviceIncrement target)
    (hbusy_endpoint_nonneg : ∀ step ∈ busy, ∀ job ∈ step.endpointJobs.jobs target,
      0 ≤ job.residualWork)
    (hbusy_active : ∀ step ∈ busy, 0 < step.segment.startWorkload target)
    (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target) =
        some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration : frontWork ≤ capacity * weight target *
      finiteGPSFCFSSegmentStepsTotalDuration busy)
    (deadline : ℝ)
    (hbusy_classRate_pos : ∀ step ∈ busy, 0 < step.segment.classRate target)
    (hbusy_service_eq_rate_mul_duration : ∀ step ∈ busy,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration)
    (hbusy_end_le_deadline : ∀ step ∈ busy,
      finiteGPSExecutionSegmentEndTime step.segment ≤ deadline) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.completionTime ≤ deadline ∧
        witness.response ≤ deadline := by
  have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep).residualJobs target :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
      before admissionStep target (taggedAdmittedFCFSJob target z (target, 0)) htag_admitted
  have hbusy_floor : ∀ step ∈ busy,
      0 < step.segment.startWorkload target →
        capacity * weight target * step.segment.duration ≤
          step.segment.serviceIncrement target := by
    intro step hstep hactive
    apply taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg target step
    · rw [hsplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inl hstep)))))
    · exact hactive
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      capacity weight
      (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep)
      target busy frontWork hpost_target_nonneg hbusy_service_nonneg
      hbusy_endpoint_nonneg hbusy_floor hbusy_active hfront hfront_pos
      hfront_le_floor_duration with
      ⟨completion, hcompletion, hkey⟩
  have hidentifier : completion.identifier = (target, 0) := by
    exact of_decide_eq_true hkey
  have hfull_completion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      start horizon target z htarget_good capacity weight := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
    rw [hsplit, finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    change completion ∈ _ ++
      (finiteGPSFCFSCompletedJobsInSegment admissionStep.segment target
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedFiniteGPSPostAdmissionLedger before admissionStep) target (busy ++ tail))
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    exact List.mem_append.mpr (Or.inr (List.mem_append.mpr
      (Or.inr (List.mem_append.mpr (Or.inl hcompletion)))))
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
      target busy deadline hbusy_classRate_pos hbusy_service_eq_rate_mul_duration
      hbusy_end_le_deadline completion hcompletion
  refine ⟨witness, htime, ?_⟩
  rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    start horizon target z htarget_good capacity weight witness]
  exact htime

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
