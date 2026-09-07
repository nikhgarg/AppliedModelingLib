import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSFCFS
import Mathlib.Tactic

/-!
# Finite tagged-job completion records for the admitted GPS construction

This module follows the literal tagged source job through the finite
source-to-FCFS adapter and the executable class-wise completion trace.  It
records only a conditional finite completion witness.  In particular, it does
not assert that the tagged job completes by a chosen horizon, or make a
stationary, Palm, probability, or tail claim.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The empty FCFS ledger used with the empty initial GPS workload. -/
def taggedAdmittedEmptyFCFSLedger :
    FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category) where
  residualJobs := fun _ => []

/-- A ledger is faithful to the literal tagged arrival epoch when any residual
record carrying the distinguished source identifier `(target, 0)` has arrival
time zero. -/
def TaggedAdmittedTargetArrivalZeroLedger
    (target : Category) (ledger : FiniteGPSFCFSJobLedger Category
      (TaggedAdmittedSourceJobId Category)) : Prop :=
  ∀ k job, job ∈ ledger.residualJobs k →
    job.identifier = (target, 0) → job.arrivalTime = 0

/-- The actual target-class completion records from the empty finite GPS/FCFS
state through the tagged source trace before its computational horizon fence. -/
def taggedAdmittedFiniteGPSPreTerminalTargetCompletions
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)) :=
  finiteGPSFCFSRunSegmentStepsClassCompletions taggedAdmittedEmptyFCFSLedger target
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0))

/-- A conditional witness that the literal tagged source record completed in
the finite pre-terminal target-class trace.  Existence is intentionally not
asserted by this definition. -/
structure TaggedAdmittedFiniteGPSResponseWitness
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) where
  completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)
  completion_mem : completion ∈ taggedAdmittedFiniteGPSPreTerminalTargetCompletions
    start horizon target z htarget_good capacity weight
  identifier_eq_tag : completion.identifier = (target, 0)

/-- Response time represented by a finite completion witness. -/
def TaggedAdmittedFiniteGPSResponseWitness.response
    {start horizon : ℝ} {target : Category}
    {z : StationaryAdmittedTargetPassiveTaggedInput target}
    {htarget_good : palmTaggedArrivalGoodCarrier z.1.1}
    {capacity : ℝ} {weight : Category → ℝ}
    (witness : TaggedAdmittedFiniteGPSResponseWitness
      start horizon target z htarget_good capacity weight) : ℝ :=
  witness.completion.completionTime - witness.completion.arrivalTime

/-- The literal tagged job is admitted into its physical zero-time source
endpoint batch whenever `[start, horizon)` contains zero. -/
theorem taggedAdmittedTargetFCFSJob_admitted_at_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target := by
  exact taggedAdmittedTargetFCFSJob_mem_zeroBatch
    start horizon target z htarget_good hstart hhorizon

/-- Under the ordinary finite GPS conditions, the literal tagged source job
is present exactly once in the actual external endpoint batches of the empty
pre-terminal FCFS execution.  This is admission only, not completion. -/
theorem taggedAdmittedTargetFCFSJob_admitted_once_in_emptyPreTerminalSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    ∃! endpointJobs : FiniteGPSFCFSEndpointJobs Category
        (TaggedAdmittedSourceJobId Category),
      endpointJobs ∈ taggedAdmittedFiniteGPSExternalEndpointJobBatches
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)) ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈ endpointJobs.jobs target := by
  simpa using
    (taggedAdmittedTargetFCFSJob_appears_once_in_preTerminalExternalEndpointBatches
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hsource_work_nonneg hstart hhorizon)

/-- The empty ledger satisfies the tagged arrival-zero invariant. -/
theorem taggedAdmittedEmptyFCFSLedger_target_arrival_zero
    (target : Category) :
    TaggedAdmittedTargetArrivalZeroLedger target taggedAdmittedEmptyFCFSLedger := by
  intro k job hjob
  simp [taggedAdmittedEmptyFCFSLedger] at hjob

/-- Every literal source endpoint job with the distinguished identifier has
the actual tagged arrival time zero. -/
theorem taggedAdmittedFCFSJobsAt_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (k : Category)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs k)
    (hidentifier : job.identifier = (target, 0)) :
    job.arrivalTime = 0 := by
  unfold taggedAdmittedFCFSJobsAt at hjob
  rcases List.mem_map.mp hjob with ⟨n, _hn, rfl⟩
  have hsource : (k, n) = (target, 0) := by
    simpa [taggedAdmittedFCFSJob] using hidentifier
  cases hsource
  simpa [taggedAdmittedFCFSJob] using
    (taggedAdmittedSourceArrival_target_zero target z)

/-- The source-selected endpoint job list retains the tagged arrival-zero
property, while an internal computational endpoint contains no source job. -/
theorem taggedAdmittedFiniteGPSEndpointJobsForSegment_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (segment : FiniteGPSExecutionSegment Category)
    (k : Category) (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ (taggedAdmittedFiniteGPSEndpointJobsForSegment
      start horizon target z eventTime segment).jobs k)
    (hidentifier : job.identifier = (target, 0)) :
    job.arrivalTime = 0 := by
  by_cases hExternal : segment.endpointIsExternalBatch = true
  · apply taggedAdmittedFCFSJobsAt_target_arrival_zero
      start horizon target z eventTime k job
    · simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using hjob
    · exact hidentifier
  · simp [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal,
      taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- FCFS consumption changes only residual work, so it preserves the literal
tagged arrival-zero property of every retained job record. -/
theorem taggedAdmittedFCFSConsume_target_arrival_zero
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (availableService : ℝ) (jobs : List (FiniteGPSFCFSJob
      (TaggedAdmittedSourceJobId Category)))
    (hjobs : ∀ job ∈ jobs, job.identifier = (target, 0) → job.arrivalTime = 0) :
    ∀ outputJob ∈ finiteGPSFCFSConsume availableService jobs,
      outputJob.identifier = (target, 0) → outputJob.arrivalTime = 0 := by
  induction jobs generalizing availableService with
  | nil =>
      simp [finiteGPSFCFSConsume]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · intro outputJob houtput hidentifier
        rw [finiteGPSFCFSConsume_eq_partial_head
          availableService job jobs hpartial] at houtput
        rcases List.mem_cons.mp houtput with hhead | htail
        · subst outputJob
          simpa using hjobs job (by simp) hidentifier
        · exact hjobs outputJob (by simp [htail]) hidentifier
      · intro outputJob houtput hidentifier
        rw [finiteGPSFCFSConsume_eq_after_complete_head
          availableService job jobs hpartial] at houtput
        exact ih (availableService := availableService - job.residualWork)
          (fun later hlater htag => hjobs later (by simp [hlater]) htag)
          outputJob houtput hidentifier

/-- Applying one finite FCFS segment preserves the tagged arrival-zero
invariant when both the pre-step ledger and endpoint source jobs satisfy it. -/
theorem taggedAdmittedFCFSApplySegment_target_arrival_zero
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (ledger : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (segment : FiniteGPSExecutionSegment Category)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Category (TaggedAdmittedSourceJobId Category))
    (hledger : TaggedAdmittedTargetArrivalZeroLedger target ledger)
    (hendpoint : ∀ k job, job ∈ endpointJobs.jobs k →
      job.identifier = (target, 0) → job.arrivalTime = 0) :
    TaggedAdmittedTargetArrivalZeroLedger target
      (finiteGPSFCFSApplySegment ledger segment endpointJobs) := by
  intro k job hjob hidentifier
  simp only [finiteGPSFCFSApplySegment] at hjob
  rcases List.mem_append.mp hjob with hserved | hendpointJob
  · exact taggedAdmittedFCFSConsume_target_arrival_zero target z
      (segment.serviceIncrement k) (ledger.residualJobs k)
      (fun sourceJob hsourceJob htag => hledger k sourceJob hsourceJob htag)
      job hserved hidentifier
  · exact hendpoint k job hendpointJob hidentifier

/-- The fixed finite FCFS fold preserves the tagged arrival-zero invariant
when every supplied endpoint job batch has the same source-faithful property. -/
theorem taggedAdmittedFCFSRunSegmentSteps_target_arrival_zero
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hinitial : TaggedAdmittedTargetArrivalZeroLedger target initial)
    (hendpoint : ∀ step ∈ steps, ∀ k job, job ∈ step.endpointJobs.jobs k →
      job.identifier = (target, 0) → job.arrivalTime = 0) :
    TaggedAdmittedTargetArrivalZeroLedger target
      (finiteGPSFCFSRunSegmentSteps initial steps) := by
  induction steps generalizing initial with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial
  | cons step steps ih =>
      have hnext : TaggedAdmittedTargetArrivalZeroLedger target
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) := by
        apply taggedAdmittedFCFSApplySegment_target_arrival_zero target z
          initial step.segment step.endpointJobs hinitial
        intro k job hjob hidentifier
        exact hendpoint step (by simp) k job hjob hidentifier
      apply ih (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
      · exact hnext
      · intro laterStep hlaterStep k job hjob hidentifier
        exact hendpoint laterStep (by simp [hlaterStep]) k job hjob hidentifier

/-- One source-labelled GPS/FCFS step has the tagged arrival-zero property at
its endpoint, whether that endpoint is external or computational. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (k : Category) (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈ (taggedAdmittedFiniteGPSBuildSegmentJobStep
      start horizon target z eventTime capacity weight work
      currentTime nextBatchDelay).endpointJobs.jobs k)
    (hidentifier : job.identifier = (target, 0)) :
    job.arrivalTime = 0 := by
  apply taggedAdmittedFiniteGPSEndpointJobsForSegment_target_arrival_zero
    start horizon target z eventTime
    (finiteGPSBuildExecutionSegment capacity weight work
      (taggedAdmittedBatchAt start horizon target z eventTime)
      currentTime nextBatchDelay)
    k job
  · simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using hjob
  · exact hidentifier

/-- Every endpoint job in one annotated finite gap has the tagged
arrival-zero property for the distinguished literal source identifier. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay,
      ∀ k job, job ∈ step.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      unfold taggedAdmittedFiniteGPSGapSegmentJobSteps
      dsimp only
      split
      · intro step hstep k job hjob hidentifier
        have hstep_eq : step = taggedAdmittedFiniteGPSBuildSegmentJobStep
            start horizon target z eventTime capacity weight work
            currentTime nextBatchDelay := by
          simpa using hstep
        subst step
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_arrival_zero
          start horizon target z eventTime capacity weight work
          currentTime nextBatchDelay k job hjob hidentifier
      · intro step hstep k job hjob hidentifier
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_target_arrival_zero
            start horizon target z eventTime capacity weight work
            currentTime nextBatchDelay k job hjob hidentifier
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime +
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (nextBatchDelay := nextBatchDelay -
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            step htail k job hjob hidentifier

/-- Every endpoint job in the finite annotated source batch trace has the
same literal tagged-arrival metadata property. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (capacity : ℝ)
    (weight work : Category → ℝ) (currentTime : ℝ) (times : List ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      ∀ k job, job ∈ step.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have hbatchApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchApplied]
        intro step hstep k job hjob hidentifier
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_arrival_zero
            start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
            capacity weight work currentTime (eventTime - currentTime)
            step hgap k job hjob hidentifier
        · exact ih
            (currentTime := eventTime)
            (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).workload)
            step htail k job hjob hidentifier
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchNotApplied]
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_target_arrival_zero
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime)

/-- The actual pre-terminal source-labelled FCFS steps retain the literal
tagged arrival-zero property at every endpoint job batch. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0),
      ∀ k job, job ∈ step.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_target_arrival_zero
      start horizon target z capacity weight (fun _ => 0) start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)

/-- Folding the actual pre-terminal source-labelled steps from the empty
ledger preserves the literal tagged arrival-zero invariant. -/
theorem taggedAdmittedFiniteGPSPreTerminalTargetLedger_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    TaggedAdmittedTargetArrivalZeroLedger target
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0))) := by
  apply taggedAdmittedFCFSRunSegmentSteps_target_arrival_zero target z
    taggedAdmittedEmptyFCFSLedger
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0))
  · exact taggedAdmittedEmptyFCFSLedger_target_arrival_zero target
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_arrival_zero
      start horizon target z htarget_good capacity weight

/-- Any recorded completion bearing the literal tag comes from a source job
whose retained arrival metadata is the physical tagged epoch zero. -/
theorem taggedAdmittedFiniteGPSPreTerminalTargetCompletion_arrival_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hcompletion : completion ∈ taggedAdmittedFiniteGPSPreTerminalTargetCompletions
      start horizon target z htarget_good capacity weight)
    (hidentifier : completion.identifier = (target, 0)) :
    completion.arrivalTime = 0 := by
  change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight (fun _ => 0)) at hcompletion
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
    taggedAdmittedEmptyFCFSLedger target
    (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0))
    completion hcompletion with
    ⟨before, step, after, hsplit, hstepCompletion⟩
  have hbefore_endpoint : ∀ earlierStep ∈ before, ∀ k job,
      job ∈ earlierStep.endpointJobs.jobs k →
        job.identifier = (target, 0) → job.arrivalTime = 0 := by
    intro earlierStep hearlier k job hjob htag
    apply taggedAdmittedFiniteGPSPreTerminalFCFSSteps_target_arrival_zero
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

/-- A tagged finite completion witness has the literal selected source
identifier and the physical zero arrival epoch. -/
theorem TaggedAdmittedFiniteGPSResponseWitness_source_faithful
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (witness : TaggedAdmittedFiniteGPSResponseWitness
      start horizon target z htarget_good capacity weight) :
    witness.completion.identifier = (target, 0) ∧ witness.completion.arrivalTime = 0 := by
  constructor
  · exact witness.identifier_eq_tag
  · exact taggedAdmittedFiniteGPSPreTerminalTargetCompletion_arrival_zero
      start horizon target z htarget_good capacity weight witness.completion
      witness.completion_mem witness.identifier_eq_tag

/-- Because the literal tagged source arrival is at zero, the response time
of any recorded finite tagged completion is exactly its completion time. -/
theorem TaggedAdmittedFiniteGPSResponseWitness_response_eq_completionTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (witness : TaggedAdmittedFiniteGPSResponseWitness
      start horizon target z htarget_good capacity weight) :
    witness.response = witness.completion.completionTime := by
  unfold TaggedAdmittedFiniteGPSResponseWitness.response
  rw [(TaggedAdmittedFiniteGPSResponseWitness_source_faithful
    start horizon target z htarget_good capacity weight witness).2]
  ring

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
