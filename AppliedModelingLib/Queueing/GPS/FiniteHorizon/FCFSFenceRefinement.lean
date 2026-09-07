import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSHorizonFence
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSPositivity
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateComparison
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSplit
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSegmentRefinement
import Mathlib.Tactic

/-!
# Semantic FCFS refinement at a finite GPS drain fence

A computational GPS fence is allowed to refine an idle interval only after
the concrete FCFS ledger has literally emptied.  This module records that
two-part fact at the job level:

* aggregate drain, together with strict job positivity, empties the concrete
  FCFS ledger of the zero-batch prefix; and
* once a scheduler exposes that common prefix, arbitrary source-empty idle
  refinements preserve the complete FCFS completion records through a shared
  real endpoint batch and common suffix.

The second statement intentionally takes the structural factorization as an
input.  Aggregate final-workload equalities do not determine intermediate
segment timestamps or job-completion records, so they are not used as a
substitute for that factorization.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- A step list is source-empty when its endpoint job ledgers are literally
empty.  The predicate is semantic: it ignores segment names, fuel, and
non-arrival bookkeeping fields. -/
def finiteGPSFCFSSourceEmptySteps
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : Prop :=
  ∀ step ∈ steps, ∀ i, step.endpointJobs.jobs i = []

/-- Observational equivalence for finite FCFS executions retains every
completion record, including the record's concrete completion time. -/
def finiteGPSFCFSCompletionTraceEquivalent
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : Prop :=
  ∀ i, finiteGPSFCFSRunSegmentStepsClassCompletions initial i left =
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i right

/-- FCFS-observational equivalence of annotated steps retains the scheduler
fields used for service and completion timestamps, together with the literal
endpoint job ledger.  It intentionally does not compare computational versus
external bookkeeping flags. -/
def FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
    (left right : FiniteGPSFCFSSegmentJobStep Class JobId) : Prop :=
  FiniteGPSExecutionSegment.FCFSObservableEq left.segment right.segment ∧
    left.endpointJobs = right.endpointJobs

/-- One FCFS ledger update is unchanged by an observationally equivalent
annotated step. -/
theorem finiteGPSFCFSApplySegment_eq_of_fcfsObservableEq
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (left right : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hequivalent : FiniteGPSFCFSSegmentJobStep.FCFSObservableEq left right) :
    finiteGPSFCFSApplySegment initial left.segment left.endpointJobs =
      finiteGPSFCFSApplySegment initial right.segment right.endpointJobs := by
  rcases hequivalent with ⟨⟨_hstart, _hduration, _hrate, hservice⟩, hjobs⟩
  simp [finiteGPSFCFSApplySegment, hservice, hjobs]

/-- One class's completion records are unchanged by an observationally
equivalent annotated step.  In particular, equality retains completion time,
not merely completed identifiers. -/
theorem finiteGPSFCFSCompletedJobsInSegment_eq_of_fcfsObservableEq
    (i : Class) (jobs : List (FiniteGPSFCFSJob JobId))
    (left right : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hequivalent : FiniteGPSFCFSSegmentJobStep.FCFSObservableEq left right) :
    finiteGPSFCFSCompletedJobsInSegment left.segment i jobs =
      finiteGPSFCFSCompletedJobsInSegment right.segment i jobs := by
  rcases hequivalent with ⟨⟨hstart, _hduration, hrate, hservice⟩, _hjobs⟩
  simp [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
    hstart, hrate, hservice]

/-- Pointwise observational equivalence of annotated step lists preserves the
literal FCFS final ledger. -/
theorem finiteGPSFCFSRunSegmentSteps_eq_of_fcfsObservableEq
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hequivalent : List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
      left right) :
    finiteGPSFCFSRunSegmentSteps initial left =
      finiteGPSFCFSRunSegmentSteps initial right := by
  induction hequivalent generalizing initial with
  | nil => rfl
  | cons hhead htail ih =>
      simp only [finiteGPSFCFSRunSegmentSteps]
      rw [finiteGPSFCFSApplySegment_eq_of_fcfsObservableEq initial _ _ hhead]
      exact ih _

/-- Pointwise observational equivalence of annotated step lists preserves all
class completion records. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_fcfsObservableEq
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hequivalent : List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
      left right) :
    finiteGPSFCFSCompletionTraceEquivalent initial left right := by
  intro i
  induction hequivalent generalizing initial with
  | nil => rfl
  | cons hhead htail ih =>
      simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
      rw [finiteGPSFCFSCompletedJobsInSegment_eq_of_fcfsObservableEq i
        (initial.residualJobs i) _ _ hhead]
      rw [finiteGPSFCFSApplySegment_eq_of_fcfsObservableEq initial _ _ hhead]
      rw [ih _]

private theorem finiteGPSFCFSSegmentStepsEndpointWorkload_emptyEndpointSteps_eq
    (initialWorkload : Class → ℝ)
    (segments : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload
      (finiteGPSFCFSEmptyEndpointSteps (JobId := JobId) segments) =
        finiteGPSExecutionSegmentsFinalWorkload initialWorkload segments := by
  induction segments generalizing initialWorkload with
  | nil => rfl
  | cons segment segments ih =>
      change finiteGPSFCFSSegmentStepsEndpointWorkload segment.endpointWorkload
        (finiteGPSFCFSEmptyEndpointSteps (JobId := JobId) segments) =
          finiteGPSExecutionSegmentsFinalWorkload segment.endpointWorkload segments
      exact ih segment.endpointWorkload

/-- A drained zero-batch GPS prefix has a literally empty FCFS ledger at its
endpoint.  This strengthens aggregate workload zero only under the explicit
strict-positivity condition on queued jobs; it does not derive list emptiness
from aggregate state alone. -/
theorem finiteGPSFCFSRunGapEmptyEndpointSteps_residualJobs_eq_nil_of_aggregate_drain
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel) :
    ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial
        (finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
            currentTime nextBatchDelay))).residualJobs i = [] := by
  let segments := finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
    currentTime nextBatchDelay
  let steps := finiteGPSFCFSEmptyEndpointSteps (JobId := JobId) segments
  have hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work steps := by
    simpa [steps, segments] using
      (finiteGPSRunGapSegments_emptyEndpointSteps_compatible_of_zeroBatch
        (JobId := JobId) fuel capacity weight work currentTime nextBatchDelay initial
        hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work)
  have hendpoint_pos : ∀ step ∈ steps, ∀ i job,
      job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
    intro step hstep i job hjob
    have hstep_in_segments : ∃ segment ∈ segments,
        { segment := segment
          endpointJobs := finiteGPSFCFSEmptyEndpointJobs } = step := by
      simpa [steps, finiteGPSFCFSEmptyEndpointSteps] using hstep
    rcases hstep_in_segments with ⟨segment, _hsegment, rfl⟩
    simp [finiteGPSFCFSEmptyEndpointJobs] at hjob
  have hendpoint_workload :
      finiteGPSFCFSSegmentStepsEndpointWorkload work steps =
        finiteGPSExecutionSegmentsFinalWorkload work segments := by
    exact finiteGPSFCFSSegmentStepsEndpointWorkload_emptyEndpointSteps_eq
      (JobId := JobId) work segments
  have hrun_workload_zero : ∀ i,
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
        nextBatchDelay).workload i = 0 :=
    finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
      fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hnextBatchDelay_nonneg haggregate_drain hfuel
  have hclass_work_zero : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial steps).classWork i = 0 := by
    intro i
    calc
      (finiteGPSFCFSRunSegmentSteps initial steps).classWork i =
          finiteGPSFCFSSegmentStepsEndpointWorkload work steps i :=
        finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
          initial work steps hinitial_nonneg hcompatible i
      _ = finiteGPSExecutionSegmentsFinalWorkload work segments i := by
        rw [hendpoint_workload]
      _ = (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
          nextBatchDelay).workload i := by
        rw [finiteGPSExecutionSegmentsFinalWorkload_runGapSegments]
      _ = 0 := hrun_workload_zero i
  intro i
  simpa [steps, segments] using
    (finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_classWork_eq_zero_of_pos
      initial steps hinitial_pos hendpoint_pos i (hclass_work_zero i))

/-- Completion-trace equivalence is stable under a common already-executed
prefix. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_append_left
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (before left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hequivalent : finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps initial before) left right) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (before ++ left) (before ++ right) := by
  intro i
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSRunSegmentStepsClassCompletions_append, hequivalent i]

/-- Source-empty steps retain an already literally empty ledger. -/
theorem finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_empty : ∀ i, initial.residualJobs i = [])
    (hsource_empty : finiteGPSFCFSSourceEmptySteps steps) :
    ∀ i, (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i = [] := by
  induction steps generalizing initial with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial_empty
  | cons step steps ih =>
      have hstep_empty : ∀ i, step.endpointJobs.jobs i = [] := by
        intro i
        exact hsource_empty step (by simp) i
      have hnext_empty : ∀ i,
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i = [] := by
        intro i
        simp [finiteGPSFCFSApplySegment, finiteGPSFCFSConsume,
          hinitial_empty i, hstep_empty i]
      have htail_empty : finiteGPSFCFSSourceEmptySteps steps := by
        intro later hlater i
        exact hsource_empty later (by simp [hlater]) i
      simpa [finiteGPSFCFSRunSegmentSteps] using
        ih (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          hnext_empty htail_empty

/-- Source-empty steps emit no completion records from a literally empty
ledger. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_eq_nil_of_sourceEmptySteps
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_empty : ∀ k, initial.residualJobs k = [])
    (hsource_empty : finiteGPSFCFSSourceEmptySteps steps) :
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps = [] := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step steps ih =>
      have hstep_empty : ∀ k, step.endpointJobs.jobs k = [] := by
        intro k
        exact hsource_empty step (by simp) k
      have hnext_empty : ∀ k,
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs k = [] := by
        intro k
        simp [finiteGPSFCFSApplySegment, finiteGPSFCFSConsume,
          hinitial_empty k, hstep_empty k]
      have htail_empty : finiteGPSFCFSSourceEmptySteps steps := by
        intro later hlater k
        exact hsource_empty later (by simp [hlater]) k
      simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
      simp [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
        hinitial_empty i]
      exact ih (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        hnext_empty htail_empty

/-- Two source-empty lead-ins from a literally empty FCFS ledger leave the
same ledger after admitting the same terminal source-job batch.  This is the
state-preservation companion to the completion-trace refinement below: it
allows an unchanged future source trace to be appended without assuming that
the two computational segment scripts are syntactically equal. -/
theorem finiteGPSFCFSRunSegmentSteps_eq_of_sourceEmptyLeadIn
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (leftIdle rightIdle : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (leftTerminal rightTerminal : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hinitial_empty : ∀ i, initial.residualJobs i = [])
    (hleft_empty : finiteGPSFCFSSourceEmptySteps leftIdle)
    (hright_empty : finiteGPSFCFSSourceEmptySteps rightIdle)
    (hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs) :
    finiteGPSFCFSRunSegmentSteps initial (leftIdle ++ [leftTerminal]) =
      finiteGPSFCFSRunSegmentSteps initial (rightIdle ++ [rightTerminal]) := by
  have ledger_eq_of_residualJobs_eq : ∀ left right : FiniteGPSFCFSJobLedger Class JobId,
      (∀ k, left.residualJobs k = right.residualJobs k) → left = right := by
    intro left right heq
    cases left
    cases right
    cases funext heq
    rfl
  have hleft_idle_final_empty : ∀ k,
      (finiteGPSFCFSRunSegmentSteps initial leftIdle).residualJobs k = [] :=
    finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
      initial leftIdle hinitial_empty hleft_empty
  have hright_idle_final_empty : ∀ k,
      (finiteGPSFCFSRunSegmentSteps initial rightIdle).residualJobs k = [] :=
    finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
      initial rightIdle hinitial_empty hright_empty
  rw [finiteGPSFCFSRunSegmentSteps_append,
    finiteGPSFCFSRunSegmentSteps_append]
  simp only [finiteGPSFCFSRunSegmentSteps]
  apply ledger_eq_of_residualJobs_eq
  intro k
  simp only [finiteGPSFCFSApplySegment]
  rw [hleft_idle_final_empty k, hright_idle_final_empty k]
  simp [finiteGPSFCFSConsume, hterminal_jobs]

/-- Different source-empty idle lead-ins following an empty FCFS ledger are
observationally equivalent when they carry the same real endpoint job batch
before the same suffix.  Equality is of completion records, hence retains
completion timestamps as well as job identifiers. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (leftIdle rightIdle : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (leftTerminal rightTerminal : FiniteGPSFCFSSegmentJobStep Class JobId)
    (suffix : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_empty : ∀ i, initial.residualJobs i = [])
    (hleft_empty : finiteGPSFCFSSourceEmptySteps leftIdle)
    (hright_empty : finiteGPSFCFSSourceEmptySteps rightIdle)
    (hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      ((leftIdle ++ [leftTerminal]) ++ suffix)
      ((rightIdle ++ [rightTerminal]) ++ suffix) := by
  have ledger_eq_of_residualJobs_eq : ∀ left right : FiniteGPSFCFSJobLedger Class JobId,
      (∀ k, left.residualJobs k = right.residualJobs k) → left = right := by
    intro left right heq
    cases left
    cases right
    cases funext heq
    rfl
  have hleft_idle_final_empty : ∀ k,
      (finiteGPSFCFSRunSegmentSteps initial leftIdle).residualJobs k = [] :=
    finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
      initial leftIdle hinitial_empty hleft_empty
  have hright_idle_final_empty : ∀ k,
      (finiteGPSFCFSRunSegmentSteps initial rightIdle).residualJobs k = [] :=
    finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
      initial rightIdle hinitial_empty hright_empty
  have hblocks_final_eq : finiteGPSFCFSRunSegmentSteps initial
      (leftIdle ++ [leftTerminal]) =
      finiteGPSFCFSRunSegmentSteps initial (rightIdle ++ [rightTerminal]) := by
    rw [finiteGPSFCFSRunSegmentSteps_append,
      finiteGPSFCFSRunSegmentSteps_append]
    simp only [finiteGPSFCFSRunSegmentSteps]
    apply ledger_eq_of_residualJobs_eq
    intro k
    simp only [finiteGPSFCFSApplySegment]
    rw [hleft_idle_final_empty k, hright_idle_final_empty k]
    simp [finiteGPSFCFSConsume, hterminal_jobs]
  intro i
  have hleft_idle_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i leftIdle = [] :=
    finiteGPSFCFSRunSegmentStepsClassCompletions_eq_nil_of_sourceEmptySteps
      initial i leftIdle hinitial_empty hleft_empty
  have hright_idle_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i rightIdle = [] :=
    finiteGPSFCFSRunSegmentStepsClassCompletions_eq_nil_of_sourceEmptySteps
      initial i rightIdle hinitial_empty hright_empty
  have hleft_terminal_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps initial leftIdle) i [leftTerminal] = [] := by
    simp [finiteGPSFCFSRunSegmentStepsClassCompletions,
      finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
      hleft_idle_final_empty i]
  have hright_terminal_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps initial rightIdle) i [rightTerminal] = [] := by
    simp [finiteGPSFCFSRunSegmentStepsClassCompletions,
      finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs,
      hright_idle_final_empty i]
  have hleft_block_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i (leftIdle ++ [leftTerminal]) = [] := by
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
      hleft_idle_completions, hleft_terminal_completions]
    rfl
  have hright_block_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i (rightIdle ++ [rightTerminal]) = [] := by
    rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
      hright_idle_completions, hright_terminal_completions]
    rfl
  calc
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i
        ((leftIdle ++ [leftTerminal]) ++ suffix) =
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i
          (leftIdle ++ [leftTerminal]) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps initial (leftIdle ++ [leftTerminal])) i suffix := by
        rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    _ = finiteGPSFCFSRunSegmentStepsClassCompletions
        (finiteGPSFCFSRunSegmentSteps initial (leftIdle ++ [leftTerminal])) i suffix := by
        rw [hleft_block_completions]
        rfl
    _ = finiteGPSFCFSRunSegmentStepsClassCompletions
        (finiteGPSFCFSRunSegmentSteps initial (rightIdle ++ [rightTerminal])) i suffix := by
        rw [hblocks_final_eq]
    _ = finiteGPSFCFSRunSegmentStepsClassCompletions initial i
        ((rightIdle ++ [rightTerminal]) ++ suffix) := by
        rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
          hright_block_completions]
        rfl

/-- A semantic fence refinement is sound once the scheduler has exposed the
common zero-batch active prefix.  The theorem derives the literal empty cut
from aggregate drain and strict positivity, then keeps the real endpoint job
batch as an explicit terminal step before the shared suffix.  It does not
infer any trace equality from aggregate final-run fields. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_aggregateDrain_fenceRefinement
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (activePrefix leftIdle rightIdle : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (leftTerminal rightTerminal : FiniteGPSFCFSSegmentJobStep Class JobId)
    (suffix : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel)
    (hactive_prefix : activePrefix =
      finiteGPSFCFSEmptyEndpointSteps
        (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
          currentTime nextBatchDelay))
    (hleft_empty : finiteGPSFCFSSourceEmptySteps leftIdle)
    (hright_empty : finiteGPSFCFSSourceEmptySteps rightIdle)
    (hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (activePrefix ++ ((leftIdle ++ [leftTerminal]) ++ suffix))
      (activePrefix ++ ((rightIdle ++ [rightTerminal]) ++ suffix)) := by
  have hactive_empty : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial activePrefix).residualJobs i = [] := by
    rw [hactive_prefix]
    exact finiteGPSFCFSRunGapEmptyEndpointSteps_residualJobs_eq_nil_of_aggregate_drain
      (JobId := JobId) fuel capacity weight work currentTime nextBatchDelay initial
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hnextBatchDelay_nonneg hinitial_nonneg hinitial_matches_work hinitial_pos
      haggregate_drain hfuel
  apply finiteGPSFCFSCompletionTraceEquivalent_append_left
  exact finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
    (finiteGPSFCFSRunSegmentSteps initial activePrefix)
    leftIdle rightIdle leftTerminal rightTerminal suffix hactive_empty
    hleft_empty hright_empty hterminal_jobs

end

end AppliedModelingLib.Probability.Queueing
