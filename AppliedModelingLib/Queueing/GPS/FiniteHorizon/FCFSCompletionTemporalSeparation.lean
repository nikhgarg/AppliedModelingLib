import AppliedModelingLib.Queueing.GPS.FiniteHorizon.CompletionTiming
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import Mathlib.Tactic

/-!
# Temporal separation of finite FCFS completion traces

These lemmas make the time ordering carried by an executable segment chain
available to finite FCFS completion traces.  They are source-agnostic: a
caller may use a literal future source epoch to show that a completion before
that epoch belongs to an actual preterminal prefix rather than a later
computational suffix.

No result here compares raw completion records across a refinement.  The
interface is solely a physical lower timestamp bound and a list-boundary
membership fact.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- In a chronological concrete segment chain with nonnegative durations,
every segment begins no earlier than the chain's initial physical clock. -/
theorem finiteGPSExecutionSegmentsChainFrom_start_le_segment_startTime
    (startTime : ℝ) (startWorkload : Class → ℝ)
    (segments : List (FiniteGPSExecutionSegment Class))
    (hchain : FiniteGPSExecutionSegmentsChainFrom startTime startWorkload segments)
    (hduration_nonneg : ∀ segment ∈ segments, 0 ≤ segment.duration)
    (segment : FiniteGPSExecutionSegment Class) (hsegment : segment ∈ segments) :
    startTime ≤ segment.startTime := by
  induction segments generalizing startTime startWorkload segment with
  | nil =>
      simp at hsegment
  | cons head tail ih =>
      rcases hchain with ⟨hhead_start, _hhead_work, htail_chain⟩
      rcases List.mem_cons.mp hsegment with hhead | htail
      · subst segment
        exact hhead_start.symm.le
      · have hstart_le_head_end : startTime ≤ finiteGPSExecutionSegmentEndTime head := by
          change startTime ≤ head.startTime + head.duration
          rw [hhead_start]
          linarith [hduration_nonneg head (by simp)]
        have htail_duration_nonneg : ∀ later ∈ tail, 0 ≤ later.duration := by
          intro later hlater
          exact hduration_nonneg later (by simp [hlater])
        exact hstart_le_head_end.trans
          (ih (startTime := finiteGPSExecutionSegmentEndTime head)
            (startWorkload := head.endpointWorkload) htail_chain
            htail_duration_nonneg segment htail)

/-- Every completion in a compatible FCFS fold over a physical segment chain
is timestamped no earlier than the chain's initial clock.  Compatibility is
used only to obtain nonnegative pre-step residual work; timing comes from the
concrete segment chain and the stored class-rate fields. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_all_completionTime_ge_start_of_compatible
    (initial : FiniteGPSFCFSJobLedger Class JobId) (initialWorkload : Class → ℝ)
    (i : Class) (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (startTime : ℝ)
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible initial initialWorkload steps)
    (hchain : FiniteGPSExecutionSegmentsChainFrom startTime initialWorkload
      (steps.map fun step => step.segment))
    (hclassRate_nonneg : ∀ step ∈ steps, 0 ≤ step.segment.classRate i)
    (hduration_nonneg : ∀ step ∈ steps, 0 ≤ step.segment.duration) :
    ∀ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      startTime ≤ completion.completionTime := by
  intro completion hcompletion
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
      initial i steps completion hcompletion with
      ⟨before, step, after, hsplit, hstep_completion⟩
  have hcompatible_split : FiniteGPSFCFSRunSegmentStepsCompatible
      initial initialWorkload (before ++ step :: after) := by
    rw [← hsplit]
    exact hcompatible
  have hbefore_compatible := finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    initial initialWorkload before (step :: after) hcompatible_split
  have hbefore_nonneg :
      (finiteGPSFCFSRunSegmentSteps initial before).Nonnegative :=
    finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      initial initialWorkload before hinitial_nonneg hbefore_compatible
  have hstep_mem : step ∈ steps := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hstep_segment_mem : step.segment ∈ steps.map (fun later => later.segment) :=
    List.mem_map.mpr ⟨step, hstep_mem, rfl⟩
  have hsegment_duration_nonneg : ∀ segment ∈ steps.map
      (fun later => later.segment), 0 ≤ segment.duration := by
    intro segment hsegment
    rcases List.mem_map.mp hsegment with ⟨sourceStep, hsourceStep, rfl⟩
    exact hduration_nonneg sourceStep hsourceStep
  have hstart_le_step : startTime ≤ step.segment.startTime :=
    finiteGPSExecutionSegmentsChainFrom_start_le_segment_startTime
      startTime initialWorkload (steps.map fun later => later.segment)
      hchain hsegment_duration_nonneg step.segment hstep_segment_mem
  have hstep_completion_ge : step.segment.startTime ≤ completion.completionTime :=
    finiteGPSFCFSCompletedJobsInSegment_completionTime_ge_startTime_of_nonneg_rate_and_jobs
      step.segment i
      ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i)
      (hclassRate_nonneg step hstep_mem)
      (fun job hjob => hbefore_nonneg i job hjob)
      completion hstep_completion
  exact hstart_le_step.trans hstep_completion_ge

/-- A completion of an appended FCFS trace that occurs strictly before a cut
belongs to its left prefix whenever every right-suffix completion is at or
after that cut. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_mem_left_of_append_of_completionTime_lt
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (cut : ℝ) (completion : FiniteGPSFCFSCompletion JobId)
    (hright : ∀ later ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps initial left) i right,
      cut ≤ later.completionTime)
    (hcompletion : completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      initial i (left ++ right))
    (hcompletion_lt : completion.completionTime < cut) :
    completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i left := by
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append] at hcompletion
  rcases List.mem_append.mp hcompletion with hleft | hright_completion
  · exact hleft
  · exact False.elim ((not_le_of_gt hcompletion_lt) (hright completion hright_completion))

end

end AppliedModelingLib.Probability.Queueing
