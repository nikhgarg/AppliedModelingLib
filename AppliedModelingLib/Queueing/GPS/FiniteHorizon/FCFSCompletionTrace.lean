import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletion
import Mathlib.Tactic

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- Deterministically collect the completion records of one chosen class over
the actual finite FCFS segment-step fold.  At each step the records are built
from the current pre-step ledger and the concrete segment's stored service;
endpoint jobs enter only in the ledger used for later steps. -/
def finiteGPSFCFSRunSegmentStepsClassCompletions
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) →
      List (FiniteGPSFCFSCompletion JobId)
  | [] => []
  | step :: steps =>
      finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps

/-- A completion in the class-wise trace has provenance when it was emitted
from the pre-step queue of some concrete step in the supplied finite fold. -/
def FiniteGPSFCFSRunSegmentStepsClassCompletionProvenance
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (completion : FiniteGPSFCFSCompletion JobId) : Prop :=
  ∃ before step after,
    steps = before ++ (step :: after) ∧
      completion ∈ finiteGPSFCFSCompletedJobsInSegment step.segment i
        ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i)

/-- Every completion record from one segment retains the identifier and
arrival metadata of an actual job in that segment's pre-step FCFS queue. -/
theorem finiteGPSFCFSCompletedJobsFrom_has_source_job
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (completion : FiniteGPSFCFSCompletion JobId)
    (hcompletion : completion ∈ finiteGPSFCFSCompletedJobsFrom
      segmentStart classRate serviceBefore availableService jobs) :
    ∃ job ∈ jobs,
      completion.identifier = job.identifier ∧ completion.arrivalTime = job.arrivalTime := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom] at hcompletion
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · simp [finiteGPSFCFSCompletedJobsFrom, hpartial] at hcompletion
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService job jobs hpartial] at hcompletion
        rcases List.mem_cons.mp hcompletion with hhead | htail
        · subst completion
          exact ⟨job, by simp, rfl, rfl⟩
        · rcases ih (serviceBefore := serviceBefore + job.residualWork)
            (availableService := availableService - job.residualWork) htail with
            ⟨sourceJob, hsourceJob, hidentifier, harrival⟩
          exact ⟨sourceJob, by simp [hsourceJob], hidentifier, harrival⟩

/-- The concrete segment wrapper inherits source-job metadata provenance. -/
theorem finiteGPSFCFSCompletedJobsInSegment_has_source_job
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (completion : FiniteGPSFCFSCompletion JobId)
    (hcompletion : completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs) :
    ∃ job ∈ jobs,
      completion.identifier = job.identifier ∧ completion.arrivalTime = job.arrivalTime := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_has_source_job (JobId := JobId)
      segment.startTime (segment.classRate i) 0 (segment.serviceIncrement i)
      jobs completion hcompletion)

/-- The finite FCFS fold itself composes at a list boundary by restarting from
the computed prefix ledger. -/
theorem finiteGPSFCFSRunSegmentSteps_append
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSRunSegmentSteps initial (left ++ right) =
      finiteGPSFCFSRunSegmentSteps
        (finiteGPSFCFSRunSegmentSteps initial left) right := by
  induction left generalizing initial with
  | nil =>
      simp [finiteGPSFCFSRunSegmentSteps]
  | cons step left ih =>
      simp only [List.cons_append, finiteGPSFCFSRunSegmentSteps]
      exact ih (initial :=
        finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)

/-- At the first step, completion records are generated from the actual
pre-step queue.  The endpoint jobs occur only in the recursive post-endpoint
ledger, so none is processed in this preceding segment. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_cons
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (step : FiniteGPSFCFSSegmentJobStep Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i (step :: steps) =
      finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps := rfl

/-- The class-wise completion trace composes at a finite step-list boundary.
The right trace starts from the actual ledger computed by the left fold. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_append
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i (left ++ right) =
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i left ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps initial left) i right := by
  induction left generalizing initial with
  | nil =>
      simp [finiteGPSFCFSRunSegmentStepsClassCompletions,
        finiteGPSFCFSRunSegmentSteps]
  | cons step left ih =>
      simp only [List.cons_append, finiteGPSFCFSRunSegmentStepsClassCompletions,
        finiteGPSFCFSRunSegmentSteps]
      rw [ih]
      simp only [List.append_assoc]

/-- Every record in the finite class-wise completion trace is emitted by one
of the supplied concrete steps from that step's actual pre-step FCFS queue. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (completion : FiniteGPSFCFSCompletion JobId)
    (hcompletion : completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps) :
    FiniteGPSFCFSRunSegmentStepsClassCompletionProvenance
      initial i steps completion := by
  induction steps generalizing initial with
  | nil =>
      simp [finiteGPSFCFSRunSegmentStepsClassCompletions] at hcompletion
  | cons step steps ih =>
      change completion ∈
        finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i) ++
          finiteGPSFCFSRunSegmentStepsClassCompletions
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps at hcompletion
      rcases List.mem_append.mp hcompletion with hhead | htail
      · refine ⟨[], step, steps, by simp, ?_⟩
        exact hhead
      · rcases ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) htail with
          ⟨before, laterStep, after, hsplit, hsource⟩
        refine ⟨step :: before, laterStep, after, ?_, ?_⟩
        · simp [hsplit]
        · simpa [finiteGPSFCFSRunSegmentSteps] using hsource

/-- The per-step completion list in every provenance witness is an ordered
head prefix of the actual pre-step FCFS queue. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_has_preStep_head_order
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (completion : FiniteGPSFCFSCompletion JobId)
    (hcompletion : completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps) :
    ∃ before step after,
      steps = before ++ (step :: after) ∧
        completion ∈ finiteGPSFCFSCompletedJobsInSegment step.segment i
          ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i) ∧
        FiniteGPSFCFSCompletionHeadOrder
          (finiteGPSFCFSCompletedJobsInSegment step.segment i
            ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i))
          ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i) := by
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_has_provenance
    initial i steps completion hcompletion with
    ⟨before, step, after, hsplit, hsource⟩
  exact ⟨before, step, after, hsplit, hsource,
    finiteGPSFCFSCompletedJobsInSegment_head_order step.segment i
      ((finiteGPSFCFSRunSegmentSteps initial before).residualJobs i)⟩

/-- A nonnegative FCFS queue containing a positive-residual job has strictly
positive aggregate queued work. -/
theorem finiteGPSFCFSJobWork_pos_of_mem_pos
    (jobs : List (FiniteGPSFCFSJob JobId)) (job : FiniteGPSFCFSJob JobId)
    (hjob : job ∈ jobs) (hjob_pos : 0 < job.residualWork)
    (hjobs_nonneg : ∀ other ∈ jobs, 0 ≤ other.residualWork) :
    0 < finiteGPSFCFSJobWork jobs := by
  induction jobs generalizing job with
  | nil =>
      simp at hjob
  | cons head tail ih =>
      rw [finiteGPSFCFSJobWork_cons]
      rcases List.mem_cons.mp hjob with hhead | htail
      · subst job
        have htail_nonneg : 0 ≤ finiteGPSFCFSJobWork tail := by
          unfold finiteGPSFCFSJobWork
          apply List.sum_nonneg
          intro residual hresidual
          rcases List.mem_map.mp hresidual with ⟨other, hother, rfl⟩
          exact hjobs_nonneg other (by simp [hother])
        exact add_pos_of_pos_of_nonneg hjob_pos htail_nonneg
      · have hhead_nonneg : 0 ≤ head.residualWork :=
          hjobs_nonneg head (by simp)
        have htail_pos : 0 < finiteGPSFCFSJobWork tail :=
          ih job htail hjob_pos (fun other hother =>
            hjobs_nonneg other (by simp [hother]))
        exact add_pos_of_nonneg_of_pos hhead_nonneg htail_pos

/-- A positive pre-segment FCFS job is either recorded as a completion in
that segment or survives in the consumed residual queue with its identifier,
arrival metadata, and positive residual work intact. -/
private theorem finiteGPSFCFSConsume_completion_or_residual_of_mem_positive
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) (job : FiniteGPSFCFSJob JobId)
    (hjob : job ∈ jobs) (hjob_pos : 0 < job.residualWork) :
    (∃ completion ∈ finiteGPSFCFSCompletedJobsFrom segmentStart classRate
        serviceBefore availableService jobs,
        completion.identifier = job.identifier ∧
          completion.arrivalTime = job.arrivalTime) ∨
      ∃ residual ∈ finiteGPSFCFSConsume availableService jobs,
        residual.identifier = job.identifier ∧
          residual.arrivalTime = job.arrivalTime ∧ 0 < residual.residualWork := by
  induction jobs generalizing serviceBefore availableService job with
  | nil =>
      simp at hjob
  | cons head tail ih =>
      by_cases hpartial : availableService < head.residualWork
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_nil_of_partial_head
          segmentStart classRate serviceBefore availableService head tail hpartial]
        right
        rw [finiteGPSFCFSConsume_eq_partial_head
          availableService head tail hpartial]
        rcases List.mem_cons.mp hjob with hhead | htail
        · subst job
          refine ⟨{ head with residualWork := head.residualWork - availableService },
            by simp, rfl, rfl, ?_⟩
          exact sub_pos.mpr hpartial
        · exact ⟨job, by simp [htail], rfl, rfl, hjob_pos⟩
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
          segmentStart classRate serviceBefore availableService head tail hpartial,
          finiteGPSFCFSConsume_eq_after_complete_head
            availableService head tail hpartial]
        rcases List.mem_cons.mp hjob with hhead | htail
        · subst job
          left
          exact ⟨finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore head,
            by simp, rfl, rfl⟩
        · rcases ih
            (serviceBefore := serviceBefore + head.residualWork)
            (availableService := availableService - head.residualWork)
            (job := job) htail hjob_pos with hcompletion | hresidual
          · left
            rcases hcompletion with ⟨completion, hcompletion, hidentifier, harrival⟩
            exact ⟨completion, by simp [hcompletion], hidentifier, harrival⟩
          · right
            exact hresidual

/-- A positive job in the pre-segment queue is either completed in that
segment or remains queued with the same identifier and arrival metadata. -/
theorem finiteGPSFCFSCompletedJobsInSegment_completion_or_residual_of_mem_positive
    (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) (job : FiniteGPSFCFSJob JobId)
    (hjob : job ∈ jobs) (hjob_pos : 0 < job.residualWork) :
    (∃ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
        completion.identifier = job.identifier ∧
          completion.arrivalTime = job.arrivalTime) ∨
      ∃ residual ∈ finiteGPSFCFSConsume (segment.serviceIncrement i) jobs,
        residual.identifier = job.identifier ∧
          residual.arrivalTime = job.arrivalTime ∧ 0 < residual.residualWork := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSConsume_completion_or_residual_of_mem_positive
      (JobId := JobId) segment.startTime (segment.classRate i) 0
      (segment.serviceIncrement i) jobs job hjob hjob_pos)

/-- A positive job already present in a finite FCFS ledger either produces a
class completion record during the actual segment-step fold or remains in the
final residual queue with unchanged identifier and arrival metadata. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_or_residual_of_mem_positive
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (job : FiniteGPSFCFSJob JobId)
    (hjob : job ∈ initial.residualJobs i) (hjob_pos : 0 < job.residualWork) :
    (∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
        completion.identifier = job.identifier ∧
          completion.arrivalTime = job.arrivalTime) ∨
      ∃ residual ∈ (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i,
        residual.identifier = job.identifier ∧
          residual.arrivalTime = job.arrivalTime ∧ 0 < residual.residualWork := by
  induction steps generalizing initial job with
  | nil =>
      right
      exact ⟨job, by simpa [finiteGPSFCFSRunSegmentSteps], rfl, rfl, hjob_pos⟩
  | cons step steps ih =>
      change
        (∃ completion ∈
            finiteGPSFCFSCompletedJobsInSegment step.segment i
              (initial.residualJobs i) ++
              finiteGPSFCFSRunSegmentStepsClassCompletions
                (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps,
            completion.identifier = job.identifier ∧
              completion.arrivalTime = job.arrivalTime) ∨
          ∃ residual ∈ (finiteGPSFCFSRunSegmentSteps
              (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
              steps).residualJobs i,
            residual.identifier = job.identifier ∧
              residual.arrivalTime = job.arrivalTime ∧ 0 < residual.residualWork
      rcases finiteGPSFCFSCompletedJobsInSegment_completion_or_residual_of_mem_positive
          step.segment i (initial.residualJobs i) job hjob hjob_pos with
          hcompletion | hresidual
      · left
        rcases hcompletion with ⟨completion, hcompletion, hidentifier, harrival⟩
        exact ⟨completion, List.mem_append.mpr (Or.inl hcompletion),
          hidentifier, harrival⟩
      · rcases hresidual with
          ⟨residual, hresidual, hidentifier, harrival, hresidual_pos⟩
        have hresidual_next : residual ∈
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i := by
          simp only [finiteGPSFCFSApplySegment]
          exact List.mem_append.mpr (Or.inl hresidual)
        rcases ih
            (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
            (job := residual) hresidual_next hresidual_pos with
            hlater_completion | hlater_residual
        · left
          rcases hlater_completion with
            ⟨completion, hcompletion, hlater_identifier, hlater_arrival⟩
          exact ⟨completion, List.mem_append.mpr (Or.inr hcompletion),
            hlater_identifier.trans hidentifier,
            hlater_arrival.trans harrival⟩
        · right
          rcases hlater_residual with
            ⟨finalResidual, hfinalResidual, hlater_identifier, hlater_arrival,
              hfinalResidual_pos⟩
          exact ⟨finalResidual, hfinalResidual,
            hlater_identifier.trans hidentifier,
            hlater_arrival.trans harrival, hfinalResidual_pos⟩

/-- A literal FCFS job is admitted in the actual finite endpoint-batch trace
when it occurs in the endpoint jobs of one concrete step in that supplied
segment-step list. -/
def FiniteGPSFCFSEndpointJobAdmission
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (i : Class) (job : FiniteGPSFCFSJob JobId) : Prop :=
  ∃ before step after,
    steps = before ++ (step :: after) ∧ job ∈ step.endpointJobs.jobs i

/-- Membership in a concrete step's endpoint batch gives the corresponding
literal endpoint-admission witness for the actual finite step list. -/
theorem finiteGPSFCFSEndpointJobAdmission_of_mem_step
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (step : FiniteGPSFCFSSegmentJobStep Class JobId)
    (i : Class) (job : FiniteGPSFCFSJob JobId)
    (hstep : step ∈ steps) (hjob : job ∈ step.endpointJobs.jobs i) :
    FiniteGPSFCFSEndpointJobAdmission steps i job := by
  induction steps generalizing step with
  | nil =>
      simp at hstep
  | cons head tail ih =>
      rcases List.mem_cons.mp hstep with hhead | htail
      · subst step
        exact ⟨[], head, tail, by simp, hjob⟩
      · rcases ih step htail hjob with ⟨before, selected, after, hsplit, hadmitted⟩
        exact ⟨head :: before, selected, after, by simp [hsplit], hadmitted⟩

/-- A positive endpoint-admitted job has a completion record whenever the
actual finite continuation ends with zero aggregate class work and the final
target-class queue is nonnegative.  That nonnegativity condition is essential:
aggregate zero alone could hide a positive residual job behind negative
work.
No identifier-uniqueness hypothesis is needed, because the conclusion tracks
the admitted job's identifier and arrival metadata directly. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_exists_of_endpointJobAdmission_and_finalClassWork_eq_zero
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (job : FiniteGPSFCFSJob JobId)
    (hadmission : FiniteGPSFCFSEndpointJobAdmission steps i job)
    (hjob_pos : 0 < job.residualWork)
    (hfinal_class_nonnegative : ∀ residual ∈
      (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i,
      0 ≤ residual.residualWork)
    (hfinal_classWork_zero :
      (finiteGPSFCFSRunSegmentSteps initial steps).classWork i = 0) :
    ∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      completion.identifier = job.identifier ∧ completion.arrivalTime = job.arrivalTime := by
  rcases hadmission with ⟨before, step, after, hsteps, hjob_admitted⟩
  subst steps
  let beforeLedger := finiteGPSFCFSRunSegmentSteps initial before
  let afterAdmissionLedger := finiteGPSFCFSApplySegment
    beforeLedger step.segment step.endpointJobs
  have hjob_after_admission : job ∈ afterAdmissionLedger.residualJobs i := by
    dsimp [afterAdmissionLedger]
    simp only [finiteGPSFCFSApplySegment]
    exact List.mem_append.mpr (Or.inr hjob_admitted)
  have hfinal_eq :
      finiteGPSFCFSRunSegmentSteps initial (before ++ step :: after) =
        finiteGPSFCFSRunSegmentSteps afterAdmissionLedger after := by
    rw [finiteGPSFCFSRunSegmentSteps_append]
    rfl
  have hfinal_class_nonnegative_after : ∀ residual ∈
      (finiteGPSFCFSRunSegmentSteps afterAdmissionLedger after).residualJobs i,
      0 ≤ residual.residualWork := by
    intro residual hresidual
    apply hfinal_class_nonnegative residual
    rw [hfinal_eq]
    exact hresidual
  have hfinal_classWork_zero_after :
      (finiteGPSFCFSRunSegmentSteps afterAdmissionLedger after).classWork i = 0 := by
    rw [← hfinal_eq]
    exact hfinal_classWork_zero
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_or_residual_of_mem_positive
      afterAdmissionLedger i after job hjob_after_admission hjob_pos with
      hcompletion | hresidual
  · rcases hcompletion with ⟨completion, hcompletion, hidentifier, harrival⟩
    refine ⟨completion, ?_, hidentifier, harrival⟩
    have htrace_eq :
        finiteGPSFCFSRunSegmentStepsClassCompletions initial i
            (before ++ step :: after) =
          finiteGPSFCFSRunSegmentStepsClassCompletions initial i before ++
            (finiteGPSFCFSCompletedJobsInSegment step.segment i
              (beforeLedger.residualJobs i) ++
              finiteGPSFCFSRunSegmentStepsClassCompletions
                afterAdmissionLedger i after) := by
      rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append]
      rfl
    rw [htrace_eq]
    exact List.mem_append.mpr (Or.inr
      (List.mem_append.mpr (Or.inr hcompletion)))
  · rcases hresidual with
      ⟨residual, hresidual, _hidentifier, _harrival, hresidual_pos⟩
    have hwork_pos : 0 <
        (finiteGPSFCFSRunSegmentSteps afterAdmissionLedger after).classWork i := by
      simpa [FiniteGPSFCFSJobLedger.classWork] using
        (finiteGPSFCFSJobWork_pos_of_mem_pos
          ((finiteGPSFCFSRunSegmentSteps afterAdmissionLedger after).residualJobs i)
          residual hresidual hresidual_pos
          hfinal_class_nonnegative_after)
    linarith

end

end AppliedModelingLib.Probability.Queueing
