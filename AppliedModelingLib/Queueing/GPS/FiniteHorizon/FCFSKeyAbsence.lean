import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFrontWorkOrder
import Mathlib.Tactic

/-!
# Key absence in finite FCFS traces

Finite FCFS service can reduce or remove jobs, but cannot create a source
identifier.  This deterministic module records that fact for a distinguished
key, including the exact service-before-endpoint front-work corollary used by
literal tagged-arrival arguments.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- A finite endpoint trace with a keyed job has a first endpoint step carrying
such a job.  Every earlier literal endpoint batch is key-free.  This is a
pure list fact, so downstream source arguments do not need identifier
uniqueness merely to establish key absence in the pre-admission ledger. -/
theorem finiteGPSFCFSSegmentJobSteps_exists_first_endpoint_key
    (key : JobId → Bool)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) (i : Class)
    (hexists : ∃ step ∈ steps, ∃ job ∈ step.endpointJobs.jobs i,
      key job.identifier = true) :
    ∃ before admission after job,
      steps = before ++ admission :: after ∧
        job ∈ admission.endpointJobs.jobs i ∧
        key job.identifier = true ∧
        ∀ earlierStep ∈ before, ∀ earlierJob ∈ earlierStep.endpointJobs.jobs i,
          key earlierJob.identifier ≠ true := by
  induction steps with
  | nil =>
      simp at hexists
  | cons head tail ih =>
      by_cases hhead : ∃ job ∈ head.endpointJobs.jobs i, key job.identifier = true
      · rcases hhead with ⟨job, hjob, hkey⟩
        exact ⟨[], head, tail, job, by simp, hjob, hkey, by simp⟩
      · have htail : ∃ step ∈ tail, ∃ job ∈ step.endpointJobs.jobs i,
            key job.identifier = true := by
          rcases hexists with ⟨step, hstep, job, hjob, hkey⟩
          rcases List.mem_cons.mp hstep with hstep | hstep
          · subst step
            exact False.elim (hhead ⟨job, hjob, hkey⟩)
          · exact ⟨step, hstep, job, hjob, hkey⟩
        rcases ih htail with
          ⟨before, admission, after, job, hsplit, hjob, hkey, hbefore⟩
        refine ⟨head :: before, admission, after, job, ?_, hjob, hkey, ?_⟩
        · simp [hsplit]
        · intro earlierStep hearlierStep earlierJob hearlierJob
          rcases List.mem_cons.mp hearlierStep with hearlierStep | hearlierStep
          · subst earlierStep
            intro hcontra
            exact hhead ⟨earlierJob, hearlierJob, hcontra⟩
          · exact hbefore earlierStep hearlierStep earlierJob hearlierJob

/-- FCFS consumption cannot introduce a job whose identifier satisfies a key. -/
theorem finiteGPSFCFSConsume_forall_not_key
    (key : JobId → Bool) (availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hjobs : ∀ job ∈ jobs, key job.identifier ≠ true) :
    ∀ job ∈ finiteGPSFCFSConsume availableService jobs,
      key job.identifier ≠ true := by
  induction jobs generalizing availableService with
  | nil =>
      simp [finiteGPSFCFSConsume]
  | cons head tail ih =>
      by_cases hpartial : availableService < head.residualWork
      · rw [finiteGPSFCFSConsume_eq_partial_head availableService head tail hpartial]
        intro job hjob
        rcases List.mem_cons.mp hjob with hhead | htail
        · subst job
          simpa using hjobs head (by simp)
        · exact hjobs job (by simp [htail])
      · rw [finiteGPSFCFSConsume_eq_after_complete_head
          availableService head tail hpartial]
        apply ih
        intro job hjob
        exact hjobs job (by simp [hjob])

/-- Applying one source endpoint preserves absence of a key when both the
pre-segment ledger and that literal endpoint batch lack the key. -/
theorem finiteGPSFCFSApplySegment_forall_not_key
    (key : JobId → Bool)
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (i : Class)
    (hledger : ∀ job ∈ ledger.residualJobs i, key job.identifier ≠ true)
    (hendpoint : ∀ job ∈ endpointJobs.jobs i, key job.identifier ≠ true) :
    ∀ job ∈ (finiteGPSFCFSApplySegment ledger segment endpointJobs).residualJobs i,
      key job.identifier ≠ true := by
  intro job hjob
  simp only [finiteGPSFCFSApplySegment] at hjob
  rcases List.mem_append.mp hjob with hserved | hendpoint_job
  · exact finiteGPSFCFSConsume_forall_not_key key (segment.serviceIncrement i)
      (ledger.residualJobs i) hledger job hserved
  · exact hendpoint job hendpoint_job

/-- Folding a finite FCFS trace cannot introduce a keyed job when neither the
initial ledger nor any actual endpoint batch contains it. -/
theorem finiteGPSFCFSRunSegmentSteps_forall_not_key
    (key : JobId → Bool)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) (i : Class)
    (hinitial : ∀ job ∈ initial.residualJobs i, key job.identifier ≠ true)
    (hendpoint : ∀ step ∈ steps, ∀ job ∈ step.endpointJobs.jobs i,
      key job.identifier ≠ true) :
    ∀ job ∈ (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i,
      key job.identifier ≠ true := by
  induction steps generalizing initial with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial
  | cons step steps ih =>
      apply ih
      · exact finiteGPSFCFSApplySegment_forall_not_key key initial step.segment
          step.endpointJobs i hinitial
          (fun job hjob => hendpoint step (by simp) job hjob)
      · intro later hlater job hjob
        exact hendpoint later (by simp [hlater]) job hjob

/-- If neither the initial FCFS ledger nor any endpoint batch contains a
Boolean-keyed source job, the corresponding finite completion trace cannot
emit one.  This follows from actual per-segment job provenance and is useful
whenever a source endpoint separates a before-tag trace from a post-tag
trace. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_forall_not_key
    (key : JobId → Bool)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) (i : Class)
    (hinitial : ∀ job ∈ initial.residualJobs i, key job.identifier ≠ true)
    (hendpoint : ∀ step ∈ steps, ∀ job ∈ step.endpointJobs.jobs i,
      key job.identifier ≠ true) :
    ∀ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier ≠ true := by
  induction steps generalizing initial with
  | nil =>
      simp [finiteGPSFCFSRunSegmentStepsClassCompletions]
  | cons step steps ih =>
      intro completion hcompletion
      change completion ∈ finiteGPSFCFSCompletedJobsInSegment step.segment i
          (initial.residualJobs i) ++
          finiteGPSFCFSRunSegmentStepsClassCompletions
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps at hcompletion
      rcases List.mem_append.mp hcompletion with hhead | htail
      · rcases finiteGPSFCFSCompletedJobsInSegment_has_source_job
          step.segment i (initial.residualJobs i) completion hhead with
          ⟨sourceJob, hsourceJob, hidentifier, _harrival⟩
        rw [hidentifier]
        exact hinitial sourceJob hsourceJob
      · apply ih
        · exact finiteGPSFCFSApplySegment_forall_not_key key initial step.segment
            step.endpointJobs i hinitial
            (fun job hjob => hendpoint step (by simp) job hjob)
        · intro later hlater job hjob
          exact hendpoint later (by simp [hlater]) job hjob
        · exact htail

/-- The service-before-endpoint front-work identity needs only key absence in
the pre-segment ledger: consumption preserves that absence automatically.
This is an exact finite FCFS identity, not a queueing or source-model
assumption. -/
theorem finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq_of_ledger_no_key
    (key : JobId → Bool) (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (i : Class) (job : FiniteGPSFCFSJob JobId)
    (hledger_no_key : ∀ earlier ∈ ledger.residualJobs i,
      key earlier.identifier ≠ true)
    (hendpoint : endpointJobs.jobs i = [job])
    (hjob_key : key job.identifier = true) :
    finiteGPSFCFSFrontWork key
        ((finiteGPSFCFSApplySegment ledger segment endpointJobs).residualJobs i) =
      some
        (finiteGPSFCFSJobWork
          (finiteGPSFCFSConsume (segment.serviceIncrement i) (ledger.residualJobs i)) +
          job.residualWork) := by
  apply finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq
    key ledger segment endpointJobs i job hendpoint
  · exact finiteGPSFCFSConsume_forall_not_key key (segment.serviceIncrement i)
      (ledger.residualJobs i) hledger_no_key
  · exact hjob_key

end

end AppliedModelingLib.Probability.Queueing
