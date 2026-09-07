import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import Mathlib.Tactic

/-!
# Strict positivity for finite FCFS GPS ledgers

The finite FCFS executor removes a completed job rather than retaining a
zero-residual placeholder.  This module records the corresponding strict
positivity facts.  They are deterministic list facts: no stochastic input,
queue stability, or completion claim is assumed here.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- FCFS consumption preserves strictly positive residual work for every job
that remains in the queue. -/
theorem finiteGPSFCFSConsume_residualWork_pos
    (availableService : Real) (jobs : List (FiniteGPSFCFSJob JobId))
    (hjobs_pos : ∀ job ∈ jobs, 0 < job.residualWork) :
    ∀ job ∈ finiteGPSFCFSConsume availableService jobs, 0 < job.residualWork := by
  induction jobs generalizing availableService with
  | nil =>
      simp [finiteGPSFCFSConsume]
  | cons head tail ih =>
      by_cases hpartial : availableService < head.residualWork
      · intro job hjob
        rw [finiteGPSFCFSConsume_eq_partial_head availableService head tail hpartial] at hjob
        rcases List.mem_cons.mp hjob with hhead | htail
        · subst job
          change 0 < head.residualWork - availableService
          exact sub_pos.mpr hpartial
        · exact hjobs_pos job (by simp [htail])
      · rw [finiteGPSFCFSConsume_eq_after_complete_head
          availableService head tail hpartial]
        apply ih
        intro job hjob
        exact hjobs_pos job (by simp [hjob])

/-- Applying one concrete GPS segment preserves strict positivity of every
surviving or newly admitted FCFS job when the incoming ledger and endpoint
batch have that property. -/
theorem finiteGPSFCFSApplySegment_residualWork_pos
    (ledger : FiniteGPSFCFSJobLedger Class JobId)
    (segment : FiniteGPSExecutionSegment Class)
    (endpointJobs : FiniteGPSFCFSEndpointJobs Class JobId)
    (hledger_pos : ∀ i job, job ∈ ledger.residualJobs i → 0 < job.residualWork)
    (hendpoint_pos : ∀ i job, job ∈ endpointJobs.jobs i → 0 < job.residualWork) :
    ∀ i job, job ∈
      (finiteGPSFCFSApplySegment ledger segment endpointJobs).residualJobs i →
      0 < job.residualWork := by
  intro i job hjob
  simp only [finiteGPSFCFSApplySegment] at hjob
  rcases List.mem_append.mp hjob with hserved | hadmitted
  · exact finiteGPSFCFSConsume_residualWork_pos
      (segment.serviceIncrement i) (ledger.residualJobs i)
      (fun prior hprior => hledger_pos i prior hprior) job hserved
  · exact hendpoint_pos i job hadmitted

/-- A finite FCFS queue with strictly positive residual jobs has zero total
work exactly when it is empty. -/
theorem finiteGPSFCFSJobWork_eq_zero_iff_nil_of_residualWork_pos
    (jobs : List (FiniteGPSFCFSJob JobId))
    (hjobs_pos : ∀ job ∈ jobs, 0 < job.residualWork) :
    finiteGPSFCFSJobWork jobs = 0 <-> jobs = [] := by
  constructor
  · intro hzero
    cases jobs with
    | nil => rfl
    | cons head tail =>
        have hhead_pos : 0 < head.residualWork := hjobs_pos head (by simp)
        have htail_nonneg : ∀ job ∈ tail, 0 ≤ job.residualWork := by
          intro job hjob
          exact (hjobs_pos job (by simp [hjob])).le
        have hwork_pos : 0 < finiteGPSFCFSJobWork (head :: tail) :=
          finiteGPSFCFSJobWork_pos_of_mem_pos (head :: tail) head (by simp)
            hhead_pos (by
              intro job hjob
              rcases List.mem_cons.mp hjob with rfl | htail
              · exact hhead_pos.le
              · exact htail_nonneg job htail)
        linarith
  · intro hnil
    simp [hnil]

/-- Strictly positive source jobs remain strictly positive through every
finite FCFS segment fold, provided every endpoint batch has strictly positive
jobs. -/
theorem finiteGPSFCFSRunSegmentSteps_residualWork_pos
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (hendpoint_pos : ∀ step ∈ steps, ∀ i job,
      job ∈ step.endpointJobs.jobs i → 0 < job.residualWork) :
    ∀ i job, job ∈
      (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i →
      0 < job.residualWork := by
  induction steps generalizing initial with
  | nil =>
      simpa [finiteGPSFCFSRunSegmentSteps] using hinitial_pos
  | cons step tail ih =>
      have hstep_pos : ∀ i job, job ∈ step.endpointJobs.jobs i →
          0 < job.residualWork := by
        intro i job hjob
        exact hendpoint_pos step (by simp) i job hjob
      have hnext_pos : ∀ i job, job ∈
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i →
          0 < job.residualWork :=
        finiteGPSFCFSApplySegment_residualWork_pos initial step.segment step.endpointJobs
          hinitial_pos hstep_pos
      have htail_pos : ∀ later ∈ tail, ∀ i job,
          job ∈ later.endpointJobs.jobs i → 0 < job.residualWork := by
        intro later hlater i job hjob
        exact hendpoint_pos later (by simp [hlater]) i job hjob
      simpa [finiteGPSFCFSRunSegmentSteps] using ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
        hnext_pos htail_pos

/-- At a finite fold whose source jobs are all strictly positive, zero final
class work means that class's residual FCFS ledger is literally empty. -/
theorem finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_classWork_eq_zero_of_pos
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (hendpoint_pos : ∀ step ∈ steps, ∀ i job,
      job ∈ step.endpointJobs.jobs i → 0 < job.residualWork)
    (i : Class)
    (hclass_work_zero :
      (finiteGPSFCFSRunSegmentSteps initial steps).classWork i = 0) :
    (finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i = [] := by
  apply (finiteGPSFCFSJobWork_eq_zero_iff_nil_of_residualWork_pos
    ((finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i) ?_).mp
  · exact hclass_work_zero
  · exact finiteGPSFCFSRunSegmentSteps_residualWork_pos initial steps
      hinitial_pos hendpoint_pos i

end

end AppliedModelingLib.Probability.Queueing
