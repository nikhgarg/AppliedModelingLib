import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSRateFloor
import Mathlib.Tactic

/-!
# Finite tagged FCFS completion from prefix service

This module isolates the deterministic FCFS ordering fact needed to compare a
literal tagged job with a lower service process.  A key identifies the tagged
job in an ordered class queue.  `finiteGPSFCFSFrontWork` is the residual work
of every job before and including the first matching job.  Endpoint jobs are
always appended after service, so later source arrivals cannot increase that
front work before the tagged job completes.

The final theorem is intentionally finite and pathwise: if the actual stored
class service in a finite FCFS segment trace reaches the tagged job's initial
front work, then the concrete completion trace contains a matching
completion.  It allows arbitrary nonnegative endpoint batches at later
segments; it neither moves those arrivals to the beginning nor assumes that
the class has no later arrivals.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- Residual FCFS work through the first job whose identifier satisfies
`key`.  `none` means that no such job is currently queued. -/
def finiteGPSFCFSFrontWork
    (key : JobId → Bool) : List (FiniteGPSFCFSJob JobId) → Option ℝ
  | [] => none
  | job :: jobs =>
      if key job.identifier = true then
        some job.residualWork
      else
        (finiteGPSFCFSFrontWork key jobs).map
          (fun tailWork => job.residualWork + tailWork)

/-- A first matching FCFS job remains the first matching job after arbitrary
later jobs are appended at the tail. -/
theorem finiteGPSFCFSFrontWork_append_of_some
    (key : JobId → Bool) (left right : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hfront : finiteGPSFCFSFrontWork key left = some frontWork) :
    finiteGPSFCFSFrontWork key (left ++ right) = some frontWork := by
  induction left generalizing frontWork with
  | nil =>
      simp [finiteGPSFCFSFrontWork] at hfront
  | cons job left ih =>
      by_cases hkey : key job.identifier = true
      · simpa [finiteGPSFCFSFrontWork, hkey] using hfront
      · cases htail : finiteGPSFCFSFrontWork key left with
        | none =>
            simp [finiteGPSFCFSFrontWork, hkey, htail] at hfront
        | some tailWork =>
            have htail_append :
                finiteGPSFCFSFrontWork key (left ++ right) = some tailWork :=
              ih tailWork htail
            simp [finiteGPSFCFSFrontWork, hkey, htail, htail_append] at hfront ⊢
            exact hfront

/-- Nonnegative residual jobs give nonnegative work through any first
matching job. -/
theorem finiteGPSFCFSFrontWork_nonneg
    (key : JobId → Bool) (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork) :
    0 ≤ frontWork := by
  induction jobs generalizing frontWork with
  | nil =>
      simp [finiteGPSFCFSFrontWork] at hfront
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hkey : key job.identifier = true
      · have hfront_eq : frontWork = job.residualWork := by
          simpa [finiteGPSFCFSFrontWork, hkey] using hfront.symm
        simpa [hfront_eq] using hjob_nonneg
      · cases htail : finiteGPSFCFSFrontWork key jobs with
        | none =>
            simp [finiteGPSFCFSFrontWork, hkey, htail] at hfront
        | some tailWork =>
            have htail_nonneg : 0 ≤ tailWork :=
              ih tailWork hjobs_tail_nonneg htail
            simp [finiteGPSFCFSFrontWork, hkey, htail] at hfront
            linarith

/-- If the supplied nonnegative service stops before the first matching FCFS
job is fully consumed, the same first matching job remains queued and its
front work decreases by exactly that service. -/
theorem finiteGPSFCFSFrontWork_consume_eq_sub_of_service_lt
    (key : JobId → Bool) (availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork)
    (hservice_lt_frontWork : availableService < frontWork) :
    finiteGPSFCFSFrontWork key (finiteGPSFCFSConsume availableService jobs) =
      some (frontWork - availableService) := by
  induction jobs generalizing availableService frontWork with
  | nil =>
      simp [finiteGPSFCFSFrontWork] at hfront
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hkey : key job.identifier = true
      · have hfront_eq : frontWork = job.residualWork := by
          simpa [finiteGPSFCFSFrontWork, hkey] using hfront.symm
        have hpartial : availableService < job.residualWork := by
          linarith
        rw [finiteGPSFCFSConsume_eq_partial_head availableService job jobs hpartial]
        simp [finiteGPSFCFSFrontWork, hkey, hfront_eq]
      · cases htail : finiteGPSFCFSFrontWork key jobs with
        | none =>
            simp [finiteGPSFCFSFrontWork, hkey, htail] at hfront
        | some tailWork =>
            have hfront_eq : frontWork = job.residualWork + tailWork := by
              simpa [finiteGPSFCFSFrontWork, hkey, htail] using hfront.symm
            by_cases hpartial : availableService < job.residualWork
            · rw [finiteGPSFCFSConsume_eq_partial_head availableService job jobs hpartial]
              simp [finiteGPSFCFSFrontWork, hkey, htail]
              linarith
            · have hjob_le_service : job.residualWork ≤ availableService :=
                le_of_not_gt hpartial
              have hremaining_service_nonneg :
                  0 ≤ availableService - job.residualWork :=
                sub_nonneg.mpr hjob_le_service
              have hremaining_service_lt_tailWork :
                  availableService - job.residualWork < tailWork := by
                linarith
              have htail_after_consume := ih
                (availableService := availableService - job.residualWork)
                (frontWork := tailWork) hremaining_service_nonneg
                hjobs_tail_nonneg htail hremaining_service_lt_tailWork
              rw [finiteGPSFCFSConsume_eq_after_complete_head
                availableService job jobs hpartial]
              rw [htail_after_consume]
              congr 1
              linarith

/-- Once nonnegative service reaches the front work through a matching job,
the per-segment FCFS completion ledger contains a completed job with that
key.  This is the precise within-class ordering fact: later jobs are never
used to satisfy the bound. -/
theorem finiteGPSFCFSCompletedJobsFrom_exists_key_of_frontWork_le_service
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork)
    (hfront_le_service : frontWork ≤ availableService) :
    ∃ completion ∈ finiteGPSFCFSCompletedJobsFrom
      segmentStart classRate serviceBefore availableService jobs,
      key completion.identifier = true := by
  induction jobs generalizing serviceBefore availableService frontWork with
  | nil =>
      simp [finiteGPSFCFSFrontWork] at hfront
  | cons job jobs ih =>
      have hjob_nonneg : 0 ≤ job.residualWork := hjobs_nonneg job (by simp)
      have hjobs_tail_nonneg : ∀ later ∈ jobs, 0 ≤ later.residualWork := by
        intro later hlater
        exact hjobs_nonneg later (by simp [hlater])
      by_cases hkey : key job.identifier = true
      · have hfront_eq : frontWork = job.residualWork := by
          simpa [finiteGPSFCFSFrontWork, hkey] using hfront.symm
        have hcomplete : ¬ availableService < job.residualWork := by
          linarith
        refine ⟨finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job, ?_, ?_⟩
        · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segmentStart classRate serviceBefore availableService job jobs hcomplete]
          simp
        · simpa [finiteGPSFCFSCompletionOf] using hkey
      · cases htail : finiteGPSFCFSFrontWork key jobs with
        | none =>
            simp [finiteGPSFCFSFrontWork, hkey, htail] at hfront
        | some tailWork =>
            have hfront_eq : frontWork = job.residualWork + tailWork := by
              simpa [finiteGPSFCFSFrontWork, hkey, htail] using hfront.symm
            have htail_nonneg : 0 ≤ tailWork :=
              finiteGPSFCFSFrontWork_nonneg key jobs tailWork hjobs_tail_nonneg htail
            have hcomplete_head : ¬ availableService < job.residualWork := by
              intro hpartial
              linarith
            have hremaining_service_nonneg :
                0 ≤ availableService - job.residualWork :=
              sub_nonneg.mpr (le_of_not_gt hcomplete_head)
            have htail_le_remaining_service :
                tailWork ≤ availableService - job.residualWork := by
              linarith
            rcases ih
                (serviceBefore := serviceBefore + job.residualWork)
                (availableService := availableService - job.residualWork)
                (frontWork := tailWork)
                hremaining_service_nonneg hjobs_tail_nonneg htail
                htail_le_remaining_service with
                ⟨completion, hcompletion, hcompletion_key⟩
            refine ⟨completion, ?_, hcompletion_key⟩
            rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
              segmentStart classRate serviceBefore availableService job jobs hcomplete_head]
            exact List.mem_cons.mpr (Or.inr hcompletion)

/-- Segment wrapper for the front-work completion criterion. -/
theorem finiteGPSFCFSCompletedJobsInSegment_exists_key_of_frontWork_le_service
    (key : JobId → Bool) (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hservice_nonneg : 0 ≤ segment.serviceIncrement i)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork)
    (hfront_le_service : frontWork ≤ segment.serviceIncrement i) :
    ∃ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      key completion.identifier = true := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_exists_key_of_frontWork_le_service
      key segment.startTime (segment.classRate i) 0 (segment.serviceIncrement i)
      jobs frontWork hservice_nonneg hjobs_nonneg hfront hfront_le_service)

/-- Over the actual finite FCFS fold, enough cumulative stored service to
cover the initial work through a keyed job forces a matching concrete
completion record.  Later endpoint jobs are allowed at every step and are
only appended after that step's service; the proof tracks the keyed front
work until the first segment that reaches it. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_totalService
    (key : JobId → Bool) (initial : FiniteGPSFCFSJobLedger Class JobId)
    (i : Class) (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (frontWork : ℝ)
    (hinitial_class_nonneg : ∀ job ∈ initial.residualJobs i, 0 ≤ job.residualWork)
    (hservice_nonneg : ∀ step ∈ steps, 0 ≤ step.segment.serviceIncrement i)
    (hendpoint_class_nonneg : ∀ step ∈ steps, ∀ job ∈ step.endpointJobs.jobs i,
      0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key (initial.residualJobs i) = some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_totalService :
      frontWork ≤ finiteGPSFCFSSegmentStepsTotalService steps i) :
    ∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier = true := by
  induction steps generalizing initial frontWork with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsTotalService] at hfront_le_totalService
      linarith
  | cons step steps ih =>
      have hhead_service_nonneg : 0 ≤ step.segment.serviceIncrement i :=
        hservice_nonneg step (by simp)
      have hhead_endpoint_nonneg : ∀ job ∈ step.endpointJobs.jobs i,
          0 ≤ job.residualWork := by
        intro job hjob
        exact hendpoint_class_nonneg step (by simp) job hjob
      have htail_service_nonneg : ∀ laterStep ∈ steps,
          0 ≤ laterStep.segment.serviceIncrement i := by
        intro laterStep hlaterStep
        exact hservice_nonneg laterStep (by simp [hlaterStep])
      have htail_endpoint_nonneg : ∀ laterStep ∈ steps,
          ∀ job ∈ laterStep.endpointJobs.jobs i, 0 ≤ job.residualWork := by
        intro laterStep hlaterStep job hjob
        exact hendpoint_class_nonneg laterStep (by simp [hlaterStep]) job hjob
      change frontWork ≤ step.segment.serviceIncrement i +
        finiteGPSFCFSSegmentStepsTotalService steps i at hfront_le_totalService
      by_cases hfront_reached : frontWork ≤ step.segment.serviceIncrement i
      · rcases finiteGPSFCFSCompletedJobsInSegment_exists_key_of_frontWork_le_service
          key step.segment i (initial.residualJobs i) frontWork
          hhead_service_nonneg hinitial_class_nonneg hfront hfront_reached with
          ⟨completion, hcompletion, hcompletion_key⟩
        refine ⟨completion, ?_, hcompletion_key⟩
        change completion ∈
          finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i) ++
            finiteGPSFCFSRunSegmentStepsClassCompletions
              (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps
        exact List.mem_append.mpr (Or.inl hcompletion)
      · have hservice_lt_frontWork :
            step.segment.serviceIncrement i < frontWork :=
          lt_of_not_ge hfront_reached
        have hfront_after_consume :
            finiteGPSFCFSFrontWork key
              (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
                (initial.residualJobs i)) =
              some (frontWork - step.segment.serviceIncrement i) :=
          finiteGPSFCFSFrontWork_consume_eq_sub_of_service_lt
            key (step.segment.serviceIncrement i) (initial.residualJobs i) frontWork
            hhead_service_nonneg hinitial_class_nonneg hfront hservice_lt_frontWork
        have hfront_next : finiteGPSFCFSFrontWork key
            ((finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i) =
              some (frontWork - step.segment.serviceIncrement i) := by
          change finiteGPSFCFSFrontWork key
              (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
                (initial.residualJobs i) ++ step.endpointJobs.jobs i) =
              some (frontWork - step.segment.serviceIncrement i)
          exact finiteGPSFCFSFrontWork_append_of_some key
            (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
              (initial.residualJobs i))
            (step.endpointJobs.jobs i)
            (frontWork - step.segment.serviceIncrement i) hfront_after_consume
        have hnext_class_nonneg : ∀ job ∈
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i,
            0 ≤ job.residualWork := by
          intro job hjob
          simp only [finiteGPSFCFSApplySegment] at hjob
          rcases List.mem_append.mp hjob with hserved | hendpoint
          · exact finiteGPSFCFSConsume_residualWork_nonneg
              (step.segment.serviceIncrement i) (initial.residualJobs i)
              hhead_service_nonneg hinitial_class_nonneg job hserved
          · exact hhead_endpoint_nonneg job hendpoint
        have hnext_front_pos :
            0 < frontWork - step.segment.serviceIncrement i :=
          sub_pos.mpr hservice_lt_frontWork
        have hnext_front_le_totalService :
            frontWork - step.segment.serviceIncrement i ≤
              finiteGPSFCFSSegmentStepsTotalService steps i := by
          linarith
        rcases ih
            (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
            (frontWork := frontWork - step.segment.serviceIncrement i)
            hnext_class_nonneg htail_service_nonneg htail_endpoint_nonneg hfront_next
            hnext_front_pos hnext_front_le_totalService with
            ⟨completion, hcompletion, hcompletion_key⟩
        refine ⟨completion, ?_, hcompletion_key⟩
        change completion ∈
          finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i) ++
            finiteGPSFCFSRunSegmentStepsClassCompletions
              (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps
        exact List.mem_append.mpr (Or.inr hcompletion)

/-- The finite GPS-to-FCFS tagged-job comparison.  Select an exact ordered
trace beginning after the literal tagged job's endpoint admission and ending
before its first possible empty-left-endpoint interval.  If that trace is
indeed backlogged for the chosen class, and the GPS guaranteed-rate floor
times its actual duration covers the tagged job's FCFS front work, the
executable completion trace contains the keyed job.  No work is moved to the
initial time and later endpoint arrivals remain appended behind the tagged
job in the actual fold. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration
    (key : JobId → Bool) (capacity : ℝ) (weight : Class → ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (i : Class) (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (frontWork : ℝ)
    (hinitial_class_nonneg : ∀ job ∈ initial.residualJobs i, 0 ≤ job.residualWork)
    (hservice_nonneg : ∀ step ∈ steps, 0 ≤ step.segment.serviceIncrement i)
    (hendpoint_class_nonneg : ∀ step ∈ steps, ∀ job ∈ step.endpointJobs.jobs i,
      0 ≤ job.residualWork)
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i)
    (hall_active : ∀ step ∈ steps, 0 < step.segment.startWorkload i)
    (hfront : finiteGPSFCFSFrontWork key (initial.residualJobs i) = some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration :
      frontWork ≤ capacity * weight i * finiteGPSFCFSSegmentStepsTotalDuration steps) :
    ∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier = true := by
  have hfloor_total :
      capacity * weight i * finiteGPSFCFSSegmentStepsTotalDuration steps ≤
        finiteGPSFCFSSegmentStepsTotalService steps i :=
    finiteGPSFCFSSegmentSteps_weightedCapacity_mul_totalDuration_le_totalService_of_all_active
      capacity weight i steps hsegment_floor hall_active
  exact finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_totalService
    key initial i steps frontWork hinitial_class_nonneg hservice_nonneg
    hendpoint_class_nonneg hfront hfront_pos
    (hfront_le_floor_duration.trans hfloor_total)

omit [Fintype Class] [DecidableEq Class] in
/-- The recursive compatibility certificate exposes the nonnegative service
and endpoint-job facts for every concrete step of its fixed FCFS fold.  This
is a finite trace property, not a source or stochastic assumption. -/
theorem finiteGPSFCFSRunSegmentStepsCompatible_all_steps_nonnegative
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class -> Real)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible
      initial initialWorkload steps) :
    (∀ step ∈ steps, ∀ i, 0 <= step.segment.serviceIncrement i) ∧
      ∀ step ∈ steps, step.endpointJobs.Nonnegative := by
  induction steps generalizing initial initialWorkload with
  | nil =>
      simp
  | cons step steps ih =>
      rcases hcompatible with ⟨_hledger_matches, _hwork_matches,
        _hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        _hservice_le, _hbalance, htail⟩
      rcases ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload) htail with
          ⟨htail_service, htail_endpoint⟩
      constructor
      · intro later hlater i
        rcases List.mem_cons.mp hlater with rfl | hlater_tail
        · exact hservice_nonneg i
        · exact htail_service later hlater_tail i
      · intro later hlater
        rcases List.mem_cons.mp hlater with rfl | hlater_tail
        · exact hendpoint_nonneg
        · exact htail_endpoint later hlater_tail

/-- If a positive keyed job begins in a compatible finite FCFS ledger and no
matching completion occurs in the trace, then its class is genuinely
backlogged at the left endpoint of every subsequent concrete segment.  The
statement follows the actual FCFS fold: later endpoint arrivals are appended
behind the keyed job and cannot make it disappear.

This is the reusable busy-prefix dichotomy.  It does not identify a source
job, choose a deadline, or construct a stationary queue. -/
theorem finiteGPSFCFSRunSegmentSteps_all_active_of_no_keyed_completion
    (key : JobId -> Bool)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class -> Real) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (job : FiniteGPSFCFSJob JobId)
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible
      initial initialWorkload steps)
    (hjob : job ∈ initial.residualJobs i)
    (hjob_pos : 0 < job.residualWork)
    (hjob_key : key job.identifier = true)
    (hno_completion : ∀ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier ≠ true) :
    ∀ step ∈ steps, 0 < step.segment.startWorkload i := by
  induction steps generalizing initial initialWorkload job with
  | nil =>
      simp
  | cons step steps ih =>
      rcases hcompatible with ⟨hledger_matches, hwork_matches,
        _hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        _hservice_le, _hbalance, htail⟩
      have hinitial_class_nonneg : ∀ prior ∈ initial.residualJobs i,
          0 <= prior.residualWork := by
        intro prior hprior
        exact hinitial_nonneg i prior hprior
      have hinitial_work_pos : 0 < initial.classWork i := by
        unfold FiniteGPSFCFSJobLedger.classWork
        exact finiteGPSFCFSJobWork_pos_of_mem_pos
          (initial.residualJobs i) job hjob hjob_pos hinitial_class_nonneg
      have hhead_active : 0 < step.segment.startWorkload i := by
        rw [← hwork_matches i, ← hledger_matches i]
        exact hinitial_work_pos
      have hnext_nonneg :
          (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative :=
        finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
          hinitial_nonneg hservice_nonneg hendpoint_nonneg
      have hno_head_completion : ∀ completion ∈
          finiteGPSFCFSCompletedJobsInSegment step.segment i (initial.residualJobs i),
          key completion.identifier ≠ true := by
        intro completion hcompletion hkey
        apply hno_completion completion
        · simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
          exact List.mem_append.mpr (Or.inl hcompletion)
        · exact hkey
      rcases finiteGPSFCFSCompletedJobsInSegment_completion_or_residual_of_mem_positive
          step.segment i (initial.residualJobs i) job hjob hjob_pos with
          hhead_completion | hresidual
      · rcases hhead_completion with
          ⟨completion, hcompletion, hidentifier, _harrival⟩
        have hkey : key completion.identifier = true := by
          rw [hidentifier]
          exact hjob_key
        exact False.elim (hno_head_completion completion hcompletion hkey)
      · rcases hresidual with
          ⟨nextJob, hnextJob_consumed, hnext_identifier, _hnext_arrival,
            hnext_pos⟩
        have hnext_mem : nextJob ∈
            (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i := by
          simp only [finiteGPSFCFSApplySegment]
          exact List.mem_append.mpr (Or.inl hnextJob_consumed)
        have hnext_key : key nextJob.identifier = true := by
          rw [hnext_identifier]
          exact hjob_key
        have hno_tail_completion : ∀ completion ∈
            finiteGPSFCFSRunSegmentStepsClassCompletions
              (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs) i steps,
            key completion.identifier ≠ true := by
          intro completion hcompletion hkey
          apply hno_completion completion
          · simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
            exact List.mem_append.mpr (Or.inr hcompletion)
          · exact hkey
        have htail_active := ih
          (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
          (initialWorkload := step.segment.endpointWorkload)
          (job := nextJob) hnext_nonneg htail hnext_mem hnext_pos hnext_key
          hno_tail_completion
        intro later hlater
        rcases List.mem_cons.mp hlater with rfl | hlater_tail
        · exact hhead_active
        · exact htail_active later hlater_tail

/-- A compatible finite FCFS trace automatically closes the usual
completion-by-rate-floor argument for a positive keyed job.  The caller no
longer has to supply a separate all-active `busy` list: if no keyed
completion existed, the preceding theorem would make every trace interval
active, and the existing rate-floor completion theorem yields a
contradiction.

The caller still supplies the actual post-admission trace, its semantic GPS
rate floor, and the front-work/deadline duration inequality.  Hence this is a
finite pathwise bridge, not a stationary/Palm response-time theorem. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration_of_compatible
    (key : JobId -> Bool) (capacity : Real) (weight : Class -> Real)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class -> Real) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (frontWork : Real) (job : FiniteGPSFCFSJob JobId)
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible
      initial initialWorkload steps)
    (hjob : job ∈ initial.residualJobs i)
    (hjob_pos : 0 < job.residualWork)
    (hjob_key : key job.identifier = true)
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i ->
        capacity * weight i * step.segment.duration <= step.segment.serviceIncrement i)
    (hfront : finiteGPSFCFSFrontWork key (initial.residualJobs i) = some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_floor_duration :
      frontWork <= capacity * weight i * finiteGPSFCFSSegmentStepsTotalDuration steps) :
    ∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier = true := by
  classical
  rcases finiteGPSFCFSRunSegmentStepsCompatible_all_steps_nonnegative
      initial initialWorkload steps hcompatible with
    ⟨hservice_nonneg, hendpoint_nonneg⟩
  by_cases hhas : ∃ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier = true
  · exact hhas
  · have hno_completion : ∀ completion ∈
        finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
        key completion.identifier ≠ true := by
      intro completion hcompletion hkey
      exact hhas ⟨completion, hcompletion, hkey⟩
    have hall_active := finiteGPSFCFSRunSegmentSteps_all_active_of_no_keyed_completion
      key initial initialWorkload i steps job hinitial_nonneg hcompatible hjob hjob_pos
      hjob_key hno_completion
    have hcompletion :=
      finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_of_frontWork_le_weightedCapacity_mul_totalDuration
        key capacity weight initial i steps frontWork
        (fun prior hprior => hinitial_nonneg i prior hprior)
        (fun step hstep => hservice_nonneg step hstep i)
        (fun step hstep endpoint hendpoint => hendpoint_nonneg step hstep i endpoint hendpoint)
        hsegment_floor hall_active hfront hfront_pos hfront_le_floor_duration
    exact False.elim (hhas hcompletion)

end

end AppliedModelingLib.Probability.Queueing
