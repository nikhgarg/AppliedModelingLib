import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSTaggedCompletion
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateComparison
import Mathlib.Tactic

/-!
# Deadline-sensitive finite FCFS completion

The basic finite FCFS front-work theorem establishes that enough stored
service completes a keyed job.  This module retains the physical time of that
completion.  In particular, when only a prefix of a concrete constant-rate
GPS segment is needed, the result is not weakened to the segment's later
right endpoint.

Everything here is deterministic and list-local.  It does not construct a
source process, insert an arrival endpoint, or make a stationary claim.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

private theorem finiteGPSFCFSCompletedJobsFrom_exists_key_of_frontWork_le_service_with_completionTime
    (key : JobId → Bool) (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hservice_nonneg : 0 ≤ availableService)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork)
    (hfront_le_service : frontWork ≤ availableService) :
    ∃ completion ∈ finiteGPSFCFSCompletedJobsFrom
      segmentStart classRate serviceBefore availableService jobs,
      key completion.identifier = true ∧
        completion.completionTime =
          segmentStart + (serviceBefore + frontWork) / classRate := by
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
        refine ⟨finiteGPSFCFSCompletionOf segmentStart classRate serviceBefore job, ?_, ?_, ?_⟩
        · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segmentStart classRate serviceBefore availableService job jobs hcomplete]
          simp
        · exact hkey
        · simp [finiteGPSFCFSCompletionOf, hfront_eq]
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
            rcases ih (serviceBefore := serviceBefore + job.residualWork)
                (availableService := availableService - job.residualWork)
                (frontWork := tailWork) hremaining_service_nonneg hjobs_tail_nonneg htail
                htail_le_remaining_service with
                ⟨completion, hcompletion, hcompletion_key, hcompletion_time⟩
            refine ⟨completion, ?_, hcompletion_key, ?_⟩
            · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
                segmentStart classRate serviceBefore availableService
                job jobs hcomplete_head]
              exact List.mem_cons.mpr (Or.inr hcompletion)
            · rw [hcompletion_time]
              rw [hfront_eq]
              ring

/-- If the FCFS front work through the first keyed job fits in a concrete
segment's stored service, the emitted keyed completion has exactly the
front-work completion time.  This is stronger than merely bounding it by the
segment endpoint and is the local fact needed to cut a physical deadline
through a segment without introducing a source batch there. -/
theorem finiteGPSFCFSCompletedJobsInSegment_exists_key_of_frontWork_le_service_with_completionTime
    (key : JobId → Bool) (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) (frontWork : ℝ)
    (hservice_nonneg : 0 ≤ segment.serviceIncrement i)
    (hjobs_nonneg : ∀ job ∈ jobs, 0 ≤ job.residualWork)
    (hfront : finiteGPSFCFSFrontWork key jobs = some frontWork)
    (hfront_le_service : frontWork ≤ segment.serviceIncrement i) :
    ∃ completion ∈ finiteGPSFCFSCompletedJobsInSegment segment i jobs,
      key completion.identifier = true ∧
        completion.completionTime =
          segment.startTime + frontWork / segment.classRate i := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_exists_key_of_frontWork_le_service_with_completionTime
      key segment.startTime (segment.classRate i) 0 (segment.serviceIncrement i)
      jobs frontWork hservice_nonneg hjobs_nonneg hfront hfront_le_service)

/-- A deadline-sensitive FCFS completion theorem for an already executable
finite segment trace.  It works directly on the longer trace, so a physical
deadline need not be represented by a source-arrival endpoint.  The chain
premise gives literal segment timing; the rate-floor premises are semantic
facts over stored fields.  Thus the theorem neither assumes a special source
event at the deadline nor infers a completion from aggregate workload alone.

The `job` argument keeps the persistence argument tied to one concrete
positive job while `key` may remain any semantic selector for that job. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_by_deadline_of_compatible
    (key : JobId → Bool) (rate : ℝ)
    (initial : FiniteGPSFCFSJobLedger Class JobId)
    (initialWorkload : Class → ℝ) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (job : FiniteGPSFCFSJob JobId) (frontWork startTime deadline : ℝ)
    (hinitial_nonneg : initial.Nonnegative)
    (hcompatible : FiniteGPSFCFSRunSegmentStepsCompatible
      initial initialWorkload steps)
    (hchain : FiniteGPSExecutionSegmentsChainFrom startTime initialWorkload
      (steps.map fun step => step.segment))
    (hstart_le_deadline : startTime ≤ deadline)
    (hdeadline_le_final : deadline ≤ finiteGPSExecutionSegmentsFinalTime startTime
      (steps.map fun step => step.segment))
    (hrate_pos : 0 < rate)
    (hclassRate_pos_of_active : ∀ step ∈ steps,
      0 < step.segment.startWorkload i → 0 < step.segment.classRate i)
    (hservice_eq_rate_mul_duration : ∀ step ∈ steps,
      step.segment.serviceIncrement i = step.segment.classRate i * step.segment.duration)
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i →
        rate * step.segment.duration ≤ step.segment.serviceIncrement i)
    (hjob : job ∈ initial.residualJobs i)
    (hjob_pos : 0 < job.residualWork)
    (hjob_key : key job.identifier = true)
    (hfront : finiteGPSFCFSFrontWork key (initial.residualJobs i) = some frontWork)
    (hfront_pos : 0 < frontWork)
    (hfront_le_deadline_floor : frontWork ≤ rate * (deadline - startTime)) :
    ∃ completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps,
      key completion.identifier = true ∧ completion.completionTime ≤ deadline := by
  induction steps generalizing initial initialWorkload job frontWork startTime with
  | nil =>
      have hdeadline_eq_start : deadline = startTime := by
        simpa [finiteGPSExecutionSegmentsFinalTime] using
          le_antisymm hdeadline_le_final hstart_le_deadline
      rw [hdeadline_eq_start] at hfront_le_deadline_floor
      norm_num at hfront_le_deadline_floor
      linarith
  | cons step steps ih =>
      rcases hcompatible with ⟨hledger_matches, hwork_matches,
        hbatch_compatible, hendpoint_nonneg, hservice_nonneg,
        hservice_le, hbalance, htail⟩
      change FiniteGPSExecutionSegmentsChainFrom startTime initialWorkload
        (step.segment :: steps.map (fun laterStep => laterStep.segment)) at hchain
      rcases hchain with ⟨hstep_start, hstep_work, htail_chain⟩
      have hinitial_class_nonneg : ∀ queued ∈ initial.residualJobs i,
          0 ≤ queued.residualWork := by
        intro queued hqueued
        exact hinitial_nonneg i queued hqueued
      have hinitial_class_pos : 0 < initial.classWork i := by
        exact finiteGPSFCFSJobWork_pos_of_mem_pos
          (initial.residualJobs i) job hjob hjob_pos hinitial_class_nonneg
      have hstep_active : 0 < step.segment.startWorkload i := by
        rw [← hwork_matches i, ← hledger_matches i]
        exact hinitial_class_pos
      have hstep_rate_pos : 0 < step.segment.classRate i :=
        hclassRate_pos_of_active step (by simp) hstep_active
      have hstep_service_eq : step.segment.serviceIncrement i =
          step.segment.classRate i * step.segment.duration :=
        hservice_eq_rate_mul_duration step (by simp)
      have hstep_floor : rate * step.segment.duration ≤
          step.segment.serviceIncrement i :=
        hsegment_floor step (by simp) hstep_active
      have hstep_end : finiteGPSExecutionSegmentEndTime step.segment =
          startTime + step.segment.duration := by
        unfold finiteGPSExecutionSegmentEndTime
        rw [hstep_start]
      by_cases hdeadline_in_head : deadline ≤ finiteGPSExecutionSegmentEndTime step.segment
      · have hdeadline_offset_nonneg : 0 ≤ deadline - startTime :=
          sub_nonneg.mpr hstart_le_deadline
        have hdeadline_offset_le_duration : deadline - startTime ≤ step.segment.duration := by
          rw [hstep_end] at hdeadline_in_head
          linarith
        have hdeadline_offset_pos : 0 < deadline - startTime := by
          nlinarith [hfront_le_deadline_floor]
        have hstep_duration_pos : 0 < step.segment.duration :=
          lt_of_lt_of_le hdeadline_offset_pos hdeadline_offset_le_duration
        have hstep_rate_floor : rate ≤ step.segment.classRate i := by
          rw [hstep_service_eq] at hstep_floor
          nlinarith
        have hfront_le_head_rate_deadline :
            frontWork ≤ step.segment.classRate i * (deadline - startTime) := by
          calc
            frontWork ≤ rate * (deadline - startTime) := hfront_le_deadline_floor
            _ ≤ step.segment.classRate i * (deadline - startTime) :=
              mul_le_mul_of_nonneg_right hstep_rate_floor hdeadline_offset_nonneg
        have hfront_le_head_service : frontWork ≤ step.segment.serviceIncrement i := by
          calc
            frontWork ≤ step.segment.classRate i * (deadline - startTime) :=
              hfront_le_head_rate_deadline
            _ ≤ step.segment.classRate i * step.segment.duration :=
              mul_le_mul_of_nonneg_left hdeadline_offset_le_duration hstep_rate_pos.le
            _ = step.segment.serviceIncrement i := hstep_service_eq.symm
        rcases finiteGPSFCFSCompletedJobsInSegment_exists_key_of_frontWork_le_service_with_completionTime
            key step.segment i (initial.residualJobs i) frontWork (hservice_nonneg i)
            hinitial_class_nonneg hfront hfront_le_head_service with
            ⟨completion, hcompletion, hcompletion_key, hcompletion_time⟩
        refine ⟨completion, ?_, hcompletion_key, ?_⟩
        · simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
          exact List.mem_append.mpr (Or.inl hcompletion)
        · rw [hcompletion_time]
          have hfront_time_le : frontWork / step.segment.classRate i ≤
              deadline - startTime := by
            apply (div_le_iff₀ hstep_rate_pos).2
            nlinarith [hfront_le_head_rate_deadline]
          rw [hstep_start]
          linarith
      · have hhead_end_lt_deadline : finiteGPSExecutionSegmentEndTime step.segment < deadline :=
          lt_of_not_ge hdeadline_in_head
        by_cases hfront_le_head_service : frontWork ≤ step.segment.serviceIncrement i
        · rcases finiteGPSFCFSCompletedJobsInSegment_exists_key_of_frontWork_le_service_with_completionTime
              key step.segment i (initial.residualJobs i) frontWork (hservice_nonneg i)
              hinitial_class_nonneg hfront hfront_le_head_service with
              ⟨completion, hcompletion, hcompletion_key, _hcompletion_time⟩
          refine ⟨completion, ?_, hcompletion_key, ?_⟩
          · simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
            exact List.mem_append.mpr (Or.inl hcompletion)
          · exact (finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime
              step.segment i (initial.residualJobs i) hstep_rate_pos hstep_service_eq
              completion hcompletion).trans hhead_end_lt_deadline.le
        · have hhead_service_lt_front : step.segment.serviceIncrement i < frontWork :=
            lt_of_not_ge hfront_le_head_service
          have hfront_after_consume : finiteGPSFCFSFrontWork key
              (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
                (initial.residualJobs i)) =
              some (frontWork - step.segment.serviceIncrement i) :=
            finiteGPSFCFSFrontWork_consume_eq_sub_of_service_lt
              key (step.segment.serviceIncrement i) (initial.residualJobs i) frontWork
              (hservice_nonneg i) hinitial_class_nonneg hfront hhead_service_lt_front
          have hfront_next : finiteGPSFCFSFrontWork key
              ((finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i) =
                some (frontWork - step.segment.serviceIncrement i) := by
            change finiteGPSFCFSFrontWork key
                (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
                  (initial.residualJobs i) ++ step.endpointJobs.jobs i) = _
            exact finiteGPSFCFSFrontWork_append_of_some key
              (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
                (initial.residualJobs i))
              (step.endpointJobs.jobs i)
              (frontWork - step.segment.serviceIncrement i) hfront_after_consume
          have hfront_next_pos : 0 < frontWork - step.segment.serviceIncrement i :=
            sub_pos.mpr hhead_service_lt_front
          have hnext_nonneg :
              (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).Nonnegative := by
            exact finiteGPSFCFSApplySegment_nonnegative initial step.segment step.endpointJobs
              hinitial_nonneg hservice_nonneg hendpoint_nonneg
          rcases finiteGPSFCFSCompletedJobsInSegment_completion_or_residual_of_mem_positive
              step.segment i (initial.residualJobs i) job hjob hjob_pos with
              ⟨headCompletion, hheadCompletion, hidentifier, _harrival⟩ |
              ⟨nextJob, hnextJobConsumed, hnext_identifier, _hnextArrival, hnextJob_pos⟩
          · have hhead_key : key headCompletion.identifier = true := by
              rw [hidentifier]
              exact hjob_key
            refine ⟨headCompletion, ?_, hhead_key, ?_⟩
            · simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
              exact List.mem_append.mpr (Or.inl hheadCompletion)
            · exact (finiteGPSFCFSCompletedJobsInSegment_completionTime_le_endTime
                step.segment i (initial.residualJobs i) hstep_rate_pos hstep_service_eq
                headCompletion hheadCompletion).trans hhead_end_lt_deadline.le
          · have hnext_mem : nextJob ∈
                (finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i := by
              simp only [finiteGPSFCFSApplySegment]
              exact List.mem_append.mpr (Or.inl hnextJobConsumed)
            have hnext_key : key nextJob.identifier = true := by
              rw [hnext_identifier]
              exact hjob_key
            have htail_deadline_le_final : deadline ≤
                finiteGPSExecutionSegmentsFinalTime
                  (finiteGPSExecutionSegmentEndTime step.segment)
                  (steps.map fun laterStep => laterStep.segment) := by
              simpa [finiteGPSExecutionSegmentsFinalTime] using hdeadline_le_final
            have htail_start_le_deadline :
                finiteGPSExecutionSegmentEndTime step.segment ≤ deadline :=
              hhead_end_lt_deadline.le
            have htail_front_le_deadline_floor :
                frontWork - step.segment.serviceIncrement i ≤
                  rate * (deadline - finiteGPSExecutionSegmentEndTime step.segment) := by
              rw [hstep_end]
              nlinarith [hfront_le_deadline_floor, hstep_floor]
            have htail_classRate_pos_of_active : ∀ laterStep ∈ steps,
                0 < laterStep.segment.startWorkload i →
                  0 < laterStep.segment.classRate i := by
              intro laterStep hlaterStep hactive
              exact hclassRate_pos_of_active laterStep (by simp [hlaterStep]) hactive
            have htail_service_eq : ∀ laterStep ∈ steps,
                laterStep.segment.serviceIncrement i =
                  laterStep.segment.classRate i * laterStep.segment.duration := by
              intro laterStep hlaterStep
              exact hservice_eq_rate_mul_duration laterStep (by simp [hlaterStep])
            have htail_floor : ∀ laterStep ∈ steps,
                0 < laterStep.segment.startWorkload i →
                  rate * laterStep.segment.duration ≤ laterStep.segment.serviceIncrement i := by
              intro laterStep hlaterStep hactive
              exact hsegment_floor laterStep (by simp [hlaterStep]) hactive
            rcases ih
                (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
                (initialWorkload := step.segment.endpointWorkload)
                (job := nextJob)
                (frontWork := frontWork - step.segment.serviceIncrement i)
                (startTime := finiteGPSExecutionSegmentEndTime step.segment)
                hnext_nonneg htail htail_chain htail_start_le_deadline
                htail_deadline_le_final htail_classRate_pos_of_active htail_service_eq
                htail_floor hnext_mem hnextJob_pos hnext_key hfront_next
                hfront_next_pos htail_front_le_deadline_floor with
                ⟨completion, hcompletion, hcompletion_key, hcompletion_time⟩
            refine ⟨completion, ?_, hcompletion_key, hcompletion_time⟩
            simp only [finiteGPSFCFSRunSegmentStepsClassCompletions]
            exact List.mem_append.mpr (Or.inr hcompletion)

end

end AppliedModelingLib.Probability.Queueing
