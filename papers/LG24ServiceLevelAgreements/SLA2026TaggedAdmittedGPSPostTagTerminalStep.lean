import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonTerminalBatch
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSFrontWork
import Mathlib.Tactic

/-!
# Literal terminal source steps for the tagged GPS trace

This adapter exposes the final annotated FCFS step of a bounded source gap
when the executable GPS runner reaches its real external endpoint.  The step
is a source step: its endpoint jobs are the literal jobs at the requested
physical batch time.  It is not the computational zero-work fence.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The source-annotated recursion has the same literal restart law as the
aggregate GPS runner.  It is public because reset arguments must distinguish
this exact physical-source split from a separate refinement that inserts a
computational zero-work fence. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (leftTimes rightTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (leftTimes ++ rightTimes))
    (hbatch_nonneg : ∀ eventTime ∈ leftTimes ++ rightTimes, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work
        (leftTimes ++ rightTimes) =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work leftTimes ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            currentTime work leftTimes).currentTime
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            currentTime work leftTimes).workload
          rightTimes := by
  induction leftTimes generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
        finiteGPSRunBatchTrace]
  | cons eventTime leftTimes ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ k,
          0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
        intro k
        exact hbatch_nonneg eventTime (by simp) k
      have hbatch_tail : ∀ laterTime ∈ leftTimes ++ rightTimes, ∀ k,
          0 ≤ taggedAdmittedBatchAt start horizon target z laterTime k := by
        intro laterTime hlaterTime k
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) k
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true := by
        exact (finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)).1
      have hgap_nonneg : ∀ k, 0 ≤ gap.workload k := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih (currentTime := eventTime) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      have hgap_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            (eventTime - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates
      change taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work
          (eventTime :: (leftTimes ++ rightTimes)) =
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight currentTime work
            (eventTime :: leftTimes) ++
          taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight
            (finiteGPSRunBatchTrace capacity weight
              (taggedAdmittedBatchAt start horizon target z)
              currentTime work (eventTime :: leftTimes)).currentTime
            (finiteGPSRunBatchTrace capacity weight
              (taggedAdmittedBatchAt start horizon target z)
              currentTime work (eventTime :: leftTimes)).workload
            rightTimes
      rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon target z capacity weight work currentTime eventTime
        (leftTimes ++ rightTimes) hgap_applied]
      rw [htail]
      rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon target z capacity weight work currentTime eventTime
        leftTimes hgap_applied]
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied
        capacity weight (taggedAdmittedBatchAt start horizon target z)
        currentTime work eventTime leftTimes hgap_applied]
      simp [gap, List.append_assoc]

/-- Appending a known final physical epoch preserves chronological order when
every existing source epoch is no later than it. -/
private theorem finiteGPSChronologicalFrom_append_singleton_of_forall_le
    (start endpoint : ℝ) (times : List ℝ)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_endpoint : start ≤ endpoint)
    (htimes_endpoint : ∀ eventTime ∈ times, eventTime ≤ endpoint) :
    FiniteGPSChronologicalFrom start (times ++ [endpoint]) := by
  induction times generalizing start with
  | nil =>
      simpa [FiniteGPSChronologicalFrom] using hstart_endpoint
  | cons eventTime times ih =>
      rcases hchronological with ⟨hstart_eventTime, htail⟩
      refine ⟨hstart_eventTime, ?_⟩
      apply ih eventTime htail
      · exact htimes_endpoint eventTime (by simp)
      · intro laterTime hlaterTime
        exact htimes_endpoint laterTime (by simp [hlaterTime])

omit [Fintype Category] [DecidableEq Category] in
/-- The endpoint workload of a nonempty annotated trace is the endpoint
workload stored by its final step. -/
private theorem finiteGPSFCFSSegmentStepsEndpointWorkload_append_singleton
    (initialWorkload : Category → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (terminal : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload
      (steps ++ [terminal]) = terminal.segment.endpointWorkload := by
  induction steps generalizing initialWorkload with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload]
  | cons step steps ih =>
      simp [finiteGPSFCFSSegmentStepsEndpointWorkload, ih]

/-- If the executable bounded GPS gap reaches its literal source epoch, the
source-annotated FCFS gap has a final external step at that same epoch.  Its
endpoint workload is the runner's post-batch workload and its endpoint jobs
are exactly the source jobs at the physical endpoint. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_external_of_batchApplied
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatchApplied :
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        nextBatchDelay).batchApplied = true) :
    ∃ preceding terminal,
      taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime fuel capacity weight work
          currentTime nextBatchDelay = preceding ++ [terminal] ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.segment.endpointWorkload =
          (finiteGPSRunGap fuel capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            nextBatchDelay).workload ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z eventTime ∧
        finiteGPSExecutionSegmentEndTime terminal.segment =
          currentTime + nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGap] at hbatchApplied
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let step := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · refine ⟨[], step, ?_, ?_, ?_, ?_, ?_⟩
        · simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step, hterminal]
        · change (finiteGPSBuildExecutionSegment capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch = true
          exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay |>.mpr (by simpa [duration] using hterminal)
        · simpa [finiteGPSRunGap, duration, step,
            taggedAdmittedFiniteGPSBuildSegmentJobStep, hterminal] using
            (finiteGPSBuildExecutionSegment_endpointWorkload
              capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay)
        · have hExternal :
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay).endpointIsExternalBatch = true :=
            finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay |>.mpr (by simpa [duration] using hterminal)
          change taggedAdmittedFiniteGPSEndpointJobsForSegment
              start horizon target z eventTime
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay) = _
          simp [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal]
        · simp [finiteGPSExecutionSegmentEndTime, step,
            taggedAdmittedFiniteGPSBuildSegmentJobStep, duration, hterminal]
      · have htail_batchApplied :
            (finiteGPSRunGap fuel capacity weight nextWork
              (taggedAdmittedBatchAt start horizon target z eventTime)
              (nextBatchDelay - duration)).batchApplied = true := by
            simpa [finiteGPSRunGap, duration, nextWork, hterminal] using hbatchApplied
        obtain ⟨preceding, terminal, hsteps, hterminal_external,
          hterminal_workload, hterminal_jobs, hterminal_time⟩ :=
          ih (work := nextWork) (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration) htail_batchApplied
        refine ⟨step :: preceding, terminal, ?_, hterminal_external, ?_,
          hterminal_jobs, ?_⟩
        · simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, step,
            nextWork, hterminal, hsteps]
        · simpa [finiteGPSRunGap, duration, nextWork, hterminal] using
            hterminal_workload
        · calc
            finiteGPSExecutionSegmentEndTime terminal.segment =
                (currentTime + duration) + (nextBatchDelay - duration) :=
              hterminal_time
            _ = currentTime + nextBatchDelay := by ring

/-- A source-labelled constructed step can carry the literal Palm target job
only at the real zero-time source epoch.  Internal endpoints are explicitly
source-empty, so this statement is independent of work values. -/
private theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_no_tag_of_eventTime_ne_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (heventTime_ne_zero : eventTime ≠ 0)
    (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hjob : job ∈
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).endpointJobs.jobs target) :
    decide (job.identifier = (target, 0)) ≠ true := by
  let segment := finiteGPSBuildExecutionSegment capacity weight work
    (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime nextBatchDelay
  by_cases hexternal : segment.endpointIsExternalBatch = true
  · have hjob' : job ∈
        (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    intro hkey
    unfold taggedAdmittedFCFSJobsAt at hjob'
    rcases List.mem_map.mp hjob' with ⟨n, hn, hsource_job_eq⟩
    have hn_indices : n ∈
        taggedAdmittedJobIndicesAt start horizon target z eventTime target :=
      (Finset.mem_sort (fun left right : ℤ => left ≤ right)).mp hn
    have hn_time := (mem_taggedAdmittedJobIndicesAt_iff
      start horizon target z eventTime target n).mp hn_indices |>.2
    have hidentifier : (target, n) = (target, 0) := by
      calc
        (target, n) = (taggedAdmittedFCFSJob target z (target, n)).identifier := rfl
        _ = job.identifier := congrArg FiniteGPSFCFSJob.identifier hsource_job_eq
        _ = (target, 0) := of_decide_eq_true hkey
    have hn_zero : n = 0 := congrArg Prod.snd hidentifier
    subst n
    rw [taggedAdmittedSourceArrival_target_zero] at hn_time
    exact heventTime_ne_zero hn_time.symm
  · have hjob_empty : job ∈
        (taggedAdmittedFCFSComputationalEndpointJobs
          (Category := Category)).jobs target := by
      simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep,
        taggedAdmittedFiniteGPSEndpointJobsForSegment, segment, hexternal] using hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob_empty

/-- All annotated steps advancing to a nonzero physical source epoch are
free of the literal zero-time Palm target job. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_no_tag_of_eventTime_ne_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (heventTime_ne_zero : eventTime ≠ 0) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work
      currentTime nextBatchDelay,
      ∀ job ∈ step.endpointJobs.jobs target,
        decide (job.identifier = (target, 0)) ≠ true := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let head := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay = [head] := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head, hduration]
        intro step hstep job hjob
        have hstep_eq : step = head := by
          simpa [hsteps] using hstep
        subst step
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_no_tag_of_eventTime_ne_zero
          start horizon target z eventTime capacity weight work currentTime nextBatchDelay
          heventTime_ne_zero job hjob
      · have hsteps : taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime (fuel + 1) capacity weight work
          currentTime nextBatchDelay =
          head :: taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime fuel capacity weight
            (finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime + duration) (nextBatchDelay - duration) := by
            simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head, hduration]
        intro step hstep job hjob
        rw [hsteps] at hstep
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_no_tag_of_eventTime_ne_zero
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay
            heventTime_ne_zero job hjob
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            step htail job hjob

/-- Before the unique external endpoint of a successfully completed bounded
source gap, every annotated step is source-empty.  This includes a zero-time
batch: any preceding zero-duration internal steps remain computational.  It
is public because source-trace refinements must distinguish this semantic
fact from equality of the generated segment lists. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatchApplied :
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        nextBatchDelay).batchApplied = true) :
    ∃ preceding terminal,
      taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime fuel capacity weight work
          currentTime nextBatchDelay = preceding ++ [terminal] ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.segment.endpointWorkload =
          (finiteGPSRunGap fuel capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            nextBatchDelay).workload ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z eventTime ∧
        finiteGPSExecutionSegmentEndTime terminal.segment =
          currentTime + nextBatchDelay ∧
        ∀ earlier ∈ preceding,
          earlier.endpointJobs =
            taggedAdmittedFCFSComputationalEndpointJobs := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGap] at hbatchApplied
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let head := taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work currentTime nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · refine ⟨[], head, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head, hterminal]
        · change (finiteGPSBuildExecutionSegment capacity weight work
            (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay).endpointIsExternalBatch = true
          exact finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
            capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
            currentTime nextBatchDelay |>.mpr (by simpa [duration] using hterminal)
        · simpa [finiteGPSRunGap, duration, head,
            taggedAdmittedFiniteGPSBuildSegmentJobStep, hterminal] using
            (finiteGPSBuildExecutionSegment_endpointWorkload
              capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay)
        · have hExternal :
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay).endpointIsExternalBatch = true :=
            finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              currentTime nextBatchDelay |>.mpr (by simpa [duration] using hterminal)
          change taggedAdmittedFiniteGPSEndpointJobsForSegment
              start horizon target z eventTime
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay) = _
          simp [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal]
        · simp [finiteGPSExecutionSegmentEndTime, head,
            taggedAdmittedFiniteGPSBuildSegmentJobStep, duration, hterminal]
        · simp
      · have htail_batchApplied :
            (finiteGPSRunGap fuel capacity weight nextWork
              (taggedAdmittedBatchAt start horizon target z eventTime)
              (nextBatchDelay - duration)).batchApplied = true := by
            simpa [finiteGPSRunGap, duration, nextWork, hterminal] using hbatchApplied
        obtain ⟨preceding, terminal, hsteps, hterminal_external,
          hterminal_workload, hterminal_jobs, hterminal_time, hempty⟩ :=
          ih (work := nextWork) (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration) htail_batchApplied
        refine ⟨head :: preceding, terminal, ?_, hterminal_external, ?_,
          hterminal_jobs, ?_, ?_⟩
        · simp [taggedAdmittedFiniteGPSGapSegmentJobSteps, duration, head,
            nextWork, hterminal, hsteps]
        · simpa [finiteGPSRunGap, duration, nextWork, hterminal] using
            hterminal_workload
        · calc
            finiteGPSExecutionSegmentEndTime terminal.segment =
                (currentTime + duration) + (nextBatchDelay - duration) :=
              hterminal_time
            _ = currentTime + nextBatchDelay := by ring
        · intro earlier hearlier
          rcases List.mem_cons.mp hearlier with hhead | hpreceding
          · subst earlier
            have hhead_not_external : head.segment.endpointIsExternalBatch ≠ true := by
              intro hhead_external
              apply hterminal
              apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
                capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay |>.mp
              simpa [head, taggedAdmittedFiniteGPSBuildSegmentJobStep] using hhead_external
            have hbuild_not_external :
                (finiteGPSBuildExecutionSegment capacity weight work
                  (taggedAdmittedBatchAt start horizon target z eventTime)
                  currentTime nextBatchDelay).endpointIsExternalBatch ≠ true := by
              simpa [head, taggedAdmittedFiniteGPSBuildSegmentJobStep] using
                hhead_not_external
            change taggedAdmittedFiniteGPSEndpointJobsForSegment
              start horizon target z eventTime
              (finiteGPSBuildExecutionSegment capacity weight work
                (taggedAdmittedBatchAt start horizon target z eventTime)
                currentTime nextBatchDelay) = _
            simp [taggedAdmittedFiniteGPSEndpointJobsForSegment,
              hbuild_not_external]
          · exact hempty earlier hpreceding

/-- A source trace whose listed epochs exclude the Palm epoch cannot contain
the literal tagged source identifier in any FCFS endpoint list.  This is
source provenance, independent of how the GPS gap is internally segmented. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_no_tag_of_times_ne_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (times : List ℝ)
    (htimes_ne_zero : ∀ eventTime ∈ times, eventTime ≠ 0) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      ∀ job ∈ step.endpointJobs.jobs target,
        decide (job.identifier = (target, 0)) ≠ true := by
  induction times generalizing currentTime work with
  | nil =>
      simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
  | cons eventTime times ih =>
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)
      let gapSteps := taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime gapFuel capacity weight work
        currentTime (eventTime - currentTime)
      have heventTime_ne_zero : eventTime ≠ 0 :=
        htimes_ne_zero eventTime (by simp)
      have htail_ne_zero : ∀ laterTime ∈ times, laterTime ≠ 0 := by
        intro laterTime hlaterTime
        exact htimes_ne_zero laterTime (by simp [hlaterTime])
      by_cases hbatchApplied : gap.batchApplied = true
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight eventTime gap.workload times := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_no_tag_of_eventTime_ne_zero
            start horizon target z eventTime gapFuel capacity weight work
            currentTime (eventTime - currentTime) heventTime_ne_zero step hgap job hjob
        · exact ih (currentTime := eventTime) (work := gap.workload)
            htail_ne_zero step htail job hjob
      · have hsteps : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work (eventTime :: times) =
          gapSteps := by
            simp [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
              gapFuel, gap, gapSteps, hbatchApplied]
        intro step hstep job hjob
        rw [hsteps] at hstep
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_no_tag_of_eventTime_ne_zero
          start horizon target z eventTime gapFuel capacity weight work
          currentTime (eventTime - currentTime) heventTime_ne_zero step hstep job hjob

/-- At a reachable literal source endpoint, the final annotated FCFS step
records precisely the state obtained by first closing the preceding GPS state
with the zero-work horizon fence and then applying the real source batch.
The returned step is still the literal external source step. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_external_eq_horizonFence_add
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hcurrentTime_le_eventTime : currentTime ≤ eventTime)
    (i : Category) :
    ∃ preceding terminal,
      taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          currentTime (eventTime - currentTime) = preceding ++ [terminal] ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.segment.endpointWorkload i =
          (finiteGPSCloseAtHorizon capacity weight
            { workload := work
              currentTime := currentTime
              service := fun _ => 0 }
            eventTime).workload i +
            taggedAdmittedBatchAt start horizon target z eventTime i ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z eventTime ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = eventTime := by
  let fuel := (finiteGPSActiveClasses work).card + 1
  let batch := taggedAdmittedBatchAt start horizon target z eventTime
  let actualGap := finiteGPSRunGap fuel capacity weight work batch
    (eventTime - currentTime)
  let zeroGap := finiteGPSRunGap fuel capacity weight work (fun _ => 0)
    (eventTime - currentTime)
  have hdelay_nonneg : 0 ≤ eventTime - currentTime :=
    sub_nonneg.mpr hcurrentTime_le_eventTime
  have hactual_terminates : actualGap.batchApplied = true := by
    simpa [actualGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg hdelay_nonneg (Nat.lt_succ_self _)).1
  have hzero_terminates : zeroGap.batchApplied = true := by
    simpa [zeroGap, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg hdelay_nonneg (Nat.lt_succ_self _)).1
  obtain ⟨preceding, terminal, hsteps, hterminal_external,
    hterminal_workload, hterminal_jobs, hterminal_time⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_external_of_batchApplied
      start horizon target z eventTime fuel capacity weight work currentTime
      (eventTime - currentTime) (by simpa [actualGap, batch] using hactual_terminates)
  refine ⟨preceding, terminal, ?_, hterminal_external, ?_, hterminal_jobs, ?_⟩
  · simpa [fuel] using hsteps
  · have hgap_workload : actualGap.workload i =
        zeroGap.workload i + batch i := by
      simpa [actualGap, zeroGap, fuel, batch] using
        (finiteGPSRunGap_workload_eq_zeroBatch_add_of_batchApplied fuel capacity weight
          work batch (eventTime - currentTime)
          (by simpa [zeroGap, fuel] using hzero_terminates) i)
    calc
      terminal.segment.endpointWorkload i = actualGap.workload i := by
        simpa [actualGap, batch] using congrFun hterminal_workload i
      _ = zeroGap.workload i + batch i := hgap_workload
      _ = (finiteGPSCloseAtHorizon capacity weight
            { workload := work
              currentTime := currentTime
              service := fun _ => 0 }
            eventTime).workload i +
            taggedAdmittedBatchAt start horizon target z eventTime i := by
          rfl
  · calc
      finiteGPSExecutionSegmentEndTime terminal.segment =
          currentTime + (eventTime - currentTime) := hterminal_time
      _ = eventTime := by ring

/-- A chronological literal source prefix followed by one real source batch
has a final annotated FCFS step for that batch.  The endpoint workload is the
zero-fence closure of the executable prefix state plus the literal batch;
thus the statement is directly usable at the Palm epoch without converting
the real batch into a synthetic fence. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_singleton_exists_terminal_external_eq_horizonFence_add
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (prefixTimes : List ℝ) (eventTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (prefixTimes ++ [eventTime]))
    (hbatch_nonneg : ∀ batchTime ∈ prefixTimes ++ [eventTime], ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z batchTime k)
    (i : Category) :
    ∃ before terminal,
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work
          (prefixTimes ++ [eventTime]) = before ++ [terminal] ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.segment.endpointWorkload i =
          (finiteGPSCloseAtHorizon capacity weight
            (finiteGPSRunBatchTrace capacity weight
              (taggedAdmittedBatchAt start horizon target z)
              currentTime work prefixTimes)
            eventTime).workload i +
            taggedAdmittedBatchAt start horizon target z eventTime i ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z eventTime ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = eventTime := by
  let prefixResult := finiteGPSRunBatchTrace capacity weight
    (taggedAdmittedBatchAt start horizon target z)
    currentTime work prefixTimes
  have hprefix_chronological :
      FiniteGPSChronologicalFrom currentTime prefixTimes :=
    finiteGPSChronologicalFrom_prefix_of_append_singleton
      currentTime eventTime prefixTimes hchronological
  have hstart_le_eventTime : currentTime ≤ eventTime :=
    finiteGPSChronologicalFrom_start_le currentTime (prefixTimes ++ [eventTime])
      hchronological eventTime (by simp)
  have hprefix_le_eventTime : ∀ batchTime ∈ prefixTimes,
      batchTime ≤ eventTime :=
    finiteGPSChronologicalFrom_prefix_le_append_singleton
      currentTime eventTime prefixTimes hchronological
  have hprefix_batch_nonneg : ∀ batchTime ∈ prefixTimes, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z batchTime k := by
    intro batchTime hbatchTime k
    exact hbatch_nonneg batchTime (by simp [hbatchTime]) k
  have hprefix_nonneg : ∀ k, 0 ≤ prefixResult.workload k := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_workload_nonneg capacity weight work
        (taggedAdmittedBatchAt start horizon target z)
        currentTime prefixTimes hwork_nonneg hprefix_batch_nonneg)
  have hprefix_time_le_eventTime : prefixResult.currentTime ≤ eventTime := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_currentTime_le capacity weight work
        (taggedAdmittedBatchAt start horizon target z)
        currentTime eventTime prefixTimes hprefix_chronological
        hstart_le_eventTime hprefix_le_eventTime)
  have hterminal_batch_nonneg : ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro k
    exact hbatch_nonneg eventTime (by simp) k
  have hterminal_gap_applied :
      (finiteGPSRunGap ((finiteGPSActiveClasses prefixResult.workload).card + 1)
        capacity weight prefixResult.workload
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - prefixResult.currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses prefixResult.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      (sub_nonneg.mpr hprefix_time_le_eventTime) (Nat.lt_succ_self _)).1
  have htrace_append :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
      start horizon target z capacity weight work currentTime prefixTimes [eventTime]
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological
      hbatch_nonneg
  obtain ⟨gapBefore, terminal, hgapSteps, hterminal_external,
    hterminal_workload, hterminal_jobs, hterminal_time⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_external_eq_horizonFence_add
      start horizon target z eventTime capacity weight prefixResult.workload
      prefixResult.currentTime hcapacity hweight_pos htotal_weight_le_one
      hprefix_nonneg hprefix_time_le_eventTime i
  refine ⟨taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work prefixTimes ++ gapBefore,
    terminal, ?_, hterminal_external, hterminal_workload, hterminal_jobs,
    hterminal_time⟩
  calc
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work
        (prefixTimes ++ [eventTime]) =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work prefixTimes ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight prefixResult.currentTime
          prefixResult.workload [eventTime] := by
        simpa [prefixResult] using htrace_append
    _ = (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work prefixTimes ++ gapBefore) ++
        [terminal] := by
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
          start horizon target z capacity weight prefixResult.workload
          prefixResult.currentTime eventTime [] hterminal_gap_applied]
        simp only [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps,
          List.append_nil]
        rw [hgapSteps]
        simp [List.append_assoc]

/-- If a chronological annotated source prefix has no zero-time source epoch,
then appending the real zero-time batch exposes its terminal FCFS step together
with a semantic proof that no earlier endpoint list contains the Palm tag. -/
private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_zero_exists_terminal_no_earlier_tag
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (prefixTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (prefixTimes ++ [0]))
    (hbatch_nonneg : ∀ batchTime ∈ prefixTimes ++ [0], ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z batchTime k)
    (htimes_ne_zero : ∀ batchTime ∈ prefixTimes, batchTime ≠ 0) :
    ∃ before terminal,
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work
          (prefixTimes ++ [0]) = before ++ [terminal] ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z 0 ∧
        terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            currentTime work (prefixTimes ++ [0])).workload target ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = 0 ∧
        ∀ earlier ∈ before, ∀ job ∈ earlier.endpointJobs.jobs target,
          decide (job.identifier = (target, 0)) ≠ true := by
  let prefixResult := finiteGPSRunBatchTrace capacity weight
    (taggedAdmittedBatchAt start horizon target z)
    currentTime work prefixTimes
  have hprefix_chronological :
      FiniteGPSChronologicalFrom currentTime prefixTimes :=
    finiteGPSChronologicalFrom_prefix_of_append_singleton
      currentTime 0 prefixTimes hchronological
  have hstart_le_zero : currentTime ≤ 0 :=
    finiteGPSChronologicalFrom_start_le currentTime (prefixTimes ++ [0])
      hchronological 0 (by simp)
  have hprefix_le_zero : ∀ batchTime ∈ prefixTimes, batchTime ≤ 0 :=
    finiteGPSChronologicalFrom_prefix_le_append_singleton
      currentTime 0 prefixTimes hchronological
  have hprefix_batch_nonneg : ∀ batchTime ∈ prefixTimes, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z batchTime k := by
    intro batchTime hbatchTime k
    exact hbatch_nonneg batchTime (by simp [hbatchTime]) k
  have hprefix_nonneg : ∀ k, 0 ≤ prefixResult.workload k := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_workload_nonneg capacity weight work
        (taggedAdmittedBatchAt start horizon target z)
        currentTime prefixTimes hwork_nonneg hprefix_batch_nonneg)
  have hprefix_time_le_zero : prefixResult.currentTime ≤ 0 := by
    simpa [prefixResult] using
      (finiteGPSRunBatchTrace_currentTime_le capacity weight work
        (taggedAdmittedBatchAt start horizon target z)
        currentTime 0 prefixTimes hprefix_chronological
        hstart_le_zero hprefix_le_zero)
  have hzero_gap_applied :
      (finiteGPSRunGap ((finiteGPSActiveClasses prefixResult.workload).card + 1)
        capacity weight prefixResult.workload
        (taggedAdmittedBatchAt start horizon target z 0)
        (0 - prefixResult.currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses prefixResult.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      (sub_nonneg.mpr hprefix_time_le_zero) (Nat.lt_succ_self _)).1
  obtain ⟨gapBefore, terminal, hgap_steps, hterminal_external,
    hterminal_workload, hterminal_jobs, hterminal_time, hgap_empty⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      start horizon target z 0
      ((finiteGPSActiveClasses prefixResult.workload).card + 1)
      capacity weight prefixResult.workload prefixResult.currentTime
      (0 - prefixResult.currentTime) hzero_gap_applied
  have hrestart :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
      start horizon target z capacity weight work currentTime prefixTimes [0]
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological
      hbatch_nonneg
  let before := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work prefixTimes ++ gapBefore
  have hsplit : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work
      (prefixTimes ++ [0]) = before ++ [terminal] := by
    calc
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight currentTime work
          (prefixTimes ++ [0]) =
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight currentTime work prefixTimes ++
          taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight prefixResult.currentTime
            prefixResult.workload [0] := by
          simpa [prefixResult] using hrestart
      _ = taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
            start horizon target z capacity weight currentTime work prefixTimes ++
          taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z 0
            ((finiteGPSActiveClasses prefixResult.workload).card + 1)
            capacity weight prefixResult.workload prefixResult.currentTime
            (0 - prefixResult.currentTime) := by
          rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
            start horizon target z capacity weight prefixResult.workload
            prefixResult.currentTime 0 [] hzero_gap_applied]
          simp [prefixResult, taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps]
      _ = before ++ [terminal] := by
          rw [hgap_steps]
          simp [before, List.append_assoc]
  have hterminal_raw_workload : terminal.segment.endpointWorkload target =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        currentTime work (prefixTimes ++ [0])).workload target := by
    have hendpoint :=
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
        start horizon target z capacity weight work currentTime (prefixTimes ++ [0])
    rw [hsplit,
      finiteGPSFCFSSegmentStepsEndpointWorkload_append_singleton
        work before terminal] at hendpoint
    exact congrFun hendpoint target
  refine ⟨before, terminal, hsplit, hterminal_external, hterminal_jobs,
    hterminal_raw_workload, ?_, ?_⟩
  · simpa using hterminal_time
  · intro earlier hearlier job hjob
    change earlier ∈
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight currentTime work prefixTimes ++ gapBefore) at hearlier
    rcases List.mem_append.mp hearlier with hprefix | hgap
    · exact taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_no_tag_of_times_ne_zero
        start horizon target z capacity weight work currentTime prefixTimes
        htimes_ne_zero earlier hprefix job hjob
    · rw [hgap_empty earlier hgap] at hjob
      simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- The full literal tagged source trace, including its computational horizon
fence, has a concrete split at the actual zero-time Palm batch.  The exposed
terminal is a real source endpoint: it contains the literal tag exactly once,
ends at physical time zero, and records the same target workload as running
the real pre-zero source batches followed by that real zero batch. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∃ before terminal after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good capacity weight =
        before ++ terminal :: after ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt resetTime horizon target z 0 ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈
          terminal.endpointJobs.jobs target ∧
        terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime horizon target z)
            resetTime (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = 0 := by
  let prefixTimes := taggedAdmittedBatchTimeTrace resetTime 0 target z
  have hprefix_chronological :
      FiniteGPSChronologicalFrom resetTime prefixTimes := by
    simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using
      (taggedAdmittedExternalBatchTrace resetTime 0 target z htarget_good).chronological
  have hprefix_le_zero : ∀ eventTime ∈ prefixTimes, eventTime ≤ 0 := by
    intro eventTime heventTime
    have heventTime_lt : eventTime < 0 := by
      apply taggedAdmittedExternalBatchTrace_time_lt_horizon
        resetTime 0 target z htarget_good eventTime
      simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using heventTime
    exact heventTime_lt.le
  have hprefix_zero_chronological :
      FiniteGPSChronologicalFrom resetTime (prefixTimes ++ [0]) :=
    finiteGPSChronologicalFrom_append_singleton_of_forall_le
      resetTime 0 prefixTimes hprefix_chronological hreset_zero hprefix_le_zero
  have hbatch_nonneg_prefix_zero : ∀ eventTime ∈ prefixTimes ++ [0], ∀ k,
      0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  obtain ⟨before, terminal, hprefix_steps, hterminal_external,
    _hterminal_closed_workload, hterminal_jobs, hterminal_time⟩ :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_singleton_exists_terminal_external_eq_horizonFence_add
      resetTime horizon target z capacity weight (fun _ => 0)
      resetTime prefixTimes 0 hcapacity hweight_pos htotal_weight_le_one
      (by intro k; norm_num) hprefix_zero_chronological
      hbatch_nonneg_prefix_zero target
  have hprefix_endpoint_workload :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointWorkload_eq_runner
      resetTime horizon target z capacity weight (fun _ => 0)
      resetTime (prefixTimes ++ [0])
  have hterminal_raw_workload : terminal.segment.endpointWorkload target =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z)
        resetTime (fun _ : Category => 0)
        (prefixTimes ++ [0])).workload target := by
    rw [hprefix_steps] at hprefix_endpoint_workload
    rw [finiteGPSFCFSSegmentStepsEndpointWorkload_append_singleton
      (fun _ : Category => 0) before terminal] at hprefix_endpoint_workload
    exact congrFun hprefix_endpoint_workload target
  have hterminal_tag : taggedAdmittedFCFSJob target z (target, 0) ∈
      terminal.endpointJobs.jobs target := by
    rw [hterminal_jobs,
      taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
        resetTime horizon target z htarget_good hreset_zero hhorizon]
    simp
  obtain ⟨tail, hzero_cons⟩ :=
    taggedAdmittedBatchTimeTrace_zero_cons horizon target z htarget_good hhorizon
  have hfull_times : taggedAdmittedBatchTimeTrace resetTime horizon target z =
      prefixTimes ++ 0 :: tail := by
    rw [taggedAdmittedBatchTimeTrace_reset_partition
      resetTime 0 horizon target z htarget_good hreset_zero hhorizon.le]
    simpa [prefixTimes] using hzero_cons
  have hfull_chronological :
      FiniteGPSChronologicalFrom resetTime ((prefixTimes ++ [0]) ++ tail) := by
    have htrace :=
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
    rw [show (taggedAdmittedExternalBatchTrace
        resetTime horizon target z htarget_good).times =
        prefixTimes ++ 0 :: tail by exact hfull_times] at htrace
    simpa [List.append_assoc] using htrace
  have hbatch_nonneg_full : ∀ eventTime ∈ (prefixTimes ++ [0]) ++ tail, ∀ k,
      0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hsource_restart :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
      resetTime horizon target z capacity weight (fun _ => 0)
      resetTime (prefixTimes ++ [0]) tail hcapacity hweight_pos
      htotal_weight_le_one (by intro k; norm_num)
      hfull_chronological hbatch_nonneg_full
  let prefixResult := finiteGPSRunBatchTrace capacity weight
    (taggedAdmittedBatchAt resetTime horizon target z)
    resetTime (fun _ : Category => 0) (prefixTimes ++ [0])
  let afterSource := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    resetTime horizon target z capacity weight prefixResult.currentTime
    prefixResult.workload tail
  let fenceSteps := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    resetTime horizon target z htarget_good capacity weight
  refine ⟨before, terminal, afterSource ++ fenceSteps, ?_, hterminal_external,
    hterminal_jobs, hterminal_tag, ?_, hterminal_time⟩
  · unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
    change taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        resetTime horizon target z capacity weight resetTime (fun _ => 0)
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) ++ fenceSteps = _
    rw [hfull_times]
    rw [show prefixTimes ++ 0 :: tail = (prefixTimes ++ [0]) ++ tail by
      simp [List.append_assoc]]
    rw [hsource_restart]
    change (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        resetTime horizon target z capacity weight resetTime (fun _ => 0)
        (prefixTimes ++ [0]) ++ afterSource) ++ fenceSteps = _
    rw [hprefix_steps]
    simp [List.append_assoc]
  · simpa [prefixTimes] using hterminal_raw_workload

/-- Strengthened literal zero-batch split for downstream FCFS front-work
arguments.  In addition to exposing the real Palm endpoint and its exact
post-batch workload, it proves semantically that no earlier target endpoint
contains that literal source identifier. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_no_earlier_tag
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∃ before terminal after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good capacity weight =
        before ++ terminal :: after ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.endpointJobs =
          taggedAdmittedFCFSJobsAt resetTime horizon target z 0 ∧
        taggedAdmittedFCFSJob target z (target, 0) ∈
          terminal.endpointJobs.jobs target ∧
        terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime horizon target z)
            resetTime (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = 0 ∧
        ∀ earlier ∈ before, ∀ job ∈ earlier.endpointJobs.jobs target,
          decide (job.identifier = (target, 0)) ≠ true := by
  let prefixTimes := taggedAdmittedBatchTimeTrace resetTime 0 target z
  have hprefix_chronological :
      FiniteGPSChronologicalFrom resetTime (prefixTimes ++ [0]) := by
    have hprefix : FiniteGPSChronologicalFrom resetTime prefixTimes := by
      simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using
        (taggedAdmittedExternalBatchTrace resetTime 0 target z htarget_good).chronological
    have hprefix_le_zero : ∀ eventTime ∈ prefixTimes, eventTime ≤ 0 := by
      intro eventTime heventTime
      have heventTime_lt : eventTime < 0 := by
        apply taggedAdmittedExternalBatchTrace_time_lt_horizon
          resetTime 0 target z htarget_good eventTime
        simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using heventTime
      exact heventTime_lt.le
    exact finiteGPSChronologicalFrom_append_singleton_of_forall_le
      resetTime 0 prefixTimes hprefix hreset_zero hprefix_le_zero
  have hbatch_nonneg_prefix_zero : ∀ eventTime ∈ prefixTimes ++ [0], ∀ k,
      0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hprefix_times_ne_zero : ∀ eventTime ∈ prefixTimes, eventTime ≠ 0 := by
    intro eventTime heventTime heventTime_zero
    have heventTime_lt : eventTime < 0 := by
      apply taggedAdmittedExternalBatchTrace_time_lt_horizon
        resetTime 0 target z htarget_good eventTime
      simpa [prefixTimes, taggedAdmittedExternalBatchTrace] using heventTime
    linarith
  obtain ⟨before, terminal, hprefix_steps, hterminal_external,
    hterminal_jobs, hterminal_raw_workload, hterminal_time, hbefore_no_tag⟩ :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_zero_exists_terminal_no_earlier_tag
      resetTime horizon target z capacity weight (fun _ => 0)
      resetTime prefixTimes hcapacity hweight_pos htotal_weight_le_one
      (by intro k; norm_num) hprefix_chronological
      hbatch_nonneg_prefix_zero hprefix_times_ne_zero
  have hterminal_tag : taggedAdmittedFCFSJob target z (target, 0) ∈
      terminal.endpointJobs.jobs target := by
    rw [hterminal_jobs,
      taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
        resetTime horizon target z htarget_good hreset_zero hhorizon]
    simp
  obtain ⟨tail, hzero_cons⟩ :=
    taggedAdmittedBatchTimeTrace_zero_cons horizon target z htarget_good hhorizon
  have hfull_times : taggedAdmittedBatchTimeTrace resetTime horizon target z =
      prefixTimes ++ 0 :: tail := by
    rw [taggedAdmittedBatchTimeTrace_reset_partition
      resetTime 0 horizon target z htarget_good hreset_zero hhorizon.le]
    simpa [prefixTimes] using hzero_cons
  have hfull_chronological :
      FiniteGPSChronologicalFrom resetTime ((prefixTimes ++ [0]) ++ tail) := by
    have htrace :=
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
    rw [show (taggedAdmittedExternalBatchTrace
        resetTime horizon target z htarget_good).times =
        prefixTimes ++ 0 :: tail by exact hfull_times] at htrace
    simpa [List.append_assoc] using htrace
  have hbatch_nonneg_full : ∀ eventTime ∈ (prefixTimes ++ [0]) ++ tail, ∀ k,
      0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hsource_restart :=
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
      resetTime horizon target z capacity weight (fun _ => 0)
      resetTime (prefixTimes ++ [0]) tail hcapacity hweight_pos
      htotal_weight_le_one (by intro k; norm_num)
      hfull_chronological hbatch_nonneg_full
  let prefixResult := finiteGPSRunBatchTrace capacity weight
    (taggedAdmittedBatchAt resetTime horizon target z)
    resetTime (fun _ : Category => 0) (prefixTimes ++ [0])
  let afterSource := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    resetTime horizon target z capacity weight prefixResult.currentTime
    prefixResult.workload tail
  let fenceSteps := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    resetTime horizon target z htarget_good capacity weight
  refine ⟨before, terminal, afterSource ++ fenceSteps, ?_, hterminal_external,
    hterminal_jobs, hterminal_tag, ?_, ?_, hbefore_no_tag⟩
  · unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
    change taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        resetTime horizon target z capacity weight resetTime (fun _ => 0)
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) ++ fenceSteps = _
    rw [hfull_times]
    rw [show prefixTimes ++ 0 :: tail = (prefixTimes ++ [0]) ++ tail by
      simp [List.append_assoc]]
    rw [hsource_restart]
    change (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        resetTime horizon target z capacity weight resetTime (fun _ => 0)
        (prefixTimes ++ [0]) ++ afterSource) ++ fenceSteps = _
    rw [hprefix_steps]
    simp [List.append_assoc]
  · simpa [prefixTimes] using hterminal_raw_workload
  · simpa using hterminal_time

/-- Ledger-level form of the literal zero-batch split.  It promotes the
semantic endpoint-list exclusion above through the actual FCFS fold, so a
downstream front-work calculation can use the concrete zero terminal without
selecting a second, name-based admission witness. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_preLedger_no_tag
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∃ before terminal after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good capacity weight =
        before ++ terminal :: after ∧
        terminal.segment.endpointIsExternalBatch = true ∧
        terminal.endpointJobs.jobs target =
          [taggedAdmittedFCFSJob target z (target, 0)] ∧
        terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime horizon target z)
            resetTime (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = 0 ∧
        ∀ earlier ∈
          (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target,
          decide (earlier.identifier = (target, 0)) ≠ true := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_no_earlier_tag
      resetTime horizon target z htarget_good capacity weight
      hreset_zero hhorizon hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg with
      ⟨before, terminal, after, hsplit, hterminal_external, hterminal_jobs,
        _hterminal_tag, hterminal_workload, hterminal_time, hbefore_no_tag⟩
  have hterminal_singleton : terminal.endpointJobs.jobs target =
      [taggedAdmittedFCFSJob target z (target, 0)] := by
    rw [hterminal_jobs,
      taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
        resetTime horizon target z htarget_good hreset_zero hhorizon]
  refine ⟨before, terminal, after, hsplit, hterminal_external,
    hterminal_singleton, hterminal_workload, hterminal_time, ?_⟩
  apply finiteGPSFCFSRunSegmentSteps_forall_not_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    taggedAdmittedEmptyFCFSLedger before target
  · intro initialJob hinitialJob
    simp [taggedAdmittedEmptyFCFSLedger] at hinitialJob
  · exact hbefore_no_tag

/-- The literal zero-batch terminal has FCFS front work exactly equal to its
stored target endpoint workload.  This is the concrete source split needed
by the finite comparator argument: it does not switch to a separately chosen
first-key witness. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_frontWork_eq_endpointWorkload
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∃ before terminal after,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good capacity weight =
        before ++ terminal :: after ∧
        terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt resetTime horizon target z)
            resetTime (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target ∧
        finiteGPSExecutionSegmentEndTime terminal.segment = 0 ∧
        finiteGPSFCFSFrontWork
          (fun identifier : TaggedAdmittedSourceJobId Category =>
            decide (identifier = (target, 0)))
          ((taggedAdmittedFiniteGPSPostAdmissionLedger before terminal).residualJobs target) =
          some (terminal.segment.endpointWorkload target) := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_preLedger_no_tag
      resetTime horizon target z htarget_good capacity weight
      hreset_zero hhorizon hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg with
      ⟨before, terminal, after, hsplit, _hterminal_external,
        hterminal_singleton, hterminal_workload, hterminal_time, hpre_no_tag⟩
  have hfull : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime horizon target z htarget_good capacity weight) :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      resetTime horizon target z htarget_good capacity weight
      (hreset_zero.trans hhorizon.le) hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg
  have hfull_split : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) (before ++ terminal :: after) := by
    rw [← hsplit]
    exact hfull
  have hbefore_compatible := finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before (terminal :: after) hfull_split
  have hterminal_suffix := finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before (terminal :: after) hfull_split
  rcases hterminal_suffix with ⟨hledger_matches, hstart_matches, hbatch_matches,
    _hendpoint_nonneg, hservice_nonneg, hservice_le, hbalance, _htail⟩
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i queuedJob hqueuedJob
    simp [taggedAdmittedEmptyFCFSLedger] at hqueuedJob
  have hbefore_nonneg := finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) before hempty_nonneg hbefore_compatible
  have hconsumed_work : finiteGPSFCFSJobWork
      (finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
          target)) =
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target -
        terminal.segment.serviceIncrement target := by
    exact finiteGPSFCFSConsume_jobWork_eq_sub
      (terminal.segment.serviceIncrement target)
      ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
        target)
      (hservice_nonneg target)
      (fun queuedJob hqueuedJob => hbefore_nonneg target queuedJob hqueuedJob)
      (hservice_le target)
  have hpre_work_eq_start :
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target =
        terminal.segment.startWorkload target := by
    calc
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target =
          finiteGPSFCFSSegmentStepsEndpointWorkload (fun _ : Category => 0) before target :=
        hledger_matches target
      _ = terminal.segment.startWorkload target := hstart_matches target
  have htag_batch : terminal.segment.endpointBatch target =
      stationaryAdmittedTargetPalmWorkAtZero target z := by
    calc
      terminal.segment.endpointBatch target =
          terminal.endpointJobs.classWork target := (hbatch_matches target).symm
      _ = finiteGPSFCFSJobWork (terminal.endpointJobs.jobs target) := rfl
      _ = stationaryAdmittedTargetPalmWorkAtZero target z := by
        rw [hterminal_singleton]
        simp [finiteGPSFCFSJobWork, taggedAdmittedFCFSJob,
          stationaryAdmittedTargetPalmWorkAtZero,
          stationaryAdmittedTargetPalmWorkPath]
  refine ⟨before, terminal, after, hsplit, hterminal_workload,
    hterminal_time, ?_⟩
  have hfront := finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq_of_ledger_no_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
    terminal.segment terminal.endpointJobs target
    (taggedAdmittedFCFSJob target z (target, 0))
    hpre_no_tag hterminal_singleton (by simp)
  have hfront' : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((finiteGPSFCFSApplySegment
        (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
        terminal.segment terminal.endpointJobs).residualJobs target) =
      some
        (finiteGPSFCFSJobWork
          (finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
            ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
              target)) +
          stationaryAdmittedTargetPalmWorkAtZero target z) := by
    simpa [taggedAdmittedFCFSJob, stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using hfront
  rw [show taggedAdmittedFiniteGPSPostAdmissionLedger before terminal =
      finiteGPSFCFSApplySegment
        (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
        terminal.segment terminal.endpointJobs by rfl]
  rw [hfront']
  congr 1
  calc
    finiteGPSFCFSJobWork
        (finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
          ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
            target)) +
        stationaryAdmittedTargetPalmWorkAtZero target z =
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).classWork target -
          terminal.segment.serviceIncrement target +
        terminal.segment.endpointBatch target := by
          rw [hconsumed_work, htag_batch]
    _ = terminal.segment.endpointWorkload target := by
      rw [hpre_work_eq_start]
      linarith [hbalance target]

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
