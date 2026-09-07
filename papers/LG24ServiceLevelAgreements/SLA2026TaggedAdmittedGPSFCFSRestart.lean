import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSPositivity
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSZeroDelayFence
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResetBridge
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonTraceTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSPostTagTerminalStep
import Mathlib.Tactic

/-!
# Source-labelled FCFS reset primitives for tagged GPS replays

This file isolates the finite, pathwise facts needed to turn a closed
aggregate GPS prefix into a genuinely empty source-labelled FCFS state.  The
strict-positivity hypothesis is essential: aggregate zero alone cannot remove
zero-residual placeholder jobs from an FCFS queue.

The restart statements below are deliberately list-parametric.  They consume
an explicit equality of annotated step traces; deriving that equality across
an inserted computational fence is a separate semantic refinement obligation.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- On a strictly positive source-work path, every literal FCFS source job in
an exact-time endpoint batch has positive residual work. -/
theorem taggedAdmittedFCFSJobsAt_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (eventTime : ℝ) :
    ∀ i job, job ∈ (taggedAdmittedFCFSJobsAt start horizon target z eventTime).jobs i →
      0 < job.residualWork := by
  intro i job hjob
  unfold taggedAdmittedFCFSJobsAt at hjob
  rcases List.mem_map.mp hjob with ⟨n, _hn, rfl⟩
  exact taggedAdmittedSourceWork_pos target z hsource_work_pos (i, n)

/-- The annotated endpoint attached to one finite GPS segment contains only
strictly positive source jobs, when it contains any jobs at all. -/
theorem taggedAdmittedFiniteGPSEndpointJobsForSegment_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (eventTime : ℝ) (segment : FiniteGPSExecutionSegment Category) :
    ∀ i job, job ∈
      (taggedAdmittedFiniteGPSEndpointJobsForSegment
        start horizon target z eventTime segment).jobs i →
      0 < job.residualWork := by
  by_cases hExternal : segment.endpointIsExternalBatch = true
  · simpa [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal] using
      (taggedAdmittedFCFSJobsAt_residualWork_pos
        start horizon target z hsource_work_pos eventTime)
  · intro i job hjob
    simp [taggedAdmittedFiniteGPSEndpointJobsForSegment, hExternal,
      taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- The concrete source-labelled wrapper preserves strict positivity of each
endpoint job. -/
theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (eventTime : ℝ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ i job, job ∈
      (taggedAdmittedFiniteGPSBuildSegmentJobStep
        start horizon target z eventTime capacity weight work
        currentTime nextBatchDelay).endpointJobs.jobs i →
      0 < job.residualWork := by
  simpa [taggedAdmittedFiniteGPSBuildSegmentJobStep] using
    (taggedAdmittedFiniteGPSEndpointJobsForSegment_residualWork_pos
      start horizon target z hsource_work_pos eventTime
      (finiteGPSBuildExecutionSegment capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        currentTime nextBatchDelay))

/-- Every endpoint job in an annotated bounded GPS gap has positive residual
work on a strictly positive source path.  Internal depletion endpoints are
source-empty. -/
theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointJobs_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (eventTime : ℝ) (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSGapSegmentJobSteps
      start horizon target z eventTime fuel capacity weight work currentTime nextBatchDelay,
      ∀ i job, job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [taggedAdmittedFiniteGPSGapSegmentJobSteps]
  | succ fuel ih =>
      unfold taggedAdmittedFiniteGPSGapSegmentJobSteps
      dsimp only
      split
      · intro step hstep i job hjob
        have hstep_eq : step = taggedAdmittedFiniteGPSBuildSegmentJobStep
            start horizon target z eventTime capacity weight work currentTime nextBatchDelay := by
          simpa using hstep
        subst step
        exact taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_residualWork_pos
          start horizon target z hsource_work_pos eventTime capacity weight work
          currentTime nextBatchDelay i job hjob
      · intro step hstep i job hjob
        rcases List.mem_cons.mp hstep with hhead | htail
        · subst step
          exact taggedAdmittedFiniteGPSBuildSegmentJobStep_endpointJobs_residualWork_pos
            start horizon target z hsource_work_pos eventTime capacity weight work
            currentTime nextBatchDelay i job hjob
        · exact ih
            (work := finiteGPSNextEventState capacity weight work
              (taggedAdmittedBatchAt start horizon target z eventTime) nextBatchDelay)
            (currentTime := currentTime +
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (nextBatchDelay := nextBatchDelay -
              finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            step htail i job hjob

/-- Strict positivity propagates through the finite annotated source batch
trace. -/
theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointJobs_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime : ℝ) (times : List ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight currentTime work times,
      ∀ i job, job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
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
        intro step hstep i job hjob
        rcases List.mem_append.mp hstep with hgap | htail
        · exact taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointJobs_residualWork_pos
            start horizon target z hsource_work_pos eventTime
            ((finiteGPSActiveClasses work).card + 1) capacity weight work currentTime
            (eventTime - currentTime) step hgap i job hjob
        · exact ih
            (currentTime := eventTime)
            (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).workload)
            step htail i job hjob
      · have hbatchNotApplied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap] using hbatch
        rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_not_batchApplied
          start horizon target z capacity weight work currentTime eventTime times hbatchNotApplied]
        exact taggedAdmittedFiniteGPSGapSegmentJobSteps_endpointJobs_residualWork_pos
          start horizon target z hsource_work_pos eventTime
          ((finiteGPSActiveClasses work).card + 1) capacity weight work currentTime
          (eventTime - currentTime)

/-- Every literal source endpoint in the actual pre-terminal tagged FCFS
trace has positive residual work on a strictly positive source path. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointJobs_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight initialWork,
      ∀ i job, job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
  simpa [taggedAdmittedFiniteGPSPreTerminalFCFSSteps] using
    (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_endpointJobs_residualWork_pos
      start horizon target z hsource_work_pos capacity weight initialWork start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times)

/-- The complete literal source/fence FCFS trace has positive residual work
for each genuine source endpoint job.  The added horizon fence has empty
endpoint lists. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endpointJobs_residualWork_pos
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight : Category → ℝ) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight,
      ∀ i job, job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
  intro step hstep i job hjob
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpre | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointJobs_residualWork_pos
      start horizon target z htarget_good hsource_work_pos capacity weight (fun _ => 0)
      step hpre i job hjob
  · have hempty := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
      start horizon target z htarget_good capacity weight step hfence
    rw [hempty] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob

/-- Strictly positive literal source records make a zero final class-work
certificate semantically stronger: the corresponding residual FCFS queue is
literally empty, not merely zero in aggregate. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFinalLedger_residualJobs_eq_nil_of_classWork_eq_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight : Category → ℝ) (i : Category)
    (hclass_work_zero :
      (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
        start horizon target z htarget_good capacity weight).classWork i = 0) :
    (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
      start horizon target z htarget_good capacity weight).residualJobs i = [] := by
  unfold taggedAdmittedFiniteGPSHorizonFenceFinalLedger
  apply finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_classWork_eq_zero_of_pos
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
  · intro j job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  · exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_endpointJobs_residualWork_pos
      start horizon target z htarget_good hsource_work_pos capacity weight
  · exact hclass_work_zero

private theorem finiteGPSFCFSSegmentStepsEndpointWorkload_eq_erasedFinalWorkload
    (initialWorkload : Category → ℝ)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) :
    finiteGPSFCFSSegmentStepsEndpointWorkload initialWorkload steps =
      finiteGPSExecutionSegmentsFinalWorkload initialWorkload
        (steps.map fun step => step.segment) := by
  induction steps generalizing initialWorkload with
  | nil => rfl
  | cons step steps ih =>
      simpa [finiteGPSFCFSSegmentStepsEndpointWorkload,
        finiteGPSExecutionSegmentsFinalWorkload] using
        ih (initialWorkload := step.segment.endpointWorkload)

private theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_erased_eq_closedHistorySegments
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight).map
        (fun step => step.segment) =
      (finiteGPSCloseAtHorizonWithSegments capacity weight
        (taggedAdmittedFiniteGPSPreTerminalHistory
          start horizon target z htarget_good capacity weight (fun _ => 0))
        horizon).segments := by
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  rw [List.map_append, taggedAdmittedFiniteGPSPreTerminalFCFSSteps_segments]
  have hfence :
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) =
        finiteGPSHorizonFenceSegments capacity weight
          (taggedAdmittedFiniteGPSPreTerminalHistory
            start horizon target z htarget_good capacity weight (fun _ => 0)).final
          horizon := by
    unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    induction finiteGPSHorizonFenceSegments capacity weight
        (taggedAdmittedFiniteGPSPreTerminalHistory
          start horizon target z htarget_good capacity weight (fun _ => 0)).final horizon with
    | nil => rfl
    | cons segment segments ih =>
        simp only [List.map_cons]
        rw [ih]
  rw [hfence]
  unfold finiteGPSCloseAtHorizonWithSegments
  rfl

private theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_erasedFinalWorkload_eq_run_workload
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      ((taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
        (fun step => step.segment)) =
      (taggedAdmittedFiniteGPSRun start horizon target z htarget_good
        capacity weight (fun _ => 0) hstart_le_horizon).workload := by
  let history := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hchronological : FiniteGPSChronologicalFrom start
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times :=
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times, ∀ k,
      0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro eventTime heventTime k
    exact taggedAdmittedBatchAt_nonneg start horizon target z hsource_work_nonneg eventTime k
  have hpre_final_work : finiteGPSExecutionSegmentsFinalWorkload
      (fun _ : Category => 0) history.segments = history.final.workload := by
    change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
        (finiteGPSRunBatchTraceSegments capacity weight
          (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
          (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0)
        (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times).workload
    exact finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hchronological hbatch_nonneg
  have hfence_final_work : finiteGPSExecutionSegmentsFinalWorkload history.final.workload
      (finiteGPSHorizonFenceSegments capacity weight history.final horizon) =
      (finiteGPSHorizonFence capacity weight history.final horizon).workload := by
    change finiteGPSExecutionSegmentsFinalWorkload history.final.workload
        (finiteGPSRunGapSegments ((finiteGPSActiveClasses history.final.workload).card + 1)
          capacity weight history.final.workload (fun _ => 0) history.final.currentTime
          (horizon - history.final.currentTime)) =
      (finiteGPSRunGap ((finiteGPSActiveClasses history.final.workload).card + 1)
        capacity weight history.final.workload (fun _ => 0)
        (horizon - history.final.currentTime)).workload
    exact finiteGPSExecutionSegmentsFinalWorkload_runGapSegments
      ((finiteGPSActiveClasses history.final.workload).card + 1)
      capacity weight history.final.workload (fun _ => 0) history.final.currentTime
      (horizon - history.final.currentTime)
  rw [taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_erased_eq_closedHistorySegments
    start horizon target z htarget_good capacity weight]
  change finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
      (history.segments ++ finiteGPSHorizonFenceSegments capacity weight history.final horizon) = _
  funext i
  rw [finiteGPSExecutionSegmentsFinalWorkload_append, hpre_final_work, hfence_final_work]
  rfl

/-- The final source-labelled FCFS ledger has exactly the class workload of
the executable closed GPS run.  This is an erasure/compatibility identity, so
it does not assert a source-trace restart across any computational fence. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFinalLedger_classWork_eq_run_workload
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
      start horizon target z htarget_good capacity weight).classWork i =
      (taggedAdmittedFiniteGPSRun start horizon target z htarget_good
        capacity weight (fun _ => 0) hstart_le_horizon).workload i := by
  unfold taggedAdmittedFiniteGPSHorizonFenceFinalLedger
  calc
    (finiteGPSFCFSRunSegmentSteps
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)).classWork i =
      finiteGPSFCFSSegmentStepsEndpointWorkload (fun _ : Category => 0)
        (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          start horizon target z htarget_good capacity weight) i :=
      finiteGPSFCFSRunSegmentSteps_classWork_eq_endpointWorkload
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) (fun _ => 0)
        (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          start horizon target z htarget_good capacity weight)
        (by
          intro j job hjob
          simp [taggedAdmittedEmptyFCFSLedger] at hjob)
        (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
          start horizon target z htarget_good capacity weight hstart_le_horizon
          hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg) i
    _ = finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0)
        ((taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          start horizon target z htarget_good capacity weight).map
          (fun step => step.segment)) i := by
        rw [finiteGPSFCFSSegmentStepsEndpointWorkload_eq_erasedFinalWorkload]
    _ = (taggedAdmittedFiniteGPSRun start horizon target z htarget_good
        capacity weight (fun _ => 0) hstart_le_horizon).workload i := by
        rw [taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_erasedFinalWorkload_eq_run_workload
          start horizon target z htarget_good capacity weight hstart_le_horizon
          hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg]

/-- A closed executable GPS prefix with zero workload is a literally empty
source-labelled FCFS prefix on the strict-positive source-work event. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFinalLedger_residualJobs_eq_nil_of_run_workload_eq_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (i : Category)
    (hrun_workload_zero :
      (taggedAdmittedFiniteGPSRun start horizon target z htarget_good
        capacity weight (fun _ => 0) hstart_le_horizon).workload i = 0) :
    (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
      start horizon target z htarget_good capacity weight).residualJobs i = [] := by
  apply taggedAdmittedFiniteGPSHorizonFenceFinalLedger_residualJobs_eq_nil_of_classWork_eq_zero
    start horizon target z htarget_good hsource_work_pos capacity weight i
  rw [taggedAdmittedFiniteGPSHorizonFenceFinalLedger_classWork_eq_run_workload
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one]
  · exact hrun_workload_zero
  · exact ⟨fun n => (hsource_work_pos.1 n).le,
      fun k n => (hsource_work_pos.2 k n).le⟩

/-- A retained global maximizer closes the source-labelled FCFS ledger of
every diagonal prefix that starts before it.  Strict positive source work is
what upgrades the aggregate zero-work certificate to literal ledger
emptiness; no statement here identifies the original unfenced source trace
with the fence-closed trace. -/
theorem taggedAdmittedFiniteGPSDiagonalHorizonFenceFinalLedger_eq_empty_of_pastGlobalMax
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (resetTime : ℝ) (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime) :
    taggedAdmittedFiniteGPSHorizonFenceFinalLedger
        (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
        G.capacity G.weight =
      taggedAdmittedEmptyFCFSLedger := by
  let final := taggedAdmittedFiniteGPSHorizonFenceFinalLedger
    (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good G.capacity G.weight
  change final = taggedAdmittedEmptyFCFSLedger
  have hfinal_empty : ∀ i, final.residualJobs i = [] := by
    intro i
    exact taggedAdmittedFiniteGPSHorizonFenceFinalLedger_residualJobs_eq_nil_of_run_workload_eq_zero
      (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
      hsource_work_pos G.capacity G.weight hdiagonal_before_reset
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one i
      (taggedAdmittedFiniteGPSDiagonalPrefix_all_work_eq_zero_of_pastGlobalMax
        M G target z htarget_good
        ⟨fun n => (hsource_work_pos.1 n).le,
          fun k n => (hsource_work_pos.2 k n).le⟩
        resetTime hreset_zero hglobal N hdiagonal_before_reset i)
  have ledger_eq_empty : ∀ ledger : FiniteGPSFCFSJobLedger Category
      (TaggedAdmittedSourceJobId Category),
      (∀ i, ledger.residualJobs i = []) → ledger = taggedAdmittedEmptyFCFSLedger := by
    intro ledger hempty
    cases ledger with
    | mk residualJobs =>
        simp only [taggedAdmittedEmptyFCFSLedger] at hempty ⊢
        congr
        funext i
        exact hempty i
  exact ledger_eq_empty final hfinal_empty

/-- The full annotated source trace factors at a physical half-open reset
boundary.  Both factors retain the full source annotation; consequently this
is a literal recursion theorem, rather than an assertion that inserting a
computational zero-work fence leaves the generated segment list unchanged.

In particular, a source batch at `resetTime` occurs in the right factor. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_eq_fullSourceRestartAtReset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ k, 0 ≤ initialWork k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight start initialWork
          (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z) start initialWork
            (taggedAdmittedExternalBatchTrace
              start resetTime target z htarget_good).times).currentTime
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z) start initialWork
            (taggedAdmittedExternalBatchTrace
              start resetTime target z htarget_good).times).workload
          (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times := by
  have hchronological : FiniteGPSChronologicalFrom start
      ((taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times) := by
    rw [← taggedAdmittedExternalBatchTrace_times_reset_partition
      start resetTime horizon target z htarget_good hstart_reset hreset_horizon]
    exact (taggedAdmittedExternalBatchTrace
      start horizon target z htarget_good).chronological
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      ∀ k, 0 ≤ taggedAdmittedBatchAt start horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      start horizon target z hsource_work_nonneg eventTime k
  unfold taggedAdmittedFiniteGPSPreTerminalFCFSSteps
  rw [taggedAdmittedExternalBatchTrace_times_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon]
  exact taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_append_eq_restart
    start horizon target z capacity weight initialWork start
    (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times
    (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
    hcapacity hweight_pos htotal_weight_le_one hinitial_nonneg hchronological
    hbatch_nonneg

/-- At a source boundary whose literal full-source prefix has reached zero,
the exact right factor starts at `resetTime` from zero work.  This remains a
full-source annotated suffix: replacing it with the separately generated
reset-to-horizon trace additionally requires a segment-refinement theorem for
the inserted computational fence. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_eq_fullSourceZeroRestartAtReset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ k, 0 ≤ initialWork k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hprefix_currentTime :
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start initialWork
        (taggedAdmittedExternalBatchTrace
          start resetTime target z htarget_good).times).currentTime = resetTime)
    (hprefix_workload_zero : ∀ k,
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z) start initialWork
        (taggedAdmittedExternalBatchTrace
          start resetTime target z htarget_good).times).workload k = 0) :
    taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight start initialWork
          (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times ++
        taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
          start horizon target z capacity weight resetTime (fun _ => 0)
          (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times := by
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_eq_fullSourceRestartAtReset
    start resetTime horizon target z htarget_good capacity weight initialWork
    hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
    hinitial_nonneg hsource_work_nonneg]
  rw [hprefix_currentTime]
  congr 2
  funext k
  exact hprefix_workload_zero k

/-- A finite annotated FCFS step list is source-empty when every endpoint
contains no literal source jobs.  The predicate deliberately ignores segment
names and service-field values: those are not source-arrival semantics. -/
def finiteGPSFCFSSourceEmptySteps
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) : Prop :=
  ∀ step ∈ steps, ∀ i, step.endpointJobs.jobs i = []

/-- Observational equivalence for annotated FCFS traces retains the complete
per-class completion records, rather than comparing generated GPS segment
lists.  It is the appropriate relation when a computational fence refines an
idle source interval into several source-empty segments. -/
def finiteGPSFCFSCompletionTraceEquivalent
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))) : Prop :=
  ∀ i, finiteGPSFCFSRunSegmentStepsClassCompletions initial i left =
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i right

/-- Lift a scheduler-level observational correspondence to annotated FCFS
steps when both lists have literally empty endpoint ledgers.  This bridge is
intentionally stated on the observable segment relation rather than on any
constructor or function name: the FCFS fold sees only service/timing fields
and endpoint jobs. -/
private theorem finiteGPSFCFSSegmentJobSteps_forall2_of_erased_forall2_of_sourceEmpty
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsegments : List.Forall₂ FiniteGPSExecutionSegment.FCFSObservableEq
      (left.map fun step => step.segment) (right.map fun step => step.segment))
    (hleft_empty : finiteGPSFCFSSourceEmptySteps left)
    (hright_empty : finiteGPSFCFSSourceEmptySteps right) :
    List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Forall₂.nil
      | cons right rights => simp at hsegments
  | cons left lefts ih =>
      cases right with
      | nil => simp at hsegments
      | cons right rights =>
          have hhead_segments : FiniteGPSExecutionSegment.FCFSObservableEq
              left.segment right.segment := by
            simpa using (List.forall₂_cons.mp hsegments).1
          have htail_segments : List.Forall₂ FiniteGPSExecutionSegment.FCFSObservableEq
              (lefts.map fun step => step.segment) (rights.map fun step => step.segment) := by
            simpa using (List.forall₂_cons.mp hsegments).2
          have hhead_jobs : left.endpointJobs = right.endpointJobs := by
            apply (FiniteGPSFCFSEndpointJobs.mk.injEq _ _).mpr
            funext i
            rw [hleft_empty left (by simp) i, hright_empty right (by simp) i]
          have hleft_tail_empty : finiteGPSFCFSSourceEmptySteps lefts := by
            intro step hstep i
            exact hleft_empty step (by simp [hstep]) i
          have hright_tail_empty : finiteGPSFCFSSourceEmptySteps rights := by
            intro step hstep i
            exact hright_empty step (by simp [hstep]) i
          exact List.Forall₂.cons ⟨hhead_segments, hhead_jobs⟩
            (ih rights htail_segments hleft_tail_empty hright_tail_empty)

/-- Split a pointwise relation at its final element.  The helper is purely
list-structural; it makes no inference from a scheduler's generated list
name or from aggregate endpoint state. -/
private theorem list_forall2_append_singleton_split
    {Left Right : Type*} {relation : Left → Right → Prop}
    (left : List Left) (right : List Right) (leftTerminal : Left)
    (rightTerminal : Right)
    (hrelated : List.Forall₂ relation (left ++ [leftTerminal])
      (right ++ [rightTerminal])) :
    List.Forall₂ relation left right ∧ relation leftTerminal rightTerminal := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil =>
          simpa using hrelated
      | cons right rights =>
          simp at hrelated
  | cons left lefts ih =>
      cases right with
      | nil =>
          simp at hrelated
      | cons right rights =>
          have hhead_tail : relation left right ∧
              List.Forall₂ relation (lefts ++ [leftTerminal])
                (rights ++ [rightTerminal]) := by
            simpa using hrelated
          rcases ih rights hhead_tail.2 with ⟨htail, hterminal⟩
          exact ⟨List.Forall₂.cons hhead_tail.1 htail, hterminal⟩

private theorem finiteGPSFCFSCompletionTraceEquivalent_append_right_of_finalLedger_eq_local
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (left right suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hequivalent : finiteGPSFCFSCompletionTraceEquivalent initial left right)
    (hfinal : finiteGPSFCFSRunSegmentSteps initial left =
      finiteGPSFCFSRunSegmentSteps initial right) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (left ++ suffix) (right ++ suffix) := by
  intro i
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSRunSegmentStepsClassCompletions_append, hequivalent i, hfinal]

/-- A strictly post-fence real source endpoint can be refined into a literal
computational drain fence followed by the same source endpoint read from the
reset window.  This is the missing source-level lift of the scheduler's
aggregate-drain factorization: the proof retains the actual endpoint job
ledger, proves the FCFS ledger is literally empty at the cut, and compares
completion records rather than generated segment-list names. -/
private theorem taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_strictAggregateDrainFence
    (start resetTime horizon eventTime currentTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcurrent_reset : currentTime ≤ resetTime) (hreset_event : resetTime < eventTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (resetTime - currentTime)) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
        capacity weight work currentTime (eventTime - currentTime) ++ suffix)
      (finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
        taggedAdmittedFiniteGPSGapSegmentJobSteps
          resetTime horizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) ∧
      finiteGPSFCFSRunSegmentSteps initial
        (taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime) ++ suffix) =
        finiteGPSFCFSRunSegmentSteps initial
          (finiteGPSFCFSEmptyEndpointSteps
              (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
            taggedAdmittedFiniteGPSGapSegmentJobSteps
              resetTime horizon target z eventTime
              ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
              capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) := by
  let fuel := (finiteGPSActiveClasses work).card + 1
  let resetFuel := (finiteGPSActiveClasses (fun _ : Category => 0)).card + 1
  let activeSegments := finiteGPSRunGapActiveSegments fuel capacity weight work
    currentTime (resetTime - currentTime)
  let activeSteps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :=
    finiteGPSFCFSEmptyEndpointSteps activeSegments
  have hfirst_nonneg : 0 ≤ resetTime - currentTime := sub_nonneg.mpr hcurrent_reset
  have hsecond_pos : 0 < eventTime - resetTime := sub_pos.mpr hreset_event
  have hfull_delay_nonneg : 0 ≤ eventTime - currentTime :=
    sub_nonneg.mpr (hcurrent_reset.trans hreset_event.le)
  have hdelay_split : (resetTime - currentTime) + (eventTime - resetTime) =
      eventTime - currentTime := by ring
  have hfuel : (finiteGPSActiveClasses work).card < fuel := by
    dsimp [fuel]
    omega
  obtain ⟨directActive, rawTerminal, hraw_steps, hraw_observable,
    hraw_empty_batch, _hraw_external, _hraw_batch, hraw_start_zero, _hraw_time⟩ :=
    finiteGPSRunGapSegments_exists_activeFactor_of_aggregate_drain
      fuel capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
      currentTime (resetTime - currentTime) (eventTime - resetTime)
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hfirst_nonneg
      hsecond_pos haggregate_drain hfuel
  have hdirect_applied :
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hfull_delay_nonneg hfuel).1
  obtain ⟨directPre, directTerminal, hdirect_steps, _hdirect_external,
    _hdirect_workload, hdirect_jobs, _hdirect_time, hdirect_pre_empty⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      start horizon target z eventTime fuel capacity weight work currentTime
      (eventTime - currentTime) hdirect_applied
  have hraw_mapped : directPre.map (fun step => step.segment) ++
      [directTerminal.segment] = directActive ++ [rawTerminal] := by
    calc
      directPre.map (fun step => step.segment) ++ [directTerminal.segment] =
          (taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z eventTime fuel capacity weight work currentTime
            (eventTime - currentTime)).map (fun step => step.segment) := by
            rw [hdirect_steps]
            simp
      _ = finiteGPSRunGapSegments fuel capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          currentTime (eventTime - currentTime) :=
        taggedAdmittedFiniteGPSGapSegmentJobSteps_segments
          start horizon target z eventTime fuel capacity weight work currentTime
          (eventTime - currentTime)
      _ = finiteGPSRunGapSegments fuel capacity weight work
          (taggedAdmittedBatchAt start horizon target z eventTime)
          currentTime ((resetTime - currentTime) + (eventTime - resetTime)) := by
            rw [hdelay_split]
      _ = directActive ++ [rawTerminal] := hraw_steps
  have hdirect_pre_map : directPre.map (fun step => step.segment) = directActive := by
    have hdrop := congrArg List.dropLast hraw_mapped
    simpa using hdrop
  have hdirect_terminal_segment : directTerminal.segment = rawTerminal := by
    have hlast := congrArg List.getLast? hraw_mapped
    simpa using hlast
  have hactive_empty : finiteGPSFCFSSourceEmptySteps activeSteps := by
    intro step hstep i
    rcases List.mem_map.mp hstep with ⟨segment, _hsegment, rfl⟩
    rfl
  have hdirect_pre_source_empty : finiteGPSFCFSSourceEmptySteps directPre := by
    intro step hstep i
    rw [hdirect_pre_empty step hstep]
    rfl
  have hactive_observable : List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
      activeSteps directPre := by
    apply finiteGPSFCFSSegmentJobSteps_forall2_of_erased_forall2_of_sourceEmpty
      activeSteps directPre
    · have hactive_map : activeSteps.map (fun step => step.segment) = activeSegments := by
        have hempty_steps_segments : ∀ segments : List (FiniteGPSExecutionSegment Category),
            (finiteGPSFCFSEmptyEndpointSteps
              (JobId := TaggedAdmittedSourceJobId Category) segments).map
                (fun step => step.segment) = segments := by
          intro segments
          induction segments with
          | nil => rfl
          | cons segment segments ih =>
              change segment ::
                  (finiteGPSFCFSEmptyEndpointSteps
                    (JobId := TaggedAdmittedSourceJobId Category) segments).map
                      (fun step => step.segment) =
                segment :: segments
              rw [ih]
        simpa [activeSteps] using hempty_steps_segments activeSegments
      rw [hactive_map, hdirect_pre_map]
      exact hraw_observable
    · exact hactive_empty
    · exact hdirect_pre_source_empty
  have hactive_direct_completion : finiteGPSFCFSCompletionTraceEquivalent initial
      activeSteps directPre := by
    simpa [finiteGPSFCFSCompletionTraceEquivalent] using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_of_fcfsObservableEq
        initial activeSteps directPre hactive_observable)
  have hactive_direct_final : finiteGPSFCFSRunSegmentSteps initial activeSteps =
      finiteGPSFCFSRunSegmentSteps initial directPre :=
    AppliedModelingLib.Probability.Queueing.finiteGPSFCFSRunSegmentSteps_eq_of_fcfsObservableEq
      initial activeSteps directPre hactive_observable
  have hdirect_compatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime fuel capacity weight work currentTime
        (eventTime - currentTime)) :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_compatible
      start horizon target z eventTime fuel capacity weight work currentTime
      (eventTime - currentTime) initial hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hsource_work_nonneg hfull_delay_nonneg hinitial_nonneg
      hinitial_matches_work
  have hdirect_pre_compatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work
      directPre := by
    apply finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
      initial work directPre [directTerminal]
    simpa [hdirect_steps] using hdirect_compatible
  have hdirect_terminal_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps initial directPre)
      (finiteGPSFCFSSegmentStepsEndpointWorkload work directPre) [directTerminal] := by
    apply finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
      initial work directPre [directTerminal]
    simpa [hdirect_steps] using hdirect_compatible
  have hdirect_pre_class_zero : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial directPre).classWork i = 0 := by
    intro i
    calc
      (finiteGPSFCFSRunSegmentSteps initial directPre).classWork i =
          finiteGPSFCFSSegmentStepsEndpointWorkload work directPre i :=
        hdirect_terminal_compatible.1 i
      _ = directTerminal.segment.startWorkload i :=
        hdirect_terminal_compatible.2.1 i
      _ = rawTerminal.startWorkload i := by rw [hdirect_terminal_segment]
      _ = 0 := hraw_start_zero i
  have hdirect_pre_endpoint_pos : ∀ step ∈ directPre, ∀ i job,
      job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
    intro step hstep i job hjob
    rw [hdirect_pre_empty step hstep] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob
  have hdirect_pre_jobs_empty : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial directPre).residualJobs i = [] := by
    intro i
    exact finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_classWork_eq_zero_of_pos
      initial directPre hinitial_pos hdirect_pre_endpoint_pos i
      (hdirect_pre_class_zero i)
  have hactive_jobs_empty : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial activeSteps).residualJobs i = [] := by
    intro i
    rw [hactive_direct_final]
    exact hdirect_pre_jobs_empty i
  obtain ⟨computationalIdle, hcomputational_factor⟩ :=
    finiteGPSRunGapSegments_zeroBatch_exists_active_append
      fuel capacity weight work currentTime (resetTime - currentTime)
  let computationalIdleSteps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :=
    finiteGPSFCFSEmptyEndpointSteps computationalIdle
  have hcomputational_idle_empty : finiteGPSFCFSSourceEmptySteps
      computationalIdleSteps := by
    intro step hstep i
    rcases List.mem_map.mp hstep with ⟨segment, _hsegment, rfl⟩
    rfl
  have hreset_delay_nonneg : 0 ≤ eventTime - resetTime := hsecond_pos.le
  have hreset_fuel : (finiteGPSActiveClasses (fun _ : Category => 0)).card < resetFuel := by
    dsimp [resetFuel]
    omega
  have hreset_applied :
      (finiteGPSRunGap resetFuel capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt resetTime horizon target z eventTime)
        (eventTime - resetTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      resetFuel hcapacity hweight_pos htotal_weight_le_one
      (by intro i; norm_num) hreset_delay_nonneg hreset_fuel).1
  obtain ⟨resetPre, resetTerminal, hreset_steps, _hreset_external,
    _hreset_workload, hreset_jobs, _hreset_time, hreset_pre_empty⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      resetTime horizon target z eventTime resetFuel capacity weight (fun _ => 0)
      resetTime (eventTime - resetTime) hreset_applied
  have hreset_pre_source_empty : finiteGPSFCFSSourceEmptySteps resetPre := by
    intro step hstep i
    rw [hreset_pre_empty step hstep]
    rfl
  have hright_idle_empty : finiteGPSFCFSSourceEmptySteps
      (computationalIdleSteps ++ resetPre) := by
    intro step hstep i
    rcases List.mem_append.mp hstep with hleft | hright
    · exact hcomputational_idle_empty step hleft i
    · exact hreset_pre_source_empty step hright i
  have hterminal_jobs : directTerminal.endpointJobs = resetTerminal.endpointJobs := by
    calc
      directTerminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z eventTime := hdirect_jobs
      _ = taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime :=
        taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
          start resetTime horizon target z htarget_good hstart_reset eventTime hreset_event.le
      _ = resetTerminal.endpointJobs := hreset_jobs.symm
  have hright_idle_empty_generic :
      AppliedModelingLib.Probability.Queueing.finiteGPSFCFSSourceEmptySteps
        (computationalIdleSteps ++ resetPre) := by
    exact hright_idle_empty
  have hempty_idle_generic :
      AppliedModelingLib.Probability.Queueing.finiteGPSFCFSSourceEmptySteps
        ([] : List (FiniteGPSFCFSSegmentJobStep Category
          (TaggedAdmittedSourceJobId Category))) := by
    intro step hstep
    simp at hstep
  have htail_equivalent : finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps initial activeSteps)
      ([directTerminal] ++ suffix)
      (((computationalIdleSteps ++ resetPre) ++ [resetTerminal]) ++ suffix) := by
    simpa [finiteGPSFCFSCompletionTraceEquivalent,
      AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent,
      List.append_assoc] using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
        (finiteGPSFCFSRunSegmentSteps initial activeSteps)
        [] (computationalIdleSteps ++ resetPre) directTerminal resetTerminal suffix
        hactive_jobs_empty hempty_idle_generic hright_idle_empty_generic hterminal_jobs)
  have htail_final : finiteGPSFCFSRunSegmentSteps
      (finiteGPSFCFSRunSegmentSteps initial activeSteps) [directTerminal] =
      finiteGPSFCFSRunSegmentSteps
        (finiteGPSFCFSRunSegmentSteps initial activeSteps)
        ((computationalIdleSteps ++ resetPre) ++ [resetTerminal]) := by
    simpa using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSRunSegmentSteps_eq_of_sourceEmptyLeadIn
        (finiteGPSFCFSRunSegmentSteps initial activeSteps)
        [] (computationalIdleSteps ++ resetPre) directTerminal resetTerminal
        hactive_jobs_empty hempty_idle_generic hright_idle_empty_generic hterminal_jobs)
  have hprefix_equivalent : finiteGPSFCFSCompletionTraceEquivalent initial
      directPre activeSteps := by
    intro i
    exact (hactive_direct_completion i).symm
  have hprefix_final : finiteGPSFCFSRunSegmentSteps initial directPre =
      finiteGPSFCFSRunSegmentSteps initial activeSteps := hactive_direct_final.symm
  have hprefix_extended : finiteGPSFCFSCompletionTraceEquivalent initial
      (directPre ++ ([directTerminal] ++ suffix))
      (activeSteps ++ ([directTerminal] ++ suffix)) :=
    finiteGPSFCFSCompletionTraceEquivalent_append_right_of_finalLedger_eq_local
      initial directPre activeSteps ([directTerminal] ++ suffix)
      hprefix_equivalent hprefix_final
  have hright_extended : finiteGPSFCFSCompletionTraceEquivalent initial
      (activeSteps ++ ([directTerminal] ++ suffix))
      (activeSteps ++ (((computationalIdleSteps ++ resetPre) ++ [resetTerminal]) ++ suffix)) :=
    by
      simpa [finiteGPSFCFSCompletionTraceEquivalent,
        AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent] using
        (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_append_left
          initial activeSteps ([directTerminal] ++ suffix)
          (((computationalIdleSteps ++ resetPre) ++ [resetTerminal]) ++ suffix)
          htail_equivalent)
  have hgap_final : finiteGPSFCFSRunSegmentSteps initial
      (directPre ++ [directTerminal]) =
      finiteGPSFCFSRunSegmentSteps initial
        (activeSteps ++ ((computationalIdleSteps ++ resetPre) ++ [resetTerminal])) := by
    rw [finiteGPSFCFSRunSegmentSteps_append,
      finiteGPSFCFSRunSegmentSteps_append, hprefix_final, htail_final]
  have hgap_final_with_suffix : finiteGPSFCFSRunSegmentSteps initial
      ((directPre ++ [directTerminal]) ++ suffix) =
      finiteGPSFCFSRunSegmentSteps initial
        ((activeSteps ++ ((computationalIdleSteps ++ resetPre) ++ [resetTerminal])) ++ suffix) := by
    calc
      finiteGPSFCFSRunSegmentSteps initial ((directPre ++ [directTerminal]) ++ suffix) =
          finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial (directPre ++ [directTerminal])) suffix := by
            rw [finiteGPSFCFSRunSegmentSteps_append]
      _ = finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial
              (activeSteps ++ ((computationalIdleSteps ++ resetPre) ++ [resetTerminal]))) suffix := by
            rw [hgap_final]
      _ = finiteGPSFCFSRunSegmentSteps initial
            ((activeSteps ++ ((computationalIdleSteps ++ resetPre) ++ [resetTerminal])) ++ suffix) := by
            exact (finiteGPSFCFSRunSegmentSteps_append initial
              (activeSteps ++ ((computationalIdleSteps ++ resetPre) ++ [resetTerminal]))
              suffix).symm
  have hzero_steps : finiteGPSFCFSEmptyEndpointSteps
      (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
        currentTime (resetTime - currentTime)) =
      activeSteps ++ computationalIdleSteps := by
    rw [hcomputational_factor]
    simp [activeSteps, activeSegments, computationalIdleSteps,
      finiteGPSFCFSEmptyEndpointSteps]
  constructor
  · intro i
    rw [hdirect_steps, hzero_steps, hreset_steps]
    simpa [List.append_assoc] using (hprefix_extended i).trans (hright_extended i)
  · rw [hdirect_steps, hzero_steps, hreset_steps]
    simpa [List.append_assoc] using hgap_final_with_suffix

/-- Completion-trace equivalence is stable under a common already-executed
prefix.  The equivalence hypothesis begins from the ledger at the physical
cut, so this does not pretend that the two generated suffix step lists are
syntactically equal. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_append_left
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (before left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hequivalent : finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps initial before) left right) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (before ++ left) (before ++ right) := by
  intro i
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSRunSegmentStepsClassCompletions_append, hequivalent i]

/-- Extending equivalent completion histories by a common continuation is
sound exactly when both histories leave the same literal FCFS ledger.  The
final-ledger condition is retained rather than inferred from completion-list
equality, because the latter alone does not determine a future FCFS run. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_append_right_of_finalLedger_eq
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (left right suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hequivalent : finiteGPSFCFSCompletionTraceEquivalent initial left right)
    (hfinal : finiteGPSFCFSRunSegmentSteps initial left =
      finiteGPSFCFSRunSegmentSteps initial right) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (left ++ suffix) (right ++ suffix) := by
  intro i
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
    finiteGPSFCFSRunSegmentStepsClassCompletions_append, hequivalent i, hfinal]

/-- Starting with no residual source jobs, a source-empty step list retains
the literally empty ledger.  No restriction on stored service is needed:
FCFS service applied to an empty queue is inert. -/
theorem finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
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
ledger.  This is the completion-level form of computational-fence stuttering. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletions_eq_nil_of_sourceEmptySteps
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (i : Category)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hinitial_empty : ∀ k, initial.residualJobs k = [])
    (hsource_empty : finiteGPSFCFSSourceEmptySteps steps) :
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps = [] := by
  induction steps generalizing initial with
  | nil =>
      rfl
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

/-- Inserting or deleting any source-empty idle block after a literal empty
cut preserves every class's FCFS completion trace.  This is a semantic
stuttering theorem; it never identifies the concrete GPS segment lists. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_insert_sourceEmptySteps
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (before idle suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hbefore_empty : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial before).residualJobs i = [])
    (hidle_source_empty : finiteGPSFCFSSourceEmptySteps idle) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (before ++ idle ++ suffix) (before ++ suffix) := by
  intro i
  have hidle_completions : finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps initial before) i idle = [] :=
    finiteGPSFCFSRunSegmentStepsClassCompletions_eq_nil_of_sourceEmptySteps
      (finiteGPSFCFSRunSegmentSteps initial before) i idle hbefore_empty hidle_source_empty
  have hidle_final_empty : ∀ k,
      (finiteGPSFCFSRunSegmentSteps
        (finiteGPSFCFSRunSegmentSteps initial before) idle).residualJobs k = [] :=
    finiteGPSFCFSRunSegmentSteps_residualJobs_eq_nil_of_sourceEmptySteps
      (finiteGPSFCFSRunSegmentSteps initial before) idle hbefore_empty hidle_source_empty
  have ledger_eq_of_residualJobs_eq : ∀ left right :
      FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category),
      (∀ k, left.residualJobs k = right.residualJobs k) → left = right := by
    intro left right heq
    cases left
    cases right
    cases funext heq
    rfl
  have hidle_run_eq : finiteGPSFCFSRunSegmentSteps
      (finiteGPSFCFSRunSegmentSteps initial before) idle =
      finiteGPSFCFSRunSegmentSteps initial before := by
    apply ledger_eq_of_residualJobs_eq
    intro k
    rw [hidle_final_empty k, hbefore_empty k]
  calc
    finiteGPSFCFSRunSegmentStepsClassCompletions initial i
        (before ++ idle ++ suffix) =
      finiteGPSFCFSRunSegmentStepsClassCompletions initial i (before ++ idle) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps initial (before ++ idle)) i suffix := by
        rw [show before ++ idle ++ suffix = (before ++ idle) ++ suffix by
          simp [List.append_assoc], finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    _ = (finiteGPSFCFSRunSegmentStepsClassCompletions initial i before ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps initial before) i idle) ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial before) idle) i suffix := by
        rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append,
          finiteGPSFCFSRunSegmentSteps_append]
    _ = finiteGPSFCFSRunSegmentStepsClassCompletions initial i before ++
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (finiteGPSFCFSRunSegmentSteps initial before) i suffix := by
        rw [hidle_completions, hidle_run_eq]
        simp
    _ = finiteGPSFCFSRunSegmentStepsClassCompletions initial i (before ++ suffix) := by
        symm
        exact finiteGPSFCFSRunSegmentStepsClassCompletions_append initial i before suffix

/-- A physical idle interval may be refined into different source-empty GPS
segment lists before the same next source endpoint.  If both versions start
from a literal empty ledger and attach identical endpoint jobs at that next
endpoint, their continuation completion traces are observationally equal.
The concrete segment service fields may differ. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (leftIdle rightIdle : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (leftTerminal rightTerminal : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hinitial_empty : ∀ i, initial.residualJobs i = [])
    (hleft_empty : finiteGPSFCFSSourceEmptySteps leftIdle)
    (hright_empty : finiteGPSFCFSSourceEmptySteps rightIdle)
    (hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      ((leftIdle ++ [leftTerminal]) ++ suffix)
      ((rightIdle ++ [rightTerminal]) ++ suffix) := by
  have ledger_eq_of_residualJobs_eq : ∀ left right :
      FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category),
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

/-- A fence refinement may change only the source-empty tail after a common
active prefix has literally emptied the FCFS ledger.  Under that structural
condition, identical terminal source jobs yield the same completion trace
through any common continuation.  This is the generic annotated-FCFS part of
a crossing-gap proof; deriving the displayed empty cut from a GPS split is a
separate scheduler theorem. -/
theorem finiteGPSFCFSCompletionTraceEquivalent_of_fenceRefinement_at_empty_cut
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (activePrefix leftIdle rightIdle : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (leftTerminal rightTerminal : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hactive_empty : ∀ i,
      (finiteGPSFCFSRunSegmentSteps initial activePrefix).residualJobs i = [])
    (hleft_empty : finiteGPSFCFSSourceEmptySteps leftIdle)
    (hright_empty : finiteGPSFCFSSourceEmptySteps rightIdle)
    (hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (activePrefix ++ ((leftIdle ++ [leftTerminal]) ++ suffix))
      (activePrefix ++ ((rightIdle ++ [rightTerminal]) ++ suffix)) := by
  apply finiteGPSFCFSCompletionTraceEquivalent_append_left
  exact finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
    (finiteGPSFCFSRunSegmentSteps initial activePrefix)
    leftIdle rightIdle leftTerminal rightTerminal suffix hactive_empty
    hleft_empty hright_empty hterminal_jobs

/-- Two literal tagged GPS gaps started with zero source work are completion
equivalent whenever their real external endpoint carries the same source-job
batch.  The generated lead-ins may contain different computational segments;
the proof exposes each as source-empty and applies semantic lead-in
equivalence, rather than asserting equality of those segment lists. -/
theorem taggedAdmittedFiniteGPSGap_completionTraceEquivalent_of_zeroStart_and_endpointJobs_eq
    (leftStart leftHorizon rightStart rightHorizon currentTime eventTime : ℝ)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_empty : ∀ i, initial.residualJobs i = [])
    (hcurrentTime_le_eventTime : currentTime ≤ eventTime)
    (hendpoint_jobs :
      taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime =
        taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
          leftStart leftHorizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) currentTime (eventTime - currentTime) ++ suffix)
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
          rightStart rightHorizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) currentTime (eventTime - currentTime) ++ suffix) := by
  have hdelay_nonneg : 0 ≤ eventTime - currentTime :=
    sub_nonneg.mpr hcurrentTime_le_eventTime
  have hleft_batch_applied :
      (finiteGPSRunGap
        ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
        capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt leftStart leftHorizon target z eventTime)
        (eventTime - currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hdelay_nonneg (Nat.lt_succ_self _)).1
  have hright_batch_applied :
      (finiteGPSRunGap
        ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
        capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt rightStart rightHorizon target z eventTime)
        (eventTime - currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      hdelay_nonneg (Nat.lt_succ_self _)).1
  obtain ⟨leftIdle, leftTerminal, hleft_steps, _hleft_external,
    _hleft_workload, hleft_terminal_jobs, _hleft_time, hleft_idle_computational⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      leftStart leftHorizon target z eventTime
      ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
      capacity weight (fun _ => 0) currentTime (eventTime - currentTime)
      hleft_batch_applied
  obtain ⟨rightIdle, rightTerminal, hright_steps, _hright_external,
    _hright_workload, hright_terminal_jobs, _hright_time, hright_idle_computational⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      rightStart rightHorizon target z eventTime
      ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
      capacity weight (fun _ => 0) currentTime (eventTime - currentTime)
      hright_batch_applied
  have hleft_idle_source_empty : finiteGPSFCFSSourceEmptySteps leftIdle := by
    intro earlier hearlier i
    rw [hleft_idle_computational earlier hearlier]
    rfl
  have hright_idle_source_empty : finiteGPSFCFSSourceEmptySteps rightIdle := by
    intro earlier hearlier i
    rw [hright_idle_computational earlier hearlier]
    rfl
  have hterminal_jobs : leftTerminal.endpointJobs = rightTerminal.endpointJobs := by
    calc
      leftTerminal.endpointJobs =
          taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime :=
        hleft_terminal_jobs
      _ = taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime :=
        hendpoint_jobs
      _ = rightTerminal.endpointJobs := hright_terminal_jobs.symm
  rw [hleft_steps, hright_steps]
  exact finiteGPSFCFSCompletionTraceEquivalent_of_sourceEmptyLeadIn
    initial leftIdle rightIdle leftTerminal rightTerminal suffix hinitial_empty
    hleft_idle_source_empty hright_idle_source_empty hterminal_jobs

/-- At a literal reset boundary, the full-source and reset-restricted GPS
gaps to the same next source epoch satisfy the semantic completion-trace
equivalence above.  The endpoint equality is source-semantic: an arrival at
`resetTime` or later belongs to the suffix ledger in both descriptions. -/
theorem taggedAdmittedFiniteGPSGap_completionTraceEquivalent_at_reset
    (start resetTime horizon eventTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hresetTime_le_eventTime : resetTime ≤ eventTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_empty : ∀ i, initial.residualJobs i = []) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix)
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
          resetTime horizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) := by
  exact taggedAdmittedFiniteGPSGap_completionTraceEquivalent_of_zeroStart_and_endpointJobs_eq
    start horizon resetTime horizon resetTime eventTime target z capacity weight
    initial suffix hcapacity hweight_pos htotal_weight_le_one hinitial_empty
    hresetTime_le_eventTime
    (taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime
      hresetTime_le_eventTime)

/- The following source-window transport helpers are private proof machinery.
They are used only to obtain an observational statement for a suffix whose
literal source inputs agree at every listed epoch; they are not a claim that a
computational-fence refinement has equal raw segment lists. -/
private theorem taggedAdmittedFiniteGPSBuildSegmentJobStep_eq_of_sourceInputs_eq
    (leftStart leftHorizon rightStart rightHorizon : ℝ)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatch : taggedAdmittedBatchAt leftStart leftHorizon target z eventTime =
      taggedAdmittedBatchAt rightStart rightHorizon target z eventTime)
    (hendpoint : taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime =
      taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime) :
    taggedAdmittedFiniteGPSBuildSegmentJobStep
        leftStart leftHorizon target z eventTime capacity weight work
        currentTime nextBatchDelay =
      taggedAdmittedFiniteGPSBuildSegmentJobStep
        rightStart rightHorizon target z eventTime capacity weight work
        currentTime nextBatchDelay := by
  unfold taggedAdmittedFiniteGPSBuildSegmentJobStep
  rw [hbatch]
  rw [FiniteGPSFCFSSegmentJobStep.mk.injEq]
  constructor
  · rfl
  · unfold taggedAdmittedFiniteGPSEndpointJobsForSegment
    split <;> simp [hendpoint]

private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_sourceInputs_eq
    (leftStart leftHorizon rightStart rightHorizon : ℝ)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (eventTime : ℝ) (fuel : ℕ) (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hbatch : taggedAdmittedBatchAt leftStart leftHorizon target z eventTime =
      taggedAdmittedBatchAt rightStart rightHorizon target z eventTime)
    (hendpoint : taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime =
      taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime) :
    taggedAdmittedFiniteGPSGapSegmentJobSteps
        leftStart leftHorizon target z eventTime fuel capacity weight work
        currentTime nextBatchDelay =
      taggedAdmittedFiniteGPSGapSegmentJobSteps
        rightStart rightHorizon target z eventTime fuel capacity weight work
        currentTime nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      rfl
  | succ fuel ih =>
      have hstep := taggedAdmittedFiniteGPSBuildSegmentJobStep_eq_of_sourceInputs_eq
        leftStart leftHorizon rightStart rightHorizon target z eventTime capacity weight work
        currentTime nextBatchDelay hbatch hendpoint
      unfold taggedAdmittedFiniteGPSGapSegmentJobSteps
      dsimp only
      rw [hstep, hbatch]
      split
      · rfl
      · rw [ih]

private theorem taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceInputs_eq
    (leftStart leftHorizon rightStart rightHorizon : ℝ)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ) (currentTime : ℝ)
    (times : List ℝ)
    (hbatch : ∀ eventTime ∈ times,
      taggedAdmittedBatchAt leftStart leftHorizon target z eventTime =
        taggedAdmittedBatchAt rightStart rightHorizon target z eventTime)
    (hendpoint : ∀ eventTime ∈ times,
      taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime =
        taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime) :
    taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        leftStart leftHorizon target z capacity weight currentTime work times =
      taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        rightStart rightHorizon target z capacity weight currentTime work times := by
  induction times generalizing currentTime work with
  | nil =>
      rfl
  | cons eventTime times ih =>
      have hbatch_head :
          taggedAdmittedBatchAt leftStart leftHorizon target z eventTime =
            taggedAdmittedBatchAt rightStart rightHorizon target z eventTime :=
        hbatch eventTime (by simp)
      have hendpoint_head :
          taggedAdmittedFCFSJobsAt leftStart leftHorizon target z eventTime =
            taggedAdmittedFCFSJobsAt rightStart rightHorizon target z eventTime :=
        hendpoint eventTime (by simp)
      have hbatch_tail : ∀ laterTime ∈ times,
          taggedAdmittedBatchAt leftStart leftHorizon target z laterTime =
            taggedAdmittedBatchAt rightStart rightHorizon target z laterTime := by
        intro laterTime hlaterTime
        exact hbatch laterTime (by simp [hlaterTime])
      have hendpoint_tail : ∀ laterTime ∈ times,
          taggedAdmittedFCFSJobsAt leftStart leftHorizon target z laterTime =
            taggedAdmittedFCFSJobsAt rightStart rightHorizon target z laterTime := by
        intro laterTime hlaterTime
        exact hendpoint laterTime (by simp [hlaterTime])
      have hgap_steps := taggedAdmittedFiniteGPSGapSegmentJobSteps_eq_of_sourceInputs_eq
        leftStart leftHorizon rightStart rightHorizon target z eventTime
        ((finiteGPSActiveClasses work).card + 1) capacity weight work
        currentTime (eventTime - currentTime) hbatch_head hendpoint_head
      have hgap_run :
          finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work
            (taggedAdmittedBatchAt leftStart leftHorizon target z eventTime)
            (eventTime - currentTime) =
          finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work
            (taggedAdmittedBatchAt rightStart rightHorizon target z eventTime)
            (eventTime - currentTime) := by
        rw [hbatch_head]
      unfold taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      dsimp only
      rw [hgap_steps, hgap_run]
      split
      · rw [ih]
        · exact hbatch_tail
        · exact hendpoint_tail
      · rfl

/-- The whole literal source suffix from a reset boundary is observationally
equivalent whether its batches are read through the full source window or
through the reset-restricted source window.  The proof recurses over every
listed physical source epoch and uses equality of both aggregate batch work
and literal endpoint jobs at that epoch.  This does not compare a trace that
has had an extra computational fence inserted before the reset. -/
theorem taggedAdmittedFiniteGPSBatchTrace_completionTraceEquivalent_at_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (hstart_reset : start ≤ resetTime) (_hreset_horizon : resetTime ≤ horizon) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times)
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime horizon target z htarget_good capacity weight (fun _ => 0)) := by
  have hbatch : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      taggedAdmittedBatchAt start horizon target z eventTime =
        taggedAdmittedBatchAt resetTime horizon target z eventTime := by
    intro eventTime heventTime
    apply taggedAdmittedBatchAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime
    apply taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime
    exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
      (by simpa [taggedAdmittedExternalBatchTrace,
        taggedAdmittedBatchTimeTrace] using heventTime)
  have hendpoint : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      taggedAdmittedFCFSJobsAt start horizon target z eventTime =
        taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime := by
    intro eventTime heventTime
    apply taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime
    apply taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime
    exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
      (by simpa [taggedAdmittedExternalBatchTrace,
        taggedAdmittedBatchTimeTrace] using heventTime)
  unfold taggedAdmittedFiniteGPSPreTerminalFCFSSteps
  intro i
  rw [taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceInputs_eq
    start horizon resetTime horizon target z capacity weight (fun _ => 0)
    resetTime
    (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
    hbatch hendpoint]

/-- Completion-trace equivalence preserves the deterministic selected Palm
completion, so a source-empty computational-fence refinement cannot change
the tag result once its structural correspondence has been supplied. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_eq_of_completionTraceEquivalent
    (target : Category)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hequivalent : finiteGPSFCFSCompletionTraceEquivalent initial left right) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial target left) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions initial target right) := by
  rw [hequivalent target]

/-- The finite FCFS fold restarts from an explicitly empty ledger once its
left step list has literally emptied that ledger. -/
theorem taggedAdmittedFCFSRunSegmentSteps_restart_empty_of_prefix_eq_empty
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hprefix_empty :
      finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) left =
        taggedAdmittedEmptyFCFSLedger) :
    finiteGPSFCFSRunSegmentSteps
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) (left ++ right) =
      finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) right := by
  rw [finiteGPSFCFSRunSegmentSteps_append, hprefix_empty]

/-- Completion records factor at an explicit source-labelled empty cut.  This
is a list-level restart law: it makes no claim that two separately generated
GPS step lists are equal. -/
theorem taggedAdmittedFCFSRunSegmentSteps_targetCompletions_append_of_prefix_eq_empty
    (target : Category)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hprefix_empty :
      finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) left =
        taggedAdmittedEmptyFCFSLedger) :
    finiteGPSFCFSRunSegmentStepsClassCompletions
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) target (left ++ right) =
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target left ++
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target right := by
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append, hprefix_empty]

/-- The deterministic tag selector is stable when the already-selected
completion list is extended on the right. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_append_of_some
    (target : Category)
    (left right : List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)))
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedFiniteGPSFirstTagCompletion? target left = some selected) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target (left ++ right) = some selected := by
  induction left with
  | nil =>
      simp [taggedAdmittedFiniteGPSFirstTagCompletion?] at hselected
  | cons completion completions ih =>
      by_cases htag : completion.identifier = (target, 0)
      · simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using hselected
      · have htail : taggedAdmittedFiniteGPSFirstTagCompletion? target completions =
            some selected := by
            simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using hselected
        simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using ih htail

/-- The deterministic tag selector skips an explicitly tag-free left trace.
This is the zero-cut form used once source provenance proves that the selected
Palm job is not admitted before the retained reset boundary. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_append_of_none
    (target : Category)
    (left right : List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)))
    (hleft : taggedAdmittedFiniteGPSFirstTagCompletion? target left = none) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target (left ++ right) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target right := by
  induction left with
  | nil =>
      rfl
  | cons completion completions ih =>
      by_cases htag : completion.identifier = (target, 0)
      · simp [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] at hleft
      · have htail : taggedAdmittedFiniteGPSFirstTagCompletion? target completions = none := by
          simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using hleft
        simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, htag] using ih htail

/-- A completion trace carrying no record with the literal Palm identifier
has no selected Palm completion.  This is stated on completion provenance,
not on how the trace was produced. -/
private theorem taggedAdmittedFiniteGPSFirstTagCompletion?_eq_none_of_forall_identifier_ne
    (target : Category)
    (completions : List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)))
    (hno_tag : ∀ completion ∈ completions, completion.identifier ≠ (target, 0)) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target completions = none := by
  induction completions with
  | nil => rfl
  | cons completion completions ih =>
      have hhead : completion.identifier ≠ (target, 0) := hno_tag completion (by simp)
      have htail : ∀ later ∈ completions, later.identifier ≠ (target, 0) := by
        intro later hlater
        exact hno_tag later (by simp [hlater])
      simpa [taggedAdmittedFiniteGPSFirstTagCompletion?, hhead] using ih htail

/-- A selected source-tag completion persists when an annotated FCFS step
trace is literally extended.  This is the horizon-extension primitive; the
caller must supply the trace equality rather than relying on aggregate
workload equality. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
    (target : Category)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hselected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target left) = some selected) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target (left ++ right)) =
      some selected := by
  rw [finiteGPSFCFSRunSegmentStepsClassCompletions_append]
  exact taggedAdmittedFiniteGPSFirstTagCompletion?_append_of_some
    target
    (finiteGPSFCFSRunSegmentStepsClassCompletions
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) target left)
    (finiteGPSFCFSRunSegmentStepsClassCompletions
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) left) target right)
    selected hselected

/-- At a literal empty cut with a tag-free prefix, the deterministic tag
selector is exactly the selector of the zero-start suffix. -/
theorem taggedAdmittedFiniteGPSFirstTagCompletion?_restart_of_stepTrace_append
    (target : Category)
    (left right : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hprefix_empty :
      finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) left =
        taggedAdmittedEmptyFCFSLedger)
    (hprefix_no_tag : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target left) = none) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target (left ++ right)) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target right) := by
  rw [taggedAdmittedFCFSRunSegmentSteps_targetCompletions_append_of_prefix_eq_empty
    target left right hprefix_empty]
  exact taggedAdmittedFiniteGPSFirstTagCompletion?_append_of_none
    target
    (finiteGPSFCFSRunSegmentStepsClassCompletions
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) target left)
    (finiteGPSFCFSRunSegmentStepsClassCompletions
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) target right)
    hprefix_no_tag

/-- The direct source endpoint at a terminal drain carries the literal source
batch at `eventTime`.  This is intentionally distinct from the computational
fence step, whose endpoint job ledger is literally empty even though its GPS
segment reaches the same clock time. -/
def taggedAdmittedGPSZeroDelayFenceDirectStep
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime drainDelay : ℝ) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  { segment := finiteGPSBuildExecutionSegment capacity weight work
      (taggedAdmittedBatchAt start horizon target z eventTime) currentTime drainDelay
    endpointJobs := taggedAdmittedFCFSJobsAt start horizon target z eventTime }

/-- The computational half of a zero-delay fence has no source admission. -/
def taggedAdmittedGPSZeroDelayFenceComputationalStep
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime drainDelay : ℝ) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  { segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
      currentTime drainDelay
    endpointJobs := taggedAdmittedFCFSComputationalEndpointJobs }

/-- The real source endpoint after a zero-delay computational fence is a
distinct zero-duration, zero-service external step.  It carries exactly the
same literal source-job batch as the direct endpoint. -/
def taggedAdmittedGPSZeroDelayFenceRealEndpointStep
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight : Category → ℝ)
    (currentTime drainDelay : ℝ) :
    FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category) :=
  { segment := finiteGPSBuildExecutionSegment capacity weight (fun _ => 0)
      (taggedAdmittedBatchAt start horizon target z eventTime)
      (currentTime + drainDelay) 0
    endpointJobs := taggedAdmittedFCFSJobsAt start horizon target z eventTime }

/-- The actual reset-start gap at a source epoch equal to the reset time has
one explicit zero-duration real endpoint.  This is an executable identity,
not a convention about simultaneous source batches. -/
private theorem taggedAdmittedFiniteGPSGapSegmentJobSteps_zeroStart_zeroDelay
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight : Category → ℝ) :
    taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime
        ((finiteGPSActiveClasses (fun _ : Category => (0 : ℝ))).card + 1)
        capacity weight (fun _ => 0) eventTime 0 =
      [taggedAdmittedGPSZeroDelayFenceRealEndpointStep
        start horizon target z eventTime capacity weight eventTime 0] := by
  have hexternal :
      (finiteGPSBuildExecutionSegment capacity weight (fun _ : Category => 0)
        (taggedAdmittedBatchAt start horizon target z eventTime) eventTime 0).endpointIsExternalBatch =
        true := by
    apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
      capacity weight (fun _ : Category => 0)
      (taggedAdmittedBatchAt start horizon target z eventTime) eventTime 0 |>.mpr
    simp [finiteGPSNextStepDuration, finiteGPSActiveClasses]
  simp [taggedAdmittedFiniteGPSGapSegmentJobSteps,
    taggedAdmittedGPSZeroDelayFenceRealEndpointStep,
    taggedAdmittedFiniteGPSBuildSegmentJobStep,
    taggedAdmittedFiniteGPSEndpointJobsForSegment,
    finiteGPSNextStepDuration, finiteGPSActiveClasses, hexternal]

/-- When the first retained source batch is exactly at the physical reset,
the direct source endpoint is related to a computational drain endpoint plus
the literal zero-duration source admission.  This is the equality case of
the crossing argument.  It carries both completion history and the literal
post-crossing FCFS ledger so that an unchanged later source trace can be
continued; no strict positive interarrival assumption is introduced. -/
private theorem taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_zeroDelayAggregateDrainFence
    (start resetTime horizon eventTime currentTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcurrent_reset : currentTime ≤ resetTime) (hreset_event : resetTime = eventTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (resetTime - currentTime)) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
        capacity weight work currentTime (eventTime - currentTime) ++ suffix)
      (finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
        taggedAdmittedFiniteGPSGapSegmentJobSteps
          resetTime horizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) ∧
      finiteGPSFCFSRunSegmentSteps initial
        (taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime) ++ suffix) =
        finiteGPSFCFSRunSegmentSteps initial
          (finiteGPSFCFSEmptyEndpointSteps
              (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
            taggedAdmittedFiniteGPSGapSegmentJobSteps
              resetTime horizon target z eventTime
              ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
              capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) := by
  subst eventTime
  let fuel := (finiteGPSActiveClasses work).card + 1
  let resetFuel := (finiteGPSActiveClasses (fun _ : Category => 0)).card + 1
  have hdelay_nonneg : 0 ≤ resetTime - currentTime := sub_nonneg.mpr hcurrent_reset
  have hfuel : (finiteGPSActiveClasses work).card < fuel := by
    dsimp [fuel]
    omega
  have hdirect_applied :
      (finiteGPSRunGap fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z resetTime)
        (resetTime - currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hdelay_nonneg hfuel).1
  obtain ⟨directPre, directTerminal, hdirect_steps, hdirect_external,
    _hdirect_workload, hdirect_jobs, _hdirect_time, hdirect_pre_empty⟩ :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_exists_terminal_preceding_source_empty
      start horizon target z resetTime fuel capacity weight work currentTime
      (resetTime - currentTime) hdirect_applied
  have hfence_applied :
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
        (resetTime - currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hdelay_nonneg hfuel).1
  obtain ⟨fencePreSegments, computationalSegment, hfence_segments,
    hcomputational_external, _hcomputational_workload,
    _hcomputational_batch, hcomputational_time⟩ :=
    finiteGPSRunGapSegments_exists_terminal_external_of_batchApplied
      fuel capacity weight work (fun _ => 0) currentTime
      (resetTime - currentTime) hfence_applied
  let fencePreSteps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)) :=
    finiteGPSFCFSEmptyEndpointSteps fencePreSegments
  let computationalTerminal : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category) :=
    { segment := computationalSegment
      endpointJobs := taggedAdmittedFCFSComputationalEndpointJobs }
  have hempty_endpointJobs :
      (finiteGPSFCFSEmptyEndpointJobs (Class := Category)
        (JobId := TaggedAdmittedSourceJobId Category)) =
        taggedAdmittedFCFSComputationalEndpointJobs := by
    rfl
  have hfence_steps : finiteGPSFCFSEmptyEndpointSteps
      (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
        currentTime (resetTime - currentTime)) =
      fencePreSteps ++ [computationalTerminal] := by
    rw [hfence_segments]
    simp [fencePreSteps, computationalTerminal,
      finiteGPSFCFSEmptyEndpointSteps, hempty_endpointJobs]
  have hdirect_mapped : directPre.map (fun step => step.segment) ++
      [directTerminal.segment] =
      finiteGPSRunGapSegments fuel capacity weight work
        (taggedAdmittedBatchAt start horizon target z resetTime)
        currentTime (resetTime - currentTime) := by
    calc
      directPre.map (fun step => step.segment) ++ [directTerminal.segment] =
          (taggedAdmittedFiniteGPSGapSegmentJobSteps
            start horizon target z resetTime fuel capacity weight work currentTime
            (resetTime - currentTime)).map (fun step => step.segment) := by
            rw [hdirect_steps]
            simp
      _ = finiteGPSRunGapSegments fuel capacity weight work
          (taggedAdmittedBatchAt start horizon target z resetTime)
          currentTime (resetTime - currentTime) :=
        taggedAdmittedFiniteGPSGapSegmentJobSteps_segments
          start horizon target z resetTime fuel capacity weight work currentTime
          (resetTime - currentTime)
  have hraw_related :=
    finiteGPSRunGapSegments_forall2_fcfsObservableEq_of_endpointBatch
      fuel capacity weight work
      (taggedAdmittedBatchAt start horizon target z resetTime) (fun _ => 0)
      currentTime (resetTime - currentTime)
  rw [← hdirect_mapped, hfence_segments] at hraw_related
  rcases list_forall2_append_singleton_split
      (relation := FiniteGPSExecutionSegment.FCFSObservableEq)
      (directPre.map fun step => step.segment) fencePreSegments
      directTerminal.segment computationalSegment hraw_related with
      ⟨hpre_segments, hterminal_segments⟩
  have hdirect_pre_source_empty : finiteGPSFCFSSourceEmptySteps directPre := by
    intro step hstep i
    rw [hdirect_pre_empty step hstep]
    rfl
  have hfence_pre_source_empty : finiteGPSFCFSSourceEmptySteps fencePreSteps := by
    intro step hstep i
    rcases List.mem_map.mp hstep with ⟨segment, _hsegment, rfl⟩
    rfl
  have hpre_observable : List.Forall₂ FiniteGPSFCFSSegmentJobStep.FCFSObservableEq
      directPre fencePreSteps := by
    apply finiteGPSFCFSSegmentJobSteps_forall2_of_erased_forall2_of_sourceEmpty
      directPre fencePreSteps
    · simpa [fencePreSteps, finiteGPSFCFSEmptyEndpointSteps] using hpre_segments
    · exact hdirect_pre_source_empty
    · exact hfence_pre_source_empty
  have hpre_completion : finiteGPSFCFSCompletionTraceEquivalent initial
      directPre fencePreSteps := by
    simpa [finiteGPSFCFSCompletionTraceEquivalent] using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_of_fcfsObservableEq
        initial directPre fencePreSteps hpre_observable)
  have hpre_final : finiteGPSFCFSRunSegmentSteps initial directPre =
      finiteGPSFCFSRunSegmentSteps initial fencePreSteps :=
    AppliedModelingLib.Probability.Queueing.finiteGPSFCFSRunSegmentSteps_eq_of_fcfsObservableEq
      initial directPre fencePreSteps hpre_observable
  have hdirect_compatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z resetTime fuel capacity weight work currentTime
        (resetTime - currentTime)) :=
    taggedAdmittedFiniteGPSGapSegmentJobSteps_compatible
      start horizon target z resetTime fuel capacity weight work currentTime
      (resetTime - currentTime) initial hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hsource_work_nonneg hdelay_nonneg hinitial_nonneg
      hinitial_matches_work
  have hdirect_pre_compatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work
      directPre := by
    apply finiteGPSFCFSRunSegmentStepsCompatible_prefix_of_append
      initial work directPre [directTerminal]
    simpa [hdirect_steps] using hdirect_compatible
  have hpre_nonnegative :
      (finiteGPSFCFSRunSegmentSteps initial directPre).Nonnegative :=
    finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      initial work directPre hinitial_nonneg hdirect_pre_compatible
  have hdirect_pre_endpoint_pos : ∀ step ∈ directPre, ∀ i job,
      job ∈ step.endpointJobs.jobs i → 0 < job.residualWork := by
    intro step hstep i job hjob
    rw [hdirect_pre_empty step hstep] at hjob
    simp [taggedAdmittedFCFSComputationalEndpointJobs] at hjob
  have hpre_pos : ∀ i job,
      job ∈ (finiteGPSFCFSRunSegmentSteps initial directPre).residualJobs i →
        0 < job.residualWork :=
    finiteGPSFCFSRunSegmentSteps_residualWork_pos initial directPre
      hinitial_pos hdirect_pre_endpoint_pos
  have hfence_compatible : FiniteGPSFCFSRunSegmentStepsCompatible initial work
      (finiteGPSFCFSEmptyEndpointSteps
        (finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
          currentTime (resetTime - currentTime))) :=
    finiteGPSRunGapSegments_emptyEndpointSteps_compatible_of_zeroBatch
      fuel capacity weight work currentTime (resetTime - currentTime) initial
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hdelay_nonneg
      hinitial_nonneg hinitial_matches_work
  have hcomputational_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps initial fencePreSteps)
      (finiteGPSFCFSSegmentStepsEndpointWorkload work fencePreSteps)
      [computationalTerminal] := by
    apply finiteGPSFCFSRunSegmentStepsCompatible_suffix_of_append
      initial work fencePreSteps [computationalTerminal]
    simpa [hfence_steps] using hfence_compatible
  have hcomputational_service_nonneg : ∀ i,
      0 ≤ computationalTerminal.segment.serviceIncrement i := by
    intro i
    exact hcomputational_compatible.2.2.2.2.1 i
  let realEndpoint : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category) :=
    taggedAdmittedGPSZeroDelayFenceRealEndpointStep
      resetTime horizon target z resetTime capacity weight resetTime 0
  have hreal_steps : taggedAdmittedFiniteGPSGapSegmentJobSteps
      resetTime horizon target z resetTime resetFuel capacity weight
      (fun _ => 0) resetTime (resetTime - resetTime) = [realEndpoint] := by
    simpa [resetFuel, realEndpoint] using
      (taggedAdmittedFiniteGPSGapSegmentJobSteps_zeroStart_zeroDelay
        resetTime horizon target z resetTime capacity weight)
  have hterminal_jobs : directTerminal.endpointJobs = realEndpoint.endpointJobs := by
    calc
      directTerminal.endpointJobs =
          taggedAdmittedFCFSJobsAt start horizon target z resetTime := hdirect_jobs
      _ = taggedAdmittedFCFSJobsAt resetTime horizon target z resetTime :=
        taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
          start resetTime horizon target z htarget_good hstart_reset resetTime le_rfl
      _ = realEndpoint.endpointJobs := by
        rfl
  have hreal_service_zero : ∀ i, realEndpoint.segment.serviceIncrement i = 0 := by
    intro i
    simp [realEndpoint, taggedAdmittedGPSZeroDelayFenceRealEndpointStep,
      finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
      finiteGPSActiveClasses, finiteGPSServiceIncrement,
      finiteGPSRemainingAfter]
  have hreal_external : realEndpoint.segment.endpointIsExternalBatch = true := by
    dsimp [realEndpoint, taggedAdmittedGPSZeroDelayFenceRealEndpointStep]
    apply finiteGPSBuildExecutionSegment_endpointIsExternalBatch_iff
      capacity weight (fun _ : Category => 0)
      (taggedAdmittedBatchAt resetTime horizon target z resetTime) resetTime 0 |>.mpr
    simp [finiteGPSNextStepDuration, finiteGPSActiveClasses]
  have hreal_duration : realEndpoint.segment.duration = 0 := by
    simp [realEndpoint, taggedAdmittedGPSZeroDelayFenceRealEndpointStep,
      finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
      finiteGPSActiveClasses]
  have hreal_start : realEndpoint.segment.startTime =
      finiteGPSExecutionSegmentEndTime computationalTerminal.segment := by
    change resetTime + 0 = finiteGPSExecutionSegmentEndTime computationalSegment
    rw [hcomputational_time]
    ring
  have hstutter : FiniteGPSFCFSZeroDelayFenceStutter
      directTerminal computationalTerminal realEndpoint := by
    refine ⟨?_, ?_, hreal_service_zero, hterminal_jobs, hdirect_external,
      ?_, hreal_external, hreal_duration, hreal_start⟩
    · exact hterminal_segments
    · intro i
      rfl
    · exact hcomputational_external
  have hterminal_completion : finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps initial directPre)
      ([directTerminal] ++ suffix)
      ([computationalTerminal, realEndpoint] ++ suffix) := by
    simpa [finiteGPSFCFSCompletionTraceEquivalent] using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_of_zeroDelayFenceStutter_append
        (finiteGPSFCFSRunSegmentSteps initial directPre)
        directTerminal computationalTerminal realEndpoint suffix hstutter
        hpre_nonnegative hpre_pos hcomputational_service_nonneg)
  have hterminal_final : finiteGPSFCFSRunSegmentSteps
      (finiteGPSFCFSRunSegmentSteps initial directPre) [directTerminal] =
      finiteGPSFCFSRunSegmentSteps
        (finiteGPSFCFSRunSegmentSteps initial directPre)
        [computationalTerminal, realEndpoint] :=
    AppliedModelingLib.Probability.Queueing.finiteGPSFCFSRunSegmentSteps_eq_of_zeroDelayFenceStutter
      (finiteGPSFCFSRunSegmentSteps initial directPre)
      directTerminal computationalTerminal realEndpoint hstutter
      hpre_nonnegative hcomputational_service_nonneg
  have hprefix_extended : finiteGPSFCFSCompletionTraceEquivalent initial
      (directPre ++ ([directTerminal] ++ suffix))
      (fencePreSteps ++ ([directTerminal] ++ suffix)) :=
    finiteGPSFCFSCompletionTraceEquivalent_append_right_of_finalLedger_eq_local
      initial directPre fencePreSteps ([directTerminal] ++ suffix)
      hpre_completion hpre_final
  have hright_extended : finiteGPSFCFSCompletionTraceEquivalent initial
      (fencePreSteps ++ ([directTerminal] ++ suffix))
      (fencePreSteps ++ ([computationalTerminal, realEndpoint] ++ suffix)) := by
    have hterminal_completion_from_fence : finiteGPSFCFSCompletionTraceEquivalent
        (finiteGPSFCFSRunSegmentSteps initial fencePreSteps)
        ([directTerminal] ++ suffix)
        ([computationalTerminal, realEndpoint] ++ suffix) := by
      rw [← hpre_final]
      exact hterminal_completion
    simpa [finiteGPSFCFSCompletionTraceEquivalent,
      AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent] using
      (AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_append_left
        initial fencePreSteps ([directTerminal] ++ suffix)
        ([computationalTerminal, realEndpoint] ++ suffix) hterminal_completion_from_fence)
  have hbase_final : finiteGPSFCFSRunSegmentSteps initial
      (directPre ++ [directTerminal]) =
      finiteGPSFCFSRunSegmentSteps initial
        (fencePreSteps ++ [computationalTerminal, realEndpoint]) := by
    calc
      finiteGPSFCFSRunSegmentSteps initial (directPre ++ [directTerminal]) =
          finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial directPre) [directTerminal] := by
            rw [finiteGPSFCFSRunSegmentSteps_append]
      _ = finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial fencePreSteps) [directTerminal] := by
            rw [hpre_final]
      _ = finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial directPre)
            [computationalTerminal, realEndpoint] := by
            rw [← hpre_final]
            exact hterminal_final
      _ = finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial fencePreSteps)
            [computationalTerminal, realEndpoint] := by
            rw [hpre_final]
      _ = finiteGPSFCFSRunSegmentSteps initial
            (fencePreSteps ++ [computationalTerminal, realEndpoint]) := by
            exact (finiteGPSFCFSRunSegmentSteps_append initial fencePreSteps
              [computationalTerminal, realEndpoint]).symm
  have hbase_final_with_suffix : finiteGPSFCFSRunSegmentSteps initial
      ((directPre ++ [directTerminal]) ++ suffix) =
      finiteGPSFCFSRunSegmentSteps initial
        ((fencePreSteps ++ [computationalTerminal, realEndpoint]) ++ suffix) := by
    calc
      finiteGPSFCFSRunSegmentSteps initial ((directPre ++ [directTerminal]) ++ suffix) =
          finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial (directPre ++ [directTerminal])) suffix := by
            rw [finiteGPSFCFSRunSegmentSteps_append]
      _ = finiteGPSFCFSRunSegmentSteps
            (finiteGPSFCFSRunSegmentSteps initial
              (fencePreSteps ++ [computationalTerminal, realEndpoint])) suffix := by
            rw [hbase_final]
      _ = finiteGPSFCFSRunSegmentSteps initial
            ((fencePreSteps ++ [computationalTerminal, realEndpoint]) ++ suffix) := by
            exact (finiteGPSFCFSRunSegmentSteps_append initial
              (fencePreSteps ++ [computationalTerminal, realEndpoint]) suffix).symm
  constructor
  · intro i
    rw [hdirect_steps, hfence_steps, hreal_steps]
    simpa [List.append_assoc] using (hprefix_extended i).trans (hright_extended i)
  · rw [hdirect_steps, hfence_steps, hreal_steps]
    simpa [List.append_assoc] using hbase_final_with_suffix

/-- A physical source gap crossing a computational reset fence has one
semantic FCFS refinement irrespective of whether its first retained source
batch is strictly after the fence or lands at the fence itself.  The equality
case is handled by an executable zero-duration source admission, not by
assuming a positive interarrival gap. -/
private theorem taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_aggregateDrainFence
    (start resetTime horizon eventTime currentTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight work : Category → ℝ)
    (initial : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (suffix : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcurrent_reset : currentTime ≤ resetTime) (hreset_event : resetTime ≤ eventTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hinitial_nonneg : initial.Nonnegative)
    (hinitial_matches_work : ∀ i, initial.classWork i = work i)
    (hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork)
    (haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (resetTime - currentTime)) :
    finiteGPSFCFSCompletionTraceEquivalent initial
      (taggedAdmittedFiniteGPSGapSegmentJobSteps
        start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
        capacity weight work currentTime (eventTime - currentTime) ++ suffix)
      (finiteGPSFCFSEmptyEndpointSteps
          (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
        taggedAdmittedFiniteGPSGapSegmentJobSteps
          resetTime horizon target z eventTime
          ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) ∧
      finiteGPSFCFSRunSegmentSteps initial
        (taggedAdmittedFiniteGPSGapSegmentJobSteps
          start horizon target z eventTime ((finiteGPSActiveClasses work).card + 1)
          capacity weight work currentTime (eventTime - currentTime) ++ suffix) =
        finiteGPSFCFSRunSegmentSteps initial
          (finiteGPSFCFSEmptyEndpointSteps
              (finiteGPSRunGapSegments ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (fun _ => 0) currentTime (resetTime - currentTime)) ++
            taggedAdmittedFiniteGPSGapSegmentJobSteps
              resetTime horizon target z eventTime
              ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
              capacity weight (fun _ => 0) resetTime (eventTime - resetTime) ++ suffix) := by
  rcases hreset_event.lt_or_eq with hstrict | heq
  · exact taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_strictAggregateDrainFence
      start resetTime horizon eventTime currentTime target z capacity weight work initial suffix
      htarget_good hstart_reset hreset_horizon hcurrent_reset hstrict hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg hsource_work_nonneg hinitial_nonneg
      hinitial_matches_work hinitial_pos haggregate_drain
  · exact taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_zeroDelayAggregateDrainFence
      start resetTime horizon eventTime currentTime target z capacity weight work initial suffix
      htarget_good hstart_reset hreset_horizon hcurrent_reset heq hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg hsource_work_nonneg hinitial_nonneg
      hinitial_matches_work hinitial_pos haggregate_drain

/-- The concrete post-batch workload of a drain-certified crossing gap is
exactly the workload obtained by first draining to the physical reset and
then applying that same batch from zero.  This is a runner-state equality;
it introduces no source event at the reset. -/
private theorem finiteGPSRunGap_workload_eq_zeroStart_of_aggregateDrainFence
    (capacity : ℝ) (weight work batchWork : Category → ℝ)
    (currentTime resetTime eventTime : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ k, 0 ≤ work k)
    (hcurrent_reset : currentTime ≤ resetTime)
    (hreset_event : resetTime ≤ eventTime)
    (haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (resetTime - currentTime)) :
    (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
      capacity weight work batchWork (eventTime - currentTime)).workload =
      (finiteGPSRunGap ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
        capacity weight (fun _ => 0) batchWork (eventTime - resetTime)).workload := by
  let fuel := (finiteGPSActiveClasses work).card + 1
  let fence := finiteGPSRunGap fuel capacity weight work (fun _ => 0)
    (resetTime - currentTime)
  have hfirst_nonneg : 0 ≤ resetTime - currentTime := sub_nonneg.mpr hcurrent_reset
  have hsecond_nonneg : 0 ≤ eventTime - resetTime := sub_nonneg.mpr hreset_event
  have hfuel : (finiteGPSActiveClasses work).card < fuel := by
    dsimp [fuel]
    omega
  have hfence_zero : ∀ i, fence.workload i = 0 := by
    simpa [fence, fuel] using
      (finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
        fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hfirst_nonneg haggregate_drain hfuel)
  have hfence_workload : fence.workload = fun _ : Category => 0 := by
    funext i
    exact hfence_zero i
  have hsplit := finiteGPSRunGap_fields_eq_splitAtZeroFence_of_aggregate_drain
    capacity weight work batchWork (resetTime - currentTime) (eventTime - resetTime)
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hfirst_nonneg hsecond_nonneg
    haggregate_drain
  have hdelay : eventTime - currentTime =
      (resetTime - currentTime) + (eventTime - resetTime) := by ring
  funext i
  calc
    (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work batchWork (eventTime - currentTime)).workload i =
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work batchWork
          ((resetTime - currentTime) + (eventTime - resetTime))).workload i := by
            rw [hdelay]
    _ = (finiteGPSRunGapSplitAtZeroFence capacity weight work batchWork
          (resetTime - currentTime) (eventTime - resetTime)).workload i := hsplit.1 i
    _ = (finiteGPSRunGap ((finiteGPSActiveClasses (fun _ : Category => 0)).card + 1)
          capacity weight (fun _ => 0) batchWork (eventTime - resetTime)).workload i := by
          simp only [finiteGPSRunGapSplitAtZeroFence]
          rw [show finiteGPSRunGap
              ((finiteGPSActiveClasses work).card + 1) capacity weight work
              (fun _ : Category => 0) (resetTime - currentTime) = fence by rfl,
            hfence_workload]

/-- The literal source selector is invariant under a physical closed-prefix
reset.  The proof chooses the first retained *source* epoch internally,
refines precisely that executable crossing gap, and transports the remaining
literal source batches by their actual endpoint data.  No caller supplies a
trace split, an artificial crossing event, or a scheduler-specific witness. -/
private theorem taggedAdmittedFiniteGPSPreTerminalFirstTagCompletion?_eq_reset_of_closedFencePrefix
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hreset_zero : resetTime ≤ 0) (hhorizon_pos : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (haggregate_drain : finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight (fun _ => 0)).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight (fun _ => 0)).currentTime))
    (hclosed_prefix : finiteGPSFCFSRunSegmentSteps
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start resetTime target z htarget_good capacity weight) =
        taggedAdmittedEmptyFCFSLedger) :
    taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0))) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
            resetTime horizon target z htarget_good capacity weight (fun _ => 0))) := by
  let hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z :=
    ⟨fun n => (hsource_work_pos.1 n).le,
      fun k n => (hsource_work_pos.2 k n).le⟩
  let prefixTimes :=
    (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times
  let suffixTimes :=
    (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
  let prefixRaw := finiteGPSRunBatchTrace capacity weight
    (taggedAdmittedBatchAt start horizon target z) start (fun _ => 0) prefixTimes
  let prefixSteps := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    start horizon target z capacity weight start (fun _ => 0) prefixTimes
  let physicalPrefixSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start resetTime target z htarget_good capacity weight (fun _ => 0)
  have hempty_nonnegative :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hempty_matches_zero : ∀ i,
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).classWork i = 0 := by
    intro i
    simp [taggedAdmittedEmptyFCFSLedger, FiniteGPSFCFSJobLedger.classWork,
      finiteGPSFCFSJobWork]
  have hprefix_steps_eq : prefixSteps = physicalPrefixSteps := by
    dsimp [prefixSteps, physicalPrefixSteps, prefixTimes]
    unfold taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    apply taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceInputs_eq
      start horizon start resetTime target z capacity weight (fun _ => 0) start
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times
    · intro eventTime heventTime
      apply taggedAdmittedBatchAt_eq_prefix_of_lt_reset
        start resetTime horizon target z htarget_good hreset_horizon eventTime
      apply taggedAdmittedBatchTimes_prefix_lt_reset start resetTime target z htarget_good
        eventTime
      exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
        (by simpa [taggedAdmittedExternalBatchTrace,
          taggedAdmittedBatchTimeTrace] using heventTime)
    · intro eventTime heventTime
      apply taggedAdmittedFCFSJobsAt_eq_prefix_of_lt_reset
        start resetTime horizon target z htarget_good hreset_horizon eventTime
      apply taggedAdmittedBatchTimes_prefix_lt_reset start resetTime target z htarget_good
        eventTime
      exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
        (by simpa [taggedAdmittedExternalBatchTrace,
          taggedAdmittedBatchTimeTrace] using heventTime)
  have hprefix_raw_eq : prefixRaw =
      taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight (fun _ => 0) := by
    dsimp [prefixRaw, prefixTimes]
    simpa [taggedAdmittedExternalBatchTrace] using
      (taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
        start resetTime horizon target z htarget_good capacity weight (fun _ => 0)
        hreset_horizon)
  let initial := finiteGPSFCFSRunSegmentSteps
    (taggedAdmittedEmptyFCFSLedger (Category := Category)) physicalPrefixSteps
  have hphysical_prefix_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) (fun _ => 0)
      physicalPrefixSteps := by
    dsimp [physicalPrefixSteps]
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
      start resetTime target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one (by intro i; norm_num)
      hsource_work_nonneg hempty_nonnegative (by intro i; exact hempty_matches_zero i)
  have hinitial_nonnegative : initial.Nonnegative := by
    dsimp [initial]
    exact finiteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) (fun _ => 0)
      physicalPrefixSteps hempty_nonnegative hphysical_prefix_compatible
  have hinitial_matches_prefixRaw : ∀ i, initial.classWork i = prefixRaw.workload i := by
    intro i
    dsimp [initial, physicalPrefixSteps]
    rw [hprefix_raw_eq]
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_fold_classWork_eq_history
      start resetTime target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one (by intro j; norm_num)
      hsource_work_nonneg hempty_nonnegative (by intro j; exact hempty_matches_zero j) i
  have hinitial_pos : ∀ i job, job ∈ initial.residualJobs i → 0 < job.residualWork := by
    dsimp [initial]
    apply finiteGPSFCFSRunSegmentSteps_residualWork_pos
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) physicalPrefixSteps
    · intro i job hjob
      simp [taggedAdmittedEmptyFCFSLedger] at hjob
    · dsimp [physicalPrefixSteps]
      exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointJobs_residualWork_pos
        start resetTime target z htarget_good hsource_work_pos capacity weight (fun _ => 0)
  have hprefix_work_nonneg : ∀ i, 0 ≤ prefixRaw.workload i := by
    intro i
    rw [hprefix_raw_eq]
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start resetTime target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg i
  have hprefix_current_reset : prefixRaw.currentTime ≤ resetTime := by
    rw [hprefix_raw_eq]
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start resetTime target z htarget_good capacity weight (fun _ => 0) hstart_reset
  let prefixFenceSteps := finiteGPSFCFSEmptyEndpointSteps
    (JobId := TaggedAdmittedSourceJobId Category)
    (finiteGPSRunGapSegments ((finiteGPSActiveClasses prefixRaw.workload).card + 1)
      capacity weight prefixRaw.workload (fun _ => 0) prefixRaw.currentTime
      (resetTime - prefixRaw.currentTime))
  have hphysical_prefix_closed_steps :
      physicalPrefixSteps ++ prefixFenceSteps =
        taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          start resetTime target z htarget_good capacity weight := by
    dsimp [physicalPrefixSteps, prefixFenceSteps]
    rw [hprefix_raw_eq]
    rfl
  have hphysical_prefix_closed : finiteGPSFCFSRunSegmentSteps
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (physicalPrefixSteps ++ prefixFenceSteps) =
        taggedAdmittedEmptyFCFSLedger := by
    rw [hphysical_prefix_closed_steps]
    exact hclosed_prefix
  have hphysical_prefix_step_no_tag : ∀ step ∈ physicalPrefixSteps,
      ∀ job ∈ step.endpointJobs.jobs target,
        decide (job.identifier = (target, 0)) ≠ true := by
    dsimp [physicalPrefixSteps]
    apply taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_no_tag_of_times_ne_zero
      start resetTime target z capacity weight (fun _ => 0) start
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times
    intro eventTime heventTime hevent_zero
    subst eventTime
    have hlt := taggedAdmittedExternalBatchTrace_time_lt_horizon
      start resetTime target z htarget_good 0 (by
        simpa [taggedAdmittedExternalBatchTrace] using heventTime)
    linarith
  have hphysical_prefix_completion_no_tag : ∀ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (physicalPrefixSteps ++ prefixFenceSteps),
      completion.identifier ≠ (target, 0) := by
    intro completion hcompletion hidentifier
    have hno_key := finiteGPSFCFSRunSegmentStepsClassCompletions_forall_not_key
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (physicalPrefixSteps ++ prefixFenceSteps) target
      (by
        intro job hjob
        simp [taggedAdmittedEmptyFCFSLedger] at hjob)
      (by
        intro step hstep job hjob
        rcases List.mem_append.mp hstep with hprefix | hfence
        · exact hphysical_prefix_step_no_tag step hprefix job hjob
        · dsimp [prefixFenceSteps] at hfence
          rcases List.mem_map.mp hfence with ⟨segment, _hsegment, rfl⟩
          simp [finiteGPSFCFSEmptyEndpointJobs] at hjob)
      completion hcompletion
    simp [hidentifier] at hno_key
  have hphysical_prefix_no_tag : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (physicalPrefixSteps ++ prefixFenceSteps)) = none :=
    taggedAdmittedFiniteGPSFirstTagCompletion?_eq_none_of_forall_identifier_ne
      target _ hphysical_prefix_completion_no_tag
  have hsuffix_nonempty : suffixTimes ≠ [] := by
    intro hsuffix_empty
    have hzero_mem : (0 : ℝ) ∈ suffixTimes := by
      dsimp [suffixTimes]
      change 0 ∈ taggedAdmittedBatchTimeTrace resetTime horizon target z
      apply (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr
      apply (mem_taggedAdmittedBatchTimes_iff resetTime horizon target z 0).mpr
      refine ⟨(target, 0), ?_, taggedAdmittedSourceArrival_target_zero target z⟩
      exact (mem_taggedAdmittedTargetSourceId_iff resetTime horizon target z
        htarget_good).mpr ⟨hreset_zero, hhorizon_pos⟩
    rw [hsuffix_empty] at hzero_mem
    simp at hzero_mem
  obtain ⟨eventTime, tail, hsuffix_times⟩ :
      ∃ eventTime tail, suffixTimes = eventTime :: tail := by
    cases htimes : suffixTimes with
    | nil => exact (hsuffix_nonempty htimes).elim
    | cons eventTime tail => exact ⟨eventTime, tail, rfl⟩
  have heventTime_ge_reset : resetTime ≤ eventTime := by
    have heventTime_mem : eventTime ∈ suffixTimes := by
      rw [hsuffix_times]
      simp
    apply taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime
    apply (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
    change eventTime ∈ taggedAdmittedBatchTimeTrace resetTime horizon target z at heventTime_mem
    exact heventTime_mem
  have hfull_delay_nonneg : 0 ≤ eventTime - prefixRaw.currentTime :=
    sub_nonneg.mpr (hprefix_current_reset.trans heventTime_ge_reset)
  let fuel := (finiteGPSActiveClasses prefixRaw.workload).card + 1
  let resetFuel := (finiteGPSActiveClasses (fun _ : Category => 0)).card + 1
  have hfuel : (finiteGPSActiveClasses prefixRaw.workload).card < fuel := by
    dsimp [fuel]
    omega
  have hdirect_applied :
      (finiteGPSRunGap fuel capacity weight prefixRaw.workload
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - prefixRaw.currentTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      fuel hcapacity hweight_pos htotal_weight_le_one hprefix_work_nonneg
      hfull_delay_nonneg hfuel).1
  have hreset_delay_nonneg : 0 ≤ eventTime - resetTime :=
    sub_nonneg.mpr heventTime_ge_reset
  have hresetFuel : (finiteGPSActiveClasses (fun _ : Category => 0)).card < resetFuel := by
    dsimp [resetFuel]
    omega
  have hreset_applied :
      (finiteGPSRunGap resetFuel capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt resetTime horizon target z eventTime)
        (eventTime - resetTime)).batchApplied = true := by
    exact (finiteGPSRunGap_terminates_of_activeCard_lt
      resetFuel hcapacity hweight_pos htotal_weight_le_one (by intro i; norm_num)
      hreset_delay_nonneg hresetFuel).1
  let directGap := taggedAdmittedFiniteGPSGapSegmentJobSteps
    start horizon target z eventTime fuel capacity weight prefixRaw.workload
    prefixRaw.currentTime (eventTime - prefixRaw.currentTime)
  let directTail := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    start horizon target z capacity weight eventTime
    (finiteGPSRunGap fuel capacity weight prefixRaw.workload
      (taggedAdmittedBatchAt start horizon target z eventTime)
      (eventTime - prefixRaw.currentTime)).workload tail
  let resetGap := taggedAdmittedFiniteGPSGapSegmentJobSteps
    resetTime horizon target z eventTime resetFuel capacity weight (fun _ => 0)
    resetTime (eventTime - resetTime)
  let resetTail := taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
    resetTime horizon target z capacity weight eventTime
    (finiteGPSRunGap resetFuel capacity weight (fun _ => 0)
      (taggedAdmittedBatchAt resetTime horizon target z eventTime)
      (eventTime - resetTime)).workload tail
  have hbatch_event : taggedAdmittedBatchAt start horizon target z eventTime =
      taggedAdmittedBatchAt resetTime horizon target z eventTime :=
    taggedAdmittedBatchAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime heventTime_ge_reset
  have hendpoint_event : taggedAdmittedFCFSJobsAt start horizon target z eventTime =
      taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime :=
    taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime heventTime_ge_reset
  have hpost_work_eq :
      (finiteGPSRunGap fuel capacity weight prefixRaw.workload
        (taggedAdmittedBatchAt start horizon target z eventTime)
        (eventTime - prefixRaw.currentTime)).workload =
      (finiteGPSRunGap resetFuel capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt resetTime horizon target z eventTime)
        (eventTime - resetTime)).workload := by
    rw [hbatch_event]
    simpa [fuel, resetFuel] using
      (finiteGPSRunGap_workload_eq_zeroStart_of_aggregateDrainFence
        capacity weight prefixRaw.workload
        (taggedAdmittedBatchAt resetTime horizon target z eventTime)
        prefixRaw.currentTime resetTime eventTime
        hcapacity hweight_pos htotal_weight_le_one hprefix_work_nonneg
        hprefix_current_reset heventTime_ge_reset (by simpa [hprefix_raw_eq] using
          haggregate_drain))
  have htail_steps_eq : directTail = resetTail := by
    dsimp [directTail, resetTail]
    rw [hpost_work_eq]
    apply taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_eq_of_sourceInputs_eq
      start horizon resetTime horizon target z capacity weight
      (finiteGPSRunGap resetFuel capacity weight (fun _ => 0)
        (taggedAdmittedBatchAt resetTime horizon target z eventTime)
        (eventTime - resetTime)).workload eventTime tail
    · intro laterTime hlaterTime
      apply taggedAdmittedBatchAt_eq_suffix_of_reset_le
        start resetTime horizon target z htarget_good hstart_reset laterTime
      apply le_trans heventTime_ge_reset
      have hchronological :=
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      rw [show (taggedAdmittedExternalBatchTrace
          resetTime horizon target z htarget_good).times = eventTime :: tail by
        simpa [suffixTimes] using hsuffix_times] at hchronological
      exact finiteGPSChronologicalFrom_start_le eventTime tail hchronological.2
        laterTime hlaterTime
    · intro laterTime hlaterTime
      apply taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
        start resetTime horizon target z htarget_good hstart_reset laterTime
      apply le_trans heventTime_ge_reset
      have hchronological :=
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      rw [show (taggedAdmittedExternalBatchTrace
          resetTime horizon target z htarget_good).times = eventTime :: tail by
        simpa [suffixTimes] using hsuffix_times] at hchronological
      exact finiteGPSChronologicalFrom_start_le eventTime tail hchronological.2
        laterTime hlaterTime
  have hdirect_cons : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      start horizon target z capacity weight prefixRaw.currentTime prefixRaw.workload
      (eventTime :: tail) = directGap ++ directTail := by
    simpa [directGap, directTail] using
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        start horizon target z capacity weight prefixRaw.workload
        prefixRaw.currentTime eventTime tail hdirect_applied)
  have hreset_cons : taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
      resetTime horizon target z capacity weight resetTime (fun _ => 0)
      (eventTime :: tail) = resetGap ++ resetTail := by
    simpa [resetGap, resetTail] using
      (taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps_cons_of_batchApplied
        resetTime horizon target z capacity weight (fun _ => 0)
        resetTime eventTime tail hreset_applied)
  have hfull_source_steps : taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      start horizon target z htarget_good capacity weight (fun _ => 0) =
      physicalPrefixSteps ++ (directGap ++ directTail) := by
    have hfactor := taggedAdmittedFiniteGPSPreTerminalFCFSSteps_eq_fullSourceRestartAtReset
      start resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
      (by intro i; norm_num) hsource_work_nonneg
    change taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight (fun _ => 0) =
      prefixSteps ++ taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        start horizon target z capacity weight prefixRaw.currentTime prefixRaw.workload
        suffixTimes at hfactor
    rw [hsuffix_times, hdirect_cons, hprefix_steps_eq] at hfactor
    exact hfactor
  have hreset_source_steps : taggedAdmittedFiniteGPSPreTerminalFCFSSteps
      resetTime horizon target z htarget_good capacity weight (fun _ => 0) =
      resetGap ++ resetTail := by
    unfold taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    change taggedAdmittedFiniteGPSBatchTraceSegmentJobSteps
        resetTime horizon target z capacity weight resetTime (fun _ => 0) suffixTimes = _
    rw [hsuffix_times, hreset_cons]
  have hcrossing :=
    taggedAdmittedFiniteGPSGap_completionTraceAndFinalLedger_eq_of_aggregateDrainFence
      start resetTime horizon eventTime prefixRaw.currentTime target z
      capacity weight prefixRaw.workload initial directTail htarget_good hstart_reset
      hreset_horizon hprefix_current_reset heventTime_ge_reset hcapacity hweight_pos
      htotal_weight_le_one hprefix_work_nonneg hsource_work_nonneg hinitial_nonnegative
      hinitial_matches_prefixRaw hinitial_pos (by simpa [hprefix_raw_eq] using haggregate_drain)
  have hgap_equivalent : finiteGPSFCFSCompletionTraceEquivalent initial
      (directGap ++ directTail)
      (prefixFenceSteps ++ (resetGap ++ directTail)) := by
    simpa [directGap, resetGap, prefixFenceSteps, fuel, resetFuel,
      List.append_assoc] using hcrossing.1
  have hsource_equivalent : finiteGPSFCFSCompletionTraceEquivalent
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (physicalPrefixSteps ++ (directGap ++ directTail))
      ((physicalPrefixSteps ++ prefixFenceSteps) ++ (resetGap ++ resetTail)) := by
    have hgap_equivalent' : finiteGPSFCFSCompletionTraceEquivalent initial
        (directGap ++ directTail)
        (prefixFenceSteps ++ (resetGap ++ resetTail)) := by
      rw [← htail_steps_eq]
      exact hgap_equivalent
    have hleft := finiteGPSFCFSCompletionTraceEquivalent_append_left
      (taggedAdmittedEmptyFCFSLedger (Category := Category)) physicalPrefixSteps
      (directGap ++ directTail) (prefixFenceSteps ++ (resetGap ++ resetTail))
      hgap_equivalent'
    simpa [List.append_assoc] using hleft
  have hsource_selector :=
    taggedAdmittedFiniteGPSFirstTagCompletion?_eq_of_completionTraceEquivalent
      target (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (physicalPrefixSteps ++ (directGap ++ directTail))
      ((physicalPrefixSteps ++ prefixFenceSteps) ++ (resetGap ++ resetTail))
      hsource_equivalent
  have hrestart_selector :=
    taggedAdmittedFiniteGPSFirstTagCompletion?_restart_of_stepTrace_append
      target (physicalPrefixSteps ++ prefixFenceSteps) (resetGap ++ resetTail)
      hphysical_prefix_closed hphysical_prefix_no_tag
  calc
    taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
            start horizon target z htarget_good capacity weight (fun _ => 0))) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (physicalPrefixSteps ++ (directGap ++ directTail))) := by
            rw [hfull_source_steps]
    _ = taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          ((physicalPrefixSteps ++ prefixFenceSteps) ++ (resetGap ++ resetTail))) :=
      hsource_selector
    _ = taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (resetGap ++ resetTail)) := hrestart_selector
    _ = taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
            resetTime horizon target z htarget_good capacity weight (fun _ => 0))) := by
      rw [hreset_source_steps]

/-- A diagonal finite response agrees exactly with its physical reset-start
replay once the latter's literal source preterminal trace has selected the
Palm completion.  The global-reset and source-selection inputs are physical;
all source-time splitting, gap crossing, and FCFS ledger bookkeeping are
internal to the checked proof. -/
theorem taggedAdmittedGPSDiagonalFiniteResponse_eq_resetHorizonResponse_of_pastGlobalMax_and_preterminalSelection
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (resetTime : ℝ) (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime)
    (selected : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category))
    (hreset_preterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          resetTime (taggedAdmittedGPSDiagonalHorizon N) target z htarget_good
          G.capacity G.weight (fun _ => 0))) = some selected) :
    taggedAdmittedGPSDiagonalFiniteResponse target z htarget_good G.capacity G.weight N =
      taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight := by
  let hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z :=
    ⟨fun n => (hsource_work_pos.1 n).le,
      fun k n => (hsource_work_pos.2 k n).le⟩
  have hreset_horizon : resetTime ≤ taggedAdmittedGPSDiagonalHorizon N :=
    hreset_zero.trans (taggedAdmittedGPSDiagonalHorizon_pos N).le
  have hclosed_workload : ∀ i,
      (taggedAdmittedFiniteGPSRun (taggedAdmittedGPSDiagonalStart N) resetTime
        target z htarget_good G.capacity G.weight (fun _ => 0)
        hdiagonal_before_reset).workload i = 0 :=
    taggedAdmittedFiniteGPSDiagonalPrefix_all_work_eq_zero_of_pastGlobalMax
      M G target z htarget_good hsource_work_nonneg resetTime hreset_zero hglobal
      N hdiagonal_before_reset
  have haggregate_drain : finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun
        (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
        G.capacity G.weight (fun _ => 0)).workload ≤
      G.capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun
          (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
          G.capacity G.weight (fun _ => 0)).currentTime) :=
    taggedAdmittedFiniteGPSPrefix_aggregate_drain_of_closed_prefix_workload_zero
      (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
      G.capacity G.weight (fun _ => 0) hdiagonal_before_reset
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      (by intro i; norm_num) hsource_work_nonneg hclosed_workload
  have hclosed_prefix : finiteGPSFCFSRunSegmentSteps
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
        G.capacity G.weight) = taggedAdmittedEmptyFCFSLedger := by
    simpa [taggedAdmittedFiniteGPSHorizonFenceFinalLedger] using
      (taggedAdmittedFiniteGPSDiagonalHorizonFenceFinalLedger_eq_empty_of_pastGlobalMax
        M G target z htarget_good hsource_work_pos resetTime hreset_zero hglobal
        N hdiagonal_before_reset)
  have hpreterminal_selector_eq :=
    taggedAdmittedFiniteGPSPreTerminalFirstTagCompletion?_eq_reset_of_closedFencePrefix
      (taggedAdmittedGPSDiagonalStart N) resetTime
      (taggedAdmittedGPSDiagonalHorizon N) target z htarget_good hsource_work_pos
      G.capacity G.weight hdiagonal_before_reset hreset_horizon hreset_zero
      (taggedAdmittedGPSDiagonalHorizon_pos N) (G.capacity_pos target)
      G.weight_pos G.total_weight_le_one haggregate_drain hclosed_prefix
  have hdiagonal_preterminal_selected : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
          target z htarget_good G.capacity G.weight (fun _ => 0))) = some selected :=
    hpreterminal_selector_eq.trans hreset_preterminal_selected
  have hdiagonal_selected : taggedAdmittedGPSDiagonalTagCompletion?
      target z htarget_good G.capacity G.weight N = some selected := by
    unfold taggedAdmittedGPSDiagonalTagCompletion?
    unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    exact taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
      target
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight (fun _ => 0))
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight)
      selected hdiagonal_preterminal_selected
  have hreset_selected : taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
      resetTime (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight = some selected := by
    unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
    unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    exact taggedAdmittedFiniteGPSFirstTagCompletion?_persists_of_stepTrace_append
      target
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight (fun _ => 0))
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight)
      selected hreset_preterminal_selected
  calc
    taggedAdmittedGPSDiagonalFiniteResponse target z htarget_good G.capacity G.weight N =
        selected.completionTime := by
          unfold taggedAdmittedGPSDiagonalFiniteResponse
          exact taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
            (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
            target z htarget_good G.capacity G.weight selected (by
              simpa [taggedAdmittedGPSDiagonalTagCompletion?] using hdiagonal_selected)
    _ = taggedAdmittedFiniteGPSHorizonFenceTotalResponse
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight :=
      (taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_completionTime_of_some
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight selected hreset_selected).symm

/-- At a source epoch coinciding with a terminal drain, the executable direct
endpoint and the computational-fence-plus-real-endpoint representation form a
zero-delay FCFS stutter.  The returned time equalities anchor the unchanged
literal batch at its actual source epoch. -/
theorem taggedAdmittedGPSZeroDelayFenceStutter_at_sourceEpoch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime drainDelay : ℝ)
    (hterminal : finiteGPSNextStepDuration capacity weight work drainDelay = drainDelay)
    (hsource_epoch : currentTime + drainDelay = eventTime) :
    FiniteGPSFCFSZeroDelayFenceStutter
      (taggedAdmittedGPSZeroDelayFenceDirectStep
        start horizon target z eventTime capacity weight work currentTime drainDelay)
      (taggedAdmittedGPSZeroDelayFenceComputationalStep
        capacity weight work currentTime drainDelay)
      (taggedAdmittedGPSZeroDelayFenceRealEndpointStep
        start horizon target z eventTime capacity weight currentTime drainDelay) ∧
    finiteGPSExecutionSegmentEndTime
      (taggedAdmittedGPSZeroDelayFenceDirectStep
        start horizon target z eventTime capacity weight work currentTime drainDelay).segment =
      eventTime ∧
    finiteGPSExecutionSegmentEndTime
      (taggedAdmittedGPSZeroDelayFenceRealEndpointStep
        start horizon target z eventTime capacity weight currentTime drainDelay).segment =
      eventTime := by
  have hstutter := finiteGPSFCFSZeroDelayFenceStutter_of_terminalDrain
    (JobId := TaggedAdmittedSourceJobId Category)
    capacity weight work (taggedAdmittedBatchAt start horizon target z eventTime)
    currentTime drainDelay (taggedAdmittedFCFSJobsAt start horizon target z eventTime)
    hterminal
  have hdirect_time : finiteGPSExecutionSegmentEndTime
      (taggedAdmittedGPSZeroDelayFenceDirectStep
        start horizon target z eventTime capacity weight work currentTime drainDelay).segment =
      eventTime := by
    calc
      finiteGPSExecutionSegmentEndTime
          (taggedAdmittedGPSZeroDelayFenceDirectStep
            start horizon target z eventTime capacity weight work currentTime drainDelay).segment =
          currentTime + drainDelay := by
            simp [taggedAdmittedGPSZeroDelayFenceDirectStep,
              finiteGPSExecutionSegmentEndTime, finiteGPSBuildExecutionSegment, hterminal]
      _ = eventTime := hsource_epoch
  have hsource_stutter : FiniteGPSFCFSZeroDelayFenceStutter
      (taggedAdmittedGPSZeroDelayFenceDirectStep
        start horizon target z eventTime capacity weight work currentTime drainDelay)
      (taggedAdmittedGPSZeroDelayFenceComputationalStep
        capacity weight work currentTime drainDelay)
      (taggedAdmittedGPSZeroDelayFenceRealEndpointStep
        start horizon target z eventTime capacity weight currentTime drainDelay) := by
    simpa [taggedAdmittedGPSZeroDelayFenceDirectStep,
      taggedAdmittedGPSZeroDelayFenceComputationalStep,
      taggedAdmittedGPSZeroDelayFenceRealEndpointStep,
      taggedAdmittedFCFSComputationalEndpointJobs,
      finiteGPSFCFSEmptyEndpointJobs] using hstutter
  refine ⟨hsource_stutter, hdirect_time, ?_⟩
  rw [FiniteGPSFCFSZeroDelayFenceStutter.realEndpointTime_eq_directEnd
    _ _ _ hsource_stutter]
  exact hdirect_time

/-- Exact source crossing refinement for a zero-delay drain fence.  Its shape
matches the `hcrossing` input of
`taggedAdmittedGPSDiagonalTagCompletion?_eq_resetReplay_of_crossingRefinement`:
the direct crossing has one draining source endpoint, while the reset replay
has its computational drain followed by a distinct zero-duration real source
endpoint and then the same suffix. -/
theorem taggedAdmittedGPSCrossingRefinement_of_zeroDelayFenceStutter
    (before suffix : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (direct computational realEndpoint :
      FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category))
    (hbefore_nonneg :
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before).Nonnegative)
    (hbefore_pos : ∀ i job, job ∈
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before).residualJobs i →
        0 < job.residualWork)
    (hcomputational_service_nonneg : ∀ i,
      0 ≤ computational.segment.serviceIncrement i)
    (hstutter : FiniteGPSFCFSZeroDelayFenceStutter direct computational realEndpoint) :
    finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before)
      ([direct] ++ suffix)
      ([computational] ++ ([realEndpoint] ++ suffix)) := by
  have hcore :=
    AppliedModelingLib.Probability.Queueing.finiteGPSFCFSCompletionTraceEquivalent_of_zeroDelayFenceStutter_append
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before)
      direct computational realEndpoint suffix hstutter hbefore_nonneg hbefore_pos
      hcomputational_service_nonneg
  simpa [finiteGPSFCFSCompletionTraceEquivalent, List.append_assoc] using hcore

/-- The source-labelled terminal-drain specialization of the exact crossing
refinement.  This is the form used under an eventual diagonal-stabilization
argument: every parameter may depend on the diagonal index, but the
completion-trace equality at each qualifying index is exact. -/
theorem taggedAdmittedGPSCrossingRefinement_of_terminalZeroDelay
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) (eventTime : ℝ)
    (capacity : ℝ) (weight work : Category → ℝ)
    (currentTime drainDelay : ℝ)
    (before suffix : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (hterminal : finiteGPSNextStepDuration capacity weight work drainDelay = drainDelay)
    (hsource_epoch : currentTime + drainDelay = eventTime)
    (hbefore_nonneg :
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before).Nonnegative)
    (hbefore_pos : ∀ i job, job ∈
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before).residualJobs i →
        0 < job.residualWork)
    (hcomputational_service_nonneg : ∀ i,
      0 ≤ (taggedAdmittedGPSZeroDelayFenceComputationalStep
        capacity weight work
        currentTime drainDelay).segment.serviceIncrement i) :
    finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before)
      ([taggedAdmittedGPSZeroDelayFenceDirectStep
        start horizon target z eventTime capacity weight work currentTime drainDelay] ++ suffix)
      ([taggedAdmittedGPSZeroDelayFenceComputationalStep
        capacity weight work currentTime drainDelay] ++
        ([taggedAdmittedGPSZeroDelayFenceRealEndpointStep
          start horizon target z eventTime capacity weight currentTime drainDelay] ++ suffix)) := by
  have hstutter :=
    (taggedAdmittedGPSZeroDelayFenceStutter_at_sourceEpoch
      start horizon target z eventTime capacity weight work currentTime drainDelay
      hterminal hsource_epoch).1
  exact taggedAdmittedGPSCrossingRefinement_of_zeroDelayFenceStutter
    before suffix
    (taggedAdmittedGPSZeroDelayFenceDirectStep
      start horizon target z eventTime capacity weight work currentTime drainDelay)
    (taggedAdmittedGPSZeroDelayFenceComputationalStep
      capacity weight work currentTime drainDelay)
    (taggedAdmittedGPSZeroDelayFenceRealEndpointStep
      start horizon target z eventTime capacity weight currentTime drainDelay)
    hbefore_nonneg hbefore_pos hcomputational_service_nonneg hstutter

/-- This is the FCFS-level integration point for a physical global reset in
a diagonal replay.  The only nonstructural input is `hcrossing`: a
completion-trace refinement for the one source gap that crosses `resetTime`.
It retains pre-reset completions in `closing`, begins the retained replay from
the literal empty ledger, and never asserts raw equality of the source-window
step lists.  A source-provenance proof of `hprefix_no_tag` is kept explicit as
well; aggregate closure alone cannot establish it. -/
theorem taggedAdmittedGPSDiagonalTagCompletion?_eq_resetReplay_of_crossingRefinement
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_pos : TaggedAdmittedSourceWorkPositive target z)
    (resetTime : ℝ) (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime)
    (before crossing closing resetReplaySteps : List
      (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)))
    (hfull_steps :
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
          target z htarget_good G.capacity G.weight = before ++ crossing)
    (hclosed_steps :
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          (taggedAdmittedGPSDiagonalStart N) resetTime
          target z htarget_good G.capacity G.weight = before ++ closing)
    (hreset_steps :
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime (taggedAdmittedGPSDiagonalHorizon N)
          target z htarget_good G.capacity G.weight = resetReplaySteps)
    (hprefix_no_tag : taggedAdmittedFiniteGPSFirstTagCompletion? target
      (finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
        (before ++ closing)) = none)
    (hcrossing : finiteGPSFCFSCompletionTraceEquivalent
      (finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category)) before)
      crossing (closing ++ resetReplaySteps)) :
    taggedAdmittedGPSDiagonalTagCompletion?
        target z htarget_good G.capacity G.weight N =
      taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
        resetTime (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight := by
  have hclosed_empty :
      finiteGPSFCFSRunSegmentSteps
        (taggedAdmittedEmptyFCFSLedger (Category := Category))
        (before ++ closing) = taggedAdmittedEmptyFCFSLedger := by
    rw [← hclosed_steps]
    simpa [taggedAdmittedFiniteGPSHorizonFenceFinalLedger] using
      (taggedAdmittedFiniteGPSDiagonalHorizonFenceFinalLedger_eq_empty_of_pastGlobalMax
        M G target z htarget_good hsource_work_pos resetTime hreset_zero hglobal
        N hdiagonal_before_reset)
  have hfull_equivalent : finiteGPSFCFSCompletionTraceEquivalent
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (before ++ crossing) ((before ++ closing) ++ resetReplaySteps) := by
    simpa only [List.append_assoc] using
      (finiteGPSFCFSCompletionTraceEquivalent_append_left
        (taggedAdmittedEmptyFCFSLedger (Category := Category))
        before crossing (closing ++ resetReplaySteps) hcrossing)
  unfold taggedAdmittedGPSDiagonalTagCompletion?
  unfold taggedAdmittedFiniteGPSHorizonFenceTagCompletion?
  unfold taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
  rw [hfull_steps, hreset_steps]
  calc
    taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          (before ++ crossing)) =
      taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          ((before ++ closing) ++ resetReplaySteps)) :=
        taggedAdmittedFiniteGPSFirstTagCompletion?_eq_of_completionTraceEquivalent
          target (taggedAdmittedEmptyFCFSLedger (Category := Category))
          (before ++ crossing) ((before ++ closing) ++ resetReplaySteps)
          hfull_equivalent
    _ = taggedAdmittedFiniteGPSFirstTagCompletion? target
        (finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedEmptyFCFSLedger (Category := Category)) target
          resetReplaySteps) :=
        taggedAdmittedFiniteGPSFirstTagCompletion?_restart_of_stepTrace_append
          target (before ++ closing) resetReplaySteps hclosed_empty hprefix_no_tag

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
