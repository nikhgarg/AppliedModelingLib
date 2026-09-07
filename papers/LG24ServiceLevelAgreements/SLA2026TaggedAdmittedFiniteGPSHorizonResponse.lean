import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSHorizonFence
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSResponse
import Mathlib.Tactic

/-!
# Conditional tagged response through a computational GPS horizon fence

This module appends the executable zero-work horizon fence to the literal
tagged source-to-FCFS trace.  Fence endpoint batches are explicitly empty:
they are computational events, not source arrivals.  The final theorem is
conditional on the actual finite FCFS target queue being nonnegative and
empty in aggregate after that finite trace.  It does not assert that this
condition occurs at a fixed horizon, almost surely, or in stationarity.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Attach the explicitly empty source-job endpoint batch to every segment of
the generic zero-work computational horizon fence. -/
def taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) :=
  (finiteGPSHorizonFenceSegments capacity weight
    (taggedAdmittedFiniteGPSPreTerminalHistory
      start horizon target z htarget_good capacity weight (fun _ => 0)).final
    horizon).map fun segment =>
      { segment := segment
        endpointJobs := taggedAdmittedFCFSComputationalEndpointJobs }

/-- Each endpoint-job batch attached to a computational horizon-fence segment
is the literal empty source batch. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_endpointJobs
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (step : FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category))
    (hstep : step ∈ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight) :
    step.endpointJobs = taggedAdmittedFCFSComputationalEndpointJobs := by
  unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hstep
  rcases List.mem_map.mp hstep with ⟨segment, _hsegment, rfl⟩
  rfl

/-- Every segment of the explicit computational horizon-fence FCFS suffix
has the stored GPS guaranteed-rate floor when the chosen class is backlogged
at that segment's left endpoint.  The suffix has no source jobs at all: its
endpoint lists are the explicitly empty computational batches above. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hpre_work_nonneg : ∀ j, 0 ≤ preterminal.final.workload j := by
    intro j
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload j
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro k; norm_num) hsource_work_nonneg j
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  have hgap : ∀ segment ∈ finiteGPSHorizonFenceSegments capacity weight
      preterminal.final horizon,
      0 < segment.startWorkload i →
        capacity * weight i * segment.duration ≤ segment.serviceIncrement i := by
    simpa [finiteGPSHorizonFenceSegments] using
      (finiteGPSRunGapSegments_weightedCapacity_mul_duration_le_serviceIncrement_of_active
        ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
        (i := i) hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
        (sub_nonneg.mpr hpre_time_le_horizon))
  intro step hstep hactive
  unfold taggedAdmittedFiniteGPSHorizonFenceFCFSSteps at hstep
  rcases List.mem_map.mp hstep with ⟨segment, hsegment, hstep_eq⟩
  subst step
  exact hgap segment hsegment hactive

/-- The source-labelled pre-terminal FCFS fold followed by its explicit
zero-batch computational fence satisfies the same ledger/workload invariant
as every other finite FCFS trace.  The fence is represented by empty endpoint
job lists, so this theorem does not turn the computational horizon into a
source arrival. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_compatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    FiniteGPSFCFSRunSegmentStepsCompatible
      (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
        (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
          start horizon target z htarget_good capacity weight (fun _ => 0)))
      (taggedAdmittedFiniteGPSPreTerminalHistory
        start horizon target z htarget_good capacity weight (fun _ => 0)).final.workload
      (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
        start horizon target z htarget_good capacity weight) := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let preterminalSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start horizon target z htarget_good capacity weight (fun _ => 0)
  let initial := finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
    preterminalSteps
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hempty_matches : ∀ i,
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).classWork i =
        (fun _ : Category => 0) i := by
    intro i
    simp [taggedAdmittedEmptyFCFSLedger, FiniteGPSFCFSJobLedger.classWork,
      finiteGPSFCFSJobWork]
  have hpre_compatible : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) preterminalSteps := by
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one
      (by intro i; norm_num) hsource_work_nonneg hempty_nonneg hempty_matches
  have hinitial_nonneg : initial.Nonnegative := by
    exact taggedAdmittedFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) preterminalSteps
      hempty_nonneg hpre_compatible
  have hinitial_matches : ∀ i, initial.classWork i = preterminal.final.workload i := by
    intro i
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_fold_classWork_eq_history
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one
      (by intro j; norm_num) hsource_work_nonneg hempty_nonneg hempty_matches i
  have hpre_work_nonneg : ∀ j, 0 ≤ preterminal.final.workload j := by
    intro j
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).workload j
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro k; norm_num) hsource_work_nonneg j
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      start horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hstart_le_horizon
  change FiniteGPSFCFSRunSegmentStepsCompatible initial preterminal.final.workload
    (finiteGPSFCFSEmptyEndpointSteps
      (finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon))
  simpa [finiteGPSHorizonFenceSegments] using
    (finiteGPSRunGapSegments_emptyEndpointSteps_compatible_of_zeroBatch
      (Class := Category) (JobId := TaggedAdmittedSourceJobId Category)
      ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
      capacity weight preterminal.final.workload preterminal.final.currentTime
      (horizon - preterminal.final.currentTime) initial
      hcapacity hweight_pos htotal_weight_le_one hpre_work_nonneg
      (sub_nonneg.mpr hpre_time_le_horizon) hinitial_nonneg hinitial_matches)

/-- The actual finite tagged FCFS trace followed by its zero-work
computational horizon-fence suffix. -/
def taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    List (FiniteGPSFCFSSegmentJobStep Category (TaggedAdmittedSourceJobId Category)) :=
  taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start horizon target z htarget_good capacity weight (fun _ => 0) ++
  taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight

/-- The complete finite source trace, including the computational fence,
preserves the FCFS ledger/workload invariant from the literal empty initial
state.  The append is through the actual pre-terminal fold state; no fence
work or synthetic arrival is inserted at the join. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) := by
  let preterminalSteps := taggedAdmittedFiniteGPSPreTerminalFCFSSteps
    start horizon target z htarget_good capacity weight (fun _ => 0)
  have hempty_nonneg :
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).Nonnegative := by
    intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  have hempty_matches : ∀ i,
      (taggedAdmittedEmptyFCFSLedger (Category := Category)).classWork i =
        (fun _ : Category => 0) i := by
    intro i
    simp [taggedAdmittedEmptyFCFSLedger, FiniteGPSFCFSJobLedger.classWork,
      finiteGPSFCFSJobWork]
  have hpre : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0) preterminalSteps := by
    exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_compatible
      start horizon target z htarget_good capacity weight (fun _ => 0)
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      hcapacity hweight_pos htotal_weight_le_one
      (by intro i; norm_num) hsource_work_nonneg hempty_nonneg hempty_matches
  have hfence := taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_compatible
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  apply finiteGPSFCFSRunSegmentStepsCompatible_append
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0) preterminalSteps
    (taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight)
    hpre
  rw [taggedAdmittedFiniteGPSPreTerminalFCFSSteps_endpointWorkload_eq_history]
  exact hfence

/-- The full literal-source FCFS response trace, including its source-empty
computational fence suffix, has the local stored GPS floor at every interval
where the chosen class is actually backlogged. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    ∀ step ∈ taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i := by
  intro step hstep hactive
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps at hstep
  rcases List.mem_append.mp hstep with hpreterminal | hfence
  · exact taggedAdmittedFiniteGPSPreTerminalFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      start horizon target z htarget_good capacity weight (fun _ => 0)
      hcapacity hweight_pos htotal_weight_le_one (by intro j; norm_num)
      hsource_work_nonneg i step hpreterminal hactive
  · exact taggedAdmittedFiniteGPSHorizonFenceFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg i
      step hfence hactive

/-- The full finite tagged response trace stores at least the chosen class's
GPS guaranteed rate times the sum of exactly those intervals in which that
class is backlogged at the left endpoint.  This is the deterministic
service-floor interface for a later literal FCFS completion comparison. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_activeDuration_le_activeService
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (i : Category) :
    capacity * weight i * finiteGPSFCFSSegmentStepsActiveDuration i
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight) ≤
      finiteGPSFCFSSegmentStepsActiveService i
        (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          start horizon target z htarget_good capacity weight) := by
  apply finiteGPSFCFSSegmentSteps_weightedCapacity_mul_activeDuration_le_activeService
  intro step hstep hactive
  exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg i
    step hstep hactive

/-- The final literal FCFS ledger after the tagged finite source trace and
the explicitly computational horizon-fence suffix. -/
def taggedAdmittedFiniteGPSHorizonFenceFinalLedger
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category) :=
  finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)

/-- The actual target-class completion records from the full tagged finite
trace, including the computational zero-work horizon-fence suffix. -/
def taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) :
    List (FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)) :=
  finiteGPSFCFSRunSegmentStepsClassCompletions taggedAdmittedEmptyFCFSLedger target
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)

/-- A conditional completion/response witness for the literal selected source
job in the full finite trace with its computational horizon-fence suffix. -/
structure TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) where
  completion : FiniteGPSFCFSCompletion (TaggedAdmittedSourceJobId Category)
  completion_mem : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
    start horizon target z htarget_good capacity weight
  identifier_eq_tag : completion.identifier = (target, 0)
  arrival_eq_zero : completion.arrivalTime = 0

/-- Response time represented by a full finite-trace completion witness. -/
def TaggedAdmittedFiniteGPSHorizonFenceResponseWitness.response
    {start horizon : ℝ} {target : Category}
    {z : StationaryAdmittedTargetPassiveTaggedInput target}
    {htarget_good : palmTaggedArrivalGoodCarrier z.1.1}
    {capacity : ℝ} {weight : Category → ℝ}
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight) : ℝ :=
  witness.completion.completionTime - witness.completion.arrivalTime

/-- Extract a literal endpoint-admission witness from an external endpoint
batch of an actual tagged FCFS segment list. -/
private theorem taggedAdmittedFCFSEndpointJobAdmission_of_externalBatch
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (endpointJobs : FiniteGPSFCFSEndpointJobs Category
      (TaggedAdmittedSourceJobId Category))
    (i : Category) (job : FiniteGPSFCFSJob (TaggedAdmittedSourceJobId Category))
    (hendpoint : endpointJobs ∈
      taggedAdmittedFiniteGPSExternalEndpointJobBatches steps)
    (hjob : job ∈ endpointJobs.jobs i) :
    FiniteGPSFCFSEndpointJobAdmission steps i job := by
  unfold taggedAdmittedFiniteGPSExternalEndpointJobBatches at hendpoint
  rcases List.mem_filterMap.mp hendpoint with ⟨step, hstep, hselected⟩
  split at hselected
  · have hendpoint_eq : step.endpointJobs = endpointJobs := by
      simpa using Option.some.inj hselected
    apply finiteGPSFCFSEndpointJobAdmission_of_mem_step steps step i job hstep
    rw [hendpoint_eq]
    exact hjob
  · contradiction

/-- If the physical source interval contains zero, the literal tagged job is
an actual endpoint admission in the full finite FCFS trace.  Appending the
computational fence preserves this source admission and adds no new source
job. -/
theorem taggedAdmittedTargetFCFSJob_admitted_in_horizonFenceRun
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    FiniteGPSFCFSEndpointJobAdmission
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
      target (taggedAdmittedFCFSJob target z (target, 0)) := by
  rcases taggedAdmittedTargetFCFSJob_admitted_once_in_emptyPreTerminalSteps
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
      hstart hhorizon with
      ⟨endpointJobs, ⟨hendpoint, hjob⟩, _hunique⟩
  rcases taggedAdmittedFCFSEndpointJobAdmission_of_externalBatch
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight (fun _ => 0))
      endpointJobs target (taggedAdmittedFCFSJob target z (target, 0))
      hendpoint hjob with
      ⟨before, step, after, hsplit, hadmitted⟩
  refine ⟨before, step,
    after ++ taggedAdmittedFiniteGPSHorizonFenceFCFSSteps
      start horizon target z htarget_good capacity weight, ?_, hadmitted⟩
  unfold taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
  rw [hsplit]
  simp [List.cons_append]

/-- The literal finite source trace and its computational fence preserve
nonnegative residual FCFS jobs in every class.  This is derived from the
actual compatible fold, rather than being an additional completion premise. -/
theorem taggedAdmittedFiniteGPSHorizonFenceFinalLedger_nonnegative
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
      start horizon target z htarget_good capacity weight).Nonnegative := by
  unfold taggedAdmittedFiniteGPSHorizonFenceFinalLedger
  apply taggedAdmittedFiniteGPSFCFSRunSegmentSteps_nonnegative_of_compatible
    (taggedAdmittedEmptyFCFSLedger (Category := Category))
    (fun _ : Category => 0)
    (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight)
  · intro i job hjob
    simp [taggedAdmittedEmptyFCFSLedger] at hjob
  · exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg

/-- If the actual finite tagged source trace followed by its computational
horizon fence has nonnegative final target residual jobs and zero target
aggregate work, the admitted literal target job has an actual completion and
response witness.  This is a finite conditional implication only; it does
not assert that the final-zero premise holds at any horizon or with any
probability. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_of_finalTargetClassWork_zero
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (htagged_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0))
    (hfinal_target_classWork_zero :
      (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
        start horizon target z htarget_good capacity weight).classWork target = 0) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        start horizon target z htarget_good capacity weight,
      witness.completion.identifier = (target, 0) ∧
        witness.completion.arrivalTime = 0 := by
  have hadmission : FiniteGPSFCFSEndpointJobAdmission
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
      target (taggedAdmittedFCFSJob target z (target, 0)) :=
    taggedAdmittedTargetFCFSJob_admitted_in_horizonFenceRun
      start horizon target z htarget_good capacity weight
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg hstart hhorizon
  have hfinal_nonneg := taggedAdmittedFiniteGPSHorizonFenceFinalLedger_nonnegative
    start horizon target z htarget_good capacity weight
    (hstart.trans hhorizon.le) hcapacity hweight_pos htotal_weight_le_one
    hsource_work_nonneg
  have hfinal_target_nonneg : ∀ residual ∈
      (taggedAdmittedFiniteGPSHorizonFenceFinalLedger
        start horizon target z htarget_good capacity weight).residualJobs target,
      0 ≤ residual.residualWork := by
    intro residual hresidual
    exact hfinal_nonneg target residual hresidual
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_of_endpointJobAdmission_and_finalClassWork_eq_zero
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight)
      (taggedAdmittedFCFSJob target z (target, 0))
      hadmission htagged_work_pos hfinal_target_nonneg hfinal_target_classWork_zero with
      ⟨completion, hcompletion, hidentifier, harrival⟩
  have hidentifier_tag : completion.identifier = (target, 0) := by
    calc
      completion.identifier =
          (taggedAdmittedFCFSJob target z (target, 0)).identifier := hidentifier
      _ = (target, 0) := rfl
  have harrival_zero : completion.arrivalTime = 0 := by
    calc
      completion.arrivalTime =
          (taggedAdmittedFCFSJob target z (target, 0)).arrivalTime := harrival
      _ = taggedAdmittedSourceArrival target z (target, 0) := rfl
      _ = 0 := taggedAdmittedSourceArrival_target_zero target z
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight :=
    { completion := completion
      completion_mem := by
        simpa [taggedAdmittedFiniteGPSHorizonFenceTargetCompletions] using hcompletion
      identifier_eq_tag := hidentifier_tag
      arrival_eq_zero := harrival_zero }
  exact ⟨witness, witness.identifier_eq_tag, witness.arrival_eq_zero⟩

/-- A literal tagged completion in the full finite horizon-fence trace has
response time equal to its completion time because its physical arrival epoch
is zero. -/
theorem TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      start horizon target z htarget_good capacity weight) :
    witness.response = witness.completion.completionTime := by
  unfold TaggedAdmittedFiniteGPSHorizonFenceResponseWitness.response
  rw [witness.arrival_eq_zero]
  ring

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
