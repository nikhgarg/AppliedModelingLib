import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSCompletionTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSHorizonTraceTiming
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSPostTagTerminalStep
import Mathlib.Tactic

/-!
# Literal finite-horizon completion for the tagged GPS source trace

This module closes the finite deterministic comparison needed by the tagged
GPS construction.  It works on the actual source-labelled FCFS trace from a
physical reset through an arbitrary later horizon.

The proof has an explicit exhaustive split.  If the literal tagged job has
already completed in the post-tag source/fence suffix, its recorded executable
completion time is bounded directly by the requested horizon.  Otherwise the
literal FCFS persistence theorem makes the target class active throughout that
suffix.  Its physical duration is then exactly the horizon, so the GPS floor
and the proved source front-work/comparator comparison force a completion.
No caller supplies a closed-front-work, busy-period, or deadline-persistence
certificate.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- If every concrete suffix step is target-active at its left endpoint, its
canonical initial active prefix is the suffix itself. -/
private theorem finiteGPSFCFSSegmentStepsInitialActivePrefix_eq_self_of_all_active
    (target : Category)
    (steps : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hall_active : ∀ step ∈ steps, 0 < step.segment.startWorkload target) :
    finiteGPSFCFSSegmentStepsInitialActivePrefix target steps = steps := by
  unfold finiteGPSFCFSSegmentStepsInitialActivePrefix
  rw [List.takeWhile_eq_self_iff]
  intro step hstep
  exact decide_eq_true (hall_active step hstep)

/-- The literal zero-time source terminal exposes the actual singleton Palm
job and its FCFS front work.  The endpoint workload is retained as a concrete
source-run value, so later deadline adapters can compare it without replacing
the source batch by a computational fence. -/
theorem taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_frontWork
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_zero : resetTime ≤ 0) (hhorizon : 0 < horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ before terminal after frontWork,
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good capacity weight =
        before ++ terminal :: after ∧
      terminal.endpointJobs.jobs target =
        [taggedAdmittedFCFSJob target z (target, 0)] ∧
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
        some frontWork ∧
      frontWork = terminal.segment.endpointWorkload target ∧
      0 < frontWork := by
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_preLedger_no_tag
      resetTime horizon target z htarget_good capacity weight
      hreset_zero hhorizon hcapacity hweight_pos htotal_weight_le_one
      hsource_work_nonneg with
      ⟨before, terminal, after, hsplit, _hterminal_external,
        hterminal_singleton, hterminal_workload, hterminal_time, hpre_no_tag⟩
  have hstart_le_horizon : resetTime ≤ horizon :=
    hreset_zero.trans hhorizon.le
  have hfull : FiniteGPSFCFSRunSegmentStepsCompatible
      (taggedAdmittedEmptyFCFSLedger (Category := Category))
      (fun _ : Category => 0)
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime horizon target z htarget_good capacity weight) :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_compatible
      resetTime horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
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
      ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)
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
  let frontWork : ℝ := finiteGPSFCFSJobWork
      (finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs
          target)) + stationaryAdmittedTargetPalmWorkAtZero target z
  have hfront_raw := finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq_of_ledger_no_key
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    (finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before)
    terminal.segment terminal.endpointJobs target
    (taggedAdmittedFCFSJob target z (target, 0))
    hpre_no_tag hterminal_singleton (by simp)
  have hfront : finiteGPSFCFSFrontWork
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      ((taggedAdmittedFiniteGPSPostAdmissionLedger before terminal).residualJobs target) =
      some frontWork := by
    simpa [frontWork, taggedAdmittedFiniteGPSPostAdmissionLedger,
      taggedAdmittedFCFSJob, stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using hfront_raw
  have hfront_eq_endpoint : frontWork = terminal.segment.endpointWorkload target := by
    dsimp [frontWork]
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
  have hpost_nonneg := taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
    resetTime horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    before terminal after hsplit
  have hpreService_nonneg : ∀ job ∈
      finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target),
      0 ≤ job.residualWork := by
    intro job hjob
    exact hpost_nonneg target job (by
      change job ∈
        finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
          ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target) ++
          terminal.endpointJobs.jobs target
      exact List.mem_append.mpr (Or.inl hjob))
  have hpreService_work_nonneg : 0 ≤ finiteGPSFCFSJobWork
      (finiteGPSFCFSConsume (terminal.segment.serviceIncrement target)
        ((finiteGPSFCFSRunSegmentSteps taggedAdmittedEmptyFCFSLedger before).residualJobs target)) := by
    unfold finiteGPSFCFSJobWork
    apply List.sum_nonneg
    intro residual hresidual
    rcases List.mem_map.mp hresidual with ⟨job, hjob, rfl⟩
    exact hpreService_nonneg job hjob
  have hfront_pos : 0 < frontWork := by
    dsimp [frontWork]
    exact add_pos_of_nonneg_of_pos hpreService_work_nonneg htagged_work_pos
  exact ⟨before, terminal, after, frontWork, hsplit, hterminal_singleton,
    hterminal_workload, hterminal_time, hfront, hfront_eq_endpoint, hfront_pos⟩

/-- A literal GPS source/fence run from a physical reset contains the tagged
completion by any later horizon that dominates its finite target-comparator
deadline.  The proof is an explicit early-completion-or-full-active-suffix
dichotomy over the executable trace. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_horizon_of_finiteComparatorResponse_le
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat) (horizon : ℝ)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z)
    (hhorizon : 0 < horizon)
    (hfiniteComparatorResponse_le_horizon :
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart ≤ horizon) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        resetTime horizon target z htarget_good G.capacity G.weight,
      witness.completion.completionTime ≤ horizon ∧ witness.response ≤ horizon := by
  have hstart_le_horizon : resetTime ≤ horizon :=
    hreset_zero.trans hhorizon.le
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have htagged_source_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0) := by
    simpa [stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using htagged_work_pos
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_frontWork
      resetTime horizon target z htarget_good G.capacity G.weight
      hreset_zero hhorizon (G.capacity_pos target) G.weight_pos
      G.total_weight_le_one hsource_work_nonneg htagged_work_pos with
      ⟨before, terminal, after, frontWork, hsplit, hterminal_singleton,
        hterminal_workload, hterminal_time, hfront, hfront_eq_endpoint,
        hfront_pos⟩
  have htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      terminal.endpointJobs.jobs target := by
    rw [hterminal_singleton]
    simp
  have hfront_le_numerator : frontWork ≤
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (G.capacity * G.weight target) z remoteStart := by
    rw [hfront_eq_endpoint, hterminal_workload]
    exact taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_le_finiteComparatorNumerator
      resetTime horizon target z htarget_good G.capacity G.weight remoteStart
      hcoverage hreset_zero hhorizon (G.capacity_pos target) G.weight_pos
      G.total_weight_le_one hsource_work_nonneg
  have hresponse_eq :
      stationaryAdmittedTargetPalmFiniteComparatorResponse
          target (G.capacity * G.weight target) z remoteStart =
        stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart /
          (G.capacity * G.weight target) :=
    stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div
      target (G.capacity * G.weight target) z remoteStart
  have hnumerator_eq_rate_response :
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        (G.capacity * G.weight target) *
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by
    calc
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart *
          (G.capacity * G.weight target) :=
        (eq_div_iff (ne_of_gt hrate_pos)).mp hresponse_eq |>.symm
      _ = (G.capacity * G.weight target) *
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by ring
  have hfront_le_rate_horizon : frontWork ≤
      G.capacity * G.weight target * horizon := by
    calc
      frontWork ≤ stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart := hfront_le_numerator
      _ = (G.capacity * G.weight target) *
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart :=
        hnumerator_eq_rate_response
      _ ≤ G.capacity * G.weight target * horizon :=
        mul_le_mul_of_nonneg_left hfiniteComparatorResponse_le_horizon hrate_pos.le
  classical
  by_cases hhas_completion : ∃ completion ∈
      finiteGPSFCFSRunSegmentStepsClassCompletions
        (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal) target after,
      decide (completion.identifier = (target, 0)) = true
  · rcases hhas_completion with ⟨completion, hcompletion, hkey⟩
    have hidentifier : completion.identifier = (target, 0) :=
      of_decide_eq_true hkey
    have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        resetTime horizon target z htarget_good G.capacity G.weight =
        (before ++ [terminal]) ++ after := by
      rw [hsplit]
      simp [List.append_assoc]
    have hfull_completion : completion ∈
        taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
          resetTime horizon target z htarget_good G.capacity G.weight := by
      change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
        taggedAdmittedEmptyFCFSLedger target
        (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
          resetTime horizon target z htarget_good G.capacity G.weight)
      rw [hsplit', finiteGPSFCFSRunSegmentStepsClassCompletions_append]
      apply List.mem_append.mpr
      right
      simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using
        hcompletion
    have harrival : completion.arrivalTime = 0 :=
      taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
        resetTime horizon target z htarget_good G.capacity G.weight completion
        hfull_completion hidentifier
    let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        resetTime horizon target z htarget_good G.capacity G.weight :=
      { completion := completion
        completion_mem := hfull_completion
        identifier_eq_tag := hidentifier
        arrival_eq_zero := harrival }
    have htime : completion.completionTime ≤ horizon :=
      taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_completionTime_le_horizon
        resetTime horizon target z htarget_good G.capacity G.weight
        hstart_le_horizon (G.capacity_pos target) G.weight_pos
        G.total_weight_le_one hsource_work_nonneg completion hfull_completion
    refine ⟨witness, htime, ?_⟩
    rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
      resetTime horizon target z htarget_good G.capacity G.weight witness]
    exact htime
  · have hno_completion : ∀ completion ∈
        finiteGPSFCFSRunSegmentStepsClassCompletions
          (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal) target after,
        decide (completion.identifier = (target, 0)) ≠ true := by
      intro completion hcompletion hkey
      exact hhas_completion ⟨completion, hcompletion, hkey⟩
    have hpost_compatible :=
      taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
        resetTime horizon target z htarget_good G.capacity G.weight
        hstart_le_horizon (G.capacity_pos target) G.weight_pos
        G.total_weight_le_one hsource_work_nonneg before terminal after hsplit
    have hpost_nonneg :=
      taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
        resetTime horizon target z htarget_good G.capacity G.weight
        hstart_le_horizon (G.capacity_pos target) G.weight_pos
        G.total_weight_le_one hsource_work_nonneg before terminal after hsplit
    have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
        (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal).residualJobs target :=
      taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
        before terminal target (taggedAdmittedFCFSJob target z (target, 0))
        htag_admitted
    have htag_residual_pos :
        0 < (taggedAdmittedFCFSJob target z (target, 0)).residualWork := by
      simpa [taggedAdmittedFCFSJob] using htagged_source_work_pos
    have hall_active := finiteGPSFCFSRunSegmentSteps_all_active_of_no_keyed_completion
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      target after (taggedAdmittedFCFSJob target z (target, 0))
      hpost_nonneg hpost_compatible htag_after htag_residual_pos (by simp)
      hno_completion
    have hactive_prefix_eq :
        finiteGPSFCFSSegmentStepsInitialActivePrefix target after = after :=
      finiteGPSFCFSSegmentStepsInitialActivePrefix_eq_self_of_all_active
        target after hall_active
    have hafter_duration :=
      taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_suffixTotalDuration_eq_horizon_sub_endpoint
        resetTime horizon target z htarget_good G.capacity G.weight
        hstart_le_horizon (G.capacity_pos target) G.weight_pos
        G.total_weight_le_one hsource_work_nonneg before terminal after hsplit
    have hafter_duration_eq_horizon :
        finiteGPSFCFSSegmentStepsTotalDuration after = horizon := by
      simpa [hterminal_time] using hafter_duration
    have hfront_le_floor_duration : frontWork ≤
        G.capacity * G.weight target *
          finiteGPSFCFSSegmentStepsTotalDuration
            (finiteGPSFCFSSegmentStepsInitialActivePrefix target after) := by
      rw [hactive_prefix_eq, hafter_duration_eq_horizon]
      exact hfront_le_rate_horizon
    exact taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_by_horizon_of_initialActivePrefixFrontWork_le_floorDuration
      resetTime horizon target z htarget_good G.capacity G.weight
      hstart_le_horizon (G.capacity_pos target) G.weight_pos
      G.total_weight_le_one hsource_work_nonneg before terminal after hsplit
      htag_admitted htagged_source_work_pos frontWork hfront hfront_pos
      hfront_le_floor_duration

/-- The reset-window specialization at the literal finite target-comparator
deadline.  This is the form used by the later diagonal extension argument:
the response is bounded by the comparator deadline itself, not merely by a
larger replay horizon. -/
theorem taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_finiteComparatorResponse
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (resetTime : ℝ) (remoteStart : Nat)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_zero : resetTime ≤ 0)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        resetTime
        (stationaryAdmittedTargetPalmFiniteComparatorResponse
          target (G.capacity * G.weight target) z remoteStart)
        target z htarget_good G.capacity G.weight,
      witness.completion.completionTime ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart ∧
        witness.response ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have hpre_nonneg : 0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target (G.capacity * G.weight target) z remoteStart :=
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target (G.capacity * G.weight target) z remoteStart
  have hdeadline_pos : 0 < stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart := by
    rw [stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div]
    exact div_pos (add_pos_of_nonneg_of_pos hpre_nonneg htagged_work_pos) hrate_pos
  exact taggedAdmittedFiniteGPSHorizonFenceResponseWitness_exists_le_horizon_of_finiteComparatorResponse_le
    M G target z resetTime remoteStart
    (stationaryAdmittedTargetPalmFiniteComparatorResponse
      target (G.capacity * G.weight target) z remoteStart)
    htarget_good hsource_work_nonneg hreset_zero hcoverage htagged_work_pos
    hdeadline_pos (le_refl _)

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
