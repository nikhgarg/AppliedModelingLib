import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSDeadline
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResetBridge
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSLiteralHorizonCompletion
import Mathlib.Tactic

/-!
# Literal comparator-deadline completion in diagonal tagged GPS traces

This module proves the finite source-semantic bridge needed by the canonical
remote-past construction.  A global aggregate reset is used only to identify
the *numeric* front work at the literal zero-time source terminal.  The actual
completion is then proved directly in the longer diagonal FCFS trace, at the
physical comparator deadline.  In particular, no source batch is inserted at
that deadline and no aggregate restart equality is treated as an equality of
FCFS completion histories.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Erasing endpoint-job annotations preserves the literal final workload
recursion of a finite FCFS step list. -/
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

/-- A literal post-zero source/fence suffix inherits both its physical chain
and the exact full-horizon final clock from the complete executable trace. -/
private theorem taggedAdmittedFiniteGPSPostAdmissionSuffix_chain_and_finalTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hstart_le_horizon : start ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (before : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (admissionStep : FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category))
    (after : List (FiniteGPSFCFSSegmentJobStep Category
      (TaggedAdmittedSourceJobId Category)))
    (hsplit : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      start horizon target z htarget_good capacity weight =
        before ++ admissionStep :: after)
    (hadmission_time : finiteGPSExecutionSegmentEndTime admissionStep.segment = 0) :
    FiniteGPSExecutionSegmentsChainFrom 0
        (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep)
        (after.map fun step => step.segment) ∧
      finiteGPSExecutionSegmentsFinalTime 0
        (after.map fun step => step.segment) = horizon := by
  have hfull_chain := taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentChain
    start horizon target z htarget_good capacity weight hstart_le_horizon
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfull_final :=
    taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_segmentsFinalTime_eq_horizon
      start horizon target z htarget_good capacity weight hstart_le_horizon
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  let preSegments := before.map (fun step => step.segment) ++ [admissionStep.segment]
  let postSegments := after.map (fun step => step.segment)
  have hsegments_split :
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        start horizon target z htarget_good capacity weight).map
          (fun step => step.segment) = preSegments ++ postSegments := by
    dsimp [preSegments, postSegments]
    rw [hsplit]
    simp [List.append_assoc]
  have hchain_split : FiniteGPSExecutionSegmentsChainFrom start
      (fun _ : Category => 0) (preSegments ++ postSegments) := by
    rw [← hsegments_split]
    exact hfull_chain
  rcases (finiteGPSExecutionSegmentsChainFrom_append_iff
      start (fun _ : Category => 0) preSegments postSegments).mp hchain_split with
      ⟨_hprefix_chain, hsuffix_chain⟩
  have hprefix_final_time :
      finiteGPSExecutionSegmentsFinalTime start preSegments =
        finiteGPSExecutionSegmentEndTime admissionStep.segment := by
    dsimp [preSegments]
    simp [finiteGPSExecutionSegmentsFinalTime_append,
      finiteGPSExecutionSegmentsFinalTime]
  have hprefix_final_workload :
      finiteGPSExecutionSegmentsFinalWorkload (fun _ : Category => 0) preSegments =
        taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep := by
    dsimp [preSegments, taggedAdmittedFiniteGPSPostAdmissionWorkload]
    rw [finiteGPSFCFSSegmentStepsEndpointWorkload_eq_erasedFinalWorkload]
    simp
  have hsuffix_chain_zero : FiniteGPSExecutionSegmentsChainFrom 0
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before admissionStep) postSegments := by
    simpa [hprefix_final_time, hadmission_time, hprefix_final_workload] using
      hsuffix_chain
  have hfull_final_split :
      finiteGPSExecutionSegmentsFinalTime start (preSegments ++ postSegments) = horizon := by
    rw [← hsegments_split]
    exact hfull_final
  have hsuffix_final : finiteGPSExecutionSegmentsFinalTime 0 postSegments = horizon := by
    rw [finiteGPSExecutionSegmentsFinalTime_append,
      hprefix_final_time, hadmission_time] at hfull_final_split
    exact hfull_final_split
  exact ⟨hsuffix_chain_zero, hsuffix_final⟩

/-- A global closed-prefix reset identifies the numeric workload at the
literal zero-time source batch in a diagonal replay with the corresponding
reset-start replay.  This is only an aggregate workload equality; the
completion proof below still runs on the diagonal source-labelled FCFS trace.
-/
private theorem taggedAdmittedFiniteGPSDiagonalPreTagThenPalmBatch_target_workload_eq_reset
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (resetTime : ℝ) (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (N : ℕ) (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime) :
    (finiteGPSRunBatchTrace G.capacity G.weight
      (taggedAdmittedBatchAt (taggedAdmittedGPSDiagonalStart N)
        (taggedAdmittedGPSDiagonalHorizon N) target z)
      (taggedAdmittedGPSDiagonalStart N) (fun _ : Category => 0)
      (taggedAdmittedBatchTimeTrace (taggedAdmittedGPSDiagonalStart N) 0 target z ++ [0])).workload
        target =
      (finiteGPSRunBatchTrace G.capacity G.weight
        (taggedAdmittedBatchAt resetTime (taggedAdmittedGPSDiagonalHorizon N) target z)
        resetTime (fun _ : Category => 0)
        (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target := by
  have hdiagonal_palm := taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_eq
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good G.capacity G.weight
    (taggedAdmittedGPSDiagonalStart_le_zero N)
    (taggedAdmittedGPSDiagonalHorizon_pos N)
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one hsource_work_nonneg
  have hreset_palm := taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_eq
    resetTime (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good G.capacity G.weight hreset_zero
    (taggedAdmittedGPSDiagonalHorizon_pos N)
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one hsource_work_nonneg
  have hclosed_restart :=
    taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_pastGlobalMax
      (taggedAdmittedGPSDiagonalStart N) resetTime target z htarget_good
      G.capacity G.weight hdiagonal_before_reset hreset_zero
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg hglobal
  have hpretag_workload_eq :
      (taggedAdmittedFiniteGPSRun
        (taggedAdmittedGPSDiagonalStart N) 0 target z htarget_good
        G.capacity G.weight (fun _ : Category => 0)
        (taggedAdmittedGPSDiagonalStart_le_zero N)).workload target =
      (taggedAdmittedFiniteGPSRun
        resetTime 0 target z htarget_good G.capacity G.weight
        (fun _ : Category => 0) hreset_zero).workload target := by
    have hprojected := congrArg
      (fun result : FiniteGPSBatchTraceResult Category => result.workload target)
      hclosed_restart
    simpa using hprojected
  calc
    (finiteGPSRunBatchTrace G.capacity G.weight
      (taggedAdmittedBatchAt (taggedAdmittedGPSDiagonalStart N)
        (taggedAdmittedGPSDiagonalHorizon N) target z)
      (taggedAdmittedGPSDiagonalStart N) (fun _ : Category => 0)
      (taggedAdmittedBatchTimeTrace (taggedAdmittedGPSDiagonalStart N) 0 target z ++ [0])).workload
        target =
        (taggedAdmittedFiniteGPSRun
          (taggedAdmittedGPSDiagonalStart N) 0 target z htarget_good
          G.capacity G.weight (fun _ : Category => 0)
          (taggedAdmittedGPSDiagonalStart_le_zero N)).workload target +
          stationaryAdmittedTargetPalmWorkAtZero target z := hdiagonal_palm
    _ = (taggedAdmittedFiniteGPSRun
          resetTime 0 target z htarget_good G.capacity G.weight
          (fun _ : Category => 0) hreset_zero).workload target +
          stationaryAdmittedTargetPalmWorkAtZero target z := by
          rw [hpretag_workload_eq]
    _ = (finiteGPSRunBatchTrace G.capacity G.weight
          (taggedAdmittedBatchAt resetTime (taggedAdmittedGPSDiagonalHorizon N) target z)
          resetTime (fun _ : Category => 0)
          (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target :=
          hreset_palm.symm

/-- Once a diagonal replay begins before a retained global reset and extends
through the finite target comparator deadline, its *actual source-labelled*
FCFS trace contains the tagged completion by that deadline.  The reset is
used solely to compare the literal zero-terminal front work numerically with
the reset-start source replay; completion persistence is proved directly in
the longer diagonal trace. -/
theorem taggedAdmittedGPSDiagonalResponseWitness_exists_le_finiteComparatorResponse_of_pastGlobalMax
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (resetTime : ℝ) (remoteStart : Nat)
    (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z)
    (N : ℕ)
    (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime)
    (hdeadline_le_horizon :
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart ≤
          taggedAdmittedGPSDiagonalHorizon N) :
    ∃ witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight,
      witness.completion.completionTime ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart ∧
        witness.response ≤
          stationaryAdmittedTargetPalmFiniteComparatorResponse
            target (G.capacity * G.weight target) z remoteStart := by
  let deadline := stationaryAdmittedTargetPalmFiniteComparatorResponse
    target (G.capacity * G.weight target) z remoteStart
  have hstart_le_horizon : taggedAdmittedGPSDiagonalStart N ≤
      taggedAdmittedGPSDiagonalHorizon N :=
    taggedAdmittedGPSDiagonalStart_le_horizon N
  have hrate_pos : 0 < G.capacity * G.weight target :=
    mul_pos (G.capacity_pos target) (G.weight_pos target)
  have hpre_nonneg : 0 ≤ stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target (G.capacity * G.weight target) z remoteStart :=
    stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload_nonneg
      target (G.capacity * G.weight target) z remoteStart
  have hdeadline_pos : 0 < deadline := by
    rw [show deadline = stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart by rfl,
      stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div]
    exact div_pos (add_pos_of_nonneg_of_pos hpre_nonneg htagged_work_pos) hrate_pos
  have htagged_source_work_pos : 0 < taggedAdmittedSourceWork target z (target, 0) := by
    simpa [stationaryAdmittedTargetPalmWorkAtZero,
      stationaryAdmittedTargetPalmWorkPath] using htagged_work_pos
  rcases taggedAdmittedFiniteGPSHorizonFenceRun_exists_literalZeroTerminalSplit_frontWork
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight
      (taggedAdmittedGPSDiagonalStart_le_zero N)
      (taggedAdmittedGPSDiagonalHorizon_pos N)
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg htagged_work_pos with
      ⟨before, terminal, after, frontWork, hsplit, hterminal_singleton,
        hterminal_workload, hterminal_time, hfront, hfront_eq_endpoint,
        hfront_pos⟩
  have htag_admitted : taggedAdmittedFCFSJob target z (target, 0) ∈
      terminal.endpointJobs.jobs target := by
    rw [hterminal_singleton]
    simp
  have hpost_nonneg :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_nonnegative_of_fullSplit
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit
  have hpost_compatible :=
    taggedAdmittedFiniteGPSPostAdmissionSuffix_compatible_of_fullSplit
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit
  have htag_after : taggedAdmittedFCFSJob target z (target, 0) ∈
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal).residualJobs target :=
    taggedAdmittedFiniteGPSPostAdmissionLedger_mem_of_endpointAdmission
      before terminal target (taggedAdmittedFCFSJob target z (target, 0))
      htag_admitted
  have htag_residual_pos :
      0 < (taggedAdmittedFCFSJob target z (target, 0)).residualWork := by
    simpa [taggedAdmittedFCFSJob] using htagged_source_work_pos
  rcases taggedAdmittedFiniteGPSPostAdmissionSuffix_chain_and_finalTime
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg before terminal after hsplit hterminal_time with
      ⟨hafter_chain, hafter_final⟩
  have hterminal_workload_eq_reset : terminal.segment.endpointWorkload target =
      (finiteGPSRunBatchTrace G.capacity G.weight
        (taggedAdmittedBatchAt resetTime (taggedAdmittedGPSDiagonalHorizon N) target z)
        resetTime (fun _ : Category => 0)
        (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target := by
    calc
      terminal.segment.endpointWorkload target =
          (finiteGPSRunBatchTrace G.capacity G.weight
            (taggedAdmittedBatchAt (taggedAdmittedGPSDiagonalStart N)
              (taggedAdmittedGPSDiagonalHorizon N) target z)
            (taggedAdmittedGPSDiagonalStart N) (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace (taggedAdmittedGPSDiagonalStart N) 0 target z ++ [0])).workload
              target := hterminal_workload
      _ = (finiteGPSRunBatchTrace G.capacity G.weight
            (taggedAdmittedBatchAt resetTime (taggedAdmittedGPSDiagonalHorizon N) target z)
            resetTime (fun _ : Category => 0)
            (taggedAdmittedBatchTimeTrace resetTime 0 target z ++ [0])).workload target :=
          taggedAdmittedFiniteGPSDiagonalPreTagThenPalmBatch_target_workload_eq_reset
            M G target z htarget_good hsource_work_nonneg resetTime hreset_zero
            hglobal N hdiagonal_before_reset
  have hfront_le_numerator : frontWork ≤
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (G.capacity * G.weight target) z remoteStart := by
    rw [hfront_eq_endpoint, hterminal_workload_eq_reset]
    exact taggedAdmittedFiniteGPSPreTagThenPalmBatch_target_workload_le_finiteComparatorNumerator
      resetTime (taggedAdmittedGPSDiagonalHorizon N) target z htarget_good
      G.capacity G.weight remoteStart hcoverage hreset_zero
      (taggedAdmittedGPSDiagonalHorizon_pos N)
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg
  have hresponse_eq : deadline =
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target (G.capacity * G.weight target) z remoteStart /
          (G.capacity * G.weight target) := by
    exact stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div
      target (G.capacity * G.weight target) z remoteStart
  have hnumerator_eq_rate_deadline :
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        (G.capacity * G.weight target) * deadline := by
    calc
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart =
        deadline * (G.capacity * G.weight target) :=
          (eq_div_iff (ne_of_gt hrate_pos)).mp hresponse_eq |>.symm
      _ = (G.capacity * G.weight target) * deadline := by ring
  have hfront_le_deadline_floor : frontWork ≤
      G.capacity * G.weight target * (deadline - 0) := by
    calc
      frontWork ≤ stationaryAdmittedTargetPalmFiniteComparatorNumerator
          target (G.capacity * G.weight target) z remoteStart := hfront_le_numerator
      _ = (G.capacity * G.weight target) * deadline :=
        hnumerator_eq_rate_deadline
      _ = G.capacity * G.weight target * (deadline - 0) := by ring
  have hdeadline_le_after_final : deadline ≤
      finiteGPSExecutionSegmentsFinalTime 0 (after.map fun step => step.segment) := by
    rw [hafter_final]
    exact hdeadline_le_horizon
  have hafter_classRate_pos_of_active : ∀ step ∈ after,
      0 < step.segment.startWorkload target → 0 < step.segment.classRate target := by
    intro step hstep hactive
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))).1 hactive
  have hafter_service_eq : ∀ step ∈ after,
      step.segment.serviceIncrement target =
        step.segment.classRate target * step.segment.duration := by
    intro step hstep
    exact (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_executable_semantics
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep))))).2
  have hafter_floor : ∀ step ∈ after,
      0 < step.segment.startWorkload target →
        G.capacity * G.weight target * step.segment.duration ≤
          step.segment.serviceIncrement target := by
    intro step hstep hactive
    exact taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight hstart_le_horizon
      (G.capacity_pos target) G.weight_pos G.total_weight_le_one
      hsource_work_nonneg target step
      (by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hstep)))) hactive
  rcases finiteGPSFCFSRunSegmentStepsClassCompletion_exists_key_by_deadline_of_compatible
      (fun identifier : TaggedAdmittedSourceJobId Category =>
        decide (identifier = (target, 0)))
      (G.capacity * G.weight target)
      (taggedAdmittedFiniteGPSPostAdmissionLedger before terminal)
      (taggedAdmittedFiniteGPSPostAdmissionWorkload before terminal)
      target after (taggedAdmittedFCFSJob target z (target, 0)) frontWork 0 deadline
      hpost_nonneg hpost_compatible hafter_chain hdeadline_pos.le hdeadline_le_after_final
      hrate_pos hafter_classRate_pos_of_active hafter_service_eq hafter_floor
      htag_after htag_residual_pos (by simp) hfront hfront_pos
      hfront_le_deadline_floor with
      ⟨completion, hcompletion, hkey, hcompletion_time⟩
  have hidentifier : completion.identifier = (target, 0) :=
    of_decide_eq_true hkey
  have hsplit' : taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight =
        (before ++ [terminal]) ++ after := by
    rw [hsplit]
    simp [List.append_assoc]
  have hfull_completion : completion ∈ taggedAdmittedFiniteGPSHorizonFenceTargetCompletions
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight := by
    change completion ∈ finiteGPSFCFSRunSegmentStepsClassCompletions
      taggedAdmittedEmptyFCFSLedger target
      (taggedAdmittedFiniteGPSHorizonFenceRunFCFSSteps
        (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
        target z htarget_good G.capacity G.weight)
    rw [hsplit', finiteGPSFCFSRunSegmentStepsClassCompletions_append]
    apply List.mem_append.mpr
    right
    simpa only [taggedAdmittedFiniteGPSPostAdmissionLedger_eq_run_prefix] using
      hcompletion
  have harrival : completion.arrivalTime = 0 :=
    taggedAdmittedFiniteGPSHorizonFenceTargetCompletion_arrival_zero
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight completion hfull_completion hidentifier
  let witness : TaggedAdmittedFiniteGPSHorizonFenceResponseWitness
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight :=
    { completion := completion
      completion_mem := hfull_completion
      identifier_eq_tag := hidentifier
      arrival_eq_zero := harrival }
  refine ⟨witness, hcompletion_time, ?_⟩
  rw [TaggedAdmittedFiniteGPSHorizonFenceResponseWitness_response_eq_completionTime
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good G.capacity G.weight witness]
  exact hcompletion_time

/-- Selector-facing form of the literal diagonal deadline bridge.  A finite
source witness rules out the canonical selector's fallback branch, so the
deterministic diagonal response is bounded by the same physical comparator
deadline. -/
theorem taggedAdmittedGPSDiagonalFiniteResponse_le_finiteComparatorResponse_of_pastGlobalMax
    (M : SLA2026BoroughQueueingInput Category) (G : SLA2026BoroughGPSParameters M)
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (resetTime : ℝ) (remoteStart : Nat)
    (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : ℝ, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          G.capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          G.capacity * (-resetTime))
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (htagged_work_pos : 0 < stationaryAdmittedTargetPalmWorkAtZero target z)
    (N : ℕ)
    (hdiagonal_before_reset : taggedAdmittedGPSDiagonalStart N ≤ resetTime)
    (hdeadline_le_horizon :
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart ≤
          taggedAdmittedGPSDiagonalHorizon N) :
    taggedAdmittedGPSDiagonalFiniteResponse
      target z htarget_good G.capacity G.weight N ≤
      stationaryAdmittedTargetPalmFiniteComparatorResponse
        target (G.capacity * G.weight target) z remoteStart := by
  rcases taggedAdmittedGPSDiagonalResponseWitness_exists_le_finiteComparatorResponse_of_pastGlobalMax
      M G target z htarget_good hsource_work_nonneg resetTime remoteStart
      hreset_zero hglobal hcoverage htagged_work_pos N hdiagonal_before_reset
      hdeadline_le_horizon with
      ⟨witness, _hcompletion_time, hwitness_response⟩
  change taggedAdmittedFiniteGPSHorizonFenceTotalResponse
      (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
      target z htarget_good G.capacity G.weight ≤ _
  rw [taggedAdmittedFiniteGPSHorizonFenceTotalResponse_eq_witness_response
    (taggedAdmittedGPSDiagonalStart N) (taggedAdmittedGPSDiagonalHorizon N)
    target z htarget_good G.capacity G.weight
    (G.capacity_pos target) G.weight_pos G.total_weight_le_one
    hsource_work_nonneg (taggedAdmittedGPSDiagonalStart_le_zero N)
    (taggedAdmittedGPSDiagonalHorizon_pos N) witness]
  exact hwitness_response

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
