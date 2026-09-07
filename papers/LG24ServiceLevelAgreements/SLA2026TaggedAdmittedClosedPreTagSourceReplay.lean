import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedClosedPreTagSourceProjection
import Mathlib.Tactic

/-!
# Literal chronological replay for the closed LG24 pre-tag GPS trace

This module is the downstream source-to-scalar adapter for the executable
closed pre-tag trace.  It does not select arrivals from a numerical batch
value: retained blocks are identified by the literal target source labels
already audited in `SLA2026TaggedAdmittedClosedPreTagSourceProjection`.

The first certificate below fixes the concrete retained endpoint at every
chronological target predecessor position.  Later results turn its physical
endpoint clocks into the service coordinates of the finite target-only
Lindley replay.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The final clock of a nonempty projected block is its retained concrete
endpoint.  This is list-structural and does not inspect source labels or
work marks. -/
private theorem finiteGPSExecutionSegmentsFinalTime_projectionSegments_append_singleton
    (initialTime : ℝ)
    (earlier : List (FiniteGPSConstantRateProjectionBlock Category))
    (block : FiniteGPSConstantRateProjectionBlock Category) :
    finiteGPSExecutionSegmentsFinalTime initialTime
      (finiteGPSConstantRateProjectionSegments (earlier ++ [block]) []) =
        finiteGPSExecutionSegmentEndTime block.retained := by
  simp [finiteGPSConstantRateProjectionSegments,
    finiteGPSConstantRateProjectionBlockSegments,
    finiteGPSExecutionSegmentsFinalTime_append,
    finiteGPSExecutionSegmentsFinalTime]

/-- The first source-retained block spans from the physical reset clock to
its literal retained endpoint. -/
private theorem finiteGPSConstantRateProjectionBlockDuration_ofFn_first
    {N : Nat} (initialTime : ℝ) (initialWorkload : Category → ℝ)
    (blocks : Fin N → FiniteGPSConstantRateProjectionBlock Category)
    (terminalZero : List (FiniteGPSExecutionSegment Category))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero))
    (hN : 0 < N) :
    finiteGPSConstantRateProjectionBlockDuration (blocks ⟨0, hN⟩) =
      finiteGPSExecutionSegmentEndTime (blocks ⟨0, hN⟩).retained - initialTime := by
  let first : FiniteGPSConstantRateProjectionBlock Category := blocks ⟨0, hN⟩
  let suffix := (List.ofFn blocks).drop 1
  have hfirst_mem : 0 < (List.ofFn blocks).length := by
    simpa using hN
  have hsplit : List.ofFn blocks = [] ++ first :: suffix := by
    calc
      List.ofFn blocks = (List.ofFn blocks).drop 0 := by simp
      _ = (List.ofFn blocks)[0]'hfirst_mem :: (List.ofFn blocks).drop 1 := by
        symm
        exact List.cons_getElem_drop_succ (l := List.ofFn blocks) (n := 0)
          (h := hfirst_mem)
      _ = [] ++ first :: suffix := by
        simp [first, suffix]
  have hchain' : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments ([] ++ first :: suffix) terminalZero) := by
    simpa [hsplit] using hchain
  have hduration := finiteGPSConstantRateProjectionBlockDuration_eq_finalTime_sub_prefix
    initialTime initialWorkload ([] : List (FiniteGPSConstantRateProjectionBlock Category))
    suffix first terminalZero hchain'
  change finiteGPSConstantRateProjectionBlockDuration first = _
  calc
    finiteGPSConstantRateProjectionBlockDuration first =
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments ([] ++ [first]) []) -
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments [] []) := hduration
    _ = finiteGPSExecutionSegmentEndTime first.retained - initialTime := by
      rw [finiteGPSExecutionSegmentsFinalTime_projectionSegments_append_singleton]
      simp [finiteGPSConstantRateProjectionSegments,
        finiteGPSExecutionSegmentsFinalTime]

/-- Every later source-retained block spans exactly from the immediately
preceding retained concrete endpoint to its own endpoint.  This is the
physical-time identity needed for the chronological service coordinates. -/
private theorem finiteGPSConstantRateProjectionBlockDuration_ofFn_later
    {N j : Nat} (initialTime : ℝ) (initialWorkload : Category → ℝ)
    (blocks : Fin N → FiniteGPSConstantRateProjectionBlock Category)
    (terminalZero : List (FiniteGPSExecutionSegment Category))
    (hchain : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero))
    (hj_pos : 0 < j) (hj : j < N) :
    finiteGPSConstantRateProjectionBlockDuration (blocks ⟨j, hj⟩) =
      finiteGPSExecutionSegmentEndTime (blocks ⟨j, hj⟩).retained -
        finiteGPSExecutionSegmentEndTime (blocks ⟨j - 1, by omega⟩).retained := by
  let current : FiniteGPSConstantRateProjectionBlock Category := blocks ⟨j, hj⟩
  let earlier := (List.ofFn blocks).take j
  let suffix := (List.ofFn blocks).drop (j + 1)
  have hj_length : j < (List.ofFn blocks).length := by
    simpa using hj
  have hsplit : List.ofFn blocks = earlier ++ current :: suffix := by
    calc
      List.ofFn blocks = (List.ofFn blocks).take j ++ (List.ofFn blocks).drop j := by
        symm
        exact List.take_append_drop j (List.ofFn blocks)
      _ = (List.ofFn blocks).take j ++
          ((List.ofFn blocks)[j]'hj_length :: (List.ofFn blocks).drop (j + 1)) := by
        rw [List.cons_getElem_drop_succ (l := List.ofFn blocks) (n := j)
          (h := hj_length)]
      _ = earlier ++ current :: suffix := by
        simp [earlier, current, suffix]
  have hchain' : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload
      (finiteGPSConstantRateProjectionSegments (earlier ++ current :: suffix) terminalZero) := by
    simpa [hsplit] using hchain
  have hduration := finiteGPSConstantRateProjectionBlockDuration_eq_finalTime_sub_prefix
    initialTime initialWorkload earlier suffix current terminalZero hchain'
  have hprevious_length : j - 1 < (List.ofFn blocks).length := by
    have hprevious_lt_j : j - 1 < j := by omega
    calc
      j - 1 < j := hprevious_lt_j
      _ < (List.ofFn blocks).length := hj_length
  have hprevious_split : earlier = (List.ofFn blocks).take (j - 1) ++
      [blocks ⟨j - 1, by omega⟩] := by
    calc
      earlier = (List.ofFn blocks).take j := rfl
      _ = (List.ofFn blocks).take ((j - 1) + 1) := by
        congr 1
        omega
      _ = (List.ofFn blocks).take (j - 1) ++
          [(List.ofFn blocks)[j - 1]'hprevious_length] := by
        symm
        exact List.take_concat_get' (List.ofFn blocks) (j - 1) hprevious_length
      _ = (List.ofFn blocks).take (j - 1) ++ [blocks ⟨j - 1, by omega⟩] := by
        simp
  have hprevious_final : finiteGPSExecutionSegmentsFinalTime initialTime
      (finiteGPSConstantRateProjectionSegments earlier []) =
        finiteGPSExecutionSegmentEndTime (blocks ⟨j - 1, by omega⟩).retained := by
    rw [hprevious_split]
    exact finiteGPSExecutionSegmentsFinalTime_projectionSegments_append_singleton
      initialTime _ _
  change finiteGPSConstantRateProjectionBlockDuration current = _
  calc
    finiteGPSConstantRateProjectionBlockDuration current =
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments (earlier ++ [current]) []) -
        finiteGPSExecutionSegmentsFinalTime initialTime
          (finiteGPSConstantRateProjectionSegments earlier []) := hduration
    _ = finiteGPSExecutionSegmentEndTime current.retained -
        finiteGPSExecutionSegmentEndTime (blocks ⟨j - 1, by omega⟩).retained := by
      rw [finiteGPSExecutionSegmentsFinalTime_projectionSegments_append_singleton,
        hprevious_final]

/-- The physical interval from chronological predecessor `j` to its newer
neighbour is precisely the direct target-comparator service coordinate read
in reverse remote-past order. -/
private theorem rate_mul_chronologicalRemotePredecessorTime_succ_sub_eq_reverseRemotePastService
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (N : Nat) (j : Fin N) :
    serviceRate *
      (taggedAdmittedChronologicalRemotePredecessorTime target z (N + 1) (Fin.succ j) -
        taggedAdmittedChronologicalRemotePredecessorTime target z (N + 1) (Fin.castSucc j)) =
      reverseRemotePastIncrement
        (stationaryAdmittedTargetPalmRemotePastService target serviceRate z)
        (N + 1) j.1 := by
  let remoteIndex := (N + 1) - (j.1 + 1)
  have hremoteIndex_pos : 0 < remoteIndex := by
    dsimp [remoteIndex]
    omega
  have hprevious_index :
      taggedAdmittedChronologicalRemotePredecessorIndex (N + 1) (Fin.castSucc j) =
        remoteIndex := by
    simp [taggedAdmittedChronologicalRemotePredecessorIndex, remoteIndex]
  have hcurrent_index :
      taggedAdmittedChronologicalRemotePredecessorIndex (N + 1) (Fin.succ j) =
        remoteIndex - 1 := by
    simp [taggedAdmittedChronologicalRemotePredecessorIndex, remoteIndex]
    omega
  have hnewer_index : Int.negSucc remoteIndex + 1 =
      Int.negSucc (remoteIndex - 1) := by
    omega
  calc
    serviceRate *
        (taggedAdmittedChronologicalRemotePredecessorTime target z (N + 1) (Fin.succ j) -
          taggedAdmittedChronologicalRemotePredecessorTime target z (N + 1) (Fin.castSucc j)) =
        serviceRate *
          (candidatePalmArrival z.1.1 (Int.negSucc (remoteIndex - 1)) -
            candidatePalmArrival z.1.1 (Int.negSucc remoteIndex)) := by
      simp only [taggedAdmittedChronologicalRemotePredecessorTime]
      rw [hcurrent_index, hprevious_index]
    _ = serviceRate *
          (candidatePalmArrival z.1.1 (Int.negSucc remoteIndex + 1) -
            candidatePalmArrival z.1.1 (Int.negSucc remoteIndex)) := by
      rw [hnewer_index]
    _ = stationaryAdmittedTargetPalmRemotePastService target serviceRate z remoteIndex := by
      symm
      exact stationaryAdmittedTargetPalmRemotePastService_eq_rate_mul_newerArrival_sub_arrival
        target serviceRate z remoteIndex
    _ = reverseRemotePastIncrement
          (stationaryAdmittedTargetPalmRemotePastService target serviceRate z)
          (N + 1) j.1 := by
      simp [reverseRemotePastIncrement, remoteIndex]

/-- A finite family of retained projection blocks is exactly a chronological
service-before-batch replay once its first interval, later intervals, and
endpoint batches have been identified.  This is generic list algebra; the
source-specific theorem below supplies those identities from literal labels
and physical clocks. -/
private theorem finiteGPSConstantRateProjectionRetainedReplaySteps_ofFn_eq_chronological
    {N : Nat} (rate : ℝ) (i : Category)
    (blocks : Fin N → FiniteGPSConstantRateProjectionBlock Category)
    (firstService : ℝ) (batch service : Nat → ℝ)
    (hbatch : ∀ j : Fin N,
      (blocks j).retained.endpointBatch i = batch j.1)
    (hfirst : ∀ hN : 0 < N,
      rate * finiteGPSConstantRateProjectionBlockDuration (blocks ⟨0, hN⟩) =
        firstService)
    (hlater : ∀ j : Fin N, ∀ hj_pos : 0 < j.1,
      rate * finiteGPSConstantRateProjectionBlockDuration (blocks j) =
        service (j.1 - 1)) :
    finiteGPSConstantRateProjectionRetainedReplaySteps rate i (List.ofFn blocks) =
      lateBatchChronologicalReplaySteps firstService batch service N := by
  cases N with
  | zero =>
      simp [finiteGPSConstantRateProjectionRetainedReplaySteps,
        lateBatchChronologicalReplaySteps]
  | succ N =>
      rw [finiteGPSConstantRateProjectionRetainedReplaySteps_ofFn]
      rw [List.ofFn_succ]
      simp only [lateBatchChronologicalReplaySteps]
      congr 1
      · change
          LateBatchReplayStep.mk
            (rate * finiteGPSConstantRateProjectionBlockDuration
              (blocks ⟨0, Nat.zero_lt_succ N⟩))
            ((blocks ⟨0, Nat.zero_lt_succ N⟩).retained.endpointBatch i) =
          LateBatchReplayStep.mk firstService (batch 0)
        rw [hfirst (Nat.zero_lt_succ N), hbatch ⟨0, Nat.zero_lt_succ N⟩]
      · apply congrArg List.ofFn
        funext j
        change
          LateBatchReplayStep.mk
            (rate * finiteGPSConstantRateProjectionBlockDuration (blocks j.succ))
            ((blocks j.succ).retained.endpointBatch i) =
          LateBatchReplayStep.mk (service j.1) (batch (j.1 + 1))
        have hj_succ_pos : 0 < (j.succ : Fin (N + 1)).1 := Nat.succ_pos _
        rw [hlater j.succ hj_succ_pos, hbatch j.succ]
        simp

/-- The executable closed pre-tag segment ledger ends at its requested
physical horizon.  This is a clock identity for the concrete runner and
computational fence, not a statement that the fence is a source arrival. -/
private theorem taggedAdmittedFiniteGPSClosedPreTagHistory_finalTime_eq_horizon
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_le_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    finiteGPSExecutionSegmentsFinalTime resetTime
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime horizon target z htarget_good capacity weight).segments = horizon := by
  let preterminal := taggedAdmittedFiniteGPSPreTerminalHistory
    resetTime horizon target z htarget_good capacity weight (fun _ => 0)
  have hbatch_nonneg : ∀ eventTime ∈
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times,
      ∀ k, 0 ≤ taggedAdmittedBatchAt resetTime horizon target z eventTime k := by
    intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg
      resetTime horizon target z hsource_work_nonneg eventTime k
  have hpre_final_time : finiteGPSExecutionSegmentsFinalTime resetTime
      preterminal.segments = preterminal.final.currentTime := by
    change finiteGPSExecutionSegmentsFinalTime resetTime
      (finiteGPSRunBatchTraceSegments capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times) =
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt resetTime horizon target z) resetTime (fun _ => 0)
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times).currentTime
    exact finiteGPSExecutionSegmentsFinalTime_runBatchTraceSegments
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times
      hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).chronological
      hbatch_nonneg
  have hpre_nonneg : ∀ k, 0 ≤ preterminal.final.workload k := by
    intro k
    change 0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).workload k
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      (by intro j; norm_num) hsource_work_nonneg k
  have hpre_time_le_horizon : preterminal.final.currentTime ≤ horizon := by
    change (taggedAdmittedFiniteGPSPreTerminalRun
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)).currentTime ≤ horizon
    exact taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
      resetTime horizon target z htarget_good capacity weight (fun _ => 0)
      hreset_le_horizon
  have hfence_final_time : finiteGPSExecutionSegmentsFinalTime
      preterminal.final.currentTime
      (finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) =
      (finiteGPSCloseAtHorizon capacity weight preterminal.final horizon).currentTime := by
    change finiteGPSExecutionSegmentsFinalTime preterminal.final.currentTime
      (finiteGPSRunGapSegments ((finiteGPSActiveClasses preterminal.final.workload).card + 1)
        capacity weight preterminal.final.workload (fun _ => 0)
        preterminal.final.currentTime (horizon - preterminal.final.currentTime)) = _
    rw [finiteGPSExecutionSegmentsFinalTime_runGapSegments]
    simp [finiteGPSCloseAtHorizon, finiteGPSHorizonFence]
  change finiteGPSExecutionSegmentsFinalTime resetTime
      (preterminal.segments ++
        finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) = horizon
  calc
    finiteGPSExecutionSegmentsFinalTime resetTime
        (preterminal.segments ++
          finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) =
        finiteGPSExecutionSegmentsFinalTime preterminal.final.currentTime
          (finiteGPSHorizonFenceSegments capacity weight preterminal.final horizon) := by
      rw [finiteGPSExecutionSegmentsFinalTime_append, hpre_final_time]
    _ = (finiteGPSCloseAtHorizon capacity weight preterminal.final horizon).currentTime :=
      hfence_final_time
    _ = horizon := finiteGPSCloseAtHorizon_currentTime capacity weight preterminal.final horizon
      hcapacity hweight_pos htotal_weight_le_one hpre_nonneg hpre_time_le_horizon

/-- Service elapsed from the physical reset to the oldest retained target
predecessor.  The empty-history branch is deliberately arbitrary because the
chronological replay contains no first event there; it avoids fabricating a
source arrival at the tag. -/
noncomputable def taggedAdmittedClosedPreTagFirstTargetService
    (serviceRate resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) : ℝ := by
  classical
  exact if hremoteStart : remoteStart = 0 then 0 else
    serviceRate *
      (taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart
        ⟨0, Nat.pos_of_ne_zero hremoteStart⟩ - resetTime)

/-- The erased retained blocks of the literal closed pre-tag source partition
can be enumerated in physical chronological target-predecessor order.  At
each position, both the stored target batch and the concrete endpoint time
are the direct source quantities at that literal predecessor label. -/
theorem exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalConcreteBlocks
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    ∃ blocks : Fin remoteStart → FiniteGPSConstantRateProjectionBlock Category,
      List.ofFn blocks = partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase ∧
      ∀ j : Fin remoteStart,
        (blocks j).retained.endpointBatch target =
          reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z)
            remoteStart j.1 ∧
        finiteGPSExecutionSegmentEndTime (blocks j).retained =
          taggedAdmittedChronologicalRemotePredecessorTime
            target z remoteStart j := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  rcases exists_taggedAdmittedClosedPreTagSourceProjectionPartition_chronologicalBlocks
      resetTime target z htarget_good capacity weight remoteStart hcoverage
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg with
      ⟨annotatedBlocks, hannotatedBlocks, hendpointJobs⟩
  let blocks : Fin remoteStart → FiniteGPSConstantRateProjectionBlock Category :=
    fun j => (annotatedBlocks j).erase
  have hblocks : List.ofFn blocks = partition.1.map
      FiniteGPSFCFSSemanticProjectionBlock.erase := by
    change List.ofFn (fun j => (annotatedBlocks j).erase) =
      partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase
    rw [List.ofFn_comp']
    rw [hannotatedBlocks]
  refine ⟨blocks, hblocks, ?_⟩
  intro j
  have hj_partition : annotatedBlocks j ∈ partition.1 := by
    rw [← hannotatedBlocks]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hj_endpointJobs : (annotatedBlocks j).retained.endpointJobs =
      ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
        resetTime target z remoteStart)[j.1]'(by simp [
          taggedAdmittedChronologicalRemotePredecessorEndpointTrace])).endpointJobs :=
    hendpointJobs j
  have hj_canonical_targetJobs :
      ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
        resetTime target z remoteStart)[j.1]'(by simp [
          taggedAdmittedChronologicalRemotePredecessorEndpointTrace])).endpointJobs.jobs target =
        [taggedAdmittedFCFSJob target z
          (target, Int.negSucc
            (taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j))] := by
    exact taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem_targetJobs_eq_singleton
      resetTime target z htarget_good remoteStart hcoverage j
  have hindex_of_mem : ∀ n : Nat,
      taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        (annotatedBlocks j).retained.endpointJobs.jobs target →
      n = taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j := by
    intro n hmem
    have hcanonical_mem : taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
        ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
          resetTime target z remoteStart)[j.1]'(by simp [
            taggedAdmittedChronologicalRemotePredecessorEndpointTrace])).endpointJobs.jobs target := by
      rw [← hj_endpointJobs]
      exact hmem
    rw [hj_canonical_targetJobs] at hcanonical_mem
    have hjob_eq : taggedAdmittedFCFSJob target z (target, Int.negSucc n) =
        taggedAdmittedFCFSJob target z (target, Int.negSucc
          (taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j)) := by
      simpa using hcanonical_mem
    exact Int.negSucc.inj
      (taggedAdmittedFCFSJob_injective target z target hjob_eq)
  constructor
  · rcases taggedAdmittedClosedPreTagSourceProjectionPartition_retained_predecessor_batch
        resetTime target z htarget_good capacity weight remoteStart
        (annotatedBlocks j) hj_partition with ⟨n, _hn, hmem, hbatch⟩
    have hindex := hindex_of_mem n hmem
    change (annotatedBlocks j).retained.segment.endpointBatch target = _
    rw [hbatch, hindex]
    rfl
  · rcases taggedAdmittedClosedPreTagSourceProjectionPartition_retained_predecessor_endTime
        resetTime target z htarget_good capacity weight remoteStart
        (annotatedBlocks j) hj_partition with ⟨n, _hn, hmem, hendTime⟩
    have hindex := hindex_of_mem n hmem
    change finiteGPSExecutionSegmentEndTime (annotatedBlocks j).retained.segment = _
    rw [hendTime, hindex]
    rfl

/-- The concrete chronological source enumeration also carries the exact
physical elapsed durations of its retained blocks.  The first block begins
at the actual reset; every later block begins at the preceding literal target
source endpoint. -/
theorem exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalBlocks_with_durations
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    ∃ blocks : Fin remoteStart → FiniteGPSConstantRateProjectionBlock Category,
      List.ofFn blocks = partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase ∧
      (∀ j : Fin remoteStart,
        (blocks j).retained.endpointBatch target =
          reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z)
            remoteStart j.1 ∧
        finiteGPSExecutionSegmentEndTime (blocks j).retained =
          taggedAdmittedChronologicalRemotePredecessorTime
            target z remoteStart j) ∧
      (∀ hremoteStart_pos : 0 < remoteStart,
        finiteGPSConstantRateProjectionBlockDuration
          (blocks ⟨0, hremoteStart_pos⟩) =
          taggedAdmittedChronologicalRemotePredecessorTime
            target z remoteStart ⟨0, hremoteStart_pos⟩ - resetTime) ∧
      (∀ j : Fin remoteStart, ∀ hj_pos : 0 < j.1,
        finiteGPSConstantRateProjectionBlockDuration (blocks j) =
          taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j -
            taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart
              ⟨j.1 - 1, by omega⟩) := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  rcases exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalConcreteBlocks
      resetTime target z htarget_good capacity weight remoteStart hcoverage
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg with
      ⟨blocks, hblocks, hconcrete⟩
  let terminalZero := partition.2.map (fun step => step.segment)
  have hsegments : finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments := by
    rw [hblocks]
    simpa [partition, terminalZero] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_erase_eq_closed_history
        resetTime target z htarget_good capacity weight remoteStart)
  have hchain : FiniteGPSExecutionSegmentsChainFrom resetTime
      (fun _ : Category => 0)
      (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero) := by
    rw [hsegments]
    exact taggedAdmittedFiniteGPSClosedPreTagHistory_segments_chainFrom
      resetTime 0 target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  refine ⟨blocks, hblocks, hconcrete, ?_, ?_⟩
  · intro hremoteStart_pos
    rw [finiteGPSConstantRateProjectionBlockDuration_ofFn_first
      resetTime (fun _ : Category => 0) blocks terminalZero hchain hremoteStart_pos]
    rw [(hconcrete ⟨0, hremoteStart_pos⟩).2]
  · intro j hj_pos
    have hduration := finiteGPSConstantRateProjectionBlockDuration_ofFn_later
      resetTime (fun _ : Category => 0) blocks terminalZero hchain hj_pos j.2
    change finiteGPSConstantRateProjectionBlockDuration (blocks j) = _
    calc
      finiteGPSConstantRateProjectionBlockDuration (blocks j) =
          finiteGPSExecutionSegmentEndTime (blocks j).retained -
            finiteGPSExecutionSegmentEndTime (blocks ⟨j.1 - 1, by omega⟩).retained := by
        simpa using hduration
      _ = taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j -
            taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart
              ⟨j.1 - 1, by omega⟩ := by
        rw [(hconcrete j).2, (hconcrete ⟨j.1 - 1, by omega⟩).2]

/-- The source-empty terminal suffix of the literal closed partition has the
actual physical duration from the final retained target predecessor to the
Palm tag.  If no predecessor is retained, it spans the full reset-to-tag
interval. -/
theorem taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_duration_eq
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    finiteGPSExecutionSegmentsTotalDuration (partition.2.map fun step => step.segment) =
      if remoteStart = 0 then 0 - resetTime else
        0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by
  classical
  dsimp only
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  rcases exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalConcreteBlocks
      resetTime target z htarget_good capacity weight remoteStart hcoverage
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg with
      ⟨blocks, hblocks, hconcrete⟩
  let terminalZero := partition.2.map (fun step => step.segment)
  have hsegments : finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments := by
    rw [hblocks]
    simpa [partition, terminalZero] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_erase_eq_closed_history
        resetTime target z htarget_good capacity weight remoteStart)
  have hchain : FiniteGPSExecutionSegmentsChainFrom resetTime
      (fun _ : Category => 0)
      (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero) := by
    rw [hsegments]
    exact taggedAdmittedFiniteGPSClosedPreTagHistory_segments_chainFrom
      resetTime 0 target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hfull_final : finiteGPSExecutionSegmentsFinalTime resetTime
      (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero) = 0 := by
    rw [hsegments]
    exact taggedAdmittedFiniteGPSClosedPreTagHistory_finalTime_eq_horizon
      resetTime 0 target z htarget_good capacity weight hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
  have hterminal_duration :=
    finiteGPSConstantRateProjectionTerminalDuration_eq_finalTime_sub_blocks
      resetTime (fun _ : Category => 0) (List.ofFn blocks) terminalZero hchain
  change finiteGPSExecutionSegmentsTotalDuration terminalZero = _
  cases remoteStart with
  | zero =>
      have hblocks_final : finiteGPSExecutionSegmentsFinalTime resetTime
          (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) []) = resetTime := by
        simp [finiteGPSConstantRateProjectionSegments,
          finiteGPSExecutionSegmentsFinalTime]
      calc
        finiteGPSExecutionSegmentsTotalDuration terminalZero =
            finiteGPSExecutionSegmentsFinalTime resetTime
              (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero) -
              finiteGPSExecutionSegmentsFinalTime resetTime
                (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) []) :=
          hterminal_duration
        _ = 0 - resetTime := by rw [hfull_final, hblocks_final]
        _ = if 0 = 0 then 0 - resetTime else
              0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by simp
  | succ N =>
      have hblocks_final : finiteGPSExecutionSegmentsFinalTime resetTime
          (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) []) =
            candidatePalmArrival z.1.1 (Int.negSucc 0) := by
        rw [List.ofFn_succ' blocks]
        simp only [List.concat_eq_append]
        rw [finiteGPSExecutionSegmentsFinalTime_projectionSegments_append_singleton]
        simpa [taggedAdmittedChronologicalRemotePredecessorTime,
          taggedAdmittedChronologicalRemotePredecessorIndex] using
          (hconcrete (Fin.last N)).2
      calc
        finiteGPSExecutionSegmentsTotalDuration terminalZero =
            finiteGPSExecutionSegmentsFinalTime resetTime
              (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) terminalZero) -
              finiteGPSExecutionSegmentsFinalTime resetTime
                (finiteGPSConstantRateProjectionSegments (List.ofFn blocks) []) :=
          hterminal_duration
        _ = 0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by
          rw [hfull_final, hblocks_final]
        _ = if N + 1 = 0 then 0 - resetTime else
              0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by simp

/-- The retained portion of the exact closed GPS source projection is the
literal finite target-predecessor Lindley replay.  Its first interval starts
at the physical reset, later intervals are the actual adjacent target source
gaps, and each endpoint batch is retained by source ID even at zero work. -/
theorem exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalRetainedReplay
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
      resetTime target z htarget_good capacity weight remoteStart
    ∃ blocks : Fin remoteStart → FiniteGPSConstantRateProjectionBlock Category,
      List.ofFn blocks = partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase ∧
      finiteGPSConstantRateProjectionRetainedReplaySteps
        (capacity * weight target) target (List.ofFn blocks) =
        lateBatchChronologicalReplaySteps
          (taggedAdmittedClosedPreTagFirstTargetService
            (capacity * weight target) resetTime target z remoteStart)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService
              target (capacity * weight target) z) remoteStart)
          remoteStart := by
  classical
  dsimp only
  rcases exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalBlocks_with_durations
      resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg with
      ⟨blocks, hblocks, hconcrete, hfirstDuration, hlaterDuration⟩
  refine ⟨blocks, hblocks, ?_⟩
  apply finiteGPSConstantRateProjectionRetainedReplaySteps_ofFn_eq_chronological
    (capacity * weight target) target blocks
    (taggedAdmittedClosedPreTagFirstTargetService
      (capacity * weight target) resetTime target z remoteStart)
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastService
        target (capacity * weight target) z) remoteStart)
  · intro j
    exact (hconcrete j).1
  · intro hremoteStart_pos
    rw [hfirstDuration hremoteStart_pos]
    simp [taggedAdmittedClosedPreTagFirstTargetService,
      Nat.ne_of_gt hremoteStart_pos]
  · intro j hj_pos
    cases remoteStart with
    | zero =>
        exact False.elim (Nat.not_lt_zero _ j.2)
    | succ N =>
        let older : Fin N := ⟨j.1 - 1, by omega⟩
        have hsucc : older.succ = j := by
          apply Fin.ext
          simp [older]
          omega
        have hcast : older.castSucc = ⟨j.1 - 1, by omega⟩ := by
          apply Fin.ext
          rfl
        have hsource :=
          rate_mul_chronologicalRemotePredecessorTime_succ_sub_eq_reverseRemotePastService
            target (capacity * weight target) z N older
        rw [hsucc, hcast] at hsource
        calc
          (capacity * weight target) *
              finiteGPSConstantRateProjectionBlockDuration (blocks j) =
              (capacity * weight target) *
                (taggedAdmittedChronologicalRemotePredecessorTime
                  target z (N + 1) j -
                  taggedAdmittedChronologicalRemotePredecessorTime
                    target z (N + 1) ⟨j.1 - 1, by omega⟩) := by
            rw [hlaterDuration j hj_pos]
          _ = reverseRemotePastIncrement
                (stationaryAdmittedTargetPalmRemotePastService
                  target (capacity * weight target) z)
                (N + 1) (j.1 - 1) := by
            simpa [older] using hsource

/-- The exact closed executable GPS scalar comparator agrees with the finite
literal target-only comparator pre-tag workload.  The proof preserves every
physical service interval: source-empty intervals are compressed only into
the preceding service coordinate, and the terminal source-to-tag suffix is
kept as the final reflected service update. -/
theorem taggedAdmittedFiniteGPSClosedSegmentComparator_eq_stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    finiteGPSConstantRateSegmentComparator (capacity * weight target) target
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments =
      stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target (capacity * weight target) z remoteStart := by
  classical
  let partition := taggedAdmittedClosedPreTagSourceProjectionPartition
    resetTime target z htarget_good capacity weight remoteStart
  let terminalZero := partition.2.map (fun step => step.segment)
  rcases exists_taggedAdmittedClosedPreTagSourceProjection_chronologicalRetainedReplay
      resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_le_zero
      hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg with
      ⟨blocks, hblocks, hretainedReplay⟩
  have hrate_nonneg : 0 ≤ capacity * weight target :=
    mul_nonneg hcapacity.le (hweight_pos target).le
  have hfirstService_nonneg : 0 ≤ taggedAdmittedClosedPreTagFirstTargetService
      (capacity * weight target) resetTime target z remoteStart := by
    unfold taggedAdmittedClosedPreTagFirstTargetService
    split
    · norm_num
    · rename_i hremoteStart_ne_zero
      have hremoteStart_pos : 0 < remoteStart := Nat.pos_of_ne_zero hremoteStart_ne_zero
      have hfirst_index_lt : remoteStart - 1 < remoteStart := by omega
      have hfirst_time : resetTime ≤
          taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart
            ⟨0, hremoteStart_pos⟩ := by
        have hcoverage_first := (hcoverage (remoteStart - 1)).mpr hfirst_index_lt
        simpa [taggedAdmittedChronologicalRemotePredecessorTime,
          taggedAdmittedChronologicalRemotePredecessorIndex] using hcoverage_first
      exact mul_nonneg hrate_nonneg (sub_nonneg.mpr hfirst_time)
  have hterminal_duration : finiteGPSExecutionSegmentsTotalDuration terminalZero =
      if remoteStart = 0 then 0 - resetTime else
        0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by
    simpa [partition, terminalZero] using
      (taggedAdmittedClosedPreTagSourceProjectionPartition_terminal_duration_eq
        resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_le_zero
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg)
  have hterminalService_nonneg_of_zero : remoteStart = 0 →
      0 ≤ (capacity * weight target) *
        finiteGPSExecutionSegmentsTotalDuration terminalZero := by
    intro hremoteStart_zero
    rw [hterminal_duration, if_pos hremoteStart_zero]
    exact mul_nonneg hrate_nonneg (sub_nonneg.mpr hreset_le_zero)
  have hterminalService_eq_final_of_succ : ∀ n, remoteStart = n + 1 →
      (capacity * weight target) *
        finiteGPSExecutionSegmentsTotalDuration terminalZero =
        reverseRemotePastIncrement
          (stationaryAdmittedTargetPalmRemotePastService
            target (capacity * weight target) z) remoteStart n := by
    intro n hremoteStart
    rw [hterminal_duration, if_neg (by omega)]
    calc
      (capacity * weight target) *
          (0 - candidatePalmArrival z.1.1 (Int.negSucc 0)) =
          stationaryAdmittedTargetPalmRemotePastService
            target (capacity * weight target) z 0 := by
        symm
        exact stationaryAdmittedTargetPalmRemotePastService_zero_eq_rate_mul_tag_sub_predecessor
          target (capacity * weight target) z
      _ = reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService
              target (capacity * weight target) z) remoteStart n := by
        simp [reverseRemotePastIncrement, hremoteStart]
  have hprojection : finiteGPSConstantRateProjectionComparatorFrom 0
      (capacity * weight target) target (List.ofFn blocks) terminalZero =
      lateBatchPreWorkload
        (reverseRemotePastIncrement
          (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
        (reverseRemotePastIncrement
          (stationaryAdmittedTargetPalmRemotePastService
            target (capacity * weight target) z) remoteStart)
        remoteStart := by
    exact finiteGPSConstantRateProjectionComparatorFrom_eq_lateBatchPreWorkload_of_retainedReplay_eq
      (capacity * weight target) target blocks terminalZero
      (taggedAdmittedClosedPreTagFirstTargetService
        (capacity * weight target) resetTime target z remoteStart)
      (reverseRemotePastIncrement
        (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
      (reverseRemotePastIncrement
        (stationaryAdmittedTargetPalmRemotePastService
          target (capacity * weight target) z) remoteStart)
      hretainedReplay hfirstService_nonneg hterminalService_nonneg_of_zero
      hterminalService_eq_final_of_succ
  calc
    finiteGPSConstantRateSegmentComparator (capacity * weight target) target
        (taggedAdmittedFiniteGPSClosedPreTagHistory
          resetTime 0 target z htarget_good capacity weight).segments =
        finiteGPSConstantRateProjectionComparatorFrom 0
          (capacity * weight target) target
          (partition.1.map FiniteGPSFCFSSemanticProjectionBlock.erase)
          terminalZero := by
      simpa [partition, terminalZero] using
        (taggedAdmittedFiniteGPSClosedSegmentComparator_eq_sourceProjection
          resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_le_zero
          hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg)
    _ = finiteGPSConstantRateProjectionComparatorFrom 0
          (capacity * weight target) target (List.ofFn blocks) terminalZero := by
      rw [hblocks]
    _ = lateBatchPreWorkload
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService
              target (capacity * weight target) z) remoteStart)
          remoteStart := hprojection
    _ = stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
          target (capacity * weight target) z remoteStart := by
      rfl

/-- At the literal pre-tag horizon, the executable GPS target workload is
bounded by the same finite direct target-only comparator state.  This merely
composes the pre-existing semantic GPS comparison with the source-replay
identity above; it does not claim tagged completion or a stationary tail. -/
theorem taggedAdmittedFiniteGPSRun_target_workload_le_stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ) (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hreset_le_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    (taggedAdmittedFiniteGPSRun
      resetTime 0 target z htarget_good capacity weight (fun _ => 0)
      hreset_le_zero).workload target ≤
      stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target (capacity * weight target) z remoteStart := by
  calc
    (taggedAdmittedFiniteGPSRun
        resetTime 0 target z htarget_good capacity weight (fun _ => 0)
        hreset_le_zero).workload target ≤
        finiteGPSConstantRateSegmentComparator (capacity * weight target) target
          (taggedAdmittedFiniteGPSClosedPreTagHistory
            resetTime 0 target z htarget_good capacity weight).segments :=
      taggedAdmittedFiniteGPSRun_target_workload_le_constantRateClosedSegmentComparator
        resetTime 0 target z htarget_good capacity weight hreset_le_zero
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg
    _ = stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
          target (capacity * weight target) z remoteStart :=
      taggedAdmittedFiniteGPSClosedSegmentComparator_eq_stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        resetTime target z htarget_good capacity weight remoteStart hcoverage hreset_le_zero
        hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
