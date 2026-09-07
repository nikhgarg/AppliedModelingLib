import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSplit
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.AggregateRecursion
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSResetRestart
import Mathlib.Tactic

/-!
# Closed-run restart for the tagged admitted SLA GPS executor

This module gives the deterministic composition rule needed to splice
finite remote-past blocks.  A computational zero-work fence is inserted at
an arbitrary half-open boundary `resetTime`; it is not a source batch.  The
literal source suffix remains `[resetTime, horizon)`, so all arrivals exactly
at `resetTime` remain in that suffix.

There are no stochastic, Palm, stationary, response-time, or tail claims.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Splitting a terminal computational fence at an intermediate reset time
preserves the closed finite executor.  Both inserted endpoint batches are
zero-work computational fences; this lemma has no source-trace content. -/
private theorem finiteGPSCloseAtHorizon_eq_closeAtReset_then_closeAtHorizon_of_aggregate_drain
    (capacity : ℝ) (weight : Category → ℝ)
    (result : FiniteGPSBatchTraceResult Category) (resetTime horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_reset : result.currentTime ≤ resetTime)
    (hreset_horizon : resetTime ≤ horizon)
    (haggregate_drain : finiteGPSAggregateWork result.workload ≤
      capacity * (resetTime - result.currentTime)) :
    finiteGPSCloseAtHorizon capacity weight result horizon =
      finiteGPSCloseAtHorizon capacity weight
        (finiteGPSCloseAtHorizon capacity weight result resetTime) horizon := by
  have hfirst_delay : 0 ≤ resetTime - result.currentTime :=
    sub_nonneg.mpr hcurrentTime_reset
  have hsecond_delay : 0 ≤ horizon - resetTime :=
    sub_nonneg.mpr hreset_horizon
  have hfirst_terminates := finiteGPSHorizonFence_terminates
    capacity weight result resetTime hcapacity hweight_pos htotal_weight_le_one
    hwork_nonneg hcurrentTime_reset
  have hfirst_remaining :
      (finiteGPSRunGap ((finiteGPSActiveClasses result.workload).card + 1)
        capacity weight result.workload (fun _ => 0)
        (resetTime - result.currentTime)).remainingDelay = 0 := by
    simpa [finiteGPSHorizonFence] using hfirst_terminates.2
  have hsplit := finiteGPSRunGap_fields_eq_splitAtZeroFence_of_aggregate_drain
    capacity weight result.workload (fun _ => 0)
    (resetTime - result.currentTime) (horizon - resetTime)
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    hfirst_delay hsecond_delay haggregate_drain
  have htotal_delay : horizon - result.currentTime =
      (resetTime - result.currentTime) + (horizon - resetTime) := by
    ring
  unfold finiteGPSCloseAtHorizon finiteGPSHorizonFence
  dsimp only
  rw [htotal_delay, hfirst_remaining]
  simp only [sub_zero]
  rw [FiniteGPSBatchTraceResult.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i
    have hworkload := hsplit.1 i
    simpa [finiteGPSRunGapSplitAtZeroFence] using hworkload
  · have hremaining := hsplit.2.1
    simpa [finiteGPSRunGapSplitAtZeroFence] using congrArg (fun x : ℝ => horizon - x) hremaining
  · funext i
    have hservice := hsplit.2.2.1 i
    simpa [finiteGPSRunGapSplitAtZeroFence, add_assoc] using hservice

/-- Adding already-accrued service to a finite trace does not change its
terminal computational fence; it only adds the same prefix service to the
closed result. -/
private theorem finiteGPSCloseAtHorizon_add_prior_service
    (capacity : ℝ) (weight : Category → ℝ)
    (result : FiniteGPSBatchTraceResult Category)
    (priorService : Category → ℝ) (horizon : ℝ) :
    finiteGPSCloseAtHorizon capacity weight
        { workload := result.workload
          currentTime := result.currentTime
          service := fun i => priorService i + result.service i }
        horizon =
      { workload := (finiteGPSCloseAtHorizon capacity weight result horizon).workload
        currentTime := (finiteGPSCloseAtHorizon capacity weight result horizon).currentTime
        service := fun i => priorService i +
          (finiteGPSCloseAtHorizon capacity weight result horizon).service i } := by
  have hfence_eq :
      finiteGPSHorizonFence capacity weight
          { workload := result.workload
            currentTime := result.currentTime
            service := fun i => priorService i + result.service i }
          horizon =
        finiteGPSHorizonFence capacity weight result horizon := by
    unfold finiteGPSHorizonFence
    rfl
  unfold finiteGPSCloseAtHorizon
  dsimp only
  rw [hfence_eq]
  rw [FiniteGPSBatchTraceResult.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  simp [add_assoc]

/-- A zero-work terminal computational fence leaves a zero workload zero and
adds no service.  This deterministic statement does not represent or assert
anything about literal source batches. -/
private theorem finiteGPSCloseAtHorizon_zero
    (capacity : ℝ) (weight : Category → ℝ) (start horizon : ℝ) :
    finiteGPSCloseAtHorizon capacity weight
        { workload := fun _ => 0
          currentTime := start
          service := fun _ => 0 }
        horizon =
      { workload := fun _ => 0
        currentTime := horizon
        service := fun _ => 0 } := by
  unfold finiteGPSCloseAtHorizon finiteGPSHorizonFence
  dsimp only
  have hzero_gap :
      finiteGPSRunGap
          ((finiteGPSActiveClasses (fun _ : Category => (0 : ℝ))).card + 1)
          capacity weight (fun _ => 0) (fun _ => 0)
          (horizon - start) =
        { workload := fun _ => 0
          remainingDelay := 0
          service := fun _ => 0
          batchApplied := true } := by
    simpa [finiteGPSActiveClasses] using
      (finiteGPSRunGap_zeroWork_succ (Class := Category) 0 capacity weight
        (fun _ => 0) (horizon - start))
  rw [hzero_gap]
  simp

/-- If a literal half-open source suffix has no batches, its zero-start
closed run is exactly the source-free computational service fence. -/
private theorem taggedAdmittedFiniteGPSRun_zero_of_empty_source_suffix
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (hreset_horizon : resetTime ≤ horizon)
    (hsuffix_empty : taggedAdmittedBatchTimeTrace resetTime horizon target z = []) :
    taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
        capacity weight (fun _ => 0) hreset_horizon =
      { workload := fun _ => 0
        currentTime := horizon
        service := fun _ => 0 } := by
  have hpreterminal :
      taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
          capacity weight (fun _ => 0) =
        { workload := fun _ => 0
          currentTime := resetTime
          service := fun _ => 0 } := by
    change finiteGPSRunBatchTrace capacity weight
      (taggedAdmittedBatchAt resetTime horizon target z)
      resetTime (fun _ => 0)
      (taggedAdmittedBatchTimeTrace resetTime horizon target z) = _
    simp [hsuffix_empty, finiteGPSRunBatchTrace]
  unfold taggedAdmittedFiniteGPSRun
  rw [hpreterminal]
  exact finiteGPSCloseAtHorizon_zero capacity weight resetTime horizon

/-- When the literal suffix has no source batches, the full pre-terminal
executor is exactly the literal prefix executor.  This is separate from the
later terminal fence, which still advances service through the requested
horizon. -/
private theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_prefix_of_empty_source_suffix
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hsuffix_empty : taggedAdmittedBatchTimeTrace resetTime horizon target z = []) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork := by
  have hrestart := taggedAdmittedFiniteGPSPreTerminalRun_eq_restart_at_reset
    start resetTime horizon target z htarget_good capacity weight initialWork
    hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
    hinit_nonneg hsource_work_nonneg
  have hprefix := taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
    start resetTime horizon target z htarget_good capacity weight initialWork hreset_horizon
  calc
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      finiteGPSRunBatchTraceRestart capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) := hrestart
    _ = finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z) := by
      rw [hsuffix_empty]
      simp [finiteGPSRunBatchTraceRestart, finiteGPSRunBatchTrace]
    _ = taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork := hprefix

/-- If the literal source suffix is nonempty, a drain-certified computational
fence at `resetTime` gives an exact closed-run factorization.  The cumulative
service retains the prefix-fence service, while workload and clock are exactly
those of the zero-start literal suffix closed at the same terminal horizon.
The premise does not make `resetTime` a source epoch. -/
theorem taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_aggregate_drain_of_suffix_nonempty
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hsuffix_nonempty : taggedAdmittedBatchTimeTrace resetTime horizon target z ≠ [])
    (hprefix_aggregate_drain : finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime)) :
    taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
        (hstart_reset.trans hreset_horizon) =
      { workload :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).workload
        currentTime :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
            capacity weight initialWork hstart_reset).service i +
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).service i } := by
  have hpreterminal :=
    taggedAdmittedFiniteGPSPreTerminalRun_eq_closed_prefix_then_source_suffix_of_aggregate_drain
      start resetTime horizon target z htarget_good capacity weight initialWork
      hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
      hinit_nonneg hsource_work_nonneg hsuffix_nonempty hprefix_aggregate_drain
  unfold taggedAdmittedFiniteGPSRun
  rw [hpreterminal]
  exact finiteGPSCloseAtHorizon_add_prior_service capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
      capacity weight (fun _ => 0))
    (fun i =>
      (finiteGPSCloseAtHorizon capacity weight
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork) resetTime).service i)
    horizon

/-- A drain-certified computational fence at any half-open source boundary
gives the exact closed-run restart law.  No literal arrival at `resetTime` is
assumed: when there are such arrivals they are retained in the suffix, and
when the suffix is source-free the separate terminal computational fence is
handled explicitly. -/
theorem taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_aggregate_drain
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hprefix_aggregate_drain : finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime)) :
    taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
        (hstart_reset.trans hreset_horizon) =
      { workload :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).workload
        currentTime :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
            capacity weight initialWork hstart_reset).service i +
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).service i } := by
  by_cases hsuffix_empty : taggedAdmittedBatchTimeTrace resetTime horizon target z = []
  · have hprefix_nonneg : ∀ i,
        0 ≤ (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).workload i := by
      intro i
      exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
        start resetTime target z htarget_good capacity weight initialWork
        hinit_nonneg hsource_work_nonneg i
    have hprefix_currentTime_le :
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime ≤ resetTime :=
      taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
        start resetTime target z htarget_good capacity weight initialWork hstart_reset
    have hprefix_reset := finiteGPSCloseAtHorizon_is_reset_of_aggregate_le_capacity_mul
      capacity weight
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork)
      resetTime hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      hprefix_currentTime_le hprefix_aggregate_drain
    have hfull_preterminal_eq_prefix :=
      taggedAdmittedFiniteGPSPreTerminalRun_eq_prefix_of_empty_source_suffix
        start resetTime horizon target z htarget_good capacity weight initialWork
        hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
        hinit_nonneg hsource_work_nonneg hsuffix_empty
    have hterminal_split :=
      finiteGPSCloseAtHorizon_eq_closeAtReset_then_closeAtHorizon_of_aggregate_drain
        capacity weight
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork)
        resetTime horizon hcapacity hweight_pos htotal_weight_le_one
        hprefix_nonneg hprefix_currentTime_le hreset_horizon hprefix_aggregate_drain
    have hprefix_closed_eq :
        finiteGPSCloseAtHorizon capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork)
            resetTime =
          { workload := fun _ => 0
            currentTime := resetTime
            service := fun i =>
              (finiteGPSCloseAtHorizon capacity weight
                (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                  capacity weight initialWork)
                resetTime).service i } := by
      rw [FiniteGPSBatchTraceResult.mk.injEq]
      refine ⟨?_, hprefix_reset.1, rfl⟩
      funext i
      exact hprefix_reset.2 i
    have hfull_closed_eq :
        taggedAdmittedFiniteGPSRun start horizon target z htarget_good
            capacity weight initialWork (hstart_reset.trans hreset_horizon) =
          { workload := fun _ => 0
            currentTime := horizon
            service := fun i =>
              (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                capacity weight initialWork hstart_reset).service i } := by
      unfold taggedAdmittedFiniteGPSRun
      rw [hfull_preterminal_eq_prefix]
      calc
        finiteGPSCloseAtHorizon capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork)
            horizon =
          finiteGPSCloseAtHorizon capacity weight
            (finiteGPSCloseAtHorizon capacity weight
              (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                capacity weight initialWork)
              resetTime)
            horizon := hterminal_split
        _ = finiteGPSCloseAtHorizon capacity weight
            { workload := fun _ => 0
              currentTime := resetTime
              service := fun i =>
                (finiteGPSCloseAtHorizon capacity weight
                  (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                    capacity weight initialWork)
                  resetTime).service i }
            horizon := by rw [hprefix_closed_eq]
        _ =
          { workload :=
              (finiteGPSCloseAtHorizon capacity weight
                { workload := fun _ => 0
                  currentTime := resetTime
                  service := fun _ => 0 }
                horizon).workload
            currentTime :=
              (finiteGPSCloseAtHorizon capacity weight
                { workload := fun _ => 0
                  currentTime := resetTime
                  service := fun _ => 0 }
                horizon).currentTime
            service := fun i =>
              (finiteGPSCloseAtHorizon capacity weight
                (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                  capacity weight initialWork)
                resetTime).service i +
              (finiteGPSCloseAtHorizon capacity weight
                { workload := fun _ => 0
                  currentTime := resetTime
                  service := fun _ => 0 }
                horizon).service i } :=
          by
            simpa using
              (finiteGPSCloseAtHorizon_add_prior_service capacity weight
                { workload := fun _ => 0
                  currentTime := resetTime
                  service := fun _ => 0 }
                (fun i =>
                  (finiteGPSCloseAtHorizon capacity weight
                    (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                      capacity weight initialWork)
                    resetTime).service i)
                horizon)
        _ =
          { workload := fun _ => 0
            currentTime := horizon
            service := fun i =>
              (finiteGPSCloseAtHorizon capacity weight
                (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                  capacity weight initialWork)
                resetTime).service i } := by
          rw [finiteGPSCloseAtHorizon_zero capacity weight resetTime horizon]
          simp
    have hsuffix_closed_zero := taggedAdmittedFiniteGPSRun_zero_of_empty_source_suffix
      resetTime horizon target z htarget_good capacity weight hreset_horizon hsuffix_empty
    rw [hfull_closed_eq, hsuffix_closed_zero]
    simp
  · exact
      taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_aggregate_drain_of_suffix_nonempty
        start resetTime horizon target z htarget_good capacity weight initialWork
        hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
        hinit_nonneg hsource_work_nonneg hsuffix_empty hprefix_aggregate_drain

/-- An actually empty computationally closed prefix provides the aggregate
drain certificate needed for the source-trace restart theorem.  This is the
reverse direction relevant to finite block constructions: no claim is made
that the fence is a literal source event. -/
theorem taggedAdmittedFiniteGPSPrefix_aggregate_drain_of_closed_prefix_workload_zero
    (start resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hclosed_prefix_zero : ∀ i,
      (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
        capacity weight initialWork hstart_reset).workload i = 0) :
    finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime) := by
  let prefixRun := taggedAdmittedFiniteGPSPreTerminalRun
    start resetTime target z htarget_good capacity weight initialWork
  have hprefix_nonneg : ∀ i, 0 ≤ prefixRun.workload i := by
    intro i
    simpa [prefixRun] using
      (taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
        start resetTime target z htarget_good capacity weight initialWork
        hinit_nonneg hsource_work_nonneg i)
  have hprefix_currentTime_le : prefixRun.currentTime ≤ resetTime := by
    simpa [prefixRun] using
      (taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
        start resetTime target z htarget_good capacity weight initialWork hstart_reset)
  have hfence_zero : ∀ i,
      (finiteGPSHorizonFence capacity weight prefixRun resetTime).workload i = 0 := by
    intro i
    simpa [taggedAdmittedFiniteGPSRun, finiteGPSCloseAtHorizon, prefixRun] using
      hclosed_prefix_zero i
  have hfence_aggregate_zero :
      finiteGPSAggregateWork
          (finiteGPSHorizonFence capacity weight prefixRun resetTime).workload = 0 := by
    unfold finiteGPSAggregateWork
    apply Finset.sum_eq_zero
    intro i _
    exact hfence_zero i
  have haggregate_formula :=
    finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
      capacity (weight := weight) (work := prefixRun.workload) (batchWork := fun _ => 0)
      (resetTime - prefixRun.currentTime)
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      (sub_nonneg.mpr hprefix_currentTime_le)
  have hmax_zero :
      max (finiteGPSAggregateWork prefixRun.workload -
        capacity * (resetTime - prefixRun.currentTime)) 0 = 0 := by
    calc
      max (finiteGPSAggregateWork prefixRun.workload -
          capacity * (resetTime - prefixRun.currentTime)) 0 =
        finiteGPSAggregateWork
          (finiteGPSHorizonFence capacity weight prefixRun resetTime).workload := by
            symm
            simpa [finiteGPSHorizonFence, finiteGPSAggregateWork] using haggregate_formula
      _ = 0 := hfence_aggregate_zero
  have hsub_nonpos :
      finiteGPSAggregateWork prefixRun.workload -
          capacity * (resetTime - prefixRun.currentTime) ≤ 0 := by
    calc
      finiteGPSAggregateWork prefixRun.workload -
          capacity * (resetTime - prefixRun.currentTime) ≤
        max (finiteGPSAggregateWork prefixRun.workload -
          capacity * (resetTime - prefixRun.currentTime)) 0 := le_max_left _ _
      _ = 0 := hmax_zero
  simpa [prefixRun] using sub_nonpos.mp hsub_nonpos

/-- Closed-run restart from the operational empty-prefix condition used by a
finite block proof.  The condition is the workload immediately after the
zero-work fence at `resetTime`, hence immediately before any literal source
batch retained by the half-open suffix. -/
theorem taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_closed_prefix_workload_zero
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hclosed_prefix_zero : ∀ i,
      (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
        capacity weight initialWork hstart_reset).workload i = 0) :
    taggedAdmittedFiniteGPSRun start horizon target z htarget_good capacity weight initialWork
        (hstart_reset.trans hreset_horizon) =
      { workload :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).workload
        currentTime :=
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
            capacity weight initialWork hstart_reset).service i +
          (taggedAdmittedFiniteGPSRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0) hreset_horizon).service i } := by
  apply taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_aggregate_drain
    start resetTime horizon target z htarget_good capacity weight initialWork
    hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
    hinit_nonneg hsource_work_nonneg
  exact taggedAdmittedFiniteGPSPrefix_aggregate_drain_of_closed_prefix_workload_zero
    start resetTime target z htarget_good capacity weight initialWork hstart_reset
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hsource_work_nonneg
    hclosed_prefix_zero

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
