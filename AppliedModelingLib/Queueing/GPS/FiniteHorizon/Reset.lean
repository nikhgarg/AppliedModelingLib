import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Composition
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Drain
import Mathlib.Tactic

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- A sufficiently long computational zero-work horizon fence is an actual
deterministic reset: it reaches the requested clock and leaves every class
empty. -/
theorem finiteGPSCloseAtHorizon_is_reset_of_aggregate_le_capacity_mul
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon)
    (haggregate_le : finiteGPSAggregateWork result.workload ≤
      capacity * (horizon - result.currentTime)) :
    (finiteGPSCloseAtHorizon capacity weight result horizon).currentTime = horizon ∧
      ∀ i, (finiteGPSCloseAtHorizon capacity weight result horizon).workload i = 0 := by
  constructor
  · exact finiteGPSCloseAtHorizon_currentTime capacity weight result horizon
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hcurrentTime_le_horizon
  · change ∀ i, (finiteGPSHorizonFence capacity weight result horizon).workload i = 0
    exact finiteGPSHorizonFence_workload_eq_zero_of_aggregate_le_capacity_mul
      capacity weight result horizon hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hcurrentTime_le_horizon haggregate_le

/-- After a drain-certified computational reset endpoint, the execution on
any common suffix is exactly the execution started from zero at that endpoint. -/
theorem finiteGPSRunBatchTrace_after_horizon_reset_eq_zero
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) (suffixTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon)
    (haggregate_le : finiteGPSAggregateWork result.workload ≤
      capacity * (horizon - result.currentTime)) :
    finiteGPSRunBatchTrace capacity weight batchWork
        (finiteGPSCloseAtHorizon capacity weight result horizon).currentTime
        (finiteGPSCloseAtHorizon capacity weight result horizon).workload suffixTimes =
      finiteGPSRunBatchTrace capacity weight batchWork horizon (fun _ => 0) suffixTimes := by
  have hreset := finiteGPSCloseAtHorizon_is_reset_of_aggregate_le_capacity_mul
    capacity weight result horizon hcapacity hweight_pos htotal_weight_le_one
    hwork_nonneg hcurrentTime_le_horizon haggregate_le
  have hworkload :
      (finiteGPSCloseAtHorizon capacity weight result horizon).workload = fun _ => 0 := by
    funext i
    exact hreset.2 i
  rw [hreset.1, hworkload]

/-- Two arbitrary finite histories that both drain at the same computational
reset endpoint have the same deterministic continuation on every common suffix. -/
theorem finiteGPSRunBatchTrace_after_horizon_reset_coalesces
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (firstResult secondResult : FiniteGPSBatchTraceResult Class)
    (horizon : ℝ) (suffixTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hfirst_nonneg : ∀ j, 0 ≤ firstResult.workload j)
    (hfirst_currentTime_le : firstResult.currentTime ≤ horizon)
    (hfirst_aggregate_le : finiteGPSAggregateWork firstResult.workload ≤
      capacity * (horizon - firstResult.currentTime))
    (hsecond_nonneg : ∀ j, 0 ≤ secondResult.workload j)
    (hsecond_currentTime_le : secondResult.currentTime ≤ horizon)
    (hsecond_aggregate_le : finiteGPSAggregateWork secondResult.workload ≤
      capacity * (horizon - secondResult.currentTime)) :
    finiteGPSRunBatchTrace capacity weight batchWork
        (finiteGPSCloseAtHorizon capacity weight firstResult horizon).currentTime
        (finiteGPSCloseAtHorizon capacity weight firstResult horizon).workload suffixTimes =
      finiteGPSRunBatchTrace capacity weight batchWork
        (finiteGPSCloseAtHorizon capacity weight secondResult horizon).currentTime
        (finiteGPSCloseAtHorizon capacity weight secondResult horizon).workload suffixTimes := by
  calc
    finiteGPSRunBatchTrace capacity weight batchWork
        (finiteGPSCloseAtHorizon capacity weight firstResult horizon).currentTime
        (finiteGPSCloseAtHorizon capacity weight firstResult horizon).workload suffixTimes =
      finiteGPSRunBatchTrace capacity weight batchWork horizon (fun _ => 0) suffixTimes :=
        finiteGPSRunBatchTrace_after_horizon_reset_eq_zero capacity weight batchWork
          firstResult horizon suffixTimes hcapacity hweight_pos htotal_weight_le_one
          hfirst_nonneg hfirst_currentTime_le hfirst_aggregate_le
    _ = finiteGPSRunBatchTrace capacity weight batchWork
        (finiteGPSCloseAtHorizon capacity weight secondResult horizon).currentTime
        (finiteGPSCloseAtHorizon capacity weight secondResult horizon).workload suffixTimes :=
        (finiteGPSRunBatchTrace_after_horizon_reset_eq_zero capacity weight batchWork
          secondResult horizon suffixTimes hcapacity hweight_pos htotal_weight_le_one
          hsecond_nonneg hsecond_currentTime_le hsecond_aggregate_le).symm

/-- If a chronological finite prefix has reached a zero-work reset state at
`resetTime`, the complete trace factors into its prefix service and the common
zero-state suffix execution.  Thus all state and service increments after the
reset are independent of the earlier nonnegative workload. -/
theorem finiteGPSRunBatchTrace_append_eq_zero_suffix_of_prefix_reset
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime resetTime : ℝ) (prefixTimes suffixTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological :
      FiniteGPSChronologicalFrom currentTime (prefixTimes ++ suffixTimes))
    (hbatch_nonneg : ∀ t ∈ prefixTimes ++ suffixTimes, ∀ j, 0 ≤ batchWork t j)
    (hprefix_currentTime :
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).currentTime =
        resetTime)
    (hprefix_workload_zero : ∀ i,
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).workload i =
        0) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work
        (prefixTimes ++ suffixTimes) =
      { workload :=
          (finiteGPSRunBatchTrace capacity weight batchWork resetTime (fun _ => 0)
            suffixTimes).workload
        currentTime :=
          (finiteGPSRunBatchTrace capacity weight batchWork resetTime (fun _ => 0)
            suffixTimes).currentTime
        service := fun i =>
          (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).service i +
            (finiteGPSRunBatchTrace capacity weight batchWork resetTime (fun _ => 0)
              suffixTimes).service i } := by
  rw [finiteGPSRunBatchTrace_append_eq_restart capacity weight work batchWork
    currentTime prefixTimes suffixTimes hcapacity hweight_pos htotal_weight_le_one
    hwork_nonneg hchronological hbatch_nonneg]
  simp only [finiteGPSRunBatchTraceRestart]
  have hprefix_workload :
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work prefixTimes).workload =
        fun _ => 0 := by
    funext i
    exact hprefix_workload_zero i
  rw [hprefix_currentTime, hprefix_workload]

end

end AppliedModelingLib.Probability.Queueing
