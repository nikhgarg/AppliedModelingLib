import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchIndexedTrace
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteExecution
import Mathlib.Tactic

/-!
# Aggregate late-batch steps for a tagged admitted finite GPS trace

This module connects the literal finite target/passive source ledger to the
deterministic aggregate late-batch GPS step interface.  It records only the
actual finite chronological source batches already selected by
`taggedAdmittedBatchTimeTrace`.

There is intentionally no infinite enumeration, drift theorem, reset
occurrence, Palm conclusion, or stationary-workload claim here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The canonical aggregate late-batch view of the actual tagged-admitted
finite GPS execution. -/
def taggedAdmittedFiniteGPSAggregateLateBatchSteps
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    List FiniteGPSAggregateLateBatchStep :=
  finiteGPSAggregateLateBatchSteps capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedBatchTimeTrace start horizon target z)

/-- Every recorded tagged-admitted source step obeys the actual finite GPS
aggregate service-before-arrival update. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_all_valid
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ k, 0 ≤ initialWork k)
    (hwork_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∀ step ∈ taggedAdmittedFiniteGPSAggregateLateBatchSteps
      start horizon target z capacity weight initialWork, step.Valid := by
  unfold taggedAdmittedFiniteGPSAggregateLateBatchSteps
  apply finiteGPSAggregateLateBatchSteps_all_valid capacity weight initialWork
    (taggedAdmittedBatchAt start horizon target z) start
    (taggedAdmittedBatchTimeTrace start horizon target z)
    hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
  · exact (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  · intro eventTime _ k
    exact taggedAdmittedBatchAt_nonneg start horizon target z hwork_nonneg eventTime k

/-- Consecutive aggregate steps of the tagged-admitted finite trace have
matching batch-time and aggregate-work endpoints. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_contiguous
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ) :
    FiniteGPSAggregateLateBatchStepsContiguous
      (taggedAdmittedFiniteGPSAggregateLateBatchSteps
        start horizon target z capacity weight initialWork) := by
  unfold taggedAdmittedFiniteGPSAggregateLateBatchSteps
  exact finiteGPSAggregateLateBatchSteps_contiguous capacity weight
    (taggedAdmittedBatchAt start horizon target z) start initialWork
    (taggedAdmittedBatchTimeTrace start horizon target z)

/-- A recorded tagged-admitted aggregate step has a batch time from the
literal chronological source trace. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_batchTime
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ taggedAdmittedFiniteGPSAggregateLateBatchSteps
      start horizon target z capacity weight initialWork) :
    step.batchTime ∈ taggedAdmittedBatchTimeTrace start horizon target z := by
  simpa [taggedAdmittedFiniteGPSAggregateLateBatchSteps] using
    (finiteGPSAggregateLateBatchSteps_mem_batchTime capacity weight
      (taggedAdmittedBatchAt start horizon target z) start initialWork
      (taggedAdmittedBatchTimeTrace start horizon target z) hmem)

/-- Every recorded step batch time is the epoch of an actual literal source
record in the finite tagged-admitted ledger. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_source_epoch
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ taggedAdmittedFiniteGPSAggregateLateBatchSteps
      start horizon target z capacity weight initialWork) :
    ∃ job : TaggedAdmittedSourceJobId Category,
      job ∈ taggedAdmittedSourceJobLedger start horizon target z ∧
        taggedAdmittedSourceArrival target z job = step.batchTime := by
  have htime := taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_batchTime
    start horizon target z capacity weight initialWork hmem
  have htime_finset : step.batchTime ∈ taggedAdmittedBatchTimes start horizon target z :=
    (Finset.mem_sort (fun s t : ℝ => s ≤ t)).mp htime
  exact (mem_taggedAdmittedBatchTimes_iff start horizon target z step.batchTime).mp htime_finset

/-- The stored aggregate batch work of a tagged-admitted step is exactly the
aggregate of the literal collapsed batch at its own source epoch. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_batchAggregateWork
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ taggedAdmittedFiniteGPSAggregateLateBatchSteps
      start horizon target z capacity weight initialWork) :
    step.batchAggregateWork =
      finiteGPSAggregateWork
        (taggedAdmittedBatchAt start horizon target z step.batchTime) := by
  simpa [taggedAdmittedFiniteGPSAggregateLateBatchSteps] using
    (finiteGPSAggregateLateBatchSteps_mem_batchAggregateWork capacity weight
      (taggedAdmittedBatchAt start horizon target z) start initialWork
      (taggedAdmittedBatchTimeTrace start horizon target z) hmem)

/-- The aggregate batch field expands to the literal finite sum of all source
work marks whose source epoch equals the step's batch time. -/
theorem taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_batchAggregateWork_eq_literal
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ taggedAdmittedFiniteGPSAggregateLateBatchSteps
      start horizon target z capacity weight initialWork) :
    step.batchAggregateWork =
      ∑ k : Category,
        ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k with
          taggedAdmittedSourceArrival target z (k, n) = step.batchTime,
          taggedAdmittedSourceWork target z (k, n) := by
  calc
    step.batchAggregateWork =
        finiteGPSAggregateWork
          (taggedAdmittedBatchAt start horizon target z step.batchTime) :=
      taggedAdmittedFiniteGPSAggregateLateBatchSteps_mem_batchAggregateWork
        start horizon target z capacity weight initialWork hmem
    _ = ∑ k : Category,
        ∑ n ∈ taggedAdmittedArrivalIndicesBetween start horizon target z k with
          taggedAdmittedSourceArrival target z (k, n) = step.batchTime,
          taggedAdmittedSourceWork target z (k, n) := by
      rfl

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
