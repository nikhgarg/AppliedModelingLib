import AppliedModelingLib.Queueing.GPS.FiniteHorizon.AggregateRecursion
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSplit
import Mathlib.Tactic

/-!
# Actual pre-batch resets in a finite GPS trace

This module isolates the deterministic bridge between an actual
service-before-arrival GPS step and the existing finite-trace reset splitter.
The endpoint batch in the hypotheses is a supplied external batch: no source
event is inserted or replaced.  The zero-work transit used in the conclusion
only exposes the state immediately before that same endpoint batch.

There is no stochastic, Palm, stationary, or response-time claim here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/--
If the actual GPS gap's aggregate state immediately before its supplied
endpoint batch is zero, then the available service through that actual
endpoint covers the incoming aggregate workload.  The pre-batch aggregate is
read from the executable gap as its post-batch aggregate minus the literal
endpoint-batch aggregate.
-/
theorem finiteGPSAggregate_drain_of_actual_preBatchAggregate_eq_zero
    (capacity : Real) (weight work batchWork : Class -> Real)
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hpreBatch_zero :
      finiteGPSAggregateWork
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work batchWork nextBatchDelay).workload -
          finiteGPSAggregateWork batchWork = 0) :
    finiteGPSAggregateWork work ≤ capacity * nextBatchDelay := by
  have hpreBatch_formula :
      finiteGPSAggregateWork
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work batchWork nextBatchDelay).workload -
          finiteGPSAggregateWork batchWork =
        max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 :=
    finiteGPSRunGap_aggregatePreBatchWork_eq_max_sub_capacity_mul
      capacity nextBatchDelay hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hnextBatchDelay_nonneg
  have hmax_zero :
      max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 = 0 := by
    rw [← hpreBatch_formula]
    exact hpreBatch_zero
  have hsub_nonpos : finiteGPSAggregateWork work - capacity * nextBatchDelay ≤ 0 := by
    calc
      finiteGPSAggregateWork work - capacity * nextBatchDelay ≤
          max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 :=
        le_max_left _ _
      _ = 0 := hmax_zero
  exact sub_nonpos.mp hsub_nonpos

/--
At a real next external batch whose executable pre-batch aggregate is zero,
the raw finite trace can be factored through its zero-work transit at that
same time.  The listed endpoint batch remains the first batch in the suffix;
the transit is not an additional source event.
-/
theorem finiteGPSRunBatchTrace_cons_eq_afterZeroFence_of_actual_preBatch_reset
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime eventTime : Real) (tail : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hcurrentTime_event : currentTime ≤ eventTime)
    (hpreBatch_zero :
      finiteGPSAggregateWork
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork eventTime) (eventTime - currentTime)).workload -
          finiteGPSAggregateWork (batchWork eventTime) = 0) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work (eventTime :: tail) =
      finiteGPSRunBatchTraceAfterZeroFence capacity weight batchWork currentTime work
        eventTime (eventTime :: tail) := by
  have haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (eventTime - currentTime) :=
    finiteGPSAggregate_drain_of_actual_preBatchAggregate_eq_zero
      capacity weight work (batchWork eventTime) (eventTime - currentTime)
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      (sub_nonneg.mpr hcurrentTime_event) hpreBatch_zero
  exact finiteGPSRunBatchTrace_cons_eq_afterZeroFence_of_aggregate_drain
    capacity weight work batchWork currentTime eventTime eventTime tail
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    hcurrentTime_event le_rfl haggregate_drain

end

end AppliedModelingLib.Probability.Queueing
