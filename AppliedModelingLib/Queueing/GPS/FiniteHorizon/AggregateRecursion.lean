import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Drain
import AppliedModelingLib.Queueing.Lindley.Recursion
import Mathlib.Tactic

/-!
# Aggregate recursion for the executable finite GPS runner

This module identifies the aggregate workload produced by the actual bounded
GPS gap runner.  It is purely deterministic: the endpoint batch is applied
after service over the preceding gap, so the aggregate update is the usual
reflected work-conservation update followed by that batch.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

omit [DecidableEq Class] in
/-- An internal finite-GPS event can occur only from a nonempty workload. -/
theorem finiteGPSActiveClasses_nonempty_of_internal
    {capacity nextBatchDelay : Real} {weight work : Class -> Real}
    (hinternal :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay) :
    (finiteGPSActiveClasses work).Nonempty := by
  by_contra hactive
  apply hinternal
  simp [finiteGPSNextStepDuration, hactive]

/--
At an external endpoint, the aggregate of the concrete next-event state is
the reflected pre-batch aggregate work plus the endpoint batch.  The result
uses the actual finite GPS event kernel; it is not an assumed scalar queue
recurrence.
-/
theorem finiteGPSNextEventState_aggregateWork_eq_max_sub_capacity_mul_add_batch_of_external
    (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hexternal :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay = nextBatchDelay) :
    finiteGPSAggregateWork
        (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) =
      max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
        finiteGPSAggregateWork batchWork := by
  by_cases hactive : (finiteGPSActiveClasses work).Nonempty
  · let zeroNext := finiteGPSNextEventState capacity weight work (fun _ => 0)
      nextBatchDelay
    have hzero_nonneg : ∀ i, 0 ≤ zeroNext i := by
      intro i
      exact finiteGPSNextEventState_nonneg (i := i) (by intro j; norm_num)
    have hzero_balance :
        finiteGPSAggregateWork zeroNext =
          finiteGPSAggregateWork work - capacity * nextBatchDelay := by
      have hbalance :=
        finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
          (nextBatchDelay := nextBatchDelay)
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
      simpa [zeroNext, hexternal] using hbalance
    have hpre_nonneg :
        0 ≤ finiteGPSAggregateWork work - capacity * nextBatchDelay := by
      rw [← hzero_balance]
      exact finiteGPSAggregateWork_nonneg hzero_nonneg
    have hbalance :=
      finiteGPSBuildExecutionSegment_aggregateWork_balance_of_active_nonempty
        capacity (weight := weight) (work := work) (batchWork := batchWork)
        0 nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
    calc
      finiteGPSAggregateWork
          (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) =
          finiteGPSAggregateWork work + finiteGPSAggregateWork batchWork -
            capacity * nextBatchDelay := by
              simpa [finiteGPSAggregateEndpointWork, finiteGPSAggregateEndpointBatchWork,
                finiteGPSBuildExecutionSegment, finiteGPSBatchApplied, hexternal] using hbalance
      _ = max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
            finiteGPSAggregateWork batchWork := by
              rw [max_eq_left hpre_nonneg]
              ring
  · have hactive_empty : finiteGPSActiveClasses work = Finset.empty :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have hwork_zero : finiteGPSAggregateWork work = 0 :=
      (finiteGPSAggregateWork_eq_zero_iff_activeClasses_eq_empty hwork_nonneg).mpr
        hactive_empty
    have hcapacity_delay_nonneg : 0 ≤ capacity * nextBatchDelay :=
      mul_nonneg hcapacity.le hnextBatchDelay_nonneg
    have hbalance :=
      finiteGPSBuildExecutionSegment_aggregateWork_balance_of_active_empty
        capacity (weight := weight) (work := work) (batchWork := batchWork)
        0 nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive_empty
    calc
      finiteGPSAggregateWork
          (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) =
          0 + finiteGPSAggregateWork batchWork := by
              simpa [finiteGPSAggregateEndpointWork, finiteGPSAggregateEndpointBatchWork,
                finiteGPSBuildExecutionSegment, finiteGPSBatchApplied, hexternal, hwork_zero]
                using hbalance
      _ = max (0 - capacity * nextBatchDelay) 0 +
            finiteGPSAggregateWork batchWork := by
              rw [max_eq_right (sub_nonpos.mpr hcapacity_delay_nonneg)]
      _ = max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
            finiteGPSAggregateWork batchWork := by rw [hwork_zero]

/--
An internal finite-GPS step carries no endpoint batch, so its actual aggregate
workload is the prior aggregate minus full-capacity service for that step.
-/
theorem finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_of_internal
    (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hactive : (finiteGPSActiveClasses work).Nonempty)
    (hinternal :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay) :
    finiteGPSAggregateWork
        (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) =
      finiteGPSAggregateWork work -
        capacity * finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  have hstate_eq :
      finiteGPSNextEventState capacity weight work batchWork nextBatchDelay =
        finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay := by
    funext i
    simp [finiteGPSNextEventState, finiteGPSBatchApplied, hinternal]
  rw [hstate_eq]
  exact finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive

/--
At the active-class fuel bound, the actual finite GPS gap runner has the
scalar reflected aggregate recursion.  This is the deterministic bridge from
the executable runner to a later Lindley-style regeneration argument.
-/
theorem finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch_of_activeCard_lt
    (fuel : Nat) (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel) :
    finiteGPSAggregateWork
        (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload =
      max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
        finiteGPSAggregateWork batchWork := by
  induction fuel generalizing work nextBatchDelay with
  | zero => exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
      by_cases hexternal : duration = nextBatchDelay
      · have hstep :=
          finiteGPSNextEventState_aggregateWork_eq_max_sub_capacity_mul_add_batch_of_external
            capacity (weight := weight) (work := work) (batchWork := batchWork)
            nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            hnextBatchDelay_nonneg (by simpa [duration] using hexternal)
        simpa [finiteGPSRunGap, duration, nextWork, hexternal] using hstep
      · have hactive : (finiteGPSActiveClasses work).Nonempty :=
          finiteGPSActiveClasses_nonempty_of_internal (by simpa [duration] using hexternal)
        have hnext_nonneg : ∀ i, 0 ≤ nextWork i := by
          intro i
          simpa [nextWork] using
            (finiteGPSNextEventState_nonneg_of_internal (batchWork := batchWork)
              (by simpa [duration] using hexternal) i)
        have hremaining_nonneg : 0 ≤ nextBatchDelay - duration := by
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work nextBatchDelay)
        have hdescent : finiteGPSActiveClasses nextWork ⊂ finiteGPSActiveClasses work := by
          exact finiteGPSActiveClasses_ssubset_nextEvent_of_internal
            (batchWork := batchWork) hcapacity hweight_pos htotal_weight_le_one
            hwork_nonneg (by simpa [duration] using hexternal)
        have hnext_fuel : (finiteGPSActiveClasses nextWork).card < fuel := by
          exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
            (Nat.lt_succ_iff.mp hfuel)
        have htail := ih (work := nextWork)
          (nextBatchDelay := nextBatchDelay - duration)
          hnext_nonneg hremaining_nonneg hnext_fuel
        have hstep :=
          finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_of_internal
            capacity (weight := weight) (work := work) (batchWork := batchWork)
            nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
            (by simpa [duration] using hexternal)
        calc
          finiteGPSAggregateWork
              (finiteGPSRunGap (fuel + 1) capacity weight work batchWork nextBatchDelay).workload =
              finiteGPSAggregateWork
                (finiteGPSRunGap fuel capacity weight nextWork batchWork
                  (nextBatchDelay - duration)).workload := by
                    simp [finiteGPSRunGap, duration, nextWork, hexternal]
          _ = max (finiteGPSAggregateWork nextWork -
                capacity * (nextBatchDelay - duration)) 0 +
                finiteGPSAggregateWork batchWork := htail
          _ = max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
                finiteGPSAggregateWork batchWork := by
                  rw [show finiteGPSAggregateWork nextWork =
                    finiteGPSAggregateWork work - capacity * duration by
                      simpa [nextWork] using hstep]
                  congr 2
                  ring

/-- The standard finite active-class fuel bound instantiates the exact aggregate recursion. -/
theorem finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
    (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    finiteGPSAggregateWork
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work batchWork nextBatchDelay).workload =
      max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 +
        finiteGPSAggregateWork batchWork := by
  exact finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch_of_activeCard_lt
    ((finiteGPSActiveClasses work).card + 1) capacity nextBatchDelay hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg (Nat.lt_succ_self _)

/--
The actual aggregate GPS gap is one `lateBatchUpdate`: `work` is the
post-batch state at the left endpoint, full-capacity service is accrued over
the gap, and `batchWork` is applied at the right endpoint.  This is only a
single-gap identity; constructing an indexed trace and its source law remains
a separate task.
-/
theorem finiteGPSRunGap_aggregateWork_eq_lateBatchUpdate
    (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    finiteGPSAggregateWork
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work batchWork nextBatchDelay).workload =
      lateBatchUpdate (finiteGPSAggregateWork work) (capacity * nextBatchDelay)
        (finiteGPSAggregateWork batchWork) := by
  simpa [lateBatchUpdate] using
    (finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
      capacity nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hnextBatchDelay_nonneg)

/--
Removing the endpoint batch from the actual post-batch runner state recovers
the aggregate just before that batch.  This is the form that composes into a
standard Lindley recursion when pre-batch states are used as the embedded
state sequence.
-/
theorem finiteGPSRunGap_aggregatePreBatchWork_eq_max_sub_capacity_mul
    (capacity : Real) {weight work batchWork : Class -> Real}
    (nextBatchDelay : Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    finiteGPSAggregateWork
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work batchWork nextBatchDelay).workload -
        finiteGPSAggregateWork batchWork =
      max (finiteGPSAggregateWork work - capacity * nextBatchDelay) 0 := by
  rw [finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
    capacity nextBatchDelay hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    hnextBatchDelay_nonneg]
  ring

end

end AppliedModelingLib.Probability.Queueing
