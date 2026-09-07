import AppliedModelingLib.Queueing.GPS.FiniteHorizon.AggregateWork
import Mathlib.Tactic

/-!
# Empty-input draining for finite GPS execution

This module proves the deterministic reset implication needed by a later
regenerative construction.  On a finite class system with positive capacity
and positive GPS weights, a zero-work external batch placed sufficiently far
in the future leaves every class empty.  The result concerns one finite gap
only; it does not assert that such gaps recur under a stochastic input law,
construct a stationary state, or make a Palm/tail claim.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The aggregate workload of a nonnegative finite GPS snapshot is
nonnegative. -/
theorem finiteGPSAggregateWork_nonneg
    {work : Class -> Real} (hwork_nonneg : forall i, 0 <= work i) :
    0 <= finiteGPSAggregateWork work := by
  unfold finiteGPSAggregateWork
  exact Finset.sum_nonneg fun i _ => hwork_nonneg i

/-- With a zero endpoint batch and a nonempty active set, one concrete GPS
event has the work-conserving aggregate balance `W' = W - C * duration`. -/
theorem finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
    {capacity nextBatchDelay : Real} {weight work : Class -> Real}
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall i, 0 <= work i)
    (hactive : (finiteGPSActiveClasses work).Nonempty) :
    finiteGPSAggregateWork
        (finiteGPSNextEventState capacity weight work (fun _ => 0) nextBatchDelay) =
      finiteGPSAggregateWork work -
        capacity * finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  have hbalance :=
    finiteGPSBuildExecutionSegment_aggregateWork_balance_of_active_nonempty
      capacity (weight := weight) (work := work) (batchWork := fun _ => 0)
      (startTime := 0) (nextBatchDelay := nextBatchDelay)
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
  simpa [finiteGPSAggregateEndpointWork, finiteGPSAggregateEndpointBatchWork,
    finiteGPSBuildExecutionSegment, finiteGPSBatchApplied] using hbalance

/-- A nonnegative workload with no active class is identically zero. -/
theorem finiteGPS_all_work_eq_zero_of_activeClasses_eq_empty
    {work : Class -> Real} (hwork_nonneg : forall i, 0 <= work i)
    (hactive_empty : finiteGPSActiveClasses work = Finset.empty) :
    forall i, work i = 0 := by
  exact (finiteGPSActiveClasses_eq_empty_iff_all_work_eq_zero hwork_nonneg).mp
    hactive_empty

/--
The executable finite GPS gap clears all work before a zero-work endpoint
whenever the supplied zero-input duration has at least the initial aggregate
work divided by capacity.  The proof follows the actual internal depletion
recursion: a strictly internal event removes an active class, and an external
endpoint is reached only after the full requested duration has been served.

The statement deliberately requires the finite active-class fuel bound.  The
standard horizon fence instantiates that bound with `card active + 1`.
-/
theorem finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
    (fuel : Nat) {capacity nextBatchDelay : Real} {weight work : Class -> Real}
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall i, 0 <= work i)
    (hnextBatchDelay_nonneg : 0 <= nextBatchDelay)
    (haggregate_le : finiteGPSAggregateWork work <= capacity * nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel) :
    forall i,
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0) nextBatchDelay).workload i = 0 := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
        nextBatchDelay
      by_cases hactive : (finiteGPSActiveClasses work).Nonempty
      · by_cases hterminal : duration = nextBatchDelay
        · have hnext_nonneg : forall i, 0 <= nextWork i := by
            intro i
            exact finiteGPSNextEventState_nonneg (i := i) (by intro j; norm_num)
          have hnext_aggregate :
              finiteGPSAggregateWork nextWork =
                finiteGPSAggregateWork work - capacity * duration := by
            exact finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
          have hnext_aggregate_le_zero : finiteGPSAggregateWork nextWork <= 0 := by
            rw [hnext_aggregate, hterminal]
            linarith
          have hnext_aggregate_eq_zero : finiteGPSAggregateWork nextWork = 0 :=
            le_antisymm hnext_aggregate_le_zero
              (finiteGPSAggregateWork_nonneg hnext_nonneg)
          have hnext_zero : forall i, nextWork i = 0 :=
            (finiteGPSAggregateWork_eq_zero_iff_all_work_eq_zero hnext_nonneg).mp
              hnext_aggregate_eq_zero
          intro i
          simp only [finiteGPSRunGap]
          simpa [duration, nextWork, hterminal] using hnext_zero i
        · have hnext_nonneg : forall i, 0 <= nextWork i := by
            intro i
            simpa [nextWork] using
              (finiteGPSNextEventState_nonneg_of_internal (batchWork := fun _ => 0)
                (by simpa [duration] using hterminal) i)
          have hdescent : finiteGPSActiveClasses nextWork ⊂
              finiteGPSActiveClasses work := by
            exact finiteGPSActiveClasses_ssubset_nextEvent_of_internal
              (batchWork := fun _ => 0) hcapacity hweight_pos htotal_weight_le_one
              hwork_nonneg (by simpa [duration, nextWork] using hterminal)
          have hnext_fuel : (finiteGPSActiveClasses nextWork).card < fuel := by
            exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
              (Nat.lt_succ_iff.mp hfuel)
          have hduration_nonneg : 0 <= duration := by
            exact finiteGPSNextStepDuration_nonneg hcapacity hweight_pos
              htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg
          have hremaining_nonneg : 0 <= nextBatchDelay - duration := by
            exact sub_nonneg.mpr
              (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work nextBatchDelay)
          have hnext_aggregate :
              finiteGPSAggregateWork nextWork =
                finiteGPSAggregateWork work - capacity * duration := by
            exact finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
          have hnext_aggregate_le :
              finiteGPSAggregateWork nextWork <=
                capacity * (nextBatchDelay - duration) := by
            rw [hnext_aggregate]
            ring_nf
            linarith
          have htail := ih (work := nextWork)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_nonneg hremaining_nonneg hnext_aggregate_le hnext_fuel
          intro i
          simp only [finiteGPSRunGap]
          simpa [duration, nextWork, hterminal] using htail i
      · have hactive_empty : finiteGPSActiveClasses work = Finset.empty :=
          Finset.not_nonempty_iff_eq_empty.mp hactive
        have hwork_zero : forall i, work i = 0 :=
          finiteGPS_all_work_eq_zero_of_activeClasses_eq_empty hwork_nonneg hactive_empty
        intro i
        have hrate_zero : finiteGPSClassRate capacity weight work i = 0 :=
          finiteGPSClassRate_eq_zero_of_not_active (by
            simpa [hwork_zero i])
        simp [finiteGPSRunGap, finiteGPSNextStepDuration, hactive,
          finiteGPSNextEventState, finiteGPSBatchApplied, finiteGPSRemainingAfter,
          hwork_zero i, hrate_zero]

/-- A terminal zero-work horizon fence clears a nonnegative finite GPS state
whenever its duration has enough capacity to cover the current aggregate
work.  This is the deterministic empty-state implication consumed by a
future stochastic regeneration proof. -/
theorem finiteGPSHorizonFence_workload_eq_zero_of_aggregate_le_capacity_mul
    (capacity : Real) (weight : Class -> Real)
    (result : FiniteGPSBatchTraceResult Class) (horizon : Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall i, 0 <= result.workload i)
    (hcurrentTime_le_horizon : result.currentTime <= horizon)
    (haggregate_le : finiteGPSAggregateWork result.workload <=
      capacity * (horizon - result.currentTime)) :
    forall i, (finiteGPSHorizonFence capacity weight result horizon).workload i = 0 := by
  exact finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
    ((finiteGPSActiveClasses result.workload).card + 1) hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hcurrentTime_le_horizon)
    haggregate_le (Nat.lt_succ_self _)

end

end AppliedModelingLib.Probability.Queueing
