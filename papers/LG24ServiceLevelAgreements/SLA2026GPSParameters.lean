import LG24ServiceLevelAgreements.SLA2026Reformulation
import LG24ServiceLevelAgreements.SLA2026StochasticPrimitives
import Mathlib.Tactic

/-!
# GPS parameters and aggregate stability for the SLA queue model

This module separates the two conditions used by the stationary GPS proof:
positive GPS weights and strict aggregate workload slack construct the global
remote-past queue, while a target's guaranteed-service slack is supplied only
where the target-comparator tail needs it.  The paper's fixed-load program
derives both facts, but the standalone response display should not silently
turn the target-local tail margin into an all-class premise.

It does not construct a queue state, stationarity, Palm law, or response time.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

variable {Category : Type*} [Fintype Category]

/-- Globally stationary GPS data for one Borough.  This record contains only
the conditions needed to construct the full steady queue.  The response-tail
route accepts its target-local guaranteed-service inequality separately. -/
structure SLA2026BoroughGPSParameters
    (input : SLA2026BoroughQueueingInput Category) where
  capacity : Real
  weight : Category -> Real
  capacity_nonneg : 0 <= capacity
  total_weight_le_one : Finset.univ.sum weight <= 1
  weight_pos : forall k, 0 < weight k
  total_admitted_lt_capacity : Finset.univ.sum input.admittedRate < capacity

namespace SLA2026BoroughGPSParameters

variable {input : SLA2026BoroughQueueingInput Category}

/-- Strict aggregate slack forces positive capacity, including when the
category type is empty. -/
theorem capacity_pos (G : SLA2026BoroughGPSParameters input) (k : Category) :
    0 < G.capacity := by
  have hsum_nonneg : 0 <= Finset.univ.sum input.admittedRate := by
    exact Finset.sum_nonneg (fun i _ => (input.admittedRate_pos i).le)
  exact hsum_nonneg.trans_lt G.total_admitted_lt_capacity

/-- The global stationary construction uses strict aggregate load below
capacity.  The fixed-load bridge below derives this fact from all-cell SLA
constraints; target-local response arguments do not use that derivation. -/
theorem total_admittedRate_lt_capacity
    (G : SLA2026BoroughGPSParameters input) (tag : Category) :
    (Finset.univ.sum input.admittedRate) < G.capacity := by
  exact G.total_admitted_lt_capacity

/-- Construct the internal scheduler parameters from separately supplied
aggregate steady-queue facts.  Paper-facing definitions keep those facts in
their source-level predicate rather than exposing this record constructor. -/
def ofAggregateSteady
    (input : SLA2026BoroughQueueingInput Category)
    (capacity : Real) (weight : Category -> Real)
    (hcapacity : 0 <= capacity)
    (hweight : forall k, 0 < weight k)
    (htotalWeight : Finset.univ.sum weight <= 1)
    (htotalLoad : Finset.univ.sum input.admittedRate < capacity) :
    SLA2026BoroughGPSParameters input where
  capacity := capacity
  weight := weight
  capacity_nonneg := hcapacity
  total_weight_le_one := htotalWeight
  weight_pos := hweight
  total_admitted_lt_capacity := htotalLoad

/-- The source's original fixed-load feasibility constraints discharge the
strict per-class GPS slack required by the queue construction.  This bridge
is intentionally restricted to the fixed-load policy model, where a positive
tail constant and positive thresholds are explicit source conditions; it does
not assert that the informal queue paragraph alone supplies them. -/
def ofOriginalFixedLoadFeasible
    {Borough : Type*} [Fintype Borough] [Nonempty Category]
    (input : SLA2026BoroughQueueingInput Category)
    {tail cityCapacity : Real}
    {admitted : Category -> Borough -> Real}
    {policy : SLA2026OriginalFixedLoadPolicy Category Borough}
    (htail : 0 < tail)
    (hpolicy : SLA2026OriginalFixedLoadFeasible tail cityCapacity admitted policy)
    (borough : Borough)
    (hadmitted_column : forall k, admitted k borough = input.admittedRate k) :
    SLA2026BoroughGPSParameters input where
  capacity := policy.boroughCapacity borough
  weight := fun k => policy.gpsWeight k borough
  capacity_nonneg := hpolicy.boroughCapacity_nonneg borough
  total_weight_le_one := hpolicy.gps borough
  weight_pos := by
    intro k
    have hsla := hpolicy.sla k borough
    have hdelay : 0 < policy.delay k borough := hpolicy.delay_pos k borough
    have hslack_times_delay :
        0 < (policy.boroughCapacity borough * policy.gpsWeight k borough -
          admitted k borough) * policy.delay k borough := by
      nlinarith
    have hslack :
        0 < policy.boroughCapacity borough * policy.gpsWeight k borough -
          admitted k borough := by
      rcases (mul_pos_iff.mp hslack_times_delay) with h | h
      · exact h.1
      · exact False.elim ((not_lt_of_ge hdelay.le) h.2)
    have hproduct : 0 < policy.boroughCapacity borough * policy.gpsWeight k borough :=
      (input.admittedRate_pos k).trans (by
        rw [<- hadmitted_column k]
        linarith)
    rcases (mul_pos_iff.mp hproduct) with h | h
    · exact h.2
    · exact False.elim ((not_lt_of_ge (hpolicy.boroughCapacity_nonneg borough)) h.1)
  total_admitted_lt_capacity := by
    have hclass_slack : forall k,
        input.admittedRate k <
          policy.boroughCapacity borough * policy.gpsWeight k borough := by
      intro k
      have hsla := hpolicy.sla k borough
      have hdelay : 0 < policy.delay k borough := hpolicy.delay_pos k borough
      have hslack_times_delay :
          0 < (policy.boroughCapacity borough * policy.gpsWeight k borough -
            admitted k borough) * policy.delay k borough := by
        nlinarith
      have hslack :
          0 < policy.boroughCapacity borough * policy.gpsWeight k borough -
            admitted k borough := by
        rcases (mul_pos_iff.mp hslack_times_delay) with h | h
        · exact h.1
        · exact False.elim ((not_lt_of_ge hdelay.le) h.2)
      rw [<- hadmitted_column k]
      linarith
    have hclass_sum :
        Finset.univ.sum input.admittedRate <
          Finset.univ.sum (fun k =>
            policy.boroughCapacity borough * policy.gpsWeight k borough) := by
      refine Finset.sum_lt_sum (fun k _ => (hclass_slack k).le) ?_
      let k0 : Category := Classical.choice (inferInstance : Nonempty Category)
      exact ⟨k0, Finset.mem_univ _, hclass_slack k0⟩
    calc
      Finset.univ.sum input.admittedRate <
          Finset.univ.sum (fun k =>
            policy.boroughCapacity borough * policy.gpsWeight k borough) := hclass_sum
      _ = policy.boroughCapacity borough *
          Finset.univ.sum (fun k => policy.gpsWeight k borough) := by
        rw [Finset.mul_sum]
      _ <= policy.boroughCapacity borough * 1 :=
        mul_le_mul_of_nonneg_left (hpolicy.gps borough)
          (hpolicy.boroughCapacity_nonneg borough)
      _ = policy.boroughCapacity borough := by ring

end SLA2026BoroughGPSParameters

end

end LG24ServiceLevelAgreements
