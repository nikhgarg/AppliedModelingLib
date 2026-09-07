import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Aggregate work conservation for finite GPS segments

This module proves the aggregate work identities of one concrete
`finiteGPSBuildExecutionSegment`.  When at least one class has positive
workload, normalized GPS allocates the whole capacity across the active finite
classes; when no class is active, it allocates zero service.  Combining those
facts with the existing exact endpoint balance gives the finite total-work
transition needed by a later regenerative construction.

The scope is a single deterministic finite segment.  No stochastic input,
stationary state, Palm interpretation, tail bound, or post-segment horizon is
asserted here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Total workload over all finite GPS classes. -/
def finiteGPSAggregateWork (work : Class → ℝ) : ℝ :=
  Finset.univ.sum work

/-- Total instantaneous class rate at a fixed finite GPS workload snapshot. -/
def finiteGPSAggregateClassRate
    (capacity : ℝ) (weight work : Class → ℝ) : ℝ :=
  Finset.univ.sum (finiteGPSClassRate capacity weight work)

/-- Total service increment stored in one concrete finite GPS segment. -/
def finiteGPSAggregateServiceIncrement
    (segment : FiniteGPSExecutionSegment Class) : ℝ :=
  Finset.univ.sum segment.serviceIncrement

/-- Total endpoint batch work stored in one concrete finite GPS segment. -/
def finiteGPSAggregateEndpointBatchWork
    (segment : FiniteGPSExecutionSegment Class) : ℝ :=
  Finset.univ.sum segment.endpointBatch

/-- Total post-endpoint workload stored in one concrete finite GPS segment. -/
def finiteGPSAggregateEndpointWork
    (segment : FiniteGPSExecutionSegment Class) : ℝ :=
  Finset.univ.sum segment.endpointWorkload

/-- Sum of weights of the currently active finite GPS classes. -/
def finiteGPSActiveWeightSum
    (weight work : Class → ℝ) : ℝ :=
  (finiteGPSActiveClasses work).sum weight

/-- The active-weight denominator of the finite segment is the existing
backlog-induced GPS denominator at its snapshot. -/
theorem finiteGPSActiveWeightSum_eq_gpsBackloggedWeightSum
    (weight work : Class → ℝ) :
    finiteGPSActiveWeightSum weight work =
      gpsBackloggedWeightSum Class weight (finiteGPSBacklogged work) 0 := by
  simp [finiteGPSActiveWeightSum, gpsBackloggedWeightSum,
    gpsBackloggedClasses, finiteGPSBacklogged, finiteGPSActiveClasses]

/-- A concrete finite GPS class rate is its normalized active-set share, or
zero if the class is inactive. -/
theorem finiteGPSClassRate_eq_activeNormalized
    (capacity : ℝ) (weight work : Class → ℝ) (i : Class) :
    finiteGPSClassRate capacity weight work i =
      if i ∈ finiteGPSActiveClasses work then
        capacity * weight i / finiteGPSActiveWeightSum weight work
      else 0 := by
  by_cases hactive : i ∈ finiteGPSActiveClasses work
  · have hwork_active : 0 < work i :=
      mem_finiteGPSActiveClasses_iff.mp hactive
    rw [finiteGPSClassRate_eq_gpsBackloggedClassRate_of_active hwork_active]
    unfold gpsBackloggedClassRate idealGPSClassRate
    rw [← finiteGPSActiveWeightSum_eq_gpsBackloggedWeightSum]
    simp [hactive]
  · have hwork_inactive : ¬ 0 < work i := by
      intro hwork
      exact hactive (mem_finiteGPSActiveClasses_iff.mpr hwork)
    rw [finiteGPSClassRate_eq_zero_of_not_active hwork_inactive]
    simp [hactive]

/-- Positive finite-class weights make the active GPS denominator positive
whenever the active class set is nonempty. -/
theorem finiteGPSActiveWeightSum_pos_of_active_nonempty
    {weight work : Class → ℝ}
    (hweight_pos : ∀ i, 0 < weight i)
    (hactive : (finiteGPSActiveClasses work).Nonempty) :
    0 < finiteGPSActiveWeightSum weight work := by
  unfold finiteGPSActiveWeightSum
  exact Finset.sum_pos (fun i _ => hweight_pos i) hactive

/-- Normalized GPS is work-conserving at a nonempty finite active snapshot:
the sum of its class rates is exactly the full capacity. -/
theorem finiteGPSAggregateClassRate_eq_capacity_of_active_nonempty
    (capacity : ℝ) {weight work : Class → ℝ}
    (hweight_pos : ∀ i, 0 < weight i)
    (hactive : (finiteGPSActiveClasses work).Nonempty) :
    finiteGPSAggregateClassRate capacity weight work = capacity := by
  let active := finiteGPSActiveClasses work
  let activeWeight := finiteGPSActiveWeightSum weight work
  have hactiveWeight_pos : 0 < activeWeight :=
    finiteGPSActiveWeightSum_pos_of_active_nonempty hweight_pos hactive
  have hrate : ∀ i,
      finiteGPSClassRate capacity weight work i =
        if i ∈ active then capacity * weight i / activeWeight else 0 := by
    intro i
    exact finiteGPSClassRate_eq_activeNormalized capacity weight work i
  calc
    finiteGPSAggregateClassRate capacity weight work =
        Finset.univ.sum (fun i =>
          if i ∈ active then capacity * weight i / activeWeight else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrate i
    _ = active.sum (fun i => capacity * weight i / activeWeight) := by
      rw [← Finset.sum_filter]
      simp
    _ = (active.sum fun i => capacity * weight i) / activeWeight := by
      rw [Finset.sum_div]
    _ = capacity * activeWeight / activeWeight := by
      congr 1
      change active.sum (fun i => capacity * weight i) =
        capacity * active.sum weight
      rw [Finset.mul_sum]
    _ = capacity := by
      simpa [mul_comm] using
        (mul_div_cancel_left₀ capacity (ne_of_gt hactiveWeight_pos))

/-- If no class has positive workload, every finite GPS class rate is zero. -/
theorem finiteGPSClassRate_eq_zero_of_active_empty
    {capacity : ℝ} {weight work : Class → ℝ}
    (hactive_empty : finiteGPSActiveClasses work = ∅) (i : Class) :
    finiteGPSClassRate capacity weight work i = 0 := by
  apply finiteGPSClassRate_eq_zero_of_not_active
  intro hwork_active
  have himem : i ∈ finiteGPSActiveClasses work :=
    mem_finiteGPSActiveClasses_iff.mpr hwork_active
  simpa [hactive_empty] using himem

/-- An empty finite active set receives no aggregate GPS service rate. -/
theorem finiteGPSAggregateClassRate_eq_zero_of_active_empty
    (capacity : ℝ) {weight work : Class → ℝ}
    (hactive_empty : finiteGPSActiveClasses work = ∅) :
    finiteGPSAggregateClassRate capacity weight work = 0 := by
  unfold finiteGPSAggregateClassRate
  apply Finset.sum_eq_zero
  intro i hi
  exact finiteGPSClassRate_eq_zero_of_active_empty hactive_empty i

/-- With nonnegative class workloads, zero total workload leaves no active
GPS class.  This is the finite reset bridge from an aggregate empty epoch to
the all-class queue state. -/
theorem finiteGPSAggregateWork_eq_zero_iff_activeClasses_eq_empty
    {work : Class → ℝ} (hwork_nonneg : ∀ i, 0 ≤ work i) :
    finiteGPSAggregateWork work = 0 ↔ finiteGPSActiveClasses work = ∅ := by
  constructor
  · intro htotal_zero
    apply Finset.eq_empty_of_forall_notMem
    intro i himem
    have hwork_pos : 0 < work i :=
      mem_finiteGPSActiveClasses_iff.mp himem
    have hwork_le_total : work i ≤ finiteGPSAggregateWork work := by
      unfold finiteGPSAggregateWork
      exact Finset.single_le_sum (fun j _ => hwork_nonneg j) (by simp)
    have htotal_pos : 0 < finiteGPSAggregateWork work :=
      lt_of_lt_of_le hwork_pos hwork_le_total
    rw [htotal_zero] at htotal_pos
    exact lt_irrefl 0 htotal_pos
  · intro hactive_empty
    unfold finiteGPSAggregateWork
    apply Finset.sum_eq_zero
    intro i hi
    have hnot_active : ¬ 0 < work i := by
      intro hwork_pos
      have himem : i ∈ finiteGPSActiveClasses work :=
        mem_finiteGPSActiveClasses_iff.mpr hwork_pos
      simpa [hactive_empty] using himem
    exact le_antisymm (le_of_not_gt hnot_active) (hwork_nonneg i)

/-- The active-set reset condition is equivalent to every finite class having
zero workload, under the physical nonnegativity invariant. -/
theorem finiteGPSActiveClasses_eq_empty_iff_all_work_eq_zero
    {work : Class → ℝ} (hwork_nonneg : ∀ i, 0 ≤ work i) :
    finiteGPSActiveClasses work = ∅ ↔ ∀ i, work i = 0 := by
  constructor
  · intro hactive_empty i
    have hnot_active : ¬ 0 < work i := by
      intro hwork_pos
      have himem : i ∈ finiteGPSActiveClasses work :=
        mem_finiteGPSActiveClasses_iff.mpr hwork_pos
      simpa [hactive_empty] using himem
    exact le_antisymm (le_of_not_gt hnot_active) (hwork_nonneg i)
  · intro hwork_zero
    apply Finset.eq_empty_of_forall_notMem
    intro i himem
    have hwork_pos : 0 < work i :=
      mem_finiteGPSActiveClasses_iff.mp himem
    rw [hwork_zero i] at hwork_pos
    exact lt_irrefl 0 hwork_pos

/-- Equivalent aggregate form of the all-class reset condition. -/
theorem finiteGPSAggregateWork_eq_zero_iff_all_work_eq_zero
    {work : Class → ℝ} (hwork_nonneg : ∀ i, 0 ≤ work i) :
    finiteGPSAggregateWork work = 0 ↔ ∀ i, work i = 0 :=
  (finiteGPSAggregateWork_eq_zero_iff_activeClasses_eq_empty hwork_nonneg).trans
    (finiteGPSActiveClasses_eq_empty_iff_all_work_eq_zero hwork_nonneg)

/-- On a nonempty active snapshot, the concrete segment's aggregate stored
service is exactly capacity times its finite event duration. -/
theorem finiteGPSBuildExecutionSegment_aggregateService_eq_capacity_mul_duration_of_active_nonempty
    (capacity : ℝ) {weight work batchWork : Class → ℝ}
    (startTime nextBatchDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hactive : (finiteGPSActiveClasses work).Nonempty) :
    finiteGPSAggregateServiceIncrement
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) =
      capacity *
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).duration := by
  unfold finiteGPSAggregateServiceIncrement
  simp only [finiteGPSBuildExecutionSegment_serviceIncrement]
  have hservice : ∀ i,
      finiteGPSServiceIncrement capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
        finiteGPSClassRate capacity weight work i *
          finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
    intro i
    exact finiteGPSServiceIncrement_eq_rate_mul_nextStep
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
  calc
    ∑ i, finiteGPSServiceIncrement capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
      ∑ i, finiteGPSClassRate capacity weight work i *
        finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hservice i
    _ = finiteGPSAggregateClassRate capacity weight work *
        finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
      unfold finiteGPSAggregateClassRate
      rw [Finset.sum_mul]
    _ = _ := by
      rw [finiteGPSAggregateClassRate_eq_capacity_of_active_nonempty
        capacity hweight_pos hactive]
      rfl

/-- If the segment starts with no active class, its aggregate stored service
increment is zero. -/
theorem finiteGPSBuildExecutionSegment_aggregateService_eq_zero_of_active_empty
    (capacity : ℝ) {weight work batchWork : Class → ℝ}
    (startTime nextBatchDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hactive_empty : finiteGPSActiveClasses work = ∅) :
    finiteGPSAggregateServiceIncrement
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) = 0 := by
  unfold finiteGPSAggregateServiceIncrement
  simp only [finiteGPSBuildExecutionSegment_serviceIncrement]
  apply Finset.sum_eq_zero
  intro i hi
  rw [finiteGPSServiceIncrement_eq_rate_mul_nextStep
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg,
    finiteGPSClassRate_eq_zero_of_active_empty hactive_empty]
  ring

/-- Summing the concrete per-class endpoint balance yields the exact total
work balance before selecting the active/nonactive branch. -/
theorem finiteGPSBuildExecutionSegment_aggregateWork_balance
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (startTime nextBatchDelay : ℝ) :
    finiteGPSAggregateEndpointWork
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) =
      finiteGPSAggregateWork work +
        finiteGPSAggregateEndpointBatchWork
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay) -
        finiteGPSAggregateServiceIncrement
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay) := by
  unfold finiteGPSAggregateEndpointWork finiteGPSAggregateWork
    finiteGPSAggregateEndpointBatchWork finiteGPSAggregateServiceIncrement
  have hbalance : ∀ i,
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).endpointWorkload i =
        work i +
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay).endpointBatch i -
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay).serviceIncrement i := by
    intro i
    exact finiteGPSBuildExecutionSegment_balance capacity weight work batchWork
      startTime nextBatchDelay i
  calc
    ∑ i, (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).endpointWorkload i =
      ∑ i, (work i +
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).endpointBatch i -
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).serviceIncrement i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hbalance i
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Work-conserving total-work balance for a concrete segment whose active
set is nonempty. -/
theorem finiteGPSBuildExecutionSegment_aggregateWork_balance_of_active_nonempty
    (capacity : ℝ) {weight work batchWork : Class → ℝ}
    (startTime nextBatchDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hactive : (finiteGPSActiveClasses work).Nonempty) :
    finiteGPSAggregateEndpointWork
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) =
      finiteGPSAggregateWork work +
        finiteGPSAggregateEndpointBatchWork
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay) -
        capacity *
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay).duration := by
  rw [finiteGPSBuildExecutionSegment_aggregateWork_balance,
    finiteGPSBuildExecutionSegment_aggregateService_eq_capacity_mul_duration_of_active_nonempty
      capacity startTime nextBatchDelay hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hactive]

/-- Idle total-work balance for a concrete segment whose active set is empty:
there is no service term before the endpoint batch is applied. -/
theorem finiteGPSBuildExecutionSegment_aggregateWork_balance_of_active_empty
    (capacity : ℝ) {weight work batchWork : Class → ℝ}
    (startTime nextBatchDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hactive_empty : finiteGPSActiveClasses work = ∅) :
    finiteGPSAggregateEndpointWork
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay) =
      finiteGPSAggregateWork work +
        finiteGPSAggregateEndpointBatchWork
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay) := by
  rw [finiteGPSBuildExecutionSegment_aggregateWork_balance,
    finiteGPSBuildExecutionSegment_aggregateService_eq_zero_of_active_empty
      capacity startTime nextBatchDelay hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hactive_empty]
  ring

end

end AppliedModelingLib.Probability.Queueing
