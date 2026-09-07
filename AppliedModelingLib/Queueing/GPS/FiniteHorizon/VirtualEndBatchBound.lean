import AppliedModelingLib.Queueing.GPS.FiniteHorizon.AggregateRecursion
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

/-!
# Virtual-end-batch aggregate bounds for finite GPS traces

This module bounds the aggregate workload of the executable finite GPS batch
runner after its explicit computational zero-work horizon fence.  The bound
charges every literal source batch in the supplied trace, but moves those
batches virtually to the terminal horizon.  The horizon fence is not included
in that source sum: it is an execution artifact with a zero endpoint batch.

The results are deterministic finite-trace facts only.  They do not construct
a stochastic input, a stationary queue, a Palm state, or a response-time tail.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The aggregate workload obtained by serving only the initial work through
the whole interval and then charging every literal source batch at the terminal
endpoint.  This is a comparison quantity, not an alternative GPS execution. -/
def finiteGPSVirtualEndBatchAggregateBound
    (capacity start horizon : ℝ) (initialWork : Class → ℝ)
    (batchWork : ℝ → Class → ℝ) (times : List ℝ) : ℝ :=
  max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
    (times.map fun t => finiteGPSAggregateWork (batchWork t)).sum

/-- Delaying a nonnegative addend until the end of a scalar service interval
can only increase the reflected workload upper bound. -/
private theorem max_sub_nonneg_add_le_virtual_end
    (x priorService laterService batch : ℝ)
    (hlaterService : 0 ≤ laterService) (hbatch : 0 ≤ batch) :
    max (max (x - priorService) 0 + batch - laterService) 0 ≤
      max (x - (priorService + laterService)) 0 + batch := by
  have hsub : max (x - priorService) 0 - laterService ≤
      max (x - priorService - laterService) 0 := by
    by_cases hx : 0 ≤ x - priorService
    · rw [max_eq_left hx]
      exact le_max_left _ _
    · have hx' : x - priorService ≤ 0 := le_of_not_ge hx
      rw [max_eq_right hx']
      exact le_trans (sub_nonpos.mpr hlaterService) (le_max_right _ _)
  have hmain : max (x - priorService) 0 + batch - laterService ≤
      max (x - (priorService + laterService)) 0 + batch := by
    calc
      max (x - priorService) 0 + batch - laterService =
          (max (x - priorService) 0 - laterService) + batch := by ring
      _ ≤ max (x - priorService - laterService) 0 + batch := by
        linarith
      _ = max (x - (priorService + laterService)) 0 + batch := by
        congr 2
        all_goals ring
  apply max_le hmain
  exact add_nonneg (le_max_right _ _) hbatch

/--
For a chronological finite list of literal external source batches, the
aggregate workload after the actual runner's explicit zero-work terminal fence
is at most the virtual-end-batch aggregate bound.  The terminal fence is used
only through `finiteGPSCloseAtHorizon`; it contributes no term to the source
batch sum.
-/
theorem finiteGPSAggregateWork_closeAtHorizon_le_virtualEndBatch
    (capacity : ℝ) (weight initialWork : Class → ℝ)
    (batchWork : ℝ → Class → ℝ) (start horizon : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ i, 0 ≤ initialWork i)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_le_horizon : start ≤ horizon)
    (htimes_le_horizon : ∀ t ∈ times, t ≤ horizon)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i) :
    finiteGPSAggregateWork
        (finiteGPSCloseAtHorizon capacity weight
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
          horizon).workload ≤
      finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork times := by
  induction times generalizing start initialWork with
  | nil =>
      have hdelay_nonneg : 0 ≤ horizon - start := sub_nonneg.mpr hstart_le_horizon
      have hgap := finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
        capacity (weight := weight) (work := initialWork) (batchWork := fun _ => 0)
        (horizon - start) hcapacity hweight_pos htotal_weight_le_one hinitial_nonneg
        hdelay_nonneg
      change finiteGPSAggregateWork
          (finiteGPSRunGap ((finiteGPSActiveClasses initialWork).card + 1)
            capacity weight initialWork (fun _ => 0) (horizon - start)).workload ≤
          finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork []
      rw [hgap]
      simp only [finiteGPSVirtualEndBatchAggregateBound, List.map_nil, List.sum_nil, add_zero]
      simp [finiteGPSAggregateWork]
  | cons t times ih =>
      rcases hchronological with ⟨hstart_le_t, htail_chronological⟩
      have ht_le_horizon : t ≤ horizon := htimes_le_horizon t (by simp)
      have htail_times_le_horizon : ∀ u ∈ times, u ≤ horizon := by
        intro u hu
        exact htimes_le_horizon u (by simp [hu])
      have hbatch_head_nonneg : ∀ i, 0 ≤ batchWork t i := by
        intro i
        exact hbatch_nonneg t (by simp) i
      have hbatch_tail_nonneg : ∀ u ∈ times, ∀ i, 0 ≤ batchWork u i := by
        intro u hu i
        exact hbatch_nonneg u (by simp [hu]) i
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses initialWork).card + 1)
        capacity weight initialWork (batchWork t) (t - start)
      have hgap_terminates : gap.batchApplied = true ∧ gap.remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses initialWork).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hinitial_nonneg (sub_nonneg.mpr hstart_le_t)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ i, 0 ≤ gap.workload i := by
        intro i
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses initialWork).card + 1) capacity weight initialWork
          (batchWork t) (t - start) hinitial_nonneg hbatch_head_nonneg i
      have hgap_aggregate : finiteGPSAggregateWork gap.workload =
          max (finiteGPSAggregateWork initialWork - capacity * (t - start)) 0 +
            finiteGPSAggregateWork (batchWork t) := by
        simpa [gap] using
          (finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
            capacity (weight := weight) (work := initialWork) (batchWork := batchWork t)
            (t - start) hcapacity hweight_pos htotal_weight_le_one hinitial_nonneg
            (sub_nonneg.mpr hstart_le_t))
      have htail := ih (start := t) (initialWork := gap.workload)
        (hinitial_nonneg := hgap_nonneg) (hchronological := htail_chronological)
        (hstart_le_horizon := ht_le_horizon)
        (htimes_le_horizon := htail_times_le_horizon)
        (hbatch_nonneg := hbatch_tail_nonneg)
      have hlater_service_nonneg : 0 ≤ capacity * (horizon - t) := by
        exact mul_nonneg hcapacity.le (sub_nonneg.mpr ht_le_horizon)
      have hhead_aggregate_nonneg : 0 ≤ finiteGPSAggregateWork (batchWork t) :=
        finiteGPSAggregateWork_nonneg hbatch_head_nonneg
      have hscalar := max_sub_nonneg_add_le_virtual_end
        (finiteGPSAggregateWork initialWork)
        (capacity * (t - start)) (capacity * (horizon - t))
        (finiteGPSAggregateWork (batchWork t)) hlater_service_nonneg hhead_aggregate_nonneg
      have hscalar' :
          max (finiteGPSAggregateWork gap.workload - capacity * (horizon - t)) 0 ≤
            max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
              finiteGPSAggregateWork (batchWork t) := by
        calc
          max (finiteGPSAggregateWork gap.workload - capacity * (horizon - t)) 0 =
              max (max (finiteGPSAggregateWork initialWork - capacity * (t - start)) 0 +
                finiteGPSAggregateWork (batchWork t) - capacity * (horizon - t)) 0 := by
                rw [hgap_aggregate]
          _ ≤ max (finiteGPSAggregateWork initialWork -
                (capacity * (t - start) + capacity * (horizon - t))) 0 +
                finiteGPSAggregateWork (batchWork t) := hscalar
          _ = max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
                finiteGPSAggregateWork (batchWork t) := by
                congr 2
                ring
      have hbatch_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses initialWork).card + 1)
            capacity weight initialWork (batchWork t) (t - start)).batchApplied = true := by
        simpa [gap] using hgap_terminates.1
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        start initialWork t times hbatch_applied]
      change finiteGPSAggregateWork
          (finiteGPSCloseAtHorizon capacity weight
            (finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times)
            horizon).workload ≤
          finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork
            (t :: times)
      rw [show finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork
          (t :: times) =
          max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
            (finiteGPSAggregateWork (batchWork t) +
              (times.map fun u => finiteGPSAggregateWork (batchWork u)).sum) by
            simp [finiteGPSVirtualEndBatchAggregateBound]]
      have htail' : finiteGPSAggregateWork
          (finiteGPSCloseAtHorizon capacity weight
            (finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times)
            horizon).workload ≤
          max (finiteGPSAggregateWork gap.workload - capacity * (horizon - t)) 0 +
            (times.map fun u => finiteGPSAggregateWork (batchWork u)).sum := by
        simpa [finiteGPSVirtualEndBatchAggregateBound] using htail
      calc
        finiteGPSAggregateWork
            (finiteGPSCloseAtHorizon capacity weight
              (finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times)
              horizon).workload ≤
            max (finiteGPSAggregateWork gap.workload - capacity * (horizon - t)) 0 +
              (times.map fun u => finiteGPSAggregateWork (batchWork u)).sum := htail'
        _ ≤ (max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
              finiteGPSAggregateWork (batchWork t)) +
              (times.map fun u => finiteGPSAggregateWork (batchWork u)).sum := by
              linarith
        _ = max (finiteGPSAggregateWork initialWork - capacity * (horizon - start)) 0 +
              (finiteGPSAggregateWork (batchWork t) +
                (times.map fun u => finiteGPSAggregateWork (batchWork u)).sum) := by ring

/-- The paper-facing distinct-time trace wrapper inherits the literal-source
virtual-end-batch bound. -/
theorem finiteGPSAggregateWork_closeExternalBatchTraceAtHorizon_le_virtualEndBatch
    (capacity : ℝ) (weight initialWork : Class → ℝ)
    (batchWork : ℝ → Class → ℝ) (start horizon : ℝ)
    (trace : FiniteGPSExternalBatchTrace start)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinitial_nonneg : ∀ i, 0 ≤ initialWork i)
    (hstart_le_horizon : start ≤ horizon)
    (htimes_le_horizon : ∀ t ∈ trace.times, t ≤ horizon)
    (hbatch_nonneg : ∀ t ∈ trace.times, ∀ i, 0 ≤ batchWork t i) :
    finiteGPSAggregateWork
        (finiteGPSCloseAtHorizon capacity weight
          (finiteGPSRunExternalBatchTrace capacity weight batchWork start initialWork trace)
          horizon).workload ≤
      finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork
        trace.times := by
  exact finiteGPSAggregateWork_closeAtHorizon_le_virtualEndBatch
    capacity weight initialWork batchWork start horizon trace.times hcapacity hweight_pos
    htotal_weight_le_one hinitial_nonneg trace.chronological hstart_le_horizon
    htimes_le_horizon hbatch_nonneg

end

end AppliedModelingLib.Probability.Queueing
