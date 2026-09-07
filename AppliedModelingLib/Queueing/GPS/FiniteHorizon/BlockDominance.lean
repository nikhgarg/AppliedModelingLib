import AppliedModelingLib.Queueing.GPS.FiniteHorizon.VirtualEndBatchBound
import Mathlib.Tactic

/-!
# Deterministic finite-block GPS dominance

This module packages the existing virtual-end-batch comparison as a scalar
block update.  A block's literal external batches lie in its half-open time
interval; closing the runner at the right endpoint uses a separate
computational zero-work fence.  The scalar update is only an upper bound, not
an alternative execution and not a reset certificate by itself.

There are no stochastic, Palm, stationary, or source-process assertions here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The aggregate work of the literal external batches in one finite block. -/
def finiteGPSLiteralBlockBatchAggregateWork
    (batchWork : Real -> Class -> Real) (times : List Real) : Real :=
  (times.map fun t => finiteGPSAggregateWork (batchWork t)).sum

/--
The scalar late-batch upper update for one finite block.  The batch total is
charged after all block service, so this is a comparison upper bound rather
than the executable GPS trajectory.
-/
def finiteGPSBlockAggregateUpperUpdate
    (capacity start horizon upper literalBatchAggregateWork : Real) : Real :=
  max (upper - capacity * (horizon - start)) 0 + literalBatchAggregateWork

/-- Replacing an initial aggregate workload by a scalar upper bound can only
increase the virtual-end-batch aggregate expression. -/
theorem finiteGPSVirtualEndBatchAggregateBound_le_blockAggregateUpperUpdate
    (capacity start horizon upper : Real) (initialWork : Class -> Real)
    (batchWork : Real -> Class -> Real) (times : List Real)
    (hinitial_le_upper : finiteGPSAggregateWork initialWork <= upper) :
    finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork times <=
      finiteGPSBlockAggregateUpperUpdate capacity start horizon upper
        (finiteGPSLiteralBlockBatchAggregateWork batchWork times) := by
  unfold finiteGPSVirtualEndBatchAggregateBound finiteGPSBlockAggregateUpperUpdate
    finiteGPSLiteralBlockBatchAggregateWork
  apply add_le_add_left
  exact max_le_max_right 0
    (sub_le_sub_right hinitial_le_upper (capacity * (horizon - start)))

/--
For literal external batches in the half-open block `[start, horizon)`, the
actual GPS runner closed by its computational zero-work horizon fence is
dominated by the scalar late-batch upper update.  The strict endpoint premise
keeps the computational fence distinct from every literal batch.
-/
theorem finiteGPSAggregateWork_closeAtHorizon_le_blockAggregateUpperUpdate
    (capacity : Real) (weight initialWork : Class -> Real)
    (batchWork : Real -> Class -> Real) (start horizon upper : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hinitial_nonneg : forall i, 0 <= initialWork i)
    (hinitial_le_upper : finiteGPSAggregateWork initialWork <= upper)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_le_horizon : start <= horizon)
    (htimes_lt_horizon : ∀ t ∈ times, t < horizon)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 <= batchWork t i) :
    finiteGPSAggregateWork
        (finiteGPSCloseAtHorizon capacity weight
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
          horizon).workload <=
      finiteGPSBlockAggregateUpperUpdate capacity start horizon upper
        (finiteGPSLiteralBlockBatchAggregateWork batchWork times) := by
  calc
    finiteGPSAggregateWork
        (finiteGPSCloseAtHorizon capacity weight
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
          horizon).workload <=
        finiteGPSVirtualEndBatchAggregateBound capacity start horizon initialWork batchWork times :=
      finiteGPSAggregateWork_closeAtHorizon_le_virtualEndBatch
        capacity weight initialWork batchWork start horizon times hcapacity hweight_pos
        htotal_weight_le_one hinitial_nonneg hchronological hstart_le_horizon
        (fun t ht => (htimes_lt_horizon t ht).le) hbatch_nonneg
    _ <= finiteGPSBlockAggregateUpperUpdate capacity start horizon upper
          (finiteGPSLiteralBlockBatchAggregateWork batchWork times) :=
      finiteGPSVirtualEndBatchAggregateBound_le_blockAggregateUpperUpdate
        capacity start horizon upper initialWork batchWork times hinitial_le_upper

/--
A zero scalar upper update does certify an actual empty post-fence GPS state.
This uses nonnegativity of the real execution in addition to the dominance
bound; no assertion is made for merely small or negative-looking comparison
expressions.
-/
theorem finiteGPSCloseAtHorizon_workload_eq_zero_of_blockAggregateUpperUpdate_eq_zero
    (capacity : Real) (weight initialWork : Class -> Real)
    (batchWork : Real -> Class -> Real) (start horizon upper : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hinitial_nonneg : forall i, 0 <= initialWork i)
    (hinitial_le_upper : finiteGPSAggregateWork initialWork <= upper)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_le_horizon : start <= horizon)
    (htimes_lt_horizon : ∀ t ∈ times, t < horizon)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 <= batchWork t i)
    (hupper_zero : finiteGPSBlockAggregateUpperUpdate capacity start horizon upper
      (finiteGPSLiteralBlockBatchAggregateWork batchWork times) = 0) :
    forall i,
      (finiteGPSCloseAtHorizon capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
        horizon).workload i = 0 := by
  have hbound := finiteGPSAggregateWork_closeAtHorizon_le_blockAggregateUpperUpdate
    capacity weight initialWork batchWork start horizon upper times hcapacity hweight_pos
    htotal_weight_le_one hinitial_nonneg hinitial_le_upper hchronological hstart_le_horizon
    htimes_lt_horizon hbatch_nonneg
  have hrun_nonneg : forall i, 0 <=
      (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times).workload i :=
    finiteGPSRunBatchTrace_workload_nonneg capacity weight initialWork batchWork start times
      hinitial_nonneg hbatch_nonneg
  have hclosed_nonneg : forall i, 0 <=
      (finiteGPSCloseAtHorizon capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
        horizon).workload i :=
    finiteGPSCloseAtHorizon_workload_nonneg capacity weight
      (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
      horizon hrun_nonneg
  have haggregate_nonneg : 0 <= finiteGPSAggregateWork
      (finiteGPSCloseAtHorizon capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
        horizon).workload :=
    finiteGPSAggregateWork_nonneg hclosed_nonneg
  have haggregate_zero : finiteGPSAggregateWork
      (finiteGPSCloseAtHorizon capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
        horizon).workload = 0 := by
    rw [hupper_zero] at hbound
    exact le_antisymm hbound haggregate_nonneg
  exact (finiteGPSAggregateWork_eq_zero_iff_all_work_eq_zero hclosed_nonneg).mp
    haggregate_zero

/--
Execute two literal half-open finite blocks with a computational zero-work
fence at the shared boundary.  The boundary itself is not included in either
literal batch list.
-/
def finiteGPSRunTwoClosedBlocks
    (capacity : Real) (weight : Class -> Real) (batchWork : Real -> Class -> Real)
    (start middle horizon : Real) (initialWork : Class -> Real)
    (leftTimes rightTimes : List Real) : FiniteGPSBatchTraceResult Class :=
  let leftClosed := finiteGPSCloseAtHorizon capacity weight
    (finiteGPSRunBatchTrace capacity weight batchWork start initialWork leftTimes)
    middle
  finiteGPSCloseAtHorizon capacity weight
    (finiteGPSRunBatchTrace capacity weight batchWork middle leftClosed.workload rightTimes)
    horizon

/--
Sequential finite-block dominance.  The first block is closed at `middle`
before the second begins, so its zero-work fence is an explicit computational
restart boundary and neither literal half-open batch list is changed.
-/
theorem finiteGPSAggregateWork_twoClosedBlocks_le_blockAggregateUpperUpdates
    (capacity : Real) (weight initialWork : Class -> Real)
    (batchWork : Real -> Class -> Real) (start middle horizon upper : Real)
    (leftTimes rightTimes : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hinitial_nonneg : forall i, 0 <= initialWork i)
    (hinitial_le_upper : finiteGPSAggregateWork initialWork <= upper)
    (hleft_chronological : FiniteGPSChronologicalFrom start leftTimes)
    (hstart_le_middle : start <= middle)
    (hleft_lt_middle : ∀ t ∈ leftTimes, t < middle)
    (hright_chronological : FiniteGPSChronologicalFrom middle rightTimes)
    (hmiddle_le_horizon : middle <= horizon)
    (hright_lt_horizon : ∀ t ∈ rightTimes, t < horizon)
    (hleft_batch_nonneg : ∀ t ∈ leftTimes, ∀ i, 0 <= batchWork t i)
    (hright_batch_nonneg : ∀ t ∈ rightTimes, ∀ i, 0 <= batchWork t i) :
    finiteGPSAggregateWork
        (finiteGPSRunTwoClosedBlocks capacity weight batchWork start middle horizon initialWork
          leftTimes rightTimes).workload <=
      finiteGPSBlockAggregateUpperUpdate capacity middle horizon
        (finiteGPSBlockAggregateUpperUpdate capacity start middle upper
          (finiteGPSLiteralBlockBatchAggregateWork batchWork leftTimes))
        (finiteGPSLiteralBlockBatchAggregateWork batchWork rightTimes) := by
  let leftClosed := finiteGPSCloseAtHorizon capacity weight
    (finiteGPSRunBatchTrace capacity weight batchWork start initialWork leftTimes)
    middle
  let leftUpper := finiteGPSBlockAggregateUpperUpdate capacity start middle upper
    (finiteGPSLiteralBlockBatchAggregateWork batchWork leftTimes)
  have hleft_bound : finiteGPSAggregateWork leftClosed.workload <= leftUpper := by
    simpa [leftClosed, leftUpper] using
      (finiteGPSAggregateWork_closeAtHorizon_le_blockAggregateUpperUpdate
        capacity weight initialWork batchWork start middle upper leftTimes hcapacity hweight_pos
        htotal_weight_le_one hinitial_nonneg hinitial_le_upper hleft_chronological
        hstart_le_middle hleft_lt_middle hleft_batch_nonneg)
  have hleft_run_nonneg : forall i, 0 <=
      (finiteGPSRunBatchTrace capacity weight batchWork start initialWork leftTimes).workload i :=
    finiteGPSRunBatchTrace_workload_nonneg capacity weight initialWork batchWork start leftTimes
      hinitial_nonneg hleft_batch_nonneg
  have hleft_closed_nonneg : forall i, 0 <= leftClosed.workload i := by
    simpa [leftClosed] using
      (finiteGPSCloseAtHorizon_workload_nonneg capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork leftTimes)
        middle hleft_run_nonneg)
  have hright_bound :=
    finiteGPSAggregateWork_closeAtHorizon_le_blockAggregateUpperUpdate
      capacity weight leftClosed.workload batchWork middle horizon leftUpper rightTimes
      hcapacity hweight_pos htotal_weight_le_one hleft_closed_nonneg hleft_bound
      hright_chronological hmiddle_le_horizon hright_lt_horizon hright_batch_nonneg
  simpa [finiteGPSRunTwoClosedBlocks, leftClosed, leftUpper] using hright_bound

end

end AppliedModelingLib.Probability.Queueing
