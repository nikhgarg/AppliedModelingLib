import AppliedModelingLib.Queueing.GPS.FiniteHorizon.PreBatchReset
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSResetRestart
import Mathlib.Tactic

/-!
# Actual pre-batch reset bridge for the tagged admitted SLA source trace

The reset time in this module is an actual source epoch in the suffix.  The
prefix remains half-open, so every literal arrival at that epoch is retained
in the suffix.  The only conditional input is that the executable GPS gap's
aggregate pre-batch workload is zero; this module turns that fact into the
drain certificate consumed by the existing exact source-trace split theorem.

There is no assertion that a reset occurs almost surely, no stationary
construction, and no response-time or tail conclusion.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/--
For a literal source batch at `resetTime`, a zero executable aggregate
pre-batch state certifies that the preceding half-open source trace drains by
that same physical epoch.  The endpoint batch is the actual full-ledger batch
at `resetTime`; it is not a synthetic zero batch.
-/
theorem taggedAdmittedFiniteGPSPrefix_aggregate_drain_of_actual_preBatch_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hpreBatch_zero :
      finiteGPSAggregateWork
          (finiteGPSRunGap
            ((finiteGPSActiveClasses
              (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                capacity weight initialWork).workload).card + 1)
            capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork).workload
            (taggedAdmittedBatchAt start horizon target z resetTime)
            (resetTime -
              (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                capacity weight initialWork).currentTime)).workload -
          finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z resetTime) = 0) :
    finiteGPSAggregateWork
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime) := by
  apply finiteGPSAggregate_drain_of_actual_preBatchAggregate_eq_zero
    capacity weight
    (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
      capacity weight initialWork).workload
    (taggedAdmittedBatchAt start horizon target z resetTime)
    (resetTime -
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).currentTime)
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · intro j
    exact taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
      start resetTime target z htarget_good capacity weight initialWork
      hinit_nonneg hsource_work_nonneg j
  · exact sub_nonneg.mpr
      (taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
        start resetTime target z htarget_good capacity weight initialWork hstart_reset)
  · exact hpreBatch_zero

/--
The source-facing reset extraction.  When `resetTime` is a literal suffix
batch and its actual executable pre-batch aggregate is zero, the complete
finite source run factors through the zero state at that same time.  The
literal batch at `resetTime` remains in the suffix, including all simultaneous
source records at that epoch.
-/
theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_closed_prefix_then_source_suffix_of_actual_preBatch_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hreset_is_suffix_batch :
      resetTime ∈ taggedAdmittedBatchTimeTrace resetTime horizon target z)
    (hpreBatch_zero :
      finiteGPSAggregateWork
          (finiteGPSRunGap
            ((finiteGPSActiveClasses
              (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                capacity weight initialWork).workload).card + 1)
            capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork).workload
            (taggedAdmittedBatchAt start horizon target z resetTime)
            (resetTime -
              (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
                capacity weight initialWork).currentTime)).workload -
          finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z resetTime) = 0) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      { workload :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).workload
        currentTime :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).currentTime
        service := fun i =>
          (finiteGPSCloseAtHorizon capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork) resetTime).service i +
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).service i } := by
  apply taggedAdmittedFiniteGPSPreTerminalRun_eq_closed_prefix_then_source_suffix_of_aggregate_drain
    start resetTime horizon target z htarget_good capacity weight initialWork
    hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
    hinit_nonneg hsource_work_nonneg
  · intro hsuffix_empty
    rw [hsuffix_empty] at hreset_is_suffix_batch
    simpa using hreset_is_suffix_batch
  · exact taggedAdmittedFiniteGPSPrefix_aggregate_drain_of_actual_preBatch_reset
      start resetTime horizon target z htarget_good capacity weight initialWork
      hstart_reset hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
      hsource_work_nonneg hpreBatch_zero

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
