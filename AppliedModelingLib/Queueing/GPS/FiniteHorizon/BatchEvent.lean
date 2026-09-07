import AppliedModelingLib.Queueing.GPS.AENormalizedAllocation
import Mathlib.Tactic

/-!
# One-event finite-horizon GPS execution kernel

This module gives an executable deterministic kernel for a finite-class fluid
GPS queue.  It advances a workload state to the earlier of the next external
arrival batch and the next internal class-emptying event.  Simultaneous
cross-class arrivals are represented by the single vector `batchWork`; no
no-ties condition is used.

The module is deliberately one event deep.  A finite-horizon stochastic
executor can fold this kernel over the finite list of admitted-arrival batches
on a nonexplosive primitive path.  It does not claim an infinite execution,
stationarity, or Palm transport.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Classes with strictly positive current workload. -/
def finiteGPSActiveClasses (work : Class → ℝ) : Finset Class :=
  Finset.univ.filter (fun i => 0 < work i)

/-- The time-constant backlog indicator induced by a workload snapshot. -/
def finiteGPSBacklogged (work : Class → ℝ) : ℝ → Class → Bool :=
  fun _ i => decide (0 < work i)

/-- Actual instantaneous service rate of a class at a workload snapshot.
Inactive classes receive zero; active classes receive the existing normalized
GPS rate for the snapshot's active set. -/
def finiteGPSClassRate
    (capacity : ℝ) (weight work : Class → ℝ) (i : Class) : ℝ :=
  if 0 < work i then
    gpsBackloggedClassRate Class i capacity weight (finiteGPSBacklogged work) 0
  else 0

/-- Work remaining after evolving at the snapshot's fixed GPS rates for one
duration.  The next-event duration below prevents an active class from being
clamped before the endpoint. -/
def finiteGPSRemainingAfter
    (capacity : ℝ) (weight work : Class → ℝ) (duration : ℝ) : Class → ℝ :=
  fun i => max 0 (work i - finiteGPSClassRate capacity weight work i * duration)

/-- Service delivered to a class over a finite GPS event step. -/
def finiteGPSServiceIncrement
    (capacity : ℝ) (weight work : Class → ℝ) (duration : ℝ) : Class → ℝ :=
  fun i => work i - finiteGPSRemainingAfter capacity weight work duration i

/-- The time at which a currently active class would empty if the active
snapshot did not change. -/
def finiteGPSClassEmptyDelay
    (capacity : ℝ) (weight work : Class → ℝ) (i : Class) : ℝ :=
  work i / finiteGPSClassRate capacity weight work i

/-- Earliest internally generated class-emptying time measured from the start
of the step.  It is zero only when the snapshot has no active class. -/
def finiteGPSEarliestEmptyDelay
    (capacity : ℝ) (weight work : Class → ℝ) : ℝ :=
  if hactive : (finiteGPSActiveClasses work).Nonempty then
    (finiteGPSActiveClasses work).inf' hactive
      (finiteGPSClassEmptyDelay capacity weight work)
  else 0

/-- Duration to the next event: either the next arrival batch or the first
class completion.  This is a concrete finite minimum, not a caller-supplied
transition certificate. -/
def finiteGPSNextStepDuration
    (capacity : ℝ) (weight work : Class → ℝ) (nextBatchDelay : ℝ) : ℝ :=
  if (finiteGPSActiveClasses work).Nonempty then
    min nextBatchDelay (finiteGPSEarliestEmptyDelay capacity weight work)
  else nextBatchDelay

/-- The arrival batch is applied exactly when the next event reaches the
external batch time, including an arrival/departure tie. -/
def finiteGPSBatchApplied
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) : Class → ℝ :=
  if finiteGPSNextStepDuration capacity weight work nextBatchDelay = nextBatchDelay
  then batchWork
  else fun _ => 0

/-- Concrete workload update at the next finite GPS event. -/
def finiteGPSNextEventState
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) : Class → ℝ :=
  fun i =>
    finiteGPSRemainingAfter capacity weight work
      (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i +
    finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i

/-- Active-class membership is the semantic positivity test on the workload
snapshot. -/
theorem mem_finiteGPSActiveClasses_iff
    {work : Class → ℝ} {i : Class} :
    i ∈ finiteGPSActiveClasses work ↔ 0 < work i := by
  simp [finiteGPSActiveClasses]

/-- A snapshot's Boolean backlog indicator agrees with its active classes. -/
theorem finiteGPSBacklogged_eq_true_iff
    {work : Class → ℝ} {i : Class} {t : ℝ} :
    finiteGPSBacklogged work t i = true ↔ 0 < work i := by
  simp [finiteGPSBacklogged]

/-- Inactive classes have zero actual GPS service rate. -/
theorem finiteGPSClassRate_eq_zero_of_not_active
    {capacity : ℝ} {weight work : Class → ℝ} {i : Class}
    (hinactive : ¬ 0 < work i) :
    finiteGPSClassRate capacity weight work i = 0 := by
  simp [finiteGPSClassRate, hinactive]

/-- An active class has the existing backlog-induced normalized GPS rate. -/
theorem finiteGPSClassRate_eq_gpsBackloggedClassRate_of_active
    {capacity : ℝ} {weight work : Class → ℝ} {i : Class}
    (hactive : 0 < work i) :
    finiteGPSClassRate capacity weight work i =
      gpsBackloggedClassRate Class i capacity weight
        (finiteGPSBacklogged work) 0 := by
  simp [finiteGPSClassRate, hactive]

/-- Under positive capacity and weights, every active class receives a
strictly positive GPS rate. -/
theorem finiteGPSClassRate_pos_of_active
    {capacity : ℝ} {weight work : Class → ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hactive : 0 < work i) :
    0 < finiteGPSClassRate capacity weight work i := by
  rw [finiteGPSClassRate_eq_gpsBackloggedClassRate_of_active hactive]
  have hguaranteed : 0 < capacity * weight i :=
    mul_pos hcapacity (hweight_pos i)
  exact lt_of_lt_of_le hguaranteed
    (gpsBackloggedClassRate_ge_guaranteed_of_tag_backlogged
      (tag := i) hcapacity.le (fun j => (hweight_pos j).le)
      htotal_weight_le_one hguaranteed
      ((finiteGPSBacklogged_eq_true_iff).mpr hactive))

/-- A next-event duration is no later than the snapshot emptying time of each
currently active class. -/
theorem finiteGPSNextStepDuration_le_emptyDelay
    {capacity nextBatchDelay : ℝ} {weight work : Class → ℝ} {i : Class}
    (hactive : i ∈ finiteGPSActiveClasses work) :
    finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤
      finiteGPSClassEmptyDelay capacity weight work i := by
  unfold finiteGPSNextStepDuration
  rw [if_pos ⟨i, hactive⟩, finiteGPSEarliestEmptyDelay,
    dif_pos ⟨i, hactive⟩]
  exact (min_le_right _ _).trans
    (Finset.inf'_le (finiteGPSClassEmptyDelay capacity weight work) hactive)

/-- The earliest emptying time is nonnegative on a nonnegative workload
snapshot with positive capacity and weights. -/
theorem finiteGPSEarliestEmptyDelay_nonneg
    {capacity : ℝ} {weight work : Class → ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    0 ≤ finiteGPSEarliestEmptyDelay capacity weight work := by
  unfold finiteGPSEarliestEmptyDelay
  split
  · apply Finset.le_inf'
    intro j hj
    exact div_nonneg (hwork_nonneg j)
      (finiteGPSClassRate_pos_of_active hcapacity hweight_pos
        htotal_weight_le_one (mem_finiteGPSActiveClasses_iff.mp hj)).le
  · rfl

/-- A nonnegative external-batch delay gives a nonnegative next-event
duration. -/
theorem finiteGPSNextStepDuration_nonneg
    {capacity nextBatchDelay : ℝ} {weight work : Class → ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay : 0 ≤ nextBatchDelay) :
    0 ≤ finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  unfold finiteGPSNextStepDuration
  split
  · exact le_min hnextBatchDelay
      (finiteGPSEarliestEmptyDelay_nonneg hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg)
  · exact hnextBatchDelay

/-- At the selected next-event time, clamping does not change the linear GPS
evolution: every active class is stopped at or before its own emptying time,
and every inactive nonnegative class has zero work and zero rate. -/
theorem finiteGPSRemainingAfter_eq_linear_nextStep
    {capacity nextBatchDelay : ℝ} {weight work : Class → ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    finiteGPSRemainingAfter capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
      work i - finiteGPSClassRate capacity weight work i *
        finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  by_cases hactive : 0 < work i
  · have hrate : 0 < finiteGPSClassRate capacity weight work i :=
      finiteGPSClassRate_pos_of_active hcapacity hweight_pos
        htotal_weight_le_one hactive
    have hduration : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤
        finiteGPSClassEmptyDelay capacity weight work i :=
      finiteGPSNextStepDuration_le_emptyDelay
        (mem_finiteGPSActiveClasses_iff.mpr hactive)
    have hservice_le_work :
        finiteGPSClassRate capacity weight work i *
          finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤ work i := by
      rw [mul_comm]
      exact (le_div_iff₀ hrate).mp hduration
    unfold finiteGPSRemainingAfter
    exact max_eq_right (sub_nonneg.mpr hservice_le_work)
  · have hwork_zero : work i = 0 :=
      le_antisymm (le_of_not_gt hactive) (hwork_nonneg i)
    have hrate_zero : finiteGPSClassRate capacity weight work i = 0 :=
      finiteGPSClassRate_eq_zero_of_not_active hactive
    unfold finiteGPSRemainingAfter
    rw [hrate_zero]
    simp [hwork_zero]

/-- The service increment of a valid next event is exactly rate times event
duration. -/
theorem finiteGPSServiceIncrement_eq_rate_mul_nextStep
    {capacity nextBatchDelay : ℝ} {weight work : Class → ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    finiteGPSServiceIncrement capacity weight work
        (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
      finiteGPSClassRate capacity weight work i *
        finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  unfold finiteGPSServiceIncrement
  rw [finiteGPSRemainingAfter_eq_linear_nextStep hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg]
  ring

/-- The next-event state satisfies the exact workload balance for the actual
batch work applied at that event.  This identity holds by construction and
does not replace arrival work with a drain-only convention. -/
theorem finiteGPSNextEventState_balance
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) (i : Class) :
    finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i =
      work i +
        finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i -
        finiteGPSServiceIncrement capacity weight work
          (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i := by
  simp only [finiteGPSNextEventState, finiteGPSServiceIncrement]
  ring

/-- The concrete next event has a linear GPS workload balance with the actual
external batch work.  This is the form used to compose finite event steps. -/
theorem finiteGPSNextEventState_linear_balance
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i =
      work i +
        finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i -
        finiteGPSClassRate capacity weight work i *
          finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
  rw [finiteGPSNextEventState_balance]
  rw [finiteGPSServiceIncrement_eq_rate_mul_nextStep hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg]

/-- Applying a nonnegative simultaneous arrival batch preserves nonnegative
workload at the concrete next event. -/
theorem finiteGPSNextEventState_nonneg
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {i : Class} (hbatch_nonneg : ∀ j, 0 ≤ batchWork j) :
    0 ≤ finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i := by
  unfold finiteGPSNextEventState finiteGPSBatchApplied
  split
  · exact add_nonneg (le_max_left _ _) (hbatch_nonneg i)
  · exact add_nonneg (le_max_left _ _) (by simp)

end

end AppliedModelingLib.Probability.Queueing
