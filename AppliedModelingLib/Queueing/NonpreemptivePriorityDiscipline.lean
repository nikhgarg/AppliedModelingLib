import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import Lean.Elab.Tactic.Omega

/-!
# Finite nonpreemptive-priority service discipline

This module gives the deterministic service-selection part of a finite
nonpreemptive priority queue.  A lower `Fin` index is a higher priority.  The
selector is deliberately separated from arrival and service-time processes:
it is the reusable rule that an event-driven or stationary construction must
implement at each service completion.
-/

namespace AppliedModelingLib
namespace Queueing

/-- The priority classes whose waiting-job count is positive. -/
def nonemptyPriorityClasses
    {n : ℕ} (backlog : Fin n → ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < backlog i

/-- The number of jobs waiting across all finite priority classes. -/
def totalPriorityBacklog
    {n : ℕ} (backlog : Fin n → ℕ) : ℕ :=
  ∑ i, backlog i

/-- The deterministic backlog update for one arrival to a declared priority
class. -/
def addPriorityArrival
    {n : ℕ} (backlog : Fin n → ℕ) (i : Fin n) : Fin n → ℕ :=
  Function.update backlog i (backlog i + 1)

/-- An arrival increments its declared class's backlog by one. -/
theorem addPriorityArrival_selected
    {n : ℕ} (backlog : Fin n → ℕ) (i : Fin n) :
    addPriorityArrival backlog i i = backlog i + 1 := by
  simp [addPriorityArrival]

/-- An arrival leaves every other priority-class backlog unchanged. -/
theorem addPriorityArrival_of_ne
    {n : ℕ} (backlog : Fin n → ℕ) (i j : Fin n) (hji : j ≠ i) :
    addPriorityArrival backlog i j = backlog j := by
  simp [addPriorityArrival, hji]

/-- One arrival increases the aggregate finite backlog by one. -/
theorem totalPriorityBacklog_addPriorityArrival
    {n : ℕ} (backlog : Fin n → ℕ) (i : Fin n) :
    totalPriorityBacklog (addPriorityArrival backlog i) =
      totalPriorityBacklog backlog + 1 := by
  classical
  unfold totalPriorityBacklog addPriorityArrival
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _ backlog (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  omega

/-- When a finite priority queue is nonempty, select the highest-priority
class with waiting work. -/
noncomputable def nextNonpreemptivePriority
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i) : Fin n :=
  (nonemptyPriorityClasses backlog).min' (by
    rcases hnonempty with ⟨i, hi⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩)

/-- Membership in the available-class set is exactly positivity of the
corresponding waiting-job count. -/
theorem mem_nonemptyPriorityClasses_iff
    {n : ℕ} (backlog : Fin n → ℕ) (i : Fin n) :
    i ∈ nonemptyPriorityClasses backlog ↔ 0 < backlog i := by
  simp [nonemptyPriorityClasses]

/-- The selected priority has waiting work. -/
theorem nextNonpreemptivePriority_positive
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i) :
    0 < backlog (nextNonpreemptivePriority backlog hnonempty) := by
  apply (mem_nonemptyPriorityClasses_iff backlog _).mp
  exact Finset.min'_mem _ _

/-- The selected class is no lower priority than every nonempty class. -/
theorem nextNonpreemptivePriority_le_of_positive
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i)
    (i : Fin n) (hi : 0 < backlog i) :
    nextNonpreemptivePriority backlog hnonempty ≤ i := by
  apply Finset.min'_le
  exact (mem_nonemptyPriorityClasses_iff backlog _).mpr hi

/-- If a class has work and every higher-priority class is empty, the service
selector chooses that class. -/
theorem nextNonpreemptivePriority_eq_of_no_higher_work
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i)
    (i : Fin n) (hi : 0 < backlog i)
    (hnoHigher : ∀ j : Fin n, j < i → backlog j = 0) :
    nextNonpreemptivePriority backlog hnonempty = i := by
  have hle := nextNonpreemptivePriority_le_of_positive backlog hnonempty i hi
  apply le_antisymm hle
  by_contra hnot
  have hne : nextNonpreemptivePriority backlog hnonempty ≠ i := by
    intro heq
    apply hnot
    simpa [heq]
  have hlt : nextNonpreemptivePriority backlog hnonempty < i :=
    lt_of_le_of_ne hle hne
  have hzero := hnoHigher (nextNonpreemptivePriority backlog hnonempty) hlt
  have hpositive := nextNonpreemptivePriority_positive backlog hnonempty
  omega

/-- The state after one service completion, conditional on a nonempty queue.
Only the selected class loses one waiting job. -/
noncomputable def completeNonpreemptivePriorityService
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i) : Fin n → ℕ :=
  Function.update backlog (nextNonpreemptivePriority backlog hnonempty)
    (backlog (nextNonpreemptivePriority backlog hnonempty) - 1)

/-- A service completion decrements the selected positive class by one. -/
theorem completeNonpreemptivePriorityService_selected
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i) :
    completeNonpreemptivePriorityService backlog hnonempty
      (nextNonpreemptivePriority backlog hnonempty) =
      backlog (nextNonpreemptivePriority backlog hnonempty) - 1 := by
  simp [completeNonpreemptivePriorityService]

/-- A service completion leaves every nonselected class unchanged. -/
theorem completeNonpreemptivePriorityService_of_ne
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i)
    (i : Fin n) (hi : i ≠ nextNonpreemptivePriority backlog hnonempty) :
    completeNonpreemptivePriorityService backlog hnonempty i = backlog i := by
  simp [completeNonpreemptivePriorityService, hi]

/-- One service completion decreases the aggregate backlog by one. -/
theorem totalPriorityBacklog_completeNonpreemptivePriorityService
    {n : ℕ} (backlog : Fin n → ℕ) (hnonempty : ∃ i, 0 < backlog i) :
    totalPriorityBacklog (completeNonpreemptivePriorityService backlog hnonempty) + 1 =
      totalPriorityBacklog backlog := by
  have hpositive : 0 < backlog (nextNonpreemptivePriority backlog hnonempty) :=
    nextNonpreemptivePriority_positive backlog hnonempty
  classical
  unfold totalPriorityBacklog completeNonpreemptivePriorityService
  rw [Finset.sum_update_of_mem (Finset.mem_univ
    (nextNonpreemptivePriority backlog hnonempty))]
  rw [← Finset.sum_erase_add _ backlog (Finset.mem_univ
    (nextNonpreemptivePriority backlog hnonempty))]
  rw [Finset.sdiff_singleton_eq_erase]
  omega

end Queueing
end AppliedModelingLib
