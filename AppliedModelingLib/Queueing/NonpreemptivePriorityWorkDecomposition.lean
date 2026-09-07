import AppliedModelingLib.Queueing.NonpreemptivePriorityMeanBalance

/-!
# Mean-work decomposition for finite nonpreemptive-priority queues

This module separates the probabilistic queueing step from the algebra that
identifies its mean waiting times.  A stationary Palm construction establishes
the displayed mean-work decomposition: an arriving job waits for residual
service work, work already queued at least as high as its own priority, and
new higher-priority work arriving while it waits.  The theorems below turn
those physical identities into the standard finite priority mean-wait balance.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-- The mean-work decomposition for a finite nonpreemptive-priority queue.
For class `i`, the final term is the work of strictly higher-priority arrivals
that overtake the tagged job during its wait.  The middle sum is the work of
customers already waiting in classes at least as urgent as the tag. -/
def finiteNonpreemptivePriorityMeanWorkDecomposition
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ)
    (meanResidualWork : ℝ) : Prop :=
  ∀ i,
    meanWait i =
      meanResidualWork +
        (∑ j, if j ≤ i then meanService j * arrivalRate j * meanWait j else 0) +
        finitePriorityStrictLoad meanService arrivalRate i * meanWait i

/-- With the residual-work quantity fixed, the physical mean-work
decomposition and the standard finite priority mean-wait balance are
equivalent rearrangements of the same conservation law. -/
theorem finiteNonpreemptivePriorityMeanWaitBalance_iff_workDecomposition
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ)
    (meanResidualWork : ℝ)
    (hresidual : meanResidualWork =
      finitePriorityResidualWork arrivalRate meanService) :
    finiteNonpreemptivePriorityMeanWaitBalance arrivalRate meanService meanWait ↔
      finiteNonpreemptivePriorityMeanWorkDecomposition
        arrivalRate meanService meanWait meanResidualWork := by
  constructor
  · intro h i
    have hi := h i
    rw [finitePriorityStrictSlack] at hi
    rw [hresidual]
    linarith
  · intro h i
    rw [finitePriorityStrictSlack]
    have hi := h i
    rw [hresidual] at hi
    linarith

/-- A stationary mean-work decomposition whose residual-service contribution
is the exponential-service residual-work numerator satisfies the finite
nonpreemptive-priority mean-wait balance. -/
theorem finiteNonpreemptivePriorityMeanWorkDecomposition.meanWaitBalance
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ)
    (meanResidualWork : ℝ)
    (hresidual : meanResidualWork =
      finitePriorityResidualWork arrivalRate meanService)
    (hdecomposition : finiteNonpreemptivePriorityMeanWorkDecomposition
      arrivalRate meanService meanWait meanResidualWork) :
    finiteNonpreemptivePriorityMeanWaitBalance arrivalRate meanService meanWait := by
  exact (finiteNonpreemptivePriorityMeanWaitBalance_iff_workDecomposition
    arrivalRate meanService meanWait meanResidualWork hresidual).mpr hdecomposition

/-- The closed-form finite priority queue-wait vector obeys the physical
mean-work decomposition whenever its strict and inclusive priority slacks are
nonzero. -/
theorem finiteNonpreemptivePriorityQueueWait_satisfiesMeanWorkDecomposition
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hstrict : ∀ i, finitePriorityStrictSlack meanService arrivalRate i ≠ 0)
    (hinclusive : ∀ i, finitePriorityInclusiveSlack meanService arrivalRate i ≠ 0) :
    finiteNonpreemptivePriorityMeanWorkDecomposition arrivalRate meanService
      (finiteNonpreemptivePriorityQueueWait arrivalRate meanService)
      (finitePriorityResidualWork arrivalRate meanService) := by
  apply (finiteNonpreemptivePriorityMeanWaitBalance_iff_workDecomposition
    arrivalRate meanService (finiteNonpreemptivePriorityQueueWait arrivalRate meanService)
    (finitePriorityResidualWork arrivalRate meanService) rfl).mp
  exact finiteNonpreemptivePriorityQueueWait_satisfiesMeanWaitBalance
    arrivalRate meanService hstrict hinclusive

/-- Once a stationary Palm/workload construction proves the mean-work
decomposition, the finite nonpreemptive-priority queue-wait expression is its
unique mean-wait vector under nonzero priority slacks. -/
theorem finiteNonpreemptivePriorityMeanWait_eq_queueWait_of_workDecomposition
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ)
    (meanResidualWork : ℝ)
    (hstrict : ∀ i, finitePriorityStrictSlack meanService arrivalRate i ≠ 0)
    (hinclusive : ∀ i, finitePriorityInclusiveSlack meanService arrivalRate i ≠ 0)
    (hresidual : meanResidualWork =
      finitePriorityResidualWork arrivalRate meanService)
    (hdecomposition : finiteNonpreemptivePriorityMeanWorkDecomposition
      arrivalRate meanService meanWait meanResidualWork)
    (i : Fin n) :
    meanWait i = finiteNonpreemptivePriorityQueueWait arrivalRate meanService i := by
  apply finiteNonpreemptivePriorityMeanWaitBalance_eq_queueWait
    arrivalRate meanService meanWait hstrict hinclusive
  exact hdecomposition.meanWaitBalance arrivalRate meanService meanWait
    meanResidualWork hresidual

end Queueing
end AppliedModelingLib
