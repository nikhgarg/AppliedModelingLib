import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Queueing.NonpreemptivePriorityDynamics

/-!
# Uniformized finite nonpreemptive-priority events

This module packages arrival and potential-completion events into a finite
PMF.  Together with `NonpreemptivePriorityDynamics`, it is the embedded-chain
carrier for a later stationary multiclass M/M/1 construction.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-- A uniformized priority-queue event is either one arrival, labelled by its
class, or one potential service completion. -/
abbrev NonpreemptivePriorityEvent (n : ℕ) := Option (Fin n)

/-- The unnormalized rate weight of an arrival or potential completion event. -/
def nonpreemptivePriorityEventWeight
    {n : ℕ} (arrivalRate : Fin n → ℝ) (serviceRate : ℝ) :
    NonpreemptivePriorityEvent n → ℝ
  | none => serviceRate
  | some i => arrivalRate i

/-- The finite event weights add to the total uniformization rate. -/
theorem sum_nonpreemptivePriorityEventWeight
    {n : ℕ} (arrivalRate : Fin n → ℝ) (serviceRate : ℝ) :
    ∑ event : NonpreemptivePriorityEvent n,
      nonpreemptivePriorityEventWeight arrivalRate serviceRate event =
      serviceRate + ∑ i, arrivalRate i := by
  simp [nonpreemptivePriorityEventWeight]

/-- The finite PMF of one uniformized arrival-or-completion event. -/
noncomputable def nonpreemptivePriorityEventPMF
    {n : ℕ} (arrivalRate : Fin n → ℝ) (serviceRate : ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i) (hserviceRate : 0 < serviceRate) :
    PMF (NonpreemptivePriorityEvent n) :=
  finiteWeightedPMF
    (nonpreemptivePriorityEventWeight arrivalRate serviceRate)
    (by
      intro event
      cases event with
      | none => exact hserviceRate.le
      | some i => exact harrivalRate i)
    (by
      rw [sum_nonpreemptivePriorityEventWeight]
      exact lt_of_lt_of_le hserviceRate
        (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => harrivalRate i)))

/-- Apply one uniformized event to a finite nonpreemptive-priority state. -/
noncomputable def stepNonpreemptivePriority
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (event : NonpreemptivePriorityEvent n) : NonpreemptivePriorityState n :=
  match event with
  | none => completeNonpreemptivePriority state
  | some i => arriveNonpreemptivePriority state i

/-- The embedded discrete-time transition kernel of a homogeneous-rate finite
nonpreemptive-priority M/M/1 queue.  A later continuous-time construction
supplies the independent Poisson uniformization clock. -/
noncomputable def nonpreemptivePriorityUniformizedKernel
    {n : ℕ} (arrivalRate : Fin n → ℝ) (serviceRate : ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i) (hserviceRate : 0 < serviceRate) :
    NonpreemptivePriorityState n → PMF (NonpreemptivePriorityState n) :=
  fun state =>
    (nonpreemptivePriorityEventPMF arrivalRate serviceRate harrivalRate hserviceRate).map
      (stepNonpreemptivePriority state)

/-- A uniformized arrival always raises the total queue population by one. -/
theorem totalNonpreemptivePriorityJobs_step_arrival
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    totalNonpreemptivePriorityJobs
        (stepNonpreemptivePriority state (some i)) =
      totalNonpreemptivePriorityJobs state + 1 := by
  exact totalNonpreemptivePriorityJobs_arrive state i

/-- A potential completion leaves an idle queue unchanged. -/
theorem totalNonpreemptivePriorityJobs_step_completion_of_idle
    {n : ℕ} (state : NonpreemptivePriorityState n) (hactive : state.active = none) :
    totalNonpreemptivePriorityJobs
        (stepNonpreemptivePriority state none) =
      totalNonpreemptivePriorityJobs state := by
  simp [stepNonpreemptivePriority, completeNonpreemptivePriority, hactive]

/-- A potential completion from a busy queue removes exactly one job. -/
theorem totalNonpreemptivePriorityJobs_step_completion_of_active
    {n : ℕ} (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active) :
    totalNonpreemptivePriorityJobs
        (stepNonpreemptivePriority state none) + 1 =
      totalNonpreemptivePriorityJobs state := by
  exact totalNonpreemptivePriorityJobs_complete_of_active state active hactive

end Queueing
end AppliedModelingLib
