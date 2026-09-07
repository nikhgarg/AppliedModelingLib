import AppliedModelingLib.Foundations.Probability.Weighted
import AppliedModelingLib.Queueing.NonpreemptivePriorityDynamics
import Mathlib.Probability.Kernel.Invariance

/-!
# Uniformized class-dependent nonpreemptive-priority queues

This module gives the embedded discrete event chain for a finite priority
queue whose exponential service rate depends on the class currently in
service.  Separate potential-completion clocks make inactive-class completion
events self-loops; the active class therefore completes at precisely its own
rate.  The construction is useful both for homogeneous M/M/1 queues and for
finite mixtures of exponential service requirements.
-/

namespace AppliedModelingLib
namespace Queueing

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The exponential service rate corresponding to a positive mean service
requirement. -/
noncomputable def exponentialServiceRate
    {Class : Type*} (meanService : Class → ℝ) (i : Class) : ℝ :=
  (meanService i)⁻¹

/-- Positive mean service requirements induce positive exponential service
rates. -/
theorem exponentialServiceRate_pos
    {Class : Type*} (meanService : Class → ℝ) (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    0 < exponentialServiceRate meanService i := by
  exact inv_pos.mpr (hmeanService i)

/-- A positive mean service requirement is the reciprocal of its induced
exponential service rate. -/
theorem meanService_mul_exponentialServiceRate
    {Class : Type*} (meanService : Class → ℝ) (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    meanService i * exponentialServiceRate meanService i = 1 := by
  unfold exponentialServiceRate
  field_simp [ne_of_gt (hmeanService i)]

/-- The reciprocal-rate identity in the orientation used by service-clock
calculations. -/
theorem exponentialServiceRate_mul_meanService
    {Class : Type*} (meanService : Class → ℝ) (hmeanService : ∀ i, 0 < meanService i)
    (i : Class) :
    exponentialServiceRate meanService i * meanService i = 1 := by
  rw [mul_comm]
  exact meanService_mul_exponentialServiceRate meanService hmeanService i

/-- A class-dependent priority-queue event is either an arrival or a potential
completion labelled by a service class. -/
abbrev ClassDependentNonpreemptivePriorityEvent (n : ℕ) := Sum (Fin n) (Fin n)

/-- The discrete measurable structure on a finite labelled queue event has
measurable singleton events. -/
instance (n : ℕ) : MeasurableSingletonClass
    (ClassDependentNonpreemptivePriorityEvent n) where
  measurableSet_singleton event := by
    cases event with
    | inl i =>
        rw [show ({Sum.inl i} : Set (Sum (Fin n) (Fin n))) = Sum.inl '' {i} by
          ext x
          simp]
        exact (measurableSet_singleton i).inl_image
    | inr i =>
        rw [show ({Sum.inr i} : Set (Sum (Fin n) (Fin n))) = Sum.inr '' {i} by
          ext x
          simp]
        exact (measurableSet_singleton i).inr_image

/-- The unnormalized rate weight of an arrival or a labelled potential
completion. -/
def classDependentNonpreemptivePriorityEventWeight
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ) :
    ClassDependentNonpreemptivePriorityEvent n → ℝ
  | .inl i => arrivalRate i
  | .inr i => serviceRate i

/-- The finite event weights add to the total arrival and potential-service
rate. -/
theorem sum_classDependentNonpreemptivePriorityEventWeight
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ) :
    ∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate event =
      (∑ i, arrivalRate i) + ∑ i, serviceRate i := by
  simp [classDependentNonpreemptivePriorityEventWeight]

/-- The finite PMF of one class-dependent arrival-or-potential-completion
event.  A nonempty class set and positive service rates ensure that the total
uniformization rate is positive. -/
noncomputable def classDependentNonpreemptivePriorityEventPMF
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    PMF (ClassDependentNonpreemptivePriorityEvent n) :=
  finiteWeightedPMF
    (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
    (by
      intro event
      cases event with
      | inl i => exact harrivalRate i
      | inr i => exact (hserviceRate i).le)
    (by
      rw [sum_classDependentNonpreemptivePriorityEventWeight]
      let i : Fin n := ⟨0, hn⟩
      have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
        Finset.sum_nonneg fun j _ => harrivalRate j
      have hserviceSum : 0 < ∑ j, serviceRate j := by
        refine Finset.sum_pos' ?_ ?_
        · intro j _
          exact (hserviceRate j).le
        · exact ⟨i, Finset.mem_univ i, hserviceRate i⟩
      linarith)

/-- Apply one class-dependent uniformized event.  A potential completion acts
only if its label equals the class currently in service; otherwise it is a
self-loop. -/
noncomputable def stepClassDependentNonpreemptivePriority
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    NonpreemptivePriorityState n :=
  match event with
  | .inl i => arriveNonpreemptivePriority state i
  | .inr i => if state.active = some i then completeNonpreemptivePriority state else state

/-- At an empty embedded state, an arrival starts exactly the corresponding
one-job busy excursion. -/
theorem stepClassDependentNonpreemptivePriority_empty_arrival
    {n : ℕ} (i : Fin n) :
    stepClassDependentNonpreemptivePriority (emptyNonpreemptivePriorityState n) (.inl i) =
      arriveNonpreemptivePriority (emptyNonpreemptivePriorityState n) i := by
  rfl

/-- Every potential-completion label is a self-loop at the empty embedded
state.  These self-loops supply the idle part of a regenerative cycle. -/
theorem stepClassDependentNonpreemptivePriority_empty_completion
    {n : ℕ} (i : Fin n) :
    stepClassDependentNonpreemptivePriority (emptyNonpreemptivePriorityState n) (.inr i) =
      emptyNonpreemptivePriorityState n := by
  simp [stepClassDependentNonpreemptivePriority]

/-- One uniformized event from the empty priority queue is the explicit
mixture of an arrival-start state and an idle self-loop.  This is the local
regeneration identity used to close the boundary term of a full-cycle
occupation calculation. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_empty
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i)
    (observable : NonpreemptivePriorityState n → ℝ) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
        hn harrivalRate hserviceRate)
      (fun event => observable
        (stepClassDependentNonpreemptivePriority (emptyNonpreemptivePriorityState n) event)) =
      ((∑ i, arrivalRate i * observable
          (arriveNonpreemptivePriority (emptyNonpreemptivePriorityState n) i)) +
        (∑ i, serviceRate i) * observable (emptyNonpreemptivePriorityState n)) /
        ((∑ i, arrivalRate i) + ∑ i, serviceRate i) := by
  let weight := classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate
  have hweightNonneg : ∀ event, 0 ≤ weight event := by
    intro event
    cases event with
    | inl i => exact harrivalRate i
    | inr i => exact (hserviceRate i).le
  have htotalPos : 0 < ∑ event, weight event := by
    rw [show (∑ event, weight event) =
      (∑ i, arrivalRate i) + ∑ i, serviceRate i by
      simp [weight, classDependentNonpreemptivePriorityEventWeight]]
    let i : Fin n := ⟨0, hn⟩
    have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hserviceSum : 0 < ∑ j, serviceRate j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (hserviceRate j).le
      · exact ⟨i, Finset.mem_univ i, hserviceRate i⟩
    linarith
  let law := finiteWeightedPMF weight hweightNonneg htotalPos
  change pmfExp law _ = _
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  have hsum :
      (∑ event, (weight event / ∑ other, weight other) * observable
        (stepClassDependentNonpreemptivePriority
          (emptyNonpreemptivePriorityState n) event)) =
      (∑ event, weight event * observable
        (stepClassDependentNonpreemptivePriority
          (emptyNonpreemptivePriorityState n) event)) /
        ∑ other, weight other := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro event _
    field_simp
  rw [hsum]
  change
    ((∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate event * observable
        (stepClassDependentNonpreemptivePriority
          (emptyNonpreemptivePriorityState n) event)) /
      ∑ event : ClassDependentNonpreemptivePriorityEvent n,
        classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate event) = _
  rw [sum_classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate]
  simp [classDependentNonpreemptivePriorityEventWeight,
    stepClassDependentNonpreemptivePriority]
  rw [Finset.sum_mul]

/-- Every literal arrival-or-potential-completion event preserves the
invariant that an idle queue has no latent waiting backlog. -/
theorem nonpreemptivePriorityStateIdleConsistent_stepClassDependent
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state) :
    nonpreemptivePriorityStateIdleConsistent
      (stepClassDependentNonpreemptivePriority state event) := by
  cases event with
  | inl i =>
      exact nonpreemptivePriorityStateIdleConsistent_arrive state i
  | inr i =>
      by_cases hactive : state.active = some i
      · simpa [stepClassDependentNonpreemptivePriority, hactive] using
          (nonpreemptivePriorityStateIdleConsistent_complete state hconsistent)
      · simpa [stepClassDependentNonpreemptivePriority, hactive] using hconsistent

/-- The embedded discrete-time transition kernel of a finite nonpreemptive
priority queue with class-dependent exponential service rates. -/
noncomputable def classDependentNonpreemptivePriorityUniformizedKernel
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    NonpreemptivePriorityState n → PMF (NonpreemptivePriorityState n) :=
  fun state =>
    (classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
      hn harrivalRate hserviceRate).map
      (stepClassDependentNonpreemptivePriority state)

/-- The class-dependent uniformized kernel parameterized directly by positive
mean service requirements.  Its completion clock for a class has the
reciprocal mean rate. -/
noncomputable def meanServiceNonpreemptivePriorityUniformizedKernel
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i) :
    NonpreemptivePriorityState n → PMF (NonpreemptivePriorityState n) :=
  classDependentNonpreemptivePriorityUniformizedKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)

/-- The countable-state Markov-kernel realization of the class-dependent
uniformized priority queue. -/
noncomputable def classDependentNonpreemptivePriorityMeasureKernel
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    Kernel (NonpreemptivePriorityState n) (NonpreemptivePriorityState n) :=
  Kernel.ofFunOfCountable fun state =>
    (classDependentNonpreemptivePriorityUniformizedKernel arrivalRate serviceRate
      hn harrivalRate hserviceRate state).toMeasure

instance
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    IsMarkovKernel
      (classDependentNonpreemptivePriorityMeasureKernel arrivalRate serviceRate
        hn harrivalRate hserviceRate) where
  isProbabilityMeasure state := by
    change IsProbabilityMeasure
      ((classDependentNonpreemptivePriorityUniformizedKernel arrivalRate serviceRate
        hn harrivalRate hserviceRate state).toMeasure)
    infer_instance

/-- The Markov-kernel realization parameterized directly by positive mean
service requirements. -/
noncomputable def meanServiceNonpreemptivePriorityMeasureKernel
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i) :
    Kernel (NonpreemptivePriorityState n) (NonpreemptivePriorityState n) :=
  classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)

/-- The countable Markov kernel has the expected one-point mass of its PMF
row.  This is the measure-level interface used by occupation-flow proofs. -/
theorem classDependentNonpreemptivePriorityMeasureKernel_apply_singleton
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i)
    (state next : NonpreemptivePriorityState n) :
    classDependentNonpreemptivePriorityMeasureKernel arrivalRate serviceRate
      hn harrivalRate hserviceRate state {next} =
      classDependentNonpreemptivePriorityUniformizedKernel arrivalRate serviceRate
        hn harrivalRate hserviceRate state next := by
  change (classDependentNonpreemptivePriorityUniformizedKernel arrivalRate serviceRate
    hn harrivalRate hserviceRate state).toMeasure {next} = _
  exact PMF.toMeasure_apply_singleton _ next (measurableSet_singleton next)

/-- Mean service work waiting in a finite priority backlog.  This is a
queueing-state statistic, independent of the stochastic construction used to
generate arrivals and completions. -/
noncomputable def priorityWaitingMeanWork
    {n : ℕ} (meanService : Fin n → ℝ) (backlog : Fin n → ℕ) : ℝ :=
  ∑ i, meanService i * (backlog i : ℝ)

/-- Admitting a job of class `i` raises weighted waiting work by its mean
service requirement. -/
theorem priorityWaitingMeanWork_addPriorityArrival
    {n : ℕ} (meanService : Fin n → ℝ) (backlog : Fin n → ℕ) (i : Fin n) :
    priorityWaitingMeanWork meanService (addPriorityArrival backlog i) =
      priorityWaitingMeanWork meanService backlog + meanService i := by
  unfold priorityWaitingMeanWork addPriorityArrival
  rw [← Finset.sum_erase_add _ (fun j => meanService j * (backlog j : ℝ))
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _
    (fun j => meanService j * ((Function.update backlog i (backlog i + 1)) j : ℝ))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  have hrest :
      ∑ x ∈ Finset.univ.erase i,
        meanService x * ((Function.update backlog i (backlog i + 1)) x : ℝ) =
      ∑ x ∈ Finset.univ.erase i, meanService x * (backlog x : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : x ≠ i := Finset.mem_erase.mp hx |>.1
    simp [Function.update_of_ne hxi]
  rw [hrest]
  norm_num
  ring

/-- Starting a waiting job after a completion transfers exactly its mean work
from the weighted waiting backlog to the active-service coordinate. -/
theorem priorityWaitingMeanWork_completeNonpreemptivePriorityService
    {n : ℕ} (meanService : Fin n → ℝ) (backlog : Fin n → ℕ)
    (hnonempty : ∃ i, 0 < backlog i) :
    priorityWaitingMeanWork meanService
      (completeNonpreemptivePriorityService backlog hnonempty) +
        meanService (nextNonpreemptivePriority backlog hnonempty) =
      priorityWaitingMeanWork meanService backlog := by
  let i := nextNonpreemptivePriority backlog hnonempty
  have hi : 0 < backlog i := nextNonpreemptivePriority_positive backlog hnonempty
  unfold priorityWaitingMeanWork completeNonpreemptivePriorityService
  rw [← Finset.sum_erase_add _ (fun j => meanService j * (backlog j : ℝ))
    (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add _
    (fun j => meanService j * ((Function.update backlog i (backlog i - 1)) j : ℝ))
    (Finset.mem_univ i)]
  simp only [Function.update_self]
  have hrest :
      ∑ x ∈ Finset.univ.erase i,
        meanService x * ((Function.update backlog i (backlog i - 1)) x : ℝ) =
      ∑ x ∈ Finset.univ.erase i, meanService x * (backlog x : ℝ) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxi : x ≠ i := Finset.mem_erase.mp hx |>.1
    simp [Function.update_of_ne hxi]
  rw [hrest]
  norm_num
  have hcast : ((backlog i - 1 : ℕ) : ℝ) = (backlog i : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr hi)]
    norm_num
  rw [hcast]
  ring

/-- Total mean service work in a finite priority state, including the job in
service when the server is busy. -/
noncomputable def nonpreemptivePriorityMeanWork
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n) : ℝ :=
  (match state.active with | none => 0 | some i => meanService i) +
    priorityWaitingMeanWork meanService state.waiting

/-- The mean-service weight of one class's waiting population is bounded by
the total waiting work. -/
theorem meanService_mul_waitingClassJobs_le_priorityWaitingMeanWork
    {n : ℕ} (meanService : Fin n → ℝ) (hmeanService : ∀ i, 0 ≤ meanService i)
    (backlog : Fin n → ℕ) (i : Fin n) :
    meanService i * (backlog i : ℝ) ≤ priorityWaitingMeanWork meanService backlog := by
  unfold priorityWaitingMeanWork
  exact Finset.single_le_sum
    (fun j _ => show 0 ≤ meanService j * (backlog j : ℝ) from
      mul_nonneg (hmeanService j) (by positivity)) (Finset.mem_univ i)

/-- The mean-service weight of a class population, including a possible job
in service, is bounded by total mean work.  This deterministic bound is what
turns workload-area estimates into terminal class-population estimates. -/
theorem meanService_mul_classNonpreemptivePriorityJobs_le_meanWork
    {n : ℕ} (meanService : Fin n → ℝ) (hmeanService : ∀ i, 0 ≤ meanService i)
    (state : NonpreemptivePriorityState n) (i : Fin n) :
    meanService i * (classNonpreemptivePriorityJobs state i : ℝ) ≤
      nonpreemptivePriorityMeanWork meanService state := by
  have hwaiting := meanService_mul_waitingClassJobs_le_priorityWaitingMeanWork
    meanService hmeanService state.waiting i
  cases hactive : state.active with
  | none =>
      simpa [classNonpreemptivePriorityJobs, nonpreemptivePriorityMeanWork, hactive]
        using hwaiting
  | some active =>
      by_cases hi : active = i
      · subst active
        have hjobs : classNonpreemptivePriorityJobs state i = state.waiting i + 1 := by
          simp [classNonpreemptivePriorityJobs, hactive]
        rw [hjobs]
        simp only [Nat.cast_add, Nat.cast_one, nonpreemptivePriorityMeanWork, hactive]
        nlinarith
      · have hactiveNonneg : 0 ≤ meanService active := hmeanService active
        have hjobs : classNonpreemptivePriorityJobs state i = state.waiting i := by
          simp [classNonpreemptivePriorityJobs, hactive, hi]
        rw [hjobs]
        simp only [nonpreemptivePriorityMeanWork, hactive]
        exact hwaiting.trans (le_add_of_nonneg_left hactiveNonneg)

/-- An idle-consistent state has zero mean work whenever its active coordinate
is empty. -/
theorem nonpreemptivePriorityMeanWork_eq_zero_of_idle
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state)
    (hactive : state.active = none) :
    nonpreemptivePriorityMeanWork meanService state = 0 := by
  rw [nonpreemptivePriorityState_eq_empty_of_active_eq_none state hconsistent hactive]
  simp [nonpreemptivePriorityMeanWork, priorityWaitingMeanWork]

/-- An arrival raises total mean service work by the mean service requirement
of its declared class. -/
theorem nonpreemptivePriorityMeanWork_arrive
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (i : Fin n) :
    nonpreemptivePriorityMeanWork meanService (arriveNonpreemptivePriority state i) =
      nonpreemptivePriorityMeanWork meanService state + meanService i := by
  cases hactive : state.active with
  | none =>
      simp [nonpreemptivePriorityMeanWork, arriveNonpreemptivePriority, hactive]
      ring
  | some active =>
      simp only [arriveNonpreemptivePriority, hactive, nonpreemptivePriorityMeanWork]
      rw [priorityWaitingMeanWork_addPriorityArrival]
      ring

/-- Completing the active job lowers total mean service work by precisely the
mean service requirement of its active class. -/
theorem nonpreemptivePriorityMeanWork_complete_of_active
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (active : Fin n) (hactive : state.active = some active) :
    nonpreemptivePriorityMeanWork meanService (completeNonpreemptivePriority state) +
        meanService active = nonpreemptivePriorityMeanWork meanService state := by
  by_cases hwaiting : ∃ i, 0 < state.waiting i
  · simp only [completeNonpreemptivePriority, hactive, dif_pos hwaiting,
      nonpreemptivePriorityMeanWork]
    have hwork := priorityWaitingMeanWork_completeNonpreemptivePriorityService
      meanService state.waiting hwaiting
    linarith
  · simp [completeNonpreemptivePriority, hactive, hwaiting,
      nonpreemptivePriorityMeanWork]
    ring

/-- A class-dependent uniformized arrival raises mean work by the arriving
class's mean service requirement. -/
theorem nonpreemptivePriorityMeanWork_stepClassDependent_arrival
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (i : Fin n) :
    nonpreemptivePriorityMeanWork meanService
      (stepClassDependentNonpreemptivePriority state (.inl i)) =
      nonpreemptivePriorityMeanWork meanService state + meanService i := by
  exact nonpreemptivePriorityMeanWork_arrive meanService state i

/-- A potential completion labelled by the actual active class lowers mean
work by that class's mean service requirement. -/
theorem nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_active
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (active : Fin n) (hactive : state.active = some active) :
    nonpreemptivePriorityMeanWork meanService
      (stepClassDependentNonpreemptivePriority state (.inr active)) + meanService active =
      nonpreemptivePriorityMeanWork meanService state := by
  simp only [stepClassDependentNonpreemptivePriority, hactive, ↓reduceIte]
  exact nonpreemptivePriorityMeanWork_complete_of_active meanService state active hactive

/-- A potential completion labelled by an inactive class leaves mean work
unchanged. -/
theorem nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_inactive
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (serviceClass : Fin n) (hinactive : state.active ≠ some serviceClass) :
    nonpreemptivePriorityMeanWork meanService
      (stepClassDependentNonpreemptivePriority state (.inr serviceClass)) =
      nonpreemptivePriorityMeanWork meanService state := by
  simp [stepClassDependentNonpreemptivePriority, hinactive]

/-- The exact quadratic mean-work increment of one class-`i` arrival.  This
is the arrival term in the second-moment generator identity. -/
theorem nonpreemptivePriorityMeanWork_sq_stepClassDependent_arrival_sub
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (i : Fin n) :
    nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inl i)) ^ 2 -
      nonpreemptivePriorityMeanWork meanService state ^ 2 =
      2 * meanService i * nonpreemptivePriorityMeanWork meanService state +
        meanService i ^ 2 := by
  rw [nonpreemptivePriorityMeanWork_stepClassDependent_arrival]
  ring

/-- The exact quadratic mean-work increment of the potential completion clock
currently serving class `i`. -/
theorem nonpreemptivePriorityMeanWork_sq_stepClassDependent_completion_sub_of_active
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (i : Fin n) (hactive : state.active = some i) :
    nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 -
      nonpreemptivePriorityMeanWork meanService state ^ 2 =
      -2 * meanService i * nonpreemptivePriorityMeanWork meanService state +
        meanService i ^ 2 := by
  have hstep := nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_active
    meanService state i hactive
  have heq : nonpreemptivePriorityMeanWork meanService
      (stepClassDependentNonpreemptivePriority state (.inr i)) =
      nonpreemptivePriorityMeanWork meanService state - meanService i := by
    linarith
  rw [heq]
  ring

/-- A potential-completion clock not matching the current service class has
zero quadratic mean-work increment. -/
theorem nonpreemptivePriorityMeanWork_sq_stepClassDependent_completion_sub_of_inactive
    {n : ℕ} (meanService : Fin n → ℝ) (state : NonpreemptivePriorityState n)
    (i : Fin n) (hinactive : state.active ≠ some i) :
    nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 -
      nonpreemptivePriorityMeanWork meanService state ^ 2 = 0 := by
  rw [nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_inactive
    meanService state i hinactive]
  ring

/-- The unnormalized one-event drift of total mean work for a class-dependent
exponential priority queue.  It is the continuous-time generator numerator:
event weights are rates, not normalized probabilities. -/
noncomputable def classDependentNonpreemptivePriorityMeanWorkRateDrift
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  ∑ event : ClassDependentNonpreemptivePriorityEvent n,
    classDependentNonpreemptivePriorityEventWeight arrivalRate
      (exponentialServiceRate meanService) event *
      (nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event) -
        nonpreemptivePriorityMeanWork meanService state)

/-- In every busy state, the mean-work generator drift is total offered work
rate minus one unit of server capacity.  This is the Lyapunov identity behind
finite-workload arguments under strict load; it does not by itself assert a
stationary distribution or an integrability conclusion. -/
theorem classDependentNonpreemptivePriorityMeanWorkRateDrift_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active)
    (hmeanService : ∀ i, 0 < meanService i) :
    classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state =
      (∑ i, arrivalRate i * meanService i) - 1 := by
  classical
  unfold classDependentNonpreemptivePriorityMeanWorkRateDrift
  have harrival : ∀ i : Fin n,
      nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inl i)) -
        nonpreemptivePriorityMeanWork meanService state = meanService i := by
    intro i
    have h := nonpreemptivePriorityMeanWork_stepClassDependent_arrival
      meanService state i
    linarith
  have hcompletion_active :
      nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inr active)) -
        nonpreemptivePriorityMeanWork meanService state = - meanService active := by
    have h := nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_active
      meanService state active hactive
    linarith
  have hcompletion_inactive : ∀ i : Fin n, i ≠ active →
      nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inr i)) -
        nonpreemptivePriorityMeanWork meanService state = 0 := by
    intro i hi
    have hinactive : state.active ≠ some i := by
      intro h
      rw [hactive] at h
      exact hi (Option.some.inj h).symm
    rw [nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_inactive
      meanService state i hinactive]
    ring
  rw [show (∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService) event *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state event) -
          nonpreemptivePriorityMeanWork meanService state)) =
      (∑ i : Fin n, arrivalRate i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inl i)) -
          nonpreemptivePriorityMeanWork meanService state)) +
      ∑ i : Fin n, exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) -
          nonpreemptivePriorityMeanWork meanService state) by
        simp [classDependentNonpreemptivePriorityEventWeight]]
  simp_rw [harrival]
  rw [show (∑ i : Fin n, exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) -
          nonpreemptivePriorityMeanWork meanService state)) =
      exponentialServiceRate meanService active * (- meanService active) by
        rw [← Finset.sum_erase_add _
          (fun i => exponentialServiceRate meanService i *
            (nonpreemptivePriorityMeanWork meanService
              (stepClassDependentNonpreemptivePriority state (.inr i)) -
              nonpreemptivePriorityMeanWork meanService state))
          (Finset.mem_univ active)]
        simp only [hcompletion_active]
        have hzero : ∑ x ∈ Finset.univ.erase active,
            exponentialServiceRate meanService x *
              (nonpreemptivePriorityMeanWork meanService
                (stepClassDependentNonpreemptivePriority state (.inr x)) -
                nonpreemptivePriorityMeanWork meanService state) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          have hne : x ≠ active := Finset.mem_erase.mp hx |>.1
          simp [hcompletion_inactive x hne]
        rw [hzero]
        ring]
  rw [show exponentialServiceRate meanService active * -meanService active =
      -(exponentialServiceRate meanService active * meanService active) by ring,
    exponentialServiceRate_mul_meanService meanService hmeanService active]
  ring

/-- The unnormalized generator drift of squared total mean work.  Unlike the
Lyapunov inequality, this records the exact finite-event algebra needed to
identify a regenerative queue's first stationary work moment. -/
noncomputable def classDependentNonpreemptivePriorityMeanWorkSqRateDrift
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  ∑ event : ClassDependentNonpreemptivePriorityEvent n,
    classDependentNonpreemptivePriorityEventWeight arrivalRate
      (exponentialServiceRate meanService) event *
      (nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event) ^ 2 -
        nonpreemptivePriorityMeanWork meanService state ^ 2)

/-- At a busy state, the squared-work generator consists of twice the linear
work drift, the arrival second-moment rate, and the mean requirement of the
job currently in service. -/
theorem classDependentNonpreemptivePriorityMeanWorkSqRateDrift_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active)
    (hmeanService : ∀ i, 0 < meanService i) :
    classDependentNonpreemptivePriorityMeanWorkSqRateDrift arrivalRate meanService state =
      2 * ((∑ i, arrivalRate i * meanService i) - 1) *
          nonpreemptivePriorityMeanWork meanService state +
        (∑ i, arrivalRate i * meanService i ^ 2) + meanService active := by
  classical
  let W := nonpreemptivePriorityMeanWork meanService state
  have harrival : ∀ i : Fin n,
      nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inl i)) ^ 2 - W ^ 2 =
        2 * meanService i * W + meanService i ^ 2 := by
    intro i
    simpa [W] using
      nonpreemptivePriorityMeanWork_sq_stepClassDependent_arrival_sub meanService state i
  have hcompletionActive :
      nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr active)) ^ 2 - W ^ 2 =
        -2 * meanService active * W + meanService active ^ 2 := by
    simpa [W] using
      nonpreemptivePriorityMeanWork_sq_stepClassDependent_completion_sub_of_active
        meanService state active hactive
  have hcompletionInactive : ∀ i : Fin n, i ≠ active →
      nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 - W ^ 2 = 0 := by
    intro i hne
    have hinactive : state.active ≠ some i := by
      intro hi
      rw [hactive] at hi
      exact hne (Option.some.inj hi).symm
    simpa [W] using
      nonpreemptivePriorityMeanWork_sq_stepClassDependent_completion_sub_of_inactive
        meanService state i hinactive
  unfold classDependentNonpreemptivePriorityMeanWorkSqRateDrift
  rw [show (∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
          (exponentialServiceRate meanService) event *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state event) ^ 2 -
          nonpreemptivePriorityMeanWork meanService state ^ 2)) =
      (∑ i : Fin n, arrivalRate i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inl i)) ^ 2 - W ^ 2)) +
      ∑ i : Fin n, exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 - W ^ 2) by
        simp [classDependentNonpreemptivePriorityEventWeight, W]]
  simp_rw [harrival]
  have hcompletionSum :
      (∑ i : Fin n, exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 - W ^ 2)) =
        exponentialServiceRate meanService active *
          (-2 * meanService active * W + meanService active ^ 2) := by
    rw [← Finset.sum_erase_add _
      (fun i => exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 - W ^ 2))
      (Finset.mem_univ active)]
    simp only [hcompletionActive]
    have hzero : ∑ i ∈ Finset.univ.erase active,
        exponentialServiceRate meanService i *
          (nonpreemptivePriorityMeanWork meanService
            (stepClassDependentNonpreemptivePriority state (.inr i)) ^ 2 - W ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : i ≠ active := Finset.mem_erase.mp hi |>.1
      simp [hcompletionInactive i hne]
    rw [hzero]
    ring
  rw [hcompletionSum]
  have hcompletionValue :
      exponentialServiceRate meanService active *
        (-2 * meanService active * W + meanService active ^ 2) =
        -2 * W + meanService active := by
    calc
      exponentialServiceRate meanService active *
          (-2 * meanService active * W + meanService active ^ 2) =
          (exponentialServiceRate meanService active * meanService active) *
            (-2 * W + meanService active) := by ring
      _ = -2 * W + meanService active := by
        rw [exponentialServiceRate_mul_meanService meanService hmeanService active]
        ring
  rw [hcompletionValue]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hlinear : ∑ i : Fin n, arrivalRate i * (2 * meanService i * W) =
      2 * (∑ i, arrivalRate i * meanService i) * W := by
    calc
      ∑ i : Fin n, arrivalRate i * (2 * meanService i * W) =
          ∑ i : Fin n, (arrivalRate i * meanService i) * (2 * W) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (∑ i : Fin n, arrivalRate i * meanService i) * (2 * W) := by
            rw [Finset.sum_mul]
      _ = 2 * (∑ i, arrivalRate i * meanService i) * W := by ring
  rw [hlinear]
  dsimp [classDependentNonpreemptivePriorityMeanWorkSqRateDrift, W]
  ring

/-- Strict total offered load gives strictly negative mean-work generator
drift in every busy state. -/
theorem classDependentNonpreemptivePriorityMeanWorkRateDrift_neg_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state < 0 := by
  rw [classDependentNonpreemptivePriorityMeanWorkRateDrift_of_active
    arrivalRate meanService state active hactive hmeanService]
  linarith

/-- For any real state observable, a uniformized one-step expectation equals
its rate-weighted change divided by the total event rate.  This is the finite
generator identity shared by first- and second-moment calculations. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_sub_eq_rateWeightedChange_div
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n)
    (V : NonpreemptivePriorityState n → ℝ) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => V (stepClassDependentNonpreemptivePriority state event)) - V state =
      (∑ event : ClassDependentNonpreemptivePriorityEvent n,
        classDependentNonpreemptivePriorityEventWeight arrivalRate
          (exponentialServiceRate meanService) event *
          (V (stepClassDependentNonpreemptivePriority state event) - V state)) /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) := by
  let serviceRate := exponentialServiceRate meanService
  let weight := classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate
  have hweightNonneg : ∀ event, 0 ≤ weight event := by
    intro event
    cases event with
    | inl i => exact harrivalRate i
    | inr i => exact (exponentialServiceRate_pos meanService hmeanService i).le
  have htotalPos : 0 < ∑ event, weight event := by
    rw [show (∑ event, weight event) =
      (∑ i, arrivalRate i) + ∑ i, serviceRate i by
      simp [weight, classDependentNonpreemptivePriorityEventWeight]]
    let i : Fin n := ⟨0, hn⟩
    have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hserviceSum : 0 < ∑ j, serviceRate j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    linarith
  let P := finiteWeightedPMF weight hweightNonneg htotalPos
  change pmfExp P (fun event => V (stepClassDependentNonpreemptivePriority state event)) -
      V state = _
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  have hsum :
      (∑ a, (weight a / ∑ b, weight b) *
        V (stepClassDependentNonpreemptivePriority state a)) - V state =
        (∑ a, weight a *
          (V (stepClassDependentNonpreemptivePriority state a) - V state)) /
          ∑ b, weight b := by
    have hden : ∑ b, weight b ≠ 0 := ne_of_gt htotalPos
    have hfrac : ∑ a, weight a / ∑ b, weight b = 1 := by
      rw [← Finset.sum_div]
      field_simp
    calc
      (∑ a, (weight a / ∑ b, weight b) *
          V (stepClassDependentNonpreemptivePriority state a)) - V state =
          (∑ a, (weight a / ∑ b, weight b) *
            V (stepClassDependentNonpreemptivePriority state a)) -
            (∑ a, weight a / ∑ b, weight b) * V state := by
              rw [hfrac]
              ring
      _ = ∑ a, ((weight a / ∑ b, weight b) *
          V (stepClassDependentNonpreemptivePriority state a) -
          (weight a / ∑ b, weight b) * V state) := by
            rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      _ = ∑ a, (weight a / ∑ b, weight b) *
          (V (stepClassDependentNonpreemptivePriority state a) - V state) := by
            apply Finset.sum_congr rfl
            intro a _
            ring
      _ = (∑ a, weight a *
          (V (stepClassDependentNonpreemptivePriority state a) - V state)) /
          ∑ b, weight b := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro a _
            field_simp
  rw [hsum]
  change (∑ a, weight a *
      (V (stepClassDependentNonpreemptivePriority state a) - V state)) /
      ∑ b, weight b = _
  simp only [weight, serviceRate]
  rw [show (∑ b : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService) b) =
      (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i by
      exact sum_classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService)]

/-- The one-step expectation of squared mean work is its exact squared-work
generator drift divided by the total uniformization rate. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_meanWorkSq_sub_eq_rateDrift_div
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event) ^ 2) -
        nonpreemptivePriorityMeanWork meanService state ^ 2 =
      classDependentNonpreemptivePriorityMeanWorkSqRateDrift arrivalRate meanService state /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) := by
  simpa [classDependentNonpreemptivePriorityMeanWorkSqRateDrift] using
    (pmfExp_classDependentNonpreemptivePriorityEvent_sub_eq_rateWeightedChange_div
      arrivalRate meanService hn harrivalRate hmeanService state
      (fun x => nonpreemptivePriorityMeanWork meanService x ^ 2))

/-- The one-step expectation over the finite uniformized event PMF is the
rate-weighted drift divided by the total uniformization rate.  This statement
uses the finite event law directly, so it remains available even though the
priority-state space itself is countably infinite. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_eq_rateDrift_div
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event)) -
        nonpreemptivePriorityMeanWork meanService state =
      classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) := by
  let serviceRate := exponentialServiceRate meanService
  let weight := classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate
  have hweight_nonneg : ∀ event, 0 ≤ weight event := by
    intro event
    cases event with
    | inl i => exact harrivalRate i
    | inr i => exact (exponentialServiceRate_pos meanService hmeanService i).le
  have htotal_pos : 0 < ∑ event, weight event := by
    rw [show (∑ event, weight event) = (∑ i, arrivalRate i) + ∑ i, serviceRate i by
      simp [weight, classDependentNonpreemptivePriorityEventWeight]]
    let i : Fin n := ⟨0, hn⟩
    have harrival_sum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hservice_sum : 0 < ∑ j, serviceRate j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    linarith
  let P := finiteWeightedPMF weight hweight_nonneg htotal_pos
  let V := nonpreemptivePriorityMeanWork meanService
  let step := stepClassDependentNonpreemptivePriority state
  change pmfExp P (fun event => V (step event)) - V state = _
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  have hsum_eq :
      (∑ a, (weight a / ∑ b, weight b) * V (step a)) - V state =
        (∑ a, weight a * (V (step a) - V state)) / ∑ b, weight b := by
    have hden : ∑ b, weight b ≠ 0 := ne_of_gt htotal_pos
    have hfrac : ∑ a, weight a / ∑ b, weight b = 1 := by
      rw [← Finset.sum_div]
      field_simp
    calc
      (∑ a, (weight a / ∑ b, weight b) * V (step a)) - V state =
          (∑ a, (weight a / ∑ b, weight b) * V (step a)) -
            (∑ a, weight a / ∑ b, weight b) * V state := by
          rw [hfrac]
          ring
      _ = ∑ a, ((weight a / ∑ b, weight b) * V (step a) -
          (weight a / ∑ b, weight b) * V state) := by
          rw [Finset.sum_mul]
          rw [← Finset.sum_sub_distrib]
      _ =
        ∑ a, (weight a / ∑ b, weight b) * (V (step a) - V state) := by
          apply Finset.sum_congr rfl
          intro a _
          ring
      _ = (∑ a, weight a * (V (step a) - V state)) / ∑ b, weight b := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro a _
          field_simp
  rw [hsum_eq]
  change (∑ a, weight a * (V (step a) - V state)) / ∑ b, weight b = _
  simp only [weight, V, step, serviceRate]
  rw [show (∑ b : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService) b) =
      (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i by
      exact sum_classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService)]
  rfl

/-- Under strict total offered load, the finite uniformized event law has
strictly negative one-step expected mean-work drift at every busy state. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_neg_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event)) -
        nonpreemptivePriorityMeanWork meanService state < 0 := by
  rw [pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_eq_rateDrift_div
    arrivalRate meanService hn harrivalRate hmeanService state]
  apply div_neg_of_neg_of_pos
  · exact classDependentNonpreemptivePriorityMeanWorkRateDrift_neg_of_active
      arrivalRate meanService state active hactive hmeanService hstable
  · let i : Fin n := ⟨0, hn⟩
    have harrival_sum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hservice_sum : 0 < ∑ j, exponentialServiceRate meanService j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    linarith

/-- In an idle state, only arrivals change total mean work, so the generator
drift is exactly the total offered work rate. -/
theorem classDependentNonpreemptivePriorityMeanWorkRateDrift_of_idle
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n)
    (hactive : state.active = none) :
    classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state =
      ∑ i, arrivalRate i * meanService i := by
  classical
  unfold classDependentNonpreemptivePriorityMeanWorkRateDrift
  have harrival : ∀ i : Fin n,
      nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inl i)) -
        nonpreemptivePriorityMeanWork meanService state = meanService i := by
    intro i
    have h := nonpreemptivePriorityMeanWork_stepClassDependent_arrival
      meanService state i
    linarith
  have hcompletion : ∀ i : Fin n,
      nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state (.inr i)) -
        nonpreemptivePriorityMeanWork meanService state = 0 := by
    intro i
    have hinactive : state.active ≠ some i := by
      rw [hactive]
      simp
    rw [nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_inactive
      meanService state i hinactive]
    ring
  rw [show (∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
        (exponentialServiceRate meanService) event *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state event) -
          nonpreemptivePriorityMeanWork meanService state)) =
      (∑ i : Fin n, arrivalRate i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inl i)) -
          nonpreemptivePriorityMeanWork meanService state)) +
      ∑ i : Fin n, exponentialServiceRate meanService i *
        (nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inr i)) -
          nonpreemptivePriorityMeanWork meanService state) by
        simp [classDependentNonpreemptivePriorityEventWeight]]
  simp_rw [harrival, hcompletion]
  simp

/-- A class-dependent uniformized arrival always raises the total queue
population by one. -/
theorem totalNonpreemptivePriorityJobs_stepClassDependent_arrival
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    totalNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inl i)) =
      totalNonpreemptivePriorityJobs state + 1 := by
  exact totalNonpreemptivePriorityJobs_arrive state i

/-- A uniformized arrival increments exactly the declared class population. -/
theorem classNonpreemptivePriorityJobs_stepClassDependent_arrival
    {n : ℕ} (state : NonpreemptivePriorityState n) (arrivalClass i : Fin n) :
    classNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inl arrivalClass)) i =
      classNonpreemptivePriorityJobs state i + if i = arrivalClass then 1 else 0 := by
  exact classNonpreemptivePriorityJobs_arrive state arrivalClass i

/-- A potential completion for the active class removes exactly one job. -/
theorem totalNonpreemptivePriorityJobs_stepClassDependent_completion_of_active
    {n : ℕ} (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active) :
    totalNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inr active)) + 1 =
      totalNonpreemptivePriorityJobs state := by
  simp only [stepClassDependentNonpreemptivePriority, hactive, ↓reduceIte]
  exact totalNonpreemptivePriorityJobs_complete_of_active state active hactive

/-- A potential completion of the actual active class decreases exactly that
class's population. -/
theorem classNonpreemptivePriorityJobs_stepClassDependent_completion_of_active
    {n : ℕ} (state : NonpreemptivePriorityState n) (active i : Fin n)
    (hactive : state.active = some active) :
    classNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inr active)) i +
        (if i = active then 1 else 0) =
      classNonpreemptivePriorityJobs state i := by
  simpa [stepClassDependentNonpreemptivePriority, hactive] using
    (classNonpreemptivePriorityJobs_complete_of_active state active i hactive)

/-- A potential completion for an inactive class is a self-loop. -/
theorem stepClassDependentNonpreemptivePriority_completion_of_inactive
    {n : ℕ} (state : NonpreemptivePriorityState n) (serviceClass : Fin n)
    (hinactive : state.active ≠ some serviceClass) :
    stepClassDependentNonpreemptivePriority state (.inr serviceClass) = state := by
  simp [stepClassDependentNonpreemptivePriority, hinactive]

/-- Hence an inactive-class potential completion leaves the total queue
population unchanged. -/
theorem totalNonpreemptivePriorityJobs_stepClassDependent_completion_of_inactive
    {n : ℕ} (state : NonpreemptivePriorityState n) (serviceClass : Fin n)
    (hinactive : state.active ≠ some serviceClass) :
    totalNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inr serviceClass)) =
      totalNonpreemptivePriorityJobs state := by
  rw [stepClassDependentNonpreemptivePriority_completion_of_inactive
    state serviceClass hinactive]

/-- An inactive potential-completion clock leaves every class population
unchanged. -/
theorem classNonpreemptivePriorityJobs_stepClassDependent_completion_of_inactive
    {n : ℕ} (state : NonpreemptivePriorityState n) (serviceClass i : Fin n)
    (hinactive : state.active ≠ some serviceClass) :
    classNonpreemptivePriorityJobs
        (stepClassDependentNonpreemptivePriority state (.inr serviceClass)) i =
      classNonpreemptivePriorityJobs state i := by
  rw [stepClassDependentNonpreemptivePriority_completion_of_inactive
    state serviceClass hinactive]

/-- The unnormalized generator drift of one class population.  Arrival rates
enter through the selected class, while a potential completion removes a job
only when that class is currently in service. -/
noncomputable def classDependentNonpreemptivePriorityClassJobRateDrift
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) (i : Fin n) : ℝ :=
  ∑ event : ClassDependentNonpreemptivePriorityEvent n,
    classDependentNonpreemptivePriorityEventWeight arrivalRate
      (exponentialServiceRate meanService) event *
      ((classNonpreemptivePriorityJobs
          (stepClassDependentNonpreemptivePriority state event) i : ℝ) -
        classNonpreemptivePriorityJobs state i)

/-- In a state serving class `active`, the class-`i` population generator is
its arrival rate minus its service-clock rate exactly when `i` is active. -/
theorem classDependentNonpreemptivePriorityClassJobRateDrift_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) (active i : Fin n)
    (hactive : state.active = some active) :
    classDependentNonpreemptivePriorityClassJobRateDrift arrivalRate meanService state i =
      arrivalRate i - exponentialServiceRate meanService i *
        (if i = active then 1 else 0) := by
  classical
  have harrival : ∀ arrivalClass : Fin n,
      (classNonpreemptivePriorityJobs
          (stepClassDependentNonpreemptivePriority state (.inl arrivalClass)) i : ℝ) -
        classNonpreemptivePriorityJobs state i =
      if i = arrivalClass then 1 else 0 := by
    intro arrivalClass
    rw [classNonpreemptivePriorityJobs_stepClassDependent_arrival]
    by_cases hi : i = arrivalClass
    · subst arrivalClass
      norm_num
    · simp [hi]
  have hcompletion : ∀ serviceClass : Fin n,
      (classNonpreemptivePriorityJobs
          (stepClassDependentNonpreemptivePriority state (.inr serviceClass)) i : ℝ) -
        classNonpreemptivePriorityJobs state i =
      if serviceClass = active then -(if i = active then 1 else 0) else 0 := by
    intro serviceClass
    by_cases hservice : serviceClass = active
    · subst serviceClass
      have hcompleted :=
        classNonpreemptivePriorityJobs_stepClassDependent_completion_of_active
          state active i hactive
      by_cases hi : i = active
      · subst i
        have hcompletedNat :
            classNonpreemptivePriorityJobs
              (stepClassDependentNonpreemptivePriority state (.inr active)) active + 1 =
              classNonpreemptivePriorityJobs state active := by
          simpa using hcompleted
        have hcompletedReal :
            (classNonpreemptivePriorityJobs
              (stepClassDependentNonpreemptivePriority state (.inr active)) active : ℝ) + 1 =
              classNonpreemptivePriorityJobs state active := by
          exact_mod_cast hcompletedNat
        simp
        linarith
      · have heq : classNonpreemptivePriorityJobs
            (stepClassDependentNonpreemptivePriority state (.inr active)) i =
            classNonpreemptivePriorityJobs state i := by
          simpa [hi] using hcompleted
        rw [heq]
        simp [hi]
    · have hinactive : state.active ≠ some serviceClass := by
        intro h
        rw [hactive] at h
        exact hservice (Option.some.inj h).symm
      rw [classNonpreemptivePriorityJobs_stepClassDependent_completion_of_inactive
        state serviceClass i hinactive]
      simp [hservice]
  unfold classDependentNonpreemptivePriorityClassJobRateDrift
  rw [show (∑ event : ClassDependentNonpreemptivePriorityEvent n,
      classDependentNonpreemptivePriorityEventWeight arrivalRate
          (exponentialServiceRate meanService) event *
        ((classNonpreemptivePriorityJobs
            (stepClassDependentNonpreemptivePriority state event) i : ℝ) -
          classNonpreemptivePriorityJobs state i)) =
      (∑ arrivalClass : Fin n, arrivalRate arrivalClass *
        ((classNonpreemptivePriorityJobs
            (stepClassDependentNonpreemptivePriority state (.inl arrivalClass)) i : ℝ) -
          classNonpreemptivePriorityJobs state i)) +
      ∑ serviceClass : Fin n, exponentialServiceRate meanService serviceClass *
        ((classNonpreemptivePriorityJobs
            (stepClassDependentNonpreemptivePriority state (.inr serviceClass)) i : ℝ) -
          classNonpreemptivePriorityJobs state i) by
        simp [classDependentNonpreemptivePriorityEventWeight]]
  simp_rw [harrival, hcompletion]
  simp
  by_cases hi : i = active
  · subst i
    ring
  · simp [hi]

/-- The one-step uniformized expectation of a class population is its exact
classwise generator drift divided by the total event rate. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_classJobs_sub_eq_rateDrift_div
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) (i : Fin n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event =>
        (classNonpreemptivePriorityJobs
          (stepClassDependentNonpreemptivePriority state event) i : ℝ)) -
        classNonpreemptivePriorityJobs state i =
      classDependentNonpreemptivePriorityClassJobRateDrift
        arrivalRate meanService state i /
        ((∑ j, arrivalRate j) + ∑ j, exponentialServiceRate meanService j) := by
  simpa [classDependentNonpreemptivePriorityClassJobRateDrift] using
    (pmfExp_classDependentNonpreemptivePriorityEvent_sub_eq_rateWeightedChange_div
      arrivalRate meanService hn harrivalRate hmeanService state
      (fun x => (classNonpreemptivePriorityJobs x i : ℝ)))

end Queueing
end AppliedModelingLib
