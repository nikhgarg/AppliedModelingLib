import AppliedModelingLib.Foundations.Probability.FiniteEventDrift
import AppliedModelingLib.Foundations.Probability.FiniteEventIIDBridge
import AppliedModelingLib.Foundations.Probability.FiniteEventCappedStopping
import AppliedModelingLib.Foundations.Probability.IidExternalWeightedReward
import AppliedModelingLib.Foundations.Probability.ExponentialMoments
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentUniformization
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentSecondMoment
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Finite-horizon busy-period control for class-dependent priority queues

This module applies the finite-event Lyapunov calculation to a literal
uniformized nonpreemptive-priority queue.  The event chain is stopped after it
first reaches an idle state.  Strict offered load then bounds the expected
accumulated busy-state charge at every finite horizon.  It is a finite-time
ingredient for a later renewal construction, not a stationary-performance
claim.
-/

namespace AppliedModelingLib.Queueing

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The uniformized queue update stopped at an idle state.  Once idle, this
auxiliary trajectory remains at that regeneration state. -/
noncomputable def stopAtIdleClassDependentNonpreemptivePriorityStep
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    NonpreemptivePriorityState n :=
  if state.active = none then state
  else stepClassDependentNonpreemptivePriority state event

/-- Stopping the auxiliary event chain at idleness preserves the structural
invariant that no waiting backlog survives an idle epoch. -/
theorem nonpreemptivePriorityStateIdleConsistent_stopAtIdleStep
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state) :
    nonpreemptivePriorityStateIdleConsistent
      (stopAtIdleClassDependentNonpreemptivePriorityStep state event) := by
  by_cases hidle : state.active = none
  · simpa [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle] using hconsistent
  · simpa [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle] using
      (nonpreemptivePriorityStateIdleConsistent_stepClassDependent state event hconsistent)

/-- Every finite prefix of an idle-stopped queue trajectory started from an
idle-consistent state remains idle-consistent. -/
theorem nonpreemptivePriorityStateIdleConsistent_stopAtIdleTrajectory
    {n : ℕ} (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (horizon : ℕ) (sample : Fin horizon → ClassDependentNonpreemptivePriorityEvent n) :
    nonpreemptivePriorityStateIdleConsistent
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) := by
  exact Probability.finiteEventTrajectory_invariant initial
    stopAtIdleClassDependentNonpreemptivePriorityStep hinitial
    (fun state event hstate =>
      nonpreemptivePriorityStateIdleConsistent_stopAtIdleStep state event hstate)
    horizon sample

/-- Reaching an idle state in an idle-stopped execution means reaching the
literal empty queue state, not merely a record with a vacant active slot. -/
theorem finiteEventTrajectory_stopAtIdle_eq_empty_of_active_eq_none
    {n : ℕ} (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (horizon : ℕ) (sample : Fin horizon → ClassDependentNonpreemptivePriorityEvent n)
    (hidle : (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample).active = none) :
    Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample =
      emptyNonpreemptivePriorityState n := by
  exact nonpreemptivePriorityState_eq_empty_of_active_eq_none _
    (nonpreemptivePriorityStateIdleConsistent_stopAtIdleTrajectory initial hinitial
      horizon sample)
    hidle

/-- The positive one-step Lyapunov allowance associated with strict total
load, expressed in uniformized-event units. -/
noncomputable def classDependentNonpreemptivePriorityBusyAllowance
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) : ℝ :=
  (1 - ∑ i, arrivalRate i * meanService i) /
    ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)

/-- Charge one uniformized busy event by the strict-load allowance and charge
an idle state by zero. -/
noncomputable def classDependentNonpreemptivePriorityBusyCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  if state.active = none then 0
  else classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService

/-- The quadratic finite-start Lyapunov potential.  The linear correction
absorbs the uniformly bounded square-increment remainder, leaving a negative
charge proportional to mean work on every busy uniformized step. -/
noncomputable def classDependentNonpreemptivePrioritySecondMomentPotential
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  nonpreemptivePriorityMeanWork meanService state ^ 2 +
    ((classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 /
      classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) *
      nonpreemptivePriorityMeanWork meanService state

/-- The second-moment potential charges a busy state in proportion to its
weighted mean work, and charges the absorbing idle state by zero. -/
noncomputable def classDependentNonpreemptivePriorityMeanWorkBusyCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  if state.active = none then 0
  else 2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService *
    nonpreemptivePriorityMeanWork meanService state

/-- On an idle-consistent queue state, the busy-state charge is simply the
strict-load coefficient times mean work: no exceptional idle term remains. -/
theorem classDependentNonpreemptivePriorityMeanWorkBusyCost_eq_scale_mul_meanWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state) :
    classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state =
      (2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) *
        nonpreemptivePriorityMeanWork meanService state := by
  unfold classDependentNonpreemptivePriorityMeanWorkBusyCost
  by_cases hidle : state.active = none
  · rw [if_pos hidle,
      nonpreemptivePriorityMeanWork_eq_zero_of_idle meanService state hconsistent hidle]
    ring
  · rw [if_neg hidle]

/-- The negative exact squared-work generator drift, stopped at the empty
state.  It is intentionally allowed to have either sign: the accompanying
finite-horizon theorem is an accounting equality, not a Lyapunov bound. -/
noncomputable def classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (state : NonpreemptivePriorityState n) : ℝ :=
  if state.active = none then 0
  else -classDependentNonpreemptivePriorityMeanWorkSqRateDrift arrivalRate meanService state /
    ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)

/-- The idle-stopped chain satisfies the exact squared-work one-step
accounting identity.  This is the finite-event form of the generator
calculation; no invariant distribution or limiting interchange is used. -/
theorem classDependentNonpreemptivePriority_stopAtIdle_meanWorkSq_exactDrift
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => nonpreemptivePriorityMeanWork meanService
        (stopAtIdleClassDependentNonpreemptivePriorityStep state event) ^ 2) +
      classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost
        arrivalRate meanService state =
      nonpreemptivePriorityMeanWork meanService state ^ 2 := by
  by_cases hidle : state.active = none
  · simp [stopAtIdleClassDependentNonpreemptivePriorityStep,
      classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost, hidle]
  · have hsq :=
      pmfExp_classDependentNonpreemptivePriorityEvent_meanWorkSq_sub_eq_rateDrift_div
        arrivalRate meanService hn harrivalRate hmeanService state
    rw [show stopAtIdleClassDependentNonpreemptivePriorityStep state =
        stepClassDependentNonpreemptivePriority state by
      funext event
      simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]]
    simp only [classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost,
      if_neg hidle]
    have hneg :
        -classDependentNonpreemptivePriorityMeanWorkSqRateDrift
            arrivalRate meanService state /
          ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) =
        -(classDependentNonpreemptivePriorityMeanWorkSqRateDrift
            arrivalRate meanService state /
          ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)) := by
      ring
    rw [hneg]
    linarith

/-- Exact finite-horizon squared-work accounting for an idle-stopped priority
excursion.  The residual endpoint is kept explicit; removing it at an
unbounded regeneration horizon requires a separate justified limit. -/
theorem finiteEventExpectedCumulativeStoppedMeanWorkSqGeneratorCost_add_expectedMeanWorkSq_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : NonpreemptivePriorityState n) (horizon : ℕ) :
    Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost
        arrivalRate meanService) horizon +
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => nonpreemptivePriorityMeanWork meanService
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) ^ 2) =
      nonpreemptivePriorityMeanWork meanService initial ^ 2 := by
  exact Probability.finiteEventExpectedCumulativeCost_add_expectedPotential_eq_initial
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    (fun state => nonpreemptivePriorityMeanWork meanService state ^ 2)
    (classDependentNonpreemptivePriorityStoppedMeanWorkSqGeneratorCost
      arrivalRate meanService)
    (classDependentNonpreemptivePriority_stopAtIdle_meanWorkSq_exactDrift
      arrivalRate meanService hn harrivalRate hmeanService)
    horizon

/-- The negative class-population generator drift, stopped at an idle state.
As with the squared-work accountant, this signed cost is an exact finite
balance rather than a nonnegative Lyapunov charge. -/
noncomputable def classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n)
    (state : NonpreemptivePriorityState n) : ℝ :=
  if state.active = none then 0
  else -classDependentNonpreemptivePriorityClassJobRateDrift
      arrivalRate meanService state i /
    ((∑ j, arrivalRate j) + ∑ j, exponentialServiceRate meanService j)

/-- Exact one-step class-population accounting for the idle-stopped queue. -/
theorem classDependentNonpreemptivePriority_stopAtIdle_classJobs_exactDrift
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
          (stopAtIdleClassDependentNonpreemptivePriorityStep state event) i : ℝ)) +
      classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
        arrivalRate meanService i state =
      classNonpreemptivePriorityJobs state i := by
  by_cases hidle : state.active = none
  · simp [stopAtIdleClassDependentNonpreemptivePriorityStep,
      classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost, hidle]
  · have hdrift :=
      pmfExp_classDependentNonpreemptivePriorityEvent_classJobs_sub_eq_rateDrift_div
        arrivalRate meanService hn harrivalRate hmeanService state i
    rw [show stopAtIdleClassDependentNonpreemptivePriorityStep state =
        stepClassDependentNonpreemptivePriority state by
      funext event
      simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]]
    simp only [classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost,
      if_neg hidle]
    have hneg :
        -classDependentNonpreemptivePriorityClassJobRateDrift
            arrivalRate meanService state i /
          ((∑ j, arrivalRate j) + ∑ j, exponentialServiceRate meanService j) =
        -(classDependentNonpreemptivePriorityClassJobRateDrift
            arrivalRate meanService state i /
          ((∑ j, arrivalRate j) + ∑ j, exponentialServiceRate meanService j)) := by
      ring
    rw [hneg]
    linarith

/-- Exact finite-horizon class-population accounting for an idle-stopped
priority excursion.  The terminal class population remains explicit until a
separate justified regeneration-limit argument removes it. -/
theorem finiteEventExpectedCumulativeStoppedClassJobGeneratorCost_add_expectedClassJobs_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : NonpreemptivePriorityState n) (i : Fin n) (horizon : ℕ) :
    Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
        arrivalRate meanService i) horizon +
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample =>
          (classNonpreemptivePriorityJobs
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i : ℝ)) =
      classNonpreemptivePriorityJobs initial i := by
  exact Probability.finiteEventExpectedCumulativeCost_add_expectedPotential_eq_initial
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    (fun state => (classNonpreemptivePriorityJobs state i : ℝ))
    (classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
      arrivalRate meanService i)
    (fun state =>
      classDependentNonpreemptivePriority_stopAtIdle_classJobs_exactDrift
        arrivalRate meanService hn harrivalRate hmeanService state i)
    horizon

/-- The one-step signed flow contribution into a fixed embedded queue state,
counted only while a stopped fresh excursion is busy.  Its finite telescoping
identity is the statewise precursor of the regenerative invariant-measure
balance. -/
noncomputable def classDependentNonpreemptivePriorityStateIndicator
    {n : ℕ} (target state : NonpreemptivePriorityState n) : ℝ := by
  classical
  exact if state = target then 1 else 0

noncomputable def classDependentNonpreemptivePriorityStoppedStateFlowCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (target state : NonpreemptivePriorityState n) : ℝ :=
  if state.active = none then 0
  else classDependentNonpreemptivePriorityStateIndicator target state -
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => classDependentNonpreemptivePriorityStateIndicator target
        (stepClassDependentNonpreemptivePriority state event))

/-- Exact one-step state-flow accounting for the idle-stopped event chain.
At a busy state the auxiliary step is the actual queue transition; at the
empty state both sides are the same self-loop. -/
theorem classDependentNonpreemptivePriority_stopAtIdle_stateIndicator_exactDrift
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (target state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => classDependentNonpreemptivePriorityStateIndicator target
        (stopAtIdleClassDependentNonpreemptivePriorityStep state event)) +
      classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService target state =
      classDependentNonpreemptivePriorityStateIndicator target state := by
  classical
  by_cases hidle : state.active = none
  · have hstep : ∀ event,
      stopAtIdleClassDependentNonpreemptivePriorityStep state event = state := by
      intro event
      simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]
    simp_rw [hstep]
    simp [classDependentNonpreemptivePriorityStoppedStateFlowCost, hidle]
  · rw [show stopAtIdleClassDependentNonpreemptivePriorityStep state =
      stepClassDependentNonpreemptivePriority state by
        funext event
        simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]]
    simp only [classDependentNonpreemptivePriorityStoppedStateFlowCost, if_neg hidle]
    ring

/-- The finite exact balance of flow into any fixed embedded queue state.
The terminal indicator is deliberately retained; strict-load regeneration
will later justify its limiting value at the literal empty state. -/
theorem finiteEventExpectedCumulativeStoppedStateFlowCost_add_expectedStateIndicator_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial target : NonpreemptivePriorityState n) (horizon : ℕ) :
    Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService target) horizon +
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => classDependentNonpreemptivePriorityStateIndicator target
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) =
      classDependentNonpreemptivePriorityStateIndicator target initial := by
  classical
  exact Probability.finiteEventExpectedCumulativeCost_add_expectedPotential_eq_initial
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    (classDependentNonpreemptivePriorityStateIndicator target)
    (classDependentNonpreemptivePriorityStoppedStateFlowCost
      arrivalRate meanService hn harrivalRate hmeanService target)
    (fun state =>
      classDependentNonpreemptivePriority_stopAtIdle_stateIndicator_exactDrift
        arrivalRate meanService hn harrivalRate hmeanService target state)
    horizon

/-- The event that a priority queue state still has an active service.  Along
an idle-stopped trajectory this is exactly the event that the busy period has
not yet ended. -/
def classDependentNonpreemptivePriorityBusy
    {n : ℕ} (state : NonpreemptivePriorityState n) : Prop :=
  state.active ≠ none

local instance classDependentNonpreemptivePriorityBusy_decidablePred
    {n : ℕ} : DecidablePred (@classDependentNonpreemptivePriorityBusy n) :=
  fun state => Classical.propDecidable (classDependentNonpreemptivePriorityBusy state)

/-- The event that the idle-stopped uniformized queue is busy after a fixed
event horizon on its literal IID event stream. -/
def classDependentNonpreemptivePriorityBusyEvent
    {n : ℕ} (initial : NonpreemptivePriorityState n) (horizon : ℕ) :
    Set (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
  {omega | classDependentNonpreemptivePriorityBusy
    (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityStep horizon
      (Probability.IIDStream.block 0 horizon omega))}

/-- Each finite-horizon busy event is Borel measurable on the IID event
stream. -/
theorem measurableSet_classDependentNonpreemptivePriorityBusyEvent
    {n : ℕ} (initial : NonpreemptivePriorityState n) (horizon : ℕ) :
    MeasurableSet
      (classDependentNonpreemptivePriorityBusyEvent initial horizon) := by
  classical
  let s : Set (Fin horizon → ClassDependentNonpreemptivePriorityEvent n) :=
    {sample | classDependentNonpreemptivePriorityBusy
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)}
  have hs : MeasurableSet s := (Set.toFinite s).measurableSet
  change MeasurableSet ((Probability.IIDStream.block 0 horizon) ⁻¹' s)
  exact hs.preimage (Probability.IIDStream.measurable_block 0 horizon)

/-- The first idle epoch before a deterministic cap in the literal
uniformized event stream.  The cap makes this a total restart index; it does
not assert that the unbounded busy period terminates on every path. -/
noncomputable def classDependentNonpreemptivePriorityBusyCappedStoppingIndex
    {n : ℕ} (initial : NonpreemptivePriorityState n) (cap : ℕ) :
    Probability.IIDStream.PrefixStoppingIndex
      (α := ClassDependentNonpreemptivePriorityEvent n) :=
  Probability.IIDStream.finiteEventFirstHitCappedStoppingIndex initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    (fun state => state.active = none) cap

/-- If the capped idle-search index stops strictly before its fallback level,
the idle-stopped trajectory is actually idle at that event epoch. -/
theorem classDependentNonpreemptivePriorityBusyCappedStoppingIndex_idle_of_lt_cap
    {n : ℕ} (initial : NonpreemptivePriorityState n) (cap : ℕ)
    (omega : ℕ → ClassDependentNonpreemptivePriorityEvent n)
    (hstop : classDependentNonpreemptivePriorityBusyCappedStoppingIndex initial cap omega < cap) :
    (Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityBusyCappedStoppingIndex initial cap omega)
      (Probability.IIDStream.block 0
        (classDependentNonpreemptivePriorityBusyCappedStoppingIndex initial cap omega) omega)).active =
      none := by
  change Probability.IIDStream.finiteEventFirstHitCapped initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    (fun state => state.active = none) cap omega < cap at hstop
  change (Probability.finiteEventTrajectory initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    (Probability.IIDStream.finiteEventFirstHitCapped initial
      stopAtIdleClassDependentNonpreemptivePriorityStep
      (fun state => state.active = none) cap omega)
    (Probability.IIDStream.block 0
      (Probability.IIDStream.finiteEventFirstHitCapped initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        (fun state => state.active = none) cap omega) omega)).active = none
  exact (Probability.IIDStream.finiteEventFirstHitCapped_eq_iff_of_lt initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    (fun state => state.active = none) hstop omega).mp rfl |>.1

/-- A finite block after the capped idle-search index has the original IID
event law.  When idleness occurs before the cap this is a discrete
regeneration fact; on the fallback level it is only a valid bounded restart
index.  Neither case identifies a stationary Palm queue with this finite-start
construction. -/
theorem classDependentNonpreemptivePriority_postBlock_hasLaw_afterBusyCappedStop
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : NonpreemptivePriorityState n) (cap q : ℕ) :
    HasLaw
      (Probability.IIDStream.PrefixStoppingIndex.postBlock
        (classDependentNonpreemptivePriorityBusyCappedStoppingIndex initial cap) q)
      (Measure.pi (fun _ : Fin q =>
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure))
      (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure law.toMeasure := by
    dsimp [law]
    infer_instance
  simpa [classDependentNonpreemptivePriorityBusyCappedStoppingIndex, law] using
    (Probability.IIDStream.PrefixStoppingIndex.postBlock_hasLaw law.toMeasure
      (Probability.IIDStream.finiteEventFirstHitCappedStoppingIndex initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        (fun state => state.active = none) cap) q)

/-- The complete unused event suffix after the capped idle-search index has
the original IID law.  The eventual-idle estimate below is what later permits
a source model to remove the cap; this theorem itself stays finite and exact. -/
theorem classDependentNonpreemptivePriority_postTail_hasLaw_afterBusyCappedStop
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : NonpreemptivePriorityState n) (cap : ℕ) :
    HasLaw
      (Probability.IIDStream.PrefixStoppingIndex.postTail
        (classDependentNonpreemptivePriorityBusyCappedStoppingIndex initial cap))
      (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure)
      (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure law.toMeasure := by
    dsimp [law]
    infer_instance
  simpa [classDependentNonpreemptivePriorityBusyCappedStoppingIndex, law] using
    (Probability.IIDStream.PrefixStoppingIndex.postTail_hasLaw law.toMeasure
      (Probability.IIDStream.finiteEventFirstHitCappedStoppingIndex initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        (fun state => state.active = none) cap))

/-- The elapsed time spent in busy states by a uniformized event path with
independent exponential holding times.  This is a one-sided regenerative
construction; it does not assert a stationary queue law or a Palm coupling. -/
noncomputable def classDependentNonpreemptivePriorityBusyHoldingTime
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    ((ℕ → ClassDependentNonpreemptivePriorityEvent n) × (ℕ → ℝ)) → ENNReal :=
  Probability.IIDStream.externalWeightedENNReward
    (classDependentNonpreemptivePriorityBusyEvent initial) ENNReal.ofReal

/-- The independent-holding-time busy-period observable is Borel. -/
theorem measurable_classDependentNonpreemptivePriorityBusyHoldingTime
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    Measurable (classDependentNonpreemptivePriorityBusyHoldingTime initial) := by
  unfold classDependentNonpreemptivePriorityBusyHoldingTime
  exact Measurable.ennreal_tsum fun horizon =>
    Probability.IIDStream.measurable_externalWeightedENNRewardSummand
      (classDependentNonpreemptivePriorityBusyEvent initial) ENNReal.ofReal
      (measurableSet_classDependentNonpreemptivePriorityBusyEvent initial)
      ENNReal.measurable_ofReal horizon

/-- Weighted mean work is nonnegative when all mean service requirements are
nonnegative. -/
theorem nonpreemptivePriorityMeanWork_nonneg
    {n : ℕ} (meanService : Fin n → ℝ) (hmeanService : ∀ i, 0 ≤ meanService i)
    (state : NonpreemptivePriorityState n) :
    0 ≤ nonpreemptivePriorityMeanWork meanService state := by
  unfold nonpreemptivePriorityMeanWork priorityWaitingMeanWork
  have hwaiting : 0 ≤ ∑ i, meanService i * (state.waiting i : ℝ) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hmeanService i) (by positivity)
  cases state.active with
  | none => simpa using hwaiting
  | some i => exact add_nonneg (hmeanService i) hwaiting

/-- The strict-load allowance is positive whenever the finite class set is
nonempty and each class has a positive exponential service rate. -/
theorem classDependentNonpreemptivePriorityBusyAllowance_pos
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    0 < classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService := by
  unfold classDependentNonpreemptivePriorityBusyAllowance
  apply div_pos
  · linarith
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

/-- The quadratic finite-start potential is nonnegative. -/
theorem classDependentNonpreemptivePrioritySecondMomentPotential_nonneg
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (state : NonpreemptivePriorityState n) :
    0 ≤ classDependentNonpreemptivePrioritySecondMomentPotential
      arrivalRate meanService state := by
  let V := nonpreemptivePriorityMeanWork meanService state
  let B := classDependentNonpreemptivePriorityMeanWorkStepBound meanService
  let a := classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService
  have hV : 0 ≤ V := by
    exact nonpreemptivePriorityMeanWork_nonneg meanService
      (fun i => (hmeanService i).le) state
  have ha : 0 < a := by
    exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  have hcoefficient : 0 ≤ B ^ 2 / a := by
    exact div_nonneg (sq_nonneg B) ha.le
  change 0 ≤ V ^ 2 + (B ^ 2 / a) * V
  positivity

/-- Under strict offered load, the idle-stopped uniformized priority queue
has a quadratic Lyapunov descent that charges its current weighted mean work.
This is a finite-start statement; it supplies a workload-area bound for a
later regenerative construction but does not assert stationarity. -/
theorem classDependentNonpreemptivePriority_stopAtIdle_secondMoment_descent
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => classDependentNonpreemptivePrioritySecondMomentPotential
        arrivalRate meanService
        (stopAtIdleClassDependentNonpreemptivePriorityStep state event)) +
      classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state ≤
      classDependentNonpreemptivePrioritySecondMomentPotential
        arrivalRate meanService state := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let V := nonpreemptivePriorityMeanWork meanService
  let B := classDependentNonpreemptivePriorityMeanWorkStepBound meanService
  let a := classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService
  let R : ℝ := (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i
  have ha : 0 < a := by
    exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  have hR : 0 < R := by
    let i : Fin n := ⟨0, hn⟩
    have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hserviceSum : 0 < ∑ j, exponentialServiceRate meanService j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    exact add_pos_of_nonneg_of_pos harrivalSum hserviceSum
  by_cases hidle : state.active = none
  · simp [stopAtIdleClassDependentNonpreemptivePriorityStep,
      classDependentNonpreemptivePriorityMeanWorkBusyCost,
      classDependentNonpreemptivePrioritySecondMomentPotential, hidle]
  · rcases Option.ne_none_iff_exists'.mp hidle with ⟨active, hactive⟩
    have hquadratic :=
      pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sq_sub_le
        arrivalRate meanService hn harrivalRate hmeanService state
    have hlinear :=
      pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_eq_rateDrift_div
        arrivalRate meanService hn harrivalRate hmeanService state
    have hdrift := classDependentNonpreemptivePriorityMeanWorkRateDrift_of_active
      arrivalRate meanService state active hactive hmeanService
    have hnegDrift :
        ((∑ i, arrivalRate i * meanService i) - 1) / R = -a := by
      dsimp [a, R, classDependentNonpreemptivePriorityBusyAllowance]
      field_simp [ne_of_gt hR]
      ring
    have hquadratic' :
        pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event) ^ 2) -
          V state ^ 2 ≤ - (2 * a * V state) + B ^ 2 := by
      change pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event) ^ 2) -
          V state ^ 2 ≤ 2 * V state *
            (classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state /
              R) + B ^ 2 at hquadratic
      rw [hdrift] at hquadratic
      rw [hnegDrift] at hquadratic
      linarith
    have hlinear' :
        pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event)) -
          V state = -a := by
      change pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event)) -
          V state = classDependentNonpreemptivePriorityMeanWorkRateDrift
            arrivalRate meanService state / R at hlinear
      rw [hdrift] at hlinear
      rwa [hnegDrift] at hlinear
    have hcancel : (B ^ 2 / a) * (-a) = - B ^ 2 := by
      field_simp [ne_of_gt ha]
    rw [show stopAtIdleClassDependentNonpreemptivePriorityStep state =
        stepClassDependentNonpreemptivePriority state by
      funext event
      simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]]
    simp only [classDependentNonpreemptivePriorityMeanWorkBusyCost, if_neg hidle,
      classDependentNonpreemptivePrioritySecondMomentPotential]
    change pmfExp law (fun event =>
      V (stepClassDependentNonpreemptivePriority state event) ^ 2 +
        (B ^ 2 / a) * V (stepClassDependentNonpreemptivePriority state event)) +
        2 * a * V state ≤ V state ^ 2 + (B ^ 2 / a) * V state
    rw [pmfExp_add, pmfExp_const_mul]
    have hlinearMul : (B ^ 2 / a) *
        pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event)) =
        (B ^ 2 / a) * V state - B ^ 2 := by
      calc
        (B ^ 2 / a) *
            pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event)) =
            (B ^ 2 / a) *
              (pmfExp law (fun event => V
                (stepClassDependentNonpreemptivePriority state event)) - V state) +
              (B ^ 2 / a) * V state := by ring
        _ = (B ^ 2 / a) * V state - B ^ 2 := by
          rw [hlinear', hcancel]
          ring
    rw [hlinearMul]
    linarith [hquadratic']

/-- Every finite event horizon of a stable finite-start priority busy period
has bounded expected accumulated weighted work.  The bound is the quadratic
Lyapunov potential of its deterministic initial state. -/
theorem finiteEventExpectedCumulativeMeanWorkBusyCost_le_secondMomentPotential
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) (horizon : ℕ) :
    Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon ≤
      classDependentNonpreemptivePrioritySecondMomentPotential
        arrivalRate meanService initial := by
  apply Probability.finiteEventExpectedCumulativeCost_le_initialPotential
  · intro state
    exact classDependentNonpreemptivePrioritySecondMomentPotential_nonneg
      arrivalRate meanService hn harrivalRate hmeanService hstable state
  · exact classDependentNonpreemptivePriority_stopAtIdle_secondMoment_descent
      arrivalRate meanService hn harrivalRate hmeanService hstable

/-- The mean-work busy charge is nonnegative under positive service means and
strict offered load. -/
theorem classDependentNonpreemptivePriorityMeanWorkBusyCost_nonneg
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (state : NonpreemptivePriorityState n) :
    0 ≤ classDependentNonpreemptivePriorityMeanWorkBusyCost
      arrivalRate meanService state := by
  unfold classDependentNonpreemptivePriorityMeanWorkBusyCost
  split_ifs with hidle
  · exact le_rfl
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (classDependentNonpreemptivePriorityBusyAllowance_pos
          arrivalRate meanService hn harrivalRate hmeanService hstable).le)
      (nonpreemptivePriorityMeanWork_nonneg meanService
        (fun i => (hmeanService i).le) state)

/-- The expected mean-work charges along a finite-start stable busy period
form a summable sequence over uniformized event horizons.  This is stronger
than mere eventual idleness and is the workload-area estimate needed by a
regenerative stationary construction. -/
theorem summable_finiteEventTrajectoryMeanWorkBusyCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    Summable (fun horizon => pmfExp
      (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
      (fun sample => classDependentNonpreemptivePriorityMeanWorkBusyCost
        arrivalRate meanService
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))) := by
  apply summable_of_sum_range_le
  · intro horizon
    apply Finset.sum_nonneg
    intro sample _
    exact mul_nonneg ENNReal.toReal_nonneg
      (classDependentNonpreemptivePriorityMeanWorkBusyCost_nonneg
        arrivalRate meanService hn harrivalRate hmeanService hstable
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))
  · intro horizon
    simpa [Probability.finiteEventExpectedCumulativeCost] using
      (finiteEventExpectedCumulativeMeanWorkBusyCost_le_secondMomentPotential
        arrivalRate meanService hn harrivalRate hmeanService hstable initial horizon)

/-- Along an idle-consistent finite-start excursion, expected weighted work
itself is summable over uniformized event horizons.  This is the terminal
estimate required when a finite accounting identity is passed to the end of a
busy excursion. -/
theorem summable_finiteEventTrajectoryExpectedMeanWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial) :
    Summable (fun horizon => pmfExp
      (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
      (fun sample => nonpreemptivePriorityMeanWork meanService
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))) := by
  let scale : ℝ := 2 * classDependentNonpreemptivePriorityBusyAllowance
    arrivalRate meanService
  have hscalePos : 0 < scale := by
    dsimp [scale]
    exact mul_pos (by norm_num)
      (classDependentNonpreemptivePriorityBusyAllowance_pos
        arrivalRate meanService hn harrivalRate hmeanService hstable)
  have hcost := summable_finiteEventTrajectoryMeanWorkBusyCost
    arrivalRate meanService hn harrivalRate hmeanService hstable initial
  have hrewrite : ∀ horizon, pmfExp
      (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
      (fun sample => classDependentNonpreemptivePriorityMeanWorkBusyCost
        arrivalRate meanService
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) =
      scale * pmfExp
        (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => nonpreemptivePriorityMeanWork meanService
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) := by
    intro horizon
    rw [← pmfExp_const_mul]
    apply pmfExp_congr
    intro sample
    exact classDependentNonpreemptivePriorityMeanWorkBusyCost_eq_scale_mul_meanWork
      arrivalRate meanService
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)
      (nonpreemptivePriorityStateIdleConsistent_stopAtIdleTrajectory initial hinitial
        horizon sample)
  refine (hcost.div_const scale).congr ?_
  intro horizon
  rw [hrewrite horizon]
  field_simp [ne_of_gt hscalePos]

/-- Expected terminal population of each class is controlled by terminal
mean work along an idle-consistent finite-start excursion. -/
theorem finiteEventTrajectoryExpectedClassJobs_le_expectedMeanWork_div
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (i : Fin n) (horizon : ℕ) :
    pmfExp
      (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
      (fun sample =>
        (classNonpreemptivePriorityJobs
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i : ℝ)) ≤
      pmfExp
        (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => nonpreemptivePriorityMeanWork meanService
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) /
        meanService i := by
  apply (le_div_iff₀ (hmeanService i)).mpr
  rw [← pmfExp_mul_const]
  apply pmfExp_le_pmfExp_of_forall_le
  intro sample
  simpa [mul_comm] using
    (meanService_mul_classNonpreemptivePriorityJobs_le_meanWork meanService
      (fun j => (hmeanService j).le)
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i)

/-- In a stable idle-stopped priority excursion, the expected terminal number
of jobs of every class converges to zero.  This removes the terminal term in
the finite classwise flow accountant without assuming regeneration. -/
theorem tendsto_finiteEventTrajectoryExpectedClassJobs_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (i : Fin n) :
    Filter.Tendsto (fun horizon => pmfExp
      (pmfProduct (Fin horizon) (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
      (fun sample =>
        (classNonpreemptivePriorityJobs
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i : ℝ)))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro horizon
    apply pmfExp_nonneg_of_forall_nonneg
    intro sample
    positivity
  · intro horizon
    exact finiteEventTrajectoryExpectedClassJobs_le_expectedMeanWork_div
      arrivalRate meanService hn harrivalRate hmeanService initial hinitial i horizon
  · have hwork := summable_finiteEventTrajectoryExpectedMeanWork
      arrivalRate meanService hn harrivalRate hmeanService hstable initial hinitial
    simpa using hwork.tendsto_atTop_zero.div_const (meanService i)

/-- The exact finite classwise accountant has a justified terminal limit on a
stable idle-stopped excursion.  This is a regeneration-limit statement for
the finite excursion only; it does not identify a stationary queue law. -/
theorem tendsto_finiteEventExpectedCumulativeStoppedClassJobGeneratorCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (i : Fin n) :
    Filter.Tendsto (fun horizon => Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
        arrivalRate meanService i) horizon)
      atTop (nhds (classNonpreemptivePriorityJobs initial i : ℝ)) := by
  have hterminal := tendsto_finiteEventTrajectoryExpectedClassJobs_zero
    arrivalRate meanService hn harrivalRate hmeanService hstable initial hinitial i
  have hrewrite : ∀ horizon, Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
        arrivalRate meanService i) horizon =
      (classNonpreemptivePriorityJobs initial i : ℝ) -
        pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
          (fun sample =>
            (classNonpreemptivePriorityJobs
              (Probability.finiteEventTrajectory initial
                stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i : ℝ)) := by
    intro horizon
    have haccount := finiteEventExpectedCumulativeStoppedClassJobGeneratorCost_add_expectedClassJobs_eq
      arrivalRate meanService hn harrivalRate hmeanService initial i horizon
    linarith
  rw [show (fun horizon => Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedClassJobGeneratorCost
        arrivalRate meanService i) horizon) =
      (fun horizon => (classNonpreemptivePriorityJobs initial i : ℝ) -
        pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
          (fun sample =>
            (classNonpreemptivePriorityJobs
              (Probability.finiteEventTrajectory initial
                stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample) i : ℝ))) by
        funext horizon
        exact hrewrite horizon]
  simpa using tendsto_const_nhds.sub hterminal

/-- The continuous-time total of the finite-start mean-work Lyapunov charge:
the event-chain charge at each busy slot multiplied by that slot's independent
exponential holding time.  It is a finite-start regenerative observable and
does not assert a stationary workload law. -/
noncomputable def classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (initial : NonpreemptivePriorityState n) :
    ((ℕ → ClassDependentNonpreemptivePriorityEvent n) × (ℕ → ℝ)) → ENNReal :=
  Probability.IIDStream.externalScaledENNReward
    (fun horizon => Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon)
    ENNReal.ofReal

/-- The finite-start mean-work busy holding charge is Borel measurable. -/
theorem measurable_classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (initial : NonpreemptivePriorityState n) :
    Measurable (classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
      arrivalRate meanService initial) := by
  unfold classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
  exact Measurable.ennreal_tsum fun horizon =>
    Probability.IIDStream.measurable_externalScaledENNRewardSummand
      (fun horizon => Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
        initial stopAtIdleClassDependentNonpreemptivePriorityStep
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon)
      ENNReal.ofReal
      (fun horizon =>
        Probability.IIDStream.measurable_finiteEventTrajectoryNonnegativeReward
          initial stopAtIdleClassDependentNonpreemptivePriorityStep
          (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon)
      ENNReal.measurable_ofReal horizon

/-- Strict load gives finite expected physical-time mean-work charge during a
finite-start priority busy period.  This is the finite-start mean-work
Lyapunov-charge estimate needed before a later stationary or Palm construction
can be identified. -/
theorem lintegral_classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ z, classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
      arrivalRate meanService initial z ∂
      ((Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)))) ≠ ⊤ := by
  let rate : ℝ := (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let weight : ℕ → (ℕ → ClassDependentNonpreemptivePriorityEvent n) → ENNReal :=
    fun horizon => Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon
  have hrate : 0 < rate := by
    let i : Fin n := ⟨0, hn⟩
    have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hserviceSum : 0 < ∑ j, exponentialServiceRate meanService j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    exact add_pos_of_nonneg_of_pos harrivalSum hserviceSum
  letI : IsProbabilityMeasure M := by
    dsimp [M, Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hweight : ∀ horizon, Measurable (weight horizon) := by
    intro horizon
    exact Probability.IIDStream.measurable_finiteEventTrajectoryNonnegativeReward
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon
  have hweightFinite : ∑' horizon, ∫⁻ omega, weight horizon omega ∂M ≠ ⊤ := by
    simpa [M, law, weight] using
      (Probability.IIDStream.tsum_lintegral_finiteEventTrajectoryNonnegativeReward_ne_top
        law initial stopAtIdleClassDependentNonpreemptivePriorityStep
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService)
        (classDependentNonpreemptivePriorityMeanWorkBusyCost_nonneg
          arrivalRate meanService hn harrivalRate hmeanService hstable)
        (summable_finiteEventTrajectoryMeanWorkBusyCost
          arrivalRate meanService hn harrivalRate hmeanService hstable initial))
  have hgapNonnegative : ∀ᵐ x ∂μ, 0 ≤ x := by
    let exponentialModel : Probability.Exponential.Model := ⟨rate, hrate⟩
    simpa [μ, exponentialModel] using exponentialModel.ae_nonnegative
  have hgapLIntegral : ∫⁻ x, ENNReal.ofReal x ∂μ = ENNReal.ofReal (1 / rate) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Probability.integrable_id_expMeasure hrate) hgapNonnegative,
      Probability.integral_id_expMeasure hrate]
  have hgapFinite : ∫⁻ x, ENNReal.ofReal x ∂μ ≠ ⊤ := by
    rw [hgapLIntegral]
    exact ENNReal.ofReal_ne_top
  simpa [classDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge,
    M, μ, law, rate, weight] using
    (Probability.IIDStream.lintegral_externalScaledENNReward_ne_top
      M μ weight ENNReal.ofReal hweight ENNReal.measurable_ofReal
      hweightFinite hgapFinite)

/-- Stopping at idle turns the exact busy-state workload drift into a
one-step descent inequality with the corresponding busy-event charge. -/
theorem classDependentNonpreemptivePriority_stopAtIdle_descent
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (state : NonpreemptivePriorityState n) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => nonpreemptivePriorityMeanWork meanService
        (stopAtIdleClassDependentNonpreemptivePriorityStep state event)) +
      classDependentNonpreemptivePriorityBusyCost arrivalRate meanService state ≤
      nonpreemptivePriorityMeanWork meanService state := by
  by_cases hidle : state.active = none
  · simp [stopAtIdleClassDependentNonpreemptivePriorityStep,
      classDependentNonpreemptivePriorityBusyCost, hidle]
  · rcases Option.ne_none_iff_exists'.mp hidle with ⟨active, hactive⟩
    have hwork :=
      pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_eq_rateDrift_div
        arrivalRate meanService hn harrivalRate hmeanService state
    have hdrift := classDependentNonpreemptivePriorityMeanWorkRateDrift_of_active
      arrivalRate meanService state active hactive hmeanService
    have hden : 0 <
        (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i := by
      let i : Fin n := ⟨0, hn⟩
      have harrival_sum : 0 ≤ ∑ j, arrivalRate j :=
        Finset.sum_nonneg fun j _ => harrivalRate j
      have hservice_sum : 0 < ∑ j, exponentialServiceRate meanService j := by
        refine Finset.sum_pos' ?_ ?_
        · intro j _
          exact (exponentialServiceRate_pos meanService hmeanService j).le
        · exact ⟨i, Finset.mem_univ i,
            exponentialServiceRate_pos meanService hmeanService i⟩
      linarith
    rw [show stopAtIdleClassDependentNonpreemptivePriorityStep state =
        stepClassDependentNonpreemptivePriority state by
      funext event
      simp [stopAtIdleClassDependentNonpreemptivePriorityStep, hidle]]
    simp only [classDependentNonpreemptivePriorityBusyCost, if_neg hidle]
    rw [hdrift] at hwork
    have hcancel :
        ((∑ i, arrivalRate i * meanService i) - 1) /
            ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) +
          classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService = 0 := by
      unfold classDependentNonpreemptivePriorityBusyAllowance
      field_simp [ne_of_gt hden]
      ring
    linarith

/-- At every finite horizon, strict load bounds the expected cumulative
busy-event charge in the idle-stopped uniformized queue by the initial mean
work. -/
theorem finiteEventExpectedCumulativeBusyCost_le_meanWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) (horizon : ℕ) :
    Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityBusyCost arrivalRate meanService) horizon ≤
      nonpreemptivePriorityMeanWork meanService initial := by
  apply Probability.finiteEventExpectedCumulativeCost_le_initialPotential
  · intro state
    exact nonpreemptivePriorityMeanWork_nonneg meanService
      (fun i => (hmeanService i).le) state
  · exact classDependentNonpreemptivePriority_stopAtIdle_descent
      arrivalRate meanService hn harrivalRate hmeanService hstable

/-- The finite-product probabilities of remaining busy after successive
uniformized events are summable under strict load.  This is the quantitative
finite-event precursor to the stopped-IID and continuous-time renewal bridges. -/
theorem summable_finiteEventTrajectory_busyProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    Summable (Probability.finiteEventTrajectoryEventProbability
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      classDependentNonpreemptivePriorityBusy) := by
  apply Probability.summable_finiteEventTrajectoryEventProbability_of_drift
  · exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    exact nonpreemptivePriorityMeanWork_nonneg meanService
      (fun i => (hmeanService i).le) state
  · exact classDependentNonpreemptivePriority_stopAtIdle_descent
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    by_cases hidle : state.active = none
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]

/-- The terminal state of a stable idle-stopped excursion converges in
probability to the literal empty state.  This is the terminal boundary term
needed when the finite state-flow identity is passed to a full cycle. -/
theorem tendsto_finiteEventTrajectoryExpectedEmptyStateIndicator_one
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial) :
    Filter.Tendsto (fun horizon =>
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => classDependentNonpreemptivePriorityStateIndicator
          (emptyNonpreemptivePriorityState n)
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)))
      atTop (nhds 1) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  have hbusy := summable_finiteEventTrajectory_busyProbability
    arrivalRate meanService hn harrivalRate hmeanService hstable initial
  have hbusyZero : Filter.Tendsto (fun horizon =>
      Probability.finiteEventTrajectoryEventProbability law initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon)
      atTop (nhds 0) := hbusy.tendsto_atTop_zero
  have heq : ∀ horizon,
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n) law)
        (fun sample => classDependentNonpreemptivePriorityStateIndicator
          (emptyNonpreemptivePriorityState n)
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) =
      1 - Probability.finiteEventTrajectoryEventProbability law initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon := by
    intro horizon
    calc
      pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n) law)
          (fun sample => classDependentNonpreemptivePriorityStateIndicator
            (emptyNonpreemptivePriorityState n)
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) =
        pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n) law)
          (fun sample => 1 - if classDependentNonpreemptivePriorityBusy
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)
            then 1 else 0) := by
          apply pmfExp_congr
          intro sample
          let state := Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
          by_cases hbusyState : classDependentNonpreemptivePriorityBusy state
          · have hne : state ≠ emptyNonpreemptivePriorityState n := by
              intro heq
              apply hbusyState
              simp [state, heq]
            simp [classDependentNonpreemptivePriorityStateIndicator, state,
              hne, hbusyState]
          · have hidle : state.active = none := by
              simpa [classDependentNonpreemptivePriorityBusy] using hbusyState
            have hempty := finiteEventTrajectory_stopAtIdle_eq_empty_of_active_eq_none
              initial hinitial horizon sample hidle
            simp [classDependentNonpreemptivePriorityStateIndicator, hempty,
              classDependentNonpreemptivePriorityBusy,
              emptyNonpreemptivePriorityState_active]
      _ = 1 - pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n) law)
          (fun sample => if classDependentNonpreemptivePriorityBusy
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)
            then 1 else 0) := by
          rw [pmfExp_sub, pmfExp_const]
      _ = 1 - Probability.finiteEventTrajectoryEventProbability law initial
          stopAtIdleClassDependentNonpreemptivePriorityStep
          classDependentNonpreemptivePriorityBusy horizon := by
          rfl
  rw [show (fun horizon =>
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n) law)
        (fun sample => classDependentNonpreemptivePriorityStateIndicator
          (emptyNonpreemptivePriorityState n)
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))) =
      (fun horizon => 1 - Probability.finiteEventTrajectoryEventProbability law initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon) by
        funext horizon
        exact heq horizon]
  simpa using tendsto_const_nhds.sub hbusyZero

/-- Every fixed nonempty embedded state has vanishing terminal probability in
a stable idle-stopped excursion.  Together with the empty-state limit, this
supplies all terminal coordinates needed for statewise regenerative flow. -/
theorem tendsto_finiteEventTrajectoryExpectedStateIndicator_zero_of_ne_empty
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial target : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial)
    (htarget : target ≠ emptyNonpreemptivePriorityState n) :
    Filter.Tendsto (fun horizon =>
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => classDependentNonpreemptivePriorityStateIndicator target
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)))
      atTop (nhds 0) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  have hbusy := summable_finiteEventTrajectory_busyProbability
    arrivalRate meanService hn harrivalRate hmeanService hstable initial
  have hbusyZero : Filter.Tendsto (fun horizon =>
      Probability.finiteEventTrajectoryEventProbability law initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon)
      atTop (nhds 0) := hbusy.tendsto_atTop_zero
  apply squeeze_zero (g := fun horizon =>
    Probability.finiteEventTrajectoryEventProbability law initial
      stopAtIdleClassDependentNonpreemptivePriorityStep
      classDependentNonpreemptivePriorityBusy horizon)
  · intro horizon
    apply pmfExp_nonneg_of_forall_nonneg
    intro sample
    unfold classDependentNonpreemptivePriorityStateIndicator
    split <;> norm_num
  · intro horizon
    change pmfExp (pmfProduct (Fin horizon)
      (ClassDependentNonpreemptivePriorityEvent n) law)
      (fun sample => classDependentNonpreemptivePriorityStateIndicator target
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) ≤
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n) law)
        (fun sample => if classDependentNonpreemptivePriorityBusy
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)
          then 1 else 0)
    apply pmfExp_le_pmfExp_of_forall_le
    intro sample
    let state := Probability.finiteEventTrajectory initial
      stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
    by_cases hbusyState : classDependentNonpreemptivePriorityBusy state
    · unfold classDependentNonpreemptivePriorityStateIndicator
      split <;> simp
    · have hidle : state.active = none := by
        simpa [classDependentNonpreemptivePriorityBusy] using hbusyState
      have hempty := finiteEventTrajectory_stopAtIdle_eq_empty_of_active_eq_none
        initial hinitial horizon sample hidle
      simp [classDependentNonpreemptivePriorityStateIndicator, hempty,
        Ne.symm htarget, classDependentNonpreemptivePriorityBusy,
        emptyNonpreemptivePriorityState_active]
  · change Filter.Tendsto (fun horizon =>
      Probability.finiteEventTrajectoryEventProbability law initial
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon) atTop (nhds 0)
    exact hbusyZero

/-- The cumulative state-flow into the empty regeneration state has its exact
stable-excursion limit.  This is a signed finite-cycle balance, obtained from
the literal finite telescoping identity and the proved terminal empty-state
limit. -/
theorem tendsto_finiteEventExpectedCumulativeStoppedEmptyStateFlowCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial) :
    Filter.Tendsto (fun horizon => Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService
        (emptyNonpreemptivePriorityState n)) horizon)
      atTop (nhds (classDependentNonpreemptivePriorityStateIndicator
        (emptyNonpreemptivePriorityState n) initial - 1)) := by
  have hterminal := tendsto_finiteEventTrajectoryExpectedEmptyStateIndicator_one
    arrivalRate meanService hn harrivalRate hmeanService hstable initial hinitial
  have hrewrite : ∀ horizon, Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService
        (emptyNonpreemptivePriorityState n)) horizon =
      classDependentNonpreemptivePriorityStateIndicator
        (emptyNonpreemptivePriorityState n) initial -
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample => classDependentNonpreemptivePriorityStateIndicator
          (emptyNonpreemptivePriorityState n)
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) := by
    intro horizon
    have hflow := finiteEventExpectedCumulativeStoppedStateFlowCost_add_expectedStateIndicator_eq
      arrivalRate meanService hn harrivalRate hmeanService initial
      (emptyNonpreemptivePriorityState n) horizon
    linarith
  rw [show (fun horizon => Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService
        (emptyNonpreemptivePriorityState n)) horizon) =
      (fun horizon => classDependentNonpreemptivePriorityStateIndicator
        (emptyNonpreemptivePriorityState n) initial -
        pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
          (fun sample => classDependentNonpreemptivePriorityStateIndicator
            (emptyNonpreemptivePriorityState n)
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))) by
        funext horizon
        exact hrewrite horizon]
  simpa using tendsto_const_nhds.sub hterminal

/-- The complete stable-excursion limit of the statewise stopped flow
accountant.  The limit is the initial point mass minus the terminal point mass
at the literal empty regeneration state. -/
theorem tendsto_finiteEventExpectedCumulativeStoppedStateFlowCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial target : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial) :
    Filter.Tendsto (fun horizon => Probability.finiteEventExpectedCumulativeCost
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityStoppedStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService target) horizon)
      atTop (nhds (classDependentNonpreemptivePriorityStateIndicator target initial -
        classDependentNonpreemptivePriorityStateIndicator target
          (emptyNonpreemptivePriorityState n))) := by
  by_cases htarget : target = emptyNonpreemptivePriorityState n
  · subst target
    simpa [classDependentNonpreemptivePriorityStateIndicator] using
      (tendsto_finiteEventExpectedCumulativeStoppedEmptyStateFlowCost
        arrivalRate meanService hn harrivalRate hmeanService hstable initial hinitial)
  · have hterminal :=
      tendsto_finiteEventTrajectoryExpectedStateIndicator_zero_of_ne_empty
        arrivalRate meanService hn harrivalRate hmeanService hstable initial target
        hinitial htarget
    have hrewrite : ∀ horizon, Probability.finiteEventExpectedCumulativeCost
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))
        initial stopAtIdleClassDependentNonpreemptivePriorityStep
        (classDependentNonpreemptivePriorityStoppedStateFlowCost
          arrivalRate meanService hn harrivalRate hmeanService target) horizon =
        classDependentNonpreemptivePriorityStateIndicator target initial -
        pmfExp (pmfProduct (Fin horizon)
          (ClassDependentNonpreemptivePriorityEvent n)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)))
          (fun sample => classDependentNonpreemptivePriorityStateIndicator target
            (Probability.finiteEventTrajectory initial
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample)) := by
      intro horizon
      have hflow := finiteEventExpectedCumulativeStoppedStateFlowCost_add_expectedStateIndicator_eq
        arrivalRate meanService hn harrivalRate hmeanService initial target horizon
      linarith
    rw [show (fun horizon => Probability.finiteEventExpectedCumulativeCost
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))
        initial stopAtIdleClassDependentNonpreemptivePriorityStep
        (classDependentNonpreemptivePriorityStoppedStateFlowCost
          arrivalRate meanService hn harrivalRate hmeanService target) horizon) =
        (fun horizon => classDependentNonpreemptivePriorityStateIndicator target initial -
          pmfExp (pmfProduct (Fin horizon)
            (ClassDependentNonpreemptivePriorityEvent n)
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService)))
            (fun sample => classDependentNonpreemptivePriorityStateIndicator target
              (Probability.finiteEventTrajectory initial
                stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))) by
          funext horizon
          exact hrewrite horizon]
    have hlimit := (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => classDependentNonpreemptivePriorityStateIndicator target initial)
      atTop (nhds (classDependentNonpreemptivePriorityStateIndicator target initial))).sub
        hterminal
    simpa [classDependentNonpreemptivePriorityStateIndicator, htarget,
      Ne.symm htarget] using hlimit

/-- The strict-load Lyapunov drift bounds the expected total number of busy
uniformization slots by initial mean work divided by the busy-state allowance. -/
theorem tsum_finiteEventTrajectory_busyProbability_le_meanWork_div_allowance
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∑' horizon, Probability.finiteEventTrajectoryEventProbability
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      initial stopAtIdleClassDependentNonpreemptivePriorityStep
      classDependentNonpreemptivePriorityBusy horizon ≤
        nonpreemptivePriorityMeanWork meanService initial /
          classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService := by
  apply Probability.tsum_finiteEventTrajectoryEventProbability_le_initialPotential_div_charge
  · exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    exact nonpreemptivePriorityMeanWork_nonneg meanService
      (fun i => (hmeanService i).le) state
  · exact classDependentNonpreemptivePriority_stopAtIdle_descent
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    by_cases hidle : state.active = none
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]

/-- On the literal canonical IID event stream, the probabilities that the
idle-stopped uniformized queue remains busy form a summable sequence. -/
theorem summable_measureReal_iidEventStream_busy
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    Summable (fun horizon =>
      (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure).real
        {omega | classDependentNonpreemptivePriorityBusy
          (Probability.finiteEventTrajectory initial
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon
            (Probability.IIDStream.block 0 horizon omega))}) := by
  apply (summable_finiteEventTrajectory_busyProbability
    arrivalRate meanService hn harrivalRate hmeanService hstable initial).congr
  intro horizon
  exact (Probability.IIDStream.measureReal_finiteEventTrajectoryEvent_eq
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy horizon).symm

/-- The number of busy uniformization slots before the idle-stopped queue
regenerates.  This is defined on the literal IID event stream and does not
presuppose a stationary queue law. -/
noncomputable def classDependentNonpreemptivePriorityBusyEventCount
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    (ℕ → ClassDependentNonpreemptivePriorityEvent n) → ENNReal :=
  Probability.IIDStream.finiteEventTrajectoryEventCount initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy

/-- A busy excursion started from an active queue has at least its initial
uniformized occupied slot on every event path.  This supplies the positivity
needed when its physical-time occupation is normalized. -/
theorem one_le_classDependentNonpreemptivePriorityBusyEventCount_of_active
    {n : ℕ} (initial : NonpreemptivePriorityState n)
    (hactive : initial.active ≠ none)
    (omega : ℕ → ClassDependentNonpreemptivePriorityEvent n) :
    1 ≤ classDependentNonpreemptivePriorityBusyEventCount initial omega := by
  exact Probability.IIDStream.one_le_finiteEventTrajectoryEventCount_of_initial
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy hactive omega

/-- If every state in an independently sampled initial family is active, its
expected busy-event count is at least one.  This is the positive-normalizer
half of the regenerative occupation construction; the companion drift bounds
provide the finite-normalizer half under strict load. -/
theorem one_le_lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_of_active
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (initial : σ → NonpreemptivePriorityState n)
    (hactive : ∀ x, (initial x).active ≠ none) :
    1 ≤ ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
        (ρ.prod (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure)) := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  letI : IsProbabilityMeasure M := by
    dsimp [M, law, Probability.IIDStream.measure]
    infer_instance
  change 1 ≤ ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
    classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂(ρ.prod M)
  calc
    1 = ∫⁻ _ : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        (1 : ENNReal) ∂(ρ.prod M) := by simp
    _ ≤ ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
          (ρ.prod M) := by
        apply MeasureTheory.lintegral_mono
        intro z
        exact one_le_classDependentNonpreemptivePriorityBusyEventCount_of_active
          (initial z.1) (hactive z.1) z.2

/-- The busy-slot count is Borel on the literal uniformized event stream. -/
theorem measurable_classDependentNonpreemptivePriorityBusyEventCount
    {n : ℕ} (initial : NonpreemptivePriorityState n) :
    Measurable (classDependentNonpreemptivePriorityBusyEventCount initial) := by
  exact Probability.IIDStream.measurable_finiteEventTrajectoryEventCount initial
    stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy

/-- Strict load gives a finite expected number of busy uniformization slots.
This is the event-count form of the regenerative busy-period estimate. -/
theorem lintegral_classDependentNonpreemptivePriorityBusyEventCount_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ omega, classDependentNonpreemptivePriorityBusyEventCount initial omega ∂
      Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure ≠ ⊤ := by
  classical
  exact Probability.IIDStream.lintegral_finiteEventTrajectoryEventCount_ne_top
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy
    (summable_finiteEventTrajectory_busyProbability
      arrivalRate meanService hn harrivalRate hmeanService hstable initial)

/-- Quantitatively, the expected busy-slot count is bounded by initial mean
work divided by the strict-load allowance. -/
theorem lintegral_classDependentNonpreemptivePriorityBusyEventCount_le_meanWork_div_allowance
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ omega, classDependentNonpreemptivePriorityBusyEventCount initial omega ∂
      Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure ≤
        ENNReal.ofReal
          (nonpreemptivePriorityMeanWork meanService initial /
            classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) := by
  classical
  apply Probability.IIDStream.lintegral_finiteEventTrajectoryEventCount_le_of_tsum_bound
  · exact summable_finiteEventTrajectory_busyProbability
      arrivalRate meanService hn harrivalRate hmeanService hstable initial
  · exact tsum_finiteEventTrajectory_busyProbability_le_meanWork_div_allowance
      arrivalRate meanService hn harrivalRate hmeanService hstable initial

/-- The busy-event count bound also applies to an independent random initial
queue state when the concrete product-carrier count is measurable.  This is
the finite-start form needed before a stationary construction can be coupled
to the uniformized event chain. -/
theorem lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_le
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : σ → NonpreemptivePriorityState n)
    (hcount : Measurable (fun z : σ ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2)) :
    ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
          (ρ.prod (Probability.IIDStream.measure
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService)).toMeasure)) ≤
      ∫⁻ x, ENNReal.ofReal
        (nonpreemptivePriorityMeanWork meanService (initial x) /
          classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂ρ := by
  classical
  apply Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryEventCount_le
  · exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    exact nonpreemptivePriorityMeanWork_nonneg meanService
      (fun i => (hmeanService i).le) state
  · exact classDependentNonpreemptivePriority_stopAtIdle_descent
      arrivalRate meanService hn harrivalRate hmeanService hstable
  · intro state
    by_cases hidle : state.active = none
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]
    · simp [classDependentNonpreemptivePriorityBusyCost,
        classDependentNonpreemptivePriorityBusy, hidle]
  · simpa [classDependentNonpreemptivePriorityBusyEventCount] using hcount

/-- A random initial state with finite expected weighted work has a finite
expected number of busy uniformization slots.  This is the exact quantitative
input needed to transfer a stationary queue state into the finite-start
regenerative estimate; it does not assert such an integrability fact for any
particular stationary construction. -/
theorem lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_ne_top
    {σ : Type*} [MeasurableSpace σ]
    (ρ : Measure σ) [IsProbabilityMeasure ρ]
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : σ → NonpreemptivePriorityState n)
    (hcount : Measurable (fun z : σ ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2))
    (hinitial : ∫⁻ x, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService (initial x) /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂ρ ≠ ⊤) :
    ∫⁻ z : σ × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2 ∂
          (ρ.prod (Probability.IIDStream.measure
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService)).toMeasure)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hinitial
  exact lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_le
    ρ arrivalRate meanService hn harrivalRate hmeanService hstable initial hcount

/-- The total number of busy uniformization slots is finite almost surely
under strict load. -/
theorem ae_classDependentNonpreemptivePriorityBusyEventCount_lt_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∀ᵐ omega ∂Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure,
      classDependentNonpreemptivePriorityBusyEventCount initial omega < ⊤ := by
  classical
  exact Probability.IIDStream.ae_finiteEventTrajectoryEventCount_lt_top
    (classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService))
    initial stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy
    (summable_finiteEventTrajectory_busyProbability
      arrivalRate meanService hn harrivalRate hmeanService hstable initial)

/-- Under strict load, independently attaching exponential holding times at
the total uniformization rate gives a finite expected total busy holding time.
This is the quantitative continuous-time part of the regenerative
construction; identifying the labelled clock construction with a particular
stationary Palm input remains a separate source-model bridge. -/
theorem lintegral_classDependentNonpreemptivePriorityBusyHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∫⁻ z, classDependentNonpreemptivePriorityBusyHoldingTime initial z ∂
      ((Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)))) ≠ ⊤ := by
  classical
  let rate : ℝ := (∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  have hrate : 0 < rate := by
    let i : Fin n := ⟨0, hn⟩
    have harrival_sum : 0 ≤ ∑ j, arrivalRate j :=
      Finset.sum_nonneg fun j _ => harrivalRate j
    have hservice_sum : 0 < ∑ j, exponentialServiceRate meanService j := by
      refine Finset.sum_pos' ?_ ?_
      · intro j _
        exact (exponentialServiceRate_pos meanService hmeanService j).le
      · exact ⟨i, Finset.mem_univ i,
          exponentialServiceRate_pos meanService hmeanService i⟩
    exact add_pos_of_nonneg_of_pos harrival_sum hservice_sum
  letI : IsProbabilityMeasure M := by
    dsimp [M, Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hbusy_meas : ∀ horizon,
      MeasurableSet (classDependentNonpreemptivePriorityBusyEvent initial horizon) := by
    intro horizon
    exact measurableSet_classDependentNonpreemptivePriorityBusyEvent initial horizon
  have hbusy_sum : Summable fun horizon =>
      M.real (classDependentNonpreemptivePriorityBusyEvent initial horizon) := by
    simpa [M, law, classDependentNonpreemptivePriorityBusyEvent] using
      (summable_measureReal_iidEventStream_busy
        arrivalRate meanService hn harrivalRate hmeanService hstable initial)
  have hgap_nonnegative : ∀ᵐ x ∂μ, 0 ≤ x := by
    let exponentialModel : Probability.Exponential.Model := ⟨rate, hrate⟩
    simpa [μ, exponentialModel] using exponentialModel.ae_nonnegative
  have hgap_lintegral : ∫⁻ x, ENNReal.ofReal x ∂μ =
      ENNReal.ofReal (1 / rate) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Probability.integrable_id_expMeasure hrate) hgap_nonnegative,
      Probability.integral_id_expMeasure hrate]
  have hgap_finite : ∫⁻ x, ENNReal.ofReal x ∂μ ≠ ⊤ := by
    rw [hgap_lintegral]
    exact ENNReal.ofReal_ne_top
  simpa [classDependentNonpreemptivePriorityBusyHoldingTime, M, μ, law, rate] using
    (Probability.IIDStream.lintegral_externalWeightedENNReward_ne_top
      M μ (classDependentNonpreemptivePriorityBusyEvent initial) ENNReal.ofReal
      hbusy_meas ENNReal.measurable_ofReal hbusy_sum hgap_finite)

/-- The total physical busy holding time in the independent uniformized
construction is finite almost surely under strict load. -/
theorem ae_classDependentNonpreemptivePriorityBusyHoldingTime_lt_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∀ᵐ z ∂
      ((Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)).toMeasure).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)))),
      classDependentNonpreemptivePriorityBusyHoldingTime initial z < ⊤ := by
  apply MeasureTheory.ae_lt_top
  · exact measurable_classDependentNonpreemptivePriorityBusyHoldingTime initial
  · exact lintegral_classDependentNonpreemptivePriorityBusyHoldingTime_ne_top
      arrivalRate meanService hn harrivalRate hmeanService hstable initial

/-- Under strict load, the literal IID uniformized event stream reaches the
idle state almost surely.  The statement follows from the summable busy-event
tail by the first Borel--Cantelli lemma; it is a regeneration fact, not a
stationary-distribution assertion. -/
theorem ae_eventually_idle_iidEventStream
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n) :
    ∀ᵐ omega ∂Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure,
      ∀ᶠ horizon in Filter.atTop,
        (Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon
          (Probability.IIDStream.block 0 horizon omega)).active = none := by
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let busyEvent : ℕ → Set (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    fun horizon => {omega | classDependentNonpreemptivePriorityBusy
      (Probability.finiteEventTrajectory initial
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon
        (Probability.IIDStream.block 0 horizon omega))}
  letI : IsProbabilityMeasure M := by
    dsimp [M, Probability.IIDStream.measure]
    infer_instance
  have hreal : Summable (fun horizon => M.real (busyEvent horizon)) := by
    simpa [M, busyEvent, law] using
      (summable_measureReal_iidEventStream_busy
        arrivalRate meanService hn harrivalRate hmeanService hstable initial)
  have hterm : ∀ horizon, ENNReal.ofReal (M.real (busyEvent horizon)) =
      M (busyEvent horizon) := by
    intro horizon
    exact ENNReal.ofReal_toReal (measure_ne_top M (busyEvent horizon))
  have hmeasure : (∑' horizon, M (busyEvent horizon)) ≠ ⊤ := by
    rw [← tsum_congr hterm]
    exact hreal.tsum_ofReal_ne_top
  have heventual : ∀ᵐ omega ∂M, ∀ᶠ horizon in Filter.atTop,
      omega ∉ busyEvent horizon :=
    MeasureTheory.ae_eventually_notMem hmeasure
  simpa [M, busyEvent, classDependentNonpreemptivePriorityBusy] using heventual

/-- The stable idle-stopped event chain eventually reaches the literal empty
state almost surely, provided its initial record is idle-consistent.  This
upgrades the busy-tail statement from a vacant-service coordinate to the
actual regeneration state needed by a full empty-to-empty cycle. -/
theorem ae_eventually_eq_empty_iidEventStream
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (initial : NonpreemptivePriorityState n)
    (hinitial : nonpreemptivePriorityStateIdleConsistent initial) :
    ∀ᵐ omega ∂Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure,
      ∀ᶠ horizon in Filter.atTop,
        Probability.finiteEventTrajectory initial
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon
          (Probability.IIDStream.block 0 horizon omega) =
          emptyNonpreemptivePriorityState n := by
  filter_upwards [ae_eventually_idle_iidEventStream arrivalRate meanService hn
    harrivalRate hmeanService hstable initial] with omega homega
  filter_upwards [homega] with horizon hidle
  exact finiteEventTrajectory_stopAtIdle_eq_empty_of_active_eq_none initial hinitial
    horizon (Probability.IIDStream.block 0 horizon omega) hidle

end

end AppliedModelingLib.Queueing
