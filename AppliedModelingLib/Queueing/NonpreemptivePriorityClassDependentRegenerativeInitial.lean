import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentPhysicalBusyPeriod
import AppliedModelingLib.Foundations.Probability.FiniteEventIIDBridge

/-!
# Arrival-start distributions for regenerative priority-queue excursions

This module packages the natural initial law of a busy excursion: choose a
class proportionally to its arrival rate and admit that one job to an empty
embedded priority queue.  It is a finite-law construction only.  A later
regenerative occupation argument must prove the invariant measure assembled
from such excursions; no stationary law is asserted here.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The class of the first arrival after an idle epoch, sampled in proportion
to the finite vector of class arrival rates. -/
noncomputable def classDependentNonpreemptivePriorityArrivalClassPMF
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) : PMF (Fin n) :=
  finiteWeightedPMF arrivalRate harrivalRate htotalArrival

/-- The embedded queue state immediately after the first arrival of a fresh
busy excursion. -/
def classDependentNonpreemptivePriorityArrivalInitialState
    {n : ℕ} (i : Fin n) : NonpreemptivePriorityState n :=
  arriveNonpreemptivePriority (emptyNonpreemptivePriorityState n) i

/-- A fresh excursion starts with the first admitted job in service, hence is
active before its first uniformized event. -/
theorem classDependentNonpreemptivePriorityArrivalInitialState_active
    {n : ℕ} (i : Fin n) :
    (classDependentNonpreemptivePriorityArrivalInitialState i).active ≠ none := by
  simp [classDependentNonpreemptivePriorityArrivalInitialState,
    arriveNonpreemptivePriority_empty]

/-- A fresh arrival state is idle-consistent: if a later stopped trajectory
becomes idle, it has reached the literal empty regeneration state. -/
theorem classDependentNonpreemptivePriorityArrivalInitialState_idleConsistent
    {n : ℕ} (i : Fin n) :
    nonpreemptivePriorityStateIdleConsistent
      (classDependentNonpreemptivePriorityArrivalInitialState i) := by
  exact nonpreemptivePriorityStateIdleConsistent_arrive
    (emptyNonpreemptivePriorityState n) i

/-- A stable fresh busy excursion reaches the literal empty queue state almost
surely.  This is the pathwise regeneration statement underlying the
arrival-start occupation construction; it does not yet identify that
construction with a stationary Palm queue. -/
theorem ae_eventually_arrivalInitialClassDependentNonpreemptivePriority_eq_empty
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∀ᵐ omega ∂Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure,
      ∀ᶠ horizon in Filter.atTop,
        Probability.finiteEventTrajectory
          (classDependentNonpreemptivePriorityArrivalInitialState i)
          stopAtIdleClassDependentNonpreemptivePriorityStep horizon
          (Probability.IIDStream.block 0 horizon omega) =
          emptyNonpreemptivePriorityState n := by
  exact ae_eventually_eq_empty_iidEventStream arrivalRate meanService hn
    harrivalRate hmeanService hstable
    (classDependentNonpreemptivePriorityArrivalInitialState i)
    (classDependentNonpreemptivePriorityArrivalInitialState_idleConsistent i)

/-- Pushing the arrival-class law through immediate admission gives the
finite distribution of a fresh busy excursion's initial state. -/
noncomputable def classDependentNonpreemptivePriorityArrivalInitialStatePMF
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    PMF (NonpreemptivePriorityState n) :=
  (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).map
      classDependentNonpreemptivePriorityArrivalInitialState

/-- The one-step law from an empty uniformized queue is the exact mixture of
the arrival-start law and the idle self-loop.  This identifies the boundary
term of a regeneration cycle directly from the queue's actual event rates. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_empty_eq_arrivalInitial_mixture
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (observable : NonpreemptivePriorityState n → ℝ) :
    pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => observable
        (stepClassDependentNonpreemptivePriority (emptyNonpreemptivePriorityState n) event)) =
      ((∑ i, arrivalRate i) /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)) *
        pmfExp
          (classDependentNonpreemptivePriorityArrivalClassPMF
            arrivalRate harrivalRate htotalArrival)
          (fun i => observable (classDependentNonpreemptivePriorityArrivalInitialState i)) +
      ((∑ i, exponentialServiceRate meanService i) /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)) *
        observable (emptyNonpreemptivePriorityState n) := by
  let L : ℝ := ∑ i, arrivalRate i
  let S : ℝ := ∑ i, exponentialServiceRate meanService i
  let R : ℝ := L + S
  let A : ℝ := ∑ i, arrivalRate i *
    observable (classDependentNonpreemptivePriorityArrivalInitialState i)
  have hL : 0 < L := by simpa [L] using htotalArrival
  have hS : 0 < S := by
    let i : Fin n := ⟨0, hn⟩
    refine Finset.sum_pos' ?_ ?_
    · intro j _
      exact (exponentialServiceRate_pos meanService hmeanService j).le
    · exact ⟨i, Finset.mem_univ i,
        exponentialServiceRate_pos meanService hmeanService i⟩
  have hR : 0 < R := add_pos hL hS
  have harrival :
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun i => observable (classDependentNonpreemptivePriorityArrivalInitialState i)) =
        A / L := by
    change pmfExp (finiteWeightedPMF arrivalRate harrivalRate htotalArrival) _ = _
    rw [finiteWeightedPMF_pmfExp_eq_sum_div]
    change (∑ i, (arrivalRate i / ∑ j, arrivalRate j) *
      observable (classDependentNonpreemptivePriorityArrivalInitialState i)) = _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
    simp [L]
    ring
  rw [pmfExp_classDependentNonpreemptivePriorityEvent_empty
    arrivalRate (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService) observable,
    harrival]
  change (A + S * observable (emptyNonpreemptivePriorityState n)) / R =
    L / R * (A / L) + S / R * observable (emptyNonpreemptivePriorityState n)
  field_simp [ne_of_gt hL, ne_of_gt hR]

/-- Empty embedded queues have zero mean service work. -/
theorem nonpreemptivePriorityMeanWork_empty
    {n : ℕ} (meanService : Fin n → ℝ) :
    nonpreemptivePriorityMeanWork meanService (emptyNonpreemptivePriorityState n) = 0 := by
  simp [nonpreemptivePriorityMeanWork, priorityWaitingMeanWork,
    emptyNonpreemptivePriorityState]

/-- A fresh excursion begun by a class-`i` arrival has exactly that class's
mean service work. -/
theorem nonpreemptivePriorityMeanWork_arrivalInitialState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) :
    nonpreemptivePriorityMeanWork meanService
      (classDependentNonpreemptivePriorityArrivalInitialState i) = meanService i := by
  unfold classDependentNonpreemptivePriorityArrivalInitialState
  rw [nonpreemptivePriorityMeanWork_arrive,
    nonpreemptivePriorityMeanWork_empty]
  ring

/-- Under the arrival-rate initial mixture, the fresh excursion starts with
one class-`i` job with probability equal to that class's share of the total
arrival rate.  This is the boundary term in the classwise regenerative flow
accountant. -/
theorem pmfExp_classDependentNonpreemptivePriorityArrivalInitialState_classJobs
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) (i : Fin n) :
    pmfExp
      (classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival)
      (fun initialClass =>
        (classNonpreemptivePriorityJobs
          (classDependentNonpreemptivePriorityArrivalInitialState initialClass) i : ℝ)) =
      arrivalRate i / ∑ j, arrivalRate j := by
  change pmfExp (finiteWeightedPMF arrivalRate harrivalRate htotalArrival) _ = _
  rw [finiteWeightedPMF_pmfExp_eq_sum_div]
  have hpopulation : ∀ initialClass : Fin n,
      (classNonpreemptivePriorityJobs
        (classDependentNonpreemptivePriorityArrivalInitialState initialClass) i : ℝ) =
        if i = initialClass then 1 else 0 := by
    intro initialClass
    unfold classDependentNonpreemptivePriorityArrivalInitialState
    rw [classNonpreemptivePriorityJobs_arrive]
    simp [classNonpreemptivePriorityJobs,
      emptyNonpreemptivePriorityState_active,
      emptyNonpreemptivePriorityState_waiting]
  simp_rw [hpopulation]
  rw [Finset.sum_eq_single i]
  · simp
  · intro initialClass _ hne
    have hne' : i ≠ initialClass := Ne.symm hne
    simp [hne']
  · simp

/-- The mean-work observable of a fresh excursion's initial class is
integrable under its finite arrival-class law. -/
theorem integrable_nonpreemptivePriorityMeanWork_arrivalInitialState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Integrable (fun i => nonpreemptivePriorityMeanWork meanService
      (classDependentNonpreemptivePriorityArrivalInitialState i))
      (classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure := by
  exact Integrable.of_finite

/-- The busy-event count is Borel when a fresh excursion's class is sampled
from the finite arrival-class carrier independently of the IID event stream. -/
theorem measurable_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount
    {n : ℕ} :
    Measurable (fun z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount
        (classDependentNonpreemptivePriorityArrivalInitialState z.1) z.2) := by
  exact Probability.IIDStream.measurable_externalInitial_finiteEventTrajectoryEventCount_of_finite
    classDependentNonpreemptivePriorityArrivalInitialState
    stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy

/-- Each fixed horizon of a fresh finite-class busy excursion is a Borel
event on its class-and-IID-event product carrier. -/
theorem measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
    {n : ℕ} (horizon : ℕ) :
    MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent
        (σ := Fin n) (n := n)
        classDependentNonpreemptivePriorityArrivalInitialState horizon) := by
  exact Probability.IIDStream.measurableSet_externalInitialFiniteEventTrajectoryEventSet_of_finite
    classDependentNonpreemptivePriorityArrivalInitialState
    stopAtIdleClassDependentNonpreemptivePriorityStep
    classDependentNonpreemptivePriorityBusy horizon

/-- The arrival-class mixture has finite expected initial mean work after
division by the positive strict-load allowance. -/
theorem lintegral_arrivalInitial_meanWork_div_busyAllowance_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ i, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService
        (classDependentNonpreemptivePriorityArrivalInitialState i) /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂
      (classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure ≠ ⊤ := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let allowance := classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService
  let f : Fin n → ℝ := fun i =>
    nonpreemptivePriorityMeanWork meanService
      (classDependentNonpreemptivePriorityArrivalInitialState i) / allowance
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hallowance : 0 < allowance := by
    exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  have hnonnegative : 0 ≤ᶠ[ae ρ] f := Filter.Eventually.of_forall fun i => by
    dsimp [f]
    rw [nonpreemptivePriorityMeanWork_arrivalInitialState]
    exact div_nonneg (hmeanService i).le hallowance.le
  have hintegrable : Integrable f ρ := Integrable.of_finite
  change ∫⁻ i, ENNReal.ofReal (f i) ∂ρ ≠ ⊤
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegrable hnonnegative]
  exact ENNReal.ofReal_ne_top

/-- Strict load gives a finite expected number of busy uniformization slots
for the actual first-arrival class mixture, not merely for each separately
chosen deterministic class. -/
theorem lintegral_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount
          (classDependentNonpreemptivePriorityArrivalInitialState z.1) z.2 ∂
      ((classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure).prod
        (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure) ≠ ⊤ := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  exact lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_ne_top
    ρ arrivalRate meanService hn harrivalRate hmeanService hstable
    classDependentNonpreemptivePriorityArrivalInitialState
    measurable_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount
    (by
      simpa [ρ] using
        lintegral_arrivalInitial_meanWork_div_busyAllowance_ne_top
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The same finite arrival-class mixture has finite expected physical busy
time on the canonical class-dependent exponential event race.  This is the
cycle-length input for a subsequent regenerative stationary construction. -/
theorem lintegral_arrivalInitial_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ z : Fin n × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n),
        externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
          classDependentNonpreemptivePriorityArrivalInitialState z ∂
      ((classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure).prod
        (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) ≠ ⊤ := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  exact lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
    ρ arrivalRate meanService hn harrivalRate hmeanService hstable
    classDependentNonpreemptivePriorityArrivalInitialState
    measurable_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount
    (fun horizon =>
      measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
        (n := n) horizon)
      (by
      simpa [ρ] using
        lintegral_arrivalInitial_meanWork_div_busyAllowance_ne_top
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The fresh-arrival busy excursion has a strictly positive physical-time
occupation normalizer on the independent uniformized-event and exponential
clock carrier.  With the strict-load finite bound, this is the finite nonzero
cycle length required before one can construct a regenerative occupation law. -/
theorem zero_lt_lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < ∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
        classDependentNonpreemptivePriorityArrivalInitialState z ∂
      (((classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure).prod
        (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService)))) := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  simpa [ρ] using
    (zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_of_active
      ρ arrivalRate meanService hn harrivalRate hmeanService
      classDependentNonpreemptivePriorityArrivalInitialState
      (fun i => classDependentNonpreemptivePriorityArrivalInitialState_active i)
      (fun horizon =>
        measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon))

/-- The canonical exponential-race realization of a fresh busy excursion has
a strictly positive physical cycle length.  Together with the existing
strict-load finiteness theorem, this supplies the exact normalizer for its
regenerative occupation measure. -/
theorem zero_lt_lintegral_arrivalInitial_classDependentNonpreemptivePriorityEventRaceBusyHoldingTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < ∫⁻ z : Fin n × (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n),
        externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
          classDependentNonpreemptivePriorityArrivalInitialState z ∂
      ((classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure).prod
        (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  simpa [ρ] using
    (zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_of_active
      ρ arrivalRate meanService hn harrivalRate hmeanService
      classDependentNonpreemptivePriorityArrivalInitialState
      (fun i => classDependentNonpreemptivePriorityArrivalInitialState_active i)
      (fun horizon =>
        measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon))

/-- The physical-time mean-work charge of a fresh busy excursion, with its
initial class sampled from the arrival-rate distribution and its event labels
and exponential holding intervals sampled independently. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) :
    ((Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) × (ℕ → ℝ)) → ENNReal :=
  Probability.IIDStream.externalScaledENNReward
    (fun horizon z => Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
      (classDependentNonpreemptivePriorityArrivalInitialState z.1)
      stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon z.2)
    ENNReal.ofReal

/-- Strict load gives finite expected mean-work occupation during a genuine
arrival-start busy excursion.  This averages the finite-start quadratic
Lyapunov estimate over the actual first-arrival class rather than assuming a
stationary initial workload. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ z,
      arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
        arrivalRate meanService z ∂
      ((classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival).toMeasure.prod
        (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
              (exponentialServiceRate meanService)))) ≠ ⊤ := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let M : Measure (ℕ → ClassDependentNonpreemptivePriorityEvent n) :=
    Probability.IIDStream.measure law.toMeasure
  let rate := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let weight : ℕ → (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) → ENNReal :=
    fun horizon z => Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
      (classDependentNonpreemptivePriorityArrivalInitialState z.1)
      stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon z.2
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure M := by
    dsimp [M, law, Probability.IIDStream.measure]
    infer_instance
  have hrate : 0 < rate := by
    dsimp [rate]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hweight : ∀ horizon, Measurable (weight horizon) := by
    intro horizon
    exact Probability.IIDStream.measurable_externalInitial_finiteEventTrajectoryNonnegativeReward_of_finite
      classDependentNonpreemptivePriorityArrivalInitialState
      stopAtIdleClassDependentNonpreemptivePriorityStep
      (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService) horizon
  have hweightFinite : ∑' horizon, ∫⁻ z, weight horizon z ∂(ρ.prod M) ≠ ⊤ := by
    simpa [ρ, M, law, weight] using
      (Probability.IIDStream.tsum_lintegral_externalInitial_finiteEventTrajectoryNonnegativeReward_ne_top_of_finite
        ρ law classDependentNonpreemptivePriorityArrivalInitialState
        stopAtIdleClassDependentNonpreemptivePriorityStep
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService)
        (classDependentNonpreemptivePriorityMeanWorkBusyCost_nonneg
          arrivalRate meanService hn harrivalRate hmeanService hstable)
        (fun i => summable_finiteEventTrajectoryMeanWorkBusyCost
          arrivalRate meanService hn harrivalRate hmeanService hstable
          (classDependentNonpreemptivePriorityArrivalInitialState i)))
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
  simpa [arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge,
    ρ, M, μ, law, rate, weight] using
    (Probability.IIDStream.lintegral_externalScaledENNReward_ne_top
      (ρ.prod M) μ weight ENNReal.ofReal hweight ENNReal.measurable_ofReal
      hweightFinite hgapFinite)

/-- Averaging the finite state-flow accountant over the literal first-arrival
class preserves its regenerative boundary.  This is the finite initial-law
step needed before the excursion occupation measure is packaged into an
invariant embedded law. -/
theorem tendsto_pmfExp_arrivalInitial_finiteEventExpectedCumulativeStoppedStateFlowCost
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    Filter.Tendsto (fun horizon =>
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass =>
          Probability.finiteEventExpectedCumulativeCost
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService))
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
            stopAtIdleClassDependentNonpreemptivePriorityStep
            (classDependentNonpreemptivePriorityStoppedStateFlowCost
              arrivalRate meanService hn harrivalRate hmeanService target)
            horizon))
      Filter.atTop
      (nhds (pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass =>
          classDependentNonpreemptivePriorityStateIndicator target
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass) -
          classDependentNonpreemptivePriorityStateIndicator target
            (emptyNonpreemptivePriorityState n)))) := by
  classical
  unfold pmfExp
  apply tendsto_finset_sum Finset.univ
  intro initialClass _
  exact (tendsto_const_nhds.mul
    (tendsto_finiteEventExpectedCumulativeStoppedStateFlowCost
      arrivalRate meanService hn harrivalRate hmeanService hstable
      (classDependentNonpreemptivePriorityArrivalInitialState initialClass) target
      (classDependentNonpreemptivePriorityArrivalInitialState_idleConsistent initialClass)))

end

end AppliedModelingLib.Queueing
