import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentRegenerativeInitial
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentTaggedBusy
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Regenerative occupation law for a finite priority queue

This module converts a fresh arrival-start busy excursion into an actual
probability law on embedded queue states.  The construction is deliberately
separate from the stationary marked-Poisson realization: it proves the finite
positive normalizer and the exact occupation mass first.  Identifying this
regenerative law with the remote-past/Palm queue remains a later theorem.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The state of a fresh arrival-start excursion immediately after a fixed
number of uniformized events. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityStateAt
    {n : ℕ} (horizon : ℕ) :
    (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) →
      NonpreemptivePriorityState n :=
  fun z => Probability.finiteEventTrajectory
    (classDependentNonpreemptivePriorityArrivalInitialState z.1)
    stopAtIdleClassDependentNonpreemptivePriorityStep horizon
    (Probability.IIDStream.block 0 horizon z.2)

/-- Every finite-horizon embedded state of the finite arrival-class mixture is
measurable: it depends only on the finite initial class and event prefix. -/
theorem measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt
    {n : ℕ} (horizon : ℕ) :
    Measurable (arrivalInitialClassDependentNonpreemptivePriorityStateAt
      (n := n) horizon) := by
  let f : Fin n × (Fin horizon → ClassDependentNonpreemptivePriorityEvent n) →
      NonpreemptivePriorityState n := fun z => Probability.finiteEventTrajectory
        (classDependentNonpreemptivePriorityArrivalInitialState z.1)
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon z.2
  have hf : Measurable f := measurable_of_countable f
  have hprefix : Measurable (fun z : Fin n ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      (z.1, Probability.IIDStream.block 0 horizon z.2)) :=
    measurable_fst.prodMk
      ((Probability.IIDStream.measurable_block 0 horizon).comp measurable_snd)
  simpa [arrivalInitialClassDependentNonpreemptivePriorityStateAt, f] using
    hf.comp hprefix

/-- The event-path carrier of a fresh busy excursion: an arrival-rate sampled
initial class followed by independent uniformized event labels.  This is the
embedded-chain counterpart of the physical-time carrier below. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
  (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure |>.prod
    (Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure)

/-- The unit event-occupation density of one embedded fresh-excursion slot.
It is one precisely while the stopped queue is busy and zero after the
literal empty regeneration state has been reached. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
    {n : ℕ} (horizon : ℕ) :
    (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) → ENNReal :=
  (externalInitialClassDependentNonpreemptivePriorityBusyEvent
    classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
    (fun _ => (1 : ENNReal))

/-- The event-slot density is measurable because the stopped queue at a fixed
horizon depends on only a finite event prefix. -/
theorem measurable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
    {n : ℕ} (horizon : ℕ) :
    Measurable (arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
      (n := n) horizon) := by
  exact measurable_const.indicator
    (measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
      (n := n) horizon)

/-- The finite-horizon expected mass of a target embedded state during a
fresh busy excursion.  The initial class is sampled from the actual
arrival-rate mixture and the subsequent events from the literal uniformized
event law. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) : ℝ :=
  pmfExp
    (classDependentNonpreemptivePriorityArrivalClassPMF
      arrivalRate harrivalRate htotalArrival)
    (fun initialClass =>
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample =>
          let state := Probability.finiteEventTrajectory
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
          if state.active = none then 0
          else classDependentNonpreemptivePriorityStateIndicator target state))

/-- The finite-horizon expected next-state mass entering a target state from
the busy part of a fresh excursion.  Pairing this with the current-state mass
gives the coordinatewise embedded occupation flow. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) : ℝ :=
  pmfExp
    (classDependentNonpreemptivePriorityArrivalClassPMF
      arrivalRate harrivalRate htotalArrival)
    (fun initialClass =>
      pmfExp (pmfProduct (Fin horizon)
        (ClassDependentNonpreemptivePriorityEvent n)
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)))
        (fun sample =>
          let state := Probability.finiteEventTrajectory
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
            stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
          if state.active = none then 0
          else pmfExp
            (classDependentNonpreemptivePriorityEventPMF arrivalRate
              (exponentialServiceRate meanService) hn harrivalRate
              (exponentialServiceRate_pos meanService hmeanService))
            (fun event => classDependentNonpreemptivePriorityStateIndicator target
              (stepClassDependentNonpreemptivePriority state event))))

/-- Finite state-occupation coordinates are nonnegative probabilities. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt_nonneg
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) :
    0 ≤ arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon := by
  unfold arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
  apply pmfExp_nonneg_of_forall_nonneg
  intro initialClass
  apply pmfExp_nonneg_of_forall_nonneg
  intro sample
  let state := Probability.finiteEventTrajectory
    (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
    stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
  change 0 ≤ if state.active = none then (0 : ℝ)
    else classDependentNonpreemptivePriorityStateIndicator target state
  by_cases hidle : state.active = none
  · simp [hidle]
  · simp only [if_neg hidle]
    unfold classDependentNonpreemptivePriorityStateIndicator
    split <;> norm_num

/-- Finite transition-occupation coordinates are nonnegative probabilities. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt_nonneg
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) :
    0 ≤ arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon := by
  unfold arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
  apply pmfExp_nonneg_of_forall_nonneg
  intro initialClass
  apply pmfExp_nonneg_of_forall_nonneg
  intro sample
  let state := Probability.finiteEventTrajectory
    (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
    stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample
  change 0 ≤ if state.active = none then (0 : ℝ)
    else pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => classDependentNonpreemptivePriorityStateIndicator target
        (stepClassDependentNonpreemptivePriority state event))
  by_cases hidle : state.active = none
  · simp [hidle]
  · simp only [if_neg hidle]
    apply pmfExp_nonneg_of_forall_nonneg
    intro event
    unfold classDependentNonpreemptivePriorityStateIndicator
    split <;> norm_num

/-- Finite excursion flow is exactly the difference between its current-state
and next-state occupation coordinates.  This is a finite identity, so the
eventual regeneration limit is not used here. -/
theorem pmfExp_arrivalInitial_finiteEventExpectedCumulativeStoppedStateFlowCost_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) :
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
          horizon) =
      ∑ eventIndex ∈ Finset.range horizon,
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex -
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex) := by
  classical
  unfold Probability.finiteEventExpectedCumulativeCost
  rw [pmfExp_sum]
  apply Finset.sum_congr rfl
  intro eventIndex _
  simp only [arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt,
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt]
  rw [← pmfExp_sub]
  apply pmfExp_congr
  intro initialClass
  rw [← pmfExp_sub]
  apply pmfExp_congr
  intro sample
  let state := Probability.finiteEventTrajectory
    (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
    stopAtIdleClassDependentNonpreemptivePriorityStep eventIndex sample
  by_cases hidle : state.active = none
  · simp [classDependentNonpreemptivePriorityStoppedStateFlowCost, state, hidle]
  · simp [classDependentNonpreemptivePriorityStoppedStateFlowCost, state, hidle]

/-- The two finite occupation coordinates have the regenerative boundary
limit under strict load.  The next step is to identify their infinite sums
with the raw embedded occupation measure and its kernel image. -/
theorem tendsto_sum_range_arrivalInitialClassDependentNonpreemptivePriorityBusyEventFlow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    Filter.Tendsto (fun horizon =>
      ∑ eventIndex ∈ Finset.range horizon,
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex -
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex))
      Filter.atTop
      (nhds (pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass =>
          classDependentNonpreemptivePriorityStateIndicator target
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass) -
          classDependentNonpreemptivePriorityStateIndicator target
            (emptyNonpreemptivePriorityState n)))) := by
  rw [show (fun horizon =>
      ∑ eventIndex ∈ Finset.range horizon,
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex -
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target eventIndex)) =
      (fun horizon => pmfExp
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
            horizon)) by
      funext horizon
      exact (pmfExp_arrivalInitial_finiteEventExpectedCumulativeStoppedStateFlowCost_eq
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon).symm]
  exact tendsto_pmfExp_arrivalInitial_finiteEventExpectedCumulativeStoppedStateFlowCost
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target

/-- The event-count contribution of one embedded state slot in a fresh busy
excursion.  Unlike the physical occupation slot below, this measure has no
holding-time weight. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) (horizon : ℕ) :
    Measure (NonpreemptivePriorityState n) :=
  Measure.map
    (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
    ((arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).withDensity
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity horizon))

/-- The unnormalized embedded-chain occupation measure of all busy slots in a
fresh excursion.  It is the discrete object that carries the regenerative
flow balance; independent exponential holding times are introduced only when
passing to physical time. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  Measure.sum fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon

/-- A single event-occupation slot has exactly the finite-product target mass
used in the coordinatewise flow calculation.  This identifies the abstract
measure construction with the literal first-arrival and IID-event carrier. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure_apply_singleton
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon {target} =
      ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  classical
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let C := arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
    (n := n)
  let reward : NonpreemptivePriorityState n → ℝ := fun state =>
    if state.active = none then 0
    else classDependentNonpreemptivePriorityStateIndicator target state
  have hreward : ∀ state, 0 ≤ reward state := by
    intro state
    unfold reward
    split_ifs with hidle
    · exact le_rfl
    · unfold classDependentNonpreemptivePriorityStateIndicator
      split <;> norm_num
  have hrewardMeasurable : Measurable reward := measurable_of_countable _
  have hfirst :
      arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon {target} =
      ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
          (classDependentNonpreemptivePriorityArrivalInitialState z.1)
          stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2 ∂C := by
    rw [show arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon =
        Measure.map (state horizon) (C.withDensity (density horizon)) by rfl]
    rw [Measure.map_apply
      (measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
      (measurableSet_singleton target)]
    rw [withDensity_apply (density horizon)
      ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
        (measurableSet_singleton target))]
    rw [← MeasureTheory.lintegral_indicator
      ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
        (measurableSet_singleton target))]
    apply MeasureTheory.lintegral_congr
    intro z
    let current := state horizon z
    have htrajectory : Probability.finiteEventTrajectory
        (classDependentNonpreemptivePriorityArrivalInitialState z.1)
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon
        (Probability.IIDStream.block 0 horizon z.2) = current := by
      rfl
    change (state horizon ⁻¹' {target}).indicator (density horizon) z =
      Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
        (classDependentNonpreemptivePriorityArrivalInitialState z.1)
        stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2
    by_cases hidle : current.active = none
    · have hnotBusy : z ∉ externalInitialClassDependentNonpreemptivePriorityBusyEvent
          classDependentNonpreemptivePriorityArrivalInitialState horizon := by
        change ¬ classDependentNonpreemptivePriorityBusy current
        simpa [classDependentNonpreemptivePriorityBusy] using hidle
      have hdensity : density horizon z = 0 := by
        unfold density arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
        rw [Set.indicator_of_notMem hnotBusy]
      by_cases htarget : state horizon z = target
      · have hmem : z ∈ state horizon ⁻¹' {target} := by
          change state horizon z = target
          exact htarget
        rw [Set.indicator_of_mem hmem, hdensity]
        simp only [Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
        rw [htrajectory]
        simp [reward, hidle]
      · have hnotmem : z ∉ state horizon ⁻¹' {target} := by
          intro hmem
          apply htarget
          exact hmem
        rw [Set.indicator_of_notMem hnotmem]
        simp only [Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
        rw [htrajectory]
        simp [reward, hidle]
    · have hbusy : z ∈ externalInitialClassDependentNonpreemptivePriorityBusyEvent
          classDependentNonpreemptivePriorityArrivalInitialState horizon := by
        change classDependentNonpreemptivePriorityBusy current
        simpa [classDependentNonpreemptivePriorityBusy] using hidle
      have hdensity : density horizon z = 1 := by
        unfold density arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
        rw [Set.indicator_of_mem hbusy]
      by_cases htarget : current = target
      · have hmem : z ∈ state horizon ⁻¹' {target} := by
          change state horizon z = target
          simpa [current] using htarget
        rw [Set.indicator_of_mem hmem, hdensity]
        simp only [Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
        rw [htrajectory]
        have htargetBusy : target.active ≠ none := by
          rw [← htarget]
          exact hidle
        simp [reward, htargetBusy, htarget,
          classDependentNonpreemptivePriorityStateIndicator]
      · have hnotmem : z ∉ state horizon ⁻¹' {target} := by
          intro hmem
          apply htarget
          change state horizon z = target at hmem
          simpa [current] using hmem
        rw [Set.indicator_of_notMem hnotmem]
        simp only [Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
        rw [htrajectory]
        simp [reward, classDependentNonpreemptivePriorityStateIndicator, htarget]
  let f : Fin n → ℝ := fun initialClass =>
    pmfExp (pmfProduct (Fin horizon)
      (ClassDependentNonpreemptivePriorityEvent n) law)
      (fun sample => reward (Probability.finiteEventTrajectory
        (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))
  have hfNonneg : ∀ initialClass, 0 ≤ f initialClass := by
    intro initialClass
    apply pmfExp_nonneg_of_forall_nonneg
    intro sample
    exact hreward _
  have hfIntegrable : Integrable f ρ := Integrable.of_finite
  calc
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon {target} =
      ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
          (classDependentNonpreemptivePriorityArrivalInitialState z.1)
          stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2 ∂C := hfirst
    _ = ∫⁻ initialClass, ENNReal.ofReal (f initialClass) ∂ρ := by
      simpa [C, ρ, law, f] using
        (Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryNonnegativeReward_eq_of_finite
          ρ law classDependentNonpreemptivePriorityArrivalInitialState
          stopAtIdleClassDependentNonpreemptivePriorityStep reward hreward horizon)
    _ = ENNReal.ofReal (pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival) f) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfIntegrable
        (Filter.Eventually.of_forall hfNonneg), ← pmfExp_eq_integral_toMeasure]
    _ = ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
      rfl

/-- Every target coordinate of the raw embedded occupation measure is the
Tonelli sum of the finite state masses used by the excursion flow identity. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_apply_singleton
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target} =
      ∑' horizon, ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure,
    Measure.sum_apply _ (measurableSet_singleton target)]
  apply tsum_congr
  intro horizon
  exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure_apply_singleton
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon

/-- The target atom of the literal embedded transition kernel is the finite
event expectation of the corresponding target indicator. -/
theorem classDependentNonpreemptivePriorityMeasureKernel_apply_singleton_eq_ofReal_pmfExp
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state target : NonpreemptivePriorityState n) :
    classDependentNonpreemptivePriorityMeasureKernel arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService) state {target} =
      ENNReal.ofReal (pmfExp
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))
        (fun event => classDependentNonpreemptivePriorityStateIndicator target
          (stepClassDependentNonpreemptivePriority state event))) := by
  classical
  rw [classDependentNonpreemptivePriorityMeasureKernel_apply_singleton]
  rw [show (fun event => classDependentNonpreemptivePriorityStateIndicator target
      (stepClassDependentNonpreemptivePriority state event)) =
      (fun event => if stepClassDependentNonpreemptivePriority state event = target then 1 else 0) by
        funext event
        simp [classDependentNonpreemptivePriorityStateIndicator]]
  rw [classDependentNonpreemptivePriorityUniformizedKernel, PMF.map_apply,
    tsum_fintype]
  simp only [pmfExp]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro event _
    by_cases htarget : stepClassDependentNonpreemptivePriority state event = target
    · simp only [htarget, if_pos]
      simpa using (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm
    · have htarget' : target ≠ stepClassDependentNonpreemptivePriority state event :=
        Ne.symm htarget
      simp [htarget, htarget']
  · intro event _
    exact mul_nonneg ENNReal.toReal_nonneg (by split <;> norm_num)

/-- Applying one embedded queue transition to a single occupation slot gives
exactly the finite next-state mass used by the state-flow accountant. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure_bind_apply_singleton
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) (horizon : ℕ) :
    (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) {target} =
      ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  classical
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let C := arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
    (n := n)
  let K := classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let reward : NonpreemptivePriorityState n → ℝ := fun state =>
    if state.active = none then 0
    else pmfExp law (fun event => classDependentNonpreemptivePriorityStateIndicator target
      (stepClassDependentNonpreemptivePriority state event))
  have hreward : ∀ queueState, 0 ≤ reward queueState := by
    intro queueState
    unfold reward
    split_ifs
    · exact le_rfl
    · apply pmfExp_nonneg_of_forall_nonneg
      intro event
      unfold classDependentNonpreemptivePriorityStateIndicator
      split <;> norm_num
  have hkernel : ∀ queueState,
      K queueState {target} = ENNReal.ofReal (pmfExp law
        (fun event => classDependentNonpreemptivePriorityStateIndicator target
          (stepClassDependentNonpreemptivePriority queueState event))) := by
    intro queueState
    exact classDependentNonpreemptivePriorityMeasureKernel_apply_singleton_eq_ofReal_pmfExp
      arrivalRate meanService hn harrivalRate hmeanService queueState target
  have hfirst :
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon).bind K {target} =
      ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
          (classDependentNonpreemptivePriorityArrivalInitialState z.1)
          stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2 ∂C := by
    rw [show arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon =
        Measure.map (state horizon) (C.withDensity (density horizon)) by rfl]
    rw [Measure.bind_apply (measurableSet_singleton target) (Kernel.aemeasurable K)]
    rw [lintegral_map (Kernel.measurable_coe K (measurableSet_singleton target))
      (measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)]
    change ∫⁻ z, K (state horizon z) {target} ∂C.withDensity (density horizon) = _
    calc
      ∫⁻ z, K (state horizon z) {target} ∂C.withDensity (density horizon) =
        ∫⁻ z, density horizon z * K (state horizon z) {target} ∂C := by
          simpa [Function.comp_def, state, density] using
            (lintegral_withDensity_eq_lintegral_mul C
              (measurable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity horizon)
              ((Kernel.measurable_coe K (measurableSet_singleton target)).comp
                (measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)))
      _ = ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
          Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
            (classDependentNonpreemptivePriorityArrivalInitialState z.1)
            stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2 ∂C := by
          apply MeasureTheory.lintegral_congr
          intro z
          let current := state horizon z
          have htrajectory : Probability.finiteEventTrajectory
              (classDependentNonpreemptivePriorityArrivalInitialState z.1)
              stopAtIdleClassDependentNonpreemptivePriorityStep horizon
              (Probability.IIDStream.block 0 horizon z.2) = current := by
            rfl
          change density horizon z * K (state horizon z) {target} =
            Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
              (classDependentNonpreemptivePriorityArrivalInitialState z.1)
              stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2
          by_cases hidle : current.active = none
          · have hnotBusy : z ∉ externalInitialClassDependentNonpreemptivePriorityBusyEvent
                classDependentNonpreemptivePriorityArrivalInitialState horizon := by
              change ¬ classDependentNonpreemptivePriorityBusy current
              simpa [classDependentNonpreemptivePriorityBusy] using hidle
            have hdensity : density horizon z = 0 := by
              unfold density arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
              rw [Set.indicator_of_notMem hnotBusy]
            rw [hdensity]
            simp only [zero_mul, Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
            rw [htrajectory]
            simp [reward, hidle]
          · have hbusy : z ∈ externalInitialClassDependentNonpreemptivePriorityBusyEvent
                classDependentNonpreemptivePriorityArrivalInitialState horizon := by
              change classDependentNonpreemptivePriorityBusy current
              simpa [classDependentNonpreemptivePriorityBusy] using hidle
            have hdensity : density horizon z = 1 := by
              unfold density arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
              rw [Set.indicator_of_mem hbusy]
            rw [hdensity, hkernel (state horizon z)]
            simp only [one_mul, Probability.IIDStream.finiteEventTrajectoryNonnegativeReward]
            have hcurrent : state horizon z = current := by rfl
            rw [hcurrent]
            rw [htrajectory]
            simp [reward, hidle]
  let f : Fin n → ℝ := fun initialClass =>
    pmfExp (pmfProduct (Fin horizon)
      (ClassDependentNonpreemptivePriorityEvent n) law)
      (fun sample => reward (Probability.finiteEventTrajectory
        (classDependentNonpreemptivePriorityArrivalInitialState initialClass)
        stopAtIdleClassDependentNonpreemptivePriorityStep horizon sample))
  have hfNonneg : ∀ initialClass, 0 ≤ f initialClass := by
    intro initialClass
    apply pmfExp_nonneg_of_forall_nonneg
    intro sample
    exact hreward _
  have hfIntegrable : Integrable f ρ := Integrable.of_finite
  calc
    (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon).bind K {target} =
      ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        Probability.IIDStream.finiteEventTrajectoryNonnegativeReward
          (classDependentNonpreemptivePriorityArrivalInitialState z.1)
          stopAtIdleClassDependentNonpreemptivePriorityStep reward horizon z.2 ∂C := hfirst
    _ = ∫⁻ initialClass, ENNReal.ofReal (f initialClass) ∂ρ := by
      simpa [C, ρ, law, f] using
        (Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryNonnegativeReward_eq_of_finite
          ρ law classDependentNonpreemptivePriorityArrivalInitialState
          stopAtIdleClassDependentNonpreemptivePriorityStep reward hreward horizon)
    _ = ENNReal.ofReal (pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival) f) := by
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfIntegrable
        (Filter.Eventually.of_forall hfNonneg), ← pmfExp_eq_integral_toMeasure]
    _ = ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
      rfl

/-- The target coordinate of the kernel image of the raw embedded occupation
measure is the Tonelli sum of its finite transition masses. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_apply_singleton
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) :
    (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) {target} =
      ∑' horizon, ENNReal.ofReal
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  rw [Measure.bind_apply (measurableSet_singleton target) (Kernel.aemeasurable _),
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure,
    lintegral_sum_measure]
  apply tsum_congr
  intro horizon
  rw [← Measure.bind_apply (measurableSet_singleton target) (Kernel.aemeasurable _)]
  exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure_bind_apply_singleton
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon

/-- The total mass of the embedded busy-occupation measure is exactly the
expected number of busy uniformization slots in the fresh excursion.  This
is a Tonelli identity on the literal IID event stream. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ =
    ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
      classDependentNonpreemptivePriorityBusyEventCount
        (classDependentNonpreemptivePriorityArrivalInitialState z.1) z.2 ∂
      arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let C := arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity
    (n := n)
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  calc
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon Set.univ :=
      Measure.sum_apply _ MeasurableSet.univ
    _ = ∑' horizon, ∫⁻ z, density horizon z ∂C := by
      apply tsum_congr
      intro horizon
      change (Measure.map (state horizon)
        (C.withDensity (density horizon))) Set.univ = _
      rw [Measure.map_apply
        (measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
        MeasurableSet.univ]
      simp only [Set.preimage_univ]
      simpa only [setLIntegral_univ] using
        (withDensity_apply (density horizon) MeasurableSet.univ)
    _ = ∑' horizon, C
        (externalInitialClassDependentNonpreemptivePriorityBusyEvent
          classDependentNonpreemptivePriorityArrivalInitialState horizon) := by
      apply tsum_congr
      intro horizon
      change ∫⁻ z, (externalInitialClassDependentNonpreemptivePriorityBusyEvent
        classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
          (fun _ => (1 : ENNReal)) z ∂C = _
      exact MeasureTheory.lintegral_indicator_one
        (measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon)
    _ = ∫⁻ z : Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n),
        classDependentNonpreemptivePriorityBusyEventCount
          (classDependentNonpreemptivePriorityArrivalInitialState z.1) z.2 ∂C := by
      symm
      simpa [C, arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure,
        classDependentNonpreemptivePriorityBusyEventCount] using
        (Probability.IIDStream.lintegral_externalInitial_finiteEventTrajectoryEventCount
          ((classDependentNonpreemptivePriorityArrivalClassPMF
            arrivalRate harrivalRate htotalArrival).toMeasure)
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService))
          classDependentNonpreemptivePriorityArrivalInitialState
          stopAtIdleClassDependentNonpreemptivePriorityStep
          classDependentNonpreemptivePriorityBusy
          (fun horizon =>
            measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
              (n := n) horizon))

/-- Strict load makes the total embedded busy occupation finite. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ ≠ ⊤ := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ]
  exact lintegral_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount_ne_top
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- A fresh arrival contributes at least its initial busy event slot, so the
embedded occupation normalizer is strictly positive before any time scaling. -/
theorem zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ]
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hcount :=
    one_le_lintegral_externalInitial_classDependentNonpreemptivePriorityBusyEventCount_of_active
      ρ arrivalRate meanService hn harrivalRate hmeanService
      classDependentNonpreemptivePriorityArrivalInitialState
      (fun i => classDependentNonpreemptivePriorityArrivalInitialState_active i)
  have hpositive : 0 < ∫⁻ z : Fin n ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n),
      classDependentNonpreemptivePriorityBusyEventCount
        (classDependentNonpreemptivePriorityArrivalInitialState z.1) z.2 ∂
      arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
    apply lt_of_lt_of_le zero_lt_one
    simpa [ρ, arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure] using hcount
  exact hpositive

/-- Strict load makes every real target-coordinate state-mass series
summable.  This is obtained from the already finite raw occupation measure,
not from an independent stationarity assumption. -/
theorem summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    Summable (fun horizon =>
      arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  let B := arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let a : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have ha : ∀ horizon, 0 ≤ a horizon := by
    intro horizon
    exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt_nonneg
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hBuniv : B Set.univ ≠ ⊤ := by
    simpa [B] using
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  have hBtarget : B {target} ≠ ⊤ :=
    ne_top_of_le_ne_top hBuniv (measure_mono (Set.subset_univ _))
  have hsumOfReal : ∑' horizon, ENNReal.ofReal (a horizon) ≠ ⊤ := by
    rw [show B {target} = ∑' horizon, ENNReal.ofReal (a horizon) by
      simpa [B, a] using
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_apply_singleton
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target)] at hBtarget
    exact hBtarget
  let aNN : ℕ → NNReal := fun horizon => ⟨a horizon, ha horizon⟩
  have hcoe : ∀ horizon, (aNN horizon : ENNReal) = ENNReal.ofReal (a horizon) := by
    intro horizon
    exact (ENNReal.ofReal_eq_coe_nnreal (ha horizon)).symm
  have hsumNN : ∑' horizon, (aNN horizon : ENNReal) ≠ ⊤ := by
    rw [show (fun horizon => (aNN horizon : ENNReal)) =
        (fun horizon => ENNReal.ofReal (a horizon)) by
      funext horizon
      exact hcoe horizon]
    exact hsumOfReal
  have hNN : Summable aNN := ENNReal.tsum_coe_ne_top_iff_summable.mp hsumNN
  simpa [aNN, a] using (NNReal.summable_coe.2 hNN)

/-- Strict load also makes every real target-coordinate transition-mass
series summable.  The embedded queue kernel preserves the finite total mass
of the raw excursion occupation measure. -/
theorem summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    Summable (fun horizon =>
      arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) := by
  let B := arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let K := classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let b : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hb : ∀ horizon, 0 ≤ b horizon := by
    intro horizon
    exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt_nonneg
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hBuniv : B Set.univ ≠ ⊤ := by
    simpa [B] using
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  have hBindUniv : (B.bind K) Set.univ = B Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable K)]
    simp_rw [IsProbabilityMeasure.measure_univ]
    exact MeasureTheory.lintegral_one
  have hBbindUniv : (B.bind K) Set.univ ≠ ⊤ := by
    rw [hBindUniv]
    exact hBuniv
  have hBbindTarget : (B.bind K) {target} ≠ ⊤ :=
    ne_top_of_le_ne_top hBbindUniv (measure_mono (Set.subset_univ _))
  have hsumOfReal : ∑' horizon, ENNReal.ofReal (b horizon) ≠ ⊤ := by
    rw [show (B.bind K) {target} = ∑' horizon, ENNReal.ofReal (b horizon) by
      simpa [B, K, b] using
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_apply_singleton
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target)] at hBbindTarget
    exact hBbindTarget
  let bNN : ℕ → NNReal := fun horizon => ⟨b horizon, hb horizon⟩
  have hcoe : ∀ horizon, (bNN horizon : ENNReal) = ENNReal.ofReal (b horizon) := by
    intro horizon
    exact (ENNReal.ofReal_eq_coe_nnreal (hb horizon)).symm
  have hsumNN : ∑' horizon, (bNN horizon : ENNReal) ≠ ⊤ := by
    rw [show (fun horizon => (bNN horizon : ENNReal)) =
        (fun horizon => ENNReal.ofReal (b horizon)) by
      funext horizon
      exact hcoe horizon]
    exact hsumOfReal
  have hNN : Summable bNN := ENNReal.tsum_coe_ne_top_iff_summable.mp hsumNN
  simpa [bNN, b] using (NNReal.summable_coe.2 hNN)

/-- The real target mass of the raw embedded occupation measure is the sum of
the finite state-occupation coordinates. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_apply_singleton_toReal_eq_tsum
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target}).toReal =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon := by
  let a : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have ha : ∀ horizon, 0 ≤ a horizon := by
    intro horizon
    exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt_nonneg
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hsum : Summable a := by
    simpa [a] using
      (summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target)
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_apply_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg ha hsum]
  simpa [a] using ENNReal.toReal_ofReal (tsum_nonneg ha)

/-- The real target mass after one embedded transition is the sum of the
finite next-state occupation coordinates. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_apply_singleton_toReal_eq_tsum
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    ((arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) {target}).toReal =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon := by
  let b : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hb : ∀ horizon, 0 ≤ b horizon := by
    intro horizon
    exact arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt_nonneg
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have hsum : Summable b := by
    simpa [b] using
      (summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target)
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_apply_singleton]
  rw [← ENNReal.ofReal_tsum_of_nonneg hb hsum]
  simpa [b] using ENNReal.toReal_ofReal (tsum_nonneg hb)

/-- The target coordinate of the fresh-arrival initial-state law is the
arrival-class expectation of its target indicator. -/
theorem classDependentNonpreemptivePriorityArrivalInitialStatePMF_toMeasure_apply_singleton_toReal
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) :
    ((classDependentNonpreemptivePriorityArrivalInitialStatePMF
      arrivalRate harrivalRate htotalArrival).toMeasure {target}).toReal =
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
          (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) := by
  classical
  rw [PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)]
  unfold classDependentNonpreemptivePriorityArrivalInitialStatePMF
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · unfold pmfExp
    apply Finset.sum_congr rfl
    intro initialClass _
    by_cases htarget : classDependentNonpreemptivePriorityArrivalInitialState initialClass = target
    · have htarget' : target =
          classDependentNonpreemptivePriorityArrivalInitialState initialClass := htarget.symm
      unfold classDependentNonpreemptivePriorityStateIndicator
      rw [if_pos htarget']
      change _ = _ * (if classDependentNonpreemptivePriorityArrivalInitialState initialClass = target
        then (1 : ℝ) else 0)
      rw [if_pos htarget]
      ring
    · have htarget' : target ≠
          classDependentNonpreemptivePriorityArrivalInitialState initialClass := Ne.symm htarget
      unfold classDependentNonpreemptivePriorityStateIndicator
      rw [if_neg htarget']
      change _ = _ * (if classDependentNonpreemptivePriorityArrivalInitialState initialClass = target
        then (1 : ℝ) else 0)
      rw [if_neg htarget]
      norm_num
  · intro initialClass _
    by_cases htarget : target =
        classDependentNonpreemptivePriorityArrivalInitialState initialClass
    · simp [htarget, PMF.apply_ne_top]
    · simp [htarget]

/-- Summing the finite coordinate flow gives the exact full-excursion
boundary balance: raw state occupation minus its one-step image is the
arrival-start mass minus the empty regeneration mass. -/
theorem tsum_arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt_sub_tsum_transitionMassAt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (target : NonpreemptivePriorityState n) :
    (∑' horizon,
      arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) -
      (∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) =
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass =>
          classDependentNonpreemptivePriorityStateIndicator target
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass) -
          classDependentNonpreemptivePriorityStateIndicator target
            (emptyNonpreemptivePriorityState n)) := by
  let a : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  let b : ℕ → ℝ := fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon
  have ha : Summable a := by
    simpa [a] using
      (summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target)
  have hb : Summable b := by
    simpa [b] using
      (summable_arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target)
  have hflow : Filter.Tendsto (fun horizon =>
      ∑ eventIndex ∈ Finset.range horizon, (a eventIndex - b eventIndex))
      Filter.atTop
      (nhds (pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass =>
          classDependentNonpreemptivePriorityStateIndicator target
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass) -
          classDependentNonpreemptivePriorityStateIndicator target
            (emptyNonpreemptivePriorityState n)))) := by
    simpa [a, b] using
      (tendsto_sum_range_arrivalInitialClassDependentNonpreemptivePriorityBusyEventFlow
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target)
  have hsum : Filter.Tendsto (fun horizon =>
      ∑ eventIndex ∈ Finset.range horizon, (a eventIndex - b eventIndex))
      Filter.atTop (nhds ((∑' horizon, a horizon) - (∑' horizon, b horizon))) := by
    rw [show (fun horizon =>
        ∑ eventIndex ∈ Finset.range horizon, (a eventIndex - b eventIndex)) =
        (fun horizon =>
          (∑ eventIndex ∈ Finset.range horizon, a eventIndex) -
          ∑ eventIndex ∈ Finset.range horizon, b eventIndex) by
      funext horizon
      rw [Finset.sum_sub_distrib]]
    exact ha.hasSum.tendsto_sum_nat.sub hb.hasSum.tendsto_sum_nat
  simpa [a, b] using (tendsto_nhds_unique hsum hflow)

/-- The raw busy-excursion occupation measure satisfies the exact embedded
flow balance: its one-step image, augmented by the fresh-arrival law, equals
the occupation measure augmented by the empty regeneration mass. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_add_arrivalInitialStatePMF_eq_add_dirac
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) +
      (classDependentNonpreemptivePriorityArrivalInitialStatePMF
        arrivalRate harrivalRate htotalArrival).toMeasure =
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival +
      Measure.dirac (emptyNonpreemptivePriorityState n) := by
  classical
  let B := arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let K := classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let μ := (classDependentNonpreemptivePriorityArrivalInitialStatePMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let empty := emptyNonpreemptivePriorityState n
  have hBuniv : B Set.univ ≠ ⊤ := by
    simpa [B] using
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  have hBindUniv : (B.bind K) Set.univ = B Set.univ := by
    rw [Measure.bind_apply MeasurableSet.univ (Kernel.aemeasurable K)]
    simp_rw [IsProbabilityMeasure.measure_univ]
    exact MeasureTheory.lintegral_one
  apply Measure.ext_of_singleton
  intro target
  have hBtarget : B {target} ≠ ⊤ :=
    ne_top_of_le_ne_top hBuniv (measure_mono (Set.subset_univ _))
  have hBindTarget : (B.bind K) {target} ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (B.bind K) Set.univ ≠ ⊤ by rw [hBindUniv]; exact hBuniv)
    exact measure_mono (Set.subset_univ _)
  have hμtarget : μ {target} ≠ ⊤ := by
    rw [show μ = (classDependentNonpreemptivePriorityArrivalInitialStatePMF
      arrivalRate harrivalRate htotalArrival).toMeasure by rfl,
      PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)]
    exact PMF.apply_ne_top _ _
  have hdiracTarget : Measure.dirac empty {target} ≠ ⊤ := by
    by_cases hempty : empty = target
    · rw [Measure.dirac_apply_of_mem (by simpa [hempty])]
      norm_num
    · rw [Measure.dirac_apply' empty (measurableSet_singleton target),
        Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff])]
      norm_num
  simp only [Measure.add_apply]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.add_ne_top.mpr ⟨hBindTarget, hμtarget⟩)
    (ENNReal.add_ne_top.mpr ⟨hBtarget, hdiracTarget⟩)).mp
  rw [ENNReal.toReal_add hBindTarget hμtarget,
    ENNReal.toReal_add hBtarget hdiracTarget]
  rw [show (B.bind K {target}).toReal =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon by
      simpa [B, K] using
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_apply_singleton_toReal_eq_tsum
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target),
    show (B {target}).toReal =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon by
      simpa [B] using
        (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_apply_singleton_toReal_eq_tsum
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target),
    show (μ {target}).toReal = pmfExp
      (classDependentNonpreemptivePriorityArrivalClassPMF
        arrivalRate harrivalRate htotalArrival)
      (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
        (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) by
      simpa [μ] using
        (classDependentNonpreemptivePriorityArrivalInitialStatePMF_toMeasure_apply_singleton_toReal
          arrivalRate harrivalRate htotalArrival target)]
  have hdirac : (Measure.dirac empty {target}).toReal =
      classDependentNonpreemptivePriorityStateIndicator target empty := by
    unfold classDependentNonpreemptivePriorityStateIndicator
    rw [Measure.dirac_apply' empty (measurableSet_singleton target)]
    change (if empty = target then (1 : ENNReal) else 0).toReal =
      if empty = target then (1 : ℝ) else 0
    split <;> norm_num
  rw [hdirac]
  have hflow :=
    tsum_arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt_sub_tsum_transitionMassAt
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable target
  have hflow' :
      (∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventStateMassAt
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) -
        (∑' horizon,
          arrivalInitialClassDependentNonpreemptivePriorityBusyEventTransitionMassAt
            arrivalRate meanService hn harrivalRate hmeanService htotalArrival target horizon) =
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
          (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) -
        classDependentNonpreemptivePriorityStateIndicator target empty := by
    simpa [empty, pmfExp_sub] using hflow
  linarith [hflow']

/-- The empty queue's uniformized transition has exactly the arrival and
service boundary fluxes needed to close a complete embedded regeneration
cycle. -/
theorem totalEventRate_smul_classDependentNonpreemptivePriorityMeasureKernel_empty_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    ENNReal.ofReal
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) •
      classDependentNonpreemptivePriorityMeasureKernel arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)
        (emptyNonpreemptivePriorityState n) =
    ENNReal.ofReal (∑ i, arrivalRate i) •
      (classDependentNonpreemptivePriorityArrivalInitialStatePMF
        arrivalRate harrivalRate htotalArrival).toMeasure +
    ENNReal.ofReal (∑ i, exponentialServiceRate meanService i) •
      Measure.dirac (emptyNonpreemptivePriorityState n) := by
  classical
  let K := classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let μ := (classDependentNonpreemptivePriorityArrivalInitialStatePMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let empty := emptyNonpreemptivePriorityState n
  let L : ℝ := ∑ i, arrivalRate i
  let S : ℝ := ∑ i, exponentialServiceRate meanService i
  have hL : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro i _
    exact harrivalRate i
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i _
    exact (exponentialServiceRate_pos meanService hmeanService i).le
  have hR : 0 < L + S := add_pos_of_pos_of_nonneg (by simpa [L] using htotalArrival) hS
  apply Measure.ext_of_singleton
  intro target
  have hKtarget : K empty {target} ≠ ⊤ := by
    exact measure_ne_top _ _
  have hμtarget : μ {target} ≠ ⊤ := by
    rw [show μ = (classDependentNonpreemptivePriorityArrivalInitialStatePMF
      arrivalRate harrivalRate htotalArrival).toMeasure by rfl,
      PMF.toMeasure_apply_singleton _ target (measurableSet_singleton target)]
    exact PMF.apply_ne_top _ _
  have hdiracTarget : Measure.dirac empty {target} ≠ ⊤ := by
    by_cases hempty : empty = target
    · rw [Measure.dirac_apply_of_mem (by simpa [hempty])]
      norm_num
    · rw [Measure.dirac_apply' empty (measurableSet_singleton target),
        Set.indicator_of_notMem (by simpa only [Set.mem_singleton_iff])]
      norm_num
  simp only [Measure.smul_apply, Measure.add_apply]
  apply (ENNReal.toReal_eq_toReal_iff'
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtarget)
    (ENNReal.add_ne_top.mpr ⟨
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμtarget,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiracTarget⟩)).mp
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_add
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμtarget)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdiracTarget),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hL, ENNReal.toReal_ofReal hS,
    ENNReal.toReal_ofReal hR.le]
  have hkernel : (K empty {target}).toReal =
      pmfExp
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))
        (fun event => classDependentNonpreemptivePriorityStateIndicator target
          (stepClassDependentNonpreemptivePriority empty event)) := by
    rw [show K empty {target} = ENNReal.ofReal (pmfExp
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (fun event => classDependentNonpreemptivePriorityStateIndicator target
        (stepClassDependentNonpreemptivePriority empty event))) by
      simpa [K, empty] using
        (classDependentNonpreemptivePriorityMeasureKernel_apply_singleton_eq_ofReal_pmfExp
          arrivalRate meanService hn harrivalRate hmeanService
          (emptyNonpreemptivePriorityState n) target)]
    apply ENNReal.toReal_ofReal
    apply pmfExp_nonneg_of_forall_nonneg
    intro event
    unfold classDependentNonpreemptivePriorityStateIndicator
    split <;> norm_num
  have hμ : (μ {target}).toReal =
      pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
          (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) := by
    simpa [μ] using
      (classDependentNonpreemptivePriorityArrivalInitialStatePMF_toMeasure_apply_singleton_toReal
        arrivalRate harrivalRate htotalArrival target)
  have hdirac : (Measure.dirac empty {target}).toReal =
      classDependentNonpreemptivePriorityStateIndicator target empty := by
    unfold classDependentNonpreemptivePriorityStateIndicator
    rw [Measure.dirac_apply' empty (measurableSet_singleton target)]
    change (if empty = target then (1 : ENNReal) else 0).toReal =
      if empty = target then (1 : ℝ) else 0
    split <;> norm_num
  rw [hkernel, hμ, hdirac]
  have hsource :=
    pmfExp_classDependentNonpreemptivePriorityEvent_empty_eq_arrivalInitial_mixture
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival
      (fun state => classDependentNonpreemptivePriorityStateIndicator target state)
  have hsource' : (L + S) *
      pmfExp
        (classDependentNonpreemptivePriorityEventPMF arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))
        (fun event => classDependentNonpreemptivePriorityStateIndicator target
          (stepClassDependentNonpreemptivePriority empty event)) =
      L * pmfExp
        (classDependentNonpreemptivePriorityArrivalClassPMF
          arrivalRate harrivalRate htotalArrival)
        (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
          (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) +
      S * classDependentNonpreemptivePriorityStateIndicator target empty := by
    calc
      (L + S) * pmfExp
          (classDependentNonpreemptivePriorityEventPMF arrivalRate
            (exponentialServiceRate meanService) hn harrivalRate
            (exponentialServiceRate_pos meanService hmeanService))
          (fun event => classDependentNonpreemptivePriorityStateIndicator target
            (stepClassDependentNonpreemptivePriority empty event)) =
        (L + S) *
          ((L / (L + S)) * pmfExp
            (classDependentNonpreemptivePriorityArrivalClassPMF
              arrivalRate harrivalRate htotalArrival)
            (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
              (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) +
          (S / (L + S)) * classDependentNonpreemptivePriorityStateIndicator target empty) := by
            simpa [L, S, empty] using congrArg (fun x : ℝ => (L + S) * x) hsource
      _ = L * pmfExp
          (classDependentNonpreemptivePriorityArrivalClassPMF
            arrivalRate harrivalRate htotalArrival)
          (fun initialClass => classDependentNonpreemptivePriorityStateIndicator target
            (classDependentNonpreemptivePriorityArrivalInitialState initialClass)) +
          S * classDependentNonpreemptivePriorityStateIndicator target empty := by
            field_simp [ne_of_gt hR]
  exact hsource'

/-- The unnormalized complete-cycle occupation measure for the uniformized
embedded queue.  The busy-excursion count is weighted by the total arrival
rate, and the idle self-loop by the total offered event rate. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  ENNReal.ofReal (∑ i, arrivalRate i) •
    arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival +
  ENNReal.ofReal
      ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) •
    Measure.dirac (emptyNonpreemptivePriorityState n)

/-- A full regenerative cycle is invariant for the actual uniformized
embedded queue kernel.  This follows from exact busy-excursion flow and the
empty-state boundary flux, with no stationary distribution assumed. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_bind_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) =
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let B := arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let K := classDependentNonpreemptivePriorityMeasureKernel arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let μ := (classDependentNonpreemptivePriorityArrivalInitialStatePMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let empty := emptyNonpreemptivePriorityState n
  let L : ℝ := ∑ i, arrivalRate i
  let S : ℝ := ∑ i, exponentialServiceRate meanService i
  let l : ENNReal := ENNReal.ofReal L
  let s : ENNReal := ENNReal.ofReal S
  let r : ENNReal := ENNReal.ofReal (L + S)
  have hL : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro i _
    exact harrivalRate i
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i _
    exact (exponentialServiceRate_pos meanService hmeanService i).le
  have hr : r = l + s := by
    dsimp [r, l, s]
    exact ENNReal.ofReal_add hL hS
  have hbind_add (first second : Measure (NonpreemptivePriorityState n)) :
      (first + second).bind K = first.bind K + second.bind K := by
    apply Measure.ext
    intro set hset
    rw [Measure.bind_apply hset (Kernel.aemeasurable K), Measure.add_apply,
      Measure.bind_apply hset (Kernel.aemeasurable K),
      Measure.bind_apply hset (Kernel.aemeasurable K)]
    exact MeasureTheory.lintegral_add_measure _ _ _
  have hbusy : B.bind K + μ = B + Measure.dirac empty := by
    simpa [B, K, μ, empty] using
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_bind_add_arrivalInitialStatePMF_eq_add_dirac
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  have hempty : r • K empty = l • μ + s • Measure.dirac empty := by
    simpa [K, μ, empty, L, S, l, s, r] using
      (totalEventRate_smul_classDependentNonpreemptivePriorityMeasureKernel_empty_eq
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival)
  have hscaled : l • (B.bind K) + l • μ =
      l • B + l • Measure.dirac empty := by
    simpa only [smul_add] using congrArg (fun measure : Measure
      (NonpreemptivePriorityState n) => l • measure) hbusy
  have hcycleBind :
      (l • B + r • Measure.dirac empty).bind K =
        l • (B.bind K) + r • K empty := by
    rw [hbind_add, Measure.bind_smul, Measure.bind_smul,
      Measure.dirac_bind (Kernel.measurable K)]
  change (l • B + r • Measure.dirac empty).bind K = l • B + r • Measure.dirac empty
  calc
    (l • B + r • Measure.dirac empty).bind K =
        l • (B.bind K) + r • K empty := hcycleBind
    _ = l • (B.bind K) + (l • μ + s • Measure.dirac empty) := by rw [hempty]
    _ = (l • (B.bind K) + l • μ) + s • Measure.dirac empty := by ac_rfl
    _ = (l • B + l • Measure.dirac empty) + s • Measure.dirac empty := by rw [hscaled]
    _ = l • B + (l • Measure.dirac empty + s • Measure.dirac empty) := by ac_rfl
    _ = l • B + (l + s) • Measure.dirac empty := by rw [← add_smul]
    _ = l • B + r • Measure.dirac empty := by rw [hr]

/-- Under strict load the complete embedded regeneration-cycle occupation has
finite total mass. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_univ_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ ≠ ⊤ := by
  unfold arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _)]
  apply ENNReal.add_ne_top.mpr
  constructor
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.one_ne_top

/-- A complete embedded regeneration cycle has strictly positive total mass. -/
theorem zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ := by
  let L : ℝ := ∑ i, arrivalRate i
  let S : ℝ := ∑ i, exponentialServiceRate meanService i
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro i _
    exact (exponentialServiceRate_pos meanService hmeanService i).le
  have hR : 0 < L + S := add_pos_of_pos_of_nonneg (by simpa [L] using htotalArrival) hS
  unfold arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _)]
  have hpositive : 0 < ENNReal.ofReal (L + S) * 1 := by
    simpa using (ENNReal.ofReal_pos.mpr hR)
  apply lt_of_lt_of_le hpositive
  exact le_add_of_nonneg_left bot_le

/-- The normalized embedded regeneration-cycle law.  The preceding invariance
theorem makes this an actual stationary probability law for the uniformized
queue, constructed rather than postulated. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ)⁻¹ •
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival

/-- The normalized embedded regeneration-cycle law has total mass one. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ = 1 := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability,
    Measure.smul_apply]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_univ
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival))
    (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_univ_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The normalized complete-cycle law is invariant for the actual uniformized
priority-queue transition kernel. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_bind_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) =
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability,
    Measure.bind_smul,
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure_bind_eq
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable]

/-- The constructed embedded-cycle probability law is an invariant measure
in the standard Markov-kernel sense. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_invariant
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    Kernel.Invariant
      (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService))
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) := by
  exact arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_bind_eq
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- The normalized complete embedded-cycle law carries the standard
probability-measure structure. -/
theorem isProbabilityMeasure_arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    IsProbabilityMeasure
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) where
  measure_univ :=
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_univ
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- The product carrier for a fresh busy excursion: an arrival-rate sampled
initial class, independent uniformized event labels, and independent
exponential total-clock gaps. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure ((Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) ×
      (ℕ → ℝ)) :=
  (((classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure).prod
    (Probability.IIDStream.measure
      (classDependentNonpreemptivePriorityEventPMF arrivalRate
        (exponentialServiceRate meanService) hn harrivalRate
        (exponentialServiceRate_pos meanService hmeanService)).toMeasure)).prod
    (Probability.IIDStream.measure
      (ProbabilityTheory.expMeasure
        (classDependentNonpreemptivePriorityTotalEventRate arrivalRate
          (exponentialServiceRate meanService))))

/-- The physical time assigned to one embedded busy slot of the fresh
excursion.  It is zero once the idle-stopped trajectory has reached the empty
state. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    {n : ℕ} (horizon : ℕ) :
    ((Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) ×
      (ℕ → ℝ)) → ENNReal :=
  (Prod.fst ⁻¹' externalInitialClassDependentNonpreemptivePriorityBusyEvent
    classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
    (fun z => ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2))

/-- The density of one fresh-excursion occupation slot is measurable. -/
theorem measurable_arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    {n : ℕ} (horizon : ℕ) :
    Measurable (arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
      (n := n) horizon) := by
  exact Probability.IIDStream.measurable_externalWeightedENNRewardSummand
    (externalInitialClassDependentNonpreemptivePriorityBusyEvent
      classDependentNonpreemptivePriorityArrivalInitialState)
    ENNReal.ofReal
    (fun h =>
      measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
        (n := n) h)
    ENNReal.measurable_ofReal horizon

/-- The unnormalized contribution of one event slot to the occupation measure
of embedded queue states during a fresh busy excursion. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) (horizon : ℕ) :
    Measure (NonpreemptivePriorityState n) :=
  Measure.map
    (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon ∘ Prod.fst)
    ((arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).withDensity
      (arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity horizon))

/-- The unnormalized time-occupation measure of a complete fresh busy
excursion, summed over its embedded event slots. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  Measure.sum fun horizon =>
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon

/-- Independent exponential holding times scale every coordinate of the
fresh-busy occupation measure by their common mean.  This is an exact
finite-excursion Tonelli calculation; it identifies the physical occupation
measure with the embedded event occupation measure up to the uniformization
clock factor, without yet relating either law to a Palm construction. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_apply_singleton_eq_event_smul
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (target : NonpreemptivePriorityState n) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target} =
      ENNReal.ofReal (1 /
        classDependentNonpreemptivePriorityTotalEventRate arrivalRate
          (exponentialServiceRate meanService)) *
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target} := by
  classical
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let C : Measure (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
    ρ.prod (Probability.IIDStream.measure law.toMeasure)
  let rate : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let μ : Measure ℝ := ProbabilityTheory.expMeasure rate
  let E : ℕ → Set (Fin n × (ℕ → ClassDependentNonpreemptivePriorityEvent n)) :=
    fun horizon =>
      externalInitialClassDependentNonpreemptivePriorityBusyEvent
        classDependentNonpreemptivePriorityArrivalInitialState horizon ∩
      (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon) ⁻¹' {target}
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsProbabilityMeasure (Probability.IIDStream.measure law.toMeasure) := by
    dsimp [law, Probability.IIDStream.measure]
    infer_instance
  letI : IsProbabilityMeasure C := by
    dsimp [C]
    infer_instance
  have hrate : 0 < rate := by
    dsimp [rate]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact ProbabilityTheory.isProbabilityMeasure_expMeasure hrate
  have hE : ∀ horizon, MeasurableSet (E horizon) := by
    intro horizon
    exact (measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
      (n := n) horizon).inter
      ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
        (measurableSet_singleton target))
  have hgapNonnegative : ∀ᵐ x ∂μ, 0 ≤ x := by
    let exponentialModel : Probability.Exponential.Model := ⟨rate, hrate⟩
    simpa [μ, exponentialModel] using exponentialModel.ae_nonnegative
  have hgap : ∫⁻ x, ENNReal.ofReal x ∂μ = ENNReal.ofReal (1 / rate) := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (Probability.integrable_id_expMeasure hrate) hgapNonnegative,
      Probability.integral_id_expMeasure hrate]
  have hphysical :
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target} =
      ∫⁻ z, Probability.IIDStream.externalWeightedENNReward E ENNReal.ofReal z ∂
        (C.prod (Probability.IIDStream.measure μ)) := by
    rw [arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure,
      Measure.sum_apply _ (measurableSet_singleton target)]
    calc
      ∑' horizon,
          arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
            arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon {target} =
        ∑' horizon, ∫⁻ z,
          (Prod.fst ⁻¹' E horizon).indicator
            (fun z => ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2)) z ∂
          (C.prod (Probability.IIDStream.measure μ)) := by
            apply tsum_congr
            intro horizon
            rw [show arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
                arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon =
                Measure.map
                  (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon ∘ Prod.fst)
                  ((C.prod (Probability.IIDStream.measure μ)).withDensity
                    (arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity horizon)) by
                  rfl,
              Measure.map_apply
                ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
                  measurable_fst)
                (measurableSet_singleton target),
              withDensity_apply
                (arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity horizon)
                (((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
                  measurable_fst) (measurableSet_singleton target)),
              ← MeasureTheory.lintegral_indicator
                (((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
                  measurable_fst) (measurableSet_singleton target))]
            apply MeasureTheory.lintegral_congr
            intro z
            by_cases hbusy : z.1 ∈ externalInitialClassDependentNonpreemptivePriorityBusyEvent
                classDependentNonpreemptivePriorityArrivalInitialState horizon <;>
              by_cases htarget : arrivalInitialClassDependentNonpreemptivePriorityStateAt
                horizon z.1 = target
            · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity,
                hbusy, htarget]
            · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity,
                hbusy, htarget]
            · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity,
                hbusy, htarget]
            · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity,
                hbusy, htarget]
      _ = ∫⁻ z, ∑' horizon,
          (Prod.fst ⁻¹' E horizon).indicator
            (fun z => ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2)) z ∂
          (C.prod (Probability.IIDStream.measure μ)) := by
            symm
            exact MeasureTheory.lintegral_tsum fun horizon =>
              (Probability.IIDStream.measurable_externalWeightedENNRewardSummand E
                ENNReal.ofReal hE ENNReal.measurable_ofReal horizon).aemeasurable
      _ = ∫⁻ z, Probability.IIDStream.externalWeightedENNReward E ENNReal.ofReal z ∂
          (C.prod (Probability.IIDStream.measure μ)) := by rfl
  have hevent :
      arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival {target} =
      ∑' horizon, C (E horizon) := by
    rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure,
      Measure.sum_apply _ (measurableSet_singleton target)]
    calc
      ∑' horizon,
          arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
            arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon {target} =
        ∑' horizon, C (E horizon) := by
          apply tsum_congr
          intro horizon
          rw [show arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationSlotMeasure
              arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon =
              Measure.map (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
                (C.withDensity
                  (arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity horizon)) by
                rfl,
            Measure.map_apply (measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt
              horizon) (measurableSet_singleton target),
            withDensity_apply
              (arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity horizon)
              ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
                (measurableSet_singleton target)),
            ← MeasureTheory.lintegral_indicator
              ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon)
                (measurableSet_singleton target))]
          calc
            ∫⁻ z,
                (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon ⁻¹' {target}).indicator
                  (arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity horizon) z ∂C =
              ∫⁻ z, (E horizon).indicator (fun _ => (1 : ENNReal)) z ∂C := by
                apply MeasureTheory.lintegral_congr
                intro z
                by_cases hbusy : z ∈ externalInitialClassDependentNonpreemptivePriorityBusyEvent
                    classDependentNonpreemptivePriorityArrivalInitialState horizon <;>
                  by_cases htarget : arrivalInitialClassDependentNonpreemptivePriorityStateAt
                    horizon z = target
                · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity,
                    hbusy, htarget]
                · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity,
                    hbusy, htarget]
                · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity,
                    hbusy, htarget]
                · simp [E, arrivalInitialClassDependentNonpreemptivePriorityBusyEventSlotDensity,
                    hbusy, htarget]
            _ = C (E horizon) :=
              MeasureTheory.lintegral_indicator_one (hE horizon)
      _ = ∑' horizon, C (E horizon) := rfl
  rw [hphysical]
  rw [Probability.IIDStream.lintegral_externalWeightedENNReward C μ E
    ENNReal.ofReal hE ENNReal.measurable_ofReal, hgap, ← hevent]
  exact mul_comm _ _

/-- Independent exponential holding times scale the entire fresh-busy
occupation measure by the reciprocal uniformization rate. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_eq_event_smul
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ENNReal.ofReal (1 /
        classDependentNonpreemptivePriorityTotalEventRate arrivalRate
          (exponentialServiceRate meanService)) •
        arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  apply MeasureTheory.Measure.ext_of_singleton
  intro target
  rw [MeasureTheory.Measure.smul_apply,
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_apply_singleton_eq_event_smul]
  rfl

/-- The expected physical duration of a fresh arrival-start busy excursion. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) : ENNReal :=
  ∫⁻ z, externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime
    classDependentNonpreemptivePriorityArrivalInitialState z ∂
    arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival

/-- The total mass of the occupation measure is exactly the expected cycle
length.  This is a direct Tonelli equality, not an assumed invariant-law
normalization. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ =
    arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let C := arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    (n := n)
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  calc
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ =
      ∑' horizon,
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon Set.univ :=
      Measure.sum_apply _ MeasurableSet.univ
    _ = ∑' horizon, ∫⁻ z, density horizon z ∂C := by
      apply tsum_congr
      intro horizon
      change (Measure.map (state horizon ∘ Prod.fst)
        (C.withDensity (density horizon))) Set.univ = _
      rw [Measure.map_apply
        ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
          measurable_fst) MeasurableSet.univ]
      simp only [Set.preimage_univ]
      simpa only [setLIntegral_univ] using
        (withDensity_apply (density horizon) MeasurableSet.univ)
    _ = ∫⁻ z, ∑' horizon, density horizon z ∂C := by
      symm
      exact MeasureTheory.lintegral_tsum fun horizon =>
        (measurable_arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
          (n := n) horizon).aemeasurable
    _ = arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
      rfl

/-- Independent exponential holding times scale the total embedded busy
occupation by the reciprocal uniformization rate.  Thus the discrete
occupation layer and the physical-time layer have the same regenerative
boundary, differing only by this explicit clock factor. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      (arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ) *
        ENNReal.ofReal (1 /
          classDependentNonpreemptivePriorityTotalEventRate arrivalRate
            (exponentialServiceRate meanService)) := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure_univ]
  simpa [arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength,
    arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure,
    arrivalInitialClassDependentNonpreemptivePriorityEventCarrierMeasure, ρ] using
    (lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_eq
      ρ arrivalRate meanService hn harrivalRate hmeanService
      classDependentNonpreemptivePriorityArrivalInitialState
      (fun horizon =>
        measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon))

/-- Integrating a measurable nonnegative state observable under the raw
occupation measure is exactly summing its gap-weighted values over the fresh
excursion.  This is the transfer identity used to convert finite excursion
reward estimates into moments of the normalized occupation law. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (f : NonpreemptivePriorityState n → ENNReal) (hf : Measurable f) :
    ∫⁻ state, f state ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ∑' horizon, ∫⁻ z,
        arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity horizon z *
          f (arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon z.1) ∂
        arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let C := arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    (n := n)
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  calc
    ∫⁻ x, f x ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ∑' horizon, ∫⁻ x, f x ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationSlotMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival horizon := by
      exact lintegral_sum_measure f _
    _ = ∑' horizon, ∫⁻ z, f (state horizon z.1) ∂
        (C.withDensity (density horizon)) := by
      apply tsum_congr
      intro horizon
      change ∫⁻ x, f x ∂Measure.map (state horizon ∘ Prod.fst)
          (C.withDensity (density horizon)) = _
      simpa [Function.comp_def, state] using
        (lintegral_map hf
          ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
            measurable_fst))
    _ = ∑' horizon, ∫⁻ z,
        density horizon z * f (state horizon z.1) ∂C := by
      apply tsum_congr
      intro horizon
      simpa [Function.comp_def, density, state] using
        (lintegral_withDensity_eq_lintegral_mul C
          (measurable_arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
            (n := n) horizon)
          (hf.comp
            ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
              measurable_fst)))

/-- The occupation integral of the Lyapunov mean-work cost is exactly the
finite-start mean-work holding charge already controlled by the strict-load
drift estimate. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWorkCost_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    ∫⁻ state, ENNReal.ofReal
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ∫⁻ z,
        arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
          arrivalRate meanService z ∂
        arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let C := arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    (n := n)
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  let cost : NonpreemptivePriorityState n → ENNReal := fun s => ENNReal.ofReal
    (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService s)
  have hcost : Measurable cost :=
    (measurable_of_countable _).ennreal_ofReal
  calc
    ∫⁻ s, cost s ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ∑' horizon, ∫⁻ z, density horizon z * cost (state horizon z.1) ∂C := by
      simpa [cost] using
        (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival cost hcost)
    _ = ∫⁻ z, ∑' horizon, density horizon z * cost (state horizon z.1) ∂C := by
      symm
      exact MeasureTheory.lintegral_tsum fun horizon =>
        (measurable_arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
          (n := n) horizon).mul
          (hcost.comp
            ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
              measurable_fst)) |>.aemeasurable
    _ = ∫⁻ z,
        arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
          arrivalRate meanService z ∂C := by
      apply MeasureTheory.lintegral_congr
      intro z
      unfold arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge
        Probability.IIDStream.externalScaledENNReward
      apply tsum_congr
      intro horizon
      let s := state horizon z.1
      change
        ((Prod.fst ⁻¹' externalInitialClassDependentNonpreemptivePriorityBusyEvent
          classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
          (fun w => ENNReal.ofReal (Probability.IIDStream.coordinate horizon w.2)) z) *
          cost (state horizon z.1) =
        cost (state horizon z.1) *
          ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2)
      by_cases hidle : s.active = none
      · have houtside : z.1 ∉
            externalInitialClassDependentNonpreemptivePriorityBusyEvent
              classDependentNonpreemptivePriorityArrivalInitialState horizon := by
          change ¬ classDependentNonpreemptivePriorityBusy s
          simpa [classDependentNonpreemptivePriorityBusy] using hidle
        have hpre : z ∉ Prod.fst ⁻¹'
            externalInitialClassDependentNonpreemptivePriorityBusyEvent
              classDependentNonpreemptivePriorityArrivalInitialState horizon := houtside
        rw [Set.indicator_of_notMem hpre]
        have hs : (state horizon z.1).active = none := by
          simpa [s] using hidle
        have hcostzero : cost (state horizon z.1) = 0 := by
          simp [cost, classDependentNonpreemptivePriorityMeanWorkBusyCost, hs]
        rw [hcostzero]
        simp
      · have hinside : z.1 ∈
            externalInitialClassDependentNonpreemptivePriorityBusyEvent
              classDependentNonpreemptivePriorityArrivalInitialState horizon := by
          change classDependentNonpreemptivePriorityBusy s
          simpa [classDependentNonpreemptivePriorityBusy] using hidle
        have hpre : z ∈ Prod.fst ⁻¹'
            externalInitialClassDependentNonpreemptivePriorityBusyEvent
              classDependentNonpreemptivePriorityArrivalInitialState horizon := hinside
        rw [Set.indicator_of_mem hpre]
        exact mul_comm _ _

/-- Strict load gives a finite mean-work Lyapunov cost under the raw
regenerative occupation measure. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWorkCost_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  rw [lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWorkCost_eq
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival]
  exact lintegral_arrivalInitialClassDependentNonpreemptivePriorityMeanWorkBusyHoldingCharge_ne_top
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- On the occupation carrier, the positive strict-load Lyapunov coefficient
converts the controlled busy cost back to actual mean service work.  Idle
states contribute zero time, so no artificial relation is imposed on
unreachable malformed idle records. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ENNReal.ofReal (1 /
        (2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService)) *
        ∫⁻ state, ENNReal.ofReal
          (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state) ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let C := arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let density := arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
    (n := n)
  let state := arrivalInitialClassDependentNonpreemptivePriorityStateAt (n := n)
  let work : NonpreemptivePriorityState n → ENNReal := fun s => ENNReal.ofReal
    (nonpreemptivePriorityMeanWork meanService s)
  let cost : NonpreemptivePriorityState n → ENNReal := fun s => ENNReal.ofReal
    (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService s)
  let factor : ENNReal := ENNReal.ofReal (1 /
    (2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService))
  have hallowance : 0 < classDependentNonpreemptivePriorityBusyAllowance
      arrivalRate meanService :=
    classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  have htwo : 0 < 2 * classDependentNonpreemptivePriorityBusyAllowance
      arrivalRate meanService := mul_pos (by norm_num) hallowance
  have hfactorReal : 0 ≤ 1 /
      (2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) :=
    (one_div_pos.mpr htwo).le
  have hwork : Measurable work := (measurable_of_countable _).ennreal_ofReal
  have hcost : Measurable cost := (measurable_of_countable _).ennreal_ofReal
  have hpoint : ∀ horizon z,
      density horizon z * work (state horizon z.1) =
        factor * (density horizon z * cost (state horizon z.1)) := by
    intro horizon z
    let s := state horizon z.1
    change
      ((Prod.fst ⁻¹' externalInitialClassDependentNonpreemptivePriorityBusyEvent
        classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
        (fun w => ENNReal.ofReal (Probability.IIDStream.coordinate horizon w.2)) z) *
        work (state horizon z.1) =
      factor *
        (((Prod.fst ⁻¹' externalInitialClassDependentNonpreemptivePriorityBusyEvent
          classDependentNonpreemptivePriorityArrivalInitialState horizon).indicator
          (fun w => ENNReal.ofReal (Probability.IIDStream.coordinate horizon w.2)) z) *
          cost (state horizon z.1))
    by_cases hidle : s.active = none
    · have houtside : z.1 ∉
          externalInitialClassDependentNonpreemptivePriorityBusyEvent
            classDependentNonpreemptivePriorityArrivalInitialState horizon := by
        change ¬ classDependentNonpreemptivePriorityBusy s
        simpa [classDependentNonpreemptivePriorityBusy] using hidle
      have hpre : z ∉ Prod.fst ⁻¹'
          externalInitialClassDependentNonpreemptivePriorityBusyEvent
            classDependentNonpreemptivePriorityArrivalInitialState horizon := houtside
      rw [Set.indicator_of_notMem hpre]
      simp
    · have hinside : z.1 ∈
          externalInitialClassDependentNonpreemptivePriorityBusyEvent
            classDependentNonpreemptivePriorityArrivalInitialState horizon := by
        change classDependentNonpreemptivePriorityBusy s
        simpa [classDependentNonpreemptivePriorityBusy] using hidle
      have hpre : z ∈ Prod.fst ⁻¹'
          externalInitialClassDependentNonpreemptivePriorityBusyEvent
            classDependentNonpreemptivePriorityArrivalInitialState horizon := hinside
      rw [Set.indicator_of_mem hpre]
      have hcostScale : factor * cost (state horizon z.1) = work (state horizon z.1) := by
        dsimp [factor, cost, work]
        rw [← ENNReal.ofReal_mul hfactorReal]
        congr 1
        rw [show classDependentNonpreemptivePriorityMeanWorkBusyCost
            arrivalRate meanService (state horizon z.1) =
            2 * classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService *
              nonpreemptivePriorityMeanWork meanService (state horizon z.1) by
          simp [classDependentNonpreemptivePriorityMeanWorkBusyCost,
            show (state horizon z.1).active ≠ none by simpa [s] using hidle]]
        field_simp [ne_of_gt htwo]
      calc
        ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2) *
            work (state horizon z.1) =
          ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2) *
            (factor * cost (state horizon z.1)) := by rw [hcostScale]
        _ = factor * (ENNReal.ofReal (Probability.IIDStream.coordinate horizon z.2) *
            cost (state horizon z.1)) := by ac_rfl
  calc
    ∫⁻ s, work s ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ∑' horizon, ∫⁻ z, density horizon z * work (state horizon z.1) ∂C := by
      simpa [work] using
        (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival work hwork)
    _ = ∑' horizon, ∫⁻ z,
        factor * (density horizon z * cost (state horizon z.1)) ∂C := by
      apply tsum_congr
      intro horizon
      exact MeasureTheory.lintegral_congr fun z => hpoint horizon z
    _ = ∑' horizon, factor * ∫⁻ z,
        density horizon z * cost (state horizon z.1) ∂C := by
      apply tsum_congr
      intro horizon
      simpa [Function.comp_def, density, state] using
        (lintegral_const_mul factor
          ((measurable_arrivalInitialClassDependentNonpreemptivePriorityBusySlotDensity
            (n := n) horizon).mul
            (hcost.comp
              ((measurable_arrivalInitialClassDependentNonpreemptivePriorityStateAt horizon).comp
                measurable_fst))))
    _ = factor * ∑' horizon, ∫⁻ z,
        density horizon z * cost (state horizon z.1) ∂C := ENNReal.tsum_mul_left
    _ = factor * ∫⁻ s, cost s ∂
        arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
      rw [lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival cost hcost]

/-- The regenerative occupation measure has a finite first mean-work moment
under strict total load. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  rw [lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_eq
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWorkCost_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- Each individual class population has a finite first occupation moment on
a strict-load fresh busy excursion.  The result follows from the deterministic
class-work bound, so it adds no stationarity assumption to the regenerative
occupation construction. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationClassJobs_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∫⁻ state, ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let occupation := arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let work : NonpreemptivePriorityState n → ENNReal := fun state =>
    ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state)
  let jobs : NonpreemptivePriorityState n → ENNReal := fun state =>
    ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ)
  let scale : ENNReal := (ENNReal.ofReal (meanService i))⁻¹
  have hmeanPos : 0 < meanService i := hmeanService i
  have hworkMeasurable : Measurable work := (measurable_of_countable _).ennreal_ofReal
  have hpoint : ∀ state, jobs state ≤ scale * work state := by
    intro state
    have hreal : (classNonpreemptivePriorityJobs state i : ℝ) ≤
        nonpreemptivePriorityMeanWork meanService state / meanService i := by
      apply (le_div_iff₀ hmeanPos).mpr
      simpa [mul_comm] using
        (meanService_mul_classNonpreemptivePriorityJobs_le_meanWork meanService
          (fun j => (hmeanService j).le) state i)
    calc
      jobs state ≤ ENNReal.ofReal
          (nonpreemptivePriorityMeanWork meanService state / meanService i) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = scale * work state := by
        rw [div_eq_mul_inv,
          ENNReal.ofReal_mul
            (nonpreemptivePriorityMeanWork_nonneg meanService
              (fun j => (hmeanService j).le) state),
          ENNReal.ofReal_inv_of_pos hmeanPos]
        simp [scale, work, mul_comm]
  have hworkFinite : ∫⁻ state, work state ∂occupation ≠ ⊤ := by
    simpa [occupation, work] using
      (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  have hupper : ∫⁻ state, jobs state ∂occupation ≤
      scale * ∫⁻ state, work state ∂occupation := by
    calc
      ∫⁻ state, jobs state ∂occupation ≤ ∫⁻ state, scale * work state ∂occupation := by
        apply MeasureTheory.lintegral_mono
        intro state
        exact hpoint state
      _ = scale * ∫⁻ state, work state ∂occupation :=
        MeasureTheory.lintegral_const_mul scale hworkMeasurable
  have hmeanENN : ENNReal.ofReal (meanService i) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr hmeanPos
  have hscaleFinite : scale ≠ ⊤ := ENNReal.inv_ne_top.mpr hmeanENN
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hscaleFinite hworkFinite)
  simpa [occupation, jobs] using hupper

/-- Strict load makes the fresh-cycle normalizer finite. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  simpa [arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength,
    arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure, ρ] using
    (lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_ne_top
      ρ arrivalRate meanService hn harrivalRate hmeanService hstable
      classDependentNonpreemptivePriorityArrivalInitialState
      measurable_arrivalInitial_classDependentNonpreemptivePriorityBusyEventCount
      (fun horizon =>
        measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon)
      (by
        simpa [ρ] using
          lintegral_arrivalInitial_meanWork_div_busyAllowance_ne_top
            arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable))

/-- A fresh busy cycle has strictly positive expected physical duration. -/
theorem zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let ρ := (classDependentNonpreemptivePriorityArrivalClassPMF
    arrivalRate harrivalRate htotalArrival).toMeasure
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  simpa [arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength,
    arrivalInitialClassDependentNonpreemptivePriorityCarrierMeasure, ρ] using
    (zero_lt_lintegral_externalInitialClassDependentNonpreemptivePriorityBusyHoldingTime_of_active
      ρ arrivalRate meanService hn harrivalRate hmeanService
      classDependentNonpreemptivePriorityArrivalInitialState
      (fun i => classDependentNonpreemptivePriorityArrivalInitialState_active i)
      (fun horizon =>
        measurableSet_arrivalInitial_classDependentNonpreemptivePriorityBusyEvent
          (n := n) horizon))

/-- The normalized occupation law conditional on being inside a fresh busy
excursion.  It intentionally omits the idle holding interval, so it is not
claimed to be the stationary queue law. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  (arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival)⁻¹ •
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival

/-- Under strict load the normalized busy-excursion occupation measure has
total mass one. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ = 1 := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability,
    Measure.smul_apply, arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_univ]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival))
    (arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The Lyapunov mean-work cost remains integrable after the finite positive
cycle occupation measure is normalized to a probability law. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbabilityMeanWorkCost_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal
        (classDependentNonpreemptivePriorityMeanWorkBusyCost arrivalRate meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability,
    lintegral_smul_measure]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival)))
    (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWorkCost_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The normalized regenerative occupation law has finite first mean service
work under strict total load. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbabilityMeanWork_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationProbability,
    lintegral_smul_measure]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival)))
    (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The expected idle holding time before the first arrival of a regeneration
cycle.  It is kept separate from the busy excursion because the server has a
different event clock while empty. -/
noncomputable def classDependentNonpreemptivePriorityIdleCycleLength
    {n : ℕ} (arrivalRate : Fin n → ℝ) : ENNReal :=
  ENNReal.ofReal (1 / ∑ i, arrivalRate i)

/-- The full regenerative occupation measure includes both the fresh busy
excursion and the idle interval preceding its first arrival.  This is the
correct candidate for a stationary time-occupation law; the busy-only law
above is intentionally only conditional on non-idleness. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival +
    classDependentNonpreemptivePriorityIdleCycleLength arrivalRate •
      Measure.dirac (emptyNonpreemptivePriorityState n)

/-- The complete physical-time regeneration occupation is the embedded
event-cycle occupation scaled by the reciprocal product of the arrival and
uniformization rates.  Thus the two cycle constructions have the same
normalization; this is still a statement about the constructed regenerative
law, not an identification with a selected Palm state. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure_eq_event_smul
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
      ENNReal.ofReal (1 / ((∑ i, arrivalRate i) *
        classDependentNonpreemptivePriorityTotalEventRate arrivalRate
          (exponentialServiceRate meanService))) •
        arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  classical
  let L : ℝ := ∑ i, arrivalRate i
  let R : ℝ := classDependentNonpreemptivePriorityTotalEventRate arrivalRate
    (exponentialServiceRate meanService)
  let B := arrivalInitialClassDependentNonpreemptivePriorityBusyEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let empty := emptyNonpreemptivePriorityState n
  have hL : 0 < L := by
    simpa [L] using htotalArrival
  have hR : 0 < R := by
    dsimp [R]
    exact classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  have hRdef : R = L + ∑ i, exponentialServiceRate meanService i := by
    simp [R, L, classDependentNonpreemptivePriorityTotalEventRate_eq]
  have hscaleBusy : ENNReal.ofReal (1 / R) =
      ENNReal.ofReal (1 / (L * R)) * ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt hL, ne_of_gt hR]
  have hscaleIdle : ENNReal.ofReal (1 / L) =
      ENNReal.ofReal (1 / (L * R)) * ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [ne_of_gt hL, ne_of_gt hR]
  apply MeasureTheory.Measure.ext_of_singleton
  intro target
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure,
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_apply_singleton_eq_event_smul]
  rw [← hRdef]
  change ENNReal.ofReal (1 / R) * B {target} +
      ENNReal.ofReal (1 / L) * Measure.dirac empty {target} =
    ENNReal.ofReal (1 / (L * R)) *
      (ENNReal.ofReal L * B {target} + ENNReal.ofReal R * Measure.dirac empty {target})
  rw [hscaleBusy, hscaleIdle]
  ring

/-- The expected physical duration of one complete empty-to-empty regeneration
cycle. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) : ENNReal :=
  arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival +
    classDependentNonpreemptivePriorityIdleCycleLength arrivalRate

/-- The full-cycle occupation mass is exactly its busy duration plus its
idle holding duration. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ =
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  simp [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure,
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength,
    arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeasure_univ]

/-- A complete cycle has strictly positive expected length. -/
theorem zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    0 < arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  exact add_pos_of_pos_of_nonneg
    (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival)
    bot_le

/-- Strict load makes the complete regeneration-cycle duration finite. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  exact ENNReal.add_ne_top.mpr ⟨
    arrivalInitialClassDependentNonpreemptivePriorityBusyCycleLength_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable,
    ENNReal.ofReal_ne_top⟩

/-- The normalized full-cycle occupation law.  This is a concrete probability
measure constructed from regeneration.  Its invariance for the uniformized
queue kernel follows below by comparison with the embedded event-cycle law;
identification with the remote-past Palm realization remains a separate
coupling theorem. -/
noncomputable def arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    Measure (NonpreemptivePriorityState n) :=
  (arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival)⁻¹ •
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival

private theorem ennreal_inv_mul_right_of_ne_zero_ne_top
    {d m : ENNReal} (hd0 : d ≠ 0) (hdtop : d ≠ ⊤) :
    (d * m)⁻¹ * d = m⁻¹ := by
  rcases eq_or_ne m 0 with rfl | hm0
  · rw [mul_zero, ENNReal.inv_zero]
    exact ENNReal.top_mul hd0
  rcases eq_or_ne m ⊤ with rfl | hmtop
  · simp [hd0]
  lift d to NNReal using hdtop
  lift m to NNReal using hmtop
  have hd0' : d ≠ 0 := by exact_mod_cast hd0
  have hm0' : m ≠ 0 := by exact_mod_cast hm0
  rw [← ENNReal.coe_mul, ← ENNReal.coe_inv (mul_ne_zero hd0' hm0'),
    ← ENNReal.coe_mul, ← ENNReal.coe_inv hm0']
  norm_cast
  field_simp

/-- The normalized physical-time and embedded-event regeneration cycles are
the same probability law.  This transfers the already-proved embedded-kernel
invariance to the physical-time normalization, but does not identify that
constructed law with a marked-Poisson Palm realization. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_eq_event
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival =
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  let d : ENNReal := ENNReal.ofReal (1 / ((∑ i, arrivalRate i) *
    classDependentNonpreemptivePriorityTotalEventRate arrivalRate
      (exponentialServiceRate meanService)))
  let M := arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationMeasure
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  have hL : 0 < ∑ i, arrivalRate i := htotalArrival
  have hR : 0 < classDependentNonpreemptivePriorityTotalEventRate arrivalRate
      (exponentialServiceRate meanService) :=
    classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
  have hd0 : d ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (one_div_pos.mpr (mul_pos hL hR)))
  have hdtop : d ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasure :
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival = d • M := by
    simpa [d, M] using
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure_eq_event_smul
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  have hlength :
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival = d * M Set.univ := by
    rw [← arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure_univ,
      hmeasure, Measure.smul_apply]
    rfl
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability,
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability,
    hlength, hmeasure, smul_smul]
  change ((d * M Set.univ)⁻¹ * d) • M = (M Set.univ)⁻¹ • M
  exact congrArg (fun scalar : ENNReal => scalar • M)
    (ennreal_inv_mul_right_of_ne_zero_ne_top hd0 hdtop)

/-- The constructed physical-time regeneration law is invariant for the
uniformized class-dependent priority kernel.  The statement concerns the
constructed regenerative law only; the separate marked-Poisson/Palm coupling
is still required before applying it to the paper's selected arrival. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_bind_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival).bind
        (classDependentNonpreemptivePriorityMeasureKernel arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService)) =
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_eq_event]
  exact arrivalInitialClassDependentNonpreemptivePriorityFullCycleEventOccupationProbability_bind_eq
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- The normalized full-cycle occupation law has total mass one. -/
theorem arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_univ
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival Set.univ = 1 := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability,
    Measure.smul_apply,
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure_univ]
  exact ENNReal.inv_mul_cancel
    (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival))
    (arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- The normalized physical full-cycle occupation law is a probability
measure.  Its stationarity/Palm realization remains a separate construction;
this theorem records only the normalization justified by the finite cycle. -/
theorem isProbabilityMeasure_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    IsProbabilityMeasure
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) where
  measure_univ :=
    arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_univ
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- The complete-cycle occupation measure has finite first mean service work;
the added idle interval contributes zero work. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeanWork_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let work : NonpreemptivePriorityState n → ENNReal := fun state => ENNReal.ofReal
    (nonpreemptivePriorityMeanWork meanService state)
  have hwork : Measurable work := (measurable_of_countable _).ennreal_ofReal
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure,
    lintegral_add_measure]
  apply ENNReal.add_ne_top.mpr
  constructor
  · simpa [work] using
      (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationMeanWork_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)
  · rw [lintegral_smul_measure, lintegral_dirac
      (emptyNonpreemptivePriorityState n) work]
    simp [work, nonpreemptivePriorityMeanWork_empty]

/-- The full empty-to-empty cycle also has a finite first occupation moment
for each class population.  The idle component is the literal empty state and
therefore contributes zero. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationClassJobs_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∫⁻ state, ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ) ∂
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let jobs : NonpreemptivePriorityState n → ENNReal := fun state =>
    ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ)
  have hjobsMeasurable : Measurable jobs := (measurable_of_countable _).ennreal_ofReal
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeasure,
    lintegral_add_measure]
  apply ENNReal.add_ne_top.mpr
  constructor
  · simpa [jobs] using
      (lintegral_arrivalInitialClassDependentNonpreemptivePriorityBusyOccupationClassJobs_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable i)
  · rw [lintegral_smul_measure, lintegral_dirac
      (emptyNonpreemptivePriorityState n) jobs]
    simp [jobs, classNonpreemptivePriorityJobs]

/-- The concrete full-cycle occupation probability has finite first mean
service work. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityMeanWork_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal (nonpreemptivePriorityMeanWork meanService state) ∂
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability,
    lintegral_smul_measure]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival)))
    (lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationMeanWork_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable)

/-- Normalizing the full finite regeneration cycle preserves the finite first
occupation moment of every class population. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityClassJobs_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∫⁻ state, ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ) ∂
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let jobs : NonpreemptivePriorityState n → ENNReal := fun state =>
    ENNReal.ofReal (classNonpreemptivePriorityJobs state i : ℝ)
  have hjobsMeasurable : Measurable jobs := (measurable_of_countable _).ennreal_ofReal
  rw [arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability,
    lintegral_smul_measure]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (ne_of_gt
      (zero_lt_arrivalInitialClassDependentNonpreemptivePriorityFullCycleLength
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival)))
    (by simpa [jobs] using
      (lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationClassJobs_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable i))

/-- The normalized physical regeneration-cycle law has an integrable first
mean-work moment.  This is the real-valued form of the preceding Lyapunov
bound, suitable for transport through a later stationary/Palm identification.
It does not yet claim that the law is the selected-arrival Palm state. -/
theorem integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    Integrable (nonpreemptivePriorityMeanWork meanService)
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_of_countable _).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun state =>
      nonpreemptivePriorityMeanWork_nonneg meanService
        (fun j => (hmeanService j).le) state)).mp
  exact
    lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityMeanWork_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable

/-- Adding one class-`i` arrival to a state drawn from the constructed
regeneration law preserves the first mean-work moment.  This is the
post-arrival initial-state bound needed when a tagged customer is studied
against an independent future event clock. -/
theorem integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork_afterArrival
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    Integrable
      (fun state : NonpreemptivePriorityState n =>
        nonpreemptivePriorityMeanWork meanService
          (stepClassDependentNonpreemptivePriority state (.inl i)))
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) := by
  letI : IsProbabilityMeasure
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) :=
    isProbabilityMeasure_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable
  simpa [nonpreemptivePriorityMeanWork_stepClassDependent_arrival] using
    (integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable).add
      (integrable_const (meanService i))

/-- The Lyapunov-normalized initial-work quantity is integrable under the
constructed physical regeneration law.  This is exactly the input required
by the random-initial-state busy-period theorem. -/
theorem lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork_div_busyAllowance_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ state, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService state /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂
      arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival ≠ ⊤ := by
  let π := arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let allowance := classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService
  let f : NonpreemptivePriorityState n → ℝ := fun state =>
    nonpreemptivePriorityMeanWork meanService state / allowance
  have hallowance : 0 < allowance := by
    exact classDependentNonpreemptivePriorityBusyAllowance_pos
      arrivalRate meanService hn harrivalRate hmeanService hstable
  have hnonnegative : 0 ≤ᶠ[ae π] f := Filter.Eventually.of_forall fun state => by
    dsimp [f]
    exact div_nonneg
      (nonpreemptivePriorityMeanWork_nonneg meanService
        (fun j => (hmeanService j).le) state)
      hallowance.le
  have hintegrable : Integrable f π := by
    simpa [f, allowance] using
      (integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable).div_const
          allowance
  change ∫⁻ state, ENNReal.ofReal (f state) ∂π ≠ ⊤
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegrable hnonnegative]
  exact ENNReal.ofReal_ne_top

/-- From a state sampled from the constructed physical regeneration law, an
independent literal exponential event race reaches the empty state in finite
expected busy holding time.  The product carrier is explicit: this is a
finite-start continuation theorem, not an identification with the two-sided
Palm construction. -/
theorem lintegral_externalInitial_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityEventRaceBusyHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
        (id : NonpreemptivePriorityState n → NonpreemptivePriorityState n) z ∂
      ((arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival).prod
        (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))) ≠ ⊤ := by
  let π := arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  letI : IsProbabilityMeasure π :=
    isProbabilityMeasure_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable
  have hcount : Measurable (fun z : NonpreemptivePriorityState n ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount z.1 z.2) := by
    simpa [classDependentNonpreemptivePriorityBusyEventCount] using
      (Probability.IIDStream.measurable_externalInitial_finiteEventTrajectoryEventCount_of_countable
        (id : NonpreemptivePriorityState n → NonpreemptivePriorityState n)
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy)
  have hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent
        (id : NonpreemptivePriorityState n → NonpreemptivePriorityState n) horizon) := by
    intro horizon
    simpa [externalInitialClassDependentNonpreemptivePriorityBusyEvent] using
      (Probability.IIDStream.measurableSet_externalInitialFiniteEventTrajectoryEventSet_of_countable
        (id : NonpreemptivePriorityState n → NonpreemptivePriorityState n)
        stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon)
  simpa [π] using
    (lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
      π arrivalRate meanService hn harrivalRate hmeanService hstable
      (id : NonpreemptivePriorityState n → NonpreemptivePriorityState n)
      hcount hbusy
      (lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork_div_busyAllowance_ne_top
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable))

/-- If a stationary regenerative state first receives one class-`i` arrival,
then its independent future exponential event race has finite expected busy
holding time under strict load.  The result is a finite-moment statement for
the constructed stationary Markov queue; identifying it with a particular
Palm input realization is a separate coupling theorem. -/
theorem lintegral_externalInitial_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityAfterArrivalEventRaceBusyHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
        (fun state => stepClassDependentNonpreemptivePriority state (.inl i)) z ∂
      ((arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival).prod
        (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))) ≠ ⊤ := by
  let π := arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
    arrivalRate meanService hn harrivalRate hmeanService htotalArrival
  let initial : NonpreemptivePriorityState n → NonpreemptivePriorityState n :=
    fun state => stepClassDependentNonpreemptivePriority state (.inl i)
  letI : IsProbabilityMeasure π :=
    isProbabilityMeasure_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable
  have hcount : Measurable (fun z : NonpreemptivePriorityState n ×
      (ℕ → ClassDependentNonpreemptivePriorityEvent n) =>
      classDependentNonpreemptivePriorityBusyEventCount (initial z.1) z.2) := by
    simpa [classDependentNonpreemptivePriorityBusyEventCount] using
      (Probability.IIDStream.measurable_externalInitial_finiteEventTrajectoryEventCount_of_countable
        initial stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy)
  have hbusy : ∀ horizon, MeasurableSet
      (externalInitialClassDependentNonpreemptivePriorityBusyEvent initial horizon) := by
    intro horizon
    simpa [externalInitialClassDependentNonpreemptivePriorityBusyEvent] using
      (Probability.IIDStream.measurableSet_externalInitialFiniteEventTrajectoryEventSet_of_countable
        initial stopAtIdleClassDependentNonpreemptivePriorityStep
        classDependentNonpreemptivePriorityBusy horizon)
  have hinitial : ∫⁻ state, ENNReal.ofReal
      (nonpreemptivePriorityMeanWork meanService (initial state) /
        classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService) ∂π ≠ ⊤ := by
    let allowance := classDependentNonpreemptivePriorityBusyAllowance arrivalRate meanService
    let f : NonpreemptivePriorityState n → ℝ := fun state =>
      nonpreemptivePriorityMeanWork meanService (initial state) / allowance
    have hallowance : 0 < allowance :=
      classDependentNonpreemptivePriorityBusyAllowance_pos
        arrivalRate meanService hn harrivalRate hmeanService hstable
    have hnonnegative : 0 ≤ᶠ[ae π] f := Filter.Eventually.of_forall fun state => by
      dsimp [f]
      exact div_nonneg
        (nonpreemptivePriorityMeanWork_nonneg meanService
          (fun j => (hmeanService j).le) (initial state))
        hallowance.le
    have hintegrable : Integrable f π := by
      simpa [f, allowance] using
        (integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_meanWork_afterArrival
          arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable i).div_const
          allowance
    change ∫⁻ state, ENNReal.ofReal (f state) ∂π ≠ ⊤
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintegrable hnonnegative]
    exact ENNReal.ofReal_ne_top
  simpa [π, initial] using
    (lintegral_externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime_ne_top
      π arrivalRate meanService hn harrivalRate hmeanService hstable initial hcount hbusy hinitial)

/-- In the constructed stationary class-dependent queue, the physical holding
time of one newly admitted tagged class-`i` customer has finite expectation.
The result uses the tagged-customer busy-period domination and the preceding
post-arrival busy-time bound.  It remains a statement about the constructed
regenerative event-race model; a separate Palm coupling is needed before this
is the response moment of the paper's literal selected arrival. -/
theorem lintegral_externalInitial_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityAfterArrivalEventRaceTagHoldingTime_ne_top
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    ∫⁻ z,
      externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime
        (fun state => admitClassDependentNonpreemptivePriorityTag state i) z ∂
      ((arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival).prod
        (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate
          (exponentialServiceRate meanService) hn harrivalRate
          (exponentialServiceRate_pos meanService hmeanService))) ≠ ⊤ := by
  have hpointwise : ∀ z : NonpreemptivePriorityState n ×
      (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n),
      externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime
          (fun state => admitClassDependentNonpreemptivePriorityTag state i) z ≤
        externalInitialClassDependentNonpreemptivePriorityEventRaceBusyHoldingTime
          (fun state => stepClassDependentNonpreemptivePriority state (.inl i)) z := by
    intro z
    simpa [externalInitialClassDependentNonpreemptivePriorityEventRaceTagHoldingTime,
      admitClassDependentNonpreemptivePriorityTag,
      stepClassDependentNonpreemptivePriorityTag_queue] using
      (classDependentNonpreemptivePriorityEventRaceTagHoldingTime_le_busyHoldingTime
        (admitClassDependentNonpreemptivePriorityTag z.1 i)
        (classDependentNonpreemptivePriorityTagValid_admit z.1 i) z.2)
  exact ne_top_of_le_ne_top
    (lintegral_externalInitial_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityAfterArrivalEventRaceBusyHoldingTime_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable i)
    (MeasureTheory.lintegral_mono hpointwise)

/-- Every class population is integrable under the normalized physical
regeneration-cycle law.  Like the mean-work version, this is a constructed
regenerative fact and awaits a proved connection to the literal Palm state
before it is used as a selected-arrival moment. -/
theorem integrable_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability_classJobs
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (htotalArrival : 0 < ∑ i, arrivalRate i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (i : Fin n) :
    Integrable (fun state : NonpreemptivePriorityState n =>
      (classNonpreemptivePriorityJobs state i : ℝ))
      (arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbability
        arrivalRate meanService hn harrivalRate hmeanService htotalArrival) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_of_countable _).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => Nat.cast_nonneg _)).mp
  exact
    lintegral_arrivalInitialClassDependentNonpreemptivePriorityFullCycleOccupationProbabilityClassJobs_ne_top
      arrivalRate meanService hn harrivalRate hmeanService htotalArrival hstable i

end

end AppliedModelingLib.Queueing
