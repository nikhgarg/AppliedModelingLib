import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedMeanWorkTerms
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastStateMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryTimeTranslation
import AppliedModelingLib.Foundations.Probability.MulticlassStationaryPoissonJointObservables

/-!
# Stationary state components for finite nonpreemptive-priority queues

The active residual and priority-filtered waiting work are named as concrete
observables of the causal stationary remote-past state.  Their distributional
Palm transport is developed from finite replays in this module.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- Residual work in service at a stationary time origin. -/
noncomputable def stationaryPriorityRemotePastActiveResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) : ℝ :=
  activeNonpreemptivePriorityResidualWork
    (stationaryPriorityRemotePastState meanService omega)

/-- Work already waiting in classes at least as urgent as `i` at a stationary
time origin. -/
noncomputable def stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (omega : Fin n → StationaryPoissonWorkPath) : ℝ :=
  priorityWaitingResidualWorkAtLeastAsUrgent
    (stationaryPriorityRemotePastState meanService omega) i

/-- The squared residual-work ledger of the literal stationary remote-past
state. -/
noncomputable def stationaryPriorityRemotePastSquaredResidualWork
    {n : ℕ} (meanService : Fin n → ℝ)
    (omega : Fin n → StationaryPoissonWorkPath) : ℝ :=
  totalNonpreemptivePrioritySquaredResidualWork
    (stationaryPriorityRemotePastState meanService omega)

/-- The finite stationary active residual stabilizes to the corresponding
causal remote-past observable under strict total load. -/
theorem ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
          stationaryPriorityRemotePastActiveResidualWork meanService omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  change activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityRemotePastState meanService omega)
  unfold activeNonpreemptivePriorityResidualWork
  rw [(hcoalesces (horizon : ℝ) (hceil.trans hcast)).2.1]

/-- The finite stationary active residual also stabilizes along arbitrary
real-valued remote-past horizons.  This is the form needed when a finite
time occupation is reindexed by its continuously varying elapsed horizon. -/
theorem ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_real_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℝ in Filter.atTop,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
          stationaryPriorityRemotePastActiveResidualWork meanService omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨cutoff, ?_⟩
  intro horizon hhorizon
  change activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) =
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityRemotePastState meanService omega)
  unfold activeNonpreemptivePriorityResidualWork
  rw [(hcoalesces horizon hhorizon).2.1]

/-- The finite stationary urgent-waiting work stabilizes to the corresponding
causal remote-past observable under strict total load. -/
theorem ae_eventually_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (i : Fin n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) i =
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService i omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  change priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) i =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityRemotePastState meanService omega) i
  unfold priorityWaitingResidualWorkAtLeastAsUrgent priorityWaitingResidualWork
  rw [(hcoalesces (horizon : ℝ) (hceil.trans hcast)).2.2]

/-- The finite stationary urgent-waiting work also stabilizes along arbitrary
real-valued remote-past horizons.  This is the form needed when finite-time
waiting occupations are reindexed by their continuously varying elapsed
past horizon. -/
theorem ae_eventually_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_real_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℝ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) selected =
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨cutoff, ?_⟩
  intro horizon hhorizon
  change priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) selected =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityRemotePastState meanService omega) selected
  exact priorityWaitingResidualWorkAtLeastAsUrgent_eq_of_liveEquivalent
    (hcoalesces horizon hhorizon) selected

/-- The finite stationary squared residual ledger stabilizes to the squared
ledger of the literal causal remote-past state under strict total load. -/
theorem ae_eventually_stationaryPriorityFiniteWindowSquaredResidualWork_eq_remotePast
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        totalNonpreemptivePrioritySquaredResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
          stationaryPriorityRemotePastSquaredResidualWork meanService omega := by
  filter_upwards [ae_exists_stationaryPriorityRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable] with omega hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  change totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) =
      totalNonpreemptivePrioritySquaredResidualWork
        (stationaryPriorityRemotePastState meanService omega)
  exact totalNonpreemptivePrioritySquaredResidualWork_eq_of_liveEquivalent
    (hcoalesces (horizon : ℝ) (hceil.trans hcast))

/-- The stationary active residual is almost-everywhere measurable, using the
finite PASTA replay laws as measurable finite representatives. -/
theorem aemeasurable_stationaryPriorityRemotePastActiveResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    AEMeasurable (stationaryPriorityRemotePastActiveResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  apply Probability.aemeasurable_response_of_ae_eventually_eq_aemeasurable
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun horizon omega => activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0))
    (stationaryPriorityRemotePastActiveResidualWork meanService)
  · intro horizon
    exact (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable
  · exact ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_eq_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable

/-- The stationary urgent-waiting component is almost-everywhere measurable,
using the finite PASTA replay laws as measurable finite representatives. -/
theorem aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1) (i : Fin n) :
    AEMeasurable (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService i)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  apply Probability.aemeasurable_response_of_ae_eventually_eq_aemeasurable
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun horizon omega => priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) i)
    (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService i)
  · intro horizon
    exact (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate i (horizon : ℝ)).aemeasurable
  · exact
      ae_eventually_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable i

/-- The stationary remote-past squared residual ledger is almost-everywhere
measurable, obtained from its finite strict-past representatives. -/
theorem aemeasurable_stationaryPriorityRemotePastSquaredResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    AEMeasurable (stationaryPriorityRemotePastSquaredResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  apply Probability.aemeasurable_response_of_ae_eventually_eq_aemeasurable
    (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
    (fun horizon omega => totalNonpreemptivePrioritySquaredResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0))
    (stationaryPriorityRemotePastSquaredResidualWork meanService)
  · intro horizon
    exact (stationaryPriorityFiniteWindowSquaredResidualWork_hasLaw_canonicalPast
      arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable
  · exact ae_eventually_stationaryPriorityFiniteWindowSquaredResidualWork_eq_remotePast
      arrivalRate meanService harrivalRate hmeanService hstable

/-- At any fixed physical time, sufficiently remote empty-start replays
coalesce in their active residual with the literal remote-past state viewed
through the stationary input flow. -/
theorem ae_eventually_activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState_at_eq_remotePast_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (t : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) =
          stationaryPriorityRemotePastActiveResidualWork meanService
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow (Class := Fin n)
  have hflow : MeasurePreserving (flow t) P P := by
    exact Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
      arrivalRate harrivalRate t
  have hcoalesces : ∀ᵐ omega ∂P,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService (flow t omega) (-older) 0)
          (stationaryPriorityRemotePastState meanService (flow t omega)) := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := flow t) (p := fun eta =>
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService eta (-older) 0)
          (stationaryPriorityRemotePastState meanService eta)) hflow.measurable.aemeasurable ?_
    rw [hflow.map_eq]
    exact ae_exists_stationaryPriorityRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable
  have htied : ∀ᵐ omega ∂P, ∀ horizon : ℕ,
      ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) t),
        ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) t),
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              first.1 omega first.2 =
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              second.1 omega second.2 → first = second := by
    rw [ae_all_iff]
    intro horizon
    exact ae_stationaryPriorityArrivalWindow_noArrivalTies
      arrivalRate harrivalRate (-(horizon : ℝ)) t
  filter_upwards [hcoalesces, htied] with omega hcoalescesOmega htiedOmega
  rcases hcoalescesOmega with ⟨cutoff, hcutoffNonneg, hcoalescesOmega⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil (cutoff - t), ?_⟩
  intro horizon hhorizon
  have hceil : cutoff - t ≤ (Nat.ceil (cutoff - t) : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil (cutoff - t) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have holder : cutoff ≤ (horizon : ℝ) + t := by linarith
  have hactive := activeNonpreemptivePriorityResidualWork_eq_of_liveEquivalent
    (hcoalescesOmega ((horizon : ℝ) + t) holder)
  have htranslate :=
    activeNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindow_flow
      meanService omega t (-(horizon : ℝ)) t (htiedOmega horizon)
  calc
    activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) =
        activeNonpreemptivePriorityResidualWork
          (stationaryPriorityFiniteWindowState meanService (flow t omega)
            (-((horizon : ℝ) + t)) 0) := by
              rw [show -((horizon : ℝ) + t) = -(horizon : ℝ) - t by ring]
              simpa [flow] using htranslate.symm
    _ = stationaryPriorityRemotePastActiveResidualWork meanService (flow t omega) := hactive

/-- At any fixed physical time, sufficiently remote empty-start replays
coalesce in each priority-filtered waiting-work component with the literal
remote-past state viewed through the stationary input flow. -/
theorem ae_eventually_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_at_eq_remotePast_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1)
    (selected : Fin n) (t : ℝ) :
    ∀ᵐ omega ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) selected =
          stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
            (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow t omega) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let flow := Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow (Class := Fin n)
  have hflow : MeasurePreserving (flow t) P P := by
    exact Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow_measurePreserving
      arrivalRate harrivalRate t
  have hcoalesces : ∀ᵐ omega ∂P,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService (flow t omega) (-older) 0)
          (stationaryPriorityRemotePastState meanService (flow t omega)) := by
    refine MeasureTheory.ae_of_ae_map (μ := P) (f := flow t) (p := fun eta =>
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        liveEquivalentNonpreemptivePriorityWorkState
          (stationaryPriorityFiniteWindowState meanService eta (-older) 0)
          (stationaryPriorityRemotePastState meanService eta)) hflow.measurable.aemeasurable ?_
    rw [hflow.map_eq]
    exact ae_exists_stationaryPriorityRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable
  have htied : ∀ᵐ omega ∂P, ∀ horizon : ℕ,
      ∀ first ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) t),
        ∀ second ∈ nonpreemptivePriorityArrivalWindowIndices
          (stationaryPriorityArrivalWindowIndices omega (-(horizon : ℝ)) t),
          Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              first.1 omega first.2 =
            Probability.PoissonProcess.multiclassStationaryPoissonWorkArrival
              second.1 omega second.2 → first = second := by
    rw [ae_all_iff]
    intro horizon
    exact ae_stationaryPriorityArrivalWindow_noArrivalTies
      arrivalRate harrivalRate (-(horizon : ℝ)) t
  filter_upwards [hcoalesces, htied] with omega hcoalescesOmega htiedOmega
  rcases hcoalescesOmega with ⟨cutoff, hcutoffNonneg, hcoalescesOmega⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil (cutoff - t), ?_⟩
  intro horizon hhorizon
  have hceil : cutoff - t ≤ (Nat.ceil (cutoff - t) : ℝ) := Nat.le_ceil _
  have hcast : (Nat.ceil (cutoff - t) : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  have holder : cutoff ≤ (horizon : ℝ) + t := by linarith
  have hwaiting := priorityWaitingResidualWorkAtLeastAsUrgent_eq_of_liveEquivalent
    (hcoalescesOmega ((horizon : ℝ) + t) holder) selected
  have htranslate :=
    priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindow_flow
      meanService omega t (-(horizon : ℝ)) t selected (htiedOmega horizon)
  calc
    priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) t) selected =
        priorityWaitingResidualWorkAtLeastAsUrgent
          (stationaryPriorityFiniteWindowState meanService (flow t omega)
            (-((horizon : ℝ) + t)) 0) selected := by
              rw [show -((horizon : ℝ) + t) = -(horizon : ℝ) - t by ring]
              simpa [flow] using htranslate.symm
    _ = stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
        (flow t omega) := hwaiting

/-- The literal stationary active residual is jointly almost-everywhere
measurable in a physical time shift and the marked-Poisson input path. -/
theorem aemeasurable_uncurry_stationaryPriorityRemotePastActiveResidualWork_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    AEMeasurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      stationaryPriorityRemotePastActiveResidualWork meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2))
      (MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  exact Probability.PoissonProcess.aemeasurable_uncurry_comp_multiclassStationaryPoissonWorkFlow
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastActiveResidualWork meanService)
    (aemeasurable_stationaryPriorityRemotePastActiveResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable)

/-- The literal stationary priority-filtered waiting work is jointly
almost-everywhere measurable in a physical time shift and the marked-Poisson
input path. -/
theorem aemeasurable_uncurry_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    AEMeasurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2))
      (MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  exact Probability.PoissonProcess.aemeasurable_uncurry_comp_multiclassStationaryPoissonWorkFlow
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected)
    (aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
      arrivalRate meanService harrivalRate hmeanService hstable selected)

/-- The squared residual ledger of the literal stationary remote-past queue is
jointly almost-everywhere measurable along physical time shifts.  This is the
state-energy observable needed when a finite replay energy balance is passed
to its stationary limit. -/
theorem aemeasurable_uncurry_stationaryPriorityRemotePastSquaredResidualWork_flow
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) :
    AEMeasurable (fun p : ℝ × (Fin n → StationaryPoissonWorkPath) =>
      stationaryPriorityRemotePastSquaredResidualWork meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2))
      (MeasureTheory.volume.prod
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  exact Probability.PoissonProcess.aemeasurable_uncurry_comp_multiclassStationaryPoissonWorkFlow
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastSquaredResidualWork meanService)
    (aemeasurable_stationaryPriorityRemotePastSquaredResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable)

/-- The active residual seen by a tagged arrival has the stationary active
residual law.  This transports the finite common-replay law through the two
pathwise remote-past stabilizations. -/
theorem stationaryPriorityClassTaggedPreArrivalActiveResidualWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    HasLaw
      (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected)
      (Measure.map (stationaryPriorityRemotePastActiveResidualWork meanService)
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let Pstationary :=
    Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected :=
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  letI : IsProbabilityMeasure Pstationary := by
    dsimp [Pstationary]
    exact
      Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
        arrivalRate harrivalRate
  letI : IsProbabilityMeasure Pselected := by
    dsimp [Pselected]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).isProbability
  let stationaryFinite : ℕ → (Fin n → StationaryPoissonWorkPath) → ℝ :=
    fun horizon omega => activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
  let selectedFinite : ℕ →
      MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected → ℝ :=
    fun horizon z => activeNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-(horizon : ℝ)) 0)
  let stationaryRemote := stationaryPriorityRemotePastActiveResidualWork meanService
  let selectedRemote :=
    stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected
  have hstationaryAE : ∀ᵐ omega ∂Pstationary,
      Tendsto (fun horizon => stationaryFinite horizon omega) Filter.atTop
        (nhds (stationaryRemote omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [stationaryFinite, stationaryRemote] using heventual)
  have hstationaryMeasure : TendstoInMeasure Pstationary stationaryFinite Filter.atTop
      stationaryRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable.aestronglyMeasurable
    · exact hstationaryAE
  have hstationaryDistribution : TendstoInDistribution stationaryFinite Filter.atTop
      stationaryRemote (fun _ => Pstationary) Pstationary :=
    hstationaryMeasure.tendstoInDistribution (fun horizon =>
      (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable)
  have hselectedAE : ∀ᵐ z ∂Pselected,
      Tendsto (fun horizon => selectedFinite horizon z) Filter.atTop
        (nhds (selectedRemote z)) := by
    filter_upwards [
      ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_preArrival
        arrivalRate meanService harrivalRate hmeanService hstable selected] with z heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [selectedFinite, selectedRemote] using heventual)
  have hselectedMeasure : TendstoInMeasure Pselected selectedFinite Filter.atTop
      selectedRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact (canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable.aestronglyMeasurable
    · exact hselectedAE
  have hselectedDistribution : TendstoInDistribution selectedFinite Filter.atTop
      selectedRemote (fun _ => Pselected) Pselected :=
    hselectedMeasure.tendstoInDistribution (fun horizon =>
      (canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable)
  have hselectedToStationary : TendstoInDistribution selectedFinite Filter.atTop
      stationaryRemote (fun _ => Pselected) Pstationary := by
    refine ⟨?_, ?_, ?_⟩
    · intro horizon
      simpa [selectedFinite, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable
    · simpa [stationaryRemote, Pstationary] using
        (aemeasurable_stationaryPriorityRemotePastActiveResidualWork
          arrivalRate meanService harrivalRate hmeanService hstable)
    · apply hstationaryDistribution.tendsto.congr'
      apply Filter.Eventually.of_forall
      intro horizon
      apply Subtype.ext
      simpa [stationaryFinite, selectedFinite, Pstationary, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).map_eq.symm
  have hmap : Pstationary.map stationaryRemote = Pselected.map selectedRemote :=
    tendstoInDistribution_unique selectedFinite hselectedToStationary hselectedDistribution
  refine ⟨?_, ?_⟩
  · simpa [selectedRemote, Pselected] using
      (aemeasurable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  · simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using hmap.symm

/-- The urgent waiting work seen by a tagged class-`i` arrival has the law of
the corresponding stationary urgent-waiting component. -/
theorem stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_hasLaw_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    HasLaw
      (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService selected)
      (Measure.map (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected)
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag := by
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  letI : IsProbabilityMeasure Pstationary := by
    dsimp [Pstationary]
    exact Probability.PoissonProcess.isProbabilityMeasure_multiclassStationaryPoissonWorkMeasure
      arrivalRate harrivalRate
  letI : IsProbabilityMeasure Pselected := by
    dsimp [Pselected]
    exact (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).isProbability
  let stationaryFinite : ℕ → (Fin n → StationaryPoissonWorkPath) → ℝ :=
    fun horizon omega => priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0) selected
  let selectedFinite : ℕ → MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) selected → ℝ :=
    fun horizon z => priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService selected z
        (-(horizon : ℝ)) 0) selected
  let stationaryRemote := stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
  let selectedRemote :=
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService selected
  have hstationaryAE : ∀ᵐ omega ∂Pstationary,
      Tendsto (fun horizon => stationaryFinite horizon omega) Filter.atTop
        (nhds (stationaryRemote omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable selected] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [stationaryFinite, stationaryRemote] using heventual)
  have hstationaryMeasure : TendstoInMeasure Pstationary stationaryFinite Filter.atTop
      stationaryRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable.aestronglyMeasurable
    · exact hstationaryAE
  have hstationaryDistribution : TendstoInDistribution stationaryFinite Filter.atTop
      stationaryRemote (fun _ => Pstationary) Pstationary :=
    hstationaryMeasure.tendstoInDistribution (fun horizon =>
      (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable)
  have hselectedAE : ∀ᵐ z ∂Pselected,
      Tendsto (fun horizon => selectedFinite horizon z) Filter.atTop
        (nhds (selectedRemote z)) := by
    filter_upwards [
      ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_preArrival
        arrivalRate meanService harrivalRate hmeanService hstable selected] with z heventual
    exact tendsto_nhds_of_eventually_eq (by
      simpa [selectedFinite, selectedRemote] using heventual)
  have hselectedMeasure : TendstoInMeasure Pselected selectedFinite Filter.atTop
      selectedRemote := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro horizon
      exact (canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable.aestronglyMeasurable
    · exact hselectedAE
  have hselectedDistribution : TendstoInDistribution selectedFinite Filter.atTop
      selectedRemote (fun _ => Pselected) Pselected :=
    hselectedMeasure.tendstoInDistribution (fun horizon =>
      (canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable)
  have hselectedToStationary : TendstoInDistribution selectedFinite Filter.atTop
      stationaryRemote (fun _ => Pselected) Pstationary := by
    refine ⟨?_, ?_, ?_⟩
    · intro horizon
      simpa [selectedFinite, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).aemeasurable
    · simpa [stationaryRemote, Pstationary] using
        (aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
          arrivalRate meanService harrivalRate hmeanService hstable selected)
    · apply hstationaryDistribution.tendsto.congr'
      apply Filter.Eventually.of_forall
      intro horizon
      apply Subtype.ext
      simpa [stationaryFinite, selectedFinite, Pstationary, Pselected] using
        (canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_stationary
          arrivalRate meanService harrivalRate selected (horizon : ℝ)).map_eq.symm
  have hmap : Pstationary.map stationaryRemote = Pselected.map selectedRemote :=
    tendstoInDistribution_unique selectedFinite hselectedToStationary hselectedDistribution
  refine ⟨?_, ?_⟩
  · simpa [selectedRemote, Pselected] using
      (aemeasurable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  · simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using hmap.symm

/-- The active residual seen by a selected arrival is integrable exactly when
the stationary active residual is integrable.  This is the integrability form
of the concrete finite-replay Palm transport above. -/
theorem integrable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_iff_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag ↔
    Integrable (stationaryPriorityRemotePastActiveResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastActiveResidualWork meanService
  let selectedRemote := stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote) Pstationary := ⟨by
    simpa [stationaryRemote, Pstationary] using
      (aemeasurable_stationaryPriorityRemotePastActiveResidualWork
        arrivalRate meanService harrivalRate hmeanService hstable), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote) Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedPreArrivalActiveResidualWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  exact (hstationary.identDistrib hselected).symm.integrable_iff

/-- Under strict total load, the literal stationary active residual has a
finite first moment.  This is transported from any selected-arrival Palm
representative through the concrete common remote-past law. -/
theorem integrable_stationaryPriorityRemotePastActiveResidualWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n) :
    Integrable (stationaryPriorityRemotePastActiveResidualWork meanService)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let selected : Fin n := ⟨0, hn⟩
  apply (integrable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_iff_stationary
    arrivalRate meanService harrivalRate hmeanService hstable selected).mp
  exact integrable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_of_totalStable
    arrivalRate meanService harrivalRate hmeanService hstable selected

/-- The expected active residual of empty-start finite replays converges to
the expected literal stationary active residual.  Eventual remote-past
coalescence supplies pointwise convergence, while every finite active term is
dominated by the integrable causal total workload. -/
theorem tendsto_integral_activeResidualWork_stationaryPriorityFiniteWindowState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n) :
    Filter.Tendsto (fun horizon : ℕ =>
      ∫ omega, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      Filter.atTop
      (nhds (∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℕ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0)
  let f : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastActiveResidualWork meanService
  let g : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastResidualWork meanService
  have hmeas : ∀ horizon, AEStronglyMeasurable (F horizon) P := by
    intro horizon
    simpa [F, P] using
      (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate (horizon : ℝ)).aemeasurable.aestronglyMeasurable
  have hgint : Integrable g P := by
    simpa [g, P] using
      MM1DirectCausal.integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hbound : ∀ horizon, ∀ᵐ omega ∂P, ‖F horizon omega‖ ≤ g omega := by
    intro horizon
    filter_upwards [
      ae_forall_activeResidualWork_stationaryPriorityFiniteWindowState_le_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable,
      ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
        arrivalRate meanService harrivalRate hmeanService (-(horizon : ℝ)) 0] with
        omega hle hpositive
    have hnonnegative : 0 ≤ F horizon omega := by
      dsimp [F]
      unfold activeNonpreemptivePriorityResidualWork
      cases hactive :
          (stationaryPriorityFiniteWindowState meanService omega (-(horizon : ℝ)) 0).active with
      | none => simp
      | some active => exact (hpositive.1 active hactive).le
    rw [Real.norm_of_nonneg hnonnegative]
    simpa [F, g] using hle horizon
  have hlimit : ∀ᵐ omega ∂P, Filter.Tendsto (fun horizon : ℕ => F horizon omega)
      Filter.atTop (nhds (f omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by simpa [F, f] using heventual)
  simpa [F, f, P, g] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := P) (F := F) (f := f) g hmeas hgint hbound hlimit)

/-- The expected active residual of empty-start finite replays also converges
along real-valued remote-past horizons.  This is the continuous form used by
the finite-time occupation reindexing. -/
theorem tendsto_integral_activeResidualWork_stationaryPriorityFiniteWindowState_real
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n) :
    Filter.Tendsto (fun horizon : ℝ =>
      ∫ omega, activeNonpreemptivePriorityResidualWork
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0)
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      Filter.atTop
      (nhds (∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon omega =>
    activeNonpreemptivePriorityResidualWork
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0)
  let f : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastActiveResidualWork meanService
  let g : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastResidualWork meanService
  have hmeas : ∀ horizon, AEStronglyMeasurable (F horizon) P := by
    intro horizon
    simpa [F, P] using
      (stationaryPriorityFiniteWindowActiveResidualWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate horizon).aemeasurable.aestronglyMeasurable
  have hgint : Integrable g P := by
    simpa [g, P] using
      MM1DirectCausal.integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hbound : ∀ᶠ horizon : ℝ in Filter.atTop, ∀ᵐ omega ∂P,
      ‖F horizon omega‖ ≤ g omega := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with horizon hhorizon
    filter_upwards [
      ae_forall_activeResidualWork_stationaryPriorityFiniteWindowState_real_le_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable,
      ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
        arrivalRate meanService harrivalRate hmeanService (-horizon) 0] with
        omega hle hpositive
    have hnonnegative : 0 ≤ F horizon omega := by
      dsimp [F]
      unfold activeNonpreemptivePriorityResidualWork
      cases hactive :
          (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0).active with
      | none => simp
      | some active => exact (hpositive.1 active hactive).le
    rw [Real.norm_of_nonneg hnonnegative]
    simpa [F, g] using hle horizon hhorizon
  have hlimit : ∀ᵐ omega ∂P, Filter.Tendsto (fun horizon : ℝ => F horizon omega)
      Filter.atTop (nhds (f omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowActiveResidualWork_real_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by simpa [F, f] using heventual)
  simpa [F, f, P, g] using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := P) (l := Filter.atTop) (F := F) (f := f) g
      (Filter.Eventually.of_forall hmeas) hbound hgint hlimit)

/-- The expected priority-filtered waiting work of empty-start finite replays
converges along real-valued remote-past horizons to the corresponding literal
stationary waiting workload.  Pointwise coalescence and the causal total-work
envelope provide the dominated-convergence bridge. -/
theorem tendsto_integral_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_real
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n)
    (selected : Fin n) :
    Filter.Tendsto (fun horizon : ℝ =>
      ∫ omega, priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) selected
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)
      Filter.atTop
      (nhds (∫ omega,
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected omega
        ∂Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) := by
  let P := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let F : ℝ → (Fin n → StationaryPoissonWorkPath) → ℝ := fun horizon omega =>
    priorityWaitingResidualWorkAtLeastAsUrgent
      (stationaryPriorityFiniteWindowState meanService omega (-horizon) 0) selected
  let f : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
  let g : (Fin n → StationaryPoissonWorkPath) → ℝ :=
    stationaryPriorityRemotePastResidualWork meanService
  have hmeas : ∀ horizon, AEStronglyMeasurable (F horizon) P := by
    intro horizon
    simpa [F, P] using
      (stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_hasLaw_canonicalPast
        arrivalRate meanService harrivalRate selected horizon).aemeasurable.aestronglyMeasurable
  have hgint : Integrable g P := by
    simpa [g, P] using
      MM1DirectCausal.integrable_stationaryPriorityRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable hn
  have hbound : ∀ᶠ horizon : ℝ in Filter.atTop, ∀ᵐ omega ∂P,
      ‖F horizon omega‖ ≤ g omega := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with horizon hhorizon
    filter_upwards [
      ae_forall_priorityWaitingResidualWorkAtLeastAsUrgent_stationaryPriorityFiniteWindowState_real_le_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable selected,
      ae_positiveNonpreemptivePriorityResidualWork_stationaryPriorityFiniteWindowState
        arrivalRate meanService harrivalRate hmeanService (-horizon) 0] with
        omega hle hpositive
    have hnonnegative : 0 ≤ F horizon omega := by
      dsimp [F]
      exact priorityWaitingResidualWorkAtLeastAsUrgent_nonneg _ hpositive.nonnegative selected
    rw [Real.norm_of_nonneg hnonnegative]
    simpa [F, g] using hle horizon hhorizon
  have hlimit : ∀ᵐ omega ∂P, Filter.Tendsto (fun horizon : ℝ => F horizon omega)
      Filter.atTop (nhds (f omega)) := by
    filter_upwards [
      ae_eventually_stationaryPriorityFiniteWindowAtLeastAsUrgentWaitingWork_real_eq_remotePast
        arrivalRate meanService harrivalRate hmeanService hstable selected] with omega heventual
    exact tendsto_nhds_of_eventually_eq (by simpa [F, f] using heventual)
  simpa [F, f, P, g] using
    (MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := P) (l := Filter.atTop) (F := F) (f := f) g
      (Filter.Eventually.of_forall hmeas) hbound hgint hlimit)

/-- The active residual seen by a selected arrival has the stationary active
residual expectation. -/
theorem integral_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_eq_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    ∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag =
    ∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastActiveResidualWork meanService
  let selectedRemote := stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote) Pstationary := ⟨by
    simpa [stationaryRemote, Pstationary] using
      (aemeasurable_stationaryPriorityRemotePastActiveResidualWork
        arrivalRate meanService harrivalRate hmeanService hstable), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote) Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedPreArrivalActiveResidualWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
    (hstationary.identDistrib hselected).symm.integral_eq

/-- The urgent waiting work seen by a selected arrival is integrable exactly
when the corresponding stationary urgent-waiting work is integrable. -/
theorem integrable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_iff_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    Integrable (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService selected)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag ↔
    Integrable (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
  let selectedRemote :=
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote) Pstationary := ⟨by
    simpa [stationaryRemote, Pstationary] using
      (aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
        arrivalRate meanService harrivalRate hmeanService hstable selected), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote) Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  exact (hstationary.identDistrib hselected).symm.integrable_iff

/-- Under strict total load, every literal stationary priority-filtered
waiting-work observable has a finite first moment. -/
theorem integrable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    Integrable (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected)
      (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
  apply (integrable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_iff_stationary
    arrivalRate meanService harrivalRate hmeanService hstable selected).mp
  exact integrable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_of_totalStable
    arrivalRate meanService harrivalRate hmeanService hstable selected

/-- The finite-time occupation integral of the literal stationary active
residual is its stationary expectation times the interval length. -/
theorem integral_stationaryPriorityRemotePastActiveResidualWork_flow_Ioc
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (hn : 0 < n)
    (a b : ℝ) (hab : a ≤ b) :
    ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
      stationaryPriorityRemotePastActiveResidualWork meanService
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2) ∂
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) =
      (b - a) * ∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  exact Probability.PoissonProcess.integral_uncurry_comp_multiclassStationaryPoissonWorkFlow_Ioc
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastActiveResidualWork meanService)
    (integrable_stationaryPriorityRemotePastActiveResidualWork_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable hn)
    a b hab

/-- The finite-time occupation integral of literal priority-filtered waiting
work is its stationary expectation times the interval length. -/
theorem integral_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_flow_Ioc
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n)
    (a b : ℝ) (hab : a ≤ b) :
    ∫ p : ℝ × (Fin n → StationaryPoissonWorkPath),
      stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
        (Probability.PoissonProcess.multiclassStationaryPoissonWorkFlow p.1 p.2) ∂
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate)) =
      (b - a) * ∫ omega,
        stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected omega ∂
        Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  exact Probability.PoissonProcess.integral_uncurry_comp_multiclassStationaryPoissonWorkFlow_Ioc
    arrivalRate harrivalRate
    (stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected)
    (integrable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable selected)
    a b hab

/-- The urgent waiting work seen by a selected arrival has the corresponding
stationary urgent-waiting expectation. -/
theorem integral_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_eq_stationary
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (selected : Fin n) :
    ∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService selected z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate selected))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag =
    ∫ omega, stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected omega ∂
      Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate := by
  let Pstationary := Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate
  let Pselected := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate selected))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate selected)).Ptag
  let stationaryRemote := stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService selected
  let selectedRemote :=
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService selected
  have hstationary : HasLaw stationaryRemote (Pstationary.map stationaryRemote) Pstationary := ⟨by
    simpa [stationaryRemote, Pstationary] using
      (aemeasurable_stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork
        arrivalRate meanService harrivalRate hmeanService hstable selected), rfl⟩
  have hselected : HasLaw selectedRemote (Pstationary.map stationaryRemote) Pselected := by
    simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
      (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_hasLaw_stationary
        arrivalRate meanService harrivalRate hmeanService hstable selected)
  simpa [stationaryRemote, selectedRemote, Pstationary, Pselected] using
    (hstationary.identDistrib hselected).symm.integral_eq

end

end AppliedModelingLib.Queueing
