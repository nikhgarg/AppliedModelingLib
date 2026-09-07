import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastCapacitySplit
import AppliedModelingLib.Queueing.NonpreemptivePriorityCanonicalPastStateMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceLedger

/-!
# Pre-arrival work terms for a tagged nonpreemptive-priority customer

This module names the two parts of the literal queue state that are present
immediately before a tagged customer's arrival: the residual of the job in
service and the waiting work in classes at least as urgent as the tag.  They
are generic state observables; later stationary arguments establish the
corresponding expectation identities.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- Residual work of the job in service immediately before the selected
customer's Palm arrival. -/
noncomputable def stationaryPriorityClassTaggedPreArrivalActiveResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : ℝ :=
  activeNonpreemptivePriorityResidualWork
    (stationaryPriorityClassTaggedRemotePastState meanService i z)

/-- Waiting work already present in classes at least as urgent as the selected
customer immediately before its Palm arrival.  The selected job itself is not
in this pre-arrival state. -/
noncomputable def stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : ℝ :=
  priorityWaitingResidualWorkAtLeastAsUrgent
    (stationaryPriorityClassTaggedRemotePastState meanService i z) i

/-- On a coalesced selected-Palm path, the generic tagged-service ledger at
the instant of admission is exactly the active residual plus the waiting work
in classes at least as urgent as the tag.  This is a deterministic state
identity; it does not yet account for later overtaking arrivals. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff) :
    nonpreemptivePriorityTaggedPreServiceWork
        (stationaryPriorityClassTaggedArrivalState meanService i z)
        (stationaryPriorityClassTaggedJob meanService i z) =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
          meanService i z := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremoteFresh : ¬ nonpreemptivePriorityWorkStateContainsJob remote tag := by
    simpa [remote, tag] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
        meanService i z hgood
  have hclearedFresh : ¬ nonpreemptivePriorityWorkStateContainsJob cleared tag := by
    intro hcontains
    apply hremoteFresh
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  have hremoteWork : nonpreemptivePriorityWorkConserving remote := by
    rw [show remote = canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0 by
      simpa [remote] using
        stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
          meanService i z hcutoff]
    exact nonpreemptivePriorityWorkConserving_canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-hcutoff.choose) 0
  have hclearedWork : nonpreemptivePriorityWorkConserving cleared := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hremoteWork
  simpa [stationaryPriorityClassTaggedArrivalState,
    stationaryPriorityClassTaggedPreArrivalActiveResidualWork,
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork,
    remote, cleared, tag, clearNonpreemptivePriorityCompletionLedger] using
    (nonpreemptivePriorityTaggedPreServiceWork_admit_self_of_fresh
      cleared tag hclearedFresh hclearedWork)

/-- The selected-arrival tagged-service ledger has its literal pre-arrival
state decomposition almost surely under the stable selected-Palm law. -/
theorem ae_nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      nonpreemptivePriorityTaggedPreServiceWork
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (stationaryPriorityClassTaggedJob meanService i z) =
        stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
            meanService i z := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i] with z hgood hcutoff
  exact nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
    meanService i z hgood hcutoff

/-- Under the concrete positive-mark Palm law, the remote-past state has
nonnegative stored residuals almost surely.  This strengthens the existing
total-work nonnegativity result to the literal state needed by the two
pre-arrival component ledgers. -/
theorem ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedRemotePastState
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      nonnegativeNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedRemotePastState meanService i z) := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i] with z hcutoff hpositive
  rw [stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
    meanService i z hcutoff]
  apply positiveNonpreemptivePriorityResidualWork.nonnegative
  unfold canonicalStationaryPriorityClassTaggedFiniteWindowState
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · constructor
    · intro active hactive
      simp [emptyNonpreemptivePriorityWorkState] at hactive
    · intro j job hmember
      simp [emptyNonpreemptivePriorityWorkState] at hmember
  · intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedArrivalWindowJobs_iff
      meanService i z (-hcutoff.choose) 0 job).mp hjob with ⟨j, k, _, hjob⟩
    subst job
    exact hpositive j k

/-- The pre-arrival active residual is nonnegative almost surely under the
concrete stationary Palm law. -/
theorem ae_nonneg_stationaryPriorityClassTaggedPreArrivalActiveResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 ≤ stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z := by
  filter_upwards [
    ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedRemotePastState
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork
  unfold stationaryPriorityClassTaggedPreArrivalActiveResidualWork
    activeNonpreemptivePriorityResidualWork
  cases hactive : (stationaryPriorityClassTaggedRemotePastState meanService i z).active with
  | none => simp
  | some active => exact hwork.1 active hactive

/-- The pre-arrival at-least-as-urgent waiting ledger is nonnegative almost
surely under the concrete stationary Palm law. -/
theorem ae_nonneg_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      0 ≤ stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
        meanService i z := by
  filter_upwards [
    ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedRemotePastState
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork
  exact priorityWaitingResidualWorkAtLeastAsUrgent_nonneg
    (stationaryPriorityClassTaggedRemotePastState meanService i z) hwork i

/-- The pre-arrival active residual is dominated almost surely by the full
causal remote-past workload. -/
theorem ae_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_le_remotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ≤
        stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  filter_upwards [
    ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedRemotePastState
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork
  exact activeNonpreemptivePriorityResidualWork_le_total
    (stationaryPriorityClassTaggedRemotePastState meanService i z) hwork

/-- The pre-arrival at-least-as-urgent waiting ledger is dominated almost
surely by the full causal remote-past workload. -/
theorem ae_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_le_remotePastResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
        meanService i z ≤
          stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  filter_upwards [
    ae_nonnegativeNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedRemotePastState
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hwork
  exact priorityWaitingResidualWorkAtLeastAsUrgent_le_total
    (stationaryPriorityClassTaggedRemotePastState meanService i z) hwork i

/-- Along growing canonical past horizons, the active residual stabilizes to
the causal pre-arrival active residual almost surely. -/
theorem ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_preArrival
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        activeNonpreemptivePriorityResidualWork
          (canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-(horizon : ℝ)) 0) =
          stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  change activeNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-(horizon : ℝ)) 0) =
      activeNonpreemptivePriorityResidualWork
        (stationaryPriorityClassTaggedRemotePastState meanService i z)
  unfold activeNonpreemptivePriorityResidualWork
  rw [(hcoalesces (horizon : ℝ) (hceil.trans hcast)).2.1]

/-- Along growing canonical past horizons, the at-least-as-urgent waiting
ledger stabilizes to its causal pre-arrival value almost surely. -/
theorem ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_preArrival
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ᶠ horizon : ℕ in Filter.atTop,
        priorityWaitingResidualWorkAtLeastAsUrgent
          (canonicalStationaryPriorityClassTaggedFiniteWindowState
            meanService i z (-(horizon : ℝ)) 0) i =
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
            meanService i z := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalesces
  rcases hcoalesces with ⟨cutoff, hnonnegative, hcoalesces⟩
  apply Filter.eventually_atTop.2
  refine ⟨Nat.ceil cutoff, ?_⟩
  intro horizon hhorizon
  have hceil : cutoff ≤ (Nat.ceil cutoff : ℝ) := Nat.le_ceil cutoff
  have hcast : (Nat.ceil cutoff : ℝ) ≤ (horizon : ℝ) := by
    exact_mod_cast hhorizon
  change priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-(horizon : ℝ)) 0) i =
      priorityWaitingResidualWorkAtLeastAsUrgent
        (stationaryPriorityClassTaggedRemotePastState meanService i z) i
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
    priorityWaitingResidualWork
  rw [(hcoalesces (horizon : ℝ) (hceil.trans hcast)).2.2]

/-- The causal pre-arrival active residual has an almost-everywhere Borel
representative obtained from finite literal replay states. -/
theorem aemeasurable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  refine Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
    (fun horizon z => activeNonpreemptivePriorityResidualWork
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-(horizon : ℝ)) 0))
    (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i)
    (fun horizon =>
      measurable_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork
        meanService i (horizon : ℝ)) ?_
  exact ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowActiveResidualWork_eq_preArrival
    arrivalRate meanService harrivalRate hmeanService hstable i

/-- The causal pre-arrival at-least-as-urgent waiting ledger has an
almost-everywhere Borel representative obtained from finite literal replay
states. -/
theorem aemeasurable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    AEMeasurable (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  refine Probability.aemeasurable_response_of_ae_eventually_eq
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
    (fun horizon z => priorityWaitingResidualWorkAtLeastAsUrgent
      (canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-(horizon : ℝ)) 0) i)
    (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i)
    (fun horizon =>
      measurable_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork
        meanService i (horizon : ℝ)) ?_
  exact ae_eventually_canonicalStationaryPriorityClassTaggedFiniteWindowAtLeastAsUrgentWaitingWork_eq_preArrival
    arrivalRate meanService harrivalRate hmeanService hstable i

/-- Under strict total load, the active residual present just before the
selected arrival has a finite first moment.  It is a measurable nonnegative
component of the integrable causal remote-past workload. -/
theorem integrable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    Integrable (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hremote : Integrable (stationaryPriorityClassTaggedRemotePastResidualWork meanService i) P := by
    simpa [P] using
      MM1DirectCausal.integrable_stationaryPriorityClassTaggedRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i
  refine Integrable.mono' hremote
    (aemeasurable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i).aestronglyMeasurable ?_
  filter_upwards [
    ae_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_le_remotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_nonneg_stationaryPriorityClassTaggedPreArrivalActiveResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hle hnonnegative
  have hremoteNonnegative : 0 ≤ stationaryPriorityClassTaggedRemotePastResidualWork
      meanService i z := hnonnegative.trans hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonnegative,
    abs_of_nonneg hremoteNonnegative] using hle

/-- Under strict total load, the already-waiting work at least as urgent as
the selected class has a finite first moment. -/
theorem integrable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_of_totalStable
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    Integrable (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hremote : Integrable (stationaryPriorityClassTaggedRemotePastResidualWork meanService i) P := by
    simpa [P] using
      MM1DirectCausal.integrable_stationaryPriorityClassTaggedRemotePastResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i
  refine Integrable.mono' hremote
    (aemeasurable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      arrivalRate meanService harrivalRate hmeanService hstable i).aestronglyMeasurable ?_
  filter_upwards [
    ae_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_le_remotePastResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_nonneg_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hle hnonnegative
  have hremoteNonnegative : 0 ≤ stationaryPriorityClassTaggedRemotePastResidualWork
      meanService i z := hnonnegative.trans hle
  simpa [Real.norm_eq_abs, abs_of_nonneg hnonnegative,
    abs_of_nonneg hremoteNonnegative] using hle

/-- The causal pre-arrival workload splits exactly into the residual service
term, the waiting work at least as urgent as the tag, and the less-urgent
waiting work. -/
theorem stationaryPriorityClassTaggedRemotePastResidualWork_eq_preArrivalTerms_add_lessUrgent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :
    stationaryPriorityClassTaggedRemotePastResidualWork meanService i z =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
          meanService i z +
          priorityWaitingResidualWorkLessUrgent
            (stationaryPriorityClassTaggedRemotePastState meanService i z) i := by
  exact totalNonpreemptivePriorityResidualWork_eq_active_add_waitingAtLeastAsUrgent_add_lessUrgent
    (stationaryPriorityClassTaggedRemotePastState meanService i z) i

/-- The pre-arrival urgent waiting term is bounded by the full remote-past
workload whenever that literal state has nonnegative stored residuals. -/
theorem stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_le_remotePastResidualWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) :
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z ≤
      stationaryPriorityClassTaggedRemotePastResidualWork meanService i z := by
  exact priorityWaitingResidualWorkAtLeastAsUrgent_le_total
    (stationaryPriorityClassTaggedRemotePastState meanService i z) hwork i

end

end AppliedModelingLib.Queueing
