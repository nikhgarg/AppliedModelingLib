import AppliedModelingLib.Foundations.Probability.FiniteExponentialRace
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentUniformization

/-!
# Physical event clock for class-dependent nonpreemptive-priority queues

This module places the finite uniformized arrival/potential-completion event
chain on a canonical continuous-time exponential event clock.  The label path
has precisely the existing uniformized event law, while the event epochs are
the nonexplosive total-clock epochs from the reusable finite-race model.

It is a finite-start construction.  It does not identify a stationary Palm
queue with this clock or establish stationary performance bounds.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The total physical rate of all arrival and potential-completion clocks. -/
def classDependentNonpreemptivePriorityTotalEventRate
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ) : ℝ :=
  Probability.finiteExponentialRaceTotalRate
    (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)

/-- The class-dependent total event rate is the sum of all offered arrival and
potential-service rates. -/
theorem classDependentNonpreemptivePriorityTotalEventRate_eq
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ) :
    classDependentNonpreemptivePriorityTotalEventRate arrivalRate serviceRate =
      (∑ i, arrivalRate i) + ∑ i, serviceRate i := by
  unfold classDependentNonpreemptivePriorityTotalEventRate
  exact sum_classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate

/-- The finite family of arrival and potential-completion rates is
nonnegative. -/
theorem classDependentNonpreemptivePriorityEventWeight_nonnegative
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    ∀ event, 0 ≤ classDependentNonpreemptivePriorityEventWeight
      arrivalRate serviceRate event := by
  intro event
  cases event with
  | inl i => exact harrivalRate i
  | inr i => exact (hserviceRate i).le

/-- A nonempty class set and positive service rates make the total event rate
strictly positive. -/
theorem classDependentNonpreemptivePriorityTotalEventRate_pos
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ) (hn : 0 < n)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    0 < classDependentNonpreemptivePriorityTotalEventRate arrivalRate serviceRate := by
  rw [classDependentNonpreemptivePriorityTotalEventRate_eq]
  let i : Fin n := ⟨0, hn⟩
  have harrivalSum : 0 ≤ ∑ j, arrivalRate j :=
    Finset.sum_nonneg fun j _ => harrivalRate j
  have hserviceSum : 0 < ∑ j, serviceRate j := by
    refine Finset.sum_pos' ?_ ?_
    · intro j _
      exact (hserviceRate j).le
    · exact ⟨i, Finset.mem_univ i, hserviceRate i⟩
  linarith

/-- The canonical continuous-time race of class-dependent queue events. -/
noncomputable def classDependentNonpreemptivePriorityEventRaceMeasure
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    Measure (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) :=
  Probability.finiteExponentialRaceEventMeasure
    (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
    (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
      harrivalRate hserviceRate)
    (by
      simpa [classDependentNonpreemptivePriorityTotalEventRate] using
        classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
          hn harrivalRate hserviceRate)

/-- The finite-race winner distribution is the existing uniformized queue
event PMF. -/
theorem finiteExponentialRaceLabelPMF_classDependentNonpreemptivePriority_eq
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    Probability.finiteExponentialRaceLabelPMF
      (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
        harrivalRate hserviceRate)
      (by
        simpa [Probability.finiteExponentialRaceTotalRate,
          classDependentNonpreemptivePriorityTotalEventRate] using
          classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
            hn harrivalRate hserviceRate) =
      classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
        hn harrivalRate hserviceRate := by
  unfold Probability.finiteExponentialRaceLabelPMF
  unfold classDependentNonpreemptivePriorityEventPMF
  rfl

/-- The discrete event-label path observed from the physical race clock. -/
def classDependentNonpreemptivePriorityEventRaceWinnerPath
    {n : ℕ} :
    (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) →
      ℕ → ClassDependentNonpreemptivePriorityEvent n :=
  Probability.finiteExponentialRaceWinnerPath

/-- The physical event clock's labels have exactly the existing uniformized
IID event-stream law. -/
theorem classDependentNonpreemptivePriorityEventRaceWinnerPath_hasLaw
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    HasLaw classDependentNonpreemptivePriorityEventRaceWinnerPath
      (Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
          hn harrivalRate hserviceRate).toMeasure)
      (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate serviceRate
        hn harrivalRate hserviceRate) := by
  simpa [classDependentNonpreemptivePriorityEventRaceWinnerPath,
    classDependentNonpreemptivePriorityEventRaceMeasure,
    Probability.finiteExponentialRaceLabelPMF,
    classDependentNonpreemptivePriorityEventPMF] using
    (Probability.finiteExponentialRaceWinnerPath_hasLaw
      (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
        harrivalRate hserviceRate)
      (by
        simpa [Probability.finiteExponentialRaceTotalRate,
          classDependentNonpreemptivePriorityTotalEventRate] using
          classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
            hn harrivalRate hserviceRate))

/-- The physical total-gap path and the uniformized event-label path are
jointly independent canonical IID streams. -/
theorem classDependentNonpreemptivePriorityEventRaceGapWinnerPaths_hasLaw
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    HasLaw Probability.finiteExponentialRaceGapWinnerPaths
      ((Probability.IIDStream.measure
        (ProbabilityTheory.expMeasure
          (classDependentNonpreemptivePriorityTotalEventRate arrivalRate serviceRate))).prod
        (Probability.IIDStream.measure
          (classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
            hn harrivalRate hserviceRate).toMeasure))
      (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate serviceRate
        hn harrivalRate hserviceRate) := by
  simpa [classDependentNonpreemptivePriorityEventRaceMeasure,
    Probability.finiteExponentialRaceLabelPMF,
    classDependentNonpreemptivePriorityEventPMF] using
    (Probability.finiteExponentialRaceGapWinnerPaths_hasLaw
      (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
        harrivalRate hserviceRate)
      (by
        simpa [Probability.finiteExponentialRaceTotalRate,
          classDependentNonpreemptivePriorityTotalEventRate] using
          classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
            hn harrivalRate hserviceRate))

/-- In label-then-gap order, the physical queue event clock has exactly the
independent product law used by the finite busy-period estimate. -/
theorem classDependentNonpreemptivePriorityEventRaceWinnerGapPaths_hasLaw
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    HasLaw Probability.finiteExponentialRaceWinnerGapPaths
      ((Probability.IIDStream.measure
        (classDependentNonpreemptivePriorityEventPMF arrivalRate serviceRate
          hn harrivalRate hserviceRate).toMeasure).prod
        (Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure
            (classDependentNonpreemptivePriorityTotalEventRate arrivalRate serviceRate))))
      (classDependentNonpreemptivePriorityEventRaceMeasure arrivalRate serviceRate
        hn harrivalRate hserviceRate) := by
  simpa [classDependentNonpreemptivePriorityEventRaceMeasure,
    Probability.finiteExponentialRaceLabelPMF,
    classDependentNonpreemptivePriorityEventPMF] using
    (Probability.finiteExponentialRaceWinnerGapPaths_hasLaw
      (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
        harrivalRate hserviceRate)
      (by
        simpa [Probability.finiteExponentialRaceTotalRate,
          classDependentNonpreemptivePriorityTotalEventRate] using
          classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
            hn harrivalRate hserviceRate))

/-- The physical epochs of the class-dependent event race. -/
def classDependentNonpreemptivePriorityEventRaceArrivalTime
    {n : ℕ} (index : ℕ) :
    (ℕ → ℝ × ClassDependentNonpreemptivePriorityEvent n) → ℝ :=
  Probability.finiteExponentialRaceArrivalTime index

/-- The physical event clock of a finite class-dependent queue is
nonexplosive. -/
theorem ae_classDependentNonpreemptivePriorityEventRaceArrivalTime_tendsto_atTop
    {n : ℕ} (arrivalRate serviceRate : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hserviceRate : ∀ i, 0 < serviceRate i) :
    ∀ᵐ path ∂classDependentNonpreemptivePriorityEventRaceMeasure
      arrivalRate serviceRate hn harrivalRate hserviceRate,
      Filter.Tendsto
        (fun index => classDependentNonpreemptivePriorityEventRaceArrivalTime index path)
        Filter.atTop Filter.atTop := by
  simpa [classDependentNonpreemptivePriorityEventRaceArrivalTime,
    classDependentNonpreemptivePriorityEventRaceMeasure] using
    (Probability.ae_finiteExponentialRaceArrivalTime_tendsto_atTop
      (classDependentNonpreemptivePriorityEventWeight arrivalRate serviceRate)
      (classDependentNonpreemptivePriorityEventWeight_nonnegative arrivalRate serviceRate
        harrivalRate hserviceRate)
      (by
        simpa [Probability.finiteExponentialRaceTotalRate,
          classDependentNonpreemptivePriorityTotalEventRate] using
          classDependentNonpreemptivePriorityTotalEventRate_pos arrivalRate serviceRate
            hn harrivalRate hserviceRate))

end

end AppliedModelingLib.Queueing
