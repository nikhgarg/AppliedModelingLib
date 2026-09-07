import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkPastRate

/-!
# Past squared-mark rate for stationary Poisson suspension input

This module is an input-process calculation.  It evaluates the sum of the
squared unit-exponential marks of arrivals in a deterministic strict-past
window.  It does not introduce a queue or a service discipline.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory Filter Finset
open PoissonProcess
open scoped Topology ProbabilityTheory

noncomputable section

/-- Total squared unit-mark reward of stationary marked-Poisson arrivals in
`[-t, 0)`. -/
def stationaryPoissonWorkPastSquareAggregate
    (z : GoodSuspensionState × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  (suspensionBaseArrivalIndices (-t) 0 z.1).sum
    (fun n => (stationaryPoissonWorkRequirement z n) ^ 2)

/-- The equilibrium-coordinate squared-mark reward accumulated in the
canonical strict-past renewal window. -/
def equilibriumMarkedPastSquareWork
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) : ℝ :=
  canonicalMarkedSquareWork (equilibriumPastPath z.1)
    (equilibriumBackwardWorkPath z.2) t

/-- Reindexing the equilibrium past enumerator turns its square reward into
the corresponding sum on the labelled backward arrivals. -/
theorem equilibriumMarkedPastSquareWork_eq_backwardArrivalSum
    (z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ)) (t : ℝ) :
    equilibriumMarkedPastSquareWork z t =
      (equilibriumBackwardArrivalIndices t z.1).sum (fun i => z.2 i ^ 2) := by
  unfold equilibriumMarkedPastSquareWork canonicalMarkedSquareWork
  rw [equilibriumBackwardArrivalIndices, Finset.sum_image]
  · rfl
  · intro m hm n hn hmn
    exact equilibriumBackwardArrivalIndex_injective hmn

/-- Equilibrium finite-horizon squared-mark past work is Borel measurable. -/
theorem measurable_equilibriumMarkedPastSquareWork (t : ℝ) :
    Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedPastSquareWork z t) := by
  have harrival : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumPastPath z.1) := by
    simpa [equilibriumPastPath] using
      ((measurable_snd : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) => p.2)).comp
        (measurable_fst : Measurable
          (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) => z.1)))
  have hwork : Measurable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumBackwardWorkPath z.2) :=
    measurable_equilibriumBackwardWorkPath.comp measurable_snd
  simpa [equilibriumMarkedPastSquareWork] using
    (measurable_canonicalMarkedSquareWork t).comp (harrival.prodMk hwork)

/-- Equilibrium finite-horizon squared-mark past reward is integrable. -/
theorem integrable_equilibriumMarkedPastSquareWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ) =>
      equilibriumMarkedPastSquareWork z t)
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedPastSquareWork, equilibriumPastMarkedInput,
    Function.comp_def] using
    ((equilibriumPastMarkedInput_measurePreserving hrate).integrable_comp
      (measurable_canonicalMarkedSquareWork t).aestronglyMeasurable).mpr
      (integrable_canonicalMarkedSquareWork hrate ht)

/-- The expected equilibrium squared-mark reward over `[-t,0)` is twice its
Poisson exposure. -/
theorem integral_equilibriumMarkedPastSquareWork
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z : ((ℕ → ℝ) × (ℕ → ℝ)) × (ℤ → ℝ), equilibriumMarkedPastSquareWork z t
      ∂((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) =
      2 * rate * t := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedPastSquareWork, equilibriumPastMarkedInput,
    Function.comp_def] using
    (equilibriumPastMarkedInput_measurePreserving hrate).hasLaw.integral_comp
      (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) =>
        canonicalMarkedSquareWork y.1 y.2 t)
      (measurable_canonicalMarkedSquareWork t).aestronglyMeasurable |>.trans
      (integral_canonicalMarkedSquareWork hrate ht)

/-- The literal stationary strict-past squared-mark ledger agrees almost
surely with the equilibrium-coordinate renewal representation at a fixed
horizon. -/
theorem ae_stationaryPoissonWorkPastSquareAggregate_eq_equilibriumMarkedPastSquareWork
    {rate : ℝ} (hrate : 0 < rate) (t : ℝ) :
    ∀ᵐ z ∂stationaryPoissonWorkMeasure rate,
      stationaryPoissonWorkPastSquareAggregate z t =
        equilibriumMarkedPastSquareWork (stationaryPoissonWorkToEquilibrium z) t := by
  filter_upwards [ae_stationaryPoissonWorkPastIndices_eq_equilibriumBackwardArrivalIndices
    hrate t] with z hindices
  rw [stationaryPoissonWorkPastSquareAggregate, hindices]
  symm
  simpa [stationaryPoissonWorkToEquilibrium, stationaryPoissonWorkRequirement] using
    (equilibriumMarkedPastSquareWork_eq_backwardArrivalSum
      (stationaryPoissonWorkToEquilibrium z) t)

/-- Literal stationary strict-past squared-mark reward is integrable at each
deterministic nonnegative horizon. -/
theorem integrable_stationaryPoissonWorkPastSquareAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    Integrable (fun z => stationaryPoissonWorkPastSquareAggregate z t)
      (stationaryPoissonWorkMeasure rate) := by
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  have hequilibrium : Integrable (fun z =>
      equilibriumMarkedPastSquareWork (stationaryPoissonWorkToEquilibrium z) t)
      (stationaryPoissonWorkMeasure rate) := by
    simpa [Function.comp_def] using
      ((stationaryPoissonWorkToEquilibrium_measurePreserving hrate).integrable_comp
        (measurable_equilibriumMarkedPastSquareWork t).aestronglyMeasurable).mpr
        (integrable_equilibriumMarkedPastSquareWork hrate ht)
  refine hequilibrium.congr ?_
  filter_upwards [
    ae_stationaryPoissonWorkPastSquareAggregate_eq_equilibriumMarkedPastSquareWork
      hrate t] with z hz
  exact hz.symm

/-- The expected literal stationary squared-mark reward of arrivals in
`[-t,0)` is twice its Poisson exposure. -/
theorem integral_stationaryPoissonWorkPastSquareAggregate
    {rate t : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) :
    ∫ z, stationaryPoissonWorkPastSquareAggregate z t ∂stationaryPoissonWorkMeasure rate =
      2 * rate * t := by
  calc
    ∫ z, stationaryPoissonWorkPastSquareAggregate z t ∂stationaryPoissonWorkMeasure rate =
        ∫ z, equilibriumMarkedPastSquareWork (stationaryPoissonWorkToEquilibrium z) t
          ∂stationaryPoissonWorkMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            exact
              ae_stationaryPoissonWorkPastSquareAggregate_eq_equilibriumMarkedPastSquareWork
                hrate t
    _ = ∫ y, equilibriumMarkedPastSquareWork y t
          ∂((equilibriumTwoSidedBaseMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ))) := by
            simpa [Function.comp_def] using
              (stationaryPoissonWorkToEquilibrium_measurePreserving hrate).hasLaw.integral_comp
                (f := fun y => equilibriumMarkedPastSquareWork y t)
                (measurable_equilibriumMarkedPastSquareWork t).aestronglyMeasurable
    _ = 2 * rate * t := integral_equilibriumMarkedPastSquareWork hrate ht

end

end AppliedModelingLib.Probability.Queueing
