import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkMGF
import AppliedModelingLib.Foundations.Probability.StationaryPoissonWorkFutureRate

/-!
# Exponential moments of stationary Poisson future work

This module transports the canonical compound-Poisson MGF to both the
equilibrium-coordinate and literal stationary future-work ledgers.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory Filter
open AppliedModelingLib.Probability.PoissonProcess

noncomputable section

/-- Equilibrium-coordinate future marked work has an integrable positive
exponential moment below the unit-exponential mark boundary. -/
theorem integrable_exp_mul_equilibriumMarkedFutureWork
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    Integrable (fun z => Real.exp (tilt * equilibriumMarkedFutureWork z t))
      ((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedFutureWork, equilibriumFutureMarkedInput,
    Function.comp_def] using
    ((equilibriumFutureMarkedInput_measurePreserving hrate).integrable_comp
      ((measurable_const.mul
        (measurable_canonicalMarkedWork t)).exp.aestronglyMeasurable)).mpr
      (integrable_exp_mul_canonicalMarkedWork hrate ht htilt)

/-- The equilibrium-coordinate future-work MGF is the compound-Poisson MGF. -/
theorem integral_exp_mul_equilibriumMarkedFutureWork
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    ∫ z, Real.exp (tilt * equilibriumMarkedFutureWork z t)
      ∂((equilibriumTwoSidedBaseMeasure rate).prod
        (twoSidedInterarrivalMeasure (1 : ℝ))) =
      Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) := by
  letI : IsProbabilityMeasure (equilibriumTwoSidedBaseMeasure rate) :=
    isProbabilityMeasure_equilibriumTwoSidedBaseMeasure hrate
  letI : IsProbabilityMeasure (twoSidedInterarrivalMeasure (1 : ℝ)) :=
    isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  simpa [equilibriumMarkedFutureWork, equilibriumFutureMarkedInput,
    Function.comp_def] using
    (equilibriumFutureMarkedInput_measurePreserving hrate).hasLaw.integral_comp
      (f := fun y : (ℕ → ℝ) × (ℕ → ℝ) =>
        Real.exp (tilt * canonicalMarkedWork y.1 y.2 t))
      ((measurable_const.mul
        (measurable_canonicalMarkedWork t)).exp.aestronglyMeasurable) |>.trans
      (integral_exp_mul_canonicalMarkedWork hrate ht htilt)

/-- Literal stationary finite future work has an integrable positive
exponential moment below the unit-exponential mark boundary. -/
theorem integrable_exp_mul_stationaryPoissonWorkFutureAggregate
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    Integrable (fun z =>
      Real.exp (tilt * stationaryPoissonWorkFutureAggregate z t))
      (stationaryPoissonWorkMeasure rate) := by
  letI : IsProbabilityMeasure (stationaryPoissonWorkMeasure rate) :=
    isProbabilityMeasure_stationaryPoissonWorkMeasure hrate
  have hequilibrium : Integrable (fun z =>
      Real.exp (tilt * equilibriumMarkedFutureWork
        (stationaryPoissonWorkToEquilibrium z) t))
      (stationaryPoissonWorkMeasure rate) := by
    simpa [Function.comp_def] using
      ((stationaryPoissonWorkToEquilibrium_measurePreserving hrate).integrable_comp
        ((measurable_const.mul
          (measurable_equilibriumMarkedFutureWork t)).exp.aestronglyMeasurable)).mpr
        (integrable_exp_mul_equilibriumMarkedFutureWork hrate ht htilt)
  refine hequilibrium.congr ?_
  filter_upwards [ae_stationaryPoissonWorkFutureAggregate_eq_equilibriumMarkedFutureWork
    hrate t] with z hz
  rw [hz]

/-- The literal stationary future-work MGF is the compound-Poisson MGF. -/
theorem integral_exp_mul_stationaryPoissonWorkFutureAggregate
    {rate t tilt : ℝ} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    ∫ z, Real.exp (tilt * stationaryPoissonWorkFutureAggregate z t)
      ∂stationaryPoissonWorkMeasure rate =
      Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) := by
  calc
    ∫ z, Real.exp (tilt * stationaryPoissonWorkFutureAggregate z t)
        ∂stationaryPoissonWorkMeasure rate =
        ∫ z, Real.exp (tilt * equilibriumMarkedFutureWork
          (stationaryPoissonWorkToEquilibrium z) t)
          ∂stationaryPoissonWorkMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [ae_stationaryPoissonWorkFutureAggregate_eq_equilibriumMarkedFutureWork
              hrate t] with z hz
            rw [hz]
    _ = ∫ y, Real.exp (tilt * equilibriumMarkedFutureWork y t)
          ∂((equilibriumTwoSidedBaseMeasure rate).prod
            (twoSidedInterarrivalMeasure (1 : ℝ))) := by
              simpa [Function.comp_def] using
                (stationaryPoissonWorkToEquilibrium_measurePreserving hrate).hasLaw.integral_comp
                  (f := fun y => Real.exp (tilt * equilibriumMarkedFutureWork y t))
                  ((measurable_const.mul
                    (measurable_equilibriumMarkedFutureWork t)).exp.aestronglyMeasurable)
    _ = Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) :=
      integral_exp_mul_equilibriumMarkedFutureWork hrate ht htilt

end

end AppliedModelingLib.Probability.Queueing
