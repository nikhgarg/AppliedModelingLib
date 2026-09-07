import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCountMGF
import AppliedModelingLib.Foundations.Probability.ExponentialMarkedRenewalWorkRate

/-!
# Exponential moments of marked exponential renewal input

The independently marked canonical exponential renewal process has an exact
fixed-horizon compound-Poisson moment-generating function.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter

noncomputable section

/-- A finite-horizon marked exponential-renewal workload has an integrable
positive exponential moment below the unit-exponential mark boundary. -/
theorem integrable_exp_mul_canonicalMarkedWork
    {rate t tilt : Real} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    Integrable (fun z : (Nat -> Real) × (Nat -> Real) =>
      Real.exp (tilt * canonicalMarkedWork z.1 z.2 t))
      ((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  let f : (Nat -> Real) × (Nat -> Real) -> Real :=
    fun z => Real.exp (tilt * canonicalMarkedWork z.1 z.2 t)
  have hmeas : Measurable f := by
    exact ((measurable_const.mul (measurable_canonicalMarkedWork t)).exp)
  refine (MeasureTheory.integrable_prod_iff hmeas.aestronglyMeasurable).2 ?_
  constructor
  · filter_upwards with gaps
    simpa [f] using
      integrable_exp_mul_canonicalMarkedWork_over_marks gaps t tilt htilt
  · have hnorm : (fun gaps : Nat -> Real =>
        ∫ marks, ‖f (gaps, marks)‖ ∂exponentialInterarrivalMeasure (1 : Real)) =
        fun gaps => (1 / (1 - tilt)) ^ canonicalRenewalCount t gaps := by
      funext gaps
      calc
        ∫ marks, ‖f (gaps, marks)‖
            ∂exponentialInterarrivalMeasure (1 : Real) =
            ∫ marks, f (gaps, marks)
              ∂exponentialInterarrivalMeasure (1 : Real) := by
                refine MeasureTheory.integral_congr_ae ?_
                filter_upwards with marks
                simp [f, Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
        _ = (1 / (1 - tilt)) ^ canonicalRenewalCount t gaps := by
              simpa [f] using
                integral_exp_mul_canonicalMarkedWork_over_marks gaps t tilt htilt
    refine (integrable_pow_canonicalRenewalCount hrate ht (1 / (1 - tilt))).congr ?_
    filter_upwards with gaps
    exact (congrFun hnorm gaps).symm

/-- The fixed-horizon compound-Poisson moment-generating function of
independently unit-exponentially marked exponential-renewal input. -/
theorem integral_exp_mul_canonicalMarkedWork
    {rate t tilt : Real} (hrate : 0 < rate) (ht : 0 ≤ t) (htilt : tilt < 1) :
    ∫ z : (Nat -> Real) × (Nat -> Real),
        Real.exp (tilt * canonicalMarkedWork z.1 z.2 t)
      ∂((exponentialInterarrivalMeasure rate).prod
        (exponentialInterarrivalMeasure (1 : Real))) =
      Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) := by
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure rate) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure hrate
  letI : IsProbabilityMeasure (exponentialInterarrivalMeasure (1 : Real)) :=
    isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hint := integrable_exp_mul_canonicalMarkedWork hrate ht htilt
  calc
    ∫ z : (Nat -> Real) × (Nat -> Real),
        Real.exp (tilt * canonicalMarkedWork z.1 z.2 t)
        ∂((exponentialInterarrivalMeasure rate).prod
          (exponentialInterarrivalMeasure (1 : Real))) =
        ∫ gaps, ∫ marks,
            Real.exp (tilt * canonicalMarkedWork gaps marks t)
            ∂exponentialInterarrivalMeasure (1 : Real)
          ∂exponentialInterarrivalMeasure rate := by
            exact MeasureTheory.integral_prod _ hint
    _ = ∫ gaps, (1 / (1 - tilt)) ^ canonicalRenewalCount t gaps
          ∂exponentialInterarrivalMeasure rate := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with gaps
            exact integral_exp_mul_canonicalMarkedWork_over_marks gaps t tilt htilt
    _ = Real.exp ((rate * t) * (1 / (1 - tilt) - 1)) :=
      integral_pow_canonicalRenewalCount hrate ht (1 / (1 - tilt))

end

end AppliedModelingLib.Probability.PoissonProcess
