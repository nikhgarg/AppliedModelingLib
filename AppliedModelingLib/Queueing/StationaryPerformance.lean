import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Stationary queueing performance from response tails

This module records measure-theoretic consequences of a stationary tagged-job
response-time law.  A queue construction supplies the tail identity; the
results here turn it into the corresponding mean-performance identity.
-/

namespace AppliedModelingLib
namespace Queueing

open MeasureTheory

/-- Under a finite measure, a nonnegative measurable response time with an
exponential strict tail is integrable. -/
theorem integrable_of_exponential_responseTail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (response : Ω → ℝ) (rate : ℝ)
    (hmeasurable : AEStronglyMeasurable response μ)
    (hnonnegative : 0 ≤ᵐ[μ] response)
    (hrate : 0 < rate)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ.real {omega | t < response omega} = Real.exp (-(rate * t))) :
    Integrable response μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable hmeasurable hnonnegative).mp
  rw [lintegral_eq_lintegral_meas_lt μ hnonnegative hmeasurable.aemeasurable]
  apply ne_of_lt
  calc
    ∫⁻ t in Set.Ioi 0, μ {omega | t < response omega} =
        ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (Real.exp (-(rate * t))) := by
          apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht
          change μ {omega | t < response omega} =
            ENNReal.ofReal (Real.exp (-(rate * t)))
          have hfinite : μ {omega | t < response omega} ≠ (⊤ : ENNReal) :=
            measure_ne_top μ _
          rw [← ENNReal.ofReal_toReal hfinite]
          simpa only [Measure.real] using
            congrArg ENNReal.ofReal (htail t (le_of_lt ht))
    _ < (⊤ : ENNReal) := by
      have hexp : IntegrableOn (fun t : ℝ => Real.exp ((-rate) * t))
          (Set.Ioi 0) volume :=
        integrableOn_exp_mul_Ioi (show -rate < 0 by linarith) 0
      have hrewrite : ∀ t : ℝ,
          Real.exp (-(rate * t)) = Real.exp ((-rate) * t) := by
        intro t
        congr 1
        ring
      refine (lintegral_congr_ae (Filter.Eventually.of_forall fun t => ?_)).trans_lt
        hexp.lintegral_lt_top
      rw [hrewrite t]

/-- An integrable nonnegative response time with exponential strict tail has
mean equal to the reciprocal decay rate.  The result is independent of the
queue discipline producing the tail law. -/
theorem integral_eq_inv_of_exponential_responseTail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (response : Ω → ℝ) (rate : ℝ)
    (hintegrable : Integrable response μ)
    (hnonnegative : 0 ≤ᵐ[μ] response)
    (hrate : 0 < rate)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ.real {omega | t < response omega} = Real.exp (-(rate * t))) :
    ∫ omega, response omega ∂μ = rate⁻¹ := by
  calc
    ∫ omega, response omega ∂μ =
        ∫ t in Set.Ioi 0, μ.real {omega | t < response omega} :=
      hintegrable.integral_eq_integral_meas_lt hnonnegative
    _ = ∫ t in Set.Ioi 0, Real.exp (-(rate * t)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact htail t (le_of_lt ht)
    _ = rate⁻¹ := by
      rw [show (fun t : ℝ => Real.exp (-(rate * t))) =
        (fun t : ℝ => Real.exp ((-rate) * t)) by
          funext t
          congr 1
          ring,
        integral_exp_mul_Ioi (show -rate < 0 by linarith) 0]
      simp

/-- A finite-measure version of
`integral_eq_inv_of_exponential_responseTail` which derives integrability
from the tail law. -/
theorem integral_eq_inv_of_exponential_responseTail_of_finite
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (response : Ω → ℝ) (rate : ℝ)
    (hmeasurable : AEStronglyMeasurable response μ)
    (hnonnegative : 0 ≤ᵐ[μ] response)
    (hrate : 0 < rate)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ.real {omega | t < response omega} = Real.exp (-(rate * t))) :
    ∫ omega, response omega ∂μ = rate⁻¹ := by
  exact integral_eq_inv_of_exponential_responseTail μ response rate
    (integrable_of_exponential_responseTail μ response rate hmeasurable
      hnonnegative hrate htail)
    hnonnegative hrate htail

end Queueing
end AppliedModelingLib
