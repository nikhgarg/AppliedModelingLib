import GN21DriverSurgePricing.Theorem2ComponentVariation

/-!
# Source endpoint-derivative bridge for GN21 Theorem 4

The third price branch of source Theorem 4 is stated using the derivative of
the *actual aggregate policy functional* at an upper endpoint of an interval
component of an open policy.  This file records that condition literally.
It does not replace it with a pointwise marginal-response condition.

The first results below establish the direct variational consequence available
from that source condition: an open optimum cannot retain a genuine bounded
connected component.  The later analytic layer will connect a locally
separated component path to the Appendix-D quotient calculus.
-/

open AppliedModelingLib
open MeasureTheory
open scoped ENNReal Topology symmDiff

namespace GN21DriverSurgePricing

noncomputable section

/-! ## Actual component paths on a two-sided neighborhood -/

/--
The Appendix-D exit-weight decomposition remains valid to the right of an
upper endpoint when the actual component is locally separated from the rest
of the policy.  This is the geometric fact missing from the inward-only
identity in `Theorem2ComponentVariation`.
-/
theorem gn21ExitWeightIntegral_gn21ComponentUpperPath_of_locallySeparated
    (mu : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius)
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (sigma \ Set.Ioo lower upper) mu)
    (hq_integrable_interval :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (Set.Ioo lower x) mu) :
    gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI
        (gn21ComponentUpperPath sigma lower upper x) =
      gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI
          (sigma \ Set.Ioo lower upper) +
        arrivalRate *
          ∫ tau in Set.Ioo lower x, gn21SwitchProb switchIJ switchJI tau ∂mu := by
  unfold gn21ComponentUpperPath
  exact gn21ExitWeightIntegral_union mu arrivalRate switchIJ switchJI
    (sigma \ Set.Ioo lower upper) (Set.Ioo lower x)
    (disjoint_gn21ComponentUpperPath_background_interval_of_locallySeparated
      sigma lower upper radius x hseparated hx_upper)
    measurableSet_Ioo hq_integrable_background hq_integrable_interval

/-- Two-sided local-separation version of the actual Appendix-D time identity. -/
theorem gn21ScaledStateTime_gn21ComponentUpperPath_of_locallySeparated
    (mu : Measure TripLength) (arrivalRate : ℝ)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius)
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (sigma \ Set.Ioo lower upper) mu)
    (htime_integrable_interval :
      IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x) mu) :
    gn21ScaledStateTime mu arrivalRate
        (gn21ComponentUpperPath sigma lower upper x) =
      gn21ScaledStateTime mu arrivalRate (sigma \ Set.Ioo lower upper) +
        arrivalRate * ∫ tau in Set.Ioo lower x, tau ∂mu := by
  unfold gn21ComponentUpperPath
  exact gn21ScaledStateTime_union mu arrivalRate
    (sigma \ Set.Ioo lower upper) (Set.Ioo lower x)
    (disjoint_gn21ComponentUpperPath_background_interval_of_locallySeparated
      sigma lower upper radius x hseparated hx_upper)
    measurableSet_Ioo htime_integrable_background htime_integrable_interval

/-- Two-sided local-separation version of the actual Appendix-D earning identity. -/
theorem gn21ScaledStateEarning_gn21ComponentUpperPath_of_locallySeparated
    (mu : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius)
    (hw_integrable_background :
      IntegrableOn w (sigma \ Set.Ioo lower upper) mu)
    (hw_integrable_interval :
      IntegrableOn w (Set.Ioo lower x) mu) :
    gn21ScaledStateEarning mu arrivalRate w
        (gn21ComponentUpperPath sigma lower upper x) =
      gn21ScaledStateEarning mu arrivalRate w (sigma \ Set.Ioo lower upper) +
        arrivalRate * ∫ tau in Set.Ioo lower x, w tau ∂mu := by
  unfold gn21ComponentUpperPath
  exact gn21ScaledStateEarning_union mu arrivalRate w
    (sigma \ Set.Ioo lower upper) (Set.Ioo lower x)
    (disjoint_gn21ComponentUpperPath_background_interval_of_locallySeparated
      sigma lower upper radius x hseparated hx_upper)
    measurableSet_Ioo hw_integrable_background hw_integrable_interval

/--
The moving open interval in a component path realizes the usual oriented
interval integral under a Lebesgue density.  The endpoint difference is
handled by the atomlessness of volume, rather than by changing the policy
syntax from `Ioo` to `Ioc`.
-/
theorem setIntegral_Ioo_withDensity_eq_intervalIntegral
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (f : TripLength → ℝ)
    {lower x : TripLength} (hlower_x : lower ≤ x) :
    ∫ tau in Set.Ioo lower x, f tau ∂(volume.withDensity
        (fun tau => (density tau : ℝ≥0∞))) =
      ∫ tau in lower..x, f tau * (density tau : ℝ) := by
  rw [intervalIntegral.integral_of_le hlower_x]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (μ := volume) (f := density) hdensity_meas f measurableSet_Ioo]
  rw [integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro tau _htau
  simp [Algebra.smul_def, mul_comm]

/-- Realization of the local component `Q` path under a Lebesgue density. -/
theorem gn21ExitWeightIntegral_componentUpperPath_withDensity_eq_componentUpperQiPath
    (arrivalRate switchIJ switchJI : ℝ)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius) (hlower_x : lower ≤ x)
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (sigma \ Set.Ioo lower upper)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞)))
    (hq_integrable_interval :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (Set.Ioo lower x)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))) :
    gn21ExitWeightIntegral
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21ComponentUpperPath sigma lower upper x) =
      gn21ComponentUpperQiPath
        (gn21ExitWeightIntegral
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate switchIJ switchJI (sigma \ Set.Ioo lower upper))
        arrivalRate lower (fun tau => (density tau : ℝ))
        (gn21SwitchProb switchIJ switchJI) x := by
  rw [gn21ExitWeightIntegral_gn21ComponentUpperPath_of_locallySeparated
    (volume.withDensity fun tau => (density tau : ℝ≥0∞))
    arrivalRate switchIJ switchJI sigma lower upper radius x hseparated
    hx_upper hq_integrable_background hq_integrable_interval]
  unfold gn21ComponentUpperQiPath
  rw [setIntegral_Ioo_withDensity_eq_intervalIntegral density hdensity_meas
    (gn21SwitchProb switchIJ switchJI) hlower_x]

/-- Realization of the local component `T` path under a Lebesgue density. -/
theorem gn21ScaledStateTime_componentUpperPath_withDensity_eq_componentUpperTiPath
    (arrivalRate : ℝ)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius) (hlower_x : lower ≤ x)
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (sigma \ Set.Ioo lower upper)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞)))
    (htime_integrable_interval :
      IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))) :
    gn21ScaledStateTime
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate (gn21ComponentUpperPath sigma lower upper x) =
      gn21ComponentUpperTiPath
        (gn21ScaledStateTime
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate (sigma \ Set.Ioo lower upper))
        arrivalRate lower (fun tau => (density tau : ℝ)) x := by
  rw [gn21ScaledStateTime_gn21ComponentUpperPath_of_locallySeparated
    (volume.withDensity fun tau => (density tau : ℝ≥0∞))
    arrivalRate sigma lower upper radius x hseparated hx_upper
    htime_integrable_background htime_integrable_interval]
  unfold gn21ComponentUpperTiPath
  rw [setIntegral_Ioo_withDensity_eq_intervalIntegral density hdensity_meas
    (fun tau : TripLength => tau) hlower_x]

/-- Realization of the local component `W` path under a Lebesgue density. -/
theorem gn21ScaledStateEarning_componentUpperPath_withDensity_eq_componentUpperWiPath
    (arrivalRate : ℝ) (w : PricingFunction)
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (density : TripLength → NNReal)
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius) (hlower_x : lower ≤ x)
    (hw_integrable_background :
      IntegrableOn w (sigma \ Set.Ioo lower upper)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞)))
    (hw_integrable_interval :
      IntegrableOn w (Set.Ioo lower x)
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))) :
    gn21ScaledStateEarning
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate w (gn21ComponentUpperPath sigma lower upper x) =
      gn21ComponentUpperWiPath
        (gn21ScaledStateEarning
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate w (sigma \ Set.Ioo lower upper))
        arrivalRate lower (fun tau => (density tau : ℝ)) w x := by
  rw [gn21ScaledStateEarning_gn21ComponentUpperPath_of_locallySeparated
    (volume.withDensity fun tau => (density tau : ℝ≥0∞))
    arrivalRate w sigma lower upper radius x hseparated hx_upper
    hw_integrable_background hw_integrable_interval]
  unfold gn21ComponentUpperWiPath
  rw [setIntegral_Ioo_withDensity_eq_intervalIntegral density hdensity_meas
    w hlower_x]

/--
The actual two-state aggregate objective agrees with the fixed-background
Appendix-D quotient on a locally separated component path.  This is a
pointwise identity; the derivative transport below obtains its neighborhood
from the displayed radius rather than assuming it as a certificate.
-/
theorem gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_withDensity_eq
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper radius x : TripLength)
    (density : TripLength → NNReal)
    (hmu0 : mu 0 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated (rho 0) lower upper radius)
    (hx_upper : x ≤ upper + radius) (hlower_x : lower ≤ x)
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (rho 0 \ Set.Ioo lower upper) (mu 0))
    (hq_integrable_interval :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (Set.Ioo lower x) (mu 0))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 0 \ Set.Ioo lower upper) (mu 0))
    (htime_integrable_interval :
      IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x) (mu 0))
    (hw_integrable_background :
      IntegrableOn (w 0) (rho 0 \ Set.Ioo lower upper) (mu 0))
    (hw_integrable_interval :
      IntegrableOn (w 0) (Set.Ioo lower x) (mu 0)) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 0
          (gn21ComponentUpperPath (rho 0) lower upper x)) =
      gn21AggregateDynamicReward
        (gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (rho 0 \ Set.Ioo lower upper))
          (arrival 0) lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch12 switch21) x)
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
        (gn21ComponentUpperTiPath
          (gn21ScaledStateTime (mu 0) (arrival 0)
            (rho 0 \ Set.Ioo lower upper))
          (arrival 0) lower (fun tau => (density tau : ℝ)) x)
        (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
        (gn21ComponentUpperWiPath
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
            (rho 0 \ Set.Ioo lower upper))
          (arrival 0) lower (fun tau => (density tau : ℝ)) (w 0) x)
        (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) := by
  rw [gn21AggregateDynamicRewardFunctional_apply]
  change
    gn21MeasuredAggregateRewardPrimitives
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1)
        (gn21ComponentUpperPath (rho 0) lower upper x) (rho 1) = _
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [hmu0]
  rw [gn21ExitWeightIntegral_componentUpperPath_withDensity_eq_componentUpperQiPath
    (arrival 0) switch12 switch21 (rho 0) lower upper radius x density
    hdensity_meas hseparated hx_upper hlower_x
    (by simpa [hmu0] using hq_integrable_background)
    (by simpa [hmu0] using hq_integrable_interval)]
  rw [gn21ScaledStateTime_componentUpperPath_withDensity_eq_componentUpperTiPath
    (arrival 0) (rho 0) lower upper radius x density hdensity_meas
    hseparated hx_upper hlower_x
    (by simpa [hmu0] using htime_integrable_background)
    (by simpa [hmu0] using htime_integrable_interval)]
  rw [gn21ScaledStateEarning_componentUpperPath_withDensity_eq_componentUpperWiPath
    (arrival 0) (w 0) (rho 0) lower upper radius x density hdensity_meas
    hseparated hx_upper hlower_x
    (by simpa [hmu0] using hw_integrable_background)
    (by simpa [hmu0] using hw_integrable_interval)]

/-- Symmetric actual-aggregate identity when the surge-state component moves. -/
theorem gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_withDensity_eq
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper radius x : TripLength)
    (density : TripLength → NNReal)
    (hmu1 : mu 1 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated (rho 1) lower upper radius)
    (hx_upper : x ≤ upper + radius) (hlower_x : lower ≤ x)
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        (rho 1 \ Set.Ioo lower upper) (mu 1))
    (hq_integrable_interval :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        (Set.Ioo lower x) (mu 1))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 1 \ Set.Ioo lower upper) (mu 1))
    (htime_integrable_interval :
      IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x) (mu 1))
    (hw_integrable_background :
      IntegrableOn (w 1) (rho 1 \ Set.Ioo lower upper) (mu 1))
    (hw_integrable_interval :
      IntegrableOn (w 1) (Set.Ioo lower x) (mu 1)) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 1
          (gn21ComponentUpperPath (rho 1) lower upper x)) =
      gn21AggregateDynamicReward
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
        (gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (rho 1 \ Set.Ioo lower upper))
          (arrival 1) lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch21 switch12) x)
        (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
        (gn21ComponentUpperTiPath
          (gn21ScaledStateTime (mu 1) (arrival 1)
            (rho 1 \ Set.Ioo lower upper))
          (arrival 1) lower (fun tau => (density tau : ℝ)) x)
        (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
        (gn21ComponentUpperWiPath
          (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
            (rho 1 \ Set.Ioo lower upper))
          (arrival 1) lower (fun tau => (density tau : ℝ)) (w 1) x) := by
  rw [gn21AggregateDynamicRewardFunctional_apply]
  change
    gn21MeasuredAggregateRewardPrimitives
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1)
        (rho 0) (gn21ComponentUpperPath (rho 1) lower upper x) = _
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [hmu1]
  rw [gn21ExitWeightIntegral_componentUpperPath_withDensity_eq_componentUpperQiPath
    (arrival 1) switch21 switch12 (rho 1) lower upper radius x density
    hdensity_meas hseparated hx_upper hlower_x
    (by simpa [hmu1] using hq_integrable_background)
    (by simpa [hmu1] using hq_integrable_interval)]
  rw [gn21ScaledStateTime_componentUpperPath_withDensity_eq_componentUpperTiPath
    (arrival 1) (rho 1) lower upper radius x density hdensity_meas
    hseparated hx_upper hlower_x
    (by simpa [hmu1] using htime_integrable_background)
    (by simpa [hmu1] using htime_integrable_interval)]
  rw [gn21ScaledStateEarning_componentUpperPath_withDensity_eq_componentUpperWiPath
    (arrival 1) (w 1) (rho 1) lower upper radius x density hdensity_meas
    hseparated hx_upper hlower_x
    (by simpa [hmu1] using hw_integrable_background)
    (by simpa [hmu1] using hw_integrable_interval)]

/-- The Lemma 6 derivative value for a fixed-background upper-component path. -/
def gn21ComponentUpperAggregateDerivativeValue
    (fixedQi fixedTi fixedWi arrivalRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : TripLength → ℝ) : ℝ :=
  ((arrivalRate * density u) * Qj *
    gn21DerivativeSignKernel (switchProb u) u (payment u)
      (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density switchProb u)
      Qj
      (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
      Tj
      (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density payment u)
      Wj /
    (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density switchProb u * Tj +
      Qj * gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u) ^ 2)

/-- Named version of the existing quotient-calculus derivative formula. -/
theorem gn21ComponentUpperAggregatePath_hasDerivAt_value
    (fixedQi fixedTi fixedWi arrivalRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : TripLength → ℝ)
    (hq_int :
      IntervalIntegrable (fun tau => switchProb tau * density tau) volume
        lowerEndpoint u)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun tau => switchProb tau * density tau) (𝓝 u))
    (hq_cont : ContinuousAt (fun tau => switchProb tau * density tau) u)
    (hw_int :
      IntervalIntegrable (fun tau => payment tau * density tau) volume
        lowerEndpoint u)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun tau => payment tau * density tau) (𝓝 u))
    (hw_cont : ContinuousAt (fun tau => payment tau * density tau) u)
    (ht_int :
      IntervalIntegrable (fun tau => tau * density tau) volume lowerEndpoint u)
    (ht_meas :
      StronglyMeasurableAtFilter (fun tau => tau * density tau) (𝓝 u))
    (ht_cont : ContinuousAt (fun tau => tau * density tau) u)
    (hden :
      gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
          switchProb u * Tj +
        Qj * gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u ≠ 0) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicReward
          (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb x)
          Qj
          (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density x)
          Tj
          (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density
            payment x)
          Wj)
      (gn21ComponentUpperAggregateDerivativeValue
        fixedQi fixedTi fixedWi arrivalRate lowerEndpoint u Qj Tj Wj
        density switchProb payment)
      u := by
  simpa [gn21ComponentUpperAggregateDerivativeValue] using
    gn21ComponentUpperAggregatePath_hasDerivAt
      fixedQi fixedTi fixedWi arrivalRate lowerEndpoint u Qj Tj Wj
      density switchProb payment
      hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont hden

/--
Transport the quotient derivative back to the actual non-surge policy path.
Unlike the older interval formula, every path term here is obtained from the
current policy's component complement.  Local separation supplies the real
neighborhood needed by `HasDerivAt`.
-/
theorem gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_hasDerivAt_of_locallySeparated
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper radius : TripLength)
    (density : TripLength → NNReal)
    (hmu0 : mu 0 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated (rho 0) lower upper radius)
    (hlower_upper : lower < upper) (hradius_pos : 0 < radius)
    (hq_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn
          (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
          (Set.Ioo lower x) (mu 0))
    (htime_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x) (mu 0))
    (hw_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn (w 0) (Set.Ioo lower x) (mu 0))
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (rho 0 \ Set.Ioo lower upper) (mu 0))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 0 \ Set.Ioo lower upper) (mu 0))
    (hw_integrable_background :
      IntegrableOn (w 0) (rho 0 \ Set.Ioo lower upper) (mu 0))
    (hq_int :
      IntervalIntegrable
        (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
        volume lower upper)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
        (𝓝 upper))
    (hq_cont : ContinuousAt
      (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
      upper)
    (hw_int :
      IntervalIntegrable (fun tau => (w 0) tau * (density tau : ℝ))
        volume lower upper)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun tau => (w 0) tau * (density tau : ℝ)) (𝓝 upper))
    (hw_cont : ContinuousAt
      (fun tau => (w 0) tau * (density tau : ℝ)) upper)
    (ht_int :
      IntervalIntegrable (fun tau => tau * (density tau : ℝ)) volume lower upper)
    (ht_meas :
      StronglyMeasurableAtFilter
        (fun tau => tau * (density tau : ℝ)) (𝓝 upper))
    (ht_cont : ContinuousAt
      (fun tau => tau * (density tau : ℝ)) upper)
    (hden :
      gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (rho 0 \ Set.Ioo lower upper))
          (arrival 0) lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch12 switch21) upper *
          gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
        gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
          gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 0) (arrival 0)
              (rho 0 \ Set.Ioo lower upper))
            (arrival 0) lower (fun tau => (density tau : ℝ)) upper ≠ 0) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 0
            (gn21ComponentUpperPath (rho 0) lower upper x)))
      (gn21ComponentUpperAggregateDerivativeValue
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
          (rho 0 \ Set.Ioo lower upper))
        (gn21ScaledStateTime (mu 0) (arrival 0)
          (rho 0 \ Set.Ioo lower upper))
        (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
          (rho 0 \ Set.Ioo lower upper))
        (arrival 0) lower upper
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
        (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
        (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1))
        (fun tau => (density tau : ℝ))
        (gn21SwitchProb switch12 switch21) (w 0))
      upper := by
  let fixedQi :=
    gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
      (rho 0 \ Set.Ioo lower upper)
  let fixedTi :=
    gn21ScaledStateTime (mu 0) (arrival 0) (rho 0 \ Set.Ioo lower upper)
  let fixedWi :=
    gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
      (rho 0 \ Set.Ioo lower upper)
  let Qj := gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1)
  let Tj := gn21ScaledStateTime (mu 1) (arrival 1) (rho 1)
  let Wj := gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)
  let F : TripLength → ℝ := fun x =>
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
      (Function.update rho 0
        (gn21ComponentUpperPath (rho 0) lower upper x))
  let G : TripLength → ℝ := fun x =>
    gn21AggregateDynamicReward
      (gn21ComponentUpperQiPath fixedQi (arrival 0) lower
        (fun tau => (density tau : ℝ)) (gn21SwitchProb switch12 switch21) x)
      Qj
      (gn21ComponentUpperTiPath fixedTi (arrival 0) lower
        (fun tau => (density tau : ℝ)) x)
      Tj
      (gn21ComponentUpperWiPath fixedWi (arrival 0) lower
        (fun tau => (density tau : ℝ)) (w 0) x)
      Wj
  change HasDerivAt F
    (gn21ComponentUpperAggregateDerivativeValue
      fixedQi fixedTi fixedWi (arrival 0) lower upper Qj Tj Wj
      (fun tau => (density tau : ℝ))
      (gn21SwitchProb switch12 switch21) (w 0)) upper
  have hquotient : HasDerivAt G
      (gn21ComponentUpperAggregateDerivativeValue
        fixedQi fixedTi fixedWi (arrival 0) lower upper Qj Tj Wj
        (fun tau => (density tau : ℝ))
        (gn21SwitchProb switch12 switch21) (w 0)) upper := by
    exact gn21ComponentUpperAggregatePath_hasDerivAt_value
      fixedQi fixedTi fixedWi (arrival 0) lower upper Qj Tj Wj
      (fun tau => (density tau : ℝ))
      (gn21SwitchProb switch12 switch21) (w 0)
      hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont
      (by simpa [fixedQi, fixedTi, Qj, Tj] using hden)
  have hnear_lower : ∀ᶠ x in 𝓝 upper, lower ≤ x :=
    eventually_ge_nhds hlower_upper
  have hnear_upper : ∀ᶠ x in 𝓝 upper, x ≤ upper + radius :=
    eventually_le_nhds (by linarith)
  have hpath_eq : F =ᶠ[𝓝 upper] G := by
    filter_upwards [hnear_lower, hnear_upper] with x hlower_x hx_upper
    dsimp [F, G, fixedQi, fixedTi, fixedWi, Qj, Tj, Wj]
    exact
      gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_withDensity_eq
        mu arrival switch12 switch21 w rho lower upper radius x density
        hmu0 hdensity_meas hseparated hx_upper hlower_x
        hq_integrable_background (hq_integrable_local x hlower_x hx_upper)
        htime_integrable_background
        (htime_integrable_local x hlower_x hx_upper)
        hw_integrable_background (hw_integrable_local x hlower_x hx_upper)
  exact hquotient.congr_of_eventuallyEq hpath_eq

/--
Transport the fixed-background quotient derivative back to the actual surge
policy path.  The quotient derivative is applied with its moving state first,
then transported through the proved symmetry of the aggregate quotient.
-/
theorem gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_hasDerivAt_of_locallySeparated
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper radius : TripLength)
    (density : TripLength → NNReal)
    (hmu1 : mu 1 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated : gn21ComponentUpperLocallySeparated (rho 1) lower upper radius)
    (hlower_upper : lower < upper) (hradius_pos : 0 < radius)
    (hq_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn
          (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
          (Set.Ioo lower x) (mu 1))
    (htime_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn (fun tau : TripLength => tau) (Set.Ioo lower x) (mu 1))
    (hw_integrable_local : ∀ x : TripLength,
      lower ≤ x → x ≤ upper + radius →
        IntegrableOn (w 1) (Set.Ioo lower x) (mu 1))
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        (rho 1 \ Set.Ioo lower upper) (mu 1))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 1 \ Set.Ioo lower upper) (mu 1))
    (hw_integrable_background :
      IntegrableOn (w 1) (rho 1 \ Set.Ioo lower upper) (mu 1))
    (hq_int :
      IntervalIntegrable
        (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
        volume lower upper)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
        (𝓝 upper))
    (hq_cont : ContinuousAt
      (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
      upper)
    (hw_int :
      IntervalIntegrable (fun tau => (w 1) tau * (density tau : ℝ))
        volume lower upper)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun tau => (w 1) tau * (density tau : ℝ)) (𝓝 upper))
    (hw_cont : ContinuousAt
      (fun tau => (w 1) tau * (density tau : ℝ)) upper)
    (ht_int :
      IntervalIntegrable (fun tau => tau * (density tau : ℝ)) volume lower upper)
    (ht_meas :
      StronglyMeasurableAtFilter (fun tau => tau * (density tau : ℝ)) (𝓝 upper))
    (ht_cont : ContinuousAt
      (fun tau => tau * (density tau : ℝ)) upper)
    (hden :
      gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
          gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 1) (arrival 1)
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ)) upper +
        gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (rho 1 \ Set.Ioo lower upper))
          (arrival 1) lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch21 switch12) upper *
          gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) ≠ 0) :
    HasDerivAt
      (fun x =>
        gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1
            (gn21ComponentUpperPath (rho 1) lower upper x)))
      (gn21ComponentUpperAggregateDerivativeValue
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
          (rho 1 \ Set.Ioo lower upper))
        (gn21ScaledStateTime (mu 1) (arrival 1)
          (rho 1 \ Set.Ioo lower upper))
        (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
          (rho 1 \ Set.Ioo lower upper))
        (arrival 1) lower upper
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
        (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
        (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
        (fun tau => (density tau : ℝ))
        (gn21SwitchProb switch21 switch12) (w 1))
      upper := by
  let fixedQi :=
    gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
      (rho 1 \ Set.Ioo lower upper)
  let fixedTi :=
    gn21ScaledStateTime (mu 1) (arrival 1) (rho 1 \ Set.Ioo lower upper)
  let fixedWi :=
    gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
      (rho 1 \ Set.Ioo lower upper)
  let Qj := gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0)
  let Tj := gn21ScaledStateTime (mu 0) (arrival 0) (rho 0)
  let Wj := gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0)
  let F : TripLength → ℝ := fun x =>
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
      (Function.update rho 1
        (gn21ComponentUpperPath (rho 1) lower upper x))
  let G : TripLength → ℝ := fun x =>
    gn21AggregateDynamicReward
      (gn21ComponentUpperQiPath fixedQi (arrival 1) lower
        (fun tau => (density tau : ℝ)) (gn21SwitchProb switch21 switch12) x)
      Qj
      (gn21ComponentUpperTiPath fixedTi (arrival 1) lower
        (fun tau => (density tau : ℝ)) x)
      Tj
      (gn21ComponentUpperWiPath fixedWi (arrival 1) lower
        (fun tau => (density tau : ℝ)) (w 1) x)
      Wj
  change HasDerivAt F
    (gn21ComponentUpperAggregateDerivativeValue
      fixedQi fixedTi fixedWi (arrival 1) lower upper Qj Tj Wj
      (fun tau => (density tau : ℝ))
      (gn21SwitchProb switch21 switch12) (w 1)) upper
  have hquotient : HasDerivAt G
      (gn21ComponentUpperAggregateDerivativeValue
        fixedQi fixedTi fixedWi (arrival 1) lower upper Qj Tj Wj
        (fun tau => (density tau : ℝ))
        (gn21SwitchProb switch21 switch12) (w 1)) upper := by
    exact gn21ComponentUpperAggregatePath_hasDerivAt_value
      fixedQi fixedTi fixedWi (arrival 1) lower upper Qj Tj Wj
      (fun tau => (density tau : ℝ))
      (gn21SwitchProb switch21 switch12) (w 1)
      hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont
      (by
        simpa [fixedQi, fixedTi, Qj, Tj, add_comm, mul_comm, mul_left_comm,
          mul_assoc] using hden)
  have hnear_lower : ∀ᶠ x in 𝓝 upper, lower ≤ x :=
    eventually_ge_nhds hlower_upper
  have hnear_upper : ∀ᶠ x in 𝓝 upper, x ≤ upper + radius :=
    eventually_le_nhds (by linarith)
  have hpath_eq : F =ᶠ[𝓝 upper] G := by
    filter_upwards [hnear_lower, hnear_upper] with x hlower_x hx_upper
    dsimp [F, G, fixedQi, fixedTi, fixedWi, Qj, Tj, Wj]
    calc
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
          (Function.update rho 1
            (gn21ComponentUpperPath (rho 1) lower upper x)) =
        gn21AggregateDynamicReward
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ComponentUpperQiPath
            (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ))
            (gn21SwitchProb switch21 switch12) x)
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 1) (arrival 1)
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ)) x)
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
          (gn21ComponentUpperWiPath
            (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ)) (w 1) x) := by
          exact
            gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_withDensity_eq
              mu arrival switch12 switch21 w rho lower upper radius x density
              hmu1 hdensity_meas hseparated hx_upper hlower_x
              hq_integrable_background (hq_integrable_local x hlower_x hx_upper)
              htime_integrable_background
              (htime_integrable_local x hlower_x hx_upper)
              hw_integrable_background (hw_integrable_local x hlower_x hx_upper)
      _ = gn21AggregateDynamicReward
          (gn21ComponentUpperQiPath
            (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ))
            (gn21SwitchProb switch21 switch12) x)
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
          (gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 1) (arrival 1)
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ)) x)
          (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
          (gn21ComponentUpperWiPath
            (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
              (rho 1 \ Set.Ioo lower upper))
            (arrival 1) lower (fun tau => (density tau : ℝ)) (w 1) x)
          (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0)) :=
        gn21AggregateDynamicReward_swap _ _ _ _ _ _
  exact hquotient.congr_of_eventuallyEq hpath_eq

/--
Direct algebraic sign bridge from the Appendix-D quotient derivative to its
fixed-current marginal response.  This avoids inserting auxiliary state-rate
variables merely to reuse the normalized Lemma 6 response.
-/
theorem gn21AggregateDerivativeValue_sameStrictSign_leftMarginalValue
    (endpointScale q u wi Qi Qj Ti Tj Wi Wj : ℝ)
    (hendpointScale_pos : 0 < endpointScale)
    (hden_pos : 0 < Qi * Tj + Qj * Ti) :
    sameStrictSign
      (endpointScale * Qj *
        gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
        (Qi * Tj + Qj * Ti) ^ 2)
      ((wi - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * u) * Qj +
        q * (Wj - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Tj)) := by
  have hden_ne : Qi * Tj + Qj * Ti ≠ 0 := ne_of_gt hden_pos
  have hmarginal :
      (wi - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * u) * Qj +
          q * (Wj - gn21AggregateDynamicReward Qi Qj Ti Tj Wi Wj * Tj) =
        Qj * gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
          (Qi * Tj + Qj * Ti) := by
    unfold gn21AggregateDynamicReward gn21DerivativeSignKernel
    field_simp [hden_ne]
    ring
  rw [hmarginal]
  have hscale_pos : 0 < endpointScale / (Qi * Tj + Qj * Ti) :=
    div_pos hendpointScale_pos hden_pos
  convert
    sameStrictSign_of_pos_mul_left
      (endpointScale / (Qi * Tj + Qj * Ti))
      (Qj * gn21DerivativeSignKernel q u wi Qi Qj Ti Tj Wi Wj /
        (Qi * Tj + Qj * Ti))
      hscale_pos using 1
  field_simp [hden_ne]

/--
An actual positive endpoint derivative transfers to a response only after a
separately proved derivative calculation for the same path.  This small
calculus lemma keeps that equality-of-path obligation explicit.
-/
theorem response_pos_of_positive_endpoint_derivative_of_same_path_calculus
    {path : TripLength → ℝ} {u derivativeValue responseValue : ℝ}
    (hsource : ∃ sourceDerivative : ℝ,
      HasDerivAt path sourceDerivative u ∧ 0 < sourceDerivative)
    (hcalculus : HasDerivAt path derivativeValue u)
    (hsign : sameStrictSign derivativeValue responseValue) :
    0 < responseValue := by
  rcases hsource with ⟨sourceDerivative, hsource_deriv, hsource_pos⟩
  have hderiv_eq : sourceDerivative = derivativeValue :=
    hsource_deriv.unique hcalculus
  apply sameStrictSign_pos_right hsign
  simpa [← hderiv_eq] using hsource_pos

/--
At a component endpoint whose quotient primitives equal the current-policy
primitives, the calculated derivative has the same strict sign as the actual
non-surge fixed-current marginal response.
-/
theorem gn21ComponentUpperDerivativeValue_sameStrictSign_measuredLeftResponse
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (fixedQi fixedTi fixedWi lower u : ℝ)
    (density : TripLength → ℝ)
    (hQi :
      gn21ComponentUpperQiPath fixedQi arrivalI lower density
          (gn21SwitchProb switchIJ switchJI) u =
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
    (hTi :
      gn21ComponentUpperTiPath fixedTi arrivalI lower density u =
        gn21ScaledStateTime muI arrivalI sigmaI)
    (hWi :
      gn21ComponentUpperWiPath fixedWi arrivalI lower density wI u =
        gn21ScaledStateEarning muI arrivalI wI sigmaI)
    (hendpointScale_pos : 0 < arrivalI * density u)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI) :
    sameStrictSign
      (gn21ComponentUpperAggregateDerivativeValue
        fixedQi fixedTi fixedWi arrivalI lower u
        (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
        (gn21ScaledStateTime muJ arrivalJ sigmaJ)
        (gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ)
        density (gn21SwitchProb switchIJ switchJI) wI)
      (gn21MeasuredLeftMarginalResponseAtCurrent
        muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ u) := by
  have hraw :=
    gn21AggregateDerivativeValue_sameStrictSign_leftMarginalValue
      (arrivalI * density u) (gn21SwitchProb switchIJ switchJI u) u (wI u)
      (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
      (gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
      (gn21ScaledStateTime muI arrivalI sigmaI)
      (gn21ScaledStateTime muJ arrivalJ sigmaJ)
      (gn21ScaledStateEarning muI arrivalI wI sigmaI)
      (gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ)
      hendpointScale_pos hden_pos
  simpa [gn21ComponentUpperAggregateDerivativeValue,
    gn21MeasuredLeftMarginalResponseAtCurrent, hQi, hTi, hWi] using hraw

/--
The same quotient-to-response calculation for a surge-state component.  This
is not a second unproved sign convention: it is the preceding calculation
with the two state roles swapped.
-/
theorem gn21ComponentUpperDerivativeValue_sameStrictSign_measuredRightResponse
    (muI muJ : Measure TripLength)
    (arrivalI arrivalJ switchIJ switchJI : ℝ)
    (wI wJ : PricingFunction) (sigmaI sigmaJ : TripPolicy)
    (fixedQj fixedTj fixedWj lower u : ℝ)
    (density : TripLength → ℝ)
    (hQj :
      gn21ComponentUpperQiPath fixedQj arrivalJ lower density
          (gn21SwitchProb switchJI switchIJ) u =
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ)
    (hTj :
      gn21ComponentUpperTiPath fixedTj arrivalJ lower density u =
        gn21ScaledStateTime muJ arrivalJ sigmaJ)
    (hWj :
      gn21ComponentUpperWiPath fixedWj arrivalJ lower density wJ u =
        gn21ScaledStateEarning muJ arrivalJ wJ sigmaJ)
    (hendpointScale_pos : 0 < arrivalJ * density u)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ +
          gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI) :
    sameStrictSign
      (gn21ComponentUpperAggregateDerivativeValue
        fixedQj fixedTj fixedWj arrivalJ lower u
        (gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI)
        (gn21ScaledStateTime muI arrivalI sigmaI)
        (gn21ScaledStateEarning muI arrivalI wI sigmaI)
        density (gn21SwitchProb switchJI switchIJ) wJ)
      (gn21MeasuredRightMarginalResponseAtCurrent
        muI muJ arrivalI arrivalJ switchIJ switchJI wI wJ sigmaI sigmaJ u) := by
  have hden_pos_swapped :
      0 <
        gn21ExitWeightIntegral muJ arrivalJ switchJI switchIJ sigmaJ *
            gn21ScaledStateTime muI arrivalI sigmaI +
          gn21ExitWeightIntegral muI arrivalI switchIJ switchJI sigmaI *
            gn21ScaledStateTime muJ arrivalJ sigmaJ := by
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hden_pos
  simpa [gn21MeasuredLeftMarginalResponseAtCurrent,
    gn21MeasuredRightMarginalResponseAtCurrent,
    gn21AggregateDynamicReward_swap] using
    (gn21ComponentUpperDerivativeValue_sameStrictSign_measuredLeftResponse
      muJ muI arrivalJ arrivalI switchJI switchIJ wJ wI sigmaJ sigmaI
      fixedQj fixedTj fixedWj lower u density hQj hTj hWj
      hendpointScale_pos hden_pos_swapped)

/--
A finite upper endpoint in the source sense: it is the upper endpoint of a
bounded *connected component of the actual open policy*, rather than of an
arbitrary caller-supplied union with an interval.
-/
structure GN21SourceFiniteUpperEndpoint
    (sigma : TripPolicy) (upper : TripLength) where
  point : TripLength
  point_mem : point ∈ sigma
  lower : TripLength
  component : connectedComponentIn sigma point = Set.Ioo lower upper

namespace GN21SourceFiniteUpperEndpoint

/-- The represented bounded component is contained in its actual policy. -/
theorem interval_subset
    {sigma : TripPolicy} {upper : TripLength}
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper) :
    Set.Ioo endpoint.lower upper ⊆ sigma := by
  rw [← endpoint.component]
  exact connectedComponentIn_subset sigma endpoint.point

/-- The selected point witnesses that the displayed interval is nonempty. -/
theorem lower_lt_upper
    {sigma : TripPolicy} {upper : TripLength}
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper) :
    endpoint.lower < upper := by
  have hpoint_component : endpoint.point ∈
      connectedComponentIn sigma endpoint.point :=
    mem_connectedComponentIn endpoint.point_mem
  rw [endpoint.component] at hpoint_component
  exact hpoint_component.1.trans hpoint_component.2

/-- Feasibility of the actual policy forces a nonnegative lower endpoint. -/
theorem lower_nonneg
    {sigma : TripPolicy} {upper : TripLength}
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper) :
    0 ≤ endpoint.lower := by
  by_contra hnot
  have hlower_neg : endpoint.lower < 0 := lt_of_not_ge hnot
  let x : TripLength := (endpoint.lower + min upper 0) / 2
  have hlower_x : endpoint.lower < x := by
    dsimp [x]
    have hmin : endpoint.lower < min upper 0 := by
      refine lt_min ?_ ?_
      · exact endpoint.lower_lt_upper
      · exact hlower_neg
    linarith
  have x_upper : x < upper := by
    dsimp [x]
    have hmin : endpoint.lower < min upper 0 := by
      refine lt_min ?_ ?_
      · exact endpoint.lower_lt_upper
      · exact hlower_neg
    have hmin_le : min upper 0 ≤ upper := min_le_left _ _
    linarith
  have x_nonpos : x ≤ 0 := by
    dsimp [x]
    have hmin_nonpos : min upper 0 ≤ 0 := min_le_right _ _
    linarith
  have hx_sigma : x ∈ sigma :=
    endpoint.interval_subset ⟨hlower_x, x_upper⟩
  have hx_pos : 0 < x := hsigma_subset hx_sigma
  exact (not_lt_of_ge x_nonpos) hx_pos

/-- A genuine component path is open for every endpoint value. -/
theorem path_open
    {sigma : TripPolicy} {upper : TripLength}
    (hsigma_open : IsOpen sigma)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper)
    (x : TripLength) :
    IsOpen (gn21ComponentUpperPath sigma endpoint.lower upper x) :=
  isOpen_gn21ComponentUpperPath_of_connectedComponent hsigma_open
    endpoint.component x

/-- The component path stays feasible when the original policy is feasible. -/
theorem path_subset_acceptAll
    {sigma : TripPolicy} {upper : TripLength}
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper)
    (x : TripLength) :
    gn21ComponentUpperPath sigma endpoint.lower upper x ⊆ acceptAllPolicy := by
  have hlower_nonneg := endpoint.lower_nonneg hsigma_subset
  intro tau htau
  rcases htau with htau | htau
  · exact hsigma_subset htau.1
  · exact lt_of_le_of_lt hlower_nonneg htau.1

/-- At the displayed upper endpoint, the path restores the original policy. -/
theorem path_at_upper
    {sigma : TripPolicy} {upper : TripLength}
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper) :
    gn21ComponentUpperPath sigma endpoint.lower upper upper = sigma :=
  gn21ComponentUpperPath_at_upper sigma endpoint.lower upper endpoint.interval_subset

/-- The local quotient `Q` primitive agrees with the current policy at a genuine endpoint. -/
theorem componentUpperQiPath_eq_current_withDensity
    (mu : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (sigma : TripPolicy) (upper radius : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper)
    (density : TripLength → NNReal)
    (hmu : mu = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated :
      gn21ComponentUpperLocallySeparated sigma endpoint.lower upper radius)
    (hradius_nonneg : 0 ≤ radius)
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (sigma \ Set.Ioo endpoint.lower upper) mu)
    (hq_integrable_interval :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switchIJ switchJI tau)
        (Set.Ioo endpoint.lower upper) mu) :
    gn21ComponentUpperQiPath
        (gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI
          (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ))
        (gn21SwitchProb switchIJ switchJI) upper =
      gn21ExitWeightIntegral mu arrivalRate switchIJ switchJI sigma := by
  rw [hmu]
  calc
    gn21ComponentUpperQiPath
        (gn21ExitWeightIntegral
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate switchIJ switchJI
          (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ))
        (gn21SwitchProb switchIJ switchJI) upper =
      gn21ExitWeightIntegral
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate switchIJ switchJI
        (gn21ComponentUpperPath sigma endpoint.lower upper upper) := by
      symm
      apply gn21ExitWeightIntegral_componentUpperPath_withDensity_eq_componentUpperQiPath
      · exact hdensity_meas
      · exact hseparated
      · linarith
      · exact le_of_lt endpoint.lower_lt_upper
      · simpa [hmu] using hq_integrable_background
      · simpa [hmu] using hq_integrable_interval
    _ = gn21ExitWeightIntegral
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate switchIJ switchJI sigma := by
      rw [endpoint.path_at_upper]

/-- The local quotient `T` primitive agrees with the current policy at a genuine endpoint. -/
theorem componentUpperTiPath_eq_current_withDensity
    (mu : Measure TripLength) (arrivalRate : ℝ)
    (sigma : TripPolicy) (upper radius : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper)
    (density : TripLength → NNReal)
    (hmu : mu = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated :
      gn21ComponentUpperLocallySeparated sigma endpoint.lower upper radius)
    (hradius_nonneg : 0 ≤ radius)
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (sigma \ Set.Ioo endpoint.lower upper) mu)
    (htime_integrable_interval :
      IntegrableOn (fun tau : TripLength => tau)
        (Set.Ioo endpoint.lower upper) mu) :
    gn21ComponentUpperTiPath
        (gn21ScaledStateTime mu arrivalRate
          (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ)) upper =
      gn21ScaledStateTime mu arrivalRate sigma := by
  rw [hmu]
  calc
    gn21ComponentUpperTiPath
        (gn21ScaledStateTime
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ)) upper =
      gn21ScaledStateTime
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate
        (gn21ComponentUpperPath sigma endpoint.lower upper upper) := by
      symm
      apply gn21ScaledStateTime_componentUpperPath_withDensity_eq_componentUpperTiPath
      · exact hdensity_meas
      · exact hseparated
      · linarith
      · exact le_of_lt endpoint.lower_lt_upper
      · simpa [hmu] using htime_integrable_background
      · simpa [hmu] using htime_integrable_interval
    _ = gn21ScaledStateTime
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate sigma := by
      rw [endpoint.path_at_upper]

/-- The local quotient `W` primitive agrees with the current policy at a genuine endpoint. -/
theorem componentUpperWiPath_eq_current_withDensity
    (mu : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (sigma : TripPolicy) (upper radius : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint sigma upper)
    (density : TripLength → NNReal)
    (hmu : mu = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hseparated :
      gn21ComponentUpperLocallySeparated sigma endpoint.lower upper radius)
    (hradius_nonneg : 0 ≤ radius)
    (hw_integrable_background :
      IntegrableOn w (sigma \ Set.Ioo endpoint.lower upper) mu)
    (hw_integrable_interval :
      IntegrableOn w (Set.Ioo endpoint.lower upper) mu) :
    gn21ComponentUpperWiPath
        (gn21ScaledStateEarning mu arrivalRate w
          (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ)) w upper =
      gn21ScaledStateEarning mu arrivalRate w sigma := by
  rw [hmu]
  calc
    gn21ComponentUpperWiPath
        (gn21ScaledStateEarning
          (volume.withDensity fun tau => (density tau : ℝ≥0∞))
          arrivalRate w (sigma \ Set.Ioo endpoint.lower upper))
        arrivalRate endpoint.lower (fun tau => (density tau : ℝ)) w upper =
      gn21ScaledStateEarning
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate w
        (gn21ComponentUpperPath sigma endpoint.lower upper upper) := by
      symm
      apply gn21ScaledStateEarning_componentUpperPath_withDensity_eq_componentUpperWiPath
      · exact hdensity_meas
      · exact hseparated
      · linarith
      · exact le_of_lt endpoint.lower_lt_upper
      · simpa [hmu] using hw_integrable_background
      · simpa [hmu] using hw_integrable_interval
    _ = gn21ScaledStateEarning
        (volume.withDensity fun tau => (density tau : ℝ≥0∞))
        arrivalRate w sigma := by
      rw [endpoint.path_at_upper]

end GN21SourceFiniteUpperEndpoint

namespace GN21SourceFiniteUpperEndpoint

/-- A displayed interval is an actual connected component when its open
background has no point in the closed interval.  This is the finite-component
geometry needed when applying the source endpoint premise to a Step-1
interval approximation. -/
noncomputable def separatedInterval
    (context : TripPolicy) {lower upper : Real}
    (hlower_upper : lower < upper)
    (hcontext : ∀ y : Real, y ∈ context → y < lower ∨ upper < y) :
    GN21SourceFiniteUpperEndpoint (context ∪ Set.Ioo lower upper) upper := by
  let point : Real := (lower + upper) / 2
  have hpoint_lower : lower < point := by
    dsimp [point]
    linarith
  have hpoint_upper : point < upper := by
    dsimp [point]
    linarith
  have hpoint_mem : point ∈ context ∪ Set.Ioo lower upper :=
    Or.inr ⟨hpoint_lower, hpoint_upper⟩
  refine ⟨point, hpoint_mem, lower, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hy_source := connectedComponentIn_subset
      (context ∪ Set.Ioo lower upper) point hy
    have hpoint_component : point ∈
        connectedComponentIn (context ∪ Set.Ioo lower upper) point :=
      mem_connectedComponentIn hpoint_mem
    have hconnected :
        (connectedComponentIn (context ∪ Set.Ioo lower upper) point).OrdConnected :=
      IsPreconnected.ordConnected isPreconnected_connectedComponentIn
    have hy_lower : lower < y := by
      by_contra hnot
      have hy_le : y ≤ lower := le_of_not_gt hnot
      have hlower_component : lower ∈
          connectedComponentIn (context ∪ Set.Ioo lower upper) point :=
        hconnected.out hy hpoint_component ⟨hy_le, le_of_lt hpoint_lower⟩
      have hlower_source := connectedComponentIn_subset
        (context ∪ Set.Ioo lower upper) point hlower_component
      rcases hlower_source with hlower_context | hlower_interval
      · rcases hcontext lower hlower_context with hleft | hright
        · exact (lt_irrefl lower) hleft
        · exact (not_lt_of_ge (le_of_lt hlower_upper)) hright
      · exact (lt_irrefl lower) hlower_interval.1
    have hy_upper : y < upper := by
      by_contra hnot
      have hupper_le : upper ≤ y := le_of_not_gt hnot
      have hupper_component : upper ∈
          connectedComponentIn (context ∪ Set.Ioo lower upper) point :=
        hconnected.out hpoint_component hy ⟨le_of_lt hpoint_upper, hupper_le⟩
      have hupper_source := connectedComponentIn_subset
        (context ∪ Set.Ioo lower upper) point hupper_component
      rcases hupper_source with hupper_context | hupper_interval
      · rcases hcontext upper hupper_context with hleft | hright
        · exact (not_lt_of_ge (le_of_lt hlower_upper)) hleft
        · exact (lt_irrefl upper) hright
      · exact (lt_irrefl upper) hupper_interval.2
    exact ⟨hy_lower, hy_upper⟩
  · apply IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo
      ⟨hpoint_lower, hpoint_upper⟩
    intro y hy
    exact Or.inr hy

/-- Opening a separated component has the expected fixed-background path. -/
theorem componentUpperPath_separatedInterval_eq
    (context : TripPolicy) {lower upper x : Real}
    (hcontext : ∀ y : Real, y ∈ context → y < lower ∨ upper < y) :
    gn21ComponentUpperPath (context ∪ Set.Ioo lower upper) lower upper x =
      context ∪ Set.Ioo lower x := by
  ext y
  simp only [gn21ComponentUpperPath, Set.mem_union, Set.mem_diff, Set.mem_Ioo]
  constructor
  · rintro (hy | hy)
    · rcases hy with ⟨hy, hnot⟩
      rcases hy with hy | hy
      · exact Or.inl hy
      · exact False.elim (hnot hy)
    · exact Or.inr hy
  · rintro (hy | hy)
    · exact Or.inl ⟨Or.inl hy, fun hinterval => by
        rcases hcontext y hy with hleft | hright
        · exact (not_lt_of_ge (le_of_lt hinterval.1)) hleft
        · exact (not_lt_of_ge (le_of_lt hinterval.2)) hright⟩
    · exact Or.inr hy

/-- A short initial interval remains an actual bounded component when it is
separated from a right tail. -/
noncomputable def prefixWithTail
    {lower upper : Real} (hupper_pos : 0 < upper) (hupper_lower : upper < lower) :
    GN21SourceFiniteUpperEndpoint
      (Set.Ioo 0 upper ∪ Set.Ioi lower) upper := by
  let point : Real := upper / 2
  have hpoint_mem : point ∈ Set.Ioo 0 upper ∪ Set.Ioi lower := by
    left
    dsimp [point]
    constructor <;> linarith
  refine ⟨point, hpoint_mem, 0, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hy_source := connectedComponentIn_subset
      (Set.Ioo 0 upper ∪ Set.Ioi lower) point hy
    have hpoint_component : point ∈
        connectedComponentIn (Set.Ioo 0 upper ∪ Set.Ioi lower) point :=
      mem_connectedComponentIn hpoint_mem
    have hconnected :
        (connectedComponentIn (Set.Ioo 0 upper ∪ Set.Ioi lower) point).OrdConnected :=
      IsPreconnected.ordConnected isPreconnected_connectedComponentIn
    constructor
    · rcases hy_source with hy_source | hy_source
      · exact hy_source.1
      · exact lt_trans (lt_trans hupper_pos hupper_lower) hy_source
    · by_contra hnot
      have hupper_le_y : upper ≤ y := le_of_not_gt hnot
      have hpoint_le_upper : point ≤ upper := by
        dsimp [point]
        linarith
      have hupper_component : upper ∈
          connectedComponentIn (Set.Ioo 0 upper ∪ Set.Ioi lower) point :=
        hconnected.out hpoint_component hy ⟨hpoint_le_upper, hupper_le_y⟩
      have hupper_source := connectedComponentIn_subset
        (Set.Ioo 0 upper ∪ Set.Ioi lower) point hupper_component
      rcases hupper_source with hupper_source | hupper_source
      · exact (lt_irrefl upper hupper_source.2)
      · exact (not_lt_of_ge (le_of_lt hupper_lower)) hupper_source
  · apply IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo
      (by
        dsimp [point]
        constructor <;> linarith)
    intro y hy
    exact Or.inl hy

/-- A nonempty initial interval is an actual bounded component of itself. -/
noncomputable def initialInterval
    {upper : Real} (hupper_pos : 0 < upper) :
    GN21SourceFiniteUpperEndpoint (Set.Ioo 0 upper) upper := by
  let point : Real := upper / 2
  have hpoint_mem : point ∈ Set.Ioo 0 upper := by
    dsimp [point]
    constructor <;> linarith
  refine ⟨point, hpoint_mem, 0, ?_⟩
  apply Set.Subset.antisymm
  · intro y hy
    have hy_source := connectedComponentIn_subset (Set.Ioo 0 upper) point hy
    have hpoint_component : point ∈ connectedComponentIn (Set.Ioo 0 upper) point :=
      mem_connectedComponentIn hpoint_mem
    have hconnected : (connectedComponentIn (Set.Ioo 0 upper) point).OrdConnected :=
      IsPreconnected.ordConnected isPreconnected_connectedComponentIn
    constructor
    · exact hy_source.1
    · by_contra hnot
      have hupper_le_y : upper ≤ y := le_of_not_gt hnot
      have hpoint_le_upper : point ≤ upper := by
        dsimp [point]
        linarith
      have hupper_component : upper ∈ connectedComponentIn (Set.Ioo 0 upper) point :=
        hconnected.out hpoint_component hy ⟨hpoint_le_upper, hupper_le_y⟩
      have hupper_source := connectedComponentIn_subset
        (Set.Ioo 0 upper) point hupper_component
      exact (lt_irrefl upper hupper_source.2)
  · apply IsPreconnected.subset_connectedComponentIn isPreconnected_Ioo
      (by
        dsimp [point]
        constructor <;> linarith)
    intro y hy
    exact hy

/-- Opening the upper endpoint of the initial component preserves the
prefix-and-tail policy representation. -/
theorem componentUpperPath_prefixWithTail_eq
    (lower upper x : Real) (hupper_lower : upper < lower) :
    gn21ComponentUpperPath (Set.Ioo 0 upper ∪ Set.Ioi lower) 0 upper x =
      Set.Ioo 0 x ∪ Set.Ioi lower := by
  ext y
  simp only [gn21ComponentUpperPath, Set.mem_union, Set.mem_diff,
    Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro (hy | hy)
    · rcases hy with ⟨hy, hnot⟩
      rcases hy with hy | hy
      · exact False.elim (hnot hy)
      · exact Or.inr hy
    · exact Or.inl hy
  · intro hy
    rcases hy with hy | hy
    · exact Or.inr hy
    · exact Or.inl ⟨Or.inr hy, fun h => by
        linarith [hupper_lower, hy, h.2]⟩

/-- Opening the upper endpoint of an initial interval has the expected prefix
representation. -/
theorem componentUpperPath_initialInterval_eq (upper x : Real) :
    gn21ComponentUpperPath (Set.Ioo 0 upper) 0 upper x = Set.Ioo 0 x := by
  ext y
  simp only [gn21ComponentUpperPath, Set.mem_union, Set.mem_diff, Set.mem_Ioo]
  constructor
  · rintro (hy | hy)
    · exact False.elim (hy.2 hy.1)
    · exact hy
  · intro hy
    exact Or.inr hy

end GN21SourceFiniteUpperEndpoint

/--
The literal positive-derivative premise in the third branches of source
Theorem 4.  The derivative is taken along the actual policy's connected
component path.  No response, arbitrary interval context, or prepackaged
sign certificate occurs in this definition.
-/
def gn21SourceUpperEndpointDerivativePositive
    (R : DynamicReward) : Prop :=
  ∀ (rho : Fin 2 → TripPolicy),
    dynamicFeasibleOpenPolicy rho →
      ∀ (i : Fin 2) (upper : TripLength),
        ∀ endpoint : GN21SourceFiniteUpperEndpoint (rho i) upper,
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                R (Function.update rho i
                  (gn21ComponentUpperPath (rho i)
                    endpoint.lower upper x)))
              derivativeValue upper ∧
            0 < derivativeValue

/-- The state-local reading of the third price branch of source Theorem 4.
The printed condition for a non-surge (respectively surge) policy concerns
only upper endpoints in that state. Keeping the state index outside the
predicate is important when one positive branch is combined with a different
affine branch in the other state. -/
def gn21SourceUpperEndpointDerivativePositiveAt
    (R : DynamicReward) (state : Fin 2) : Prop :=
  ∀ (rho : Fin 2 → TripPolicy),
    dynamicFeasibleOpenPolicy rho →
      ∀ (upper : TripLength),
        ∀ endpoint : GN21SourceFiniteUpperEndpoint (rho state) upper,
          ∃ derivativeValue : ℝ,
            HasDerivAt
              (fun x =>
                R (Function.update rho state
                  (gn21ComponentUpperPath (rho state)
                    endpoint.lower upper x)))
              derivativeValue upper ∧
            0 < derivativeValue

/-- A two-state positive-endpoint premise specializes to either literal
state-local source premise. -/
theorem gn21SourceUpperEndpointDerivativePositive.at
    (R : DynamicReward) (hsource : gn21SourceUpperEndpointDerivativePositive R)
    (state : Fin 2) : gn21SourceUpperEndpointDerivativePositiveAt R state := by
  intro rho hrho upper endpoint
  exact hsource rho hrho state upper endpoint

/-- Changing the upper endpoint of one interval can only change the policy
inside a short interval around the two endpoint values. -/
theorem gn21SymmDiff_union_Ioo_subset_Icc
    (context : TripPolicy) {lower x y radius : Real}
    (hradius : 0 < radius) (hxy : |x - y| < radius) :
    ((context ∪ Set.Ioo lower x) ∆ (context ∪ Set.Ioo lower y)) ⊆
      Set.Icc (y - radius) (y + radius) := by
  intro z hz
  have hz' : z ∈ Set.Ioo lower x ∆ Set.Ioo lower y :=
    AppliedModelingLib.symmDiff_union_left_subset hz
  simp only [Set.mem_symmDiff, Set.mem_Ioo, not_and_or] at hz'
  rcases hz' with hz' | hz'
  · rcases hz' with ⟨⟨hzlower, hz_x⟩, hznot⟩
    rcases hznot with hznot_lower | hznot_y
    · exact False.elim (hznot_lower hzlower)
    · constructor <;> linarith [abs_lt.mp hxy]
  · rcases hz' with ⟨⟨hzlower, hz_y⟩, hznot⟩
    rcases hznot with hznot_lower | hznot_x
    · exact False.elim (hznot_lower hzlower)
    · constructor <;> linarith [abs_lt.mp hxy]

/-- The source's symmetric-difference continuity premise gives ordinary
continuity along every one-interval endpoint path. -/
theorem continuous_union_Ioo_of_GN21SymmDiffContinuousAt
    (mu : Measure TripLength) [IsFiniteMeasure mu] [NoAtoms mu]
    (Rhat : SingleStateReward) (context : TripPolicy) (lower : Real)
    (hcontinuous : ∀ sigma : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat sigma) :
    Continuous (fun x : Real => Rhat (context ∪ Set.Ioo lower x)) := by
  rw [continuous_iff_continuousAt]
  intro b
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  let sigma : TripPolicy := context ∪ Set.Ioo lower b
  rcases hcontinuous sigma epsilon hepsilon with ⟨delta, hdelta_ne, hdelta⟩
  have hdelta_pos : 0 < delta := bot_lt_iff_ne_bot.mpr hdelta_ne
  have hmeasure_eventually :
      ∀ᶠ radius : Real in 𝓝 0,
        mu (Set.Icc (b - radius) (b + radius)) < delta := by
    exact (tendsto_measure_Icc mu b).eventually (Iio_mem_nhds hdelta_pos)
  rcases Metric.mem_nhds_iff.mp hmeasure_eventually with
    ⟨radius0, hradius0, hball⟩
  let radius : Real := radius0 / 2
  have hradius : 0 < radius := by
    dsimp [radius]
    linarith
  have hradius_ball : radius ∈ Metric.ball (0 : Real) radius0 := by
    simp only [Metric.mem_ball, dist_zero_right]
    dsimp [radius]
    rw [abs_of_pos]
    · linarith
    · linarith
  have hmeasure := hball hradius_ball
  refine ⟨radius, hradius, ?_⟩
  intro x hdist
  have hxy : |x - b| < radius := by
    simpa [Real.dist_eq] using hdist
  have hsubset := gn21SymmDiff_union_Ioo_subset_Icc
    context (lower := lower) hradius hxy
  have hmeasure_lt :
      mu ((context ∪ Set.Ioo lower x) ∆ (context ∪ Set.Ioo lower b)) < delta :=
    (measure_mono hsubset).trans_lt hmeasure
  have hmeasure_lt' :
      mu ((context ∪ Set.Ioo lower b) ∆ (context ∪ Set.Ioo lower x)) < delta := by
    simpa only [symmDiff_comm] using hmeasure_lt
  have hreward := hdelta (context ∪ Set.Ioo lower x) hmeasure_lt'
  simpa only [sigma, Real.dist_eq] using hreward

/--
The real non-surge endpoint bridge.  Under the source's density model and a
genuine locally separated component, the printed positive-derivative premise
implies positivity of the actual fixed-current marginal response *at that
endpoint*.  It deliberately does not claim positivity at arbitrary trip
lengths or arbitrary policies.
-/
theorem gn21SourceUpperEndpointDerivativePositive_measuredLeftResponse_pos_at_endpoint
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (upper radius : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint (rho 0) upper)
    (density : TripLength → NNReal)
    (hmu0 : mu 0 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hsource : gn21SourceUpperEndpointDerivativePositive
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w))
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hseparated :
      gn21ComponentUpperLocallySeparated (rho 0) endpoint.lower upper radius)
    (hradius_pos : 0 < radius)
    (hendpoint_scale_pos : 0 < (arrival 0) * (density upper : ℝ))
    (hq_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn
          (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
          (Set.Ioo endpoint.lower x) (mu 0))
    (htime_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn (fun tau : TripLength => tau)
          (Set.Ioo endpoint.lower x) (mu 0))
    (hw_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn (w 0) (Set.Ioo endpoint.lower x) (mu 0))
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch12 switch21 tau)
        (rho 0 \ Set.Ioo endpoint.lower upper) (mu 0))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 0 \ Set.Ioo endpoint.lower upper) (mu 0))
    (hw_integrable_background :
      IntegrableOn (w 0) (rho 0 \ Set.Ioo endpoint.lower upper) (mu 0))
    (hq_int :
      IntervalIntegrable
        (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
        (𝓝 upper))
    (hq_cont : ContinuousAt
      (fun tau => gn21SwitchProb switch12 switch21 tau * (density tau : ℝ))
      upper)
    (hw_int :
      IntervalIntegrable (fun tau => (w 0) tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun tau => (w 0) tau * (density tau : ℝ)) (𝓝 upper))
    (hw_cont : ContinuousAt
      (fun tau => (w 0) tau * (density tau : ℝ)) upper)
    (ht_int :
      IntervalIntegrable (fun tau => tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (ht_meas :
      StronglyMeasurableAtFilter
        (fun tau => tau * (density tau : ℝ)) (𝓝 upper))
    (ht_cont : ContinuousAt
      (fun tau => tau * (density tau : ℝ)) upper)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0)) :
    0 <
      gn21MeasuredLeftMarginalResponseAtCurrent
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rho 0) (rho 1) upper := by
  have hupper_le : upper ≤ upper + radius := by linarith
  have hQi := GN21SourceFiniteUpperEndpoint.componentUpperQiPath_eq_current_withDensity
    (mu 0) (arrival 0) switch12 switch21 (rho 0) upper radius endpoint density
    hmu0 hdensity_meas hseparated (le_of_lt hradius_pos)
    hq_integrable_background
    (hq_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hTi := GN21SourceFiniteUpperEndpoint.componentUpperTiPath_eq_current_withDensity
    (mu 0) (arrival 0) (rho 0) upper radius endpoint density
    hmu0 hdensity_meas hseparated (le_of_lt hradius_pos)
    htime_integrable_background
    (htime_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hWi := GN21SourceFiniteUpperEndpoint.componentUpperWiPath_eq_current_withDensity
    (mu 0) (arrival 0) (w 0) (rho 0) upper radius endpoint density
    hmu0 hdensity_meas hseparated (le_of_lt hradius_pos)
    hw_integrable_background
    (hw_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hden :
      gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (rho 0 \ Set.Ioo endpoint.lower upper))
          (arrival 0) endpoint.lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch12 switch21) upper *
          gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
        gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
          gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 0) (arrival 0)
              (rho 0 \ Set.Ioo endpoint.lower upper))
            (arrival 0) endpoint.lower (fun tau => (density tau : ℝ)) upper ≠ 0 := by
    rw [hQi, hTi]
    exact ne_of_gt hden_pos
  have hcalculus :=
    gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_hasDerivAt_of_locallySeparated
      mu arrival switch12 switch21 w rho endpoint.lower upper radius density
      hmu0 hdensity_meas hseparated endpoint.lower_lt_upper hradius_pos
      hq_integrable_local htime_integrable_local hw_integrable_local
      hq_integrable_background htime_integrable_background hw_integrable_background
      hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont hden
  have hsign :=
    gn21ComponentUpperDerivativeValue_sameStrictSign_measuredLeftResponse
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1)
      (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
        (rho 0 \ Set.Ioo endpoint.lower upper))
      (gn21ScaledStateTime (mu 0) (arrival 0)
        (rho 0 \ Set.Ioo endpoint.lower upper))
      (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
        (rho 0 \ Set.Ioo endpoint.lower upper))
      endpoint.lower upper (fun tau => (density tau : ℝ))
      hQi hTi hWi hendpoint_scale_pos hden_pos
  apply response_pos_of_positive_endpoint_derivative_of_same_path_calculus
  · exact hsource rho hrho 0 upper endpoint
  · exact hcalculus
  · exact hsign

/--
The symmetric surge endpoint bridge.  It proves the same genuinely local
fact for the source's surge-state third branch, again without strengthening
the source condition into a global response hypothesis.
-/
theorem gn21SourceUpperEndpointDerivativePositive_measuredRightResponse_pos_at_endpoint
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (upper radius : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint (rho 1) upper)
    (density : TripLength → NNReal)
    (hmu1 : mu 1 = volume.withDensity fun tau => (density tau : ℝ≥0∞))
    (hdensity_meas : Measurable density)
    (hsource : gn21SourceUpperEndpointDerivativePositive
      (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w))
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hseparated :
      gn21ComponentUpperLocallySeparated (rho 1) endpoint.lower upper radius)
    (hradius_pos : 0 < radius)
    (hendpoint_scale_pos : 0 < (arrival 1) * (density upper : ℝ))
    (hq_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn
          (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
          (Set.Ioo endpoint.lower x) (mu 1))
    (htime_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn (fun tau : TripLength => tau)
          (Set.Ioo endpoint.lower x) (mu 1))
    (hw_integrable_local : ∀ x : TripLength,
      endpoint.lower ≤ x → x ≤ upper + radius →
        IntegrableOn (w 1) (Set.Ioo endpoint.lower x) (mu 1))
    (hq_integrable_background :
      IntegrableOn
        (fun tau : TripLength => gn21SwitchProb switch21 switch12 tau)
        (rho 1 \ Set.Ioo endpoint.lower upper) (mu 1))
    (htime_integrable_background :
      IntegrableOn (fun tau : TripLength => tau)
        (rho 1 \ Set.Ioo endpoint.lower upper) (mu 1))
    (hw_integrable_background :
      IntegrableOn (w 1) (rho 1 \ Set.Ioo endpoint.lower upper) (mu 1))
    (hq_int :
      IntervalIntegrable
        (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (hq_meas :
      StronglyMeasurableAtFilter
        (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
        (𝓝 upper))
    (hq_cont : ContinuousAt
      (fun tau => gn21SwitchProb switch21 switch12 tau * (density tau : ℝ))
      upper)
    (hw_int :
      IntervalIntegrable (fun tau => (w 1) tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (hw_meas :
      StronglyMeasurableAtFilter
        (fun tau => (w 1) tau * (density tau : ℝ)) (𝓝 upper))
    (hw_cont : ContinuousAt
      (fun tau => (w 1) tau * (density tau : ℝ)) upper)
    (ht_int :
      IntervalIntegrable (fun tau => tau * (density tau : ℝ))
        volume endpoint.lower upper)
    (ht_meas :
      StronglyMeasurableAtFilter
        (fun tau => tau * (density tau : ℝ)) (𝓝 upper))
    (ht_cont : ContinuousAt
      (fun tau => tau * (density tau : ℝ)) upper)
    (hden_pos :
      0 <
        gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
            gn21ScaledStateTime (mu 1) (arrival 1) (rho 1) +
          gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1) *
            gn21ScaledStateTime (mu 0) (arrival 0) (rho 0)) :
    0 <
      gn21MeasuredRightMarginalResponseAtCurrent
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1) (rho 0) (rho 1) upper := by
  have hupper_le : upper ≤ upper + radius := by linarith
  have hQj := GN21SourceFiniteUpperEndpoint.componentUpperQiPath_eq_current_withDensity
    (mu 1) (arrival 1) switch21 switch12 (rho 1) upper radius endpoint density
    hmu1 hdensity_meas hseparated (le_of_lt hradius_pos)
    hq_integrable_background
    (hq_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hTj := GN21SourceFiniteUpperEndpoint.componentUpperTiPath_eq_current_withDensity
    (mu 1) (arrival 1) (rho 1) upper radius endpoint density
    hmu1 hdensity_meas hseparated (le_of_lt hradius_pos)
    htime_integrable_background
    (htime_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hWj := GN21SourceFiniteUpperEndpoint.componentUpperWiPath_eq_current_withDensity
    (mu 1) (arrival 1) (w 1) (rho 1) upper radius endpoint density
    hmu1 hdensity_meas hseparated (le_of_lt hradius_pos)
    hw_integrable_background
    (hw_integrable_local upper (le_of_lt endpoint.lower_lt_upper) hupper_le)
  have hden :
      gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0) *
          gn21ComponentUpperTiPath
            (gn21ScaledStateTime (mu 1) (arrival 1)
              (rho 1 \ Set.Ioo endpoint.lower upper))
            (arrival 1) endpoint.lower (fun tau => (density tau : ℝ)) upper +
        gn21ComponentUpperQiPath
          (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (rho 1 \ Set.Ioo endpoint.lower upper))
          (arrival 1) endpoint.lower (fun tau => (density tau : ℝ))
          (gn21SwitchProb switch21 switch12) upper *
          gn21ScaledStateTime (mu 0) (arrival 0) (rho 0) ≠ 0 := by
    rw [hQj, hTj]
    exact ne_of_gt hden_pos
  have hcalculus :=
    gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_hasDerivAt_of_locallySeparated
      mu arrival switch12 switch21 w rho endpoint.lower upper radius density
      hmu1 hdensity_meas hseparated endpoint.lower_lt_upper hradius_pos
      hq_integrable_local htime_integrable_local hw_integrable_local
      hq_integrable_background htime_integrable_background hw_integrable_background
      hq_int hq_meas hq_cont hw_int hw_meas hw_cont ht_int ht_meas ht_cont hden
  have hsign :=
    gn21ComponentUpperDerivativeValue_sameStrictSign_measuredRightResponse
      (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
      (w 0) (w 1) (rho 0) (rho 1)
      (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
        (rho 1 \ Set.Ioo endpoint.lower upper))
      (gn21ScaledStateTime (mu 1) (arrival 1)
        (rho 1 \ Set.Ioo endpoint.lower upper))
      (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
        (rho 1 \ Set.Ioo endpoint.lower upper))
      endpoint.lower upper (fun tau => (density tau : ℝ))
      hQj hTj hWj hendpoint_scale_pos hden_pos
  apply response_pos_of_positive_endpoint_derivative_of_same_path_calculus
  · exact hsource rho hrho 1 upper endpoint
  · exact hcalculus
  · exact hsign

/--
The literal source condition already has a nontrivial, fully semantic
consequence: an open maximizer cannot contain a bounded connected component.
This conclusion uses the actual aggregate policy path and does not pass
through a response function.
-/
theorem not_dynamicOpenOptimal_of_gn21SourceUpperEndpointDerivativePositive
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hoptimal : dynamicOpenOptimal R rho)
    (upper : TripLength)
    (endpoint : GN21SourceFiniteUpperEndpoint (rho i) upper) :
    False := by
  rcases hsource rho hoptimal.1 upper endpoint with
    ⟨derivativeValue, hderivative, hderivative_pos⟩
  rcases exists_pos_right_improvement_of_hasDerivAt_pos
      hderivative hderivative_pos with
    ⟨epsilon, hepsilon_pos, himprovement⟩
  have himproved_feasible :
      dynamicFeasibleOpenPolicy
        (Function.update rho i
          (gn21ComponentUpperPath (rho i) endpoint.lower upper
            (upper + epsilon))) := by
    intro j
    by_cases hji : j = i
    · subst j
      exact
        ⟨by
            simpa using
              endpoint.path_subset_acceptAll (hoptimal.1 i).1
                (upper + epsilon),
          by
            simpa using endpoint.path_open (hoptimal.1 i).2
              (upper + epsilon)⟩
    · simpa [Function.update, hji] using hoptimal.1 j
  have hnot_improve := hoptimal.2 _ himproved_feasible
  have hstart :
      R (Function.update rho i
        (gn21ComponentUpperPath (rho i) endpoint.lower upper upper)) =
        R rho := by
    rw [endpoint.path_at_upper]
    simp
  have hstrict : R rho <
      R (Function.update rho i
        (gn21ComponentUpperPath (rho i) endpoint.lower upper
          (upper + epsilon))) := by
    simpa [hstart] using himprovement
  exact (not_lt_of_ge hnot_improve) hstrict

/-- Every open optimum satisfying the literal source condition has no genuine
bounded connected component in either state. -/
theorem gn21SourceUpperEndpointDerivativePositive_optimal_no_finite_endpoint
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositive R)
    {rho : Fin 2 → TripPolicy}
    (hoptimal : dynamicOpenOptimal R rho) :
    ∀ (i : Fin 2) (upper : TripLength)
      (endpoint : GN21SourceFiniteUpperEndpoint (rho i) upper), False := by
  intro i upper endpoint
  exact
    not_dynamicOpenOptimal_of_gn21SourceUpperEndpointDerivativePositive
      R i (gn21SourceUpperEndpointDerivativePositive.at R hsource i)
        hoptimal upper endpoint

private theorem gn21SourceUpperEndpointDerivativePositive_prefixWithTail_derivative_zero
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R 0)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {lower t : Real}
    (ht_pos : 0 < t) (ht_lower : t < lower) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho 0 (Set.Ioo 0 x ∪ Set.Ioi lower)))
        derivativeValue t ∧
      0 < derivativeValue := by
  let rhoAt : Fin 2 → TripPolicy :=
    ![Set.Ioo 0 t ∪ Set.Ioi lower, rho 1]
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    intro j
    fin_cases j
    · simp only [rhoAt, Matrix.vecCons]
      refine ⟨?_, isOpen_Ioo.union isOpen_Ioi⟩
      intro x hx
      rcases hx with hx | hx
      · simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1
      · exact lt_trans (lt_trans ht_pos ht_lower) hx
    · simpa [rhoAt] using hrho 1
  have hsourceAt := hsource rhoAt hrhoAt t
    (GN21SourceFiniteUpperEndpoint.prefixWithTail ht_pos ht_lower)
  rcases hsourceAt with ⟨d, hd, hd_pos⟩
  refine ⟨d, ?_, hd_pos⟩
  have hupdate_eq (policy : TripPolicy) :
      Function.update rhoAt 0 policy = Function.update rho 0 policy := by
    funext j
    fin_cases j <;> simp [rhoAt]
  simp_rw [hupdate_eq] at hd
  simpa [rhoAt, GN21SourceFiniteUpperEndpoint.prefixWithTail,
    GN21SourceFiniteUpperEndpoint.componentUpperPath_prefixWithTail_eq lower t _ ht_lower]
    using hd

private theorem gn21SourceUpperEndpointDerivativePositive_prefixWithTail_derivative_one
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R 1)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {lower t : Real}
    (ht_pos : 0 < t) (ht_lower : t < lower) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho 1 (Set.Ioo 0 x ∪ Set.Ioi lower)))
        derivativeValue t ∧
      0 < derivativeValue := by
  let rhoAt : Fin 2 → TripPolicy :=
    ![rho 0, Set.Ioo 0 t ∪ Set.Ioi lower]
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    intro j
    fin_cases j
    · simpa [rhoAt] using hrho 0
    · simp only [rhoAt, Matrix.vecCons]
      refine ⟨?_, isOpen_Ioo.union isOpen_Ioi⟩
      intro x hx
      rcases hx with hx | hx
      · simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1
      · exact lt_trans (lt_trans ht_pos ht_lower) hx
  have hsourceAt := hsource rhoAt hrhoAt t
    (GN21SourceFiniteUpperEndpoint.prefixWithTail ht_pos ht_lower)
  rcases hsourceAt with ⟨d, hd, hd_pos⟩
  refine ⟨d, ?_, hd_pos⟩
  have hupdate_eq (policy : TripPolicy) :
      Function.update rhoAt 1 policy = Function.update rho 1 policy := by
    funext j
    fin_cases j <;> simp [rhoAt]
  simp_rw [hupdate_eq] at hd
  simpa [rhoAt, GN21SourceFiniteUpperEndpoint.prefixWithTail,
    GN21SourceFiniteUpperEndpoint.componentUpperPath_prefixWithTail_eq lower t _ ht_lower]
    using hd

private theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_derivative_zero
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R 0)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real}
    (ht_pos : 0 < t) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho 0 (Set.Ioo 0 x))) derivativeValue t ∧
      0 < derivativeValue := by
  let rhoAt : Fin 2 → TripPolicy := ![Set.Ioo 0 t, rho 1]
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    intro j
    fin_cases j
    · simp only [rhoAt, Matrix.vecCons]
      exact ⟨fun x hx => by
        simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1,
        isOpen_Ioo⟩
    · simpa [rhoAt] using hrho 1
  have hsourceAt := hsource rhoAt hrhoAt t
    (GN21SourceFiniteUpperEndpoint.initialInterval ht_pos)
  rcases hsourceAt with ⟨d, hd, hd_pos⟩
  refine ⟨d, ?_, hd_pos⟩
  have hupdate_eq (policy : TripPolicy) :
      Function.update rhoAt 0 policy = Function.update rho 0 policy := by
    funext j
    fin_cases j <;> simp [rhoAt]
  simp_rw [hupdate_eq] at hd
  simpa [rhoAt, GN21SourceFiniteUpperEndpoint.initialInterval,
    GN21SourceFiniteUpperEndpoint.componentUpperPath_initialInterval_eq t _] using hd

private theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_derivative_one
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R 1)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real}
    (ht_pos : 0 < t) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho 1 (Set.Ioo 0 x))) derivativeValue t ∧
      0 < derivativeValue := by
  let rhoAt : Fin 2 → TripPolicy := ![rho 0, Set.Ioo 0 t]
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    intro j
    fin_cases j
    · simpa [rhoAt] using hrho 0
    · simp only [rhoAt, Matrix.vecCons]
      exact ⟨fun x hx => by
        simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1,
        isOpen_Ioo⟩
  have hsourceAt := hsource rhoAt hrhoAt t
    (GN21SourceFiniteUpperEndpoint.initialInterval ht_pos)
  rcases hsourceAt with ⟨d, hd, hd_pos⟩
  refine ⟨d, ?_, hd_pos⟩
  have hupdate_eq (policy : TripPolicy) :
      Function.update rhoAt 1 policy = Function.update rho 1 policy := by
    funext j
    fin_cases j <;> simp [rhoAt]
  simp_rw [hupdate_eq] at hd
  simpa [rhoAt, GN21SourceFiniteUpperEndpoint.initialInterval,
    GN21SourceFiniteUpperEndpoint.componentUpperPath_initialInterval_eq t _] using hd

/-- The literal endpoint premise supplies a positive derivative while a short
initial component is expanded in front of any disjoint right tail. -/
theorem gn21SourceUpperEndpointDerivativePositive_prefixWithTail_path_derivative
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {lower t : Real}
    (ht_pos : 0 < t) (ht_lower : t < lower) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho i (Set.Ioo 0 x ∪ Set.Ioi lower)))
        derivativeValue t ∧
      0 < derivativeValue := by
  fin_cases i
  · exact gn21SourceUpperEndpointDerivativePositive_prefixWithTail_derivative_zero
      R hsource hrho ht_pos ht_lower
  · exact gn21SourceUpperEndpointDerivativePositive_prefixWithTail_derivative_one
      R hsource hrho ht_pos ht_lower

/-- The literal endpoint premise supplies a positive derivative while an
initial interval is expanded from the empty state component. -/
theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_path_derivative
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real}
    (ht_pos : 0 < t) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho i (Set.Ioo 0 x))) derivativeValue t ∧
      0 < derivativeValue := by
  fin_cases i
  · exact gn21SourceUpperEndpointDerivativePositive_initialInterval_derivative_zero
      R hsource hrho ht_pos
  · exact gn21SourceUpperEndpointDerivativePositive_initialInterval_derivative_one
      R hsource hrho ht_pos

/-- The source's path-continuity condition turns the preceding pointwise
positive derivatives into a strict improvement of a nonempty right-tail
policy. -/
theorem gn21SourceUpperEndpointDerivativePositive_prefixWithTail_strict_improvement
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {lower t : Real}
    (ht_pos : 0 < t) (ht_lower : t < lower)
    (hcontinuous :
      ContinuousOn
        (fun x => R (Function.update rho i (Set.Ioo 0 x ∪ Set.Ioi lower)))
        (Set.Icc 0 t)) :
    R (Function.update rho i (Set.Ioi lower)) <
      R (Function.update rho i (Set.Ioo 0 t ∪ Set.Ioi lower)) := by
  have hstrict := endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc ht_pos hcontinuous
    (fun x hx =>
      gn21SourceUpperEndpointDerivativePositive_prefixWithTail_path_derivative
        R i hsource hrho hx.1 (lt_trans hx.2 ht_lower))
  simpa using hstrict

/-- The source's path-continuity condition turns the initial-component
derivatives into a strict improvement over the empty state component. -/
theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_strict_improvement
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real}
    (ht_pos : 0 < t)
    (hcontinuous :
      ContinuousOn (fun x => R (Function.update rho i (Set.Ioo 0 x)))
        (Set.Icc 0 t)) :
    R (Function.update rho i ∅) < R (Function.update rho i (Set.Ioo 0 t)) := by
  have hstrict := endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc ht_pos hcontinuous
    (fun x hx =>
      gn21SourceUpperEndpointDerivativePositive_initialInterval_path_derivative
        R i hsource hrho hx.1)
  simpa using hstrict

/-- The state-local source premise supplies the derivative while an initial
interval is expanded.  This is the local form needed by a mixed Theorem 4
price case, where the other state may be affine rather than positive. -/
theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_path_derivative_at
    (R : DynamicReward) (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real} (ht_pos : 0 < t) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho state (Set.Ioo 0 x)))
        derivativeValue t ∧
      0 < derivativeValue := by
  let rhoAt : Fin 2 → TripPolicy := Function.update rho state (Set.Ioo 0 t)
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    exact dynamicFeasibleOpenPolicy_update hrho state (Set.Ioo 0 t)
      (fun x hx => by
        simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1)
      isOpen_Ioo
  let endpointAt : GN21SourceFiniteUpperEndpoint (rhoAt state) t :=
    { point := t / 2
      point_mem := by
        change t / 2 ∈ rhoAt state
        simp only [rhoAt, Function.update_self]
        constructor <;> linarith
      lower := 0
      component := by
        simpa [rhoAt] using
          (GN21SourceFiniteUpperEndpoint.initialInterval ht_pos).component }
  rcases hsource rhoAt hrhoAt t endpointAt with
    ⟨derivativeValue, hderivative, hderivative_pos⟩
  refine ⟨derivativeValue, ?_, hderivative_pos⟩
  have hupdate_eq (policy : TripPolicy) :
      Function.update rhoAt state policy = Function.update rho state policy := by
    funext j
    by_cases hjs : j = state
    · subst j
      simp [rhoAt]
    · simp [rhoAt, hjs]
  simp_rw [hupdate_eq] at hderivative
  simpa [rhoAt, endpointAt, GN21SourceFiniteUpperEndpoint.initialInterval,
    GN21SourceFiniteUpperEndpoint.componentUpperPath_initialInterval_eq t _]
    using hderivative

/-- Source-continuity turns the state-local literal endpoint premise into a
strict improvement from the empty state component. -/
theorem gn21SourceUpperEndpointDerivativePositive_initialInterval_strict_improvement_at
    (R : DynamicReward) (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    {t : Real} (ht_pos : 0 < t)
    (hcontinuous :
      ContinuousOn (fun x => R (Function.update rho state (Set.Ioo 0 x)))
        (Set.Icc 0 t)) :
    R (Function.update rho state ∅) < R (Function.update rho state (Set.Ioo 0 t)) := by
  have hstrict := endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc ht_pos hcontinuous
    (fun x hx =>
      gn21SourceUpperEndpointDerivativePositive_initialInterval_path_derivative_at
        R state hsource hrho hx.1)
  simpa using hstrict

/-- In the positive branch, actual finite-component derivatives together with
the source continuity requirement rule out every open optimal policy except
accept-all.  The theorem is an optimizer-classification result; it does not
assert existence of an optimizer. -/
theorem gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hoptimal : dynamicOpenOptimal R rho)
    (htail_continuous :
      ∀ (lower t : Real), 0 < t → t < lower →
        ContinuousOn
          (fun x => R (Function.update rho i (Set.Ioo 0 x ∪ Set.Ioi lower)))
          (Set.Icc 0 t))
    (hempty_continuous :
      ∀ t : Real, 0 < t →
        ContinuousOn (fun x => R (Function.update rho i (Set.Ioo 0 x)))
          (Set.Icc 0 t)) :
    rho i = acceptAllPolicy := by
  by_cases hempty : rho i = ∅
  · let t : Real := 1
    have ht_pos : 0 < t := by dsimp [t]; norm_num
    have hstrict :=
      gn21SourceUpperEndpointDerivativePositive_initialInterval_strict_improvement
        R i hsource hoptimal.1 ht_pos (hempty_continuous t ht_pos)
    have hcandidate_subset : Set.Ioo 0 t ⊆ acceptAllPolicy := by
      intro x hx
      simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1
    have hcandidate_feasible :
        dynamicFeasibleOpenPolicy (Function.update rho i (Set.Ioo 0 t)) :=
      dynamicFeasibleOpenPolicy_update hoptimal.1 i (Set.Ioo 0 t)
        hcandidate_subset isOpen_Ioo
    have hstart : Function.update rho i ∅ = rho := by
      rw [← hempty]
      exact Function.update_eq_self i rho
    have hnot_improve :
        R (Function.update rho i (Set.Ioo 0 t)) ≤ R (Function.update rho i ∅) := by
      rw [hstart]
      exact hoptimal.2 _ hcandidate_feasible
    exact False.elim ((not_lt_of_ge hnot_improve) hstrict)
  have hnonempty : (rho i).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
  have hform : lemma5SourcePolicyForm .strictlyIncreasing (rho i) := by
    by_contra hnot_form
    rcases exists_bounded_connectedComponent_of_not_strictlyIncreasing_form
        (hoptimal.1 i).2 (hoptimal.1 i).1 hnonempty hnot_form with
      ⟨point, lower, upper, hpoint, _hlower_nonneg, hlower_upper, hcomponent⟩
    let endpoint : GN21SourceFiniteUpperEndpoint (rho i) upper :=
      ⟨point, hpoint, lower, hcomponent⟩
    exact not_dynamicOpenOptimal_of_gn21SourceUpperEndpointDerivativePositive
      R i hsource hoptimal upper endpoint
  rcases hform with ⟨cutoff, hcutoff⟩
  by_cases hcutoff_zero : cutoff = 0
  · calc
      rho i = gn21RightExtendedCutoffPolicy (cutoff : ℝ≥0∞) := hcutoff
      _ = acceptAllPolicy := by simp [hcutoff_zero]
  · have hcutoff_ne : (cutoff : Real) ≠ 0 := by
      exact_mod_cast hcutoff_zero
    have hcutoff_pos : 0 < (cutoff : Real) :=
      lt_of_le_of_ne cutoff.property (Ne.symm hcutoff_ne)
    have hpolicy : rho i = Set.Ioi (cutoff : Real) := by
      calc
        rho i = gn21RightExtendedCutoffPolicy (cutoff : ℝ≥0∞) := hcutoff
        _ = rejectShortTripsPolicy (cutoff : Real) :=
          gn21RightExtendedCutoffPolicy_coe cutoff
        _ = Set.Ioi (cutoff : Real) := by
          ext x
          constructor
          · intro hx
            exact hx.2
          · intro hx
            exact ⟨lt_of_le_of_lt cutoff.property hx, hx⟩
    let t : Real := (cutoff : Real) / 2
    have ht_pos : 0 < t := by
      dsimp [t]
      linarith
    have ht_lower : t < (cutoff : Real) := by
      dsimp [t]
      linarith
    have hstrict :=
      gn21SourceUpperEndpointDerivativePositive_prefixWithTail_strict_improvement
        R i hsource hoptimal.1 ht_pos ht_lower
          (htail_continuous (cutoff : Real) t ht_pos ht_lower)
    have hcandidate_subset :
        Set.Ioo 0 t ∪ Set.Ioi (cutoff : Real) ⊆ acceptAllPolicy := by
      intro x hx
      rcases hx with hx | hx
      · simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1
      · exact lt_trans hcutoff_pos hx
    have hcandidate_feasible : dynamicFeasibleOpenPolicy
        (Function.update rho i (Set.Ioo 0 t ∪ Set.Ioi (cutoff : Real))) :=
      dynamicFeasibleOpenPolicy_update hoptimal.1 i _ hcandidate_subset
        (isOpen_Ioo.union isOpen_Ioi)
    have hstart : Function.update rho i (Set.Ioi (cutoff : Real)) = rho := by
      rw [← hpolicy]
      exact Function.update_eq_self i rho
    have hnot_improve :
        R (Function.update rho i (Set.Ioo 0 t ∪ Set.Ioi (cutoff : Real))) ≤
          R (Function.update rho i (Set.Ioi (cutoff : Real))) := by
      rw [hstart]
      exact hoptimal.2 _ hcandidate_feasible
    exact False.elim ((not_lt_of_ge hnot_improve) hstrict)

/-- Source-continuity specialization of the positive-branch optimizer
classification.  Atomlessness lets the paper's symmetric-difference
continuity premise control the moving interval endpoints used in the
component argument.  This classifies an optimizer if one exists; it does not
prove the separate finite-approximation/attainment part of Lemma 5. -/
theorem gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll_of_symmDiffContinuousAt
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (i : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R i)
    {rho : Fin 2 → TripPolicy}
    (hoptimal : dynamicOpenOptimal R rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau) :
    rho i = acceptAllPolicy := by
  letI : IsFiniteMeasure (mu i) := hfinite i
  letI : NoAtoms (mu i) := hatomless i
  apply gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll
    R i hsource hoptimal
  · intro lower t ht_pos ht_lower
    simpa only [Set.union_comm] using
      (continuous_union_Ioo_of_GN21SymmDiffContinuousAt
        (mu i) (fun policy => R (Function.update rho i policy))
        (Set.Ioi lower) 0 (hcontinuous rho hoptimal.1 i)).continuousOn
  · intro t ht_pos
    simpa only [Set.empty_union] using
      (continuous_union_Ioo_of_GN21SymmDiffContinuousAt
        (mu i) (fun policy => R (Function.update rho i policy))
        ∅ 0 (hcontinuous rho hoptimal.1 i)).continuousOn

/-! ## Finite approximation for the literal positive branch -/

/-- Updating the first finite gap leaves the remaining endpoint tail unchanged. -/
theorem gn21EndpointVectorTail_update_firstGapUpper
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1)) (x : Real) :
    gn21EndpointVectorTail
      (gn21UpdateEndpoint endpoints
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x) =
      gn21EndpointVectorTail endpoints := by
  funext j
  simp [gn21EndpointVectorTail, gn21UpdateEndpoint,
    gn21Lemma5GapUpperIndex]

/-- A second update of the first gap replaces the first update. -/
theorem gn21UpdateEndpoint_firstGapUpper_idempotent
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (x y : Real) :
    gn21UpdateEndpoint
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) y =
      gn21UpdateEndpoint endpoints
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) y := by
  funext j
  simp [gn21UpdateEndpoint]

/-- If the first upper endpoint is zero, replacing it by zero changes nothing. -/
theorem gn21UpdateEndpoint_firstGapUpper_zero_eq
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hzero : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = 0) :
    gn21UpdateEndpoint endpoints
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) 0 = endpoints := by
  funext j
  by_cases hj : j = gn21Lemma5GapUpperIndex (0 : Fin (n + 1))
  · subst j
    simp [gn21UpdateEndpoint, hzero]
  · simp [gn21UpdateEndpoint, hj]

/-- The first-gap update is an initial interval together with the fixed tail. -/
theorem gn21EndpointVectorPolicy_update_firstGapUpper
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1)) (x : Real) :
    gn21EndpointVectorPolicy
      (gn21UpdateEndpoint endpoints
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x) =
      gn21ExtendedMiddlePolicy (endpoints 0) (ENNReal.ofReal x) ∪
        gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) := by
  rw [gn21EndpointVectorPolicy_succ]
  rw [gn21EndpointVectorTail_update_firstGapUpper]
  simp [gn21UpdateEndpoint, gn21Lemma5GapUpperIndex]

/-- The first finite interval with lower endpoint zero is the ordinary real interval. -/
theorem gn21ExtendedMiddlePolicy_zero_ofReal_eq_Ioo
    (u : Real) :
    gn21ExtendedMiddlePolicy 0 (ENNReal.ofReal u) = Set.Ioo 0 u := by
  by_cases hu : 0 ≤ u
  · rw [ENNReal.ofReal_eq_coe_nnreal hu]
    change gn21ExtendedMiddlePolicy ((0 : NNReal) : ENNReal)
        ((NNReal.mk u hu : NNReal) : ENNReal) = Set.Ioo 0 u
    rw [gn21ExtendedMiddlePolicy_coe_coe_eq_Ioo]
    simp
  · have hu_nonpos : u ≤ 0 := le_of_not_ge hu
    rw [ENNReal.ofReal_eq_zero.mpr hu_nonpos,
      gn21ExtendedMiddlePolicy_zero, gn21LeftExtendedCutoffPolicy_zero,
      Set.Ioo_eq_empty_of_le hu_nonpos]

/-- Every point in the tail lies strictly after a genuine first gap. -/
theorem gn21EndpointVectorTail_strictly_above_firstGapUpper
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    {u : Real}
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u)
    (hu_pos : 0 < u)
    (hgap : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1)))) :
    ∀ y : Real, y ∈ gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) →
      u < y := by
  intro y hy
  rcases Set.mem_iUnion.1 hy with ⟨slot, hslot⟩
  have hsecond_lower_le :
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) ≤
        endpoints (gn21LowerEndpointIndex slot.succ) := by
    apply hordered
    apply Fin.mk_le_mk.2
    simp
  have hgap_lower :
      endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
        endpoints (gn21LowerEndpointIndex slot.succ) :=
    hgap.trans_le hsecond_lower_le
  change y ∈ gn21ExtendedMiddlePolicy
    (endpoints (gn21LowerEndpointIndex slot.succ))
    (endpoints (gn21UpperEndpointIndex slot.succ)) at hslot
  cases hlower : endpoints (gn21LowerEndpointIndex slot.succ)
      using ENNReal.recTopCoe with
  | top =>
      rw [hlower, gn21ExtendedMiddlePolicy_top] at hslot
      exact False.elim (by simp at hslot)
  | coe lower =>
      have hupper_lower : ENNReal.ofReal u < (lower : ENNReal) := by
        rw [← hupper, ← hlower]
        exact hgap_lower
      have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
      have hu_lower : u < (lower : Real) :=
        (ENNReal.ofReal_lt_coe_iff hu_nonneg).mp hupper_lower
      rw [gn21ExtendedMiddlePolicy, hlower,
        gn21RightExtendedCutoffPolicy_coe] at hslot
      exact hu_lower.trans hslot.1.2

/-- The first interval of a positive endpoint vector is a tail plus `(0,u)`. -/
theorem gn21EndpointVectorPolicy_firstGap_eq_tail_union_Ioo
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    {u : Real}
    (hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0)
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u) :
    gn21EndpointVectorPolicy endpoints =
      gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) ∪ Set.Ioo 0 u := by
  rw [gn21EndpointVectorPolicy_succ]
  change endpoints 0 = 0 at hfirst
  change endpoints 1 = ENNReal.ofReal u at hupper
  rw [hfirst, hupper, gn21ExtendedMiddlePolicy_zero_ofReal_eq_Ioo]
  ac_rfl

/-- Updating the first gap changes only the end of the initial interval. -/
theorem gn21EndpointVectorPolicy_update_firstGap_eq_tail_union_Ioo
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    {x : Real}
    (hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0) :
    gn21EndpointVectorPolicy
      (gn21UpdateEndpoint endpoints
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x) =
      gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) ∪ Set.Ioo 0 x := by
  rw [gn21EndpointVectorPolicy_update_firstGapUpper]
  change endpoints 0 = 0 at hfirst
  rw [hfirst, gn21ExtendedMiddlePolicy_zero_ofReal_eq_Ioo]
  ac_rfl

/-- A separated first finite interval is an actual component of the represented policy. -/
noncomputable def gn21FirstGap_actualFiniteUpperEndpoint
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0)
    {u : Real}
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u)
    (hu_pos : 0 < u)
    (hgap : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1)))) :
    GN21SourceFiniteUpperEndpoint (gn21EndpointVectorPolicy endpoints) u := by
  have htail : ∀ y : Real,
      y ∈ gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) →
        u < y :=
    gn21EndpointVectorTail_strictly_above_firstGapUpper n endpoints hordered
      hupper hu_pos hgap
  have hpolicy :=
    gn21EndpointVectorPolicy_firstGap_eq_tail_union_Ioo n endpoints hfirst hupper
  refine ⟨u / 2, ?_, 0, ?_⟩
  · rw [hpolicy]
    exact Or.inr ⟨by linarith, by linarith⟩
  · rw [hpolicy]
    simpa [GN21SourceFiniteUpperEndpoint.separatedInterval] using
      (GN21SourceFiniteUpperEndpoint.separatedInterval
        (gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints)) hu_pos
        (fun y hy => Or.inr (htail y hy))).component

/-- The constructed first component has lower endpoint zero by construction. -/
theorem gn21FirstGap_actualFiniteUpperEndpoint_lower
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0)
    {u : Real}
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u)
    (hu_pos : 0 < u)
    (hgap : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1)))) :
    (gn21FirstGap_actualFiniteUpperEndpoint n endpoints hordered hfirst
      hupper hu_pos hgap).lower = 0 := by
  rfl

/-- The literal component path agrees with updating the first finite upper endpoint. -/
theorem gn21FirstGap_componentUpperPath_eq_update
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hordered : endpoints ∈ gn21OrderedEndpointVectors (n + 2))
    (hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0)
    {u : Real}
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u)
    (hu_pos : 0 < u)
    (hgap : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))))
    (x : Real) :
    gn21ComponentUpperPath (gn21EndpointVectorPolicy endpoints) 0 u x =
      gn21EndpointVectorPolicy
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x) := by
  have htail : ∀ y : Real,
      y ∈ gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) →
        u < y :=
    gn21EndpointVectorTail_strictly_above_firstGapUpper n endpoints hordered
      hupper hu_pos hgap
  have hpolicy :=
    gn21EndpointVectorPolicy_firstGap_eq_tail_union_Ioo n endpoints hfirst hupper
  calc
    gn21ComponentUpperPath (gn21EndpointVectorPolicy endpoints) 0 u x =
        gn21ComponentUpperPath
          (gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) ∪ Set.Ioo 0 u)
          0 u x := by rw [hpolicy]
    _ = gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) ∪ Set.Ioo 0 x := by
      exact GN21SourceFiniteUpperEndpoint.componentUpperPath_separatedInterval_eq
        (gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints))
        (fun y hy => Or.inr (htail y hy))
    _ = gn21EndpointVectorPolicy
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x) := by
      symm
      exact gn21EndpointVectorPolicy_update_firstGap_eq_tail_union_Ioo
        n endpoints hfirst

/-- Moving a zero first upper endpoint within the next gap stays in the positive domain. -/
theorem gn21UpdateEndpoint_firstGapUpper_mem_positive_domain
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive (n + 1))
    {x : Real}
    (hzero : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = 0)
    (hx_next : ENNReal.ofReal x ≤
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1)))) :
    gn21UpdateEndpoint endpoints
      (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x ∈
        gn21Lemma5EndpointDomain .positive (n + 1) := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  apply gn21UpdateEndpoint_mem_lemma5EndpointDomain
    .positive (n + 1) hdomain
    (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x
  · intro j hj
    calc
      endpoints j ≤ endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) :=
        hordered (le_of_lt hj)
      _ = 0 := hzero
      _ ≤ ENNReal.ofReal x := bot_le
  · intro j hj
    exact hx_next.trans
      (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt
        (0 : Fin (n + 1)) hj))
  · intro _
    exact gn21Lemma5GapUpperIndex_ne_first (0 : Fin (n + 1))
  · intro _
    exact gn21Lemma5GapUpperIndex_ne_last (0 : Fin (n + 1))

/-- The literal source premise gives the derivative of the first finite-gap update. -/
theorem gn21SourceUpperEndpointDerivativePositive_firstGap_derivative
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (n : Nat) (endpoints : GN21Lemma5EndpointVector (n + 1))
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive (n + 1))
    {u : Real}
    (hupper : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      ENNReal.ofReal u)
    (hu_pos : 0 < u)
    (hgap : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1)))) :
    ∃ derivativeValue : Real,
      HasDerivAt
        (fun x => R (Function.update rho state
          (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint endpoints
              (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x))))
        derivativeValue u ∧
      0 < derivativeValue := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0 :=
    hdomain.1.2
  let rhoAt : Fin 2 → TripPolicy := Function.update rho state
    (gn21EndpointVectorPolicy endpoints)
  have hrhoAt : dynamicFeasibleOpenPolicy rhoAt := by
    exact dynamicFeasibleOpenPolicy_update hrho state
      (gn21EndpointVectorPolicy endpoints)
      (gn21EndpointVectorPolicy_subset_acceptAll endpoints)
      (gn21EndpointVectorPolicy_open endpoints)
  let endpoint : GN21SourceFiniteUpperEndpoint
      (gn21EndpointVectorPolicy endpoints) u :=
    gn21FirstGap_actualFiniteUpperEndpoint n endpoints hordered hfirst hupper hu_pos hgap
  let endpointAt : GN21SourceFiniteUpperEndpoint (rhoAt state) u :=
    { point := endpoint.point
      point_mem := by simpa [rhoAt] using endpoint.point_mem
      lower := 0
      component := by
        simpa [rhoAt,
          gn21FirstGap_actualFiniteUpperEndpoint_lower n endpoints hordered hfirst
            hupper hu_pos hgap] using endpoint.component }
  rcases hsource rhoAt hrhoAt u endpointAt with
    ⟨derivativeValue, hderivative, hderivative_pos⟩
  refine ⟨derivativeValue, ?_, hderivative_pos⟩
  have hpath :
    (fun x => R (Function.update rhoAt state
        (gn21ComponentUpperPath (rhoAt state) 0 u x))) =
      (fun x => R (Function.update rho state
        (gn21EndpointVectorPolicy
          (gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)))) := by
    funext x
    dsimp [rhoAt]
    have hupdate :
        Function.update
            (Function.update rho state (gn21EndpointVectorPolicy endpoints)) state
            (gn21ComponentUpperPath (gn21EndpointVectorPolicy endpoints) 0 u x) =
          Function.update rho state
            (gn21ComponentUpperPath (gn21EndpointVectorPolicy endpoints) 0 u x) := by
      funext j
      by_cases hj : j = state
      · subst j
        simp
      · simp [hj]
    rw [Function.update_self]
    rw [hupdate]
    rw [gn21FirstGap_componentUpperPath_eq_update n endpoints hordered hfirst
      hupper hu_pos hgap]
  dsimp [endpointAt] at hderivative
  rw [hpath] at hderivative
  exact hderivative

/-- At a finite positive-branch maximizer, a positive first upper endpoint cannot leave a gap. -/
theorem gn21SourceUpperEndpointDerivativePositive_firstGap_eq_of_upper_pos_maximum
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (n : Nat) {endpoints : GN21Lemma5EndpointVector (n + 1)}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive (n + 1))
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive (n + 1),
        R (Function.update rho state (gn21EndpointVectorPolicy candidate)) ≤
          R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
    (hupper_pos : 0 < endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1)))) :
    endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := by
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hle :
      endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) ≤
        endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) :=
    hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex (0 : Fin (n + 1))))
  apply le_antisymm hle
  by_contra hnot
  have hgap :
      endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
        endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) :=
    lt_of_not_ge hnot
  rcases exists_real_right_neighborhood_of_ennreal_lt hgap with
    ⟨value, upper, hvalue, hvalue_upper, hupper_bound⟩
  have hvalue_pos : 0 < value := by
    rw [hvalue, ENNReal.ofReal_pos] at hupper_pos
    exact hupper_pos
  rcases gn21SourceUpperEndpointDerivativePositive_firstGap_derivative
      R state hsource hrho n endpoints hdomain hvalue hvalue_pos hgap with
    ⟨derivativeValue, hderivative, hderivative_pos⟩
  have hderivative_nonpos : derivativeValue ≤ 0 := by
    apply endpoint_derivative_nonpos_of_lemma5EndpointDomain_maximum
        .positive (n + 1)
        (fun sigma => R (Function.update rho state sigma)) hdomain hmax
        (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) hvalue hvalue_upper
    · intro j hj
      exact hupper_bound.trans
        (hordered (gn21Lemma5GapLowerIndex_le_of_upperIndex_lt
          (0 : Fin (n + 1)) hj))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_first (0 : Fin (n + 1))
    · intro _
      exact gn21Lemma5GapUpperIndex_ne_last (0 : Fin (n + 1))
    · exact hderivative
  exact (not_lt_of_ge hderivative_nonpos) hderivative_pos

/-- At a finite positive-branch maximizer, a zero first upper endpoint cannot leave a gap. -/
theorem gn21SourceUpperEndpointDerivativePositive_firstGap_eq_of_upper_zero_maximum
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (n : Nat) {endpoints : GN21Lemma5EndpointVector (n + 1)}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive (n + 1))
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive (n + 1),
        R (Function.update rho state (gn21EndpointVectorPolicy candidate)) ≤
          R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
    (hupper_zero : endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = 0) :
    endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) =
      endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := by
  letI : IsFiniteMeasure (mu state) := hfinite state
  letI : NoAtoms (mu state) := hatomless state
  have hordered := gn21Lemma5EndpointDomain_ordered hdomain
  have hfirst : endpoints (gn21Lemma5FirstEndpointIndex (n + 1)) = 0 :=
    hdomain.1.2
  have hle :
      endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) ≤
        endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) :=
    hordered (le_of_lt (gn21Lemma5GapUpperIndex_lt_lowerIndex (0 : Fin (n + 1))))
  apply le_antisymm hle
  by_contra hnot
  have hnext_pos : 0 < endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := by
    rw [hupper_zero] at hnot
    exact lt_of_not_ge hnot
  rcases exists_pos_real_of_zero_lt_ennreal hnext_pos with
    ⟨upper, hupper_pos, hupper_bound⟩
  let path : Real → Real := fun x =>
    R (Function.update rho state
      (gn21EndpointVectorPolicy
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)))
  have hcandidate_mem :
      ∀ x ∈ Set.Icc (0 : Real) upper,
        gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x ∈
          gn21Lemma5EndpointDomain .positive (n + 1) := by
    intro x hx
    apply gn21UpdateEndpoint_firstGapUpper_mem_positive_domain
      n endpoints hdomain hupper_zero
    exact (ENNReal.ofReal_mono hx.2).trans hupper_bound
  have hpath_continuous : ContinuousOn path (Set.Icc 0 upper) := by
    have hbase :=
      continuous_union_Ioo_of_GN21SymmDiffContinuousAt
        (mu state) (fun policy => R (Function.update rho state policy))
        (gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints)) 0
        (hcontinuous rho hrho state)
    have hpath_eq : path =
        (fun x => R (Function.update rho state
          (gn21EndpointVectorPolicy (gn21EndpointVectorTail endpoints) ∪ Set.Ioo 0 x))) := by
      funext x
      dsimp [path]
      rw [gn21EndpointVectorPolicy_update_firstGap_eq_tail_union_Ioo n endpoints hfirst]
    rw [hpath_eq]
    exact hbase.continuousOn
  have hpath_derivative :
      ∀ x ∈ Set.Ioo (0 : Real) upper,
        ∃ derivativeValue : Real,
          HasDerivAt path derivativeValue x ∧ 0 < derivativeValue := by
    intro x hx
    have hdomain_x := hcandidate_mem x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    have hupper_x :
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = ENNReal.ofReal x := by
      simp [gn21UpdateEndpoint]
    have hx_lt_upper : ENNReal.ofReal x < ENNReal.ofReal upper :=
      (ENNReal.ofReal_lt_ofReal_iff hupper_pos).mpr hx.2
    have hgap_x :
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) <
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
          (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := by
      calc
        (gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
            (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = ENNReal.ofReal x := hupper_x
        _ < ENNReal.ofReal upper := hx_lt_upper
        _ ≤ endpoints (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := hupper_bound
        _ = (gn21UpdateEndpoint endpoints
            (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
            (gn21Lemma5GapLowerIndex (0 : Fin (n + 1))) := by
          symm
          simp [gn21UpdateEndpoint,
            ne_of_gt (gn21Lemma5GapUpperIndex_lt_lowerIndex (0 : Fin (n + 1)))]
    rcases gn21SourceUpperEndpointDerivativePositive_firstGap_derivative
        R state hsource hrho n
        (gn21UpdateEndpoint endpoints
          (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
        hdomain_x hupper_x hx.1 hgap_x with
      ⟨derivativeValue, hderivative, hderivative_pos⟩
    refine ⟨derivativeValue, ?_, hderivative_pos⟩
    have hpath_eq :
        (fun y => R (Function.update rho state
          (gn21EndpointVectorPolicy
            (gn21UpdateEndpoint
              (gn21UpdateEndpoint endpoints
                (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) x)
              (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) y)))) = path := by
      funext y
      dsimp [path]
      rw [gn21UpdateEndpoint_firstGapUpper_idempotent n endpoints x y]
    rw [hpath_eq] at hderivative
    exact hderivative
  have hstrict : path 0 < path upper :=
    endpoint_path_lt_of_exists_hasDerivAt_pos_on_Icc hupper_pos hpath_continuous
      hpath_derivative
  have hpath_zero : path 0 =
      R (Function.update rho state (gn21EndpointVectorPolicy endpoints)) := by
    dsimp [path]
    rw [gn21UpdateEndpoint_firstGapUpper_zero_eq n endpoints hupper_zero]
  have hnot_improve : path upper ≤ path 0 := by
    rw [hpath_zero]
    exact hmax _ (hcandidate_mem upper ⟨le_of_lt hupper_pos, le_rfl⟩)
  exact (not_lt_of_ge hnot_improve) hstrict

/-- The literal endpoint condition rules out every first finite gap at a positive maximizer. -/
theorem gn21SourceUpperEndpointDerivativePositive_firstGap_eq_at_maximum
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (extra : Nat) {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        R (Function.update rho state (gn21EndpointVectorPolicy candidate)) ≤
          R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
    (hextra_pos : 0 < extra) :
    endpoints (gn21Lemma5GapUpperIndex ⟨0, hextra_pos⟩) =
      endpoints (gn21Lemma5GapLowerIndex ⟨0, hextra_pos⟩) := by
  cases extra with
  | zero => exact False.elim (Nat.not_lt_zero _ hextra_pos)
  | succ n =>
      by_cases hupper_pos :
          0 < endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1)))
      · exact gn21SourceUpperEndpointDerivativePositive_firstGap_eq_of_upper_pos_maximum
          R state hsource hrho n hdomain hmax hupper_pos
      · have hupper_zero :
            endpoints (gn21Lemma5GapUpperIndex (0 : Fin (n + 1))) = 0 :=
          le_antisymm (le_of_not_gt hupper_pos) bot_le
        exact gn21SourceUpperEndpointDerivativePositive_firstGap_eq_of_upper_zero_maximum
          mu hfinite hatomless R state hsource hrho hcontinuous n hdomain hmax hupper_zero

/-- A finite positive-branch endpoint maximum has the same reward as accept-all. -/
theorem gn21SourceUpperEndpointDerivativePositive_endpointMaximum_reward_eq_acceptAll
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (extra : Nat) {endpoints : GN21Lemma5EndpointVector extra}
    (hdomain : endpoints ∈ gn21Lemma5EndpointDomain .positive extra)
    (hmax :
      ∀ candidate ∈ gn21Lemma5EndpointDomain .positive extra,
        R (Function.update rho state (gn21EndpointVectorPolicy candidate)) ≤
          R (Function.update rho state (gn21EndpointVectorPolicy endpoints))) :
    R (Function.update rho state (gn21EndpointVectorPolicy endpoints)) =
      R (Function.update rho state acceptAllPolicy) := by
  letI : NoAtoms (mu state) := hatomless state
  have hRhat_ae : ∀ {sigma tau : TripPolicy},
      policyAlmostEverywhereEq (mu state) sigma tau →
        R (Function.update rho state sigma) = R (Function.update rho state tau) := by
    intro sigma tau hae
    exact reward_eq_of_symmDiffContinuousAt_of_policyAlmostEverywhereEq
      (mu state) (fun policy => R (Function.update rho state policy))
      (hcontinuous rho hrho state sigma) hae
  rcases exists_gn21Lemma5CompressionReduced_maximum
      (mu state) .positive (fun policy => R (Function.update rho state policy))
      hRhat_ae extra hdomain hmax with
    ⟨reducedExtra, _, reduced, hreduced_domain, hreduced_max,
      hreduced_reward, hreduced⟩
  have hreduced_zero : reducedExtra = 0 := by
    by_contra hnot
    have hpositive : 0 < reducedExtra := Nat.pos_of_ne_zero hnot
    have hgap_eq := gn21SourceUpperEndpointDerivativePositive_firstGap_eq_at_maximum
      mu hfinite hatomless R state hsource hrho hcontinuous reducedExtra
      hreduced_domain hreduced_max hpositive
    exact (ne_of_lt (hreduced.2 ⟨0, hpositive⟩)) hgap_eq
  subst reducedExtra
  have hform : lemma5SourcePolicyForm .positive
      (gn21EndpointVectorPolicy reduced) := by
    exact lemma5SourcePolicyForm_of_mem_canonicalEndpointDomain .positive reduced
      hreduced_domain (by simp)
  change gn21EndpointVectorPolicy reduced = acceptAllPolicy at hform
  rw [hform] at hreduced_reward
  exact hreduced_reward.symm

/-- The literal positive endpoint premise yields weak dominance of accept-all
over an open state-policy that is better than its empty benchmark.  The two
continuity arguments are exactly the source Lemma 5 continuity-in-policy
condition, expressed respectively for arbitrary policies and finite endpoint
approximants. -/
theorem gn21SourceUpperEndpointDerivativePositive_open_reward_le_acceptAll
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop)
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
          (gn21Lemma5EndpointDomain .positive extra))
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma :
      R (Function.update rho state ∅) < R (Function.update rho state sigma)) :
    R (Function.update rho state sigma) ≤
      R (Function.update rho state acceptAllPolicy) := by
  letI : IsFiniteMeasure (mu state) := hfinite state
  letI : (mu state).InnerRegularCompactLTTop := hinner state
  letI : NoAtoms (mu state) := hatomless state
  by_contra hnot
  have haccept_lt_sigma :
      R (Function.update rho state acceptAllPolicy) <
        R (Function.update rho state sigma) := lt_of_not_ge hnot
  let gap_accept : Real :=
    R (Function.update rho state sigma) -
      R (Function.update rho state acceptAllPolicy)
  let gap_empty : Real :=
    R (Function.update rho state sigma) -
      R (Function.update rho state ∅)
  have hgap_accept_pos : 0 < gap_accept := by
    dsimp [gap_accept]
    linarith
  have hgap_empty_pos : 0 < gap_empty := by
    dsimp [gap_empty]
    linarith
  let epsilon : Real := min (gap_accept / 2) (gap_empty / 2)
  have hepsilon_pos : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min (by linarith) (by linarith)
  have hepsilon_lt_empty :
      epsilon < R (Function.update rho state sigma) -
        R (Function.update rho state ∅) := by
    calc
      epsilon ≤ gap_empty / 2 := min_le_right _ _
      _ < gap_empty := by linarith
      _ = R (Function.update rho state sigma) -
          R (Function.update rho state ∅) := rfl
  rcases exists_gn21Lemma5EndpointDomain_maximum_above_source_sub
      (mu state) .positive
      (fun policy => R (Function.update rho state policy))
      hsigma_open hsigma_subset (hcontinuous rho hrho state)
      hendpoint_continuous hepsilon_pos hepsilon_lt_empty with
    ⟨extra, endpoints, hdomain, hmax, hsource_lower⟩
  have hendpoint_reward :=
    gn21SourceUpperEndpointDerivativePositive_endpointMaximum_reward_eq_acceptAll
      mu hfinite hatomless R state hsource hrho hcontinuous extra hdomain hmax
  rw [hendpoint_reward] at hsource_lower
  have hepsilon_le_accept : epsilon ≤ gap_accept / 2 := min_le_left _ _
  have haccept_lt_source :
      R (Function.update rho state acceptAllPolicy) <
        R (Function.update rho state sigma) - epsilon := by
    dsimp [gap_accept] at hepsilon_le_accept
    linarith
  exact (not_lt_of_ge (le_of_lt haccept_lt_source)) hsource_lower

/-- The literal positive endpoint premise yields statewise accept-all
dominance, including policies no better than the empty policy. -/
theorem gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop)
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (state : Fin 2)
    (hsource : gn21SourceUpperEndpointDerivativePositiveAt R state)
    {rho : Fin 2 → TripPolicy}
    (hrho : dynamicFeasibleOpenPolicy rho)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
          (gn21Lemma5EndpointDomain .positive extra))
    (sigma : TripPolicy)
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy) :
    R (Function.update rho state sigma) ≤
      R (Function.update rho state acceptAllPolicy) := by
  letI : IsFiniteMeasure (mu state) := hfinite state
  letI : NoAtoms (mu state) := hatomless state
  let t : Real := 1
  have ht_pos : 0 < t := by
    dsimp [t]
    norm_num
  have hshort_subset : Set.Ioo 0 t ⊆ acceptAllPolicy := by
    intro x hx
    simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll] using hx.1
  have hshort_continuous :
      ContinuousOn (fun x => R (Function.update rho state (Set.Ioo 0 x)))
        (Set.Icc 0 t) := by
    simpa only [Set.empty_union] using
      (continuous_union_Ioo_of_GN21SymmDiffContinuousAt
        (mu state) (fun policy => R (Function.update rho state policy)) ∅ 0
        (hcontinuous rho hrho state)).continuousOn
  have hempty_lt_short :
      R (Function.update rho state ∅) <
        R (Function.update rho state (Set.Ioo 0 t)) :=
    gn21SourceUpperEndpointDerivativePositive_initialInterval_strict_improvement_at
      R state hsource hrho ht_pos hshort_continuous
  have hshort_le_accept :
      R (Function.update rho state (Set.Ioo 0 t)) ≤
        R (Function.update rho state acceptAllPolicy) :=
    gn21SourceUpperEndpointDerivativePositive_open_reward_le_acceptAll
      mu hfinite hinner hatomless R state hsource hrho hcontinuous
      hendpoint_continuous isOpen_Ioo hshort_subset hempty_lt_short
  have hempty_lt_accept :
      R (Function.update rho state ∅) <
        R (Function.update rho state acceptAllPolicy) :=
    hempty_lt_short.trans_le hshort_le_accept
  by_cases hsigma_le_empty :
      R (Function.update rho state sigma) ≤ R (Function.update rho state ∅)
  · exact hsigma_le_empty.trans (le_of_lt hempty_lt_accept)
  · exact gn21SourceUpperEndpointDerivativePositive_open_reward_le_acceptAll
      mu hfinite hinner hatomless R state hsource hrho hcontinuous
      hendpoint_continuous hsigma_open hsigma_subset
        (lt_of_not_ge hsigma_le_empty)

/-- Under the source Lemma 5 continuity condition, the literal positive
endpoint premise makes accept-all dynamically open-optimal. -/
theorem gn21SourceUpperEndpointDerivativePositive_dynamicOpenOptimal_acceptAll
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop)
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositive R)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (state : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain .positive extra)) :
    dynamicOpenOptimal R acceptAllDynamicPolicy := by
  refine ⟨dynamicFeasibleOpenPolicy_acceptAllDynamicPolicy, ?_⟩
  intro sigma hsigma
  have hzero_raw :=
    gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
      mu hfinite hinner hatomless R 0
      (gn21SourceUpperEndpointDerivativePositive.at R hsource 0)
      hsigma hcontinuous
      (hendpoint_continuous sigma hsigma 0) (sigma 0) (hsigma 0).2 (hsigma 0).1
  have hzero : R sigma ≤ R (Function.update sigma 0 acceptAllPolicy) := by
    simpa [Function.update_eq_self] using hzero_raw
  let sigma0 : Fin 2 → TripPolicy := Function.update sigma 0 acceptAllPolicy
  have hsigma0 : dynamicFeasibleOpenPolicy sigma0 := by
    exact dynamicFeasibleOpenPolicy_update hsigma 0 acceptAllPolicy
      (fun _ h => h)
      (by
        simpa [acceptAllPolicy, positiveTripLengths, positiveRealAcceptAll]
          using (isOpen_Ioi : IsOpen (Set.Ioi (0 : Real))))
  have hone_raw :=
    gn21SourceUpperEndpointDerivativePositive_state_reward_le_acceptAll
      mu hfinite hinner hatomless R 1
      (gn21SourceUpperEndpointDerivativePositive.at R hsource 1)
      hsigma0 hcontinuous
      (hendpoint_continuous sigma0 hsigma0 1) (sigma0 1) (hsigma0 1).2
      (hsigma0 1).1
  have hone : R sigma0 ≤ R acceptAllDynamicPolicy := by
    have hcurrent : Function.update sigma0 1 (sigma0 1) = sigma0 :=
      Function.update_eq_self 1 sigma0
    have htarget : Function.update sigma0 1 acceptAllPolicy =
        acceptAllDynamicPolicy := by
      funext i
      fin_cases i <;> simp [sigma0, acceptAllDynamicPolicy]
    simpa [hcurrent, htarget] using hone_raw
  exact hzero.trans (by simpa [sigma0] using hone)

/-- The same literal source assumptions make accept-all the only open
optimizer, by combining the finite-approximation existence proof with the
actual-component optimizer classification. -/
theorem gn21SourceUpperEndpointDerivativePositive_dynamicOpenOptimal_acceptAll_unique
    (mu : Fin 2 → Measure TripLength)
    (hfinite : ∀ i : Fin 2, IsFiniteMeasure (mu i))
    (hinner : ∀ i : Fin 2, (mu i).InnerRegularCompactLTTop)
    (hatomless : ∀ i : Fin 2, NoAtoms (mu i))
    (R : DynamicReward)
    (hsource : gn21SourceUpperEndpointDerivativePositive R)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy => R (Function.update rho i policy)) tau)
    (hendpoint_continuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (state : Fin 2) (extra : Nat),
            ContinuousOn
              (fun endpoints : GN21Lemma5EndpointVector extra =>
                R (Function.update rho state (gn21EndpointVectorPolicy endpoints)))
              (gn21Lemma5EndpointDomain .positive extra)) :
    dynamicOpenOptimal R acceptAllDynamicPolicy ∧
      ∀ rho : Fin 2 → TripPolicy,
        dynamicOpenOptimal R rho → rho = acceptAllDynamicPolicy := by
  constructor
  · exact gn21SourceUpperEndpointDerivativePositive_dynamicOpenOptimal_acceptAll
      mu hfinite hinner hatomless R hsource hcontinuous hendpoint_continuous
  · intro rho hoptimal
    funext state
    exact
      gn21SourceUpperEndpointDerivativePositive_optimal_state_acceptAll_of_symmDiffContinuousAt
        mu hfinite hatomless R state
          (gn21SourceUpperEndpointDerivativePositive.at R hsource state)
          hoptimal hcontinuous

end

end GN21DriverSurgePricing
