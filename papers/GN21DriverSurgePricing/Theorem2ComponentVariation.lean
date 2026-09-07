import GN21DriverSurgePricing.Lemma5Variational

/-!
# Component-local aggregate paths for GN21 Theorem 2

This module isolates the algebraic part of the local variation used by the
source proof of Theorem 2.  In particular, it does not quantify over an
arbitrary background policy.  The background is obtained by removing a
selected bounded connected component of the current open policy, and the
moving endpoint is restricted to the component's inward side.  On that side
the moving interval is disjoint from the background, so the Appendix-D
`Q`, `T`, and `W` primitives have exact union decompositions.

No derivative of the *policy* path is assumed or proved here.  The module does
derive the fixed-background quotient derivative under explicit interval
integrability and local-continuity hypotheses; transporting it back to the
policy path remains a separate obligation.
-/

open AppliedModelingLib
open MeasureTheory
open scoped ENNReal Topology

namespace GN21DriverSurgePricing

noncomputable section

/--
The local upper-endpoint path for a selected bounded component of `sigma`.
The fixed background is the rest of the original policy, not an arbitrary
context supplied by a caller.
-/
def gn21ComponentUpperPath
    (sigma : TripPolicy) (lower upper x : TripLength) : TripPolicy :=
  (sigma \ Set.Ioo lower upper) ∪ Set.Ioo lower x

/-- The inward upper-endpoint path has no overlap between its background and moving interval. -/
theorem disjoint_gn21ComponentUpperPath_background_interval
    (sigma : TripPolicy) (lower upper x : TripLength)
    (hx_upper : x ≤ upper) :
    Disjoint (sigma \ Set.Ioo lower upper) (Set.Ioo lower x) := by
  refine Set.disjoint_left.2 ?_
  intro y hy_background hy_interval
  exact hy_background.2 ⟨hy_interval.1, hy_interval.2.trans_le hx_upper⟩

/--
The geometric condition needed to extend an upper endpoint to the right while
keeping the moving interval disjoint from the remainder of the policy.  It is
not automatic for arbitrary open-set presentations with touching components.
-/
def gn21ComponentUpperLocallySeparated
    (sigma : TripPolicy) (lower upper radius : TripLength) : Prop :=
  Disjoint (sigma \ Set.Ioo lower upper) (Set.Ioo lower (upper + radius))

/--
Under an explicit local separation condition, the component path has the same
disjoint-union geometry on a two-sided endpoint neighborhood.
-/
theorem disjoint_gn21ComponentUpperPath_background_interval_of_locallySeparated
    (sigma : TripPolicy) (lower upper radius x : TripLength)
    (hseparated : gn21ComponentUpperLocallySeparated sigma lower upper radius)
    (hx_upper : x ≤ upper + radius) :
    Disjoint (sigma \ Set.Ioo lower upper) (Set.Ioo lower x) := by
  unfold gn21ComponentUpperLocallySeparated at hseparated
  apply hseparated.mono_right
  intro y hy
  exact ⟨hy.1, hy.2.trans_le hx_upper⟩

/-- A selected component is restored exactly at its original upper endpoint. -/
theorem gn21ComponentUpperPath_at_upper
    (sigma : TripPolicy) (lower upper : TripLength)
    (hcomponent_subset : Set.Ioo lower upper ⊆ sigma) :
    gn21ComponentUpperPath sigma lower upper upper = sigma := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · exact hy.1
    · exact hcomponent_subset hy
  · intro hy
    by_cases hy_component : y ∈ Set.Ioo lower upper
    · exact Or.inr hy_component
    · exact Or.inl ⟨hy, hy_component⟩

/-- An inward component path remains a subset of the original feasible policy. -/
theorem gn21ComponentUpperPath_subset
    (sigma : TripPolicy) (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
    (hcomponent_subset : Set.Ioo lower upper ⊆ sigma) :
    gn21ComponentUpperPath sigma lower upper x ⊆ sigma := by
  intro y hy
  rcases hy with hy | hy
  · exact hy.1
  · exact hcomponent_subset ⟨hy.1, hy.2.trans_le hx_upper⟩

/--
When the interval is an actual connected component of an open policy, its
fixed background is open, so every local path policy is open as well.
-/
theorem isOpen_gn21ComponentUpperPath_of_connectedComponent
    {sigma : TripPolicy} {point lower upper : TripLength}
    (hsigma_open : IsOpen sigma)
    (hcomponent : connectedComponentIn sigma point = Set.Ioo lower upper)
    (x : TripLength) :
    IsOpen (gn21ComponentUpperPath sigma lower upper x) := by
  unfold gn21ComponentUpperPath
  rw [← hcomponent]
  exact (isOpen_diff_connectedComponentIn hsigma_open point).union isOpen_Ioo

/-- The local component path is measurable whenever the original policy is measurable. -/
theorem measurableSet_gn21ComponentUpperPath
    {sigma : TripPolicy} (hsigma_measurable : MeasurableSet sigma)
    (lower upper x : TripLength) :
    MeasurableSet (gn21ComponentUpperPath sigma lower upper x) := by
  exact (hsigma_measurable.diff measurableSet_Ioo).union measurableSet_Ioo

/-- The actual `Q` primitive is a fixed-background plus moving-interval path. -/
theorem gn21ExitWeightIntegral_gn21ComponentUpperPath
    (mu : Measure TripLength) (arrivalRate switchIJ switchJI : ℝ)
    (sigma : TripPolicy) (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
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
    (disjoint_gn21ComponentUpperPath_background_interval sigma lower upper x hx_upper)
    measurableSet_Ioo hq_integrable_background hq_integrable_interval

/-- The actual `T` primitive is a fixed-background plus moving-interval path. -/
theorem gn21ScaledStateTime_gn21ComponentUpperPath
    (mu : Measure TripLength) (arrivalRate : ℝ)
    (sigma : TripPolicy) (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
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
    (disjoint_gn21ComponentUpperPath_background_interval sigma lower upper x hx_upper)
    measurableSet_Ioo htime_integrable_background htime_integrable_interval

/-- The actual `W` primitive is a fixed-background plus moving-interval path. -/
theorem gn21ScaledStateEarning_gn21ComponentUpperPath
    (mu : Measure TripLength) (arrivalRate : ℝ) (w : PricingFunction)
    (sigma : TripPolicy) (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
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
    (disjoint_gn21ComponentUpperPath_background_interval sigma lower upper x hx_upper)
    measurableSet_Ioo hw_integrable_background hw_integrable_interval

/-! ## Fixed-background quotient calculus -/

/-- The `Q` path obtained by holding a component complement fixed. -/
def gn21ComponentUpperQiPath
    (fixedQi arrivalRate lowerEndpoint : ℝ)
    (density switchProb : TripLength → ℝ) (x : TripLength) : ℝ :=
  fixedQi + arrivalRate * ∫ tau in lowerEndpoint..x, switchProb tau * density tau

/-- The `W` path obtained by holding a component complement fixed. -/
def gn21ComponentUpperWiPath
    (fixedWi arrivalRate lowerEndpoint : ℝ)
    (density payment : TripLength → ℝ) (x : TripLength) : ℝ :=
  fixedWi + arrivalRate * ∫ tau in lowerEndpoint..x, payment tau * density tau

/-- The `T` path obtained by holding a component complement fixed. -/
def gn21ComponentUpperTiPath
    (fixedTi arrivalRate lowerEndpoint : ℝ)
    (density : TripLength → ℝ) (x : TripLength) : ℝ :=
  fixedTi + arrivalRate * ∫ tau in lowerEndpoint..x, tau * density tau

/-- Fundamental-theorem calculation for the fixed-background `Q` path. -/
theorem gn21ComponentUpperQiPath_hasDerivAt
    (fixedQi arrivalRate lowerEndpoint u : ℝ)
    (density switchProb : TripLength → ℝ)
    (hint :
      IntervalIntegrable (fun tau => switchProb tau * density tau) volume
        lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun tau => switchProb tau * density tau) (𝓝 u))
    (hcont : ContinuousAt (fun tau => switchProb tau * density tau) u) :
    HasDerivAt
      (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density switchProb)
      (arrivalRate * (switchProb u * density u)) u := by
  unfold gn21ComponentUpperQiPath
  exact
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate).const_add fixedQi

/-- Fundamental-theorem calculation for the fixed-background `W` path. -/
theorem gn21ComponentUpperWiPath_hasDerivAt
    (fixedWi arrivalRate lowerEndpoint u : ℝ)
    (density payment : TripLength → ℝ)
    (hint :
      IntervalIntegrable (fun tau => payment tau * density tau) volume
        lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter
        (fun tau => payment tau * density tau) (𝓝 u))
    (hcont : ContinuousAt (fun tau => payment tau * density tau) u) :
    HasDerivAt
      (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density payment)
      (arrivalRate * (payment u * density u)) u := by
  unfold gn21ComponentUpperWiPath
  exact
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate).const_add fixedWi

/-- Fundamental-theorem calculation for the fixed-background `T` path. -/
theorem gn21ComponentUpperTiPath_hasDerivAt
    (fixedTi arrivalRate lowerEndpoint u : ℝ)
    (density : TripLength → ℝ)
    (hint :
      IntervalIntegrable (fun tau => tau * density tau) volume lowerEndpoint u)
    (hmeas :
      StronglyMeasurableAtFilter (fun tau => tau * density tau) (𝓝 u))
    (hcont : ContinuousAt (fun tau => tau * density tau) u) :
    HasDerivAt
      (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density)
      (arrivalRate * (u * density u)) u := by
  unfold gn21ComponentUpperTiPath
  exact
    ((intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_mul
      arrivalRate).const_add fixedTi

/--
Lemma 6's quotient derivative calculation for a genuine fixed-background
component path.  Unlike the older interval path, the three baseline values
are arbitrary primitive values of the *rest of the current policy*, not a
fresh empty policy.  Every analytic premise is displayed explicitly.
-/
theorem gn21ComponentUpperAggregatePath_hasDerivAt
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
        Qj *
          gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u ≠ 0) :
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
      ((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb u)
          Qj
          (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
          Tj
          (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density
            payment u)
          Wj /
        (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb u * Tj +
          Qj *
            gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u) ^ 2)
      u := by
  apply paper_lemma6_aggregate_reward_hasDerivAt
    (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density switchProb)
    (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density payment)
    (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density)
    (switchProb u) u (payment u)
    (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density switchProb u)
    Qj
    (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
    Tj
    (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density payment u)
    Wj
    (arrivalRate * density u)
  · convert
      gn21ComponentUpperQiPath_hasDerivAt
        fixedQi arrivalRate lowerEndpoint u density switchProb
        hq_int hq_meas hq_cont using 1
    ring
  · convert
      gn21ComponentUpperWiPath_hasDerivAt
        fixedWi arrivalRate lowerEndpoint u density payment
        hw_int hw_meas hw_cont using 1
    ring
  · convert
      gn21ComponentUpperTiPath_hasDerivAt
        fixedTi arrivalRate lowerEndpoint u density ht_int ht_meas ht_cont
        using 1
    ring
  · rfl
  · rfl
  · rfl
  · exact hden

/--
The fixed-background derivative has the Lemma 6 kernel's strict sign whenever
the arrival-density scale and opposite-state exit weight are positive.
-/
theorem gn21ComponentUpperAggregatePath_sameStrictSign_kernel
    (fixedQi fixedTi fixedWi arrivalRate lowerEndpoint u Qj Tj Wj : ℝ)
    (density switchProb payment : TripLength → ℝ)
    (hscale_pos : 0 < arrivalRate * density u)
    (hQj_pos : 0 < Qj)
    (hden :
      gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
          switchProb u * Tj +
        Qj *
          gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u ≠ 0) :
    sameStrictSign
      ((arrivalRate * density u) * Qj *
        gn21DerivativeSignKernel (switchProb u) u (payment u)
          (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb u)
          Qj
          (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
          Tj
          (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density
            payment u)
          Wj /
        (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb u * Tj +
          Qj *
            gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u) ^ 2)
      (gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
          switchProb u)
        Qj
        (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
        Tj
        (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density
          payment u)
        Wj) := by
  have hpositive_scale :
      0 <
        (arrivalRate * density u) * Qj /
          (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
              switchProb u * Tj +
            Qj *
              gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u) ^ 2 :=
    div_pos (mul_pos hscale_pos hQj_pos) (sq_pos_of_ne_zero hden)
  convert
    sameStrictSign_of_pos_mul_left
      ((arrivalRate * density u) * Qj /
        (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
            switchProb u * Tj +
          Qj *
            gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u) ^ 2)
      (gn21DerivativeSignKernel (switchProb u) u (payment u)
        (gn21ComponentUpperQiPath fixedQi arrivalRate lowerEndpoint density
          switchProb u)
        Qj
        (gn21ComponentUpperTiPath fixedTi arrivalRate lowerEndpoint density u)
        Tj
        (gn21ComponentUpperWiPath fixedWi arrivalRate lowerEndpoint density
          payment u)
        Wj)
      hpositive_scale using 1
  field_simp [hden]

/--
The actual Appendix-D aggregate functional, with the non-surge policy varied
along a bounded component, is exactly the quotient with fixed-background
`Q/T/W` terms and moving interval integrals.  This is an inward-path identity;
it makes no derivative claim.
-/
theorem gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_eq
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
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
        (Function.update rho 0 (gn21ComponentUpperPath (rho 0) lower upper x)) =
      gn21AggregateDynamicReward
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21
            (rho 0 \ Set.Ioo lower upper) +
          (arrival 0) *
            ∫ tau in Set.Ioo lower x, gn21SwitchProb switch12 switch21 tau ∂(mu 0))
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12 (rho 1))
        (gn21ScaledStateTime (mu 0) (arrival 0)
            (rho 0 \ Set.Ioo lower upper) +
          (arrival 0) * ∫ tau in Set.Ioo lower x, tau ∂(mu 0))
        (gn21ScaledStateTime (mu 1) (arrival 1) (rho 1))
        (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0)
            (rho 0 \ Set.Ioo lower upper) +
          (arrival 0) * ∫ tau in Set.Ioo lower x, (w 0) tau ∂(mu 0))
        (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1) (rho 1)) := by
  rw [gn21AggregateDynamicRewardFunctional_apply]
  change
    gn21MeasuredAggregateRewardPrimitives
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1)
        (gn21ComponentUpperPath (rho 0) lower upper x) (rho 1) = _
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [gn21ExitWeightIntegral_gn21ComponentUpperPath
      (mu 0) (arrival 0) switch12 switch21 (rho 0) lower upper x hx_upper
      hq_integrable_background hq_integrable_interval,
    gn21ScaledStateTime_gn21ComponentUpperPath
      (mu 0) (arrival 0) (rho 0) lower upper x hx_upper
      htime_integrable_background htime_integrable_interval,
    gn21ScaledStateEarning_gn21ComponentUpperPath
      (mu 0) (arrival 0) (w 0) (rho 0) lower upper x hx_upper
      hw_integrable_background hw_integrable_interval]

/--
At the selected component endpoint, the actual updated aggregate policy is the
original one.  This ties the fixed-background path to the current policy
without a null-set replacement or a global policy-form assumption.
-/
theorem gn21AggregateDynamicRewardFunctional_update_zero_componentUpperPath_at_upper
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper : TripLength)
    (hcomponent_subset : Set.Ioo lower upper ⊆ rho 0) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 0
          (gn21ComponentUpperPath (rho 0) lower upper upper)) =
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho := by
  have hpath :
      gn21ComponentUpperPath (rho 0) lower upper upper = rho 0 :=
    gn21ComponentUpperPath_at_upper (rho 0) lower upper hcomponent_subset
  rw [hpath]
  simp

/--
The symmetric Appendix-D identity when the surge policy is varied along one
of its bounded components.  The switch directions are swapped exactly as in
the source two-state aggregate formula.
-/
theorem gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_eq
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper x : TripLength)
    (hx_upper : x ≤ upper)
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
        (Function.update rho 1 (gn21ComponentUpperPath (rho 1) lower upper x)) =
      gn21AggregateDynamicReward
        (gn21ExitWeightIntegral (mu 0) (arrival 0) switch12 switch21 (rho 0))
        (gn21ExitWeightIntegral (mu 1) (arrival 1) switch21 switch12
            (rho 1 \ Set.Ioo lower upper) +
          (arrival 1) *
            ∫ tau in Set.Ioo lower x, gn21SwitchProb switch21 switch12 tau ∂(mu 1))
        (gn21ScaledStateTime (mu 0) (arrival 0) (rho 0))
        (gn21ScaledStateTime (mu 1) (arrival 1)
            (rho 1 \ Set.Ioo lower upper) +
          (arrival 1) * ∫ tau in Set.Ioo lower x, tau ∂(mu 1))
        (gn21ScaledStateEarning (mu 0) (arrival 0) (w 0) (rho 0))
        (gn21ScaledStateEarning (mu 1) (arrival 1) (w 1)
            (rho 1 \ Set.Ioo lower upper) +
          (arrival 1) * ∫ tau in Set.Ioo lower x, (w 1) tau ∂(mu 1)) := by
  rw [gn21AggregateDynamicRewardFunctional_apply]
  change
    gn21MeasuredAggregateRewardPrimitives
        (mu 0) (mu 1) (arrival 0) (arrival 1) switch12 switch21
        (w 0) (w 1)
        (rho 0) (gn21ComponentUpperPath (rho 1) lower upper x) = _
  unfold gn21MeasuredAggregateRewardPrimitives
  rw [gn21ExitWeightIntegral_gn21ComponentUpperPath
      (mu 1) (arrival 1) switch21 switch12 (rho 1) lower upper x hx_upper
      hq_integrable_background hq_integrable_interval,
    gn21ScaledStateTime_gn21ComponentUpperPath
      (mu 1) (arrival 1) (rho 1) lower upper x hx_upper
      htime_integrable_background htime_integrable_interval,
    gn21ScaledStateEarning_gn21ComponentUpperPath
      (mu 1) (arrival 1) (w 1) (rho 1) lower upper x hx_upper
      hw_integrable_background hw_integrable_interval]

/-- The surge-state component path also restores the original policy at its endpoint. -/
theorem gn21AggregateDynamicRewardFunctional_update_one_componentUpperPath_at_upper
    (mu : Fin 2 → Measure TripLength)
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction) (rho : Fin 2 → TripPolicy)
    (lower upper : TripLength)
    (hcomponent_subset : Set.Ioo lower upper ⊆ rho 1) :
    gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
        (Function.update rho 1
          (gn21ComponentUpperPath (rho 1) lower upper upper)) =
      gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w rho := by
  have hpath :
      gn21ComponentUpperPath (rho 1) lower upper upper = rho 1 :=
    gn21ComponentUpperPath_at_upper (rho 1) lower upper hcomponent_subset
  rw [hpath]
  simp

/-!
## Remaining derivative boundary

`gn21ComponentUpperAggregatePath_hasDerivAt` closes the quotient-calculus
part of the repair: its baseline values can be the actual `Q/T/W` primitives
of the component complement.  The still-missing theorem is a *policy-path
transport* theorem, not another derivative formula.  It must derive, from a
Lebesgue-with-density representation and the displayed integrability facts,
an eventual equality between

```
fun x => gn21AggregateDynamicRewardFunctional ...
  (Function.update rho i (gn21ComponentUpperPath (rho i) lower upper x))
```

and the fixed-background quotient path above.  The inward equality is proved
here exactly.  A two-sided `HasDerivAt` transport additionally needs either
`gn21ComponentUpperLocallySeparated` on a real neighborhood or an a.e.
canonicalization theorem that first merges touching components.  The existing
`paper_lemma6_upper_endpoint_interval_density_response_formula_no_density_premise`
only treats a standalone interval baseline and therefore cannot provide this
transport.
-/

end

end GN21DriverSurgePricing
