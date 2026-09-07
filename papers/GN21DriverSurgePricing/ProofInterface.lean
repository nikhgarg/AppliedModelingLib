import GN21DriverSurgePricing.PaperInterface

import GN21DriverSurgePricing.ProofBridge



namespace GN21DriverSurgePricing

namespace PaperInterface

open ProofBridge
open MeasureTheory
open scoped ENNReal

/-! ## Source-model definitions -/

theorem review_definition_incentive_compatible_realizes_spec :
    ((fun R : SingleStateReward =>
        GN21DriverSurgePricing.ProofBridge.review_definition_single_state_ic (R := R)),
      (fun R : DynamicReward =>
        GN21DriverSurgePricing.ProofBridge.review_definition_dynamic_ic (R := R))) =
      review_definition_incentive_compatibleSpec := by
  rfl

theorem review_definition_surge_state_realizes_spec
    (mu : Fin 2 → Measure TripLength) (arrival : Fin 2 → ℝ)
    (w : Fin 2 → PricingFunction) :
    GN21DriverSurgePricing.ProofBridge.review_definition_surge_state
        (mu := mu) (arrival := arrival) (w := w) ↔
      review_definition_surge_stateSpec (mu := mu) (arrival := arrival) (w := w) := by
  rfl

/-! ## Main-text results -/

theorem review_theorem1_single_state_threshold_best_response
  (μ : MeasureTheory.Measure TripLength) (arrivalRate : ℝ) (w : GN21PayoutFunction)
  (hrate_measurable : Measurable fun τ => w.toPricingFunction τ / τ)
  (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll :
    MeasureTheory.IntegrableOn w.toPricingFunction acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ)
  (hlambda : 0 < arrivalRate) :
  review_theorem1_single_state_threshold_best_responseSpec
    (μ := μ) (arrivalRate := arrivalRate) (w := w)
    (hrate_measurable := hrate_measurable)
    (hfinite_acceptAll := hfinite_acceptAll)
    (hw_integrable_acceptAll := hw_integrable_acceptAll)
    (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda) := by
  exact GN21DriverSurgePricing.ProofBridge.review_theorem1_single_state_threshold_best_response
    (μ := μ) (arrivalRate := arrivalRate) (w := w)
    (hrate_measurable := hrate_measurable)
    (hfinite_acceptAll := hfinite_acceptAll)
    (hw_integrable_acceptAll := hw_integrable_acceptAll)
    (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda)

theorem review_proposition3_1_affine_single_state_ic (mu : MeasureTheory.Measure TripLength)
  (arrivalRate m a : ℝ)
  (haccept_mass : singleStateTripMass mu acceptAllPolicy = 1)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ : TripLength => τ) acceptAllPolicy mu)
  (hlambda : 0 < arrivalRate) (ha_nonneg : 0 ≤ a)
  (ha_le_wait_value : a ≤ m / arrivalRate) : review_proposition3_1_affine_single_state_icSpec (mu := mu) (arrivalRate := arrivalRate) (m := m) (a := a) (haccept_mass := haccept_mass) (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda) (ha_nonneg := ha_nonneg) (ha_le_wait_value := ha_le_wait_value) := by
  exact GN21DriverSurgePricing.ProofBridge.review_proposition3_1_affine_single_state_ic (mu := mu) (arrivalRate := arrivalRate) (m := m) (a := a) (haccept_mass := haccept_mass) (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda) (ha_nonneg := ha_nonneg) (ha_le_wait_value := ha_le_wait_value)

theorem review_theorem2_multiplicative_policy_shape_source_claim
    (mu : Fin 2 → MeasureTheory.Measure TripLength)
    [MeasureTheory.NoAtoms (mu 0)] [MeasureTheory.NoAtoms (mu 1)]
    [MeasureTheory.IsFiniteMeasure (mu 0)] [MeasureTheory.IsFiniteMeasure (mu 1)]
    (arrival : Fin 2 → ℝ)
    (switch12 switch21 : ℝ)
    (m : Fin 2 → ℝ)
    (hm0_nonneg : 0 ≤ m 0)
    (hm1_nonneg : 0 ≤ m 1)
    (harrival0_pos : 0 < arrival 0)
    (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12)
    (hswitch21_pos : 0 < switch21)
    (hmass0_eq_one : singleStateTripMass (mu 0) acceptAllPolicy = 1)
    (hmass1_eq_one : singleStateTripMass (mu 1) acceptAllPolicy = 1)
    (htime0_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1_integrable_acceptAll :
      IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival
      (fun i => multiplicativePricing (m i))) : review_theorem2_multiplicative_policy_shape_source_claimSpec (mu := mu) (arrival := arrival) (switch12 := switch12) (switch21 := switch21) (m := m) (hm0_nonneg := hm0_nonneg) (hm1_nonneg := hm1_nonneg) (harrival0_pos := harrival0_pos) (harrival1_pos := harrival1_pos) (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos) (hmass0_eq_one := hmass0_eq_one) (hmass1_eq_one := hmass1_eq_one) (htime0_integrable_acceptAll := htime0_integrable_acceptAll) (htime1_integrable_acceptAll := htime1_integrable_acceptAll) (hsurge := hsurge) := by
  exact GN21DriverSurgePricing.ProofBridge.review_theorem2_multiplicative_policy_shape_source_claim (mu := mu) (arrival := arrival) (switch12 := switch12) (switch21 := switch21) (m := m) (hm0_nonneg := hm0_nonneg) (hm1_nonneg := hm1_nonneg) (harrival0_pos := harrival0_pos) (harrival1_pos := harrival1_pos) (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos) (hmass0_eq_one := hmass0_eq_one) (hmass1_eq_one := hmass1_eq_one) (htime0_integrable_acceptAll := htime0_integrable_acceptAll) (htime1_integrable_acceptAll := htime1_integrable_acceptAll) (hsurge := hsurge)

theorem review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states : review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_statesSpec := by
  exact GN21DriverSurgePricing.ProofBridge.review_theorem2_multiplicative_positive_finite_cutoff_not_ic_both_states

theorem review_lemma1_measured_dynamic_reward_decomposition
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {wI wJ : PricingFunction} {sigmaI sigmaJ : TripPolicy}
    (C : GN21DynamicIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI wI wJ sigmaI sigmaJ) : review_lemma1_measured_dynamic_reward_decompositionSpec (Omega := Omega) (POmega := POmega) (muI := muI) (muJ := muJ) (arrivalI := arrivalI) (arrivalJ := arrivalJ) (switchIJ := switchIJ) (switchJI := switchJI) (wI := wI) (wJ := wJ) (sigmaI := sigmaI) (sigmaJ := sigmaJ) (C := C) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma1_measured_dynamic_reward_decomposition (Omega := Omega) (POmega := POmega) (muI := muI) (muJ := muJ) (arrivalI := arrivalI) (arrivalJ := arrivalJ) (switchIJ := switchIJ) (switchJI := switchJI) (wI := wI) (wJ := wJ) (sigmaI := sigmaI) (sigmaJ := sigmaJ) (C := C)

/-- Source-model Lemma 1 endpoint: the raw calendar itself constructs the
successive IID renewal observations used by the convergence result. -/
abbrev review_lemma1_measured_dynamic_reward_decomposition_of_actual_calendar :=
  @GN21DriverSurgePricing.ProofBridge.review_lemma1_measured_dynamic_reward_decomposition_of_actual_calendar

theorem review_lemma2_switch_probability_formula (lambdaIJ lambdaJI s : ℝ) : review_lemma2_switch_probability_formulaSpec (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (s := s) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma2_switch_probability_formula (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (s := s)

theorem review_lemma3_measured_time_fraction_formula
    {Omega : Type u_1} [MeasurableSpace Omega]
    {POmega : Measure Omega}
    {muI muJ : Measure TripLength}
    {arrivalI arrivalJ switchIJ switchJI : ℝ}
    {sigmaI sigmaJ : TripPolicy}
    (C : GN21TimeFractionIIDCycleModel POmega muI muJ arrivalI arrivalJ
      switchIJ switchJI sigmaI sigmaJ) : review_lemma3_measured_time_fraction_formulaSpec (Omega := Omega) (POmega := POmega) (muI := muI) (muJ := muJ) (arrivalI := arrivalI) (arrivalJ := arrivalJ) (switchIJ := switchIJ) (switchJI := switchJI) (sigmaI := sigmaI) (sigmaJ := sigmaJ) (C := C) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma3_measured_time_fraction_formula (Omega := Omega) (POmega := POmega) (muI := muI) (muJ := muJ) (arrivalI := arrivalI) (arrivalJ := arrivalJ) (switchIJ := switchIJ) (switchJI := switchJI) (sigmaI := sigmaI) (sigmaJ := sigmaJ) (C := C)

/-- Source-model Lemma 3 endpoint: the raw calendar itself constructs the
successive IID time observations used by the convergence result. -/
abbrev review_lemma3_measured_time_fraction_formula_of_actual_calendar :=
  @GN21DriverSurgePricing.ProofBridge.review_lemma3_measured_time_fraction_formula_of_actual_calendar

theorem review_theorem3_structured_pricing :
    review_theorem3_structured_pricingSpec := by
  constructor
  · intro mu arrival R1 R2 switch12 switch21 _ _ _ _ hR1_lt_R2
      harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one
    exact GN21DriverSurgePricing.ProofBridge.review_theorem3_structured_general_policy_source_claim
      (mu := mu) (arrival := arrival) (R1 := R1) (R2 := R2)
      (switch12 := switch12) (switch21 := switch21)
      (hR1_lt_R2 := hR1_lt_R2)
      (harrival1_pos := harrival1_pos) (harrival2_pos := harrival2_pos)
      (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos)
      (htime1_integrable := htime1_integrable)
      (htime2_integrable := htime2_integrable)
      (hmass1_eq_one := hmass1_eq_one) (hmass2_eq_one := hmass2_eq_one)
  · intro mu arrival R1 R2 switch12 switch21 _ _ _ _ hR2_pos hC_lt_ratio
      hratio_lt_one harrival1_pos harrival2_pos hswitch12_pos hswitch21_pos
      htime1_integrable htime2_integrable hmass1_eq_one hmass2_eq_one
    exact GN21DriverSurgePricing.ProofBridge.review_theorem3_structured_ic_source_claim
      (mu := mu) (arrival := arrival) (R1 := R1) (R2 := R2)
      (switch12 := switch12) (switch21 := switch21)
      (hR2_pos := hR2_pos) (hC_lt_ratio := hC_lt_ratio)
      (hratio_lt_one := hratio_lt_one)
      (harrival1_pos := harrival1_pos) (harrival2_pos := harrival2_pos)
      (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos)
      (htime1_integrable := htime1_integrable)
      (htime2_integrable := htime2_integrable)
      (hmass1_eq_one := hmass1_eq_one) (hmass2_eq_one := hmass2_eq_one)

/-! ## Appendix results -/

theorem review_lemma4_single_state_threshold_uniqueness (μ : MeasureTheory.Measure TripLength)
  (arrivalRate : ℝ) (w : PricingFunction) (hrate_measurable : Measurable fun τ => w τ / τ)
  (hrate_nonneg : ∀ (τ : TripLength), 0 < τ → 0 ≤ w τ / τ) (hfinite_acceptAll : μ acceptAllPolicy ≠ ⊤)
  (hw_integrable_acceptAll : MeasureTheory.IntegrableOn w acceptAllPolicy μ)
  (htime_integrable_acceptAll : MeasureTheory.IntegrableOn (fun τ => τ) acceptAllPolicy μ) (hlambda : 0 < arrivalRate) : review_lemma4_single_state_threshold_uniquenessSpec (μ := μ) (arrivalRate := arrivalRate) (w := w) (hrate_measurable := hrate_measurable) (hrate_nonneg := hrate_nonneg) (hfinite_acceptAll := hfinite_acceptAll) (hw_integrable_acceptAll := hw_integrable_acceptAll) (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma4_single_state_threshold_uniqueness (μ := μ) (arrivalRate := arrivalRate) (w := w) (hrate_measurable := hrate_measurable) (hrate_nonneg := hrate_nonneg) (hfinite_acceptAll := hfinite_acceptAll) (hw_integrable_acceptAll := hw_integrable_acceptAll) (htime_integrable_acceptAll := htime_integrable_acceptAll) (hlambda := hlambda)

theorem lemma5_full_variational_policy_forms
    (mu : Measure TripLength) [IsFiniteMeasure mu]
    [mu.InnerRegularCompactLTTop] [NoAtoms mu]
    (Rhat : SingleStateReward)
    (response : TripPolicy → TripLength → ℝ)
    (shape : Lemma5DerivativeShape)
    {sigma : TripPolicy}
    (hsigma_open : IsOpen sigma)
    (hsigma_subset : sigma ⊆ acceptAllPolicy)
    (hempty_lt_sigma : Rhat ∅ < Rhat sigma)
    {margin : ℝ} (hmargin : 0 < margin)
    (hcontinuous : ∀ tau : TripPolicy,
      GN21SymmDiffContinuousAt mu Rhat tau)
    (hendpoint_continuous :
      ∀ extra : Nat,
        ContinuousOn
          (fun endpoints : GN21Lemma5EndpointVector extra =>
            Rhat (gn21EndpointVectorPolicy endpoints))
          (gn21Lemma5EndpointDomain shape extra))
    (hresponse_positive :
      shape = .positive →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ u : TripLength, 0 < u → 0 < response tau u)
    (hresponse_increasing :
      shape = .strictlyIncreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictMonoOn (response tau) (Set.Ici 0))
    (hresponse_decreasing :
      shape = .strictlyDecreasing →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            StrictAntiOn (response tau) (Set.Ici 0))
    (hresponse_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConvexOnPositive (response tau))
    (hzero_quasiConvex :
      shape = .strictlyQuasiConvex →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middleLower middleUpper right : ℝ},
              0 < middleLower → middleLower < middleUpper →
                middleUpper < right →
                  response tau middleLower <
                    max (response tau 0) (response tau right))
    (hresponse_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            strictQuasiConcaveOnPositive (response tau))
    (hzero_quasiConcave :
      shape = .strictlyQuasiConcave →
        ∀ tau : TripPolicy,
          Rhat sigma - margin ≤ Rhat tau →
            ∀ {middle right : ℝ}, 0 < middle → middle < right →
              min (response tau 0) (response tau right) <
                response tau middle)
    (H : GN21Lemma5AENullEndpointVariation
      mu Rhat response shape sigma margin) : lemma5_full_variational_policy_formsSpec (mu := mu) (Rhat := Rhat) (response := response) (shape := shape) (sigma := sigma) (hsigma_open := hsigma_open) (hsigma_subset := hsigma_subset) (hempty_lt_sigma := hempty_lt_sigma) (margin := margin) (hmargin := hmargin) (hcontinuous := hcontinuous) (hendpoint_continuous := hendpoint_continuous) (hresponse_positive := hresponse_positive) (hresponse_increasing := hresponse_increasing) (hresponse_decreasing := hresponse_decreasing) (hresponse_quasiConvex := hresponse_quasiConvex) (hzero_quasiConvex := hzero_quasiConvex) (hresponse_quasiConcave := hresponse_quasiConcave) (hzero_quasiConcave := hzero_quasiConcave) (H := H) := by
  exact GN21DriverSurgePricing.ProofBridge.lemma5_full_variational_policy_forms (mu := mu) (Rhat := Rhat) (response := response) (shape := shape) (sigma := sigma) (hsigma_open := hsigma_open) (hsigma_subset := hsigma_subset) (hempty_lt_sigma := hempty_lt_sigma) (margin := margin) (hmargin := hmargin) (hcontinuous := hcontinuous) (hendpoint_continuous := hendpoint_continuous) (hresponse_positive := hresponse_positive) (hresponse_increasing := hresponse_increasing) (hresponse_decreasing := hresponse_decreasing) (hresponse_quasiConvex := hresponse_quasiConvex) (hzero_quasiConvex := hzero_quasiConvex) (hresponse_quasiConcave := hresponse_quasiConcave) (hzero_quasiConcave := hzero_quasiConcave) (H := H)

theorem review_lemma6_upper_endpoint_derivative_formula
  (arrivalRate switchRate lowerEndpoint u Qj Tj Wj Ri Rj : ℝ) (density switchProb payment : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hu : 0 < u) (hQj_pos : 0 < Qj)
  (hTi_pos : 0 < gn21EndpointTiPath arrivalRate lowerEndpoint density u) (hTj_pos : 0 < Tj)
  (hWi :
    gn21EndpointWiPath arrivalRate lowerEndpoint density payment u =
      Ri * gn21EndpointTiPath arrivalRate lowerEndpoint density u)
  (hWj : Wj = Rj * Tj)
  (hden :
    gn21EndpointQiPath arrivalRate switchRate lowerEndpoint density switchProb u * Tj +
        Qj * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int : IntervalIntegrable (fun τ => switchProb τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas : StronglyMeasurableAtFilter (fun τ => switchProb τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => switchProb τ * density τ) u)
  (hw_int : IntervalIntegrable (fun τ => payment τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hw_meas : StronglyMeasurableAtFilter (fun τ => payment τ * density τ) (nhds u) MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => payment τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u) : review_lemma6_upper_endpoint_derivative_formulaSpec (arrivalRate := arrivalRate) (switchRate := switchRate) (lowerEndpoint := lowerEndpoint) (u := u) (Qj := Qj) (Tj := Tj) (Wj := Wj) (Ri := Ri) (Rj := Rj) (density := density) (switchProb := switchProb) (payment := payment) (harrival_pos := harrival_pos) (hu := hu) (hQj_pos := hQj_pos) (hTi_pos := hTi_pos) (hTj_pos := hTj_pos) (hWi := hWi) (hWj := hWj) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma6_upper_endpoint_derivative_formula (arrivalRate := arrivalRate) (switchRate := switchRate) (lowerEndpoint := lowerEndpoint) (u := u) (Qj := Qj) (Tj := Tj) (Wj := Wj) (Ri := Ri) (Rj := Rj) (density := density) (switchProb := switchProb) (payment := payment) (harrival_pos := harrival_pos) (hu := hu) (hQj_pos := hQj_pos) (hTi_pos := hTi_pos) (hTj_pos := hTj_pos) (hWi := hWi) (hWj := hWj) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont)

theorem review_lemma7_affine_positive_additive_response_quasi_convex
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_pos : 0 < a) (hdelta_ji_nonpos : Rj - Ri ≤ 0)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) : review_lemma7_affine_positive_additive_response_quasi_convexSpec (m := m) (a := a) (Qi := Qi) (Qj := Qj) (Ti := Ti) (Tj := Tj) (Ri := Ri) (Rj := Rj) (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (hm_pos := hm_pos) (ha_pos := ha_pos) (hdelta_ji_nonpos := hdelta_ji_nonpos) (hstate_weight_pos := hstate_weight_pos) (hlambdaIJ := hlambdaIJ) (hsum := hsum) (hTi := hTi) (hTj := hTj) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma7_affine_positive_additive_response_quasi_convex (m := m) (a := a) (Qi := Qi) (Qj := Qj) (Ti := Ti) (Tj := Tj) (Ri := Ri) (Rj := Rj) (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (hm_pos := hm_pos) (ha_pos := ha_pos) (hdelta_ji_nonpos := hdelta_ji_nonpos) (hstate_weight_pos := hstate_weight_pos) (hlambdaIJ := hlambdaIJ) (hsum := hsum) (hTi := hTi) (hTj := hTj)

theorem review_lemma8_affine_negative_additive_response_quasi_concave
  (m a Qi Qj Ti Tj Ri Rj lambdaIJ lambdaJI : ℝ) (hm_pos : 0 < m) (ha_neg : a < 0) (hdelta_ji_nonneg : 0 ≤ Rj - Ri)
  (hstate_weight_pos : 0 < Qi / Ti + Qj / Tj) (hlambdaIJ : 0 < lambdaIJ) (hsum : 0 < lambdaIJ + lambdaJI) (hTi : Ti ≠ 0)
  (hTj : Tj ≠ 0) : review_lemma8_affine_negative_additive_response_quasi_concaveSpec (m := m) (a := a) (Qi := Qi) (Qj := Qj) (Ti := Ti) (Tj := Tj) (Ri := Ri) (Rj := Rj) (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (hm_pos := hm_pos) (ha_neg := ha_neg) (hdelta_ji_nonneg := hdelta_ji_nonneg) (hstate_weight_pos := hstate_weight_pos) (hlambdaIJ := hlambdaIJ) (hsum := hsum) (hTi := hTi) (hTj := hTj) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma8_affine_negative_additive_response_quasi_concave (m := m) (a := a) (Qi := Qi) (Qj := Qj) (Ti := Ti) (Tj := Tj) (Ri := Ri) (Rj := Rj) (lambdaIJ := lambdaIJ) (lambdaJI := lambdaJI) (hm_pos := hm_pos) (ha_neg := ha_neg) (hdelta_ji_nonneg := hdelta_ji_nonneg) (hstate_weight_pos := hstate_weight_pos) (hlambdaIJ := hlambdaIJ) (hsum := hsum) (hTi := hTi) (hTj := hTj)

theorem review_lemma9_surge_derivative_positive_of_acceptAll_bounds
  (arrivalRate lowerEndpoint u T1 Q1 T2 Q2 Tbar2 Qbar2 switch21 switch12 m R1 z ratio : ℝ) (density : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hdensity_pos : 0 < density u) (hQ1_pos : 0 < Q1)
  (hden :
    gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density (gn21SwitchProb switch21 switch12) u * T1 +
        Q1 * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int :
    IntervalIntegrable (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas :
    StronglyMeasurableAtFilter (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => gn21SwitchProb switch21 switch12 τ * density τ) u)
  (hw_int :
    IntervalIntegrable (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) MeasureTheory.volume
      lowerEndpoint u)
  (hw_meas :
    StronglyMeasurableAtFilter (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) (nhds u)
      MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => ctmcStructuredSurgePrice m z switch21 switch12 τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
  (hQ2 : gn21EndpointQiPath arrivalRate switch21 lowerEndpoint density (gn21SwitchProb switch21 switch12) u = Q2)
  (hT2 : gn21EndpointTiPath arrivalRate lowerEndpoint density u = T2)
  (hW2 :
    gn21EndpointWiPath arrivalRate lowerEndpoint density (ctmcStructuredSurgePrice m z switch21 switch12) u =
      m * (T2 - 1) + z * (Q2 - switch21))
  (hbounds_bar : lemma9StructuredBounds ratio T1 Q1 Tbar2 Qbar2 switch21) (hz_nonneg : 0 ≤ z)
  (hz : z = ratio * (m - R1))
  (hmR_pos : 0 < m - R1) (hR1_nonneg : 0 ≤ R1) (hT1_nonneg : 0 ≤ T1) (hswitch21_pos : 0 < switch21)
  (hsum : 0 < switch21 + switch12) (hu : 0 < u) (hgap_nonneg : 0 ≤ switch21 * T2 - Q2)
  (hgap_le : switch21 * T2 - Q2 ≤ switch21 * Tbar2 - Qbar2) (hswitch_lt_Q2 : switch21 < Q2) (hQ2_le : Q2 ≤ Qbar2) : review_lemma9_surge_derivative_positive_of_acceptAll_boundsSpec (arrivalRate := arrivalRate) (lowerEndpoint := lowerEndpoint) (u := u) (T1 := T1) (Q1 := Q1) (T2 := T2) (Q2 := Q2) (Tbar2 := Tbar2) (Qbar2 := Qbar2) (switch21 := switch21) (switch12 := switch12) (m := m) (R1 := R1) (z := z) (ratio := ratio) (density := density) (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos) (hQ1_pos := hQ1_pos) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ2 := hQ2) (hT2 := hT2) (hW2 := hW2) (hbounds_bar := hbounds_bar) (hz_nonneg := hz_nonneg) (hz := hz) (hmR_pos := hmR_pos) (hR1_nonneg := hR1_nonneg) (hT1_nonneg := hT1_nonneg) (hswitch21_pos := hswitch21_pos) (hsum := hsum) (hu := hu) (hgap_nonneg := hgap_nonneg) (hgap_le := hgap_le) (hswitch_lt_Q2 := hswitch_lt_Q2) (hQ2_le := hQ2_le) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma9_surge_derivative_positive_of_acceptAll_bounds (arrivalRate := arrivalRate) (lowerEndpoint := lowerEndpoint) (u := u) (T1 := T1) (Q1 := Q1) (T2 := T2) (Q2 := Q2) (Tbar2 := Tbar2) (Qbar2 := Qbar2) (switch21 := switch21) (switch12 := switch12) (m := m) (R1 := R1) (z := z) (ratio := ratio) (density := density) (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos) (hQ1_pos := hQ1_pos) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ2 := hQ2) (hT2 := hT2) (hW2 := hW2) (hbounds_bar := hbounds_bar) (hz_nonneg := hz_nonneg) (hz := hz) (hmR_pos := hmR_pos) (hR1_nonneg := hR1_nonneg) (hT1_nonneg := hT1_nonneg) (hswitch21_pos := hswitch21_pos) (hsum := hsum) (hu := hu) (hgap_nonneg := hgap_nonneg) (hgap_le := hgap_le) (hswitch_lt_Q2 := hswitch_lt_Q2) (hQ2_le := hQ2_le)

theorem review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds
  (arrivalRate lowerEndpoint u T2 Q2 T1 Q1 Tbar1 Qbar1 switch12 switch21 R2 z ratio : ℝ) (density : ℝ → ℝ)
  (harrival_pos : 0 < arrivalRate) (hdensity_pos : 0 < density u) (hQ2_pos : 0 < Q2)
  (hden :
    gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density (gn21SwitchProb switch12 switch21) u * T2 +
        Q2 * gn21EndpointTiPath arrivalRate lowerEndpoint density u ≠
      0)
  (hq_int :
    IntervalIntegrable (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (hq_meas :
    StronglyMeasurableAtFilter (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) (nhds u) MeasureTheory.volume)
  (hq_cont : ContinuousAt (fun τ => gn21SwitchProb switch12 switch21 τ * density τ) u)
  (hw_int :
    IntervalIntegrable (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) MeasureTheory.volume
      lowerEndpoint u)
  (hw_meas :
    StronglyMeasurableAtFilter (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) (nhds u)
      MeasureTheory.volume)
  (hw_cont : ContinuousAt (fun τ => ctmcStructuredSurgePrice R2 z switch12 switch21 τ * density τ) u)
  (ht_int : IntervalIntegrable (fun τ => τ * density τ) MeasureTheory.volume lowerEndpoint u)
  (ht_meas : StronglyMeasurableAtFilter (fun τ => τ * density τ) (nhds u) MeasureTheory.volume)
  (ht_cont : ContinuousAt (fun τ => τ * density τ) u)
  (hQ1 : gn21EndpointQiPath arrivalRate switch12 lowerEndpoint density (gn21SwitchProb switch12 switch21) u = Q1)
  (hT1 : gn21EndpointTiPath arrivalRate lowerEndpoint density u = T1)
  (hW1 :
    gn21EndpointWiPath arrivalRate lowerEndpoint density (ctmcStructuredSurgePrice R2 z switch12 switch21) u =
      R2 * (T1 - 1) + z * (Q1 - switch12))
  (hbounds_bar : lemma10StructuredBounds ratio T2 Q2 Tbar1 Qbar1 switch12) (hz_nonpos : z ≤ 0)
  (hz : z = ratio * R2) (hR2_pos : 0 < R2)
  (hswitch12_pos : 0 < switch12) (hsum : 0 < switch12 + switch21) (hu : 0 < u) (hA_pos : 0 < T2 * switch12 + Q2)
  (hgap_nonneg : 0 ≤ switch12 * T1 - Q1) (hgap_le : switch12 * T1 - Q1 ≤ switch12 * Tbar1 - Qbar1)
  (hswitch_lt_Q1 : switch12 < Q1) (hQ1_le : Q1 ≤ Qbar1) : review_lemma10_nonsurge_derivative_positive_of_acceptAll_boundsSpec (arrivalRate := arrivalRate) (lowerEndpoint := lowerEndpoint) (u := u) (T2 := T2) (Q2 := Q2) (T1 := T1) (Q1 := Q1) (Tbar1 := Tbar1) (Qbar1 := Qbar1) (switch12 := switch12) (switch21 := switch21) (R2 := R2) (z := z) (ratio := ratio) (density := density) (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos) (hQ2_pos := hQ2_pos) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ1 := hQ1) (hT1 := hT1) (hW1 := hW1) (hbounds_bar := hbounds_bar) (hz_nonpos := hz_nonpos) (hz := hz) (hR2_pos := hR2_pos) (hswitch12_pos := hswitch12_pos) (hsum := hsum) (hu := hu) (hA_pos := hA_pos) (hgap_nonneg := hgap_nonneg) (hgap_le := hgap_le) (hswitch_lt_Q1 := hswitch_lt_Q1) (hQ1_le := hQ1_le) := by
  exact GN21DriverSurgePricing.ProofBridge.review_lemma10_nonsurge_derivative_positive_of_acceptAll_bounds (arrivalRate := arrivalRate) (lowerEndpoint := lowerEndpoint) (u := u) (T2 := T2) (Q2 := Q2) (T1 := T1) (Q1 := Q1) (Tbar1 := Tbar1) (Qbar1 := Qbar1) (switch12 := switch12) (switch21 := switch21) (R2 := R2) (z := z) (ratio := ratio) (density := density) (harrival_pos := harrival_pos) (hdensity_pos := hdensity_pos) (hQ2_pos := hQ2_pos) (hden := hden) (hq_int := hq_int) (hq_meas := hq_meas) (hq_cont := hq_cont) (hw_int := hw_int) (hw_meas := hw_meas) (hw_cont := hw_cont) (ht_int := ht_int) (ht_meas := ht_meas) (ht_cont := ht_cont) (hQ1 := hQ1) (hT1 := hT1) (hW1 := hW1) (hbounds_bar := hbounds_bar) (hz_nonpos := hz_nonpos) (hz := hz) (hR2_pos := hR2_pos) (hswitch12_pos := hswitch12_pos) (hsum := hsum) (hu := hu) (hA_pos := hA_pos) (hgap_nonneg := hgap_nonneg) (hgap_le := hgap_le) (hswitch_lt_Q1 := hswitch_lt_Q1) (hQ1_le := hQ1_le)

theorem review_theorem4_full_structural_policy_forms_direct
    (mu : Fin 2 → Measure TripLength)
    [NoAtoms (mu 0)] [NoAtoms (mu 1)]
    [IsFiniteMeasure (mu 0)] [IsFiniteMeasure (mu 1)]
    [(mu 0).InnerRegularCompactLTTop] [(mu 1).InnerRegularCompactLTTop]
    (arrival : Fin 2 → ℝ) (switch12 switch21 : ℝ)
    (w : Fin 2 → PricingFunction)
    (shape : Fin 2 → Lemma5DerivativeShape)
    (harrival0_pos : 0 < arrival 0) (harrival1_pos : 0 < arrival 1)
    (hswitch12_pos : 0 < switch12) (hswitch21_pos : 0 < switch21)
    (hw0_measurable : Measurable (w 0)) (hw1_measurable : Measurable (w 1))
    (htime0 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 0))
    (htime1 : IntegrableOn (fun tau : TripLength => tau) acceptAllPolicy (mu 1))
    (hw0 : IntegrableOn (w 0) acceptAllPolicy (mu 0))
    (hw1 : IntegrableOn (w 1) acceptAllPolicy (mu 1))
    (hsurge : gn21SourceSurgeStateDominance mu arrival w)
    (hnonsurge_price_case :
      gn21Theorem4NonsurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hsurge_price_case :
      gn21Theorem4SurgeLiteralEndpointPriceCase
        (gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w) w shape)
    (hcontinuous :
      ∀ (rho : Fin 2 → TripPolicy),
        dynamicFeasibleOpenPolicy rho →
          ∀ (i : Fin 2) (tau : TripPolicy),
            GN21SymmDiffContinuousAt (mu i)
              (fun policy =>
                gn21AggregateDynamicRewardFunctional mu arrival switch12 switch21 w
                  (Function.update rho i policy)) tau) : review_theorem4_full_structural_policy_forms_directSpec (mu := mu) (arrival := arrival) (switch12 := switch12) (switch21 := switch21) (w := w) (shape := shape) (harrival0_pos := harrival0_pos) (harrival1_pos := harrival1_pos) (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos) (hw0_measurable := hw0_measurable) (hw1_measurable := hw1_measurable) (htime0 := htime0) (htime1 := htime1) (hw0 := hw0) (hw1 := hw1) (hsurge := hsurge) (hnonsurge_price_case := hnonsurge_price_case) (hsurge_price_case := hsurge_price_case) (hcontinuous := hcontinuous) := by
  exact GN21DriverSurgePricing.ProofBridge.review_theorem4_full_structural_policy_forms_direct (mu := mu) (arrival := arrival) (switch12 := switch12) (switch21 := switch21) (w := w) (shape := shape) (harrival0_pos := harrival0_pos) (harrival1_pos := harrival1_pos) (hswitch12_pos := hswitch12_pos) (hswitch21_pos := hswitch21_pos) (hw0_measurable := hw0_measurable) (hw1_measurable := hw1_measurable) (htime0 := htime0) (htime1 := htime1) (hw0 := hw0) (hw1 := hw1) (hsurge := hsurge) (hnonsurge_price_case := hnonsurge_price_case) (hsurge_price_case := hsurge_price_case) (hcontinuous := hcontinuous)



end PaperInterface
end GN21DriverSurgePricing
